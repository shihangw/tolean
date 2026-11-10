import tolean.Sql.IR.Eval

/-!
The part of the SQL translator that builds the IR of `tolean/Sql/IR.lean`,
for `SELECT` queries.

A query here is one `SELECT`, `:one` or `:many`, with no `WITH`. Its tables
are joined with `JOIN … ON` or commas, and each is reached through its
primary key by a condition `alias.key = e` where `e` reads only the tables
before it. The expressions are those of the string translation, without
subqueries.

The translator is a total function, so that Lean can reason about it.
`translate_sound` in `tolean/Sql/Proof/Query.lean` proves that every plan it
writes means what the source means: when the IR's evaluator gives a result
for a database, the interpreter in `tolean/Sql/Spec/Eval.lean`, which scans
every table, gives the same result. `tolean/Sql/Translate.lean` prints the
plan of every query that this part accepts, and uses its string translation
for the others.

The plan prints as the string translation would print the same query. This
part refuses more, wherever the printed code would differ from PostgreSQL
on some database:

- Integer arithmetic must have the type `bigint`, because the printed code
  checks the range of a `bigint`. PostgreSQL computes `integer + integer` as
  an `integer`. A parameter counts as the narrowest integer, unless a cast
  gives its type.
- A cast may not narrow an integer, because the printed code does not check
  the range.
- `jsonb` values are not compared, because PostgreSQL does not compare them
  as text.
- `IS NULL` on a value that cannot be NULL prints as a constant, so it must
  read a column, which cannot fail.
- A string literal takes an enum type only as an operand of `=` or `<>`.
- `COALESCE` of integers must have operands of one width, because the
  interpreter does not model the conversion to their common type.
-/
namespace tolean.Sql.Plan

open tolean tolean.Sql
open tolean.Sql.IR (Ty TyN)
open tolean.Sql.Eval (Width Target)

/-- The type of a translated expression. The width of an integer decides
where the printed `Pg.int64` computes what PostgreSQL computes. -/
structure T where
  ty : Ty
  nullable : Bool := false
  width : Width := .w64
deriving DecidableEq, Inhabited

def T.tyN (t : T) : TyN := ⟨t.ty, t.nullable⟩

/-- An alias of `FROM` in scope, with the variable that holds its row. -/
structure Entry where
  alias : String
  table : Table
  var : String

/-- The aliases in scope. The innermost comes first, as in the
interpreter's environment. -/
abbrev Scope := List Entry

def Entry.shape (e : Entry) : Eval.Shape := (e.alias, e.table)

/-- The parameters whose type is known, in the order they got it. -/
structure St where
  args : List (String × Ty) := []

abbrev TM := StateT St (Except String)

def reject {A : Type} (m : String) : TM A := throw m

def Width.le : Width → Width → Bool
  | .w16, _ => true
  | .w32, .w16 => false
  | .w32, _ => true
  | .w64, .w64 => true
  | .w64, _ => false

/-- The type of a column or cast, by its name. -/
def tyOfName (s : Schema) (tn : TypeName) : Option (Ty × Width) :=
  let tn := s.resolve tn
  if tn.array then none
  else match canonicalType tn with
    | "bigint" => some (.int, .w64)
    | "integer" => some (.int, .w32)
    | "smallint" => some (.int, .w16)
    | "boolean" => some (.bool, .w64)
    | "text" | "character varying" => some (.text, .w64)
    | "uuid" => some (.uuid, .w64)
    | "timestamp with time zone" | "timestamp without time zone" => some (.ts, .w64)
    | "jsonb" | "json" => some (.json, .w64)
    | "bytea" => some (.bytes, .w64)
    | n => if s.enums.any (·.1 == n) then some (.enum n, .w64) else none

def _root_.tolean.Sql.Eval.Target.ty : Target → Ty
  | .int _ => .int
  | .bool => .bool
  | .text => .text
  | .uuid => .uuid
  | .enum n _ => .enum n

/-- Refuse unless `c` holds. -/
def check (c : Bool) (m : String) : TM Unit := if c then pure () else reject m

/-- The value in `o`, or refuse. -/
def need {A : Type} (o : Option A) (m : String) : TM A :=
  match o with
  | some a => pure a
  | none => reject m

def single? {A : Type} : List A → Option A
  | [a] => some a
  | _ => none

def argTy? (n : String) : TM (Option Ty) := do
  return (← get).args.lookup n

def setArgTy (n : String) (t : Ty) : TM Unit := do
  match ← argTy? n with
  | some t' => check (t' = t) s!"sqlc.arg({n}) is used with two types"
  | none => modify fun st => { st with args := st.args ++ [(n, t)] }

/-- The type of `sqlc.arg(n)`: the type it already has, or else the hint,
which it keeps. -/
def argType (n : String) (hint : Option Ty) : TM Ty := do
  match ← argTy? n with
  | some t => pure t
  | none => do
    let t ← need hint s!"cannot tell the type of sqlc.arg({n}); cast it"
    setArgTy n t
    pure t

/-- A cast of a parameter gives the parameter its type. -/
def typeArg (e : Expr) (t : Ty) : TM Unit :=
  match e with
  | .arg _ n _ => setArgTy n t
  | _ => pure ()

def _root_.tolean.Sql.IR.Expr.isEnumLit : IR.Expr → Bool
  | .enumLit .. => true
  | _ => false

def _root_.tolean.Sql.IR.Expr.isCol : IR.Expr → Bool
  | .col .. => true
  | _ => false

/-- The code of `ie::tgt`, where `ie` has the type `t`. -/
def castCode (tgt : Target) (ie : IR.Expr) (t : T) : TM (IR.Expr × T) :=
  if t.ty = tgt.ty then
    match tgt with
    | .int w => do
      check (Width.le t.width w) "a cast that narrows an integer is not supported"
      pure (.cast tgt ie, { t with width := w })
    | _ => pure (.cast tgt ie, t)
  else match t.ty, tgt with
    | .enum en, .text => pure (.enumText en t.nullable ie, { ty := .text, nullable := t.nullable })
    | _, _ => reject "this cast is not supported"

/-- The code of `a op b`, for an operator other than `AND` and `OR`, on
operands that cannot be NULL. -/
def binCode (bop : Eval.BinOp) (ia : IR.Expr) (ta : T) (ib : IR.Expr) (tb : T) : TM (IR.Expr × T) :=
  match bop with
  | .arith aop => do
    check (ta.ty = .int ∧ tb.ty = .int ∧ ta.width.max tb.width = .w64) "arithmetic must be on bigint"
    pure (.arith aop ia ib, { ty := .int })
  | .eq => do
    check (ta.ty = tb.ty ∧ ta.ty ≠ .bool ∧ ta.ty ≠ .json) "this comparison is not supported"
    pure (.eq false ia ib, { ty := .bool })
  | .ne => do
    check (ta.ty = tb.ty ∧ ta.ty ≠ .bool ∧ ta.ty ≠ .json) "this comparison is not supported"
    pure (.eq true ia ib, { ty := .bool })
  | .cmp cop => do
    check (ta.ty = .int ∧ tb.ty = .int) "orders are supported on numbers only"
    pure (.cmp cop ia ib, { ty := .bool })
  | _ => reject "unreachable"

section
variable (s : Schema)

/-- The type of a column. -/
def colT (c : Column) : Option T :=
  (tyOfName s c.type).map fun (ty, width) => { ty, nullable := !c.notNull, width }

/-- The type of an expression, where it can be known without translating
it: the hint that the string translation gives the other operand. -/
def peek (Γ : Scope) (st : St) : Expr → Option Ty
  | .column _ qual n => do
    let (d, j) ← Eval.resolve (Γ.map Entry.shape) qual n
    let e ← Γ[d]?
    let c ← e.table.columns[j]?
    (tyOfName s c.type).map (·.1)
  | .int .. => some .int
  | .bool .. => some .bool
  | .arg _ n _ => st.args.lookup n
  | .cast _ _ tn => (tyOfName s tn).map (·.1)
  | .binary _ op a b =>
    if op = "+" ∨ op = "-" ∨ op = "*" then some ((peek Γ st a <|> peek Γ st b).getD .int)
    else some .bool
  | .call _ f args =>
    if f = "now" ∧ args = [] then some .ts
    else match args with
      | a :: _ => peek Γ st a
      | [] => none
  | .exists .. | .isNull .. | .unary .. => some .bool
  | _ => none

/-- A string literal: an enum label when the context expects that enum. -/
def strLit (hint : Option Ty) (v : String) : TM (IR.Expr × T) :=
  match hint with
  | some (.enum n) => do
    check (((s.enums.find? (·.1 == n)).map (·.2.contains v)).getD false) s!"'{v}' is not a label of {n}"
    pure (.enumLit n v, { ty := .enum n })
  | _ => pure (.text v, { ty := .text })

/-- The code of an expression and its type. `hint` is the type the context
expects, for parameters and enum labels. -/
def trExpr (Γ : Scope) : Option Ty → Expr → TM (IR.Expr × T)
  | _, .column _ qual n => do
    let (d, j) ← need (Eval.resolve (Γ.map Entry.shape) qual n) s!"unknown or ambiguous column {n}"
    let e ← need Γ[d]? "unknown column"
    let c ← need e.table.columns[j]? "unknown column"
    let t ← need (colT s c) s!"the type of {n} is not supported"
    pure (.col d j e.var n, t)
  | _, .int _ v => do
    check (Width.w64.fits v) "the literal does not fit in bigint"
    pure (.int v, { ty := .int, width := if Width.w32.fits v then .w32 else .w64 })
  | _, .bool _ b => pure (.bool b, { ty := .bool })
  | hint, .str _ v => strLit s hint v
  | _, .null _ => reject "NULL literals are not supported here"
  | hint, .arg _ n nullable => do
    check (!nullable) "sqlc.narg is not supported yet"
    let t ← argType n hint
    pure (.arg n (t = .bool), { ty := t, width := .w16 })
  | _, .cast _ inner tn => do
    let tgt ← need (Eval.targetOf s tn) "this cast is not supported"
    typeArg inner tgt.ty
    let (ie, t) ← trExpr Γ (some tgt.ty) inner
    check (!ie.isEnumLit) "a cast of a string to an enum is not supported"
    castCode tgt ie t
  | _, .binary _ op a b =>
    match Eval.BinOp.ofString op with
    | some .and => do
      let (ia, ta) ← trExpr Γ (some .bool) a
      let (ib, tb) ← trExpr Γ (some .bool) b
      check (ta.ty = .bool ∧ tb.ty = .bool) "AND needs booleans"
      pure (.and ia ib, { ty := .bool })
    | some .or => do
      let (ia, ta) ← trExpr Γ (some .bool) a
      let (ib, tb) ← trExpr Γ (some .bool) b
      check (ta.ty = .bool ∧ tb.ty = .bool) "OR needs booleans"
      pure (.or ia ib, { ty := .bool })
    | some bop => do
      let st ← get
      let pa := peek s Γ st a
      let pb := peek s Γ st b
      let (ia, ta) ← trExpr Γ (pb <|> (pa <|> pb)) a
      let (ib, tb) ← trExpr Γ (some ta.ty) b
      check (!(ta.nullable || tb.nullable)) "operators on nullable values are not supported yet"
      binCode bop ia ta ib tb
    | none => reject s!"the operator '{op}' is not supported"
  | _, .unary sp op a =>
    match Eval.constInt? (.unary sp op a) with
    | some n => do
      check (Width.w64.fits n) "the literal does not fit in bigint"
      pure (.int n, { ty := .int, width := if Width.w32.fits n then .w32 else .w64 })
    | none =>
    if op = "not" then do
      let (ia, ta) ← trExpr Γ (some .bool) a
      check (ta.ty = .bool) "NOT needs a boolean"
      pure (.not ia, { ty := .bool })
    else if op = "-" then do
      let (ia, ta) ← trExpr Γ (some .int) a
      check (ta.ty = .int ∧ !ta.nullable ∧ ta.width = .w64) "'-' needs a bigint"
      pure (.neg ia, ta)
    else reject s!"the operator '{op}' is not supported"
  | _, .isNull _ inner negated => do
    let (ie, t) ← trExpr Γ none inner
    check (t.nullable || ie.isCol) "IS NULL on this expression is not supported"
    pure (.isNull negated t.nullable ie, { ty := .bool })
  | hint, .call _ f args =>
    match Eval.Fn.ofString f, args with
    | some .now, [] => pure (.now, { ty := .ts })
    | some .least, [a, b] => do
      let (ia, ta) ← trExpr Γ (some .int) a
      let (ib, tb) ← trExpr Γ (some .int) b
      check (ta.ty = .int ∧ tb.ty = .int ∧ !ta.nullable ∧ !tb.nullable) "LEAST is supported on numbers that are not NULL"
      pure (.least ia ib, { ty := .int, width := ta.width.max tb.width })
    | some .coalesce, [a, b] => do
      let (ia, ta) ← trExpr Γ hint a
      let (ib, tb) ← trExpr Γ (some ta.ty) b
      check (!ia.isEnumLit && !ib.isEnumLit) "COALESCE of an enum label is not supported"
      check (ta.ty = tb.ty ∧ ta.ty ≠ .bool) "COALESCE needs one type that is not boolean"
      check (ta.ty ≠ .int ∨ ta.width = tb.width) "COALESCE of integers of two widths is not supported yet"
      pure (.coalesce ta.nullable ia ib, if ta.nullable then tb else ta)
    | _, _ => reject s!"the function {f} is not supported"
  | _, .typedLit .. => reject "typed literals are not supported"
  | _, .exists .. => reject "EXISTS is not supported yet"
  | _, .subquery .. => reject "subqueries are not supported yet"

end

/-! ## `SELECT` -/

/-- The conditions joined by `AND` at the top of `e`. -/
def conjuncts : Expr → List Expr
  | .binary sp op a b =>
    if Eval.BinOp.ofString op = some .and then conjuncts a ++ conjuncts b else [.binary sp op a b]
  | e => [e]

mutual

/-- Does `e` read the alias `a`? An unqualified column could belong to any
table, so it reads every alias. -/
def reads (a : String) : Expr → Bool
  | .column _ (some q') _ => q' == a
  | .column _ none _ => true
  | .cast _ x _ | .unary _ _ x | .isNull _ x _ => reads a x
  | .binary _ _ x y => reads a x || reads a y
  | .call _ _ xs => readsList a xs
  | _ => false

def readsList (a : String) : List Expr → Bool
  | [] => false
  | x :: xs => reads a x || readsList a xs

end

/-- `e` may give the key of `alias`: it reads neither `alias` nor a table
after it. -/
def keyOK (alias : String) (unbound : List String) (e : Expr) : Bool :=
  !unbound.any (reads · e) && !reads alias e

/-- The key that the condition `c` gives `alias`, whose key column is `k`,
with the qualifier of the column. As in the string translation, only the
left side of `=` is tried when it is a column. -/
def keyCand (alias k : String) (unbound : List String) (c : Expr) : Option (Option String × Expr) :=
  match c with
  | .binary _ op l r =>
    if op = "=" then
      match l with
      | .column _ qual col =>
        if qual.all (· == alias) && col == k && keyOK alias unbound r then some (qual, r) else none
      | _ =>
        match r with
        | .column _ qual col =>
          if qual.all (· == alias) && col == k && keyOK alias unbound l then some (qual, l) else none
        | _ => none
    else none
  | _ => none

def keyFor (alias k : String) (unbound : List String) : List Expr → Option (Option String × Expr)
  | [] => none
  | c :: cs =>
    match keyCand alias k unbound c with
    | some r => some r
    | none => keyFor alias k unbound cs

section
variable (s : Schema)

/-- The aliases of `FROM`, in order, with the variables the string
translation gives them. -/
def entries : List FromItem → Nat → TM (List Entry)
  | [], _ => pure []
  | .mk table alias _ :: rest, n => do
    let t ← need (s.table? table) s!"the table {table} is not in the schema"
    let es ← entries rest (n + 1)
    pure ({ alias, table := t, var := s!"r_{alias}_{n}" } :: es)

/-- The lookup of each alias of `items`, in order. `before` is the scope of
the aliases before them, innermost first, and `full` the scope of them all. -/
def trLookups (conds : List Expr) (full : List Eval.Shape) : Scope → List Entry → TM (List IR.Lookup)
  | _, [] => pure []
  | before, e :: rest => do
    let k ← need (single? e.table.primaryKey) s!"{e.table.name} needs a primary key of one column"
    let (qual, key) ← need (keyFor e.alias k (rest.map (·.alias)) conds)
      s!"reading {e.table.name} needs a condition {e.alias}.{k} = …; a full scan is not supported"
    let j ← need (Eval.colIndex e.table k) "no key column"
    check (Eval.resolve full qual k = some (rest.length, j)) "the key column is ambiguous"
    let c ← need e.table.columns[j]? "no key column"
    let kt ← need (colT s c) "the type of the key is not supported"
    let (ik, tk) ← trExpr s before (some kt.ty) key
    check (!ik.isEnumLit && tk.ty = kt.ty && !tk.nullable) "the key has the wrong type"
    let ls ← trLookups conds full (e :: before) rest
    pure ({ table := e.table.name, var := e.var, keyIndex := j, key := ik } :: ls)

def trConds (Γ : Scope) : List Expr → TM (List IR.Expr)
  | [] => pure []
  | c :: cs => do
    let (ic, t) ← trExpr s Γ (some .bool) c
    check (t.ty = .bool) "a condition must be a boolean"
    let rest ← trConds Γ cs
    pure (ic :: rest)

def trOuts (Γ : Scope) : List Expr → TM (List (IR.Expr × T))
  | [] => pure []
  | e :: es => do
    let r ← trExpr s Γ none e
    let rest ← trOuts Γ es
    pure (r :: rest)

def itemName (i : Nat) : SelectItem → String
  | .mk _ (some a) => a
  | .mk (.column _ _ n) none => n
  | .mk (.cast _ (.column _ _ n) _) none => n
  | .mk _ none => s!"column{i + 1}"

/-- The conditions of every `ON` and of `WHERE`, split at `AND`. -/
def condsOf (from_ : List FromItem) (where_ : Option Expr) : List Expr :=
  (from_.filterMap Eval.onOf).flatMap conjuncts ++ ((where_.map conjuncts).getD [])

def trSelect (sel : Select) : TM (IR.Select × List (String × TyN)) := do
  let .mk _ items from_ where_ _ := sel
  let es ← entries s from_ 1
  check (Eval.distinct (es.map (·.alias))) "an alias is used twice"
  let conds := condsOf from_ where_
  let full := es.reverse
  let ls ← trLookups s conds (full.map Entry.shape) [] es
  let ics ← trConds s full conds
  let outs ← trOuts s full (items.map Eval.itemExpr)
  let cols := (items.zipIdx.zip outs).map fun ((it, i), (_, t)) => (itemName i it, t.tyN)
  pure ({ lookups := ls, conds := ics, outs := outs.map (·.1) }, cols)

/-- The plan of a query, or why this part refuses it. -/
def translate (nq : NamedQuery) (qy : Query) : Except String IR.Query := do
  let some kind := Eval.Kind.ofString nq.kind | throw s!"a query with :{nq.kind} is not supported"
  match qy.ctes, qy.main with
  | [], .select sel => do
    let ((isel, cols), st) ← (trSelect s sel).run {}
    if kind = .many ∧ cols.any (·.2.ty = .bool) then throw "a :many query returning booleans is not supported yet"
    pure { name := nq.name, args := st.args, kind, select := isel, columns := cols }
  | _, _ => throw "only a SELECT without WITH is supported"

end

end tolean.Sql.Plan
