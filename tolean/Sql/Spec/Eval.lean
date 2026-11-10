import tolean.Sql.Schema
import tolean.Sql.Spec.Basic

/-!
The meaning of the PostgreSQL subset: an interpreter for queries, over a
database whose tables are lists of rows.

This file is the specification that `translate_sound` in
`tolean/Sql/Proof/Query.lean` proves the translator against. It reads the
source syntax of `tolean/Sql/Syntax.lean` directly, and it knows nothing of
the translator:

- A table is a list of rows, and a row is a list of values, one for each
  column of the table in the schema. A `SELECT` scans every table in its
  `FROM` clause, row by row, as nested loops. It never looks a row up by its
  key.
- Names resolve as PostgreSQL resolves them: `a.x` is the column `x` of the
  table that the alias `a` names, and `x` alone is the one column called `x`
  among the tables in `FROM`. A name that two tables share is ambiguous.
- The conditions of every `JOIN … ON` and the `WHERE` form one conjunction,
  as they do in PostgreSQL for inner joins.
- Values follow PostgreSQL's three-valued logic and its errors, as
  `tolean/Sql/Spec/Basic.lean` states them, including the rule that `AND` and
  `OR` raise an error only when every order of evaluation must.
- Integers carry the width of their type, `smallint`, `integer` or `bigint`.
  Arithmetic gives the wider of the two widths and raises `outOfRange` when
  the result leaves it, as PostgreSQL does.
- A minus sign before an integer literal is part of the literal, as in
  PostgreSQL's grammar. So `-2147483648` is an `integer`, although
  `2147483648` is a `bigint`.

The interpreter is untyped: it follows the values. It gives no meaning to a
query outside the subset, such as a type error or an unsupported construct,
and reports `Fault.stuck` there. Where PostgreSQL picks a meaning from static
types that values do not show, the interpreter can differ from PostgreSQL,
and the translator refuses the queries where that matters. The interpreter
compares a string with an enum value by the label, which PostgreSQL does
only for a string literal. `COALESCE` gives the value it picks, with its own
width, but PostgreSQL converts that value to the widest type of all the
arguments.
-/
namespace tolean.Sql.Eval

open tolean tolean.Sql

/-! ## Values -/

/-- The width of an integer type. -/
inductive Width where
  | w16 | w32 | w64
deriving DecidableEq, Repr, Inhabited

/-- Whether `x` fits a type of width `w`. -/
def Width.fits : Width → Int → Bool
  | .w16, x => decide (-2 ^ 15 ≤ x ∧ x < 2 ^ 15)
  | .w32, x => decide (-2 ^ 31 ≤ x ∧ x < 2 ^ 31)
  | .w64, x => decide (-2 ^ 63 ≤ x ∧ x < 2 ^ 63)

/-- The result type of an operator on two integer types: the wider one. -/
def Width.max : Width → Width → Width
  | .w64, _ | _, .w64 => .w64
  | .w32, _ | _, .w32 => .w32
  | .w16, .w16 => .w16

/-- A value of the subset. `null` is SQL's NULL, of any type. -/
inductive Val where
  | null
  | int (w : Width) (n : Int)
  | bool (b : Bool)
  | text (s : String)
  | uuid (u : Pg.UUID)
  | ts (t : Pg.Timestamp)
  | json (j : Pg.Json)
  | bytes (b : Pg.Bytes)
  | enum (type label : String)
deriving DecidableEq, Inhabited

/-- Why an evaluation gives no value: a PostgreSQL error, or a query that the
subset gives no meaning. -/
inductive Fault where
  | error (e : Pg.Error)
  | stuck
deriving DecidableEq, Repr, Inhabited

abbrev M := Except Fault

def raise {A : Type} (e : Pg.Error) : M A := .error (.error e)

def stuck {A : Type} : M A := .error .stuck

/-! ## Operators -/

/-- An integer literal: an `integer` when it fits, else a `bigint`, as
PostgreSQL types it. A larger literal is a `numeric`, which the subset leaves
out. -/
def intLit (n : Int) : M Val :=
  if Width.w32.fits n then pure (.int .w32 n)
  else if Width.w64.fits n then pure (.int .w64 n)
  else stuck

/-- The truth value of a condition: NULL is `none`. -/
def truth : Val → M (Option Bool)
  | .null => pure none
  | .bool b => pure (some b)
  | _ => stuck

def ofTruth : Option Bool → Val
  | none => .null
  | some b => .bool b

/-- `a AND b` in three-valued logic. Like `Pg.and3`, it raises an error only
when no side is false. -/
def and3 {ε : Type} (a b : Except ε (Option Bool)) : Except ε (Option Bool) :=
  match a, b with
  | .ok (some false), _ => .ok (some false)
  | _, .ok (some false) => .ok (some false)
  | .error e, _ => .error e
  | _, .error e => .error e
  | .ok (some true), .ok x => .ok x
  | .ok none, .ok _ => .ok none

/-- `a OR b` in three-valued logic, the dual of `and3`. -/
def or3 {ε : Type} (a b : Except ε (Option Bool)) : Except ε (Option Bool) :=
  match a, b with
  | .ok (some true), _ => .ok (some true)
  | _, .ok (some true) => .ok (some true)
  | .error e, _ => .error e
  | _, .error e => .error e
  | .ok (some false), .ok x => .ok x
  | .ok none, .ok _ => .ok none

def andM (a b : M Val) : M Val := ofTruth <$> and3 (a >>= truth) (b >>= truth)

def orM (a b : M Val) : M Val := ofTruth <$> or3 (a >>= truth) (b >>= truth)

def notM (a : M Val) : M Val := do
  let t ← truth (← a)
  pure (ofTruth (t.map not))

/-- `a = b`. NULL on either side gives NULL. A string compares with an enum
value by its label, as a string literal does in PostgreSQL. `jsonb` equality
is not textual, so the subset leaves it out. -/
def eq3 : Val → Val → M (Option Bool)
  | .null, _ => pure none
  | _, .null => pure none
  | .int _ a, .int _ b => pure (some (a == b))
  | .bool a, .bool b => pure (some (a == b))
  | .text a, .text b => pure (some (a == b))
  | .uuid a, .uuid b => pure (some (a == b))
  | .ts a, .ts b => pure (some (a == b))
  | .bytes a, .bytes b => pure (some (a == b))
  | .enum t a, .enum t' b => if t = t' then pure (some (a == b)) else stuck
  | .enum _ a, .text b => pure (some (a == b))
  | .text a, .enum _ b => pure (some (a == b))
  | _, _ => stuck

def eqM (ne : Bool) (a b : M Val) : M Val := do
  let t ← eq3 (← a) (← b)
  pure (ofTruth (t.map (· != ne)))

/-- The orders on integers. -/
inductive CmpOp where
  | lt | le | gt | ge
deriving DecidableEq, Repr, Inhabited

def CmpOp.test : CmpOp → Int → Int → Bool
  | .lt, a, b => decide (a < b)
  | .le, a, b => decide (a ≤ b)
  | .gt, a, b => decide (a > b)
  | .ge, a, b => decide (a ≥ b)

def cmp3 (op : CmpOp) : Val → Val → M (Option Bool)
  | .null, _ => pure none
  | _, .null => pure none
  | .int _ a, .int _ b => pure (some (op.test a b))
  | _, _ => stuck

def cmpM (op : CmpOp) (a b : M Val) : M Val := do
  let t ← cmp3 op (← a) (← b)
  pure (ofTruth t)

inductive ArithOp where
  | add | sub | mul
deriving DecidableEq, Repr, Inhabited

def ArithOp.apply : ArithOp → Int → Int → Int
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b

/-- An integer of width `w`, or `outOfRange`. -/
def intOf (w : Width) (n : Int) : M Val :=
  if w.fits n then pure (.int w n) else raise .outOfRange

def arith3 (op : ArithOp) : Val → Val → M Val
  | .null, _ => pure .null
  | _, .null => pure .null
  | .int w a, .int w' b => intOf (w.max w') (op.apply a b)
  | _, _ => stuck

def arithM (op : ArithOp) (a b : M Val) : M Val := do arith3 op (← a) (← b)

def negM (a : M Val) : M Val := do
  match ← a with
  | .null => pure .null
  | .int w n => intOf w (-n)
  | _ => stuck

def isNullM (negated : Bool) (a : M Val) : M Val := do
  match ← a with
  | .null => pure (.bool !negated)
  | _ => pure (.bool negated)

/-- `COALESCE(a, b)`: `a`, unless it is NULL. -/
def coalesceM (a b : M Val) : M Val := do
  match ← a with
  | .null => b
  | v => pure v

/-- `LEAST(a, b)`, which skips NULLs, on integers. -/
def least2 : Val → Val → M Val
  | .null, b => pure b
  | a, .null => pure a
  | .int w a, .int w' b => pure (.int (w.max w') (min a b))
  | _, _ => stuck

def leastM (a b : M Val) : M Val := do least2 (← a) (← b)

/-! ## Casts -/

/-- A type that a cast can name. An enum carries its labels. -/
inductive Target where
  | int (w : Width)
  | bool
  | text
  | uuid
  | enum (name : String) (labels : List String)
deriving DecidableEq, Repr, Inhabited

/-- The target of `::tn`, after domains resolve. Timestamps, `jsonb`, `bytea`
and types with modifiers are left out. -/
def targetOf (s : Schema) (tn : TypeName) : Option Target :=
  let tn := s.resolve tn
  if tn.array then none
  else match canonicalType tn with
    | "bigint" => some (.int .w64)
    | "integer" => some (.int .w32)
    | "smallint" => some (.int .w16)
    | "boolean" => some .bool
    | "text" => some .text
    | "uuid" => some .uuid
    | n => (s.enums.find? (·.1 == n)).map fun (_, labels) => .enum n labels

/-- The value of `v::t`. -/
def castVal : Target → Val → M Val
  | _, .null => pure .null
  | .int w, .int _ n => intOf w n
  | .bool, .bool b => pure (.bool b)
  | .text, .text s => pure (.text s)
  | .text, .enum _ l => pure (.text l)
  | .uuid, .uuid u => pure (.uuid u)
  | .enum n _, .enum n' l => if n = n' then pure (.enum n l) else stuck
  | .enum n labels, .text l => if labels.contains l then pure (.enum n l) else stuck
  | _, _ => stuck

/-! ## Names -/

/-- What the interpreter knows of a binding when it resolves a name. -/
abbrev Shape := String × Table

/-- The index of the first element with alias `a`. -/
def aliasIndex : List Shape → String → Option Nat
  | [], _ => none
  | (b, _) :: rest, a => if b = a then some 0 else (aliasIndex rest a).map (· + 1)

/-- The index of the column `n` in `t`. -/
def colIndex (t : Table) (n : String) : Option Nat :=
  go t.columns
where
  go : List Column → Option Nat
    | [] => none
    | c :: cs => if c.name = n then some 0 else (go cs).map (· + 1)

/-- The bindings, from index `i` on, whose table has a column `n`, with
that column's index. -/
def hits (n : String) : List Shape → Nat → List (Nat × Nat)
  | [], _ => []
  | (_, t) :: rest, i =>
    match colIndex t n with
    | some j => (i, j) :: hits n rest (i + 1)
    | none => hits n rest (i + 1)

/-- The binding and column that a column reference names: for `a.n`, the
table that `a` names; for `n` alone, the only table with a column `n`. -/
def resolve (scope : List Shape) : Option String → String → Option (Nat × Nat)
  | some a, n => do
    let i ← aliasIndex scope a
    let (_, t) ← scope[i]?
    let j ← colIndex t n
    pure (i, j)
  | none, n =>
    match hits n scope 0 with
    | [h] => some h
    | _ => none

/-! ## Evaluation -/

abbrev Row := List Val

/-- The rows of each table, by name. -/
abbrev DB := String → List Row

/-- What a query reads besides its source: the database, `now()`, and the
values of its `sqlc.arg` parameters. -/
structure Input where
  db : DB
  now : Pg.Timestamp
  args : List (String × Val)

/-- A row bound to an alias of a `FROM` item. -/
structure Binding where
  alias : String
  table : Table
  row : Row

def Binding.shape (b : Binding) : Shape := (b.alias, b.table)

/-- The value of the column at `(i, j)`: column `j` of the `i`-th binding. -/
def column (env : List Binding) (ij : Nat × Nat) : M Val :=
  match env[ij.1]? with
  | some b => match b.row[ij.2]? with
    | some v => pure v
    | none => stuck
  | none => stuck

inductive BinOp where
  | and | or | arith (op : ArithOp) | eq | ne | cmp (op : CmpOp)
deriving DecidableEq, Repr, Inhabited

def BinOp.ofString : String → Option BinOp
  | "and" => some .and
  | "or" => some .or
  | "+" => some (.arith .add)
  | "-" => some (.arith .sub)
  | "*" => some (.arith .mul)
  | "=" => some .eq
  | "<>" => some .ne
  | "<" => some (.cmp .lt)
  | "<=" => some (.cmp .le)
  | ">" => some (.cmp .gt)
  | ">=" => some (.cmp .ge)
  | _ => none

def binary : Option BinOp → M Val → M Val → M Val
  | some .and, a, b => andM a b
  | some .or, a, b => orM a b
  | some (.arith op), a, b => arithM op a b
  | some .eq, a, b => eqM false a b
  | some .ne, a, b => eqM true a b
  | some (.cmp op), a, b => cmpM op a b
  | none, _, _ => stuck

/-- The value of an integer literal with minus signs before it. PostgreSQL's
grammar folds such a minus into the literal. -/
def constInt? : Expr → Option Int
  | .int _ n => some n
  | .unary _ op a => if op = "-" then (constInt? a).map (- ·) else none
  | _ => none

def unary (op : String) (a : M Val) : M Val :=
  if op = "not" then notM a
  else if op = "-" then negM a
  else stuck

/-- The functions of the subset. -/
inductive Fn where
  | now | coalesce | least
deriving DecidableEq, Repr, Inhabited

def Fn.ofString : String → Option Fn
  | "now" => some .now
  | "coalesce" => some .coalesce
  | "least" => some .least
  | _ => none

section
variable (s : Schema) (i : Input)

mutual

/-- The value of an expression. The innermost binding comes first in
`env`. -/
def eval (env : List Binding) : Expr → M Val
  | .column _ q n =>
    match resolve (env.map Binding.shape) q n with
    | some ij => column env ij
    | none => stuck
  | .int _ n => intLit n
  | .str _ v => pure (.text v)
  | .bool _ b => pure (.bool b)
  | .null _ => pure .null
  | .arg _ n _ =>
    match i.args.lookup n with
    | some v => pure v
    | none => stuck
  | .cast _ e tn =>
    match targetOf s tn with
    | some t => eval env e >>= castVal t
    | none => stuck
  | .typedLit .. => stuck
  | .binary _ op a b => binary (BinOp.ofString op) (eval env a) (eval env b)
  | .unary sp op a =>
    match constInt? (.unary sp op a) with
    | some n => intLit n
    | none => unary op (eval env a)
  | .isNull _ a negated => isNullM negated (eval env a)
  | .call _ f args => evalCall env (Fn.ofString f) args
  | .exists .. => stuck
  | .subquery .. => stuck

/-- A call of `f`: `now()`; `COALESCE`, the first argument that is not NULL;
`LEAST`, the smallest argument that is not NULL. -/
def evalCall (env : List Binding) (f : Option Fn) : List Expr → M Val
  | [] =>
    if f = some .now then pure (.ts i.now)
    else if f = some .coalesce then pure .null
    else stuck
  | a :: rest =>
    if f = some .coalesce then coalesceM (eval env a) (evalCall env f rest)
    else if f = some .least then
      if rest.isEmpty then eval env a else leastM (eval env a) (evalCall env f rest)
    else stuck

end

/-- The conjunction of conditions. -/
def andAll : List (M (Option Bool)) → M (Option Bool)
  | [] => pure (some true)
  | [c] => c
  | c :: cs => and3 c (andAll cs)

def flatMapM {ε α β : Type} : List α → (α → Except ε (List β)) → Except ε (List β)
  | [], _ => .ok []
  | x :: xs, f => do
    let ys ← f x
    let rest ← flatMapM xs f
    return ys ++ rest

/-- The output row for the bindings `env`, if the condition holds. -/
def emit (conds : List Expr) (items : List Expr) (env : List Binding) : M (List Row) := do
  let c ← andAll (conds.map fun e => eval s i env e >>= truth)
  if c = some true then
    let row ← items.mapM (eval s i env)
    pure [row]
  else pure []

/-- Nested loops over the tables of `FROM`: every row of each table, in
order. -/
def scan (body : List Binding → M (List Row)) : List Shape → List Binding → M (List Row)
  | [], env => body env
  | (a, t) :: rest, env => flatMapM (i.db t.name) fun r => scan body rest ({ alias := a, table := t, row := r } :: env)

/-- The tables of `FROM`, from the schema. -/
def fromShapes : List FromItem → M (List Shape)
  | [] => pure []
  | .mk table a _ :: rest => do
    match s.table? table with
    | some t => pure ((a, t) :: (← fromShapes rest))
    | none => stuck

/-- The condition of a `JOIN … ON`. -/
def onOf : FromItem → Option Expr
  | .mk _ _ on => on

def itemExpr : SelectItem → Expr
  | .mk e _ => e

/-- No name twice. -/
def distinct : List String → Bool
  | [] => true
  | a :: rest => !rest.contains a && distinct rest

/-- The rows of a `SELECT`. `FOR UPDATE` only takes locks, so it does not
change them. -/
def select (sel : Select) : M (List Row) := do
  let .mk _ items from_ where_ _ := sel
  let shapes ← fromShapes s from_
  if !distinct (shapes.map (·.1)) then stuck
  let conds := from_.filterMap onOf ++ where_.toList
  scan i (emit s i conds (items.map itemExpr)) shapes []

/-- The kinds of sqlc queries in the subset. -/
inductive Kind where
  | one | many
deriving DecidableEq, Repr, Inhabited

def Kind.ofString : String → Option Kind
  | "one" => some .one
  | "many" => some .many
  | _ => none

/-- What a query of kind `k` returns from its rows: `:one` the first row, or
`noRows`. -/
def Kind.result : Kind → List Row → M (List Row)
  | .one, [] => raise .noRows
  | .one, r :: _ => pure [r]
  | .many, rows => pure rows

/-- A query: the rows it returns and the database after it. -/
def run (kind : String) (q : Query) : M (List Row × DB) :=
  match q.ctes, q.main, Kind.ofString kind with
  | [], .select sel, some k => do
    let rows ← select s i sel
    pure (← k.result rows, i.db)
  | _, _, _ => stuck

end

end tolean.Sql.Eval
