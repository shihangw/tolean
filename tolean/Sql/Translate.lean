import tolean.Sql.Schema

/-!
The SQL translator. It writes the schema of the reached tables (see
`tolean/Sql/Schema.lean`), then one Lean function for each root query:

```
def Q (now : Pg.Timestamp) (args…) (db : DB) : Pg.Result (result × DB)
```

- Every table in `FROM` and every `UPDATE` target must be reached through its
  primary key, by a condition `alias.key = e` where `e` does not read the
  table. Tolean refuses a full scan. With the invariant `Valid db`, which says
  each row sits under its own key, the lookup gives the same rows as a scan.
- Every part of a statement reads the snapshot `db` from before the
  statement, as data-modifying `WITH` queries do in PostgreSQL, and the
  updates are written at the end.
- Conditions are three-valued and errors follow `tolean/Sql/Spec/Basic.lean`.
- `FOR UPDATE` only takes locks, so it does not change the result.
-/
namespace tolean.Sql.Translate

open tolean tolean.Sql

inductive Ty where
  | int
  | bool
  | text
  | uuid
  | ts
  | json
  | bytes
  | enum (name : String)
deriving BEq, Inhabited, Repr

def Ty.enumName : Ty → String
  | .enum n => n
  | _ => ""

structure TyN where
  ty : Ty
  nullable : Bool
deriving BEq, Inhabited

/-- What an alias stands for: a table row, or a row of a `WITH` query. -/
inductive Source where
  | row (table : Table)
  | cte (columns : List (String × TyN))

structure Binding where
  alias : String
  source : Source
  /-- The Lean variable that holds the row. -/
  var : String

structure Cte where
  name : String
  columns : List (String × TyN)
  rowsVar : String
  /-- The tables a `SELECT` in `WITH` reads, and whether it locks them. -/
  reads : List String := []
  locked : Bool := false

structure TState where
  schema : Schema
  args : Array (String × Ty) := #[]
  fresh : Nat := 0
  ctes : List Cte := []
  path : String := ""
  /-- Added to a line in a query's source to give the line in its file. -/
  lineOffset : Nat := 0

abbrev TM := StateT TState (Except String)

def fail {A : Type} (span : Span) (m : String) : TM A := do
  let s ← get
  throw s!"{s.path}:{span.start.line + s.lineOffset}:{span.start.col}: {m}"

def freshVar (base : String) : TM String := do
  modify fun s => { s with fresh := s.fresh + 1 }
  return s!"{base}_{(← get).fresh}"

def q (n : String) : String := s!"«{n}»"

def tyOf (s : Schema) (tn : TypeName) : Except String Ty := do
  let tn := s.resolve tn
  if tn.array then throw s!"the array type {canonicalType tn} is not supported in queries"
  match canonicalType tn with
  | "bigint" | "integer" | "smallint" => return .int
  | "boolean" => return .bool
  | "text" | "character varying" => return .text
  | "uuid" => return .uuid
  | "timestamp with time zone" | "timestamp without time zone" => return .ts
  | "jsonb" | "json" => return .json
  | "bytea" => return .bytes
  | n => if s.enums.any (·.1 == n) then return .enum n else throw s!"the type {n} is not supported"

def liftE {A : Type} (span : Span) (x : Except String A) : TM A :=
  match x with
  | .ok v => pure v
  | .error m => fail span m

def leanTy : Ty → String
  | .int => "Int"
  | .bool => "Bool"
  | .text => "String"
  | .uuid => "Pg.UUID"
  | .ts => "Pg.Timestamp"
  | .json => "Pg.Json"
  | .bytes => "Pg.Bytes"
  | .enum n => q n

/-- The Lean type of a value in generated code. Booleans are always three
valued there. -/
def valueTy (t : TyN) : String :=
  if t.ty == .bool then "(Option Bool)"
  else if t.nullable then s!"(Option {leanTy t.ty})" else leanTy t.ty

/-- The type of a result column. A boolean that cannot be NULL is a `Bool`. -/
def resultTy (t : TyN) : String :=
  if t.nullable then s!"(Option {leanTy t.ty})" else leanTy t.ty

def tupleTy : List String → String
  | [] => "Unit"
  | [t] => t
  | ts => "(" ++ " × ".intercalate ts ++ ")"

/-- The `i`-th of `n` parts of the tuple `v`. -/
def tupleGet (v : String) (i n : Nat) : String :=
  if n == 1 then v
  else
    let seconds := String.join (List.replicate i ".2")
    if i == n - 1 then v ++ seconds else v ++ seconds ++ ".1"

def tupleOf : List String → String
  | [] => "()"
  | [x] => x
  | xs => "(" ++ ", ".intercalate xs ++ ")"

/-! ## Names -/

def resolveColumn (env : List Binding) (span : Span) (qual : Option String) (name : String) :
    TM (String × TyN) := do
  let candidates := env.filter fun b => match qual with
    | some a => b.alias == a
    | none => match b.source with
      | .row t => (t.column? name).isSome
      | .cte cs => cs.any (·.1 == name)
  match candidates with
  | b :: _ =>
    match b.source with
    | .row t =>
      let some c := t.column? name | fail span s!"no column {name} in {t.name}"
      let ty ← liftE span (tyOf (← get).schema c.type)
      return (s!"{b.var}.{q name}", { ty, nullable := !c.notNull })
    | .cte cs =>
      match cs.findIdx? (·.1 == name) with
      | some i => return (tupleGet b.var i cs.length, cs[i]!.2)
      | none => fail span s!"no column {name} in {b.alias}"
  | [] => fail span s!"unknown column {(qual.map (· ++ ".")).getD ""}{name}"

def argTy? (n : String) : TM (Option Ty) := do
  return ((← get).args.find? (·.1 == n)).map (·.2)

def setArgTy (span : Span) (n : String) (t : Ty) : TM Unit := do
  match ← argTy? n with
  | some t' => if t' != t then fail span s!"sqlc.arg({n}) is used with two types"
  | none => modify fun s => { s with args := s.args.push (n, t) }

/-! ## Types without code -/

mutual

/-- The type of an expression, if it can be known without a hint. -/
partial def peekTy (env : List Binding) (e : Expr) : TM (Option TyN) := do
  match e with
  | .column s qual n => return some (← resolveColumn env s qual n).2
  | .int .. => return some { ty := .int, nullable := false }
  | .bool .. => return some { ty := .bool, nullable := false }
  | .arg _ n nullable => return (← argTy? n).map ({ ty := ·, nullable })
  | .cast s _ tn => return some { ty := ← liftE s (tyOf (← get).schema tn), nullable := false }
  | .binary _ op a b =>
    if ["+", "-", "*"].contains op then
      return some (((← peekTy env a) <|> (← peekTy env b)).getD { ty := .int, nullable := false })
    return some { ty := .bool, nullable := false }
  | .call _ "now" [] => return some { ty := .ts, nullable := false }
  | .call _ "coalesce" args =>
    -- NULL only when the last argument can be NULL.
    let first ← (args.head?.map (peekTy env)).getD (pure none)
    let last ← (args.getLast?.map (peekTy env)).getD (pure none)
    return first.map fun t => { t with nullable := (last.map (·.nullable)).getD true }
  | .call _ _ (a :: _) => peekTy env a
  | .exists .. | .isNull .. | .unary .. => return some { ty := .bool, nullable := false }
  | .subquery _ (.mk _ [.mk e _] from_ _ _) =>
    -- One column, and NULL when the subquery finds no row.
    let inner ← from_.foldlM (init := env) fun acc (.mk table alias _) => do
      match (← get).ctes.find? (·.name == table) with
      | some cte => return { alias, source := .cte cte.columns, var := "_" } :: acc
      | none =>
        match (← get).schema.table? table with
        | some t => return { alias, source := .row t, var := "_" } :: acc
        | none => return acc
    return (← peekTy inner e).map ({ · with nullable := true })
  | _ => return none

end

/-! ## Expressions -/

def compareOp : String → String
  | "<>" => "!="
  | "=" => "=="
  | op => op

mutual

/-- A Lean term of type `Pg.Result v` for the expression, and its type.
`hint` is the type the context expects, for arguments and enum literals. -/
partial def cExpr (env : List Binding) (e : Expr) (hint : Option Ty) : TM (String × TyN) := do
  match e with
  | .column s qual n =>
    let (code, t) ← resolveColumn env s qual n
    return (s!"pure {code}", t)
  | .int _ v => return (s!"pure ({v} : Int)", { ty := .int, nullable := false })
  | .bool _ v => return (s!"pure (some {v})", { ty := .bool, nullable := false })
  | .str s v =>
    match hint with
    | some (.enum n) =>
      let labels := (((← get).schema.enums.find? (·.1 == n)).map (·.2)).getD []
      if !labels.contains v then fail s s!"'{v}' is not a label of {n}"
      return (s!"pure (.{q v} : {q n})", { ty := .enum n, nullable := false })
    | _ => return (s!"pure {v.quote}", { ty := .text, nullable := false })
  | .null s => fail s "NULL literals are not supported here"
  | .arg s n nullable =>
    if nullable then fail s "sqlc.narg is not supported yet"
    let t ← match ← argTy? n with
      | some t => pure t
      | none => match hint with
        | some t => do setArgTy s n t; pure t
        | none => fail s s!"cannot tell the type of sqlc.arg({n}); cast it"
    let code := if t == .bool then s!"pure (some {q n})" else s!"pure {q n}"
    return (code, { ty := t, nullable := false })
  | .cast s inner tn =>
    let target ← liftE s (tyOf (← get).schema tn)
    if let .arg _ n _ := inner then setArgTy s n target
    let (code, t) ← cExpr env inner (some target)
    if t.ty == target then return (code, { t with ty := target })
    match t.ty, target with
    | .enum _, .text =>
      let conv := if t.nullable then s!"x.map {q t.ty.enumName}.text" else s!"{q t.ty.enumName}.text x"
      return (s!"(do let x ← {code}; pure ({conv}))", { ty := .text, nullable := t.nullable })
    | _, _ => fail s s!"this cast is not supported"
  | .binary s op a b =>
    if op == "and" || op == "or" then
      let (ca, _) ← cExpr env a (some .bool)
      let (cb, _) ← cExpr env b (some .bool)
      return (s!"(Pg.{op}3 ({ca}) ({cb}))", { ty := .bool, nullable := false })
    let ta ← peekTy env a
    let tb ← peekTy env b
    let h := ((ta <|> tb).map (·.ty))
    let (ca, ta') ← cExpr env a (tb.map (·.ty) <|> h)
    let (cb, tb') ← cExpr env b (some ta'.ty)
    if ta'.nullable || tb'.nullable then fail s "operators on nullable values are not supported yet"
    if ["+", "-", "*"].contains op then
      if ta'.ty != .int || tb'.ty != .int then fail s s!"'{op}' needs numbers"
      return (s!"(do let a ← {ca}; let b ← {cb}; Pg.int64 (a {op} b))", { ty := .int, nullable := false })
    if ["=", "<>", "<", "<=", ">", ">="].contains op then
      if ta'.ty != tb'.ty then fail s "the two sides have different types"
      if ta'.ty == .bool then fail s "comparing booleans is not supported"
      let lop := compareOp op
      let test := if op == "=" || op == "<>" then s!"a {lop} b" else s!"decide (a {lop} b)"
      if (op != "=" && op != "<>") && ta'.ty != .int then fail s s!"'{op}' is supported on numbers only"
      return (s!"(do let a ← {ca}; let b ← {cb}; pure (some ({test})))", { ty := .bool, nullable := false })
    fail s s!"the operator '{op}' is not supported"
  | .unary s op a =>
    if op == "not" then
      let (ca, _) ← cExpr env a (some .bool)
      return (s!"(Pg.not3 ({ca}))", { ty := .bool, nullable := false })
    if op == "-" then
      let (ca, t) ← cExpr env a (some .int)
      if t.ty != .int || t.nullable then fail s "'-' needs a number"
      return (s!"(do let a ← {ca}; Pg.int64 (-a))", t)
    fail s s!"the operator '{op}' is not supported"
  | .isNull _ inner negated =>
    let (c, t) ← cExpr env inner none
    let test := if negated then "isSome" else "isNone"
    if !t.nullable then return (s!"pure (some {negated})", { ty := .bool, nullable := false })
    return (s!"(do let x ← {c}; pure (some x.{test}))", { ty := .bool, nullable := false })
  | .call _ "now" [] => return ("pure now", { ty := .ts, nullable := false })
  | .call s "least" [a, b] =>
    let (ca, ta) ← cExpr env a (some .int)
    let (cb, tb) ← cExpr env b (some .int)
    if ta.ty != .int || tb.ty != .int || ta.nullable || tb.nullable then
      fail s "LEAST is supported on numbers that are not NULL"
    return (s!"(do let a ← {ca}; let b ← {cb}; pure (Pg.least a b))", { ty := .int, nullable := false })
  | .call s "coalesce" [a, b] =>
    let (ca, ta) ← cExpr env a hint
    let (cb, tb) ← cExpr env b (some ta.ty)
    if ta.ty != tb.ty then fail s "COALESCE needs one type"
    if ta.ty == .bool then fail s "COALESCE on booleans is not supported"
    if !ta.nullable then return (ca, ta)
    return (s!"(do let x ← {ca}; match x with | some v => pure v | none => {cb})", tb)
  | .call s name _ => fail s s!"the function {name} is not supported"
  | .exists _ sel =>
    let (rows, _) ← cSelect env sel
    return (s!"(do let rows ← {rows}; pure (some !rows.isEmpty))", { ty := .bool, nullable := false })
  | .subquery s sel =>
    let (rows, cols) ← cSelect env sel
    let [(_, t)] := cols | fail s "a scalar subquery must return one column"
    if t.nullable || t.ty == .bool then fail s "a scalar subquery of a nullable value is not supported"
    return (s!"(do let rows ← {rows}; Pg.scalar rows)", { t with nullable := true })
  | .typedLit s .. => fail s "typed literals are not supported in queries"

/-- The conditions joined by `AND` at the top of `e`. -/
partial def conjuncts : Expr → List Expr
  | .binary _ "and" a b => conjuncts a ++ conjuncts b
  | e => [e]

/-- Does `e` read the alias `a`? -/
partial def reads (a : String) (e : Expr) : Bool :=
  match e with
  | .column _ (some q') _ => q' == a
  -- An unqualified column could belong to any table in scope.
  | .column _ none _ => true
  | .cast _ x _ | .unary _ _ x | .isNull _ x _ => reads a x
  | .binary _ _ x y => reads a x || reads a y
  | .call _ _ xs => xs.any (reads a)
  | _ => false

/-- A condition `alias.key = e` among `conds`, where `e` reads none of
`unbound`: the key to look up. -/
partial def keyFor (t : Table) (alias : String) (unbound : List String) (conds : List Expr) :
    Option Expr :=
  match t.primaryKey with
  | [k] =>
    conds.findSome? fun c => match c with
      | .binary _ "=" (.column _ qual col) e =>
        if qual.all (· == alias) && col == k && !unbound.any (reads · e) && !reads alias e then some e else none
      | .binary _ "=" e (.column _ qual col) =>
        if qual.all (· == alias) && col == k && !unbound.any (reads · e) && !reads alias e then some e else none
      | _ => none
  | _ => none

/-- The rows of `FROM` items, nested: `inner` is the code with every alias
bound. Returns code of type `Pg.Result (List _)`. -/
partial def cFrom (env : List Binding) (items : List FromItem) (conds : List Expr)
    (inner : List Binding → TM String) (span : Span) : TM String := do
  match items with
  | [] => inner env
  | .mk table alias _ :: rest =>
    let unbound := rest.map fun (.mk _ a _) => a
    let var ← freshVar s!"r_{alias}"
    match (← get).ctes.find? (·.name == table) with
    | some cte =>
      let b : Binding := { alias, source := .cte cte.columns, var }
      let body ← cFrom (b :: env) rest conds inner span
      return s!"(Pg.flatMapM {cte.rowsVar} fun {var} => {body})"
    | none =>
      let some t := (← get).schema.table? table | fail span s!"the table {table} is not in the schema"
      let some key := keyFor t alias unbound conds
        | fail span s!"reading {table} needs a condition {alias}.{", ".intercalate t.primaryKey} = …; a full scan is not supported"
      let (ck, _) ← cExpr env key (some (← liftE span (tyOf (← get).schema (t.column? t.primaryKey.head!).get!.type)))
      let b : Binding := { alias, source := .row t, var }
      let body ← cFrom (b :: env) rest conds inner span
      return s!"(do let k ← {ck}; Pg.flatMapM (Pg.lookup db.{q table} k) fun {var} => {body})"

partial def condOf (env : List Binding) (conds : List Expr) : TM String := do
  match conds with
  | [] => return "pure (some true)"
  | c :: cs =>
    let (code, _) ← cExpr env c (some .bool)
    if cs.isEmpty then return code
    return s!"(Pg.and3 ({code}) ({← condOf env cs}))"

partial def itemName (i : Nat) : SelectItem → String
  | .mk _ (some a) => a
  | .mk (.column _ _ n) none => n
  | .mk (.cast _ (.column _ _ n) _) none => n
  | .mk _ none => s!"column{i + 1}"

/-- A `SELECT`, as code of type `Pg.Result (List row)`, and its columns. -/
partial def cSelect (env : List Binding) (sel : Select) : TM (String × List (String × TyN)) := do
  let .mk span items from_ where_ _ := sel
  let ons := from_.filterMap fun (.mk _ _ on) => on
  let conds := ons.flatMap conjuncts ++ ((where_.map conjuncts).getD [])
  let mut result : List (String × TyN) := []
  let inner (env' : List Binding) : TM String := do
    let cond ← condOf env' conds
    let mut binds := #[]
    let mut names := #[]
    for (it, i) in items.zipIdx do
      let .mk e _ := it
      let (code, _) ← cExpr env' e none
      let v := s!"v{i}"
      binds := binds.push s!"let {v} ← {code}"
      names := names.push v
    let rowCode := s!"(do {"; ".intercalate binds.toList}; pure [{tupleOf names.toList}])"
    return s!"(do let c ← {cond}; if c = some true then {rowCode} else pure [])"
  let code ← cFrom env from_ conds inner span
  -- The column types, read in an environment with every alias bound.
  let typeEnv ← from_.foldlM (init := env) fun acc (.mk table alias _) => do
    match (← get).ctes.find? (·.name == table) with
    | some cte => return { alias, source := .cte cte.columns, var := "_" } :: acc
    | none =>
      let some t := (← get).schema.table? table | fail span s!"no table {table}"
      return { alias, source := .row t, var := "_" } :: acc
  for (it, i) in items.zipIdx do
    let .mk e _ := it
    let some t ← peekTy typeEnv e | fail span s!"cannot tell the type of column {i + 1}"
    result := result ++ [(itemName i it, t)]
  return (code, result)

end

/-! ## Statements -/

/-- The tables the subqueries of an expression read. -/
partial def exprTables : Expr → List String
  | .exists _ s | .subquery _ s => selectTables s
  | .binary _ _ a b => exprTables a ++ exprTables b
  | .unary _ _ a | .cast _ a _ | .isNull _ a _ => exprTables a
  | .call _ _ xs => xs.flatMap exprTables
  | _ => []
where
  /-- The tables a `SELECT` reads. -/
  selectTables : Select → List String
    | .mk _ items from_ w _ =>
      from_.map (fun (.mk t _ _) => t) ++ items.flatMap (fun (.mk e _) => exprTables e) ++
        ((w.map exprTables).getD [])

/-- Under READ COMMITTED, an `UPDATE` re-checks its `WHERE` on the newest
version of the row, but a value it took from an earlier read of the same
table without `FOR UPDATE` can be stale, and writing it loses an update. So
an `UPDATE` may not use such a value. -/
def checkFreshReads (u : Update) : TM Unit := do
  for (.mk table _ _) in u.from_ do
    if let some cte := (← get).ctes.find? (·.name == table) then
      if cte.reads.contains u.table && !cte.locked then
        fail u.span s!"UPDATE {u.table} uses {cte.name}, which reads {u.table} without FOR UPDATE; under READ COMMITTED its values can be stale and an update can be lost"
  for (col, e) in u.sets do
    if (exprTables e).contains u.table then
      fail e.span s!"the new value of {col} reads {u.table} in a subquery; under READ COMMITTED it can be stale and an update can be lost"

/-- An `UPDATE`, as code of type `Pg.Result (List (key × row × returned))`,
and the columns it returns. -/
def cUpdate (u : Update) : TM (String × List (String × TyN)) := do
  checkFreshReads u
  let some t := (← get).schema.table? u.table | fail u.span s!"the table {u.table} is not in the schema"
  let conds := (u.where_.map conjuncts).getD []
  let ons := u.from_.filterMap fun (.mk _ _ on) => on
  let allConds := ons.flatMap conjuncts ++ conds
  let some key := keyFor t u.alias [] allConds
    | fail u.span s!"UPDATE {u.table} needs a condition {u.alias}.{", ".intercalate t.primaryKey} = …"
  let keyTy ← liftE u.span (tyOf (← get).schema (t.column? t.primaryKey.head!).get!.type)
  let mut retCols : List (String × TyN) := []
  let inner (env : List Binding) : TM String := do
    let (ck, _) ← cExpr env key (some keyTy)
    let var ← freshVar s!"r_{u.alias}"
    let b : Binding := { alias := u.alias, source := .row t, var }
    let env' := b :: env
    let cond ← condOf env' allConds
    let mut sets := #[]
    let mut binds := #[]
    for ((col, e), i) in u.sets.zipIdx do
      let some c := t.column? col | fail u.span s!"no column {col} in {u.table}"
      let cty ← liftE u.span (tyOf (← get).schema c.type)
      let (code, et) ← cExpr env' e (some cty)
      if et.ty != cty then fail e.span s!"the new value of {col} has the wrong type"
      if et.nullable && c.notNull then fail e.span s!"{col} cannot be NULL"
      let wrapped := if !c.notNull && !et.nullable then s!"some s{i}" else s!"s{i}"
      binds := binds.push s!"let s{i} ← {code}"
      sets := sets.push s!"{q col} := {wrapped}"
    let setCode := s!"(fun {var} => do {"; ".intercalate binds.toList}; pure \{ {var} with {", ".intercalate sets.toList} })"
    let mut rbinds := #[]
    let mut rnames := #[]
    for (SelectItem.mk e _, i) in u.returning.zipIdx do
      let (code, _) ← cExpr env' e none
      rbinds := rbinds.push s!"let v{i} ← {code}"
      rnames := rnames.push s!"v{i}"
    let retCode := if u.returning.isEmpty then s!"(fun {var} => pure ())"
      else s!"(fun {var} => do {"; ".intercalate rbinds.toList}; pure {tupleOf rnames.toList})"
    return s!"(do let k ← {ck}; Pg.updateOne db.{q u.table} k (fun {var} => {cond}) {setCode} {retCode})"
  let code ← cFrom [] u.from_ allConds inner u.span
  -- Returned column types.
  let typeEnv ← (u.from_.foldlM (init := [{ alias := u.alias, source := .row t, var := "_" }]) fun acc (.mk table alias _) => do
    match (← get).ctes.find? (·.name == table) with
    | some cte => return { alias, source := .cte cte.columns, var := "_" } :: acc
    | none =>
      let some t' := (← get).schema.table? table | fail u.span s!"no table {table}"
      return { alias, source := .row t', var := "_" } :: acc)
  for (it, i) in u.returning.zipIdx do
    let .mk e _ := it
    let some ty ← peekTy typeEnv e | fail u.span s!"cannot tell the type of returned column {i + 1}"
    retCols := retCols ++ [(itemName i it, ty)]
  return (code, retCols)

/-- `u : List (key × row × returned)`: its returned rows. -/
def returnedRows (v : String) : String := s!"({v}.map (·.2.2))"

def cQuery (nq : NamedQuery) (query : Query) : TM String := do
  let mut lines := #[]
  let mut updates : List (String × String) := []
  for (name, body) in query.ctes do
    let var ← freshVar name
    match body with
    | .select sel =>
      let (code, cols) ← cSelect [] sel
      lines := lines.push s!"  let {var} ← {code}"
      let .mk _ _ _ _ forUpdate := sel
      modify fun s => { s with ctes := s.ctes ++ [{ name, columns := cols, rowsVar := var,
                                                    reads := exprTables.selectTables sel,
                                                    locked := forUpdate }] }
    | .update u =>
      if updates.any (·.1 == u.table) then fail u.span s!"two updates of {u.table} in one statement are not supported"
      let (code, cols) ← cUpdate u
      lines := lines.push s!"  let {var} ← {code}"
      lines := lines.push s!"  let {var}_rows := {returnedRows var}"
      updates := updates ++ [(u.table, var)]
      modify fun s => { s with ctes := s.ctes ++ [{ name, columns := cols, rowsVar := s!"{var}_rows" }] }
  let mut resultTyStr := "Unit"
  let mut resultCode := "()"
  let mut rowStruct := ""
  match query.main with
  | .select sel =>
    let (code, cols) ← cSelect [] sel
    lines := lines.push s!"  let main ← {code}"
    match nq.kind, cols with
    | "one", [(_, t)] =>
      resultTyStr := resultTy t
      resultCode := if t.ty == .bool && !t.nullable then "((← Pg.one main).getD false)" else "(← Pg.one main)"
    | "one", cols =>
      let structName := s!"{nq.name}Row"
      rowStruct := s!"structure {q structName} where\n" ++
        "\n".intercalate (cols.map fun (n, t) => s!"  {q n} : {resultTy t}")
      resultTyStr := q structName
      let fields := cols.zipIdx.map fun ((n, t), i) =>
        let v := tupleGet "r" i cols.length
        let v := if t.ty == .bool && !t.nullable then s!"({v}).getD false" else v
        s!"{q n} := {v}"
      resultCode := s!"(do let r ← Pg.one main; pure ((\{ {", ".intercalate fields} } : {q structName})))"
      resultCode := s!"(← {resultCode})"
    | "many", cols =>
      resultTyStr := s!"(List {tupleTy (cols.map (resultTy ·.2))})"
      resultCode := "main"
      if cols.any (·.2.ty == .bool) then fail (Select.span sel) "a :many query returning booleans is not supported yet"
    | k, _ => fail ⟨⟨nq.line, 1⟩, ⟨nq.line, 1⟩⟩ s!"a SELECT with :{k} is not supported"
  | .update u =>
    if updates.any (·.1 == u.table) then fail u.span s!"two updates of {u.table} in one statement are not supported"
    let (code, cols) ← cUpdate u
    lines := lines.push s!"  let main ← {code}"
    updates := updates ++ [(u.table, "main")]
    match nq.kind with
    | "execrows" =>
      resultTyStr := "Int"
      resultCode := "(Int.ofNat main.length)"
    | "exec" => pure ()
    | "one" =>
      let [(_, t)] := cols | fail u.span "a :one UPDATE must return one column"
      resultTyStr := resultTy t
      resultCode := s!"(← Pg.one {returnedRows "main"})"
    | k => fail u.span s!"an UPDATE with :{k} is not supported"
  -- Write the updates, in statement order.
  let mut dbExpr := "db"
  for (table, var) in updates do
    dbExpr := s!"\{ {dbExpr} with {q table} := Pg.applyUpdates {dbExpr}.{q table} {var} }"
  lines := lines.push s!"  pure ({resultCode}, {dbExpr})"
  let args := (← get).args.toList.map fun (n, t) => s!"({q n} : {leanTy t})"
  let header := s!"def {q nq.name} (now : Pg.Timestamp) {" ".intercalate args} (db : DB) :\n    Pg.Result ({resultTyStr} × DB) := do"
  let defText := header ++ "\n" ++ "\n".intercalate lines.toList
  return if rowStruct.isEmpty then defText else rowStruct ++ "\n\n" ++ defText

/-- The tables a query reads or writes. -/
partial def queryTables (query : Query) : List String :=
  let ofSelect : Select → List String := fun (.mk _ _ from_ _ _) => from_.map fun (.mk t _ _) => t
  let rec exprTables : Expr → List String
    | .exists _ s | .subquery _ s => ofSelect s
    | .binary _ _ a b => exprTables a ++ exprTables b
    | .unary _ _ a | .cast _ a _ | .isNull _ a _ => exprTables a
    | .call _ _ xs => xs.flatMap exprTables
    | _ => []
  let selectAll : Select → List String := fun s@(.mk _ items _ w _) =>
    ofSelect s ++ items.flatMap (fun (.mk e _) => exprTables e) ++ ((w.map exprTables).getD [])
  let bodyTables : Body → List String
    | .select s => selectAll s
    | .update u => [u.table] ++ u.from_.map (fun (.mk t _ _) => t) ++ ((u.where_.map exprTables).getD [])
  let cteNames := query.ctes.map (·.1)
  ((query.ctes.map (·.2)).flatMap bodyTables ++ bodyTables query.main).filter (!cteNames.contains ·) |>.eraseDups

/-- Translate the root queries `roots`, found in `queryFiles`, over the
schema that `migrations` (in order) build. -/
def translate (migrations : List (String × String)) (queryFiles : List (String × String))
    (roots : List String) (ns : String) : Except String String := do
  let named := queryFiles.flatMap fun (path, src) => (splitNamedQueries src).map (path, ·)
  let mut parsed := #[]
  for r in roots do
    let some (path, nq) := named.find? (·.2.name == r) | throw s!"no query named {r}"
    match parseStatements nq.source with
    | .ok [(.query _ query, none)] => parsed := parsed.push (path, nq, query)
    | .ok [(_, some e)] => throw s!"{path}:{e.span.start.line + nq.line - 1}:{e.span.start.col}: {e.message}"
    | .ok _ => throw s!"{path}: the query {r} must be one SELECT or UPDATE statement"
    | .error e => throw (e.render path)
  let tables := (parsed.toList.flatMap fun (_, _, query) => queryTables query).eraseDups
  let files ← migrations.mapM fun (path, src) =>
    match parseStatements src with
    | .ok stmts => .ok (path, stmts)
    | .error e => .error (e.render path)
  let schema ← reachTables files tables
  let schemaText ← schema.toLean
  let mut defs := #[]
  for (path, nq, query) in parsed do
    let run := cQuery nq query
    match run.run { schema, path, lineOffset := nq.line - 1 } with
    | .ok (text, _) => defs := defs.push text
    | .error m => throw m
  return s!"-- Generated by tolean from {", ".intercalate ((migrations ++ queryFiles).map (·.1))}. Do not edit.\n" ++
    "import tolean.Sql.Spec.Basic\n\nset_option linter.unusedVariables false\n\n" ++
    s!"namespace {ns}\n\nopen tolean\n\n" ++ schemaText ++ "\n\n" ++ "\n\n".intercalate defs.toList ++
    s!"\n\nend {ns}\n"

end tolean.Sql.Translate
