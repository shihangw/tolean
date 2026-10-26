import tolean.Sql.Syntax

/-!
The schema translator. It replays migrations in order and keeps the final
shape of the tables that the translated queries reach, and of the tables their
foreign keys point to.

A statement that could change a reached table or type must parse; Tolean
refuses it otherwise. A statement that names none of them, such as an
extension setup, is skipped, and so is one that cannot change a schema at all,
such as a data backfill or a session setting.
-/
namespace tolean.Sql

open tolean tolean.Sql

structure Column where
  name : String
  type : TypeName
  notNull : Bool
  hasDefault : Bool
deriving Inhabited

structure ForeignKey where
  columns : List String
  table : String
  refColumns : List String
  onDelete : OnDelete

structure Unique where
  name : String
  columns : List String
  partial_ : Bool

structure Table where
  name : String
  columns : List Column
  primaryKey : List String := []
  uniques : List Unique := []
  foreignKeys : List ForeignKey := []
  checks : Nat := 0
deriving Inhabited

instance : Inhabited ForeignKey := ⟨{ columns := [], table := "", refColumns := [], onDelete := .noAction }⟩

structure Schema where
  tables : List Table := []
  enums : List (String × List String) := []
  domains : List (String × TypeName) := []

def Schema.table? (s : Schema) (n : String) : Option Table := s.tables.find? (·.name == n)

def Schema.updateTable (s : Schema) (n : String) (f : Table → Table) : Schema :=
  { s with tables := s.tables.map fun t => if t.name == n then f t else t }

/-- The names in a statement's tokens, including those inside `$$` bodies. -/
def tokenNames (ts : List Token) : List String :=
  ts.flatMap fun t => match t.kind with
    | .word w _ => [w]
    | .dollar body => (body.split (fun c => !(c.isAlphanum || c == '_'))).toList.map (·.toString.toLower)
    | _ => []

def tableFromCreate (name : String) (cols : List ColumnDef)
    (cons : List (Option String × TableConstraint)) : Except String Table := do
  let mut t : Table := { name, columns := [] }
  for c in cols do
    let mut col : Column := { name := c.name, type := c.type, notNull := false, hasDefault := false }
    for cc in c.constraints do
      match cc with
      | .notNull => col := { col with notNull := true }
      | .null => pure ()
      | .default _ => col := { col with hasDefault := true }
      | .primaryKey =>
        col := { col with notNull := true }
        t := { t with primaryKey := [c.name] }
      | .unique => t := { t with uniques := t.uniques ++ [{ name := s!"{name}_{c.name}_key", columns := [c.name], partial_ := false }] }
      | .references rt rc od =>
        t := { t with foreignKeys := t.foreignKeys ++ [{ columns := [c.name], table := rt, refColumns := rc.toList, onDelete := od }] }
      | .check _ => t := { t with checks := t.checks + 1 }
    t := { t with columns := t.columns ++ [col] }
  for (cname, tc) in cons do
    match tc with
    | .primaryKey cs =>
      t := { t with primaryKey := cs, columns := t.columns.map fun col =>
        if cs.contains col.name then { col with notNull := true } else col }
    | .unique cs =>
      t := { t with uniques := t.uniques ++ [{ name := cname.getD s!"{name}_key", columns := cs, partial_ := false }] }
    | .foreignKey cs rt rcs od =>
      t := { t with foreignKeys := t.foreignKeys ++ [{ columns := cs, table := rt, refColumns := rcs, onDelete := od }] }
    | .check _ => t := { t with checks := t.checks + 1 }
  return t

def applyAlter (t : Table) (a : AlterAction) : Except String Table := do
  match a with
  | .addColumn c ifNotExists =>
    if t.columns.any (·.name == c.name) then
      if ifNotExists then return t
      throw s!"column {c.name} already exists"
    let t' ← tableFromCreate t.name [c] []
    return { t with columns := t.columns ++ t'.columns, uniques := t.uniques ++ t'.uniques,
                    foreignKeys := t.foreignKeys ++ t'.foreignKeys,
                    primaryKey := if t'.primaryKey.isEmpty then t.primaryKey else t'.primaryKey,
                    checks := t.checks + t'.checks }
  | .dropColumn n =>
    return { t with columns := t.columns.filter (·.name != n),
                    uniques := t.uniques.filter (!·.columns.contains n),
                    foreignKeys := t.foreignKeys.filter (!·.columns.contains n) }
  | .setType c ty => return { t with columns := t.columns.map fun col => if col.name == c then { col with type := ty } else col }
  | .setDefault c _ => return { t with columns := t.columns.map fun col => if col.name == c then { col with hasDefault := true } else col }
  | .dropDefault c => return { t with columns := t.columns.map fun col => if col.name == c then { col with hasDefault := false } else col }
  | .setNotNull c => return { t with columns := t.columns.map fun col => if col.name == c then { col with notNull := true } else col }
  | .dropNotNull c => return { t with columns := t.columns.map fun col => if col.name == c then { col with notNull := false } else col }
  | .addConstraint n tc =>
    let t' ← tableFromCreate t.name [] [(n, tc)]
    return { t with uniques := t.uniques ++ t'.uniques, foreignKeys := t.foreignKeys ++ t'.foreignKeys,
                    primaryKey := if t'.primaryKey.isEmpty then t.primaryKey else t'.primaryKey,
                    checks := t.checks + t'.checks,
                    columns := if t'.primaryKey.isEmpty then t.columns else t.columns.map fun col =>
                      if t'.primaryKey.contains col.name then { col with notNull := true } else col }
  | .dropConstraint n =>
    if t.uniques.any (·.name == n) then return { t with uniques := t.uniques.filter (·.name != n) }
    throw s!"dropping the constraint {n} is not supported"

/-- Replay `files` (path and statements, in order) for the tables `reached`. -/
def replay (files : List (String × List (Stmt × Option ParseError))) (reached : List String) :
    Except String Schema := do
  let mut s : Schema := {}
  for (path, stmts) in files do
    for (st, err) in stmts do
      let at_ := s!"{path}:{st.span.start.line}:{st.span.start.col}"
      let fail {A : Type} (m : String) : Except String A := throw s!"{at_}: {m}"
      match st with
      | .createEnum _ n ls => s := { s with enums := (s.enums.filter (·.1 != n)) ++ [(n, ls)] }
      | .createDomain _ n ty => s := { s with domains := (s.domains.filter (·.1 != n)) ++ [(n, ty)] }
      | .createTable _ n ifNotExists cols cons =>
        if !reached.contains n then continue
        if (s.table? n).isSome then
          if ifNotExists then continue
          fail s!"table {n} already exists"
        match tableFromCreate n cols cons with
        | .ok t => s := { s with tables := s.tables ++ [t] }
        | .error m => fail m
      | .createPartition .. => pure ()
      | .alterTable _ n actions =>
        if !reached.contains n then continue
        let some t := s.table? n | fail s!"no table {n}"
        let mut t := t
        for a in actions do
          match applyAlter t a with
          | .ok t' => t := t'
          | .error m => fail m
        s := s.updateTable n fun _ => t
      | .createIndex _ unique name table cols where_ =>
        if unique && reached.contains table then
          s := s.updateTable table fun t =>
            { t with uniques := t.uniques ++ [{ name, columns := cols, partial_ := where_.isSome }] }
      | .drop _ kind names =>
        for n in names do
          match kind with
          | "table" => if reached.contains n then fail s!"the reached table {n} is dropped"
          | "type" => s := { s with enums := s.enums.filter (·.1 != n) }
          | "domain" => s := { s with domains := s.domains.filter (·.1 != n) }
          | "index" => s := { s with tables := s.tables.map fun t => { t with uniques := t.uniques.filter (·.name != n) } }
          | _ => pure ()
      | .query .. => pure ()
      | .opaque _ tokens =>
        -- Data changes, reads and session settings cannot change a schema.
        let first := match tokens.head? with
          | some { kind := .word w false, .. } => w
          | _ => ""
        if ["select", "insert", "update", "delete", "with", "values", "set", "reset", "comment",
            "grant", "revoke", "analyze", "vacuum", "begin", "commit"].contains first then continue
        let names := tokenNames tokens
        -- User types only: a built-in type such as `jsonb` names no reached object.
        let userTypes := s.enums.map (·.1) ++ s.domains.map (·.1)
        let typeNames := (s.tables.flatMap fun t => t.columns.map (·.type.name)).filter userTypes.contains
        if names.any (fun n => reached.contains n || typeNames.contains n) then
          let reason := (err.map (·.message)).getD "it does not parse"
          fail s!"this statement names a translated table or type, but tolean cannot read it: {reason}"
  for n in reached do
    if (s.table? n).isNone then throw s!"no migration creates the table {n}"
  return s

/-- `reached`, and every table their foreign keys point to. -/
def reachTables (files : List (String × List (Stmt × Option ParseError))) (roots : List String) :
    Except String Schema := do
  let mut reached := roots
  for _ in [0:20] do
    let s ← replay files reached
    let more := (s.tables.flatMap fun t => t.foreignKeys.map (·.table)).filter (!reached.contains ·)
    if more.isEmpty then return s
    reached := reached ++ more.eraseDups
  throw "foreign keys reach too many tables"

/-! ## Types -/

def Schema.resolve (s : Schema) (ty : TypeName) : TypeName :=
  match s.domains.find? (·.1 == ty.name) with
  | some (_, under) => { under with array := ty.array || under.array }
  | none => ty

/-- The name PostgreSQL's `format_type` gives. -/
def canonicalType (ty : TypeName) : String :=
  let base := match ty.name with
    | "int8" => "bigint"
    | "int" | "int4" => "integer"
    | "int2" => "smallint"
    | "bool" => "boolean"
    | "timestamptz" => "timestamp with time zone"
    | "timestamp" => "timestamp without time zone"
    | "varchar" => "character varying"
    | "float8" => "double precision"
    | n => n
  let mods := if ty.mods.isEmpty then "" else "(" ++ ",".intercalate (ty.mods.map toString) ++ ")"
  base ++ mods ++ (if ty.array then "[]" else "")

def leanIdent (n : String) : String := s!"«{n}»"

/-- The Lean type of a column type. -/
def Schema.leanType (s : Schema) (ty : TypeName) : Except String String := do
  let ty := s.resolve ty
  let base ← match canonicalType { ty with array := false, mods := [] } with
    | "bigint" | "integer" | "smallint" => pure "Int"
    | "boolean" => pure "Bool"
    | "text" | "character varying" => pure "String"
    | "uuid" => pure "Pg.UUID"
    | "bytea" => pure "Pg.Bytes"
    | "timestamp with time zone" | "timestamp without time zone" => pure "Pg.Timestamp"
    | "jsonb" | "json" => pure "Pg.Json"
    | n =>
      if s.enums.any (·.1 == n) then pure (leanIdent n)
      else throw s!"the type {n} is not supported"
  return if ty.array then s!"(List {base})" else base

def Table.column? (t : Table) (n : String) : Option Column := t.columns.find? (·.name == n)

def Schema.columnType (s : Schema) (c : Column) : Except String String := do
  let base ← s.leanType c.type
  return if c.notNull then base else s!"(Option {base})"

def Schema.keyType (s : Schema) (t : Table) : Except String String := do
  if t.primaryKey.isEmpty then throw s!"the table {t.name} has no primary key"
  let parts ← t.primaryKey.mapM fun k => do
    let some c := t.column? k | throw s!"no column {k} in {t.name}"
    s.leanType c.type
  return match parts with
    | [p] => p
    | ps => "(" ++ " × ".intercalate ps ++ ")"

/-- The key of row `r` of table `t`. -/
def Table.keyOf (t : Table) (r : String) : String :=
  match t.primaryKey with
  | [k] => s!"{r}.{leanIdent k}"
  | ks => "(" ++ ", ".intercalate (ks.map fun k => s!"{r}.{leanIdent k}") ++ ")"

/-! ## Lean output -/

def Schema.toLean (s : Schema) : Except String String := do
  let usedTypes := s.tables.flatMap fun t => t.columns.map fun c => canonicalType (s.resolve c.type)
  let mut out := #[]
  for (n, labels) in s.enums do
    if !usedTypes.contains n then continue
    out := out.push (s!"inductive {leanIdent n} where\n" ++
      String.join (labels.map fun l => s!"  | {leanIdent l}\n") ++
      "deriving DecidableEq, Repr, Inhabited")
    out := out.push (s!"def {leanIdent n}.text : {leanIdent n} → String\n" ++
      "\n".intercalate (labels.map fun l => s!"  | .{leanIdent l} => {l.quote}"))
  for t in s.tables do
    let mut fields := #[]
    for c in t.columns do
      fields := fields.push s!"  {leanIdent c.name} : {← s.columnType c}"
    out := out.push (s!"namespace {leanIdent t.name}\n\n" ++
      s!"structure Row where\n" ++ "\n".intercalate fields.toList ++ "\n\n" ++
      s!"abbrev Key := {← s.keyType t}\n\n" ++
      s!"abbrev Table := Pg.Table Key Row\n\nend {leanIdent t.name}")
  let dbFields := s.tables.map fun t => s!"  {leanIdent t.name} : {leanIdent t.name}.Table := fun _ => none"
  out := out.push ("/-- The database: one table per reached table. -/\nstructure DB where\n" ++
    "\n".intercalate dbFields)
  -- The invariant PostgreSQL keeps on every write.
  let mut conds := #[]
  for t in s.tables do
    let tn := leanIdent t.name
    conds := conds.push s!"(∀ k r, db.{tn} k = some r → {t.keyOf "r"} = k)"
    for c in t.columns do
      let ty := canonicalType (s.resolve c.type)
      if ty == "bigint" then
        if c.notNull then conds := conds.push s!"(∀ k r, db.{tn} k = some r → Pg.inInt64 r.{leanIdent c.name})"
        else conds := conds.push s!"(∀ k r v, db.{tn} k = some r → r.{leanIdent c.name} = some v → Pg.inInt64 v)"
    for fk in t.foreignKeys do
      let some target := s.table? fk.table | throw s!"no table {fk.table}"
      if fk.columns.length != 1 || target.primaryKey.length != 1 then
        throw s!"only single-column foreign keys to a primary key are supported ({t.name})"
      let refCols := if fk.refColumns.isEmpty then target.primaryKey else fk.refColumns
      if refCols != target.primaryKey then throw s!"a foreign key must point to the primary key ({t.name})"
      let some col := t.column? fk.columns.head! | throw s!"no column {fk.columns.head!}"
      if col.notNull then
        conds := conds.push s!"(∀ k r, db.{tn} k = some r → (db.{leanIdent fk.table} r.{leanIdent col.name}).isSome)"
      else
        conds := conds.push s!"(∀ k r v, db.{tn} k = some r → r.{leanIdent col.name} = some v → (db.{leanIdent fk.table} v).isSome)"
    if t.checks > 0 then throw s!"CHECK constraints on {t.name} are not supported yet"
    for u in t.uniques do
      if u.partial_ then throw s!"the partial unique index {u.name} on {t.name} is not supported yet"
      if u.columns != t.primaryKey then
        let same := " ∧ ".intercalate (u.columns.map fun c => s!"r₁.{leanIdent c} = r₂.{leanIdent c}")
        conds := conds.push s!"(∀ k₁ k₂ r₁ r₂, db.{tn} k₁ = some r₁ → db.{tn} k₂ = some r₂ → {same} → k₁ = k₂)"
  let body := if conds.isEmpty then "True" else " ∧\n  ".intercalate conds.toList
  out := out.push ("/-- What PostgreSQL enforces on every write: keys match rows, numbers stay in\n" ++
    "range, foreign keys point to rows, and unique columns are unique. -/\n" ++
    s!"def Valid (db : DB) : Prop :=\n  {body}")
  return "\n\n".intercalate out.toList

/-- The schema in the canonical form that `tests/sql/schemacheck` prints from
PostgreSQL's catalog. -/
def Schema.canonical (s : Schema) : String := Id.run do
  let mut lines := #[]
  for t in s.tables.toArray.qsort (·.name < ·.name) do
    lines := lines.push s!"table {t.name}"
    for c in t.columns do
      lines := lines.push s!"  column {c.name} {canonicalType c.type}{if c.notNull then " not null" else ""}{if c.hasDefault then " default" else ""}"
    if !t.primaryKey.isEmpty then lines := lines.push s!"  primary key ({", ".intercalate t.primaryKey})"
    let fks := t.foreignKeys.toArray.qsort (fun a b => a.columns.toString < b.columns.toString)
    for fk in fks do
      let target := (s.table? fk.table).map (·.primaryKey) |>.getD []
      let refs := if fk.refColumns.isEmpty then target else fk.refColumns
      let action := match fk.onDelete with
        | .cascade => " on delete cascade"
        | .restrict => " on delete restrict"
        | .setNull => " on delete set null"
        | .noAction => ""
      lines := lines.push s!"  foreign key ({", ".intercalate fk.columns}) references {fk.table} ({", ".intercalate refs}){action}"
    let uniques := (t.uniques.filter (·.columns != t.primaryKey)).toArray.qsort (fun a b => a.columns.toString < b.columns.toString)
    for u in uniques do
      lines := lines.push s!"  unique ({", ".intercalate u.columns}){if u.partial_ then " partial" else ""}"
    if t.checks > 0 then lines := lines.push s!"  checks {t.checks}"
  let used := s.tables.flatMap fun t => t.columns.map (·.type.name)
  for (n, labels) in s.enums.toArray.qsort (·.1 < ·.1) do
    if used.contains n then lines := lines.push s!"enum {n} {",".intercalate labels}"
  return "\n".intercalate lines.toList

end tolean.Sql
