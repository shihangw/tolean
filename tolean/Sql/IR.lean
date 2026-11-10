import tolean.Sql.Spec.Eval

/-!
The IR of the SQL translator: the Lean code of a query, as data.

A query becomes a plan. Each table of `FROM` is read through its primary
key, by a lookup nested inside the lookups of the tables before it. The
innermost level tests the conditions and builds the output row. The
printer below writes a plan as the code that `tolean/Sql/Translate.lean`
has always written for it, and `tolean/Sql/IR/Eval.lean` gives the plan its
meaning.

SQL does not build the shared Tolean IR of `tolean/IR.lean` yet. That IR is
pure, and every SQL expression can raise an error, such as `bigint out of
range`. The plan of the shared core adds errors to that IR. Then this IR can
become its SQL extension.

A node that the printer specializes by type, such as `IS NULL` on a column
that cannot be NULL, keeps the operation in the evaluator. The evaluator
then follows the values, as the interpreter does, and the type that makes
the printed code agree is a fact about the printed code alone.
-/
namespace tolean.Sql.IR

open tolean tolean.Sql

/-- The type of a value in printed code. -/
inductive Ty where
  | int
  | bool
  | text
  | uuid
  | ts
  | json
  | bytes
  | enum (name : String)
deriving DecidableEq, Inhabited, Repr

def Ty.enumName : Ty → String
  | .enum n => n
  | _ => ""

structure TyN where
  ty : Ty
  nullable : Bool
deriving DecidableEq, Inhabited

def q (n : String) : String := s!"«{n}»"

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

/-! ## The IR -/

/-- An expression: code of type `Pg.Result v`. -/
inductive Expr where
  /-- `{var}.«name»`: column `index` of the row bound `depth` levels out. -/
  | col (depth index : Nat) (var name : String)
  | int (n : Int)
  | bool (b : Bool)
  | text (s : String)
  /-- An enum label, for a string literal that the other side of `=` gives an
  enum type. -/
  | enumLit (type label : String)
  /-- `sqlc.arg(name)`. A boolean is three valued in code. -/
  | arg (name : String) (isBool : Bool)
  | now
  | arith (op : Eval.ArithOp) (a b : Expr)
  | neg (a : Expr)
  | eq (ne : Bool) (a b : Expr)
  | cmp (op : Eval.CmpOp) (a b : Expr)
  | and (a b : Expr)
  | or (a b : Expr)
  | not (a : Expr)
  /-- `a IS [NOT] NULL`. When `a` cannot be NULL, the code is a constant. -/
  | isNull (negated nullable : Bool) (a : Expr)
  /-- A cast that does not change the code. -/
  | cast (target : Eval.Target) (a : Expr)
  /-- `a::text` on an enum. -/
  | enumText (type : String) (nullable : Bool) (a : Expr)
  | least (a b : Expr)
  /-- `COALESCE(a, b)`. When `a` cannot be NULL, the code is `a`. -/
  | coalesce (nullable : Bool) (a b : Expr)
deriving Inhabited

/-- A table of `FROM`, read by its key. -/
structure Lookup where
  table : String
  /-- The Lean variable of the row. -/
  var : String
  /-- The index of the key column. -/
  keyIndex : Nat
  /-- The key, read in the levels outside this one. -/
  key : Expr

structure Select where
  lookups : List Lookup
  /-- The conditions of every `ON` and of `WHERE`, split at `AND`. -/
  conds : List Expr
  outs : List Expr

/-- A query: a function of `now`, its arguments and the database. -/
structure Query where
  name : String
  args : List (String × Ty)
  kind : Eval.Kind
  select : Select
  /-- The names and types of the result columns. -/
  columns : List (String × TyN)

/-! ## The printer -/

def ArithOp.symbol : Eval.ArithOp → String
  | .add => "+"
  | .sub => "-"
  | .mul => "*"

def CmpOp.symbol : Eval.CmpOp → String
  | .lt => "<"
  | .le => "<="
  | .gt => ">"
  | .ge => ">="

def Expr.print : Expr → String
  | .col _ _ var name => s!"pure {var}.{q name}"
  | .int n => s!"pure ({n} : Int)"
  | .bool b => s!"pure (some {b})"
  | .text s => s!"pure {s.quote}"
  | .enumLit t l => s!"pure (.{q l} : {q t})"
  | .arg n isBool => if isBool then s!"pure (some {q n})" else s!"pure {q n}"
  | .now => "pure now"
  | .arith op a b => s!"(do let a ← {a.print}; let b ← {b.print}; Pg.int64 (a {ArithOp.symbol op} b))"
  | .neg a => s!"(do let a ← {a.print}; Pg.int64 (-a))"
  | .eq ne a b =>
    let test := if ne then "a != b" else "a == b"
    s!"(do let a ← {a.print}; let b ← {b.print}; pure (some ({test})))"
  | .cmp op a b =>
    s!"(do let a ← {a.print}; let b ← {b.print}; pure (some (decide (a {CmpOp.symbol op} b))))"
  | .and a b => s!"(Pg.and3 ({a.print}) ({b.print}))"
  | .or a b => s!"(Pg.or3 ({a.print}) ({b.print}))"
  | .not a => s!"(Pg.not3 ({a.print}))"
  | .isNull negated nullable a =>
    if nullable then
      let test := if negated then "isSome" else "isNone"
      s!"(do let x ← {a.print}; pure (some x.{test}))"
    else s!"pure (some {negated})"
  | .cast _ a => a.print
  | .enumText t nullable a =>
    let conv := if nullable then s!"x.map {q t}.text" else s!"{q t}.text x"
    s!"(do let x ← {a.print}; pure ({conv}))"
  | .least a b => s!"(do let a ← {a.print}; let b ← {b.print}; pure (Pg.least a b))"
  | .coalesce nullable a b =>
    if nullable then s!"(do let x ← {a.print}; match x with | some v => pure v | none => {b.print})"
    else a.print

/-- The conjunction of conditions. -/
def printConds : List Expr → String
  | [] => "pure (some true)"
  | [c] => c.print
  | c :: cs => s!"(Pg.and3 ({c.print}) ({printConds cs}))"

/-- The innermost level: test the conditions and build the row. -/
def Select.printEmit (s : Select) : String :=
  let binds := s.outs.zipIdx.map fun (e, i) => s!"let v{i} ← {e.print}"
  let names := s.outs.zipIdx.map fun (_, i) => s!"v{i}"
  let rowCode := s!"(do {"; ".intercalate binds}; pure [{tupleOf names}])"
  s!"(do let c ← {printConds s.conds}; if c = some true then {rowCode} else pure [])"

def printLookups (inner : String) : List Lookup → String
  | [] => inner
  | l :: rest =>
    s!"(do let k ← {l.key.print}; Pg.flatMapM (Pg.lookup db.{q l.table} k) fun {l.var} => {printLookups inner rest})"

/-- Code of type `Pg.Result (List row)`. -/
def Select.print (s : Select) : String := printLookups s.printEmit s.lookups

/-- The definition of the query, after the structure of its row when it
needs one. -/
def Query.print (qy : Query) : String :=
  let (resTy, resCode, rowStruct) : String × String × String :=
    match qy.kind, qy.columns with
    | .one, [(_, t)] =>
      (resultTy t, if t.ty == .bool && !t.nullable then "((← Pg.one main).getD false)" else "(← Pg.one main)", "")
    | .one, cols =>
      let structName := s!"{qy.name}Row"
      let rowStruct := s!"structure {q structName} where\n" ++
        "\n".intercalate (cols.map fun (n, t) => s!"  {q n} : {resultTy t}")
      let fields := cols.zipIdx.map fun ((n, t), i) =>
        let v := tupleGet "r" i cols.length
        let v := if t.ty == .bool && !t.nullable then s!"({v}).getD false" else v
        s!"{q n} := {v}"
      (q structName, s!"(← (do let r ← Pg.one main; pure ((\{ {", ".intercalate fields} } : {q structName}))))", rowStruct)
    | .many, cols => (s!"(List {tupleTy (cols.map (resultTy ·.2))})", "main", "")
  let lines := [s!"  let main ← {qy.select.print}", s!"  pure ({resCode}, db)"]
  let args := qy.args.map fun (n, t) => s!"({q n} : {leanTy t})"
  let header := s!"def {q qy.name} (now : Pg.Timestamp) {" ".intercalate args} (db : DB) :\n    Pg.Result ({resTy} × DB) := do"
  let defText := header ++ "\n" ++ "\n".intercalate lines
  if rowStruct.isEmpty then defText else rowStruct ++ "\n\n" ++ defText

end tolean.Sql.IR
