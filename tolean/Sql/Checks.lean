import tolean.Sql.Translate

/-!
Checks of the SQL interpreter and of the proved path on single queries. Each
`#guard` holds when this module builds, so a change that breaks one fails
`lake build`.

The cases come from review: places where the interpreter once disagreed with
PostgreSQL 18, or where the proved path accepted a query whose printed code
disagreed with it.
-/
namespace tolean.Sql.Checks

open tolean tolean.Sql

def schemaSql : String :=
  "CREATE TABLE t (id BIGINT PRIMARY KEY, x BIGINT, i INTEGER);"

def schema : Schema :=
  match parseStatements schemaSql with
  | .ok stmts => (reachTables [("schema.sql", stmts)] ["t"]).toOption.getD {}
  | .error _ => {}

/-- The query of a one-query file, with its name and kind. -/
def query (source : String) : Option (NamedQuery × Query) :=
  match splitNamedQueries source with
  | [nq] =>
    match parseStatements nq.source with
    | .ok [(.query _ q, none)] => some (nq, q)
    | _ => none
  | _ => none

/-- The row `(1, 2147483648, 2147483647)`. -/
def db : Eval.DB := fun table =>
  if table = "t" then [[.int .w64 1, .int .w64 2147483648, .int .w32 2147483647]] else []

def input : Eval.Input := { db, now := ⟨0⟩, args := [] }

/-- What the interpreter gives for a query. -/
def interpret (source : String) : Option (Eval.M (List Eval.Row × Eval.DB)) :=
  (query source).map fun (nq, q) => Eval.run schema input nq.kind q

/-- Whether the proved path accepts a query. -/
def accepted (source : String) : Bool :=
  match query source with
  | some (nq, q) => (Plan.translate schema nq q).toBool
  | none => false

def raisesOutOfRange : Option (Eval.M (List Eval.Row × Eval.DB)) → Bool
  | some (.error (.error .outOfRange)) => true
  | _ => false

def gives (row : Eval.Row) : Option (Eval.M (List Eval.Row × Eval.DB)) → Bool
  | some (.ok ([r], _)) => r == row
  | _ => false

/-! A minus sign before an integer literal is part of the literal, so
`-2147483648` is an `integer`, and subtracting 1 leaves its range. -/

def negativeLiteral : String := "-- name: Q :one\nSELECT -2147483648 - 1 AS result;"

#guard raisesOutOfRange (interpret negativeLiteral)
#guard !accepted negativeLiteral
#guard gives [.int .w32 (-2147483648)] (interpret "-- name: Q :one\nSELECT -2147483648 AS v;")
#guard gives [.int .w64 (-2147483649)] (interpret "-- name: Q :one\nSELECT -2147483649 AS v;")

/-! `COALESCE` converts its value to the widest type of its arguments, which
the interpreter does not model. So the proved path refuses integers of two
widths, such as a `bigint` and the `integer` literal `0`. Otherwise it would
miss the narrowing cast below, which raises `outOfRange` in PostgreSQL. -/

#guard !accepted "-- name: Q :one\nSELECT COALESCE(t.x, 0)::integer AS v FROM t WHERE t.id = 1;"
#guard !accepted "-- name: Q :one\nSELECT COALESCE(t.i, 0::bigint) + 1 AS v FROM t WHERE t.id = 1;"
#guard accepted "-- name: Q :one\nSELECT COALESCE(t.x, 0::bigint) AS v FROM t WHERE t.id = 1;"
#guard gives [.int .w64 2147483648]
  (interpret "-- name: Q :one\nSELECT COALESCE(t.x, 0::bigint) AS v FROM t WHERE t.id = 1;")

end tolean.Sql.Checks
