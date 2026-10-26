/-!
The model of PostgreSQL values and errors that code generated from SQL
imports. Proofs assume only what this file states, so review it with care.

- `bigint`, `integer` and `smallint` are `Int`. Arithmetic that leaves the
  type's range raises `outOfRange`, as PostgreSQL does.
- `uuid` is 16 bytes, the same type as Go's `[16]byte`, so Go and SQL code
  can share IDs.
- `timestamptz` is a count of microseconds. `now()` is the same within one
  transaction, so generated code takes it as an argument.
- `jsonb` is opaque: Tolean does not translate code that looks inside it.
- A table is a map from its primary key to its row.
- Booleans in conditions are three-valued: `none` is SQL's NULL, and `WHERE`
  keeps a row only when its condition is `some true`.
- PostgreSQL does not fix the order in which it evaluates `AND` and `OR`.
  When one side would raise an error and the other side decides the result,
  PostgreSQL may raise or may not. The model does not raise there, and raises
  only when every order must. So when PostgreSQL succeeds, the model succeeds
  with the same result, and a theorem about successful runs carries over.
-/
namespace tolean.Pg

abbrev UUID := Vector UInt8 16

structure Timestamp where
  micros : Int
deriving DecidableEq, Repr, Inhabited

structure Json where
  text : String
deriving DecidableEq, Repr, Inhabited

abbrev Bytes := List UInt8

/-- The errors a statement can raise. A failed statement changes nothing. -/
inductive Error where
  /-- SQLSTATE 22003: a number left its type's range. -/
  | outOfRange
  /-- `:one` found no row. -/
  | noRows
  /-- SQLSTATE 21000: a scalar subquery returned more than one row. -/
  | cardinality
deriving DecidableEq, Repr, Inhabited

abbrev Result (A : Type) := Except Error A

def inInt64 (x : Int) : Prop := -2 ^ 63 ≤ x ∧ x < 2 ^ 63

/-- A `bigint` result: the value, or `outOfRange`. -/
def int64 (x : Int) : Result Int :=
  if -2 ^ 63 ≤ x ∧ x < 2 ^ 63 then .ok x else .error .outOfRange

/-- `LEAST(a, b)` on non-null values. -/
def least (a b : Int) : Int := min a b

/-- A table: each primary key has at most one row. -/
abbrev Table (Key Row : Type) := Key → Option Row

def Table.set {Key Row : Type} [DecidableEq Key] (t : Table Key Row) (k : Key) (r : Row) : Table Key Row :=
  fun k' => if k' = k then some r else t k'

/-- `a AND b` in three-valued logic; see the module comment for errors. -/
def and3 (a b : Result (Option Bool)) : Result (Option Bool) :=
  match a, b with
  | .ok (some false), _ => .ok (some false)
  | _, .ok (some false) => .ok (some false)
  | .error e, _ => .error e
  | _, .error e => .error e
  | .ok (some true), .ok x => .ok x
  | .ok none, .ok _ => .ok none

/-- `a OR b` in three-valued logic; see the module comment for errors. -/
def or3 (a b : Result (Option Bool)) : Result (Option Bool) :=
  match a, b with
  | .ok (some true), _ => .ok (some true)
  | _, .ok (some true) => .ok (some true)
  | .error e, _ => .error e
  | _, .error e => .error e
  | .ok (some false), .ok x => .ok x
  | .ok none, .ok _ => .ok none

def not3 (a : Result (Option Bool)) : Result (Option Bool) := a.map (Option.map not)

/-- The rows with key `k`: none or one. -/
def lookup {Key Row : Type} (t : Table Key Row) (k : Key) : List Row :=
  match t k with
  | some r => [r]
  | none => []

/-- The elements whose condition is `some true`. -/
def filterM {A : Type} : List A → (A → Result (Option Bool)) → Result (List A)
  | [], _ => .ok []
  | x :: xs, p => do
    let c ← p x
    let rest ← filterM xs p
    return if c = some true then x :: rest else rest

def flatMapM {A B : Type} : List A → (A → Result (List B)) → Result (List B)
  | [], _ => .ok []
  | x :: xs, f => do
    let ys ← f x
    let rest ← flatMapM xs f
    return ys ++ rest

/-- A scalar subquery: NULL for no row, an error for more than one. -/
def scalar {A : Type} : List A → Result (Option A)
  | [] => .ok none
  | [x] => .ok (some x)
  | _ => .error .cardinality

/-- `:one`: the first row, or `noRows`. -/
def one {A : Type} : List A → Result A
  | [] => .error .noRows
  | x :: _ => .ok x

/-- Update the row with key `k` when `cond` holds: the new row comes from
`set`, and `ret` gives what `RETURNING` returns from the new row. -/
def updateOne {Key Row T : Type} (t : Table Key Row) (k : Key) (cond : Row → Result (Option Bool))
    (set : Row → Result Row) (ret : Row → Result T) : Result (List (Key × Row × T)) :=
  match t k with
  | none => .ok []
  | some r => do
    let c ← cond r
    if c = some true then
      let r' ← set r
      let v ← ret r'
      return [(k, r', v)]
    else return []

/-- Write the rows an `UPDATE` changed. -/
def applyUpdates {Key Row T : Type} [DecidableEq Key] (t : Table Key Row) (us : List (Key × Row × T)) :
    Table Key Row :=
  us.foldl (fun t (k, r, _) => t.set k r) t

end tolean.Pg
