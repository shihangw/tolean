/-!
A JS `Map` as a Lean value, for the output of the translator.

ECMA-262 keeps the entries of a `Map` in the order that `set` first added each
key (§24.1), and `for … of` visits them in that order. So the model is the
list of entries in that order, with each key at most once. `set` on a key that
the map has changes its value in place, and `delete` removes its entry
(§24.1.3.9 and §24.1.3.3).

A key is found with `==`. The translator accepts only keys whose
SameValueZero (§7.2.11) is Lean's equality: bigints, booleans, strings and
literal unions of strings.

This file is not trusted. A certificate proves that the output computes what
the interpreter computes, so a wrong definition here would make a certificate
fail, not pass.
-/
namespace tolean.TypeScript

/-- A JS `Map`: its entries, in the order that `set` first added each key. -/
structure JSMap (K V : Type) where
  entries : List (K × V)
deriving DecidableEq, Repr, Inhabited

namespace JSMap

variable {K V : Type} [BEq K]

/-- `new Map()`: a map without entries. -/
def empty : JSMap K V := ⟨[]⟩

/-- `m.get(k)`: the value of `k`, or `none` (`undefined`) when the map has no
such key. -/
def get? (m : JSMap K V) (k : K) : Option V := (m.entries.find? (·.1 == k)).map (·.2)

/-- `m.has(k)`. -/
def has (m : JSMap K V) (k : K) : Bool := m.entries.any (·.1 == k)

/-- `m.set(k, v)`: the value of `k` changes in place when the map has `k`, and
a new entry for `k` goes last otherwise. -/
def set (m : JSMap K V) (k : K) (v : V) : JSMap K V :=
  if m.has k then ⟨m.entries.map fun e => if e.1 == k then (e.1, v) else e⟩
  else ⟨m.entries ++ [(k, v)]⟩

/-- `m.delete(k)`: the map without the entry of `k`. -/
def delete (m : JSMap K V) (k : K) : JSMap K V := ⟨m.entries.filter fun e => !(e.1 == k)⟩

/-- `m.size`: the number of entries. -/
def size (m : JSMap K V) : Nat := m.entries.length

end JSMap

end tolean.TypeScript
