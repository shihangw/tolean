import tolean.TypeScript.Spec.Number

/-!
A JS `Map` and a JS `Set` as Lean values, for the output of the translator.

ECMA-262 keeps the entries of a `Map` in the order that `set` first added each
key (§24.1), and `for … of` visits them in that order. So the model is the
list of entries in that order, with each key at most once. `set` on a key that
the map has changes its value in place, and `delete` removes its entry
(§24.1.3.9 and §24.1.3.3).

A `Set` is the list of its elements in the same way (§24.2).

A map compares keys with SameValueZero (§7.2.11), which `JSKey.same` gives.
On bigints, booleans, strings and literal unions of strings it is Lean's
equality. On numbers it is `JSNumber.sameValueZero`, so `NaN` is the same key
as `NaN` and `+0` the same as `-0`. A map that adds a key stores
`JSKey.stored` of it, which is `+0` for `-0` (§24.1.3.9 and §24.2.4.1).

This file is not trusted. A certificate proves that the output computes what
the interpreter computes, so a wrong definition here would make a certificate
fail, not pass.
-/
namespace tolean.TypeScript

/-- How a map or a set compares its keys and which key it stores. -/
class JSKey (K : Type) where
  /-- SameValueZero (ECMA-262 §7.2.11) on two keys. -/
  same : K → K → Bool
  /-- The key that a map or a set stores when it adds `k`. -/
  stored : K → K

/-- On a type with decidable equality, such as `Int`, `Bool`, `JSString` or a
literal union, SameValueZero is `=`, and a map stores a key as it is. -/
instance (priority := low) JSKey.ofDecidableEq {K : Type} [DecidableEq K] : JSKey K :=
  ⟨fun a b => decide (a = b), id⟩

/-- On numbers, SameValueZero is `===` except that `NaN` is the same as `NaN`,
and a map stores `+0` for `-0`. A number is `+0` or `-0` exactly when it is
`=== 0`. -/
instance JSKey.ofJSNumber {N : Type} [JSNumber N] : JSKey N where
  same := JSNumber.sameValueZero
  stored k := if JSNumber.eq k (JSNumber.ofSafeInt 0) then JSNumber.ofSafeInt 0 else k

/-! The equations of the two instances, which a certificate unfolds the model
with. -/

theorem JSKey.same_ofDecidableEq {K : Type} [DecidableEq K] (a b : K) :
    @JSKey.same K JSKey.ofDecidableEq a b = decide (a = b) := rfl

theorem JSKey.stored_ofDecidableEq {K : Type} [DecidableEq K] (k : K) :
    @JSKey.stored K JSKey.ofDecidableEq k = k := rfl

theorem JSKey.same_ofJSNumber {N : Type} [JSNumber N] (a b : N) :
    @JSKey.same N JSKey.ofJSNumber a b = JSNumber.sameValueZero a b := rfl

theorem JSKey.stored_ofJSNumber {N : Type} [JSNumber N] (k : N) :
    @JSKey.stored N JSKey.ofJSNumber k =
      if JSNumber.eq k (JSNumber.ofSafeInt 0) then JSNumber.ofSafeInt 0 else k := rfl

/-- A JS `Map`: its entries, in the order that `set` first added each key. -/
structure JSMap (K V : Type) where
  entries : List (K × V)
deriving DecidableEq, Repr, Inhabited

namespace JSMap

variable {K V : Type} [JSKey K]

/-- `new Map()`: a map without entries. -/
def empty : JSMap K V := ⟨[]⟩

/-- `m.get(k)`: the value of `k`, or `none` (`undefined`) when the map has no
such key. -/
def get? (m : JSMap K V) (k : K) : Option V := (m.entries.find? (JSKey.same ·.1 k)).map (·.2)

/-- `m.has(k)`. -/
def has (m : JSMap K V) (k : K) : Bool := m.entries.any (JSKey.same ·.1 k)

/-- `m.set(k, v)`: the value of `k` changes in place when the map has `k`, and
a new entry for the stored key of `k` goes last otherwise. -/
def set (m : JSMap K V) (k : K) (v : V) : JSMap K V :=
  if m.has k then ⟨m.entries.map fun e => if JSKey.same e.1 k then (e.1, v) else e⟩
  else ⟨m.entries ++ [(JSKey.stored k, v)]⟩

/-- `m.delete(k)`: the map without the entry of `k`. -/
def delete (m : JSMap K V) (k : K) : JSMap K V := ⟨m.entries.filter fun e => !(JSKey.same e.1 k)⟩

/-- `m.size`: the number of entries. -/
def size (m : JSMap K V) : Nat := m.entries.length

/-- `new Map(items)`: the map after setting each pair of `items`, in order. -/
def ofList (items : List (K × V)) : JSMap K V := items.foldl (fun m e => m.set e.1 e.2) empty

end JSMap

/-- A JS `Set`: its elements, in the order that `add` first added each one
(ECMA-262 §24.2). -/
structure JSSet (T : Type) where
  elems : List T
deriving DecidableEq, Repr, Inhabited

namespace JSSet

variable {T : Type} [JSKey T]

/-- `new Set()`: a set without elements. -/
def empty : JSSet T := ⟨[]⟩

/-- `s.has(x)`. -/
def has (s : JSSet T) (x : T) : Bool := s.elems.any (JSKey.same · x)

/-- `s.add(x)`: the stored key of `x` goes last when the set does not have `x`. -/
def add (s : JSSet T) (x : T) : JSSet T := if s.has x then s else ⟨s.elems ++ [JSKey.stored x]⟩

/-- `s.delete(x)`: the set without `x`. -/
def delete (s : JSSet T) (x : T) : JSSet T := ⟨s.elems.filter fun y => !(JSKey.same y x)⟩

/-- `s.size`: the number of elements. -/
def size (s : JSSet T) : Nat := s.elems.length

/-- `new Set(items)`: the set after adding each of `items`, in order. -/
def ofList (items : List T) : JSSet T := items.foldl add empty

end JSSet

end tolean.TypeScript
