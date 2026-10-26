/-
The model of a JS `number` that `tolean` translates to.

A JS `number` is an IEEE-754 double. Lean's `Float` has no lemmas, so it
cannot support proofs. Instead, generated code is generic over an abstract
type `N` with the operations JS uses. A theorem proved for every `N` holds for
real doubles with nothing assumed.

Facts about doubles enter only as hypotheses, in two classes:

- `SafeIntLaws`: on safe integers (`Number.isSafeInteger`), JS arithmetic and
  comparison agree with `Int`.
- `SpecialValueLaws`: how `NaN` and `±Infinity` behave. `===` is reflexive
  except for `NaN`, `NaN` fails every comparison and spreads through
  arithmetic, and `±Infinity` bound every finite number.

A theorem that needs them takes `[SafeIntLaws N]` or `[SpecialValueLaws N]`.
These are hypotheses, not postulates: if one were false, the theorem would not
apply to JS, but Lean stays consistent. `tests/typescript/jsNumberLaws.test.ts`
checks each one against JS.

Editions: every edition tolean supports (`tolean.TypeScript.Edition`). ECMA-262
has defined a `number` as an IEEE-754 binary64 double since its first edition
(the Number type, with `Number::add`, `Number::lessThan` and the like), and
`Number.isSafeInteger`, `Number.isNaN` and `Number.isFinite` since ES2015.
Engines: the laws pass on each engine in `engines` in `flake.nix`
(`nix run .#test-engines`).
-/
namespace tolean.TypeScript

/-- `Number.MAX_SAFE_INTEGER`, 2⁵³ − 1. -/
def maxSafe : Int := 9007199254740991

/-- The safe-integer range, `[-(2⁵³ − 1), 2⁵³ − 1]`. -/
def InRange (i : Int) : Prop := -maxSafe ≤ i ∧ i ≤ maxSafe

/-- An abstract JS `number`: the operations, with nothing assumed about them. -/
class JSNumber (N : Type) where
  add : N → N → N
  sub : N → N → N
  mul : N → N → N
  neg : N → N
  /-- `a < b` -/
  lt : N → N → Bool
  /-- `a <= b` -/
  le : N → N → Bool
  /-- `a === b` -/
  eq : N → N → Bool
  /-- An integer literal in the source. -/
  ofSafeInt : Int → N
  /-- The integer `x` is when `Number.isSafeInteger(x)`, and `none` otherwise. -/
  toSafeInt : N → Option Int
  /-- `Number.isNaN(x)` -/
  isNaN : N → Bool
  /-- `Number.isFinite(x)`: neither `NaN` nor `±Infinity`. -/
  isFinite : N → Bool
  /-- `NaN` -/
  nan : N
  /-- `Infinity` -/
  posInf : N
  /-- `-Infinity` -/
  negInf : N

open JSNumber

/-- On safe integers, JS `number` operations agree with `Int`. -/
class SafeIntLaws (N : Type) [JSNumber N] : Prop where
  toSafeInt_inRange : ∀ {x : N} {i : Int}, toSafeInt x = some i → InRange i
  ofSafeInt : ∀ {i : Int}, InRange i → toSafeInt (ofSafeInt (N := N) i) = some i
  add : ∀ {a b : N} {i j : Int}, toSafeInt a = some i → toSafeInt b = some j →
    InRange (i + j) → toSafeInt (add a b) = some (i + j)
  sub : ∀ {a b : N} {i j : Int}, toSafeInt a = some i → toSafeInt b = some j →
    InRange (i - j) → toSafeInt (sub a b) = some (i - j)
  mul : ∀ {a b : N} {i j : Int}, toSafeInt a = some i → toSafeInt b = some j →
    InRange (i * j) → toSafeInt (mul a b) = some (i * j)
  neg : ∀ {a : N} {i : Int}, toSafeInt a = some i → toSafeInt (neg a) = some (-i)
  lt : ∀ {a b : N} {i j : Int}, toSafeInt a = some i → toSafeInt b = some j →
    lt a b = decide (i < j)
  le : ∀ {a b : N} {i j : Int}, toSafeInt a = some i → toSafeInt b = some j →
    le a b = decide (i ≤ j)
  eq : ∀ {a b : N} {i j : Int}, toSafeInt a = some i → toSafeInt b = some j →
    eq a b = decide (i = j)

/-- How `NaN` and `±Infinity` behave. -/
class SpecialValueLaws (N : Type) [JSNumber N] : Prop where
  eq_refl : ∀ {a : N}, isNaN a = false → eq a a = true
  eq_symm : ∀ {a b : N}, eq a b = eq b a
  nan_eq : ∀ {a b : N}, isNaN a = true → eq a b = false
  nan_lt : ∀ {a b : N}, isNaN a = true → lt a b = false ∧ lt b a = false
  nan_le : ∀ {a b : N}, isNaN a = true → le a b = false ∧ le b a = false
  nan_add : ∀ {a b : N}, isNaN a = true → isNaN (add a b) = true ∧ isNaN (add b a) = true
  nan_sub : ∀ {a b : N}, isNaN a = true → isNaN (sub a b) = true ∧ isNaN (sub b a) = true
  nan_mul : ∀ {a b : N}, isNaN a = true → isNaN (mul a b) = true ∧ isNaN (mul b a) = true
  isNaN_nan : isNaN (nan (N := N)) = true
  isNaN_posInf : isNaN (posInf (N := N)) = false
  isNaN_negInf : isNaN (negInf (N := N)) = false
  isFinite_posInf : isFinite (posInf (N := N)) = false
  isFinite_negInf : isFinite (negInf (N := N)) = false
  isFinite_not_nan : ∀ {a : N}, isFinite a = true → isNaN a = false
  safe_finite : ∀ {a : N} {i : Int}, toSafeInt a = some i → isFinite a = true
  lt_posInf : ∀ {a : N}, isFinite a = true → lt a posInf = true
  negInf_lt : ∀ {a : N}, isFinite a = true → lt negInf a = true
  sub_posInf_posInf : isNaN (sub (posInf (N := N)) posInf) = true

end tolean.TypeScript
