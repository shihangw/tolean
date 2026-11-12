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

Editions: every edition Tolean supports (`tolean.TypeScript.Edition`). ECMA-262
has defined a `number` as an IEEE-754 binary64 double since its first edition
(the Number type, with `Number::add`, `Number::divide`, `Number::lessThan` and
the like), `Math.floor`, `Math.ceil`, `Math.round`, `Math.abs`, `Math.min` and
`Math.max` since its first edition, and `Number.isSafeInteger`, `Number.isNaN`,
`Number.isFinite`, `Number.isInteger` and `Math.trunc` since ES2015. ECMA-262
defines each of these exactly, unlike `Math.sin` and its relatives, whose
results it leaves to the engine.
Engines: the laws pass on each engine in `engines` in `flake.nix`
(`nix run .#test-engines`).
-/
import tolean.TypeScript.Spec.BigInt

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
  /-- `a / b` (Number::divide, §6.1.6.1.5): the double nearest to the
  quotient, `±Infinity` for a nonzero `a` over a zero `b`, and `NaN` for `0 / 0`. -/
  div : N → N → N
  neg : N → N
  /-- `Math.floor(x)` (§21.3.2.16) -/
  floor : N → N
  /-- `Math.ceil(x)` (§21.3.2.10) -/
  ceil : N → N
  /-- `Math.trunc(x)` (§21.3.2.35) -/
  trunc : N → N
  /-- `Math.round(x)` (§21.3.2.28): the nearest integer, and the larger one
  when `x` is halfway between two. -/
  round : N → N
  /-- `Math.abs(x)` (§21.3.2.1) -/
  abs : N → N
  /-- `Math.min(a, b)` (§21.3.2.25): `NaN` when either is `NaN`, and `-0` is
  less than `+0`. -/
  min : N → N → N
  /-- `Math.max(a, b)` (§21.3.2.24) -/
  max : N → N → N
  /-- The integer that `x` is after its fraction is dropped, when `x` is
  finite, and `none` for `NaN` and `±Infinity`: truncate(ℝ(x)), which
  ToInt32 (§7.1.6) starts from. A double is a fraction with a power of two
  below it, so this integer is exact, however large `x` is. -/
  toInt : N → Option Int
  /-- `x` is `-0`, which `===` does not tell from `+0`, but `Object.is` does. -/
  isNegZero : N → Bool
  /-- `Number(b)` on a bigint `b` (§21.1.1.1): the Number value for `b`
  (§6.1.6.1), the double nearest to it, with ties to the one whose last bit
  is zero, and `±Infinity` beyond the largest double. -/
  ofInt : Int → N
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

/-- `Math.min(...xs)` (§21.3.2.25). The spec starts from `+Infinity` and
takes each argument in turn, so this is a fold of `Math.min` of two. A `NaN`
ends the spec's loop, and `Math.min(NaN, x)` is `NaN`, so the fold gives the
same value. `Math.min()` is `+Infinity`. -/
def JSNumber.minimum {N : Type} [JSNumber N] (xs : List N) : N := xs.foldl min posInf

/-- `Math.max(...xs)` (§21.3.2.24), a fold from `-Infinity`. -/
def JSNumber.maximum {N : Type} [JSNumber N] (xs : List N) : N := xs.foldl max negInf

/-- `Number.isInteger(x)` (§21.1.2.3): IsIntegralNumber (§7.2.6), which holds
when `x` is finite and its truncation is `x`. -/
def JSNumber.isInteger {N : Type} [JSNumber N] (x : N) : Bool := isFinite x && eq (trunc x) x

/-- The integer in `[-2^31, 2^31)` that is `i` modulo 2^32. -/
def wrapInt32 (i : Int) : Int :=
  let b := i % 4294967296
  if b ≥ 2147483648 then b - 4294967296 else b

/-- ToInt32 (§7.1.6): `NaN`, `±Infinity` and `±0` are `0`, and any other
number is its integer part modulo 2^32, as a signed 32-bit integer. -/
def JSNumber.toInt32 {N : Type} [JSNumber N] (x : N) : Int := wrapInt32 ((toInt x).getD 0)

/-- ToUint32 (§7.1.7): the same, as an unsigned 32-bit integer. -/
def JSNumber.toUint32 {N : Type} [JSNumber N] (x : N) : Int := ((toInt x).getD 0) % 4294967296

/-- `a & b` on numbers (Number::bitwiseAND, §6.1.6.1.17): the operation on
the two's complement of ToInt32 of each, which `JSBigInt.bitAnd` is for
integers of that range. The result is a 32-bit integer, so it is safe. -/
def JSNumber.bitAnd {N : Type} [JSNumber N] (a b : N) : N :=
  ofSafeInt (JSBigInt.bitAnd (toInt32 a) (toInt32 b))

/-- `a | b` on numbers (Number::bitwiseOR, §6.1.6.1.19). -/
def JSNumber.bitOr {N : Type} [JSNumber N] (a b : N) : N :=
  ofSafeInt (JSBigInt.bitOr (toInt32 a) (toInt32 b))

/-- `a ^ b` on numbers (Number::bitwiseXOR, §6.1.6.1.18). -/
def JSNumber.bitXor {N : Type} [JSNumber N] (a b : N) : N :=
  ofSafeInt (JSBigInt.bitXor (toInt32 a) (toInt32 b))

/-- `~a` on a number (Number::bitwiseNOT, §6.1.6.1.2): `-x - 1` for `x` the
ToInt32 of `a`, which stays a 32-bit integer. -/
def JSNumber.bitNot {N : Type} [JSNumber N] (a : N) : N := ofSafeInt (JSBigInt.bitNot (toInt32 a))

/-- `a << b` on numbers (Number::leftShift, §6.1.6.1.9): ToInt32 of `a`,
shifted left by ToUint32 of `b` modulo 32, as a signed 32-bit integer. -/
def JSNumber.shiftLeft {N : Type} [JSNumber N] (a b : N) : N :=
  ofSafeInt (wrapInt32 (toInt32 a * 2 ^ (toUint32 b % 32).toNat))

/-- `a >> b` on numbers (Number::signedRightShift, §6.1.6.1.10): ToInt32 of
`a`, shifted right with copies of its sign bit, which rounds down. -/
def JSNumber.shiftRight {N : Type} [JSNumber N] (a b : N) : N :=
  ofSafeInt (toInt32 a >>> (toUint32 b % 32).toNat)

/-- `a >>> b` on numbers (Number::unsignedRightShift, §6.1.6.1.11): ToUint32
of `a`, shifted right with zeros. -/
def JSNumber.unsignedShiftRight {N : Type} [JSNumber N] (a b : N) : N :=
  ofSafeInt (toUint32 a >>> (toUint32 b % 32).toNat)

/-- Number::sameValue (§6.1.6.1.14), which `Object.is` uses (SameValue,
§7.2.10): `===`, except that `NaN` is the same as `NaN`, and `+0` is not the
same as `-0`. -/
def JSNumber.sameValue {N : Type} [JSNumber N] (a b : N) : Bool :=
  (isNaN a && isNaN b) || (eq a b && isNegZero a == isNegZero b)

/-- SameValueZero (ECMA-262 §7.2.11) on numbers: `===`, except that `NaN` is
the same as `NaN`. `Array.prototype.includes` compares with it. -/
def JSNumber.sameValueZero {N : Type} [JSNumber N] (a b : N) : Bool :=
  eq a b || (isNaN a && isNaN b)

/-- `xs[i]` with a number `i`: the element whose index is `i`, when `i` is a
safe integer within the array, and `none` otherwise. An index is a property
key, and no other number is the key of an element (ECMA-262 §10.4.2). -/
def JSNumber.elementAt? {N α : Type} [JSNumber N] (xs : List α) (i : N) : Option α :=
  match toSafeInt i with
  | some k => if 0 ≤ k then xs[k.toNat]? else none
  | none => none

/-- The sign of `v`, the value of a sort's comparator, as
`Array.prototype.sort` reads it: `lt` when `v < 0`, `gt` when `v > 0`, and
`eq` when `v` is `+0` or `-0` (CompareArrayElements, ECMA-262 §23.1.3.30.2).
It is none for `NaN`, which a consistent comparator never gives
(§23.1.3.30.1). -/
def JSNumber.compareSign {N : Type} [JSNumber N] (v : N) : Option Ordering :=
  if lt v (ofSafeInt 0) then some .lt
  else if lt (ofSafeInt 0) v then some .gt
  else if eq v (ofSafeInt 0) then some .eq
  else none

/-- `xs.toSorted(cmp)` and `[...xs].sort(cmp)` when `cmp` is consistent for
the elements of `xs`: the stable merge sort, where `a` comes after `b` only
when `cmp a b` is greater than `0`. The interpreter gives this order
(`Eval.sortValues`). -/
def JSNumber.sortWith {N α : Type} [JSNumber N] (cmp : α → α → N) (xs : List α) : List α :=
  xs.mergeSort fun a b => compareSign (cmp a b) != some .gt

/-- `ToIntegerOrInfinity(x)` (ECMA-262 §7.1.5), as `at` and `slice` read an
index: `NaN` is `0`, and a finite number loses its fraction, rounded toward
zero, as `toInt` gives it. `Infinity` becomes `2^53` and `-Infinity`
becomes `-2^53`. That changes no index, because an array has fewer than 2^32
elements: either way, the index is past the end of the array, or before its
start. -/
def JSNumber.toIndexInt {N : Type} [JSNumber N] (x : N) : Int :=
  match toInt x with
  | some i => i
  | none => if isNaN x then 0 else if lt x (ofSafeInt 0) then -(maxSafe + 1) else maxSafe + 1

/-- `xs.at(i)` with a number `i` (`Array.prototype.at`, ECMA-262 §23.1.3.1):
the element at the index that `toIndexInt` gives, counted from the end when
it is negative, or `none` when the index is outside the array. -/
def JSNumber.atIndex? {N α : Type} [JSNumber N] (xs : List α) (i : N) : Option α :=
  let k := toIndexInt i
  if 0 ≤ k then xs[k.toNat]? else xs.reverse[(-k - 1).toNat]?

/-- `xs.entries()` (`Array.prototype.entries`, ECMA-262 §23.1.3.4), as a loop
or a spread visits it: each element with its index, as a number. An array
has fewer than 2^32 elements, so each index is a safe integer. -/
def JSNumber.entries {N α : Type} [JSNumber N] (xs : List α) : List (N × α) :=
  xs.mapIdx fun i x => (ofSafeInt i, x)

/-- A relative index into a list of `len` elements, as `slice` reads its
bounds: a negative `k` counts from the end, and the result is clamped to `0`
and `len`. -/
def JSNumber.clampIndex (len : Nat) (k : Int) : Nat :=
  if k < 0 then (len + k).toNat else Nat.min k.toNat len

/-- `xs.slice(start, stop)` (`Array.prototype.slice`, ECMA-262 §23.1.3.28),
where `start` and `stop` are the integers of the arguments: the elements from
`start` up to `stop`, or to the end when `stop` is none. -/
def JSNumber.sliceInt {α : Type} (xs : List α) (start : Int) (stop : Option Int) : List α :=
  let k := clampIndex xs.length start
  let final := match stop with
    | some e => clampIndex xs.length e
    | none => xs.length
  (xs.drop k).take (final - k)

/-- The values of `i` from the safe integer `k` on, for as long as `i < b`
holds, after the values in `acc`, which are in reverse order. At most `left`
values may come, and `none` means that the loop would go on past them. The
list grows in `acc`, so the recursion is a loop. -/
def JSNumber.countFrom {N : Type} [JSNumber N] (b : N) (acc : List N) (k : Int) : Nat → Option (List N)
  | 0 => none
  | left + 1 =>
    if lt (ofSafeInt k) b then countFrom b (ofSafeInt k :: acc) (k + 1) left else some acc.reverse

/-- The values that `i` takes in `for (let i = k; i < b; i++)`, where the start
`k` is an integer literal: `k`, then each integer after it, for as long as it
is less than `b`. It is `none` when `i` would pass `Number.MAX_SAFE_INTEGER`,
as it would for a bound of `Infinity`.

The literal `k` is the number `ofSafeInt k`, and on safe integers `i++` adds
one exactly (`SafeIntLaws.add`), so these are the values that JS gives. -/
def JSNumber.countUp? {N : Type} [JSNumber N] (k : Int) (b : N) : Option (List N) :=
  countFrom b [] k (maxSafe - k + 1).toNat

/-- `countUp?`, empty when it is `none`. The translation of a counted loop runs
over this list. -/
def JSNumber.countUp {N : Type} [JSNumber N] (k : Int) (b : N) : List N :=
  (countUp? k b).getD []

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
  div : ∀ {a b : N} {i j : Int}, toSafeInt a = some i → toSafeInt b = some j →
    j ≠ 0 → i.tmod j = 0 → toSafeInt (div a b) = some (i.tdiv j)
  floor : ∀ {a : N} {i : Int}, toSafeInt a = some i → toSafeInt (floor a) = some i
  ceil : ∀ {a : N} {i : Int}, toSafeInt a = some i → toSafeInt (ceil a) = some i
  trunc : ∀ {a : N} {i : Int}, toSafeInt a = some i → toSafeInt (trunc a) = some i
  round : ∀ {a : N} {i : Int}, toSafeInt a = some i → toSafeInt (round a) = some i
  abs : ∀ {a : N} {i : Int}, toSafeInt a = some i → toSafeInt (abs a) = some (i.natAbs : Int)
  min : ∀ {a b : N} {i j : Int}, toSafeInt a = some i → toSafeInt b = some j →
    toSafeInt (min a b) = some (Min.min i j)
  max : ∀ {a b : N} {i j : Int}, toSafeInt a = some i → toSafeInt b = some j →
    toSafeInt (max a b) = some (Max.max i j)
  toInt : ∀ {a : N} {i : Int}, toSafeInt a = some i → toInt a = some i
  ofInt : ∀ {i : Int}, InRange i → toSafeInt (ofInt (N := N) i) = some i
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
  nan_div : ∀ {a b : N}, isNaN a = true → isNaN (div a b) = true ∧ isNaN (div b a) = true
  nan_floor : ∀ {a : N}, isNaN a = true → isNaN (floor a) = true
  nan_ceil : ∀ {a : N}, isNaN a = true → isNaN (ceil a) = true
  nan_trunc : ∀ {a : N}, isNaN a = true → isNaN (trunc a) = true
  nan_round : ∀ {a : N}, isNaN a = true → isNaN (round a) = true
  nan_abs : ∀ {a : N}, isNaN a = true → isNaN (abs a) = true
  nan_min : ∀ {a b : N}, isNaN a = true → isNaN (min a b) = true ∧ isNaN (min b a) = true
  nan_max : ∀ {a b : N}, isNaN a = true → isNaN (max a b) = true ∧ isNaN (max b a) = true
  toInt_not_finite : ∀ {a : N}, isFinite a = false → toInt a = none
  negZero_eq_zero : ∀ {a : N}, isNegZero a = true → eq a (ofSafeInt 0) = true
  negZero_ofSafeInt : ∀ {i : Int}, isNegZero (ofSafeInt (N := N) i) = false
  nan_not_negZero : ∀ {a : N}, isNaN a = true → isNegZero a = false
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
