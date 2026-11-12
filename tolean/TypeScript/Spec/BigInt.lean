/-!
The model of the bitwise operators on a JS `bigint`.

A bigint is an integer of any size, which the translation writes as Lean's
`Int`. ECMA-262 defines `&`, `|` and `^` on bigints by the two's complement
of each operand, extended with copies of its sign bit (BigIntBitwiseOp,
§6.1.6.2.17). Lean's core library has no such operations on `Int`, so this
file defines them from the operations on `Nat`: a negative integer `-[n+1]`
is the complement of `n` in two's complement, so for example
`-[m+1] & -[n+1]` is the complement of `m | n`.

`a << b` is `a × 2^b` (BigInt::leftShift, §6.1.6.2.9), which is
`a / 2^-b` rounded down when `b` is negative. `a >> b` is `a << -b`
(BigInt::signedRightShift, §6.1.6.2.10). `~a` is `-a - 1`
(BigInt::bitwiseNOT, §6.1.6.2.2).

`tests/typescript/bigintBitwise.test.ts` checks each operation against the
JS engine on random operands.

Editions: ES2020, which adds the BigInt type, and every edition after it.
-/
namespace tolean.TypeScript.JSBigInt

/-- The bits of `m` that are not in `n`. -/
def andNot (m n : Nat) : Nat := Nat.bitwise (fun a b => a && !b) m n

/-- `a & b` on bigints (BigInt::bitwiseAND). -/
def bitAnd : Int → Int → Int
  | .ofNat m, .ofNat n => .ofNat (m &&& n)
  | .ofNat m, .negSucc n => .ofNat (andNot m n)
  | .negSucc m, .ofNat n => .ofNat (andNot n m)
  | .negSucc m, .negSucc n => .negSucc (m ||| n)

/-- `a | b` on bigints (BigInt::bitwiseOR). -/
def bitOr : Int → Int → Int
  | .ofNat m, .ofNat n => .ofNat (m ||| n)
  | .ofNat m, .negSucc n => .negSucc (andNot n m)
  | .negSucc m, .ofNat n => .negSucc (andNot m n)
  | .negSucc m, .negSucc n => .negSucc (m &&& n)

/-- `a ^ b` on bigints (BigInt::bitwiseXOR). -/
def bitXor : Int → Int → Int
  | .ofNat m, .ofNat n => .ofNat (m ^^^ n)
  | .ofNat m, .negSucc n => .negSucc (m ^^^ n)
  | .negSucc m, .ofNat n => .negSucc (m ^^^ n)
  | .negSucc m, .negSucc n => .ofNat (m ^^^ n)

/-- `~a` on a bigint (BigInt::bitwiseNOT). -/
def bitNot (a : Int) : Int := -a - 1

/-- `a << b` on bigints (BigInt::leftShift): `a × 2^b`, rounded down when `b`
is negative. `Int.shiftRight` rounds down. -/
def shiftLeft (a b : Int) : Int :=
  if 0 ≤ b then a <<< b.toNat else a >>> (-b).toNat

/-- `a >> b` on bigints (BigInt::signedRightShift). -/
def shiftRight (a b : Int) : Int := shiftLeft a (-b)

end tolean.TypeScript.JSBigInt
