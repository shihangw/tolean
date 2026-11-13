import tolean.TypeScript.Spec.Eval
import tolean.TypeScript.Syntax.Parser
import tolean.TypeScript.Translate
import Lean.Data.Json

/-!
The interpreter of `Spec/Eval.lean`, run on real doubles, for the test that
compares it with Node (`tests/typescript/interpreter.test.ts`).

The interpreter is generic over the number model `N`. Here `N` is Lean's
`Float`, which is an IEEE 754 double with the same rounding as a JS
`number`, so the interpreter computes what JS computes. Nothing in `Spec/`
or in the proofs uses this model: the proofs hold for every `N`.

`tolean interpret` reads programs and calls as JSON, runs each call in the
interpreter, and prints the results as JSON. A value is written so that
Node can read it back exactly:

- a bigint as `{"bigint": "<decimal>"}`;
- a number as `{"number": "<the 64 bits of the double, in decimal>"}`, so
  that `-0` and each `NaN` keep their bits;
- a boolean, a string and `null` as themselves;
- an array as a JSON array;
- an object as `{"object": [["<key>", <value>], …]}`, in the order of its
  keys;
- an error object as `{"error": ["<class>", [["<key>", <value>], …]]}`, with
  its own properties, such as `message`;
- a date as `{"date": "<time value in decimal>"}`, or `{"date": null}` when
  it is invalid.
-/
namespace tolean.TypeScript.Interpret

open Lean (Json)
open tolean.TypeScript.Eval (Val)

/-- `a * 2^b < c * 10^d` and the like, exactly: the two sides as integers
after moving each negative exponent to the other side. -/
def cmpScaled (a : Nat) (b : Int) (c : Nat) (d : Int) : Ordering :=
  let l := a * 2 ^ b.toNat * 10 ^ (-d).toNat
  let r := c * 10 ^ d.toNat * 2 ^ (-b).toNat
  compare l r

/-- The decimal digits of `n`. -/
def digitsOf (n : Nat) : String := toString n

/-- Number::toString of a positive finite double `m * 2^e`, whose rounding
interval is `(lo, hi)` around it, with the ends in it when `even`. -/
def shortest (m : Nat) (e : Int) (loNum : Nat) (loExp : Int) (hiNum : Nat) (hiExp : Int) (even : Bool) :
    Nat × Int × Nat :=
  -- `n` with 10^(n-1) ≤ v < 10^n.
  let v := (m, e)
  let below (d : Int) : Bool := cmpScaled v.1 v.2 1 d == .lt  -- v < 10^d
  let n0 : Int := ((e + Nat.log2 m + 1) * 30103 / 100000)
  let rec up (n : Int) : Nat → Int
    | 0 => n
    | f + 1 => if below n then n else up (n + 1) f
  let rec down (n : Int) : Nat → Int
    | 0 => n
    | f + 1 => if below (n - 1) then down (n - 1) f else n
  let n := down (up n0 40) 40
  let inside (s : Nat) (d : Int) : Bool :=
    let gtLo := match cmpScaled loNum loExp s d with | .lt => true | .eq => even | .gt => false
    let ltHi := match cmpScaled hiNum hiExp s d with | .gt => true | .eq => even | .lt => false
    gtLo && ltHi
  -- `|s * 10^d - v|` compared between two candidates, as twice the scale.
  let rec tryK : Nat → Nat × Int × Nat
    | 0 => (m, e, 0)  -- unreachable: 17 digits always suffice
    | fuel + 1 =>
      let k : Nat := 18 - (fuel + 1)
      let d : Int := n - k
      -- s = floor(v / 10^d)
      let num := m * 2 ^ e.toNat * 10 ^ (-d).toNat
      let den := 10 ^ d.toNat * 2 ^ (-e).toNat
      let s := num / den
      let lowOk := inside s d
      let highOk := inside (s + 1) d
      if lowOk && highOk then
        -- The closer one: compare v - s*10^d with (s+1)*10^d - v, that is
        -- 2v with (2s+1)*10^d.
        match cmpScaled (2 * m) e (2 * s + 1) d with
        | .lt => (s, n, k)
        | .gt => (s + 1, n, k)
        | .eq => if s % 2 == 0 then (s, n, k) else (s + 1, n, k)
      else if lowOk then (s, n, k)
      else if highOk then (s + 1, n, k)
      else tryK fuel
  tryK 17

/-- Formats `s * 10^(n-k)`, where `s` has `k` digits, as Number::toString
does (§6.1.6.1.20, steps 6 to 12). -/
def format (s : Nat) (n : Int) (k : Nat) : String :=
  -- A rounded-up `s` may have k + 1 digits, such as 10 for k = 1.
  let (s, n, k) := if (digitsOf s).length > k then (s / 10, n + 1, k) else (s, n, k)
  let ds := digitsOf s
  if k ≤ n ∧ n ≤ 21 then ds ++ String.ofList (List.replicate (n - k).toNat '0')
  else if 0 < n ∧ n ≤ 21 then String.ofList (ds.toList.take n.toNat) ++ "." ++ String.ofList (ds.toList.drop n.toNat)
  else if -6 < n ∧ n ≤ 0 then "0." ++ String.ofList (List.replicate (-n).toNat '0') ++ ds
  else
    let e := n - 1
    let sign := if e < 0 then "-" else "+"
    let mant := if k = 1 then ds else String.ofList (ds.toList.take 1) ++ "." ++ String.ofList (ds.toList.drop 1)
    mant ++ "e" ++ sign ++ toString e.natAbs

/-- Number::toString of a positive finite double. -/
def positiveToString (x : Float) : String :=
    let bits : Nat := x.toBits.toNat
    let ef : Nat := (bits / 2 ^ 52) % 2048
    let f : Nat := bits % 2 ^ 52
    let (m, e) : Nat × Int := if ef = 0 then (f, -1074) else (f + 2 ^ 52, (ef : Int) - 1075)
    -- The neighbours are half an ulp away, and a quarter below a power of two.
    let (loNum, loExp) : Nat × Int :=
      if f = 0 ∧ ef > 1 then (4 * m - 1, e - 2) else (2 * m - 1, e - 1)
    let (s, n, k) := shortest m e loNum loExp (2 * m + 1) (e - 1) (m % 2 == 0)
    format s n k

/-- Number::toString(x) with radix 10 (ECMA-262 §6.1.6.1.20). -/
def jsNumberToString (x : Float) : String :=
  if x.isNaN then "NaN"
  else if x == 0 then "0"
  else if x.isInf then (if x < 0 then "-Infinity" else "Infinity")
  else if x < 0 then "-" ++ positiveToString (-x)
  else positiveToString x
/-- `-0` is the one double that is `0` and whose reciprocal is negative. -/
def isNegZero (x : Float) : Bool := x == 0 && 1 / x < 0

/-- `Math.trunc(x)`: the integer part, toward zero. `ceil` keeps the sign of a
negative `x` that rounds to zero, as JS does. -/
def jsTrunc (x : Float) : Float := if x < 0 then x.ceil else x.floor

/-- `Math.round(x)` (ECMA-262 §21.3.2.28): the nearest integer, and the larger
one at a half. `x - floor(x)` is exact, so the test of the half is too. A
negative `x` that rounds to zero gives `-0`. -/
def jsRound (x : Float) : Float :=
  if !x.isFinite then x
  else
    let r := x.floor
    let y := if x - r ≥ 0.5 then r + 1 else r
    if y == 0 && (x < 0 || isNegZero x) then -0.0 else y

/-- `Math.min(a, b)` (§21.3.2.25): `NaN` when either is `NaN`, and `-0` is less
than `+0`. -/
def jsMin (a b : Float) : Float :=
  if a.isNaN || b.isNaN then 0.0 / 0.0
  else if a == 0 && b == 0 then (if isNegZero a then a else b)
  else if a < b then a else b

/-- `Math.max(a, b)` (§21.3.2.24): `NaN` when either is `NaN`, and `+0` is
greater than `-0`. -/
def jsMax (a b : Float) : Float :=
  if a.isNaN || b.isNaN then 0.0 / 0.0
  else if a == 0 && b == 0 then (if isNegZero a then b else a)
  else if a > b then a else b

/-- The integer that a finite double is after its fraction is dropped, read
exactly from its bits: the significand times a power of two, toward zero.
`Float.toInt64` would saturate past 2^63, where JS keeps every bit. -/
def jsToInt (x : Float) : Option Int :=
  if !x.isFinite then none
  else
    let bits := x.toBits
    let exp := ((bits >>> 52) &&& 0x7FF).toNat
    let frac := (bits &&& 0xFFFFFFFFFFFFF).toNat
    -- A subnormal double is less than 1, so its integer part is 0.
    if exp == 0 then some 0
    else
      let m := frac + 2 ^ 52
      let magnitude : Nat :=
        if exp ≥ 1075 then m * 2 ^ (exp - 1075) else m / 2 ^ (1075 - exp)
      some (if bits >>> 63 == 1 then -(magnitude : Int) else magnitude)

/-- The double nearest to `n`, with ties to the one whose last bit is zero:
the Number value for `n` (ECMA-262 §6.1.6.1). A natural below 2^53 is a
double already. Above it, the 53 highest bits round by the bits below them.
`Float.ofNat` keeps only 64 bits before it rounds, which can round a value
just past a halfway point down. -/
def natToDouble (n : Nat) : Float :=
  if n < 2 ^ 53 then Float.ofNat n
  else
    let shift := Nat.log2 n - 52
    let q := n >>> shift
    let r := n - (q <<< shift)
    let half := 2 ^ (shift - 1)
    let q := if r > half || (r == half && q % 2 == 1) then q + 1 else q
    -- `q` has at most 54 bits, so it is a double, and `scaleB` is exact up
    -- to the largest double, past which it gives `Infinity`.
    (Float.ofNat q).scaleB shift

/-- JS numbers as Lean's IEEE 754 doubles. -/
instance : JSNumber Float where
  toInt := jsToInt
  isNegZero := isNegZero
  ofInt i := if i < 0 then -(natToDouble i.natAbs) else natToDouble i.natAbs
  add := Float.add
  sub := Float.sub
  mul := Float.mul
  div := Float.div
  neg := Float.neg
  floor := Float.floor
  ceil := Float.ceil
  trunc := jsTrunc
  round := jsRound
  abs := Float.abs
  min := jsMin
  max := jsMax
  lt a b := decide (a < b)
  le a b := decide (a ≤ b)
  eq a b := a == b
  ofSafeInt := Float.ofInt
  toSafeInt x :=
    if x.isFinite && x.floor == x && x.abs ≤ 9007199254740991 then some x.toInt64.toInt else none
  toStr x := JSString.ofString (jsNumberToString x)
  isNaN := Float.isNaN
  isFinite := Float.isFinite
  nan := 0.0 / 0.0
  posInf := 1.0 / 0.0
  negInf := -1.0 / 0.0

partial def toJson : Val Float → Json
  | .int i => Json.mkObj [("bigint", toString i)]
  | .num n => Json.mkObj [("number", toString n.toBits)]
  | .bool b => Json.bool b
  -- A string that a JSON string can hold is that text. One that holds a lone
  -- surrogate, as `split("")` can give, is its list of code units, because
  -- the text would turn the surrogate into U+FFFD.
  | .str s =>
    if JSString.ofString s.toString = s then Json.str s.toString
    else Json.mkObj [("utf16", Json.arr (s.units.map fun u => Json.num u.toNat).toArray)]
  | .null => Json.null
  | .undefined => Json.mkObj [("undefined", Json.bool true)]
  | .list xs => Json.arr (xs.map toJson).toArray
  | .obj fs => Json.mkObj [("object", Json.arr (fs.map fun (k, v) => Json.arr #[Json.str k, toJson v]).toArray)]
  | .map es => Json.mkObj [("map", Json.arr (es.map fun (k, v) => Json.arr #[toJson k, toJson v]).toArray)]
  | .set xs => Json.mkObj [("set", Json.arr (xs.map toJson).toArray)]
  | .error cls fs =>
    Json.mkObj [("error", Json.arr #[Json.str cls,
      Json.arr (fs.map fun (k, v) => Json.arr #[Json.str k, toJson v]).toArray])]
  | .date t => Json.mkObj [("date", match t with | some i => Json.str (toString i) | none => Json.null)]
  -- A function cannot leave the function that declares it, so no result
  -- holds one; the test of the interpreter compares only results.
  | .closure _ _ => Json.mkObj [("function", Json.bool true)]

partial def ofJson (j : Json) : Except String (Val Float) :=
  match j with
  | .bool b => pure (.bool b)
  | .str s => pure (.str (JSString.ofString s))
  | .null => pure .null
  | .arr xs => (.list ∘ Array.toList) <$> xs.mapM ofJson
  | j => do
    if let .ok true := j.getObjValAs? Bool "undefined" then return .undefined
    if let .ok (units : Array Nat) := j.getObjValAs? (Array Nat) "utf16" then
      return .str ⟨units.toList.map Nat.toUInt16⟩
    if let .ok (s : String) := j.getObjValAs? String "bigint" then
      let some i := s.toInt? | throw s!"not a bigint: {s}"
      return .int i
    if let .ok (s : String) := j.getObjValAs? String "number" then
      let some bits := s.toNat? | throw s!"not the bits of a double: {s}"
      return .num (Float.ofBits (UInt64.ofNat bits))
    if let .ok (entries : Array Json) := j.getObjValAs? (Array Json) "map" then
      let entries ← entries.mapM fun e => do
        let #[k, v] := (← e.getArr?) | throw "a map entry is not a [key, value] pair"
        return (← ofJson k, ← ofJson v)
      return .map entries.toList
    if let .ok (elems : Array Json) := j.getObjValAs? (Array Json) "set" then
      return .set (← elems.mapM ofJson).toList
    if let .ok (d : Json) := j.getObjVal? "date" then
      if d matches .null then return .date none
      let .ok (s : String) := d.getStr? | throw "a date is not a time value"
      let some i := s.toInt? | throw s!"not a time value: {s}"
      return .date (some i)
    let fields ← j.getObjValAs? (Array Json) "object"
    let fields ← fields.mapM fun f => do
      let #[k, v] := (← f.getArr?) | throw "an object field is not a [key, value] pair"
      return (← k.getStr?, ← ofJson v)
    return .obj fields.toList

/-- The file name that each program has. -/
def file : String := "main.ts"

/-- Run one program: whether the parser and the translator accept it, and the
result of each call. A result is `{"value": <value>}`, or
`{"throws": <value>}` when the call throws, or `null` when the interpreter
gives no value, so a call that returns `null` gives `{"value": null}`. -/
def runProgram (p : Json) : Except String Json := do
  let source ← p.getObjValAs? String "source"
  let target := match p.getObjValAs? String "target" with
    | .ok name => (Edition.parse? name).getD .default
    | .error _ => .default
  let calls ← p.getObjValAs? (Array Json) "calls"
  match Syntax.parse source target with
  | .error _ => return Json.mkObj [("parsed", false)]
  | .ok m =>
    let accepted := (Translate.translateTree file source target).toBool
    let results ← calls.mapM fun c => do
      let name ← c.getObjValAs? String "function"
      let args ← (← c.getObjValAs? (Array Json) "args").mapM ofJson
      return match Eval.callIn [(file, m)] ⟨file, name⟩ args.toList with
        | some (.ok v) => Json.mkObj [("value", toJson v)]
        | some (.error t) => Json.mkObj [("throws", toJson t)]
        | none => Json.null
    return Json.mkObj [("parsed", true), ("accepted", accepted), ("results", Json.arr results)]

/-- `{"programs": [{"source", "target"?, "calls": [{"function", "args"}]}]}`
to `{"programs": [{"parsed", "accepted", "results"}]}`. -/
def interpret (input : String) : Except String String := do
  let programs ← (← Json.parse input).getObjValAs? (Array Json) "programs"  let out ← programs.mapM runProgram
  return (Json.mkObj [("programs", Json.arr out)]).compress

end tolean.TypeScript.Interpret
