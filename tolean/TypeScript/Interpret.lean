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
  its own properties, such as `message`.
-/
namespace tolean.TypeScript.Interpret

open Lean (Json)
open tolean.TypeScript.Eval (Val)

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

/-- JS numbers as Lean's IEEE 754 doubles. -/
instance : JSNumber Float where
  toInt := jsToInt
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
