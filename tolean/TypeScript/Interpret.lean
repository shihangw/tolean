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
  keys.
-/
namespace tolean.TypeScript.Interpret

open Lean (Json)
open tolean.TypeScript.Eval (Val)

/-- JS numbers as Lean's IEEE 754 doubles. -/
instance : JSNumber Float where
  add := Float.add
  sub := Float.sub
  mul := Float.mul
  neg := Float.neg
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
  | .str s => Json.str s
  | .null => Json.null
  | .list xs => Json.arr (xs.map toJson).toArray
  | .obj fs => Json.mkObj [("object", Json.arr (fs.map fun (k, v) => Json.arr #[Json.str k, toJson v]).toArray)]

partial def ofJson (j : Json) : Except String (Val Float) :=
  match j with
  | .bool b => pure (.bool b)
  | .str s => pure (.str s)
  | .null => pure .null
  | .arr xs => (.list ∘ Array.toList) <$> xs.mapM ofJson
  | j => do
    if let .ok (s : String) := j.getObjValAs? String "bigint" then
      let some i := s.toInt? | throw s!"not a bigint: {s}"
      return .int i
    if let .ok (s : String) := j.getObjValAs? String "number" then
      let some bits := s.toNat? | throw s!"not the bits of a double: {s}"
      return .num (Float.ofBits (UInt64.ofNat bits))
    let fields ← j.getObjValAs? (Array Json) "object"
    let fields ← fields.mapM fun f => do
      let #[k, v] := (← f.getArr?) | throw "an object field is not a [key, value] pair"
      return (← k.getStr?, ← ofJson v)
    return .obj fields.toList

/-- The file name that each program has. -/
def file : String := "main.ts"

/-- Run one program: whether the parser and the translator accept it, and the
result of each call, or `null` when the interpreter gives no value. -/
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
      return match Eval.runIn [(file, m)] ⟨file, name⟩ args.toList with
        | some v => toJson v
        | none => Json.null
    return Json.mkObj [("parsed", true), ("accepted", accepted), ("results", Json.arr results)]

/-- `{"programs": [{"source", "target"?, "calls": [{"function", "args"}]}]}`
to `{"programs": [{"parsed", "accepted", "results"}]}`. -/
def interpret (input : String) : Except String String := do
  let programs ← (← Json.parse input).getObjValAs? (Array Json) "programs"
  let out ← programs.mapM runProgram
  return (Json.mkObj [("programs", Json.arr out)]).compress

end tolean.TypeScript.Interpret
