import tolean.Go.Syntax.Parser
import tolean.Go.Proof.Package

/-! Package-level constants on the proved path: the translation and the
interpreter agree, and the constants that the proved path leaves out make it
refuse the function that reads them. -/

open tolean.Go

private def parseDecls (consts body : String) : Except String (List Syntax.Decl) := do
  match Syntax.parse ("package k\n" ++ consts ++ "\nfunc F(x int) int {\n" ++ body ++ "\n}\n") with
  | .ok file => return file.decls
  | .error _ => throw "the constant test did not parse"

/-- `F` is translated, and both sides give `expected` for `input`. -/
private def check (consts body : String) (input expected : Int) : Bool :=
  match parseDecls consts body with
  | .error _ => false
  | .ok decls =>
    let translated := Pure.translateFuncs decls ["F"]
    let same : Option (Except Eval.Val Eval.Val) → Bool
      | some (.ok v) => v == .int expected
      | _ => false
    translated.length == 1 &&
      same (IR.runIn (IR.functions (translated.map (·.1))) ⟨"", "F"⟩ [.int input]) &&
      same (Eval.runIn (Eval.program decls) "F" [.int input])

private def refused (consts body : String) : Bool :=
  match parseDecls consts body with
  | .error _ => false
  | .ok decls => (Pure.translateFuncs decls ["F"]).isEmpty

-- Untyped and typed integer constants, alone and in a group.
#guard check "const N = 7" "return x + N" 3 10
#guard check "const N int = -7" "return x * N" 3 (-21)
#guard check "const (\n  A = 2\n  B int64 = 5\n)" "var y int64 = B; return x + A" 1 3
-- A constant of type int64 does not fit an int.
#guard refused "const B int64 = 5" "return x + B"
-- An untyped constant is exact, so two of them make a constant expression.
#guard refused "const A = 2\nconst B = 3" "return A + B"
-- String and boolean constants.
#guard check "const S = \"ab\"\nconst T bool = true" "if T && S + \"c\" == \"abc\" { return 1 }; return 0" 0 1
-- A local hides a constant.
#guard check "const N = 7" "N := x; return N" 4 4
-- A constant divisor: zero is refused, and another one needs no test.
#guard check "const D = 3" "return x / D" 10 3
#guard refused "const D = 0" "return x / D"
-- Forms that leave the subset: iota, a constant from another constant, a
-- constant of a named type, and one too large for int64.
#guard refused "const (\n  A = iota\n  B\n)" "return x + B"
#guard refused "const A = 2\nconst B = A" "return x + B"
#guard refused "type T int\nconst A T = 2" "return x + A"
#guard refused "const Big = 9223372036854775808" "return x + Big"
-- A package-level `var` stays on the string path.
#guard refused "var V = 2" "return x + V"
