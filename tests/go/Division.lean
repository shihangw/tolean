import tolean.Go.Syntax.Parser
import tolean.Go.Proof.Package

/-!
Integer `/` and `%` on the proved path. The IR's evaluator and the
interpreter must give the same value, or the same panic, for each input.
-/

open tolean.Go

private def parseDecls (src : String) : Except String (List Syntax.Decl) := do
  match Syntax.parse ("package divide\n" ++ src) with
  | .ok file => return file.decls
  | .error _ => throw "the division test did not parse"

/-- Equal results of a call. `Except` has no `BEq` instance. -/
private def same : Option (Except Eval.Val Eval.Val) → Option (Except Eval.Val Eval.Val) → Bool
  | some (.ok a), some (.ok b) | some (.error a), some (.error b) => a == b
  | none, none => true
  | _, _ => false

/-- `F` is translated, and both sides give `expected` for `args`. -/
private def check (src : String) (args : List Int) (expected : Except Eval.Val Eval.Val) : Bool :=
  match parseDecls src with
  | .error _ => false
  | .ok decls =>
    let translated := Pure.translateFuncs decls ["F"]
    let vs := args.map Eval.Val.int
    translated.length == 1 &&
      same (IR.runIn (IR.functions (translated.map (·.1))) ⟨"", "F"⟩ vs) (some expected) &&
      same (Eval.runIn (Eval.program decls) "F" vs) (some expected)

private def refused (src : String) : Bool :=
  match parseDecls src with
  | .error _ => false
  | .ok decls => (Pure.translateFuncs decls ["F"]).isEmpty

private def panics : Except Eval.Val Eval.Val := .error Eval.divideByZero
private def ok (i : Int) : Except Eval.Val Eval.Val := .ok (.int i)

private def quo := "func F(a int, b int) int { return a / b }"
private def rem := "func F(a int, b int) int { return a % b }"

#guard check quo [7, 2] (ok 3)
#guard check quo [-7, 2] (ok (-3))
#guard check quo [7, -2] (ok (-3))
#guard check quo [7, 0] panics
#guard check quo [-9223372036854775808, -1] (ok (-9223372036854775808))
#guard check rem [7, 2] (ok 1)
#guard check rem [-7, 2] (ok (-1))
#guard check rem [7, -2] (ok 1)
#guard check rem [7, 0] panics
#guard check rem [-9223372036854775808, -1] (ok 0)
-- The panic of the first statement that divides by zero.
#guard check "func F(a int, b int) int { x := a / b; x /= a; return x % 3 }" [6, 2] (ok 0)
#guard check "func F(a int, b int) int { x := a / b; x /= a; return x % 3 }" [0, 2] panics
#guard check "func F(a int, b int) int { x := a / b; x /= a; return x % 3 }" [6, 0] panics
#guard check "func F(a int, b int) int { var x int = a % b; x %= 4; return x }" [7, 5] (ok 2)
#guard check "func F(a int, b int) int { if a / b > 1 { return 1 }; return 0 }" [3, 2] (ok 0)
#guard check "func F(a int, b int) int { if a / b > 1 { return 1 }; return 0 }" [6, 2] (ok 1)
#guard check "func F(a int, b int) int { if a / b > 1 { return 1 }; return 0 }" [6, 0] panics
#guard check "func F(a int, b int) int { x := 0; if b != 0 { x = a / b }; return x }" [6, 0] (ok 0)
#guard check "func F(a int, b int) int { x := 0; if b != 0 { x = a / b }; return x }" [6, 3] (ok 2)
#guard check "func F(a int, b int) int { x := 0; if b < 9 { x = a / b }; return x }" [6, 0] panics
#guard check "func F(a int, b int) int { return (a / b) / (b - 2) }" [8, 2] panics
#guard check "func F(a int, b int) int { return (a / b) / (b - 2) }" [8, 4] (ok 1)
#guard check "func F(a int, b int) int { for i := 0; i < 3; i++ { a = a / (b - i) }; return a }"
  [60, 5] (ok 1)
#guard check "func F(a int, b int) int { for i := 0; i < 3; i++ { a = a / (b - i) }; return a }"
  [60, 1] panics
#guard check "func F(a int, b int) int { return a / -1 }" [5, 0] (ok (-5))
-- Go refuses a constant zero divisor, and Go might not evaluate the right
-- operand of && and ||, so the translator refuses a division there.
#guard refused "func F(a int, b int) int { return a / 0 }"
#guard refused "func F(a int, b int) int { return a % -0 }"
#guard refused "func F(a int, b int) bool { return b != 0 && a / b > 1 }"
#guard refused "func F(a int, b int) bool { return b == 0 || a % b > 1 }"
#guard refused "func F(a string, b string) string { return a / b }"
-- A call of a function that can panic is not supported yet.
#guard refused "func G(a int) int { return 1 / a }\nfunc F(a int, b int) int { return G(a) }"

#print axioms Proof.translate_sound
