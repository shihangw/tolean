import tolean.Go.Syntax.Parser
import tolean.Go.Proof.Package

/-!
Strings as bytes on the proved path: `len(s)`, `s[i]`, and the orders of
strings. The IR's evaluator and the interpreter must give the same value, or
the same panic, for each input.
-/

open tolean.Go
open tolean.Go.Eval (Val)

private def parseDecls (src : String) : Except String (List Syntax.Decl) := do
  match Syntax.parse ("package strs\n" ++ src) with
  | .ok file => return file.decls
  | .error _ => throw "the string test did not parse"

/-- Equal results of a call. `Except` has no `BEq` instance. -/
private def same : Option (Except Val Val) → Option (Except Val Val) → Bool
  | some (.ok a), some (.ok b) | some (.error a), some (.error b) => a == b
  | none, none => true
  | _, _ => false

/-- `F` is translated, and both sides give `expected` for `args`. -/
private def check (src : String) (args : List Val) (expected : Except Val Val) : Bool :=
  match parseDecls src with
  | .error _ => false
  | .ok decls =>
    let translated := Pure.translateFuncs decls ["F"]
    translated.length == 1 &&
      same (IR.runIn (IR.functions (translated.map (·.1))) ⟨"", "F"⟩ args) (some expected) &&
      same (Eval.runIn (Eval.program decls) "F" args) (some expected)

/-- `G` and then `F` are translated, and both sides give `expected` for a
call of `F`. -/
private def checkCall (src : String) (args : List Val) (expected : Except Val Val) : Bool :=
  match parseDecls src with
  | .error _ => false
  | .ok decls =>
    let translated := Pure.translateFuncs decls ["G", "F"]
    translated.length == 2 &&
      same (IR.runIn (IR.functions (translated.map (·.1))) ⟨"", "F"⟩ args) (some expected) &&
      same (Eval.runIn (Eval.program decls) "F" args) (some expected)

private def refused (src : String) : Bool :=
  match parseDecls src with
  | .error _ => false
  | .ok decls => (Pure.translateFuncs decls ["F"]).isEmpty

private def ok (i : Int) : Except Val Val := .ok (.int i)
private def yes (b : Bool) : Except Val Val := .ok (.bool b)
private def panics (m : String) : Except Val Val := .error (.str m)

private def at_ := "func F(s string, i int) int { return int(s[i]) }"

#guard check "func F(s string) int { return len(s) }" [.str "héllo"] (ok 6)
#guard check "func F(s string) int { return len(s) }" [.str ""] (ok 0)
#guard check at_ [.str "abc", .int 1] (ok 98)
#guard check at_ [.str "é", .int 1] (ok 169)
#guard check at_ [.str "abc", .int 3]
  (panics "runtime error: index out of range [3] with length 3")
#guard check at_ [.str "abc", .int (-1)] (panics "runtime error: index out of range [-1]")
#guard check at_ [.str "", .int 0] (panics "runtime error: index out of range [0] with length 0")
-- Go evaluates operands from left to right, so the first failing check panics.
#guard check "func F(s string, i int, j int) int { return int(s[i]) / int(s[j]) + j / i }"
  [.str "ab\x00", .int 0, .int 9] (panics "runtime error: index out of range [9] with length 3")
#guard check "func F(s string, i int, j int) int { return int(s[i]) / int(s[j]) + j / i }"
  [.str "ab\x00", .int 1, .int 2] (panics "runtime error: integer divide by zero")
#guard check "func F(s string, i int, j int) int { return int(s[i]) / int(s[j]) + j / i }"
  [.str "ab\x00", .int 7, .int 2] (panics "runtime error: index out of range [7] with length 3")
#guard check "func F(s string, i int) int { x := 0; if i < len(s) { x = int(s[i]) }; return x }"
  [.str "a", .int 4] (ok 0)
-- Strings compare bytewise: "é" is 0xC3 0xA9, above "z".
#guard check "func F(a string, b string) bool { return a < b }" [.str "z", .str "é"] (yes true)
#guard check "func F(a string, b string) bool { return a <= b }" [.str "ab", .str "ab"] (yes true)
#guard check "func F(a string, b string) bool { return a > b }" [.str "ab", .str "a"] (yes true)
#guard check "func F(a string, b string) bool { return a >= b }" [.str "a", .str "ab"] (yes false)
#guard check "func F(a string, b string) int { return len(a + b) }" [.str "ab", .str "é"] (ok 4)
-- The arguments of a call of a function that can panic are checked first,
-- and the callee's panic follows.
private def callG := "func G(a int) int { return 10 / a }\nfunc F(s string, i int) int { x := G(int(s[i])); return x }"
#guard checkCall callG [.str "ab", .int 1] (ok 0)
#guard checkCall callG [.str "ab", .int 2]
  (panics "runtime error: index out of range [2] with length 2")
#guard checkCall callG [.str "a\x00", .int 1] (panics "runtime error: integer divide by zero")
-- A failed check of an argument panics, even when the callee would panic on
-- the value that Lean computes for the argument.
#guard checkCall "func G(a int) int { return 10 / a }\nfunc F(a int, b int) int { x := G(a / b); return x }"
  [.int 3, .int 0] (panics "runtime error: integer divide by zero")
-- A slice can cut a UTF-8 sequence, which no Lean `String` holds.
#guard refused "func F(s string) string { return s[1:] }"
#guard refused "func F(s string, i int, j int) string { return s[i:j] }"
-- A byte is an 8-bit integer: its arithmetic wraps, which is not modeled.
#guard refused "func F(s string) int { return int(s[0] + s[1]) }"
#guard refused "func F(s string) bool { return s[0] == 'a' }"
#guard refused "func F(s string) int { n := 0; for range s { n++ }; return n }"
#guard refused "func F(s string) int { return len([]rune(s)) }"
#guard refused "func F(s string) int { return s[0] }"
#guard refused "func F(s string) int { return len(s[0]) }"

#print axioms Proof.translate_sound
