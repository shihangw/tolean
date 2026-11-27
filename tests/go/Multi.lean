import tolean.Go.Syntax.Parser
import tolean.Go.Proof.Package

/-!
Functions with several results, `return a, b`, and assignments of several
values on the proved path. The IR's evaluator and the interpreter must give
the same value, or the same panic, for each input.
-/

open tolean.Go
open tolean.Go.Eval (Val)

private def parseDecls (src : String) : Except String (List Syntax.Decl) := do
  match Syntax.parse ("package multi\n" ++ src) with
  | .ok file => return file.decls
  | .error _ => throw "the multi test did not parse"

/-- Equal results of a call. `Except` has no `BEq` instance. -/
private def same : Option (Except Val Val) → Option (Except Val Val) → Bool
  | some (.ok a), some (.ok b) | some (.error a), some (.error b) => a == b
  | none, none => true
  | _, _ => false

/-- The functions `names` are translated, and both sides give `expected` for a
call of the last one. -/
private def checkIn (names : List String) (src : String) (args : List Val)
    (expected : Except Val Val) : Bool :=
  match parseDecls src with
  | .error _ => false
  | .ok decls =>
    let translated := Pure.translateFuncs decls names
    let f := names.getLast?.getD "F"
    translated.length == names.length &&
      same (IR.runIn (IR.functions (translated.map (·.1))) ⟨"", f⟩ args) (some expected) &&
      same (Eval.runIn (Eval.program decls) f args) (some expected)

private def check := checkIn ["F"]
private def checkCall := checkIn ["G", "F"]

private def refusedIn (names : List String) (src : String) : Bool :=
  match parseDecls src with
  | .error _ => false
  | .ok decls => (Pure.translateFuncs decls names).length < names.length

private def refused := refusedIn ["F"]

private def ok (i : Int) : Except Val Val := .ok (.int i)
private def panics (m : String) : Except Val Val := .error (.str m)

-- `return a, b` returns a pair, nested to the right as Lean's tuples are.
#guard check "func F(a int, b int) (int, int) { return b, a }" [.int 1, .int 2]
  (.ok (.pair (.int 2) (.int 1)))
#guard check "func F(a int, s string) (int, bool, string) { return a + 1, a > 0, s + s }"
  [.int 3, .str "x"] (.ok (.pair (.int 4) (.pair (.bool true) (.str "xx"))))
#guard check "func F(a int, b int) (int, int) { return a, b / a }" [.int 0, .int 3]
  (panics "runtime error: integer divide by zero")
-- Go fixes the order of calls only, and gc may test a later value's divisor
-- before an earlier value's index, so at most one value may panic.
#guard refused "func F(a int, b int) (int, int) { return a / b, b / a }"
#guard refused "func F(s string, i int, b int) (int, int) { return int(s[i]), i / b }"
#guard refused "func F(s string, i int, b int) int { x, y := int(s[i]), i / b; return x + y }"
-- `a, b = b, a` swaps: every value is evaluated before any is assigned.
#guard check "func F(a int, b int) int { a, b = b, a; return a * 10 + b }" [.int 1, .int 2] (ok 21)
#guard check "func F(a int) int { x, y := a, a + 1; return x * y }" [.int 4] (ok 20)
#guard check "func F(a int, b int) int { x, _ := a, a / b; return x }" [.int 4, .int 0]
  (panics "runtime error: integer divide by zero")
#guard check "func F(a int) int { _, y := a, 7; return y }" [.int 4] (ok 7)
-- A call with several results gives the variables their values.
private def divmod := "func G(a int, b int) (int, int) { return a + b, a - b }\n"
#guard checkCall (divmod ++ "func F(a int, b int) int { q, r := G(a, b); return q * 100 + r }")
  [.int 17, .int 5] (ok 2212)
#guard checkCall (divmod ++ "func F(a int, b int) int { q, r := G(a, b); return q * 100 + r }")
  [.int (-17), .int 5] (ok (-1222))
#guard checkCall (divmod ++ "func F(a int, b int) int { q := 0; r := 0; q, r = G(a, b); return q + r }")
  [.int 17, .int 5] (ok 34)
#guard checkCall (divmod ++ "func F(a int, b int) int { _, r := G(a, b); return r }")
  [.int 17, .int 5] (ok 12)
#guard checkCall (divmod ++ "func F(a int, b int) (int, int) { return G(b, a) }")
  [.int 5, .int 17] (.ok (.pair (.int 22) (.int 12)))
-- The callee's argument divisors are checked before the call.
#guard checkCall (divmod ++ "func F(a int, b int) int { q, r := G(a / b, 1); return q + r }")
  [.int 17, .int 0] (panics "runtime error: integer divide by zero")
-- The body of a counted loop does not take several values yet: its proof of
-- the counter's frame covers one name at a time.
#guard refused "func F(a int, b int) int { for i := 0; i < 10; i++ { a, b = b, a + b }; return a }"

-- A callee with several results that can panic is outside the subset.
#guard refusedIn ["G", "F"]
  "func G(a int, b int) (int, int) { return a / b, a % b }\nfunc F(a int, b int) int { q, r := G(a, b); return q + r }"
#guard refusedIn ["G", "F"]
  "func G(a int) (int, int) { if a == 0 { panic(\"zero\") }; return a, a }\nfunc F(a int) int { x, y := G(a); return x + y }"
-- Named results, a `:=` that redeclares, and mismatched counts are refused.
#guard refused "func F(a int) (x int, y int) { return a, a }"
#guard refused "func F(a int) int { x := 1; x, y := a, a; return x + y }"
#guard refused "func F(a int) int { x, y := a, a, a; return x + y }"
#guard refused "func F(a int) int { x, y := a; return x + y }"
#guard refused "func F(a int) int { x, x := a, a; return x }"
#guard refused "func F(a int) int { _, _ := a, a; return a }"
#guard refused "func F(a int) int { x := 0; x, x = a, a; return x }"
#guard refused "func F(a int) int { x := 0; y := false; x, y = a, a; return x }"
#guard refused "func F(a int) (int, int) { return a }"
#guard refused "func F(a int) int { return a, a }"
#guard refusedIn ["G", "F"] (divmod ++ "func F(a int, b int) int { return G(a, b) + 1 }")
#guard refusedIn ["G", "F"] (divmod ++ "func F(a int, b int) int { x := G(a, b); return x }")

#print axioms Proof.translate_sound
