import tolean.Go.Syntax.Parser
import tolean.Go.Proof.Package

open tolean.Go

private def parseDecls (body : String) : Except String (List Syntax.Decl) := do
  match Syntax.parse ("package counted\nfunc Sum(total int) int {\n" ++ body ++ "\n}\n") with
  | .ok file => return file.decls
  | .error _ => throw "the counted-loop test did not parse"

/-- Equal results of a call. `Except` has no `BEq` instance. -/
private def same : Option (Except Eval.Val Eval.Val) → Option (Except Eval.Val Eval.Val) → Bool
  | some (.ok a), some (.ok b) | some (.error a), some (.error b) => a == b
  | none, none => true
  | _, _ => false

private def check (body : String) (input expected : Int) : Bool :=
  match parseDecls body with
  | .error _ => false
  | .ok decls =>
    let translated := Pure.translateFuncs decls ["Sum"]
    translated.length == 1 &&
      same (IR.runIn (IR.functions (translated.map (·.1))) ⟨"", "Sum"⟩ [.int input])
        (some (.ok (.int expected))) &&
      same (Eval.runIn (Eval.program decls) "Sum" [.int input]) (some (.ok (.int expected)))

private def refused (body : String) : Bool :=
  match parseDecls body with
  | .error _ => false
  | .ok decls => (Pure.translateFuncs decls ["Sum"]).isEmpty

#guard check "for i := 0; i < 10; i++ { total += i }; return total" 7 52
#guard check "for i := 0; i < 256; i++ { total += i }; return total" 0 32640
#guard check "for i := 3; i < 6; i++ { total += i }; return total" 0 12
#guard check "for i := 4; i < 2; i++ { total += i }; return total" 19 19
#guard check "for i := 0; i < 2; i++ { total++ }; return total"
  9223372036854775807 (-9223372036854775807)
#guard check "for i := 0; i < 4; i++ { x := i * 2; if i < 2 { total += x } }; return total" 5 7
#guard refused "for i := 0; i < total; i++ { total += i }; return total"
#guard check "for i := 0; i < 257; i++ { total += i }; return total" 0 32896
#guard check "n := total; total = 0; for i := 0; i < n; i++ { total += i }; return total" 5 10
#guard check "n := total; for i := n - 2; i < n * 2; i++ { total += 1 }; return total" 3 8
#guard check "n := total; for i := 0; i < n; i++ { total += 1 }; return total" (-4) (-4)
#guard check "s := \"abc\"; for i := 0; i < len(s); i++ { total += int(s[i]) }; return total" 0 294
#guard check "if total > 0 { for i := 0; i < 3; i++ { total += i } }; return total" 3 6
#guard check "for i := 0; i < 2; i++ { total += 1 }; for j := 0; j < 3; j++ { total += 10 }; return total" 0 32
-- The bound may not read the counter, and the body may not change what the
-- bound reads.
#guard refused "for i := 0; i < i + 3; i++ { total += 1 }; return total"
#guard refused "n := 3; for i := 0; i < n; i++ { n++ }; return total"
-- A bound that could panic, a bound of another type and other tests stay
-- refused.
#guard refused "for i := 0; i < 10 / total; i++ { total += 1 }; return total"
#guard refused "var n int64 = 3; for i := 0; i < n; i++ { total += 1 }; return total"
#guard refused "for i := 0; i <= 3; i++ { total += i }; return total"
#guard refused "for i := 0; i < 3; i++ { i++; total += i }; return total"
#guard refused "for i := 0; i < 3; i++ { return total }; return total"
#guard refused "for i := 0; i < 3; i++ { break }; return total"
#guard refused "for i := 0; i < 3; i++ { continue }; return total"
#guard check "total++; for i := 0; i < 3; i++ { total += i }; return total" 1 5
#guard refused "for i := 0; i < 3; i++ { for j := 0; j < 3; j++ { total += j } }; return total"

#print axioms Proof.LoopFrame.loop_refines
#print axioms Proof.top_sound
#print axioms Proof.translate_sound
