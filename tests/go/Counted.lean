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
#guard check "for i := 0; i < 3; i++ { break }; return total" 4 4
#guard check "for i := 0; i < 3; i++ { continue }; return total" 4 4
#guard check "for i := 0; i < 10; i++ { if i == 4 { break }; total += i }; return total" 1 7
#guard check "for i := 0; i < 10; i++ { if i % 2 == 0 { continue }; total += i }; return total" 0 25
#guard check "for i := 0; i < 6; i++ { switch i { case 2: break; default: total += i } }; return total" 0 13
#guard check "for i := 0; i < 6; i++ { switch i { case 3: continue; default: total += i } }; return total" 0 12
-- A switch that both breaks and continues stays refused.
#guard refused "for i := 0; i < 6; i++ { switch i { case 2: break; case 3: continue; default: total += i } }; return total"
#guard check "for i := 0; i < 6; i++ { switch i { case 4: total += 100 }; if i == 4 { break }; total += 1 }; return total" 0 104
-- A block that breaks must end the statements of the loop's body.
#guard refused "for i := 0; i < 5; i++ { { if i == 3 { break } }; total += i }; return total"
#guard check "for i := 0; i < 5; i++ { total += i; { if i == 3 { break } } }; return total" 0 6
#guard refused "for i := 0; i < total; i++ { total += i }; return total"
#guard refused "for i := 0; i < 257; i++ { total += i }; return total"
#guard refused "for i := 0; i < 3; i++ { i++; total += i }; return total"
#guard refused "for i := 0; i < 3; i++ { return total }; return total"
#guard refused "total++; for i := 0; i < 3; i++ { total += i }; return total"
#guard refused "for i := 0; i < 3; i++ { for j := 0; j < 3; j++ { total += j } }; return total"

#print axioms Proof.LoopFrame.loop_refines
#print axioms Proof.top_sound
#print axioms Proof.translate_sound
