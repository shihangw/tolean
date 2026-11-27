import tolean.Go.Proof.LoopFrame

namespace tolean.Go.Proof.LoopDefinedness

/-- Existing call soundness permits an undefined target call. It only promises
that a successful target call has the same source result. -/
theorem empty_target_calls (p : Eval.Program) (fuel : Nat) : CallsAgree p [] fuel := by
  intro f vs v h
  cases fuel <;> simp [callO, List.lookup] at h

private def identityProgram : Eval.Program :=
  ⟨[("identity", ["x"], .ret default [.ident default "x"])], ["identity"]⟩

theorem source_identity :
    callS identityProgram 1 "identity" [.int 7] = some (.ok (.int 7)) := by
  simp [callS, identityProgram, Eval.execStmt, Eval.eval, List.lookup]

theorem target_identity :
    callO [] 1 ⟨"", "identity"⟩ [.int 7] = none := by
  simp [callO, List.lookup]

/-- The existing CallsAgree premise cannot establish the exact failure
equivalence required by Related. This is not a counterexample to program_sound:
an empty target function table is not a translation of identityProgram. -/
theorem exact_calls_do_not_follow :
    ¬ (∀ p fs fuel, CallsAgree p fs fuel →
      ∀ f vs, tolean.Core.Loop.Related Eq (callS p fuel f vs)
        ((callO fs fuel ⟨"", f⟩ vs).map Except.ok)) := by
  intro law
  have h := law identityProgram [] 1 (empty_target_calls _ _) "identity" [.int 7]
  rw [source_identity, target_identity] at h
  exact h

end tolean.Go.Proof.LoopDefinedness
