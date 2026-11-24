import tolean.Core.Loop
import tolean.Go.Proof.Expr

namespace tolean.Go.Proof.LoopScope

open tolean.Core.Loop

/-- This is the scope-exit formula in Go's existing block interpreter. -/
def sourceLeave (outer inner : Eval.Env) : Option Eval.Env :=
  some (inner.drop (inner.length - outer.length))

private def outer : Eval.Env := [("x", .int 0)]
private def shadowed : Eval.Env := [("x", .int 1), ("x", .int 0)]
private def updated : Eval.Env := [("x", .int 1)]

/-- Updating a binding and shadowing it agree on every current lookup. -/
theorem update_shadow_agree :
    Agree (Eval.Env.set outer "x" (.int 1)) (("x", .int 1) :: outer) := by
  intro n
  cases h : n == "x" <;> simp [outer, Eval.Env.set, List.lookup, h]

private theorem inner_agree : Agree shadowed updated := by
  intro n
  cases h : n == "x" <;> simp [shadowed, updated, List.lookup, h]

/-- Lookup agreement alone cannot discharge the shared loop's scope law.
Dropping a source declaration exposes the old x. Copying the target's changed
x reads the new x. This is a counterexample to a universal environment law,
not an accepted Go translation: a declaration of x must not count as a write
to the outer x. The body proof must carry that scope fact as well as Agree. -/
theorem lookup_scope_law_false :
    ¬ (∀ (s t si ti : Eval.Env), Agree s t → Agree si ti →
      Related Agree (sourceLeave s si) (IR.bindState ["x"] ti t)) := by
  intro law
  have h := law outer outer shadowed updated (Agree.refl outer) inner_agree
  change Agree [("x", .int 0)] [("x", .int 1)] at h
  have hx := h "x"
  simp [List.lookup] at hx

/-- The failed law has an observable witness, not merely unequal lists. -/
theorem scope_lookup_diff :
    (sourceLeave outer shadowed >>= fun env => env.lookup "x") = some (.int 0) ∧
    (IR.bindState ["x"] updated outer >>= fun env => env.lookup "x") = some (.int 1) := by
  decide

end tolean.Go.Proof.LoopScope
