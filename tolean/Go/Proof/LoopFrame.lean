import tolean.Go.Proof.LoopScope
import tolean.Go.Proof.Stmt

namespace tolean.Go.Proof.LoopFrame

open tolean.Go.Syntax tolean.Go.Pure tolean.Core.Loop

/-- The source keeps new locals before an updated outer frame. The target may
shadow old bindings, but agrees on the inner store's current lookups. Fresh
locals are not outer variables, so changedNames never copies them out. -/
def Inner (env : Pure.Env) (ss : List Stmt) (outerS _outerT innerS innerT : Eval.Env) : Prop :=
  ∃ fresh modified, innerS = fresh ++ modified ∧
    Agree innerS innerT ∧ (∀ p ∈ fresh, env.has p.1 = false) ∧
    Frame (changesList ss) modified outerS

theorem bind_frame (env : Pure.Env) (ss : List Stmt) (s t : Eval.Env)
    (agree : Agree s t) (x : String) (v : Eval.Val) (fresh : env.has x = false) :
    Inner env ss s t ((x, v) :: s) ((x, v) :: t) := by
  refine ⟨[(x, v)], s, rfl, agree_cons agree x v, ?_, Frame.refl _ _⟩
  intro p hp
  have : p = (x, v) := by simpa using hp
  subst p
  exact fresh

theorem body_frame (p : Eval.Program) (fs : Funcs) (fuel : Nat)
    (env : Pure.Env) (ss : List Stmt) (tail : Tail) (body : IR.Body)
    (sim : StmtSim p fs fuel env tail ss body)
    (s t innerT : Eval.Env) (agree : Agree s t) (scope : Scoped env s)
    (done : IR.Body.exec fs fuel t body = some (.normal innerT)) :
    ∃ innerS, Eval.exec p fuel s ss = some (.normal innerS) ∧
      Inner env ss s t innerS innerT := by
  obtain ⟨_, fresh, modified, hs, ha, hn, hf⟩ := (sim s t agree scope).2 innerT done
  exact ⟨fresh ++ modified, hs, fresh, modified, rfl, ha, hn, hf⟩

/-- This uses the real translator's no-shadowing check and its statement proof.
The premise is successful translation, not an assumed body simulation. -/
theorem accepted_body_frame (p : Eval.Program) (fs : Funcs) (fuel : Nat)
    (ctx : Ctx) (program : ctx.program = p) (calls : CallsAgree p fs fuel)
    (env : Pure.Env) (ss : List Stmt) (tail : Tail) (body : IR.Body) (budget : Nat)
    (translated : translateStmts ctx env tail budget ss = .ok body)
    (s t innerT : Eval.Env) (agree : Agree s t) (scope : Scoped env s)
    (done : IR.Body.exec fs fuel t body = some (.normal innerT)) :
    ∃ innerS, Eval.exec p fuel s ss = some (.normal innerS) ∧
      Inner env ss s t innerS innerT :=
  body_frame p fs fuel env ss tail body (stmts_sound p fs fuel program calls translated)
    s t innerT agree scope done

theorem leave_frame (env : Pure.Env) (ss : List Stmt)
    (s t si ti out : Eval.Env) (agree : Agree s t) (scope : Scoped env s)
    (frame : Inner env ss s t si ti)
    (bound : IR.bindState (changedNames ss env) ti t = some out) :
    ∃ result, LoopScope.sourceLeave s si = some result ∧ Agree result out ∧
      Scoped env result := by
  obtain ⟨fresh, modified, rfl, ha, hn, hf⟩ := frame
  refine ⟨modified, ?_, ?_, ?_⟩
  · simp [LoopScope.sourceLeave, List.length_append, hf.length]
  · intro k
    rw [bindState_lookup bound k]
    split
    · next hk =>
      have hkenv := (mem_changedNames.mp hk).1
      rw [← ha k, lookup_append_fresh modified (fun p hp heq => by
        have h := hn p hp
        rw [heq, hkenv] at h
        exact Bool.noConfusion h)]
    · next hk =>
      rw [← agree k]
      by_cases hkc : k ∈ changesList ss
      · have hkenv : env.has k = false := by
          cases he : env.has k
          · rfl
          · exact False.elim (hk (mem_changedNames.mpr ⟨he, hkc⟩))
        have hs : (s.lookup k).isSome = false := (scope k).trans hkenv
        have hm : (modified.lookup k).isSome = false := (hf.isSome k).trans hs
        cases hsl : s.lookup k <;> cases hml : modified.lookup k <;> simp_all
      · exact hf.lookup hkc
  · intro k
    exact (hf.isSome k).trans (scope k)

private theorem bindState_defined (inner : Eval.Env) :
    ∀ (names : List String) (outer : Eval.Env),
      (∀ n ∈ names, (inner.lookup n).isSome = true) →
      ∃ out, IR.bindState names inner outer = some out
  | [], outer, _ => ⟨outer, rfl⟩
  | n :: names, outer, found => by
    cases hv : inner.lookup n with
    | none =>
      have h := found n (List.mem_cons_self ..)
      simp [hv] at h
    | some v =>
      let mid := if (outer.lookup n).isSome then outer.set n v else (n, v) :: outer
      obtain ⟨out, ho⟩ := bindState_defined inner names mid
        (fun k hk => found k (List.mem_cons_of_mem n hk))
      refine ⟨out, ?_⟩
      simpa [IR.bindState, List.foldlM_cons, hv, mid] using ho

/-- The anchored frame proves the full scope law, including definedness of
target state projection. Scope is preserved for the next iteration. -/
theorem leave_related (env : Pure.Env) (ss : List Stmt)
    (s t si ti : Eval.Env) (agree : Agree s t) (scope : Scoped env s)
    (frame : Inner env ss s t si ti) :
    Related (fun a b => Agree a b ∧ Scoped env a)
      (LoopScope.sourceLeave s si) (IR.bindState (changedNames ss env) ti t) := by
  have found : ∀ n ∈ changedNames ss env, (ti.lookup n).isSome = true := by
    intro n hn
    have hen := (mem_changedNames.mp hn).1
    obtain ⟨fresh, modified, rfl, ha, hfresh, hframe⟩ := frame
    rw [← ha n, lookup_append_fresh modified (fun p hp heq => by
      have h := hfresh p hp
      rw [heq, hen] at h
      exact Bool.noConfusion h)]
    exact (hframe.isSome n).trans ((scope n).trans hen)
  obtain ⟨out, hb⟩ := bindState_defined ti (changedNames ss env) t found
  obtain ⟨result, hs, ha, hscope⟩ := leave_frame env ss s t si ti out agree scope frame hb
  rw [hs, hb]
  exact ⟨ha, hscope⟩

end tolean.Go.Proof.LoopFrame
