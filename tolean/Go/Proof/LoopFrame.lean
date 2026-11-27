import tolean.Go.Proof.LoopScope
import tolean.Go.Proof.Stmt

namespace tolean.Go.Proof.LoopFrame

open tolean.Go.Syntax tolean.Go.Pure tolean.Core.Loop

/-- The source keeps new locals before an updated outer frame. The target may
shadow old bindings, but agrees with the outer frame on the names in scope.
Fresh locals are not outer variables, so changedNames never copies them out. -/
def Inner (env : Pure.Env) (ss : List Stmt) (outerS _outerT innerS innerT : Eval.Env) : Prop :=
  ∃ fresh modified, innerS = fresh ++ modified ∧
    AgreeOn env modified innerT ∧ (∀ p ∈ fresh, env.has p.1 = false) ∧
    Frame (changesList ss) modified outerS

theorem bind_frame (env : Pure.Env) (ss : List Stmt) (s t : Eval.Env)
    (agree : Agree s t) (x : String) (v : Eval.Val) (fresh : env.has x = false) :
    Inner env ss s t ((x, v) :: s) ((x, v) :: t) := by
  refine ⟨[(x, v)], s, rfl, fun n hn => ?_, ?_, Frame.refl _ _⟩
  · have hnx : n ≠ x := fun h => by rw [h, fresh] at hn; exact Bool.noConfusion hn
    rw [lookup_cons_ne _ _ hnx]
    exact agree n
  · intro p hp
    have : p = (x, v) := by simpa using hp
    subst p
    exact fresh

/-- The way the body of a loop ended, as the statements say: `yield` is their
end or a `continue`, and `done` is a `break`. -/
theorem body_frame (p : Eval.Program) (fs : Funcs) (fuel : Nat)
    (env : Pure.Env) (ss : List Stmt) (tail : Tail) (body : IR.Body)
    (sim : StmtSim p fs fuel env tail ss body)
    (s t innerT : Eval.Env) (agree : Agree s t) (scope : Scoped env s) (b : Bool)
    (done : IR.Body.exec fs fuel t body = some (irEnd b innerT)) :
    ∃ k innerS, tail.Allows b k ∧ Eval.exec p fuel s ss = some (k.out innerS) ∧
      Inner env ss s t innerS innerT := by
  obtain ⟨k, fresh, modified, hk, hs, ha, hn, hf⟩ := (sim s t agree scope).2.1 b innerT done
  exact ⟨k, fresh ++ modified, hk, hs, fresh, modified, rfl, ha, hn, hf⟩

/-- This uses the real translator's no-shadowing check and its statement proof.
The premise is successful translation, not an assumed body simulation. -/
theorem accepted_body_frame (p : Eval.Program) (fs : Funcs) (fuel : Nat)
    (ctx : Ctx) (program : ctx.program = p) (calls : CallsAgree p fs fuel)
    (env : Pure.Env) (ss : List Stmt) (tail : Tail) (body : IR.Body) (budget : Nat)
    (translated : translateStmts ctx env tail budget ss = .ok body)
    (s t innerT : Eval.Env) (agree : Agree s t) (scope : Scoped env s) (b : Bool)
    (done : IR.Body.exec fs fuel t body = some (irEnd b innerT)) :
    ∃ k innerS, tail.Allows b k ∧ Eval.exec p fuel s ss = some (k.out innerS) ∧
      Inner env ss s t innerS innerT :=
  body_frame p fs fuel env ss tail body (stmts_sound p fs fuel program calls translated)
    s t innerT agree scope b done

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
      exact ha k (mem_changedNames.mp hk).1
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
    rw [← ha n hen]
    exact (hframe.isSome n).trans ((scope n).trans hen)
  obtain ⟨out, hb⟩ := bindState_defined ti (changedNames ss env) t found
  obtain ⟨result, hs, ha, hscope⟩ := leave_frame env ss s t si ti out agree scope frame hb
  rw [hs, hb]
  exact ⟨ha, hscope⟩

/-- Binding the counter adds one fresh local to the body's frame. Scope exit
must discard that binding as well as declarations made by the body. -/
theorem bound_body_frame (p : Eval.Program) (fs : Funcs) (fuel : Nat)
    (env : Pure.Env) (ss : List Stmt) (tail : Tail) (body : IR.Body)
    (index : String) (value : Eval.Val) (freshIndex : env.has index = false)
    (sim : StmtSim p fs fuel (env ++ [⟨index, .int⟩]) tail ss body)
    (s t innerT : Eval.Env) (agree : Agree s t) (scope : Scoped env s) (b : Bool)
    (done : IR.Body.exec fs fuel ((index, value) :: t) body = some (irEnd b innerT)) :
    ∃ k innerS, tail.Allows b k ∧ Eval.exec p fuel ((index, value) :: s) ss = some (k.out innerS) ∧
      Inner env ss s t innerS innerT := by
  obtain ⟨k, innerS, allows, executed, fresh, modified, shape, agreement, freshNames, frame⟩ :=
    body_frame p fs fuel _ ss tail body sim _ _ innerT
      (agree_cons agree index value) (scoped_cons scope index .int value) b done
  cases modified with
  | nil => simp [Frame] at frame
  | cons entry modified =>
    obtain ⟨entryName, _, frame⟩ := frame
    refine ⟨k, innerS, allows, executed, fresh ++ [entry], modified, ?_, fun n hn => ?_, ?_, frame⟩
    · simpa [List.append_assoc] using shape
    · have hni : n ≠ index := fun h => by rw [h, freshIndex] at hn; exact Bool.noConfusion hn
      have := agreement n (by rw [has_append, hn]; rfl)
      rw [← this]
      obtain ⟨name, w⟩ := entry
      simp only at entryName
      subst entryName
      exact (lookup_cons_ne _ _ hni).symm
    · intro q hq
      rcases List.mem_append.mp hq with hq | hq
      · have h := freshNames q hq
        rw [has_append] at h
        exact (Bool.or_eq_false_iff.mp h).1
      · have : q = entry := by simpa using hq
        subst q
        simpa only [entryName] using freshIndex

/-- The output has no `continue`: a loop's body that goes on gives
`ForInStep.yield`, which is an end. -/
theorem exec_ne_cont (fs : Funcs) : ∀ (fuel : Nat) (ρ : Eval.Env) (b : IR.Body) (e : Eval.Env),
    IR.Body.exec fs fuel ρ b ≠ some (.cont e)
  | fuel, ρ, .let name x rest, e, h => by
    rw [IR.Body.exec.eq_def] at h
    simp only [bind, Option.bind_eq_some_iff] at h
    obtain ⟨_, _, h⟩ := h
    exact exec_ne_cont fs fuel _ rest e h
  | fuel, ρ, .ite c t f, e, h => by
    rw [IR.Body.exec.eq_def] at h
    simp only [bind, Option.bind_eq_some_iff] at h
    obtain ⟨a, _, h⟩ := h
    split at h
    · split at h
      · exact exec_ne_cont fs fuel _ t e h
      · exact exec_ne_cont fs fuel _ f e h
    · simp at h
  | fuel, ρ, .letState names br rest, e, h => by
    rw [IR.Body.exec.eq_def] at h
    simp only [bind, Option.bind_eq_some_iff] at h
    obtain ⟨a, _, h⟩ := h
    split at h
    · simp only [Option.bind_eq_some_iff] at h
      obtain ⟨_, _, h⟩ := h
      exact exec_ne_cont fs fuel _ rest e h
    · simp at h
    · simp at h
  | 0, ρ, .bind name ref args rest, e, h => by
    rw [IR.Body.exec.eq_def] at h
    simp [bind] at h
  | fuel + 1, ρ, .bind name ref args rest, e, h => by
    rw [IR.Body.exec.eq_def] at h
    simp only [bind, Option.bind_eq_some_iff] at h
    obtain ⟨a, _, _, _, h⟩ := h
    split at h
    · simp at h
    · simp only [pure, Option.bind_some, Option.bind_eq_some_iff] at h
      obtain ⟨o, _, h⟩ := h
      split at h
      · exact exec_ne_cont fs (fuel + 1) _ rest e h
      · simp at h
      · simp at h
  | fuel, ρ, .fold names el body items rest m, e, h => by
    rw [IR.Body.exec.eq_def] at h
    cases items
    all_goals try (split at h <;> simp_all; done)
    simp only [bind, Option.bind_eq_some_iff] at h
    obtain ⟨_, _, o, _, h⟩ := h
    split at h
    · exact exec_ne_cont fs fuel _ rest e h
    all_goals simp at h
  | fuel, ρ, .handle .., e, h => by rw [IR.Body.exec.eq_def] at h; split at h <;> simp_all
  | fuel, ρ, .value .., e, h => by rw [IR.Body.exec.eq_def] at h; split at h <;> simp_all [bind, Option.bind_eq_some_iff]
  | fuel, ρ, .state .., e, h => by rw [IR.Body.exec.eq_def] at h; split at h <;> simp_all
  | fuel, ρ, .yield .., e, h => by rw [IR.Body.exec.eq_def] at h; split at h <;> simp_all
  | fuel, ρ, .done .., e, h => by rw [IR.Body.exec.eq_def] at h; split at h <;> simp_all
  | fuel, ρ, .exit .., e, h => by rw [IR.Body.exec.eq_def] at h; split at h <;> simp_all
  | fuel, ρ, .letArray .., e, h => by rw [IR.Body.exec.eq_def] at h; split at h <;> simp_all
  | fuel, ρ, .matchNull .., e, h => by rw [IR.Body.exec.eq_def] at h; split at h <;> simp_all
  | fuel, ρ, .matchTag .., e, h => by rw [IR.Body.exec.eq_def] at h; split at h <;> simp_all
  | fuel, ρ, .letTuple .., e, h => by rw [IR.Body.exec.eq_def] at h; split at h <;> simp_all
  | fuel, ρ, .throw .., e, h => by rw [IR.Body.exec.eq_def] at h; split at h <;> simp_all [bind, Option.bind_eq_some_iff]
  | fuel, ρ, .letBorrow .., e, h => by rw [IR.Body.exec.eq_def] at h; split at h <;> simp_all
  | fuel, ρ, .letCall .., e, h => by rw [IR.Body.exec.eq_def] at h; split at h <;> simp_all
  | fuel, ρ, .letLifted .., e, h => by rw [IR.Body.exec.eq_def] at h; split at h <;> simp_all
termination_by fuel _ b => (fuel, sizeOf b)

/-- The shared loop theorem lifts Go's success-only statement simulation.
Unlike exact simulation, this does not require failed target calls to fail in
the source. -/
theorem loop_refines (p : Eval.Program) (fs : Funcs) (fuel : Nat)
    (env : Pure.Env) (ss : List Stmt) (tail : Tail) (body : IR.Body)
    (index : String) (freshIndex : env.has index = false)
    (sim : StmtSim p fs fuel (env ++ [⟨index, .int⟩]) tail ss body)
    (loopTail : ∀ b k, tail.Allows b k →
      (b = false ∧ (k = .next ∨ k = .cont)) ∨ (b = true ∧ k = .brk))
    (s t : Eval.Env) (agree : Agree s t) (scope : Scoped env s)
    (items : List Eval.Val) :
    ∀ {out}, runFold
        (fun inner => (IR.Body.exec fs fuel inner body).map IR.loopOutcome)
        (fun value outer => some ((index, value) :: outer))
        (fun outer inner => IR.bindState (changedNames ss env) inner outer) t items = some out →
      ∃ source, execLoop
        (fun inner => (Eval.exec p fuel inner ss).map Eval.Outcome.toLoop)
        (fun value outer => some ((index, value) :: outer))
        LoopScope.sourceLeave s items = some source ∧
        Outcome.Rel (fun a b => Agree a b ∧ Scoped env a ∧ Frame (changesList ss) a s)
          Eq source out := by
  apply execLoop_refines
    (fun a b => Agree a b ∧ Scoped env a ∧ Frame (changesList ss) a s) Eq (Inner env ss)
  · intro current target si ti h frame
    have related := leave_related env ss current target si ti h.1 h.2.1 frame
    obtain ⟨fresh, modified, rfl, _, _, modifiedFrame⟩ := frame
    have left : LoopScope.sourceLeave current (fresh ++ modified) = some modified := by
      simp [LoopScope.sourceLeave, modifiedFrame.length]
    rw [left] at related ⊢
    cases right : IR.bindState (changedNames ss env) ti target with
    | none => simp [right, Related] at related
    | some next =>
      rw [right] at related
      refine ⟨related.1, related.2, ?_⟩
      exact (modifiedFrame.trans h.2.2).mono (by simp)
  · intro value s t h out executed
    simp only [loopStep, Option.bind_some] at executed ⊢
    cases ht : IR.Body.exec fs fuel ((index, value) :: t) body with
    | none => simp [ht] at executed
    | some result =>
      cases result with
      | ret result =>
        simp only [ht, Option.map_some, IR.loopOutcome, Option.some.injEq] at executed
        subst out
        have hs := (sim _ _ (agree_cons h.1 index value)
          (scoped_cons h.2.1 index .int value)).1 result ht
        exact ⟨.ret (.ok result), by simp [hs, Eval.Outcome.toLoop], rfl⟩
      | panic x =>
        simp only [ht, Option.map_some, IR.loopOutcome, Option.some.injEq] at executed
        subst out
        have hs := (sim _ _ (agree_cons h.1 index value)
          (scoped_cons h.2.1 index .int value)).2.2 x ht
        exact ⟨.ret (.error x), by simp [hs, Eval.Outcome.toLoop], rfl⟩
      | normal innerT =>
        simp only [ht, Option.map_some, IR.loopOutcome, Option.some.injEq] at executed
        subst out
        obtain ⟨k, innerS, allows, hs, frame⟩ :=
          bound_body_frame p fs fuel env ss tail body index value freshIndex sim
            s t innerT h.1 h.2.1 false ht
        rcases loopTail false k allows with ⟨-, rfl | rfl⟩ | ⟨h', -⟩
        · exact ⟨.normal innerS, by simp [hs, Jump.out, Eval.Outcome.toLoop], frame⟩
        · exact ⟨.cont innerS, by simp [hs, Jump.out, Eval.Outcome.toLoop], frame⟩
        · cases h'
      | brk innerT =>
        simp only [ht, Option.map_some, IR.loopOutcome, Option.some.injEq] at executed
        subst out
        obtain ⟨k, innerS, allows, hs, frame⟩ :=
          bound_body_frame p fs fuel env ss tail body index value freshIndex sim
            s t innerT h.1 h.2.1 true ht
        rcases loopTail true k allows with ⟨h', -⟩ | ⟨-, rfl⟩
        · cases h'
        · exact ⟨.brk innerS, by simp [hs, Jump.out, Eval.Outcome.toLoop], frame⟩
      | cont innerT =>
        simp only [ht, Option.map_some, IR.loopOutcome, Option.some.injEq] at executed
        exact absurd ht (exec_ne_cont fs fuel _ body innerT)
  · exact ⟨agree, scope, Frame.refl _ _⟩

end tolean.Go.Proof.LoopFrame

namespace tolean.Go.Proof

open tolean.Go.Syntax tolean.Go.Pure

theorem eval_valueCodes (fs : Funcs) (fuel : Nat) (env : Eval.Env) (values : List Eval.Val) :
    IR.Expr.evalList fs fuel env (values.map valueCode) = some values := by
  induction values with
  | nil => simp [IR.Expr.evalList]
  | cons value values ih =>
    cases value <;> simp [valueCode, IR.Expr.evalList, IR.Expr.eval, ih]

/-- The leading counted loop and the statements after it obey the same
success-only contract as the existing statement translator. -/
theorem top_sound (p : Eval.Program) (fs : Funcs) (fuel : Nat)
    {ctx : Ctx} (hp : ctx.program = p) (hc : CallsAgree p fs fuel)
    {env : Pure.Env} {result : Ty} {monadic : Bool} {ss : List Stmt} {body : IR.Body}
    (translated : translateTop ctx env result monadic ss = .ok body) :
    StmtSim p fs fuel env (.ret result monadic) ss body := by
  unfold translateTop at translated
  split at translated
  · next sp init cond post bsp loopSS rest =>
    cases head : Eval.countedHead init cond post with
    | none => simp [head, reject, throw, throwThe, MonadExceptOf.throw] at translated
    | some pair =>
      obtain ⟨index, items⟩ := pair
      simp only [head] at translated
      tm_simp at translated
      obtain ⟨safe, inner, declared, loopBody, loopTranslated, next, nextTranslated, rfl⟩ := translated
      obtain ⟨freshIndex, rfl⟩ := declare_ok declared
      have simBody := stmts_sound p fs fuel hp hc loopTranslated
      have simRest := stmts_sound p fs fuel hp hc nextTranslated
      intro s t agree scope
      have key : ∀ out, IR.Body.exec fs fuel t
          (tolean.Core.Loop.lowerLoop sp
            ((env.filter fun l => (changesList loopSS).contains l.name).map
              fun l => (l.name, l.type.lean))
            index .int loopBody (.list (items.map valueCode) .int) next (exitsList true loopSS) none) = some out →
          (Eval.exec p fuel s (.forStmt sp init cond post (.block bsp loopSS) :: rest) = some out ∧
            ∀ b ρ, out ≠ irEnd b ρ) ∨
          ∃ source target, Eval.execStmt p fuel s
              (.forStmt sp init cond post (.block bsp loopSS)) = some (.normal source) ∧
            Agree source target ∧ Scoped env source ∧
            IR.Body.exec fs fuel target next = some out := by
        intro out executed
        simp only [tolean.Core.Loop.lowerLoop, IR.Body.exec, eval_valueCodes,
          List.map_map, Function.comp_def] at executed
        change (do
          let value ← tolean.Core.Loop.runFold
            (fun inner => (IR.Body.exec fs fuel inner loopBody).map IR.loopOutcome)
            (fun value outer => some ((index, value) :: outer))
            (fun outer inner => IR.bindState (changedNames loopSS env) inner outer) t items
          match value with
          | .normal inner => IR.Body.exec fs fuel inner next
          | .ret (.ok value) => some (.ret value)
          | .ret (.error value) => some (.panic value)
          | _ => none) = some out at executed
        cases targetRun : tolean.Core.Loop.runFold
            (fun inner => (IR.Body.exec fs fuel inner loopBody).map IR.loopOutcome)
            (fun value outer => some ((index, value) :: outer))
            (fun outer inner => IR.bindState (changedNames loopSS env) inner outer) t items with
        | none => simp [targetRun] at executed
        | some targetOut =>
          obtain ⟨sourceOut, sourceRun, related⟩ :=
            LoopFrame.loop_refines p fs fuel env loopSS _ loopBody index freshIndex simBody
              (fun b k hk => by
                split at hk <;> cases b <;> simp_all [Tail.Allows])
              s t agree scope items targetRun
          have sourceStmt : Eval.execStmt p fuel s
              (.forStmt sp init cond post (.block bsp loopSS)) =
              Eval.Outcome.fromLoop sourceOut := by
            rw [Eval.execStmt]
            simp only [head, bind, Option.bind, safe, Bool.not_true, Bool.false_eq_true,
              ↓reduceIte]
            change ((tolean.Core.Loop.execLoop
              (fun inner => (Eval.exec p fuel inner loopSS).map Eval.Outcome.toLoop)
              (fun value outer => some ((index, value) :: outer))
              LoopScope.sourceLeave s items).bind _) = _
            rw [sourceRun]
            rfl
          cases targetOut <;> cases sourceOut <;>
            simp only [tolean.Core.Loop.Outcome.Rel] at related
          all_goals try contradiction
          · right
            exact ⟨_, _, sourceStmt, related.1, related.2.1,
              by simpa [targetRun] using executed⟩
          · left
            subst related
            rename_i r
            cases r with
            | ok v =>
              simp [targetRun, bind, Option.bind] at executed
              subst out
              exact ⟨exec_cons_ret p fuel sourceStmt, fun b _ h => by cases b <;> cases h⟩
            | error x =>
              simp [targetRun, bind, Option.bind] at executed
              subst out
              exact ⟨exec_cons_panic p fuel sourceStmt, fun b _ h => by cases b <;> cases h⟩
          · simp [targetRun] at executed
          · simp [targetRun] at executed
      refine ⟨fun value executed => ?_, fun b target executed => ?_, fun x executed => ?_⟩
      · rcases key _ executed with done | ⟨source, target, step, ha, hs, next⟩
        · exact done.1
        · rw [exec_cons_normal p fuel step]
          exact (simRest source target ha hs).1 value next
      · rcases key _ executed with done | ⟨source, inner, step, ha, hs, next⟩
        · exact absurd rfl (done.2 b target)
        · obtain ⟨_, _, _, impossible, -⟩ := (simRest source inner ha hs).2.1 b target next
          cases b <;> simp [Tail.Allows] at impossible
      · rcases key _ executed with done | ⟨source, target, step, ha, hs, next⟩
        · exact done.1
        · rw [exec_cons_normal p fuel step]
          exact (simRest source target ha hs).2.2 x next
  · exact stmts_sound p fs fuel hp hc translated

end tolean.Go.Proof
