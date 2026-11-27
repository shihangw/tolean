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
  obtain ⟨_, fresh, modified, hs, ha, hn, hf⟩ := (sim s t agree scope).2.1 innerT done
  exact ⟨fresh ++ modified, hs, fresh, modified, rfl, ha, hn, hf⟩

/-- This uses the real translator's no-shadowing check and its statement proof.
The premise is successful translation, not an assumed body simulation. -/
theorem accepted_body_frame (p : Eval.Program) (fs : Funcs) (fuel : Nat)
    (ctx : Ctx) (program : ctx.program = p) (calls : CallsAgree p fs fuel)
    (laws : LoopLaw p fs fuel)
    (env : Pure.Env) (ss : List Stmt) (tail : Tail) (body : IR.Body) (budget : Nat)
    (translated : translateStmts ctx env tail budget ss = .ok body)
    (s t innerT : Eval.Env) (agree : Agree s t) (scope : Scoped env s)
    (done : IR.Body.exec fs fuel t body = some (.normal innerT)) :
    ∃ innerS, Eval.exec p fuel s ss = some (.normal innerS) ∧
      Inner env ss s t innerS innerT :=
  body_frame p fs fuel env ss tail body (stmts_sound p fs fuel program calls laws translated)
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

/-- Binding the counter adds one fresh local to the body's frame. Scope exit
must discard that binding as well as declarations made by the body. -/
theorem bound_body_frame (p : Eval.Program) (fs : Funcs) (fuel : Nat)
    (env : Pure.Env) (ss : List Stmt) (tail : Tail) (body : IR.Body)
    (index : String) (value : Eval.Val) (freshIndex : env.has index = false)
    (sim : StmtSim p fs fuel (env ++ [⟨index, .int⟩]) tail ss body)
    (s t innerT : Eval.Env) (agree : Agree s t) (scope : Scoped env s)
    (done : IR.Body.exec fs fuel ((index, value) :: t) body = some (.normal innerT)) :
    ∃ innerS, Eval.exec p fuel ((index, value) :: s) ss = some (.normal innerS) ∧
      Inner env ss s t innerS innerT := by
  obtain ⟨innerS, executed, fresh, modified, shape, agreement, freshNames, frame⟩ :=
    body_frame p fs fuel _ ss tail body sim _ _ innerT
      (agree_cons agree index value) (scoped_cons scope index .int value) done
  cases modified with
  | nil => simp [Frame] at frame
  | cons entry modified =>
    obtain ⟨entryName, _, frame⟩ := frame
    refine ⟨innerS, executed, fresh ++ [entry], modified, ?_, agreement, ?_, frame⟩
    · simpa [List.append_assoc] using shape
    · intro q hq
      rcases List.mem_append.mp hq with hq | hq
      · have h := freshNames q hq
        rw [has_append] at h
        exact (Bool.or_eq_false_iff.mp h).1
      · have : q = entry := by simpa using hq
        subst q
        simpa only [entryName] using freshIndex

/-- The shared loop theorem lifts Go's success-only statement simulation.
Unlike exact simulation, this does not require failed target calls to fail in
the source. -/
theorem loop_refines (p : Eval.Program) (fs : Funcs) (fuel : Nat)
    (env : Pure.Env) (ss : List Stmt) (tail : Tail) (body : IR.Body)
    (index : String) (freshIndex : env.has index = false)
    (sim : StmtSim p fs fuel (env ++ [⟨index, .int⟩]) tail ss body)
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
        obtain ⟨innerS, hs, frame⟩ :=
          bound_body_frame p fs fuel env ss tail body index value freshIndex sim
            s t innerT h.1 h.2.1 ht
        exact ⟨.normal innerS, by simp [hs, Eval.Outcome.toLoop], frame⟩
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

/-- The interpreter's counted loop, once its bounds have values. -/
theorem execStmt_counted (p : Eval.Program) (fuel : Nat) {s : Eval.Env} {sp bsp : Span}
    {init : Option Stmt} {cond : Option Expr} {post : Option Stmt} {loopSS : List Stmt}
    {index : String} {start stop : Expr} {reads : List String} {a b : Int}
    (head : Eval.countedHead init cond post = some (index, start, stop, reads))
    (safe : Eval.countedBodySafe (index :: reads) (.block bsp loopSS) = true)
    (hlo : Eval.eval p fuel s start = some (.ok (.int a)))
    (hhi : Eval.eval p fuel s stop = some (.ok (.int b))) :
    Eval.execStmt p fuel s (.forStmt sp init cond post (.block bsp loopSS)) =
      (tolean.Core.Loop.execLoop
        (fun inner => (Eval.exec p fuel inner loopSS).map Eval.Outcome.toLoop)
        (fun value outer => some ((index, value) :: outer))
        LoopScope.sourceLeave s ((upTo a b).map .int)).bind Eval.Outcome.fromLoop := by
  have head' := head
  clear head
  unfold Eval.countedHead at head'
  split at head'
  · simp only [bind, pure] at head'
    split at head'
    · simp at head'
    · rename_i sp1 sp2 index' start' sp3 sp4 test stop' sp5 sp6 step hne
      simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, not_or, Decidable.not_not] at hne
      obtain ⟨rfl, rfl⟩ := hne
      cases hs : Eval.boundReads start' with
      | none => simp [hs] at head'
      | some r0 =>
        cases hr : Eval.boundReads stop' with
        | none => simp [hs, hr] at head'
        | some r =>
          by_cases hc : r.contains index' = true
          · simp [hs, hr] at head'
            exact absurd (by simpa using hc) head'.1
          · simp only [hs, hr, hc, Option.bind_some, Bool.false_eq_true, ↓reduceIte,
              Option.some.injEq, Prod.mk.injEq] at head'
            obtain ⟨rfl, rfl, rfl, rfl⟩ := head'
            rw [Eval.execStmt]
            simp only [Eval.countedHead, hs, hr, hc, bind, Option.bind, safe, bne_self_eq_false,
              Bool.or_self, Bool.false_eq_true, ↓reduceIte, Bool.not_true, hlo, hhi,
              Eval.withValue, pure]
            first
              | rfl
              | (congr 1; funext o; rcases o with _ | ⟨_ | _⟩ | _ | _ <;> rfl)
  · simp at head'

/-- A counted loop and the statements after it mean what their source
means, from the shared loop core's refinement. -/
theorem loop_law (p : Eval.Program) (fs : Funcs) (fuel : Nat) : LoopLaw p fs fuel := by
  intro env tail sp bsp init cond post loopSS rest index start stop reads items loopBody next
    head safe freshIndex bounds simBody simRest
  intro s t agree scope
  have key : ∀ out, IR.Body.exec fs fuel t
      (tolean.Core.Loop.lowerLoop sp
        ((env.filter fun l => (changesList loopSS).contains l.name).map
          fun l => (l.name, l.type.lean))
        index .int loopBody items next false none) = some out →
      (Eval.exec p fuel s (.forStmt sp init cond post (.block bsp loopSS) :: rest) = some out ∧
        ∀ ρ, out ≠ .normal ρ) ∨
      ∃ source target, Eval.execStmt p fuel s
          (.forStmt sp init cond post (.block bsp loopSS)) = some (.normal source) ∧
        Agree source target ∧ Scoped env source ∧ Frame (changesList loopSS) source s ∧
        IR.Body.exec fs fuel target next = some out := by
    intro out executed
    simp only [tolean.Core.Loop.lowerLoop, IR.Body.exec, List.map_map, Function.comp_def] at executed
    cases hitems : IR.Expr.items fs fuel t items with
    | none => simp [hitems] at executed
    | some values =>
      obtain ⟨a, b, rfl, hlo, hhi⟩ := bounds s t values agree scope hitems
      rw [hitems] at executed
      change (do
        let value ← tolean.Core.Loop.runFold
          (fun inner => (IR.Body.exec fs fuel inner loopBody).map IR.loopOutcome)
          (fun value outer => some ((index, value) :: outer))
          (fun outer inner => IR.bindState (changedNames loopSS env) inner outer) t
          ((upTo a b).map .int)
        match value with
        | .normal inner => IR.Body.exec fs fuel inner next
        | .ret (.ok value) => some (.ret value)
        | .ret (.error value) => some (.panic value)
        | _ => none) = some out at executed
      cases targetRun : tolean.Core.Loop.runFold
          (fun inner => (IR.Body.exec fs fuel inner loopBody).map IR.loopOutcome)
          (fun value outer => some ((index, value) :: outer))
          (fun outer inner => IR.bindState (changedNames loopSS env) inner outer) t
          ((upTo a b).map .int) with
      | none => simp [targetRun] at executed
      | some targetOut =>
        obtain ⟨sourceOut, sourceRun, related⟩ :=
          LoopFrame.loop_refines p fs fuel env loopSS _ loopBody index freshIndex simBody
            s t agree scope _ targetRun
        have sourceStmt : Eval.execStmt p fuel s
            (.forStmt sp init cond post (.block bsp loopSS)) =
            Eval.Outcome.fromLoop sourceOut := by
          rw [execStmt_counted p fuel head safe hlo hhi, sourceRun]
          rfl
        cases targetOut <;> cases sourceOut <;>
          simp only [tolean.Core.Loop.Outcome.Rel] at related
        all_goals try contradiction
        · right
          exact ⟨_, _, sourceStmt, related.1, related.2.1, related.2.2,
            by simpa [targetRun] using executed⟩
        · left
          subst related
          rename_i r
          cases r with
          | ok v =>
            simp [targetRun, bind, Option.bind] at executed
            subst out
            exact ⟨exec_cons_ret p fuel sourceStmt, fun _ h => by cases h⟩
          | error x =>
            simp [targetRun, bind, Option.bind] at executed
            subst out
            exact ⟨exec_cons_panic p fuel sourceStmt, fun _ h => by cases h⟩
        · simp [targetRun] at executed
        · simp [targetRun] at executed
  refine ⟨fun value executed => ?_, fun target executed => ?_, fun x executed => ?_⟩
  · rcases key _ executed with done | ⟨source, target, step, ha, hs, -, hnext⟩
    · exact done.1
    · rw [exec_cons_normal p fuel step]
      exact (simRest source target ha hs).1 value hnext
  · rcases key _ executed with done | ⟨source, inner, step, ha, hs, hfr, hnext⟩
    · exact absurd rfl (done.2 target)
    · obtain ⟨hret, new, mod, hex, hag, hnew, hfr'⟩ := (simRest source inner ha hs).2.1 target hnext
      refine ⟨hret, new, mod, by rw [exec_cons_normal p fuel step]; exact hex, hag, hnew, ?_⟩
      simpa [changesList, stmtChanges] using hfr'.trans hfr
  · rcases key _ executed with done | ⟨source, target, step, ha, hs, -, hnext⟩
    · exact done.1
    · rw [exec_cons_normal p fuel step]
      exact (simRest source target ha hs).2.2 x hnext

/-- The body of a function, with counted loops anywhere in it, obeys the
success-only contract of the statement translator. -/
theorem top_sound (p : Eval.Program) (fs : Funcs) (fuel : Nat)
    {ctx : Ctx} (hp : ctx.program = p) (hc : CallsAgree p fs fuel)
    {env : Pure.Env} {result : Ty} {monadic : Bool} {ss : List Stmt} {body : IR.Body}
    (translated : translateTop ctx env result monadic ss = .ok body) :
    StmtSim p fs fuel env (.ret result monadic) ss body :=
  stmts_sound p fs fuel hp hc (loop_law p fs fuel) translated

end tolean.Go.Proof
