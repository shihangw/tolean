import tolean.TypeScript.Proof.LoopHead

namespace tolean.TypeScript.Proof
open tolean.TypeScript.Syntax
open tolean.TypeScript.Eval (Val Outcome)

variable {N : Type} [JSNumber N]

/-- A successful state-result call supplies the callee's final map. -/
theorem exec_letBorrow {fs : List (DeclRef × List String × IR.Body)}
    {fuel : Nat} {ρ : Eval.Env N} {name : String} {ref : DeclRef} {index : Nat}
    {args : List IR.Expr} {rest : IR.Body} {o : Outcome N}
    (h : IR.Body.exec fs fuel ρ (.letBorrow name ref index args rest) = some o) :
    ∃ before vs k ps body param after entries,
      ρ.lookup name = some (.map before) ∧
      IR.Expr.evalList fs fuel ρ args = some vs ∧ fuel = k + 1 ∧
      fs.lookup ref = some (ps, body) ∧ ps.length = vs.length ∧ ps[index]? = some param ∧
      body.returnedState = some [param] ∧
      IR.Body.exec fs k (ps.zip vs).reverse body = some (.normal after) ∧
      after.lookup param = some (.map entries) ∧
      IR.Body.exec fs fuel (ρ.set name (.map entries)) rest = some o := by
  simp only [IR.Body.exec] at h
  cases hp : ρ.lookup name with
  | none => simp_all
  | some v =>
    cases v <;> try simp_all
    rename_i before
    cases hv : IR.Expr.evalList fs fuel ρ args with
    | none => simp_all
    | some vs =>
      cases fuel with
      | zero => simp_all
      | succ k =>
        cases hf : fs.lookup ref with
        | none => simp_all
        | some pb =>
          obtain ⟨ps, body⟩ := pb
          by_cases hl : ps.length = vs.length
          · cases hi : ps[index]? with
            | none => simp_all
            | some param =>
              by_cases hs : body.returnedState = some [param]
              · cases hr : IR.Body.exec fs k (ps.zip vs).reverse body with
                | none => simp_all
                | some result =>
                  cases result <;> try simp_all
                  rename_i after
                  cases hm : after.lookup param with
                  | none => simp_all
                  | some w =>
                    cases w <;> try simp_all
                    rename_i entries
                    exact ⟨ps, body, ⟨rfl, rfl⟩, hl, param, hi, hs, after, hr, entries, hm, h⟩
              · simp_all
          · simp_all

/-- The call invariant supplies a source normal completion with the same
map, which the call statement copies back into the caller's binding. -/
theorem borrow_call_from_agreement
    (m : Eval.Scope) (fs : List (DeclRef × List String × IR.Body))
    (k : Nat) (hc : CallsAgree (N := N) m.program fs (k + 1))
    (ρ : Eval.Env N) (sp cs ns ms : Span) (fn target param : String)
    (i : Nat) (args : List Expr) (vs : List (Val N))
    (ps : List String) (body : IR.Body) (after : Eval.Env N)
    (before entries : List (Val N × Val N))
    (hargs : Eval.evalList m (k + 1) ρ args = some vs)
    (hglobal : ρ.lookup fn = none)
    (htarget : args[i]? = some (.ident ms target))
    (hout : fs.lookup ⟨m.file, fn⟩ = some (ps, body))
    (hparam : ps[i]? = some param)
    (hstate : body.returnedState = some [param])
    (hlen : ps.length = vs.length)
    (hbefore : ρ.lookup target = some (.map before))
    (hrun : IR.Body.exec fs k (ps.zip vs).reverse body = some (.normal after))
    (hfinal : after.lookup param = some (.map entries)) :
    Eval.execStmt m (k + 1) ρ (.exprStmt sp (.call cs (.ident ns fn) args)) =
      some (.normal (ρ.set target (.map entries))) := by
  obtain ⟨source, afterS, hsource, hsig, hrunS, hfinalS⟩ :=
    hc.borrow k rfl ⟨m.file, fn⟩ ps body i param vs after entries
      hout hparam hstate hlen hrun hfinal
  have hbind : Eval.bindArgs ps vs = some (ps.zip vs).reverse := by
    simp [Eval.bindArgs, hlen]
  rw [Eval.execStmt]
  simp [hargs, hglobal, hsig, htarget, hsource, hparam, hbefore, hbind, hrunS, hfinalS]

open tolean.TypeScript.Translate

variable (m : Eval.Scope) (fs : List (DeclRef × List String × IR.Body)) (fuel : Nat)

/-- Writing out a value's type does not change its meaning. -/
theorem eval_withType (e : IR.Expr) (t source : Ty) (ρ : Eval.Env N) :
    IR.Expr.eval fs fuel ρ (withType e t source) = IR.Expr.eval fs fuel ρ e := by
  unfold withType
  cases e <;> (try simp only) <;> (try split) <;> simp [IR.Expr.eval]

theorem translateBorrowPlain_sim (hc : CallsAgree (N := N) m.program fs fuel)
    {env : Translate.Env} {ty : Ty} {arg : Expr} {ctx ctx' : Ctx} {out : IR.Expr}
    (h : translateBorrowPlain env ty arg ctx = .ok out ctx') :
    Sim (N := N) m fs fuel env arg out := by
  simp only [translateBorrowPlain, bind_ok, fuelLimit_ok, ite_state] at h
  obtain ⟨_, _, ⟨rfl, rfl⟩, code, s, he, h⟩ := h
  split at h
  rotate_left
  · simp at h
  simp only [bind_ok, pure_ok] at h
  obtain ⟨_, _, ⟨_, rfl⟩, rfl, _⟩ := h
  intro ρs ρo v ha hs hv
  rw [eval_withType, eval_value] at hv
  exact (expr_sound m fs fuel hc _).1 _ _ _ _ _ _ he ρs ρo v ha hs hv

theorem translateBorrowArg_sim (hc : CallsAgree (N := N) m.program fs fuel)
    {env : Translate.Env} {target : String} {mt ty : Ty} {arg : Expr} {ctx ctx' : Ctx} {out : IR.Expr}
    (h : translateBorrowArg env target mt ty arg ctx = .ok out ctx') :
    Sim (N := N) m fs fuel env arg out := by
  cases arg <;> try exact translateBorrowPlain_sim m fs fuel hc h
  rename_i sp name
  simp only [translateBorrowArg, ite_state] at h
  split at h
  · split at h
    · simp only [pure_bind, pure_ok] at h
      obtain ⟨rfl, _⟩ := h
      intro ρs ρo v ha _ hv
      simp only [IR.Expr.eval] at hv
      rw [Eval.eval]
      rw [ha name, hv]
    · simp at h
  · exact translateBorrowPlain_sim m fs fuel hc h

theorem translateBorrowArgs_sim (hc : CallsAgree (N := N) m.program fs fuel)
    {env : Translate.Env} {target : String} {mt : Ty} :
    ∀ ps args ctx outs ctx', args.length = ps.length →
      translateBorrowArgs env target mt ps args ctx = .ok outs ctx' →
      SimList (N := N) m fs fuel env args outs
  | [], [], _, outs, _, _, h => by
    simp only [translateBorrowArgs, pure_ok] at h
    obtain ⟨rfl, _⟩ := h
    intro ρs ρo vs _ _ hv
    simp [IR.Expr.evalList] at hv
    subst hv
    simp [Eval.evalList]
  | p :: ps, a :: args, _, outs, _, hl, h => by
    simp only [translateBorrowArgs, bind_ok, pure_ok] at h
    obtain ⟨code, s, hcode, codes, s', hcodes, rfl, _⟩ := h
    have hsim := translateBorrowArg_sim m fs fuel hc hcode
    have ih := translateBorrowArgs_sim hc ps args _ _ _ (by simpa using hl) hcodes
    intro ρs ρo vs ha hs hv
    simp only [IR.Expr.evalList] at hv
    cases hx : IR.Expr.eval fs fuel ρo code with
    | none => simp [hx] at hv
    | some x =>
      cases hxs : IR.Expr.evalList fs fuel ρo codes with
      | none => simp [hx, hxs] at hv
      | some xs =>
        simp [hx, hxs] at hv
        subst hv
        simp [Eval.evalList, hsim ρs ρo x ha hs hx, ih ρs ρo xs ha hs hxs]
  | [], _ :: _, _, _, _, hl, _ | _ :: _, [], _, _, _, hl, _ => by simp at hl

theorem translateBorrowCall_sim (hc : CallsAgree (N := N) m.program fs fuel)
    {env : Translate.Env} {sp : Span} {fn : FnInfo} {i : Nat} {args : List Expr}
    {ctx ctx' : Ctx} {target : String} {call : IR.Expr}
    (h : translateBorrowCall env sp fn i args ctx = .ok (target, call) ctx') :
    env.has fn.name = false ∧ ∃ ms outs,
      args[i]? = some (.ident ms target) ∧ call = .call fn.ref outs ∧
      SimList (N := N) m fs fuel env args outs := by
  unfold translateBorrowCall at h
  simp only [ite_state] at h
  split at h
  · simp at h
  rename_i hn
  have hname : env.has fn.name = false := by simpa using hn
  simp only [pure_bind, bind_ok, get_ok] at h
  obtain ⟨_, _, ⟨rfl, rfl⟩, h⟩ := h
  split at h
  rotate_left
  · simp at h
  split at h
  rotate_left
  · simp at h
  rename_i hl
  have hlen : args.length = fn.params.length := by simpa using hl
  cases ha : args[i]? with
  | none => simp [ha] at h
  | some a =>
    cases a <;> try simp [ha] at h
    rename_i ms name
    cases hb : env.lookup name with
    | none => simp [hb] at h
    | some binding =>
      simp only [hb, ite_state] at h
      split at h
      rotate_left
      · simp at h
      simp only [map_ok] at h
      obtain ⟨outs, hargs, he⟩ := h
      cases he
      exact ⟨hname, ms, outs, rfl, rfl, translateBorrowArgs_sim m fs fuel hc _ _ _ _ _ hlen hargs⟩

theorem borrowCall?_some {env : Translate.Env} {e : Expr} {fn : FnInfo} {i : Nat} {args : List Expr}
    (h : borrowCall? env e = some (fn, i, args)) :
    ∃ cs ns, e = .call cs (.ident ns fn.name) args ∧ fn ∈ env.functions ∧ fn.borrow = some i := by
  unfold borrowCall? at h
  split at h
  · rename_i cs ns name args'
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨f, hf, j, hj, rfl, rfl, rfl⟩ := h
    have hn : fn.name = name := by simpa using List.find?_some hf
    subst hn
    exact ⟨cs, ns, rfl, List.mem_of_find?_eq_some hf, hj⟩
  · simp at h

theorem exprChanges_stmt {fns : List (String × List String)} {sp : Span} {e : Expr} {n : String}
    (h : n ∈ exprChanges fns e) : n ∈ stmtChanges fns (.exprStmt sp e) := by
  cases e <;> try exact h
  rename_i cs callee args
  cases callee <;> try exact h
  rename_i ns name
  cases hf : fns.lookup name with
  | none =>
    simp only [stmtChanges, hf, List.mem_append]
    exact Or.inr (by simpa [exprChanges, calleeChanges, hf] using h)
  | some names => simpa [stmtChanges, exprChanges, calleeChanges, hf] using h

end tolean.TypeScript.Proof
