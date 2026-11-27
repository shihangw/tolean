import tolean.TypeScript.Proof.LoopHead

namespace tolean.TypeScript.Proof
open tolean.TypeScript.Syntax
open tolean.TypeScript.Eval (Val Outcome)

variable {N : Type} [JSNumber N]

/-! ### Copying borrowed maps back -/

omit [JSNumber N] in
theorem lookup_set_isSome (ρ : Eval.Env N) (k n : String) (v : Val N) :
    ((ρ.set k v).lookup n).isSome = (ρ.lookup n).isSome := by
  by_cases hn : k = n
  · subst hn
    cases hl : ρ.lookup k with
    | none =>
      have : ∀ ρ' : Eval.Env N, ρ'.lookup k = none → ρ'.set k v = ρ' := by
        intro ρ' h'
        induction ρ' with
        | nil => rfl
        | cons p rest ih =>
          obtain ⟨j, w⟩ := p
          have hj : j ≠ k := by
            intro hj; subst hj; simp at h'
          have hr : rest.lookup k = none := by
            have hj' : ¬ k = j := fun e => hj e.symm
            simpa [Eval.Env.lookup_cons, hj'] using h'
          simp [Eval.Env.set_cons, hj, ih hr]
      rw [this ρ hl, hl]
    | some w => rw [Eval.Env.lookup_set_same _ _ _ (by simp [hl])]; simp
  · rw [Eval.Env.lookup_set_ne _ _ _ _ hn]

omit [JSNumber N] in
/-- Changing distinct variables that the environment has gives each its
new value, and leaves the others. -/
theorem lookup_setAll {n : String} :
    ∀ (binds env : Eval.Env N), (binds.map (·.1)).Nodup → (env.lookup n).isSome →
      (env.setAll binds).lookup n = (binds.lookup n).or (env.lookup n)
  | [], env, _, _ => by simp [Eval.Env.setAll]
  | (k, w) :: bs, env, hnd, hn => by
    have hset : (env.setAll ((k, w) :: bs)) = (env.set k w).setAll bs := by
      simp [Eval.Env.setAll]
    rw [hset, lookup_setAll bs (env.set k w) (List.nodup_cons.mp hnd).2
      (by rw [lookup_set_isSome]; exact hn)]
    by_cases hk : n = k
    · subst hk
      have hnot : bs.lookup n = none := by
        apply List.lookup_eq_none_iff.mpr
        intro q hq
        simp only [bne_iff_ne, ne_eq]
        intro he
        exact (List.nodup_cons.mp hnd).1 (List.mem_map.mpr ⟨q, hq, he.symm⟩)
      rw [hnot, Eval.Env.lookup_set_same _ _ _ hn]
      simp [List.lookup]
    · have hne : (n == k) = false := by simpa using hk
      rw [Eval.Env.lookup_set_ne _ _ _ _ (Ne.symm hk)]
      simp [List.lookup, hne]

theorem mapM_some_map {α β γ : Type} {f : α → Option β} {g : β → γ} {h : α → γ}
    (H : ∀ x y, f x = some y → g y = h x) :
    ∀ {l : List α} {r : List β}, l.mapM f = some r → r.map g = l.map h
  | [], r, hl => by simp at hl; subst hl; rfl
  | x :: l, r, hl => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hl
    obtain ⟨y, hy, rest, hr, rfl⟩ := hl
    simp [H x y hy, mapM_some_map H hr]

theorem mapM_congr_mem {α β : Type} {f f' : α → Option β} :
    ∀ {l : List α}, (∀ x ∈ l, f x = f' x) → l.mapM f = l.mapM f'
  | [], _ => rfl
  | x :: l, H => by
    simp only [List.mapM_cons]
    rw [H x (by simp), mapM_congr_mem (l := l) (fun y hy => H y (by simp [hy]))]

omit [JSNumber N] in
theorem borrowedMaps_keys {after : Eval.Env N} {pairs : List (String × String)} {inner : Eval.Env N}
    (h : Eval.borrowedMaps after pairs = some inner) : inner.map (·.1) = pairs.map (·.1) := by
  refine mapM_some_map (fun x y hxy => ?_) h
  obtain ⟨t, q⟩ := x
  simp only [Option.bind_eq_bind] at hxy
  cases hq : after.lookup q with
  | none => simp [hq] at hxy
  | some v =>
    cases v <;> simp [hq] at hxy
    subst hxy; rfl

omit [JSNumber N] in
theorem borrowedMaps_congr {a b : Eval.Env N} {pairs : List (String × String)}
    (h : ∀ q ∈ pairs.map (·.2), a.lookup q = b.lookup q) :
    Eval.borrowedMaps a pairs = Eval.borrowedMaps b pairs := by
  unfold Eval.borrowedMaps
  apply mapM_congr_mem
  intro x hx
  obtain ⟨t, q⟩ := x
  simp only [h q (List.mem_map.mpr ⟨_, hx, rfl⟩)]

omit [JSNumber N] in
theorem mapM_getElem?_length {ps : List String} :
    ∀ {is : List Nat} {qs : List String}, is.mapM (ps[·]?) = some qs → qs.length = is.length
  | [], qs, h => by simp at h; subst h; rfl
  | i :: is, qs, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨q, _, rest, hr, rfl⟩ := h
    simp [mapM_getElem?_length hr]

omit [JSNumber N] in
theorem mapM_getElem?_mem {ps : List String} :
    ∀ {is : List Nat} {qs : List String}, is.mapM (ps[·]?) = some qs → ∀ q ∈ qs, q ∈ ps
  | [], qs, h, q, hq => by simp at h; subst h; simp at hq
  | i :: is, qs, h, q, hq => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨q', hq', rest, hr, rfl⟩ := h
    rcases List.mem_cons.mp hq with rfl | hq
    · exact List.mem_of_getElem? hq'
    · exact mapM_getElem?_mem hr q hq

omit [JSNumber N] in
/-- Distinct parameters name the same list of indices only once. -/
theorem mapM_getElem?_inj {ps : List String} (hnd : ps.Nodup) :
    ∀ {is js : List Nat} {qs : List String}, is.mapM (ps[·]?) = some qs →
      js.mapM (ps[·]?) = some qs → is = js
  | [], [], _, _, _ => rfl
  | [], _ :: _, qs, h₁, h₂ => by
    have := mapM_getElem?_length h₁
    have := mapM_getElem?_length h₂
    simp_all
  | _ :: _, [], qs, h₁, h₂ => by
    have := mapM_getElem?_length h₁
    have := mapM_getElem?_length h₂
    simp_all
  | i :: is, j :: js, qs, h₁, h₂ => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h₁ h₂
    obtain ⟨q, hq, rest, hr, rfl⟩ := h₁
    obtain ⟨q', hq', rest', hr', he⟩ := h₂
    simp only [List.cons.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    have hij : i = j := (List.getElem?_inj (List.getElem?_eq_some_iff.mp hq).1 hnd).mp (hq.trans hq'.symm)
    rw [hij, mapM_getElem?_inj hnd hr hr']

omit [JSNumber N] in
theorem holdMaps_isSome {ρ : Eval.Env N} {names : List String} (h : Eval.holdMaps ρ names = true)
    {n : String} (hn : n ∈ names) : (ρ.lookup n).isSome := by
  unfold Eval.holdMaps at h
  have := List.all_eq_true.mp h n hn
  cases hl : ρ.lookup n with
  | none => simp [hl] at this
  | some v => rfl

omit [JSNumber N] in
theorem holdMaps_congr {ρs ρo : Eval.Env N} (ha : ∀ n, ρs.lookup n = ρo.lookup n) (names : List String) :
    Eval.holdMaps ρs names = Eval.holdMaps ρo names := by
  unfold Eval.holdMaps
  simp only [ha]

theorem mem_borrowTargetsAt {args : List Expr} :
    ∀ {is : List Nat} {ts : List (Span × String)}, borrowTargetsAt args is = some ts →
      ∀ {ms : Span} {n : String}, (ms, n) ∈ ts → ∃ i : Nat, args[i]? = some (Expr.ident ms n)
  | [], ts, h, _, _, hm => by
    simp [borrowTargetsAt] at h; subst h; simp at hm
  | i :: is, ts, h, ms, n, hm => by
    unfold borrowTargetsAt at h
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨t, ht, rest, hr, rfl⟩ := h
    rcases List.mem_cons.mp hm with he | hm
    · subst he
      revert ht
      cases ha : args[i]? with
      | none => simp
      | some a =>
        cases a <;> simp
        rintro rfl rfl
        exact ⟨i, ha⟩
    · exact mem_borrowTargetsAt (is := is) (by unfold borrowTargetsAt; exact hr) hm

/-- A successful state-result call supplies the callee's final maps. -/
theorem exec_letBorrow {fs : List (DeclRef × List String × IR.Body)}
    {fuel : Nat} {ρ : Eval.Env N} {names : List String} {ref : DeclRef} {indices : List Nat}
    {args : List IR.Expr} {rest : IR.Body} {o : Outcome N}
    (h : IR.Body.exec fs fuel ρ (.letBorrow none names ref indices args rest) = some o) :
    ∃ vs k ps body params after inner ρ₂,
      Eval.holdMaps ρ names = true ∧
      IR.Expr.evalList fs fuel ρ args = some vs ∧ fuel = k + 1 ∧
      fs.lookup ref = some (ps, body) ∧ ps.length = vs.length ∧
      indices.mapM (ps[·]?) = some params ∧ names.length = params.length ∧
      body.returnedState = some params ∧
      IR.Body.exec fs k (ps.zip vs).reverse body = some (.normal after) ∧
      Eval.borrowedMaps after (names.zip params) = some inner ∧
      IR.bindState names inner ρ = some ρ₂ ∧
      IR.Body.exec fs fuel ρ₂ rest = some o := by
  simp only [IR.Body.exec] at h
  by_cases hm : Eval.holdMaps ρ names = true
  rotate_left
  · simp [hm] at h
  simp only [hm, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
  cases hv : IR.Expr.evalList fs fuel ρ args with
  | none => simp [hv] at h
  | some vs =>
    cases fuel with
    | zero => simp [hv] at h
    | succ k =>
      cases hf : fs.lookup ref with
      | none => simp [hv, hf] at h
      | some pb =>
        obtain ⟨ps, body⟩ := pb
        by_cases hl : ps.length = vs.length
        rotate_left
        · simp [hv, hf, hl] at h
        cases hp : indices.mapM (ps[·]?) with
        | none => simp [hv, hf, hl, hp] at h
        | some params =>
          by_cases hn : names.length = params.length
          rotate_left
          · simp [hv, hf, hl, hp, hn] at h
          by_cases hs : body.returnedState = some params
          rotate_left
          · simp [hv, hf, hl, hp, hn, hs] at h
          cases hr : IR.Body.exec fs k (ps.zip vs).reverse body with
          | none => simp [hv, hf, hl, hp, hn, hs, hr] at h
          | some result =>
            cases result with
            | normal after =>
              cases hi : Eval.borrowedMaps after (names.zip params) with
              | none => simp [hv, hf, hl, hp, hn, hs, hr, hi] at h
              | some inner =>
                cases hb : IR.bindState names inner ρ with
                | none => simp [hv, hf, hl, hp, hn, hs, hr, hi, hb] at h
                | some ρ₂ =>
                  simp [hv, hf, hl, hp, hn, hs, hr, hi, hb] at h
                  exact ⟨vs, k, ps, body, params, after, inner, ρ₂, hm, rfl, rfl, rfl, hl, hp, hn, hs,
                    hr, hi, hb, h⟩
            | _ => simp [hv, hf, hl, hp, hn, hs, hr] at h

/-- A successful call of a borrowing function that returns a value binds
its variable, and supplies the value and the callee's final maps. -/
theorem exec_letBorrowValue {fs : List (DeclRef × List String × IR.Body)}
    {fuel : Nat} {ρ : Eval.Env N} {x : String} {names : List String} {ref : DeclRef} {indices : List Nat}
    {args : List IR.Expr} {rest : IR.Body} {o : Outcome N}
    (h : IR.Body.exec fs fuel ρ (.letBorrow (some x) names ref indices args rest) = some o) :
    ∃ vs k ps body params r after w inner ρ₂,
      Eval.holdMaps ρ names = true ∧
      IR.Expr.evalList fs fuel ρ args = some vs ∧ fuel = k + 1 ∧
      fs.lookup ref = some (ps, body) ∧ ps.length = vs.length ∧
      indices.mapM (ps[·]?) = some params ∧ names.length = params.length ∧
      body.returnedState = some (r :: params) ∧ r ∉ ps ∧
      IR.Body.exec fs k ((r, .undefined) :: (ps.zip vs).reverse) body = some (.normal after) ∧
      after.lookup r = some w ∧
      Eval.borrowedMaps after (names.zip params) = some inner ∧
      IR.bindState names inner ρ = some ρ₂ ∧
      IR.Body.exec fs fuel ((x, w) :: ρ₂) rest = some o := by
  simp only [IR.Body.exec] at h
  by_cases hm : Eval.holdMaps ρ names = true
  rotate_left
  · simp [hm] at h
  simp only [hm, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
  cases hv : IR.Expr.evalList fs fuel ρ args with
  | none => simp [hv] at h
  | some vs =>
    cases fuel with
    | zero => simp [hv] at h
    | succ k =>
      cases hf : fs.lookup ref with
      | none => simp [hv, hf] at h
      | some pb =>
        obtain ⟨ps, body⟩ := pb
        by_cases hl : ps.length = vs.length
        rotate_left
        · simp [hv, hf, hl] at h
        cases hp : indices.mapM (ps[·]?) with
        | none => simp [hv, hf, hl, hp] at h
        | some params =>
          by_cases hn : names.length = params.length
          rotate_left
          · simp [hv, hf, hl, hp, hn] at h
          cases hs : body.returnedState with
          | none => simp [hv, hf, hl, hp, hn, hs] at h
          | some rs =>
            cases rs with
            | nil => simp [hv, hf, hl, hp, hn, hs] at h
            | cons r ps' =>
              by_cases hq' : ps' = params
              rotate_left
              · simp [hv, hf, hl, hp, hn, hs, hq'] at h
              subst hq'
              by_cases hr : r ∈ ps
              · simp [hv, hf, hl, hp, hn, hs, hr] at h
              cases hrun : IR.Body.exec fs k ((r, .undefined) :: (ps.zip vs).reverse) body with
              | none => simp [hv, hf, hl, hp, hn, hs, hr, hrun] at h
              | some result =>
                cases result with
                | normal after =>
                  cases hw : after.lookup r with
                  | none => simp [hv, hf, hl, hp, hn, hs, hr, hrun, hw] at h
                  | some w =>
                    cases hi : Eval.borrowedMaps after (names.zip ps') with
                    | none => simp [hv, hf, hl, hp, hn, hs, hr, hrun, hw, hi] at h
                    | some inner =>
                      cases hb : IR.bindState names inner ρ with
                      | none => simp [hv, hf, hl, hp, hn, hs, hr, hrun, hw, hi, hb] at h
                      | some ρ₂ =>
                        simp [hv, hf, hl, hp, hn, hs, hr, hrun, hw, hi, hb] at h
                        exact ⟨vs, k, ps, body, ps', r, after, w, inner, ρ₂, hm, rfl, rfl, rfl, hl, hp, hn,
                          hs, hr, hrun, hw, hi, hb, h⟩
                | _ => simp [hv, hf, hl, hp, hn, hs, hr, hrun] at h

/-- The call invariant supplies a source normal completion with the same
maps, which the call statement copies back into the caller's bindings. -/
theorem borrow_call_from_agreement
    (m : Eval.Scope) (fs : List (DeclRef × List String × IR.Body))
    (k : Nat) (hc : CallsAgree (N := N) m.program fs (k + 1))
    (ρ : Eval.Env N) (sp cs ns : Span) (fn : String)
    (indices : List Nat) (args : List Expr) (ts : List (Span × String)) (vs : List (Val N))
    (ps : List String) (body : IR.Body) (params : List String) (after inner : Eval.Env N)
    (hargs : Eval.evalList m (k + 1) ρ args = some vs)
    (hglobal : ρ.lookup fn = none)
    (hts : borrowTargetsAt args indices = some ts)
    (hnd : (ts.map (·.2)).Nodup)
    (hmaps : Eval.holdMaps ρ (ts.map (·.2)) = true)
    (hout : fs.lookup ⟨m.file, fn⟩ = some (ps, body))
    (hparams : indices.mapM (ps[·]?) = some params)
    (hstate : body.returnedState = some params)
    (hlen : ps.length = vs.length)
    (hrun : IR.Body.exec fs k (ps.zip vs).reverse body = some (.normal after))
    (hinner : Eval.borrowedMaps after ((ts.map (·.2)).zip params) = some inner) :
    Eval.execStmt m (k + 1) ρ (.exprStmt sp (.call cs (.ident ns fn) args)) =
      some (.normal (ρ.setAll inner)) := by
  obtain ⟨source, afterS, hsource, hsig, hrunS, hagree⟩ :=
    hc.borrow k rfl ⟨m.file, fn⟩ ps body indices params vs after hout hparams hstate hlen hrun
  have hbind : Eval.bindArgs ps vs = some (ps.zip vs).reverse := by
    simp [Eval.bindArgs, hlen]
  have hinnerS : Eval.borrowedMaps afterS ((ts.map (·.2)).zip params) = some inner := by
    rw [borrowedMaps_congr (b := after) ?_]
    · exact hinner
    intro q hq
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hq
    exact hagree _ (List.of_mem_zip hx).2
  rw [Eval.execStmt]
  simp [hargs, hglobal, hsig, hts, hnd, hmaps, hsource, hparams, hbind, hrunS, hinnerS]

open tolean.TypeScript.Translate

variable (m : Eval.Scope) (fs : List (DeclRef × List String × IR.Body)) (fuel : Nat)

/-- Writing out a value's type does not change its meaning. -/
theorem eval_withType (e : IR.Expr) (t source : Ty) (ρ : Eval.Env N) :
    IR.Expr.eval fs fuel ρ (withType e t source) = IR.Expr.eval fs fuel ρ e := by
  unfold withType
  repeat' first | (solve | simp only [IR.Expr.eval]) | split

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
    {env : Translate.Env} {targets : List (String × Ty)} {ty : Ty} {arg : Expr} {ctx ctx' : Ctx} {out : IR.Expr}
    (h : translateBorrowArg env targets ty arg ctx = .ok out ctx') :
    Sim (N := N) m fs fuel env arg out := by
  cases arg <;> try exact translateBorrowPlain_sim m fs fuel hc h
  rename_i sp name
  simp only [translateBorrowArg] at h
  cases hl : targets.lookup name with
  | none =>
    simp only [hl] at h
    exact translateBorrowPlain_sim m fs fuel hc h
  | some mapType =>
    simp only [hl, ite_state] at h
    split at h
    · simp only [pure_bind, pure_ok] at h
      obtain ⟨rfl, _⟩ := h
      intro ρs ρo v ha _ hv
      simp only [IR.Expr.eval] at hv
      rw [Eval.eval]
      rw [ha name, hv]
    · simp at h

theorem translateBorrowArgs_sim (hc : CallsAgree (N := N) m.program fs fuel)
    {env : Translate.Env} {targets : List (String × Ty)} :
    ∀ ps args ctx outs ctx', args.length = ps.length →
      translateBorrowArgs env targets ps args ctx = .ok outs ctx' →
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

omit [JSNumber N] in
theorem borrowTargetTypes_ok {env : Translate.Env} {sp : Span} {args : List Expr} :
    ∀ {is : List Nat} {ctx ctx' : Ctx} {tys : List (String × Ty)},
      borrowTargetTypes env sp args is ctx = .ok tys ctx' →
      ∃ ts, borrowTargetsAt args is = some ts ∧ tys.map (·.1) = ts.map (·.2)
  | [], ctx, ctx', tys, h => by
    simp only [borrowTargetTypes, pure_ok] at h
    obtain ⟨rfl, _⟩ := h
    exact ⟨[], rfl, rfl⟩
  | i :: is, ctx, ctx', tys, h => by
    simp only [borrowTargetTypes] at h
    cases ha : args[i]? with
    | none => simp [ha] at h; try exact absurd h (reject_ne_ok _ _ _ _ _)
    | some a =>
      cases a <;> simp only [ha] at h <;> try exact absurd h (reject_ne_ok _ _ _ _ _)
      rename_i ms name
      cases hb : env.lookup name with
      | none => simp only [hb] at h; exact absurd h (reject_ne_ok _ _ _ _ _)
      | some binding =>
        simp only [hb, ite_state] at h
        split at h
        · simp only [pure_bind, bind_ok, pure_ok] at h
          obtain ⟨rest, c, hrest, rfl, _⟩ := h
          obtain ⟨ts, hts, hmap⟩ := borrowTargetTypes_ok hrest
          refine ⟨(ms, name) :: ts, ?_, by simp [hmap]⟩
          unfold borrowTargetsAt at hts ⊢
          simp [List.mapM_cons, ha, hts]
        · rw [bind_ok] at h; obtain ⟨_, _, h, -⟩ := h; exact absurd h (reject_ne_ok _ _ _ _ _)

theorem translateBorrowCall_sim (hc : CallsAgree (N := N) m.program fs fuel)
    {env : Translate.Env} {sp : Span} {fn : FnInfo} {is : List Nat} {args : List Expr}
    {ctx ctx' : Ctx} {names : List String} {call : IR.Expr}
    (h : translateBorrowCall env sp fn is args ctx = .ok (names, call) ctx') :
    env.has fn.name = false ∧ ∃ ts outs,
      borrowTargetsAt args is = some ts ∧ names = ts.map (·.2) ∧ names.Nodup ∧
      call = .call fn.ref outs ∧ SimList (N := N) m fs fuel env args outs := by
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
  simp only [bind_ok] at h
  obtain ⟨tys, c, htys, h⟩ := h
  obtain ⟨ts, hts, hmap⟩ := borrowTargetTypes_ok htys
  simp only [ite_state] at h
  split at h
  rotate_left
  · simp at h
  rename_i hnd
  simp only [bind_ok, pure_ok] at h
  obtain ⟨outs, c', hargs, he, -⟩ := h
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  refine ⟨hname, ts, outs, hts, hmap, by simpa using hnd, rfl,
    translateBorrowArgs_sim m fs fuel hc _ _ _ _ _ hlen hargs⟩

theorem borrowCall?_some {env : Translate.Env} {e : Expr} {fn : FnInfo} {is : List Nat} {args : List Expr}
    (h : borrowCall? env e = some (fn, is, args)) :
    ∃ cs ns, e = .call cs (.ident ns fn.name) args ∧ fn ∈ env.functions ∧ fn.borrow = some is := by
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
