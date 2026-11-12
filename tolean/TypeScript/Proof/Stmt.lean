import tolean.TypeScript.Proof.LoopHead
import tolean.TypeScript.Spec.Lemmas.Eval

/-!
The translation of a statement list means what the statements mean.

`stmts_sound` states it for the statement functions of the translator, with
`StmtSim`. When the output body returns a value, the interpreter returns the
same value. When the output body ends, as the body of a branch or a loop
does, the interpreter ends too, and its environment agrees with the output's.

The interpreter keeps one environment and changes a variable in place, while
the output binds a new name for each change. So the proof tracks where the
interpreter's environment differs from the one it started with. A `Frame`
says that the names are the same and in the same places, and that only the
names the statements assign have new values. The bindings that a statement
list declares come in front, and the translator's `declare` makes sure that
none of them is a name already in scope.

Calls are still the hypothesis `CallsAgree`, as in `Proof/Expr.lean`.
-/
namespace tolean.TypeScript.Proof
open tolean.TypeScript tolean.TypeScript.Syntax tolean.TypeScript.Translate
open tolean.TypeScript.Eval (Val Outcome)

variable {N : Type}

/-! ### Frames -/

/-- `ρ'` has the names of `ρ` in the same places, and the same value for each
name outside `changes`. -/
def Frame (changes : List String) : Eval.Env N → Eval.Env N → Prop
  | [], [] => True
  | p :: ρ', q :: ρ => p.1 = q.1 ∧ (p.1 ∉ changes → p.2 = q.2) ∧ Frame changes ρ' ρ
  | _, _ => False

variable {c c₁ c₂ : List String}

theorem Frame.refl (c : List String) : ∀ ρ : Eval.Env N, Frame c ρ ρ
  | [] => trivial
  | _ :: ρ => ⟨rfl, fun _ => rfl, Frame.refl c ρ⟩

theorem Frame.length : ∀ {ρ' ρ : Eval.Env N}, Frame c ρ' ρ → ρ'.length = ρ.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, ⟨_, _, h⟩ => by simp [h.length]
  | [], _ :: _, h | _ :: _, [], h => h.elim

theorem Frame.mono (hc : ∀ n, n ∈ c → n ∈ c₁) : ∀ {ρ' ρ : Eval.Env N}, Frame c ρ' ρ → Frame c₁ ρ' ρ
  | [], [], _ => trivial
  | _ :: _, _ :: _, ⟨hk, hv, h⟩ => ⟨hk, fun hn => hv fun hn' => hn (hc _ hn'), h.mono hc⟩
  | [], _ :: _, h | _ :: _, [], h => h.elim

theorem Frame.trans : ∀ {ρ₂ ρ₁ ρ : Eval.Env N}, Frame c₂ ρ₂ ρ₁ → Frame c₁ ρ₁ ρ → Frame (c₁ ++ c₂) ρ₂ ρ
  | [], [], [], _, _ => trivial
  | _ :: _, _ :: _, _ :: _, ⟨hk, hv, h⟩, ⟨hk', hv', h'⟩ =>
    ⟨hk.trans hk', fun hn => by
      simp only [List.mem_append, not_or] at hn
      rw [hv hn.2, hv' (hk ▸ hn.1)], h.trans h'⟩
  | [], _ :: _, _, h, _ | _ :: _, [], _, h, _ => h.elim
  | [], [], _ :: _, _, h | _ :: _, _ :: _, [], _, h => h.elim

theorem Frame.lookup {n : String} (hn : n ∉ c) :
    ∀ {ρ' ρ : Eval.Env N}, Frame c ρ' ρ → ρ'.lookup n = ρ.lookup n
  | [], [], _ => rfl
  | (k, v) :: _, (k', v') :: _, ⟨hk, hv, h⟩ => by
    simp only at hk hv
    subst hk
    simp only [List.lookup]
    by_cases hnk : n = k
    · subst hnk; simp [hv hn]
    · have : (n == k) = false := by simpa using hnk
      simp [this, h.lookup hn]
  | [], _ :: _, h | _ :: _, [], h => h.elim

theorem Frame.isSome (n : String) :
    ∀ {ρ' ρ : Eval.Env N}, Frame c ρ' ρ → (ρ'.lookup n).isSome = (ρ.lookup n).isSome
  | [], [], _ => rfl
  | (k, v) :: _, (k', v') :: _, ⟨hk, _, h⟩ => by
    simp only at hk
    subst hk
    simp only [List.lookup]
    cases n == k <;> simp [h.isSome n]
  | [], _ :: _, h | _ :: _, [], h => h.elim

theorem Frame.set {n : String} {v : Val N} (hn : n ∈ c) : ∀ ρ : Eval.Env N, Frame c (ρ.set n v) ρ
  | [] => trivial
  | (k, w) :: ρ => by
    simp only [Eval.Env.set]
    split
    · rename_i hk
      have : k = n := by simpa using hk
      subst this
      exact ⟨rfl, fun h => absurd hn h, Frame.refl c ρ⟩
    · exact ⟨rfl, fun _ => rfl, Frame.set hn ρ⟩

theorem Frame.append : ∀ {a a' : Eval.Env N} {b b' : Eval.Env N},
    Frame c a a' → Frame c b b' → Frame c (a ++ b) (a' ++ b')
  | [], [], _, _, _, hb => hb
  | _ :: _, _ :: _, _, _, ⟨hk, hv, h⟩, hb => ⟨hk, hv, h.append hb⟩
  | [], _ :: _, _, _, h, _ | _ :: _, [], _, _, h, _ => h.elim

theorem Frame.mem {p : String × Val N} :
    ∀ {ρ' ρ : Eval.Env N}, Frame c ρ' ρ → p ∈ ρ' → ∃ q ∈ ρ, p.1 = q.1
  | _ :: _, q :: _, ⟨hk, _, h⟩, hp => by
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨q, List.mem_cons_self .., hk⟩
    · obtain ⟨q', hq', hk'⟩ := Frame.mem h hp
      exact ⟨q', List.mem_cons_of_mem _ hq', hk'⟩
  | [], _, _, hp => by simp at hp
  | _ :: _, [], h, _ => h.elim

theorem Frame.split : ∀ {ρ' a b : Eval.Env N}, Frame c ρ' (a ++ b) →
    ∃ ρ₁ ρ₂, ρ' = ρ₁ ++ ρ₂ ∧ Frame c ρ₁ a ∧ Frame c ρ₂ b
  | ρ', [], b, h => ⟨[], ρ', rfl, trivial, h⟩
  | p :: ρ', q :: a, b, ⟨hk, hv, h⟩ => by
    obtain ⟨ρ₁, ρ₂, rfl, h₁, h₂⟩ := Frame.split h
    exact ⟨p :: ρ₁, ρ₂, rfl, ⟨hk, hv, h₁⟩, h₂⟩
  | [], _ :: _, _, h => h.elim

/-! ### Environments -/

theorem bindState_lookup {inner : Eval.Env N} :
    ∀ {names : List String} {outer ρ : Eval.Env N}, IR.bindState names inner outer = some ρ →
      ∀ n, ρ.lookup n = if n ∈ names then inner.lookup n else outer.lookup n
  | [], outer, ρ, h, n => by
    simp [IR.bindState] at h; subst h; simp
  | k :: ks, outer, ρ, h, n => by
    simp only [IR.bindState, List.foldlM_cons] at h
    cases hk : inner.lookup k with
    | none => simp [hk] at h
    | some w =>
      simp only [hk] at h
      -- After `k`, a lookup of `k` gives `w`, and a lookup of another name
      -- gives what it gave in `outer`.
      have hmid : ∀ m, (if (outer.lookup k).isSome then Eval.Env.set outer k w else (k, w) :: outer).lookup m =
          if m = k then some w else outer.lookup m := by
        intro m
        split
        · next hs =>
          by_cases hm : m = k
          · subst hm; simp [Eval.Env.lookup_set_same _ _ _ hs]
          · simp [hm, Eval.Env.lookup_set_ne _ _ _ _ (Ne.symm hm)]
        · by_cases hm : m = k
          · subst hm; simp [List.lookup]
          · have : (m == k) = false := by simpa using hm
            simp [hm, this, List.lookup]
      have := bindState_lookup (names := ks) (by simpa [IR.bindState] using h) n
      rw [this, hmid]
      by_cases hn : n = k
      · subst hn; by_cases hm : n ∈ ks <;> simp [hm, hk]
      · by_cases hm : n ∈ ks <;> simp [hm, hn]

/-! ### The translator's state -/

section Monad

variable {α : Type}

@[simp] theorem modify_ok {f : Ctx → Ctx} {s s' : Ctx} {u : PUnit} :
    (modify f : TM PUnit) s = .ok u s' ↔ s' = f s := by
  simp [modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]
  exact eq_comm

@[simp] theorem throw_ne_ok {e : String} {s s' : Ctx} {a : α} : (throw e : TM α) s ≠ .ok a s' := by
  simp [throw, throwThe, MonadExceptOf.throw, EStateM.throw]

end Monad

/-! ### The statement -/

variable [JSNumber N]
variable (m : Eval.Scope) (fs : List (DeclRef × List String × IR.Body)) (fuel : Nat)

omit [JSNumber N] in
theorem scoped_frame {m : Eval.Scope} {env : Translate.Env} {ρ ρ' : Eval.Env N} {c : List String}
    (hs : Scoped m env ρ) (hf : Frame c ρ' ρ) : Scoped m env ρ' :=
  ⟨fun n => (hf.isSome n).trans (hs.1 n), hs.2⟩

omit [JSNumber N] in
theorem agree_set {ρs ρo : Eval.Env N} {n : String} {w : Val N} (ha : Agree ρs ρo)
    (hn : (ρs.lookup n).isSome) : Agree (ρs.set n w) ((n, w) :: ρo) := by
  intro x
  by_cases hx : x = n
  · subst hx; rw [Eval.Env.lookup_set_same _ _ _ hn]; simp
  · rw [Frame.lookup (c := [n]) (by simpa using hx) (Frame.set (by simp) ρs)]
    have : (x == n) = false := by simpa using hx
    simp [List.lookup, this, ha x]

theorem out_push {ρ : Eval.Env N} {name : String} {a : IR.Expr} {w : Val N}
    (h : IR.Expr.eval fs fuel ρ (.push name a) = some w) :
    ∃ xs va, ρ.lookup name = some (.list xs) ∧ IR.Expr.eval fs fuel ρ a = some va ∧
      w = .list (xs ++ [va]) := by
  simp only [IR.Expr.eval] at h
  cases hx : ρ.lookup name with
  | none => simp [hx] at h
  | some u =>
    cases u <;> simp [hx] at h
    rename_i xs
    cases hy : IR.Expr.eval fs fuel ρ a with
    | none => simp [hy] at h
    | some va => simp [hy] at h; exact ⟨xs, va, rfl, rfl, h.symm⟩

theorem out_update {ρ : Eval.Env N} {op : IR.IntOp} {name : String} {a : IR.Expr} {w : Val N}
    (h : IR.Expr.eval fs fuel ρ (.update op name a) = some w) :
    ∃ x y, ρ.lookup name = some (.int x) ∧ IR.Expr.eval fs fuel ρ a = some (.int y) ∧
      w = .int (op.apply x y) := by
  simp only [IR.Expr.eval] at h
  cases hx : ρ.lookup name with
  | none => simp [hx] at h
  | some u =>
    cases u <;> simp [hx] at h
    rename_i x
    cases hy : IR.Expr.eval fs fuel ρ a with
    | none => simp [hy] at h
    | some u => cases u <;> simp_all

/-- Writing out the type of a value does not change it. -/
theorem eval_withType (e : IR.Expr) (t source : Ty) (ρ : Eval.Env N) :
    IR.Expr.eval fs fuel ρ (withType e t source) = IR.Expr.eval fs fuel ρ e := by
  unfold withType
  cases e <;> (try simp only) <;> (try split) <;> simp [IR.Expr.eval]

omit [JSNumber N] in
/-- Setting a name to the value it has leaves the environment as it is. -/
theorem env_set_self {n : String} {v : Val N} : ∀ {ρ : Eval.Env N}, ρ.lookup n = some v → ρ.set n v = ρ
  | [], h => by simp [List.lookup] at h
  | (k, w) :: rest, h => by
    rw [Eval.Env.lookup_cons] at h
    rw [Eval.Env.set_cons]
    by_cases hk : k = n
    · subst hk; simp at h; simp [h]
    · rw [if_neg (Ne.symm hk)] at h
      simp only [hk, ↓reduceIte]
      rw [env_set_self h]

/-- An update statement sets a name in scope to the value of the output's
update. -/
theorem update_sound (hc : CallsAgree (N := N) m.program fs fuel) {env : Translate.Env} {sp : Span} {e : Expr}
    {ctx ctx' : Ctx} {name : String} {upd : IR.Expr}
    (h : translateUpdate env sp e ctx = .ok (name, upd) ctx')
    {ρs ρo : Eval.Env N} (ha : Agree ρs ρo) (hs : Scoped m env ρs) {w : Val N}
    (hw : IR.Expr.eval fs fuel ρo upd = some w) :
    env.has name = true ∧ name ∈ exprChanges env.fnChanges e ∧
      Eval.execStmt m fuel ρs (.exprStmt sp e) = some (.normal (ρs.set name w)) := by
  unfold translateUpdate at h
  cases e <;> (try simp only at h) <;> try (simp at h; done)
  case call sp' callee args =>
    cases callee <;> (try simp only at h) <;> try (simp at h; done)
    rename_i sp1 obj field
    cases obj <;> (try simp only at h) <;> try (simp at h; done)
    rename_i sp2 target
    by_cases hf : field = "push"
    · subst hf
      simp only at h
      cases hl : env.lookup target with
      | none => simp [hl] at h
      | some loc =>
        obtain ⟨lname, lb, lt⟩ := loc
        cases lb <;> cases lt <;> simp [hl] at h
        rename_i elemType
        rcases args with _ | ⟨element, _ | ⟨a2, more⟩⟩ <;> simp at h
        obtain ⟨_, _, ⟨rfl, rfl⟩, a, s₃, ha', h⟩ := h
        split at h
        · simp at h
          obtain ⟨⟨rfl, rfl⟩, -⟩ := h
          have hsim := (expr_sound m fs fuel hc _).1 _ _ _ _ _ _ ha'
          obtain ⟨xs, va, hx, hva, rfl⟩ := out_push fs fuel hw
          rw [eval_value] at hva
          rw [← ha target] at hx
          refine ⟨by simp [Env.has, hl], by simp [exprChanges, calleeChanges], ?_⟩
          simp [Eval.execStmt, hx, hsim ρs ρo va ha hs hva]
        · simp at h
    by_cases hset : field = "set"
    · -- `m.set(k, v)` on an owned map: the map with the entry.
      subst hset
      simp only at h
      cases hl : env.lookup target with
      | none => simp [hl] at h
      | some loc =>
        obtain ⟨lname, lb, lt⟩ := loc
        cases lb <;> cases lt <;> simp [hl] at h
        rename_i k v
        rcases args with _ | ⟨key, _ | ⟨value, _ | ⟨a3, more⟩⟩⟩ <;> simp at h
        obtain ⟨_, _, ⟨rfl, rfl⟩, kc, s₃, hkc, h⟩ := h
        split at h
        · simp at h
          obtain ⟨_, _, ⟨rfl, rfl⟩, vc, s₄, hvc, h⟩ := h
          split at h
          · simp at h
            obtain ⟨⟨rfl, rfl⟩, -⟩ := h
            have hk := (expr_sound m fs fuel hc _).1 _ _ _ _ _ _ hkc
            have hv := (expr_sound m fs fuel hc _).1 _ _ _ _ _ _ hvc
            obtain ⟨vs, hvs, happ⟩ := out_ext fs fuel hw
            simp only [IR.Expr.evalList, IR.Expr.eval] at hvs
            cases hx : ρo.lookup target with
            | none => simp [hx] at hvs
            | some vm =>
              cases hy : IR.Expr.eval fs fuel ρo kc.value with
              | none => simp [hx, hy] at hvs
              | some vk =>
                cases hz : IR.Expr.eval fs fuel ρo vc.value with
                | none => simp [hx, hy, hz] at hvs
                | some vv =>
                  simp [hx, hy, hz] at hvs
                  subst hvs
                  rw [eval_value] at hy hz
                  cases vm <;> simp [IR.ExprExt.apply] at happ
                  obtain ⟨es', hes, rfl⟩ := happ
                  rw [← ha target] at hx
                  refine ⟨by simp [Env.has, hl], by simp [exprChanges, calleeChanges], ?_⟩
                  simp [Eval.execStmt, hx, hk ρs ρo vk ha hs hy, hv ρs ρo vv ha hs hz, hes]
          · simp at h
        · simp at h
    by_cases hdel : field = "delete"
    · -- `m.delete(k)` on an owned map, or `s.delete(x)` on an owned set.
      subst hdel
      simp only at h
      cases hl : env.lookup target with
      | none => simp [hl] at h
      | some loc =>
        obtain ⟨lname, lb, lt⟩ := loc
        cases lb <;> cases lt <;> simp [hl] at h
        next k v =>
          rcases args with _ | ⟨key, _ | ⟨a2, more⟩⟩ <;> simp at h
          obtain ⟨_, _, ⟨rfl, rfl⟩, kc, s₃, hkc, h⟩ := h
          split at h
          · simp at h
            obtain ⟨⟨rfl, rfl⟩, -⟩ := h
            have hk := (expr_sound m fs fuel hc _).1 _ _ _ _ _ _ hkc
            obtain ⟨vs, hvs, happ⟩ := out_ext fs fuel hw
            simp only [IR.Expr.evalList, IR.Expr.eval] at hvs
            cases hx : ρo.lookup target with
            | none => simp [hx] at hvs
            | some vm =>
              cases hy : IR.Expr.eval fs fuel ρo kc.value with
              | none => simp [hx, hy] at hvs
              | some vk =>
                simp [hx, hy] at hvs
                subst hvs
                rw [eval_value] at hy
                cases vm <;> simp [IR.ExprExt.apply] at happ
                obtain ⟨es', hes, rfl⟩ := happ
                rw [← ha target] at hx
                refine ⟨by simp [Env.has, hl], by simp [exprChanges, calleeChanges], ?_⟩
                simp [Eval.execStmt, hx, hk ρs ρo vk ha hs hy, hes]
          · simp at h
        next t =>
          rcases args with _ | ⟨key, _ | ⟨a2, more⟩⟩ <;> simp at h
          obtain ⟨_, _, ⟨rfl, rfl⟩, kc, s₃, hkc, h⟩ := h
          split at h
          · simp at h
            obtain ⟨⟨rfl, rfl⟩, -⟩ := h
            have hk := (expr_sound m fs fuel hc _).1 _ _ _ _ _ _ hkc
            obtain ⟨vs, hvs, happ⟩ := out_ext fs fuel hw
            simp only [IR.Expr.evalList, IR.Expr.eval] at hvs
            cases hx : ρo.lookup target with
            | none => simp [hx] at hvs
            | some vm =>
              cases hy : IR.Expr.eval fs fuel ρo kc.value with
              | none => simp [hx, hy] at hvs
              | some vk =>
                simp [hx, hy] at hvs
                subst hvs
                rw [eval_value] at hy
                cases vm <;> simp [IR.ExprExt.apply] at happ
                obtain ⟨es', hes, rfl⟩ := happ
                rw [← ha target] at hx
                refine ⟨by simp [Env.has, hl], by simp [exprChanges, calleeChanges], ?_⟩
                simp [Eval.execStmt, hx, hk ρs ρo vk ha hs hy, hes]
          · simp at h
    by_cases hadd : field = "add"
    · -- `s.add(x)` on an owned set: the set with `x`.
      subst hadd
      simp only at h
      cases hl : env.lookup target with
      | none => simp [hl] at h
      | some loc =>
        obtain ⟨lname, lb, lt⟩ := loc
        cases lb <;> cases lt <;> simp [hl] at h
        rename_i t
        rcases args with _ | ⟨key, _ | ⟨a2, more⟩⟩ <;> simp at h
        obtain ⟨_, _, ⟨rfl, rfl⟩, kc, s₃, hkc, h⟩ := h
        split at h
        · simp at h
          obtain ⟨⟨rfl, rfl⟩, -⟩ := h
          have hk := (expr_sound m fs fuel hc _).1 _ _ _ _ _ _ hkc
          obtain ⟨vs, hvs, happ⟩ := out_ext fs fuel hw
          simp only [IR.Expr.evalList, IR.Expr.eval] at hvs
          cases hx : ρo.lookup target with
          | none => simp [hx] at hvs
          | some vm =>
            cases hy : IR.Expr.eval fs fuel ρo kc.value with
            | none => simp [hx, hy] at hvs
            | some vk =>
              simp [hx, hy] at hvs
              subst hvs
              rw [eval_value] at hy
              cases vm <;> simp [IR.ExprExt.apply] at happ
              obtain ⟨es', hes, rfl⟩ := happ
              rw [← ha target] at hx
              refine ⟨by simp [Env.has, hl], by simp [exprChanges, calleeChanges], ?_⟩
              simp [Eval.execStmt, hx, hk ρs ρo vk ha hs hy, hes]
        · simp at h
    · simp [hf, hset, hdel, hadd] at h
  case assign sp' op target right =>
    cases target <;> (try simp only at h) <;> try (simp at h; done)
    rename_i sp1 x
    simp only [ite_state] at h
    split at h
    · -- `x ??= e`: `x` unless it is `null`, and then `e`.
      rename_i hco
      obtain rfl : op = .coalesce := by cases op <;> first | rfl | exact absurd hco (by decide)
      cases hl : env.lookup x with
      | none => simp [hl] at h
      | some loc =>
        obtain ⟨lname, lb, lt⟩ := loc
        cases lb <;> cases lt <;> simp [hl] at h
        rename_i value
        obtain ⟨v, s₂, hv, h⟩ := h
        obtain ⟨rfl, rfl⟩ := hv
        obtain ⟨a, s₃, ha', h⟩ := h
        split at h
        · simp at h
          obtain ⟨⟨rfl, rfl⟩, -⟩ := h
          have hsim := (expr_sound m fs fuel hc _).1 _ _ _ _ _ _ ha'
          have hhas : env.has x = true := by simp [Env.has, hl]
          refine ⟨hhas, by simp [exprChanges, show (AssignOp.coalesce == AssignOp.coalesce) = true from rfl], ?_⟩
          obtain ⟨u, hu, hcase⟩ := out_coalesce fs fuel hw
          simp only [IR.Expr.eval] at hu
          rw [← ha x] at hu
          rcases hcase with ⟨hnu, hbv⟩ | ⟨hn, hnu, rfl⟩
          · rw [eval_value] at hbv
            rcases hnu with rfl | rfl <;> simp [Eval.execStmt, hu, hsim ρs ρo w ha hs hbv]
          · cases w <;> simp_all [Eval.execStmt, isNullVal, env_set_self]
        · simp at h
    · split at h
      · rename_i hsimple
        cases hl : env.lookup x with
        | none => simp [hl] at h
        | some loc =>
          obtain ⟨lname, lb, lt⟩ := loc
          cases lb <;> simp [hl] at h
          obtain ⟨v, s₂, hv, h⟩ := h
          obtain ⟨rfl, rfl⟩ := hv
          obtain ⟨a, s₃, ha', h⟩ := h
          have hsim := (expr_sound m fs fuel hc _).1 _ _ _ _ _ _ ha'
          have hhas : env.has x = true := by simp [Env.has, hl]
          cases op <;> simp [AssignOp.isSimple] at hsimple <;> simp only [assignOps?, ite_state] at h
          all_goals (repeat' split at h) <;> simp at h
          -- Only `+=` joins strings.
          all_goals try (obtain ⟨-, hop⟩ := ‹((_ : Ty) == _) = true ∧ ((_ : IR.IntOp) == _) = true›
                         exact absurd hop (by decide))
          -- `s += e` on a string.
          case ident.isFalse.isTrue.some.let.add.isFalse.isTrue =>
              (obtain ⟨c, hcat, rfl, rfl⟩ := h
               obtain ⟨left, right, hp, rfl⟩ := concatOperands_ok hcat
               have hw' : IR.Expr.eval fs fuel ρo
                   (.ext (.stringAppend left right) [.var x, a.value]) = some w := hw
               refine ⟨hhas, by simp [exprChanges, AssignOp.isSimple], ?_⟩
               obtain ⟨p, q, sp, sq, hp', hq, hsp, hsq, rfl⟩ := out_stringAppend fs fuel hw'
               simp only [IR.Expr.eval] at hp'
               rw [eval_value] at hq
               rw [← ha x] at hp'
               simp [Eval.execStmt, hp', hsim ρs ρo _ ha hs hq, concatParts?_binary hp hsp hsq])
          all_goals obtain ⟨⟨rfl, rfl⟩, -⟩ := h
          all_goals refine ⟨hhas, by simp [exprChanges, AssignOp.isSimple], ?_⟩
          · rw [eval_withType, eval_value] at hw
            simp [Eval.execStmt, hsim ρs ρo w ha hs hw]
          all_goals first
            | (obtain ⟨p, q, hp, hq, rfl⟩ := out_numberOp fs fuel hw
               simp only [IR.Expr.eval] at hp
               rw [eval_value] at hq
               rw [← ha x] at hp
               simp [Eval.execStmt, hp, hsim ρs ρo _ ha hs hq, Eval.binary, IR.NumberOp.apply])
            | (obtain ⟨p, q, hp, hq, rfl⟩ := out_update fs fuel hw
               rw [eval_value] at hq
               rw [← ha x] at hp
               simp [Eval.execStmt, hp, hsim ρs ρo _ ha hs hq, Eval.binary, IR.IntOp.apply])
      · simp at h

/-- How an output body ends without a return: in the state of a branch or of
a loop body, or, when `brk`, in a `break`. -/
def endOf : Bool → Eval.Env N → Outcome N
  | false, ρ => .normal ρ
  | true, ρ => .brk ρ

/-- How statements that end in `tail` end, when they do not return: `r` is
their outcome, with the variables `e`. When the output ends in a `break`
(`brk`), they end in one. Otherwise a branch runs to its end, a branch that
must reach a `continue` or a `break` ends in a `continue`, and a loop body
runs to its end or to a `continue`. -/
def Ends : Tail → Bool → Option (Outcome N) → Eval.Env N → Prop
  | .ret, _, _, _ => False
  | _, true, r, e => r = some (.brk e)
  | .state _, false, r, e => r = some (.normal e)
  | .loop .., false, r, e => r = some (.normal e) ∨ r = some (.cont e)
  | .cont .., false, r, e => r = some (.cont e)

/-- The output body `body` means what the statements `ss` mean. A return gives
the same value. An end, which only a body for a branch or a loop has, gives
environments that agree on the old names: each side has new bindings, which
`env` does not have, in front of them, and the interpreter changes only the
names that `ss` change. The interpreter ends as `Ends` says, which tells a `break` from
the other ends.

The two sides' new bindings can differ. A `continue` in a block drops the
block's locals from the interpreter's environment, while the output's step
of the loop still has them until it returns its state. -/
def StmtSim (env : Translate.Env) (tail : Tail) (ss : List Stmt) (body : IR.Body) : Prop :=
  ∀ (ρs ρo : Eval.Env N), Agree ρs ρo → Scoped m env ρs →
    (∀ v, IR.Body.exec fs fuel ρo body = some (.ret v) → Eval.exec m fuel ρs ss = some (.ret v)) ∧
    (∀ brk ρo', IR.Body.exec fs fuel ρo body = some (endOf brk ρo') →
      tail.isRet = false ∧ ∃ new out mod, Ends tail brk (Eval.exec m fuel ρs ss) (new ++ mod) ∧
        Agree (out ++ mod) ρo' ∧ (∀ p ∈ new, env.has p.1 = false) ∧
        (∀ p ∈ out, env.has p.1 = false) ∧ Frame (stmtsChanges env.fnChanges ss) mod ρs)

omit [JSNumber N] in
theorem Ends.congr {tail : Tail} {brk : Bool} {r r' : Option (Outcome N)} {e : Eval.Env N} (h : r = r') :
    Ends tail brk r e → Ends tail brk r' e := fun he => h ▸ he

omit [JSNumber N] in
theorem Ends.brk {tail : Tail} {r : Option (Outcome N)} {e : Eval.Env N} (h : Ends tail true r e) :
    r = some (.brk e) := by
  cases tail <;> first | exact h | exact h.elim

omit [JSNumber N] in
theorem Ends.of_brk {tail : Tail} (h : tail.isRet = false) (e : Eval.Env N) :
    Ends tail true (some (.brk e)) e := by
  cases tail <;> simp_all [Tail.isRet, Ends]

omit [JSNumber N] in
theorem endOf_normal {brk : Bool} {ρ ρ' : Eval.Env N} (h : some (Outcome.normal ρ) = some (endOf brk ρ')) :
    brk = false ∧ ρ' = ρ := by
  cases brk <;> simp_all [endOf]

/-- The end of one run of a loop body gives its state as it is. -/
theorem exec_stepEnd (names : List String) (b r : Bool) (ρ : Eval.Env N) :
    IR.Body.exec fs fuel ρ (stepEnd names b r) = some (.normal ρ) := by
  cases b <;> simp [stepEnd, IR.Body.exec]

/-! ### The interpreter on statements -/

theorem exec_single (t : Stmt) (ρ : Eval.Env N) : Eval.exec m fuel ρ [t] = Eval.execStmt m fuel ρ t := by
  simp only [Eval.exec, Stmt.constAssignedIn_nil, Bool.false_eq_true, ↓reduceIte, pure_bind]
  cases h : Eval.execStmt m fuel ρ t with
  | none => rfl
  | some o => cases o <;> simp

omit [JSNumber N] in
theorem blockStatements_eq (t : Stmt) :
    blockStatements t = [t] ∨ ∃ sp body, t = .block sp body ∧ blockStatements t = body := by
  cases t <;> simp [blockStatements]

theorem execStmt_block (sp : Span) (body : List Stmt) (ρ : Eval.Env N) :
    Eval.execStmt m fuel ρ (.block sp body) = (do
      match ← Eval.exec m fuel ρ body with
      | .ret v => some (.ret v)
      | .normal ρ' => some (.normal (ρ'.drop (ρ'.length - ρ.length)))
      | .brk ρ' => some (.brk (ρ'.drop (ρ'.length - ρ.length)))
      | .cont ρ' => some (.cont (ρ'.drop (ρ'.length - ρ.length)))) := by
  rw [Eval.execStmt]; rfl

theorem block_ret (t : Stmt) {ρ : Eval.Env N} {v : Except (Val N) (Val N)}
    (h : Eval.exec m fuel ρ (blockStatements t) = some (.ret v)) :
    Eval.execStmt m fuel ρ t = some (.ret v) := by
  rcases blockStatements_eq t with h1 | ⟨sp, body, rfl, h1⟩
  · rwa [h1, exec_single] at h
  · rw [h1] at h
    rw [execStmt_block, h]
    rfl

theorem block_normal (t : Stmt) {ρ new mod : Eval.Env N} {c : List String}
    (h : Eval.exec m fuel ρ (blockStatements t) = some (.normal (new ++ mod))) (hf : Frame c mod ρ) :
    ∃ e, Eval.execStmt m fuel ρ t = some (.normal e) ∧ e.drop (e.length - ρ.length) = mod ∧
      ρ.length ≤ e.length := by
  have hlen := hf.length
  rcases blockStatements_eq t with h1 | ⟨sp, body, rfl, h1⟩
  · rw [h1, exec_single] at h
    refine ⟨new ++ mod, h, ?_, by simp [hlen]⟩
    have : (new ++ mod).length - ρ.length = new.length := by simp [hlen]
    rw [this, List.drop_left]
  · rw [h1] at h
    have : (new ++ mod).length - ρ.length = new.length := by simp [hlen]
    refine ⟨mod, by rw [execStmt_block, h]; simp [hlen], by simp [hlen], by simp [hlen]⟩

theorem execStmt_if (sp : Span) (test : Expr) (t : Stmt) (e : Option Stmt) (ρ : Eval.Env N) :
    Eval.execStmt m fuel ρ (.ifStmt sp test t e) = (do
      let out ← if (← Eval.eval m fuel ρ test).truthy then Eval.execStmt m fuel ρ t
        else match e with
          | some f => Eval.execStmt m fuel ρ f
          | none => some (.normal ρ)
      match out with
      | .ret v => some (.ret v)
      | .normal ρ' => some (.normal (ρ'.drop (ρ'.length - ρ.length)))
      | .brk ρ' => some (.brk (ρ'.drop (ρ'.length - ρ.length)))
      | .cont ρ' => some (.cont (ρ'.drop (ρ'.length - ρ.length)))) := by
  rw [Eval.execStmt]; rfl

/-- The statements of the branch that the test picks. -/
def branchStatements (w : Val N) (t : Stmt) (e : Option Stmt) : List Stmt :=
  if w.truthy then blockStatements t else (e.map blockStatements).getD []

theorem if_ret {sp : Span} {test : Expr} {t : Stmt} {e : Option Stmt} {ρ : Eval.Env N} {w : Val N}
    {v : Except (Val N) (Val N)}
    (hw : Eval.eval m fuel ρ test = some w)
    (hex : Eval.exec m fuel ρ (branchStatements w t e) = some (.ret v)) :
    Eval.execStmt m fuel ρ (.ifStmt sp test t e) = some (.ret v) := by
  rw [execStmt_if, hw]
  unfold branchStatements at hex
  cases htr : w.truthy <;>
    simp only [htr, Bool.false_eq_true, ↓reduceIte, Option.bind_eq_bind, Option.bind_some] at hex ⊢
  · cases e with
    | none => simp [Eval.exec] at hex
    | some f => simp [block_ret m fuel f hex]
  · simp [block_ret m fuel t hex]

theorem if_normal {sp : Span} {test : Expr} {t : Stmt} {e : Option Stmt} {ρ new mod : Eval.Env N}
    {w : Val N} {c : List String} (hw : Eval.eval m fuel ρ test = some w)
    (hex : Eval.exec m fuel ρ (branchStatements w t e) = some (.normal (new ++ mod)))
    (hf : Frame c mod ρ) :
    Eval.execStmt m fuel ρ (.ifStmt sp test t e) = some (.normal mod) := by
  rw [execStmt_if, hw]
  unfold branchStatements at hex
  have hlen := hf.length
  cases htr : w.truthy <;>
    simp only [htr, Bool.false_eq_true, ↓reduceIte, Option.bind_eq_bind, Option.bind_some] at hex ⊢
  · cases e with
    | none =>
      simp only [Option.map_none, Option.getD_none, Eval.exec, Option.some.injEq,
        Outcome.normal.injEq] at hex
      have hl : new.length = 0 := by
        have := congrArg List.length hex
        simp only [List.length_append] at this
        omega
      rw [List.length_eq_zero_iff] at hl
      subst hl
      simp only [List.nil_append] at hex
      subst hex
      simp
    | some f =>
      obtain ⟨e', h1, h2, -⟩ := block_normal m fuel f hex hf
      simp [h1, h2]
  · obtain ⟨e', h1, h2, -⟩ := block_normal m fuel t hex hf
    simp [h1, h2]

/-- A block that ends in a `continue` or a `break` ends in it, without the
bindings it declares. -/
theorem block_jump (t : Stmt) {ρ new mod : Eval.Env N} {c : List String} {k : Eval.Env N → Outcome N}
    (hk : k = .cont ∨ k = .brk)
    (h : Eval.exec m fuel ρ (blockStatements t) = some (k (new ++ mod))) (hf : Frame c mod ρ) :
    ∃ e, Eval.execStmt m fuel ρ t = some (k e) ∧ e.drop (e.length - ρ.length) = mod ∧
      ρ.length ≤ e.length := by
  have hlen := hf.length
  rcases hk with rfl | rfl
  all_goals
    rcases blockStatements_eq t with h1 | ⟨sp, body, rfl, h1⟩
    · rw [h1, exec_single] at h
      refine ⟨new ++ mod, h, ?_, by simp [hlen]⟩
      have : (new ++ mod).length - ρ.length = new.length := by simp [hlen]
      rw [this, List.drop_left]
    · rw [h1] at h
      refine ⟨mod, by rw [execStmt_block, h]; simp [hlen], by simp [hlen], by simp [hlen]⟩

/-- A branch that ends in a `continue` or a `break` ends its `if` in it. -/
theorem if_jump {sp : Span} {test : Expr} {t : Stmt} {e : Option Stmt} {ρ new mod : Eval.Env N}
    {w : Val N} {c : List String} {k : Eval.Env N → Outcome N} (hk : k = .cont ∨ k = .brk)
    (hw : Eval.eval m fuel ρ test = some w)
    (hex : Eval.exec m fuel ρ (branchStatements w t e) = some (k (new ++ mod)))
    (hf : Frame c mod ρ) :
    Eval.execStmt m fuel ρ (.ifStmt sp test t e) = some (k mod) := by
  rw [execStmt_if, hw]
  unfold branchStatements at hex
  cases htr : w.truthy <;>
    simp only [htr, Bool.false_eq_true, ↓reduceIte, Option.bind_eq_bind, Option.bind_some] at hex ⊢
  · cases e with
    | none => rcases hk with rfl | rfl <;> simp [Eval.exec] at hex
    | some f =>
      obtain ⟨e', h1, h2, -⟩ := block_jump m fuel f hk hex hf
      rcases hk with rfl | rfl <;> simp [h1, h2]
  · obtain ⟨e', h1, h2, -⟩ := block_jump m fuel t hk hex hf
    rcases hk with rfl | rfl <;> simp [h1, h2]

/-- A branch ends its `if` as `Ends` says, without the bindings it declares. -/
theorem if_ends {tail : Tail} {brk : Bool} {sp : Span} {test : Expr} {t : Stmt} {e : Option Stmt}
    {ρ new mod : Eval.Env N} {w : Val N} {c : List String} (hw : Eval.eval m fuel ρ test = some w)
    (hex : Ends tail brk (Eval.exec m fuel ρ (branchStatements w t e)) (new ++ mod)) (hf : Frame c mod ρ) :
    Ends tail brk (Eval.execStmt m fuel ρ (.ifStmt sp test t e)) mod := by
  cases brk
  · cases tail with
    | ret => exact hex.elim
    | state _ => exact if_normal m fuel hw hex hf
    | loop _ _ _ =>
      rcases hex with hex | hex
      · exact .inl (if_normal m fuel hw hex hf)
      · exact .inr (if_jump m fuel (.inl rfl) hw hex hf)
    | cont _ _ _ => exact if_jump m fuel (.inl rfl) hw hex hf
  · cases tail with
    | ret => exact hex.elim
    | _ => exact if_jump m fuel (.inr rfl) hw hex.brk hf

omit [JSNumber N] in
theorem stmtsChanges_append (fns : List (String × List String)) (a b : List Stmt) :
    stmtsChanges fns (a ++ b) = stmtsChanges fns a ++ stmtsChanges fns b := by
  induction a with
  | nil => simp [stmtsChanges]
  | cons s rest ih => simp [stmtsChanges, ih]

omit [JSNumber N] in
theorem stmtsChanges_block (fns : List (String × List String)) (t : Stmt) :
    stmtsChanges fns (blockStatements t) = stmtChanges fns t := by
  cases t <;> simp [blockStatements, stmtsChanges, stmtChanges]

omit [JSNumber N] in
theorem mem_changedNames {ss : List Stmt} {env : Translate.Env} {n : String} :
    n ∈ changedNames ss env ↔ env.has n = true ∧ n ∈ stmtsChanges env.fnChanges ss := by
  simp only [changedNames, List.mem_map, List.mem_filter, Env.has, Env.lookup, List.find?_isSome,
    List.contains_iff_mem, beq_iff_eq]
  constructor
  · rintro ⟨l, ⟨hl, hc⟩, rfl⟩; exact ⟨⟨l, hl, rfl⟩, hc⟩
  · rintro ⟨⟨l, hl, rfl⟩, hc⟩; exact ⟨l, ⟨hl, hc⟩, rfl⟩

/-- A declaration, whose output binds `d.name` to the value of the
initializer, means what the source means, when the rest does. -/
theorem decl_sim {env env' : Translate.Env} {s : Span} {d : VarDecl} {init : Expr} {rest : List Stmt}
    {tail : Tail} {body rb : IR.Body} {b : Binding} {ty : Ty}
    (hinit : d.init = some init) (hconst : (Stmt.varDecl s d).constAssignedIn rest = false)
    (hfresh : env.has d.name = false)
    (henv : env' = env.add { name := d.name, binding := b, type := ty })
    (hbody : ∀ (ρo : Eval.Env N) (o : Outcome N), IR.Body.exec fs fuel ρo body = some o → ∃ w,
      (∀ ρs, Agree ρs ρo → Scoped m env ρs → Eval.eval m fuel ρs init = some w) ∧
        IR.Body.exec fs fuel ((d.name, w) :: ρo) rb = some o)
    (hrest : StmtSim (N := N) m fs fuel env' tail rest rb) :
    StmtSim (N := N) m fs fuel env tail (.varDecl s d :: rest) body := by
  subst henv
  obtain ⟨kind, name, type, init?⟩ := d
  simp only at hinit hfresh hbody ⊢
  subst hinit
  intro ρs ρo ha hs
  have ha' : ∀ w, Agree ((name, w) :: ρs) ((name, w) :: ρo) := fun w x => by
    simp only [List.lookup]; split
    · rfl
    · exact ha x
  have hs' : ∀ w, Scoped m (env.add { name, binding := b, type := ty }) ((name, w) :: ρs) :=
    fun w => ⟨fun x => by
    rw [has_add, ← hs.1 x]
    simp only [List.lookup]
    by_cases hx : x = name
    · subst hx; simp
    · have h1 : (x == name) = false := by simpa using hx
      have h2 : (name == x) = false := by simpa using Ne.symm hx
      simp [h1, h2], hs.2⟩
  have hstep : ∀ w, Eval.eval m fuel ρs init = some w →
      Eval.exec m fuel ρs (.varDecl s { kind, name, type, init := some init } :: rest) =
        Eval.exec m fuel ((name, w) :: ρs) rest := by
    intro w hw
    simp [Eval.exec, Eval.execStmt, evalTop_ok m fuel hw, hconst]
  constructor
  · intro v hv
    obtain ⟨w, hw, hb⟩ := hbody ρo _ hv
    rw [hstep w (hw ρs ha hs)]
    exact ((hrest _ _ (ha' w) (hs' w)).1 v hb)
  · intro brk ρo' hv
    obtain ⟨w, hw, hb⟩ := hbody ρo _ hv
    obtain ⟨htail, new, out, mod, hex, hag, hnew, hout, hfr⟩ := (hrest _ _ (ha' w) (hs' w)).2 brk ρo' hb
    obtain ⟨ρ₁, ρ₂, rfl, h₁, h₂⟩ := Frame.split (a := [(name, w)]) (b := ρs) hfr
    -- The new bindings of either side, and the declared name, are not in `env`.
    have hfr₁ : ∀ l : Eval.Env N,
        (∀ p ∈ l, (env.add { name, binding := b, type := ty }).has p.1 = false) →
        ∀ p ∈ l ++ ρ₁, env.has p.1 = false := by
      intro l hl p hp
      rcases List.mem_append.mp hp with hp | hp
      · have := hl p hp
        rw [has_add] at this
        simp only [Bool.or_eq_false_iff] at this
        exact this.1
      · obtain ⟨q, hq, hk⟩ := Frame.mem h₁ hp
        simp only [List.mem_singleton] at hq
        subst hq
        rw [hk]; exact hfresh
    refine ⟨htail, new ++ ρ₁, out ++ ρ₁, ρ₂, ?_, ?_, hfr₁ new hnew, hfr₁ out hout, ?_⟩
    · rw [hstep w (hw ρs ha hs), List.append_assoc]; exact hex
    · rwa [List.append_assoc]
    · exact h₂.mono fun n hn => by simp only [Env.fnChanges_add] at hn; simp [stmtsChanges, hn]

omit [JSNumber N] in
theorem lookup_append_fresh {n : String} :
    ∀ {new : Eval.Env N} (mod : Eval.Env N), (∀ p ∈ new, p.1 ≠ n) → (new ++ mod).lookup n = mod.lookup n
  | [], _, _ => rfl
  | (k, v) :: new, mod, h => by
    have hk : (n == k) = false := by simpa using Ne.symm (h (k, v) (List.mem_cons_self ..))
    simp only [List.cons_append, List.lookup, hk]
    exact lookup_append_fresh mod fun p hp => h p (List.mem_cons_of_mem _ hp)

/-- The output `br` runs `whenTrue` when the interpreter's test is truthy, and
`whenFalse` when it is not. -/
def BranchSim (env : Translate.Env) (test : Expr) (br whenTrue whenFalse : IR.Body) : Prop :=
  ∀ (ρs ρo : Eval.Env N) (o : Outcome N), Agree ρs ρo → Scoped m env ρs →
    IR.Body.exec fs fuel ρo br = some o →
    ∃ w, Eval.eval m fuel ρs test = some w ∧
      IR.Body.exec fs fuel ρo (if w.truthy then whenTrue else whenFalse) = some o

omit [JSNumber N] in
/-- The first branch of an `if` that `earlyTail` picks ends the statements:
in a `return`, or in a `continue` where they are a loop body. -/
theorem earlyTail_ends {tail thenTail : Tail} {ss : List Stmt} (h : earlyTail tail ss = some thenTail) :
    (thenTail.isRet = false → tail.isRet = false) ∧
      ∀ (r : Option (Outcome N)) e, Ends thenTail false r e → r = some (.cont e) ∧ tail.isRet = false ∧
        ∀ e', Ends (N := N) tail false (some (.cont e')) e' := by
  cases tail with
  | ret =>
    simp only [earlyTail] at h
    split at h <;> cases h
    exact ⟨fun h => absurd h (by simp [Tail.isRet]), fun _ _ he => he.elim⟩
  | state _ => simp [earlyTail] at h
  | loop _ _ _ | cont _ _ _ =>
    simp only [earlyTail] at h
    split at h <;> cases h
    exact ⟨fun _ => rfl, fun _ _ he => ⟨he, rfl, fun e' => by simp [Ends]⟩⟩

/-- An `if` whose first branch ends the statements on every path, in a
`return` or in a `continue`: the statements after the `if` join its other
branch. -/
theorem if_early_sim {env envT envF : Translate.Env} {sp : Span} {test : Expr} {t : Stmt}
    {e : Option Stmt} {rest : List Stmt} {tail thenTail : Tail} {br wt wf : IR.Body}
    (hT : ∀ x, envT.has x = env.has x) (hF : ∀ x, envF.has x = env.has x)
    (hTf : globals envT = globals env) (hFf : globals envF = globals env)
    (htail : (thenTail.isRet = false → tail.isRet = false) ∧
      ∀ (r : Option (Outcome N)) e, Ends thenTail false r e → r = some (.cont e) ∧ tail.isRet = false ∧
        ∀ e', Ends (N := N) tail false (some (.cont e')) e')
    (hrest : e.isSome = true → rest = [])
    (hbr : BranchSim (N := N) m fs fuel env test br wt wf)
    (hwt : StmtSim (N := N) m fs fuel envT thenTail (blockStatements t) wt)
    (hwf : StmtSim (N := N) m fs fuel envF tail ((e.map blockStatements).getD [] ++ rest) wf) :
    StmtSim (N := N) m fs fuel env tail (.ifStmt sp test t e :: rest) br := by
  simp only [StmtSim, fnChanges_congr hTf] at hwt
  simp only [StmtSim, fnChanges_congr hFf] at hwf
  intro ρs ρo ha hs
  have hsT : Scoped m envT ρs := ⟨fun x => (hs.1 x).trans (hT x).symm, hs.2.congr hTf⟩
  have hsF : Scoped m envF ρs := ⟨fun x => (hs.1 x).trans (hF x).symm, hs.2.congr hFf⟩
  constructor
  · intro v hv
    obtain ⟨w, hw, hb⟩ := hbr ρs ρo _ ha hs hv
    cases htr : w.truthy <;> simp only [htr, Bool.false_eq_true, ↓reduceIte] at hb
    · have := (hwf ρs ρo ha hsF).1 v hb
      cases e with
      | none =>
        simp only [Option.map_none, Option.getD_none, List.nil_append] at this
        have hif := if_normal m fuel (sp := sp) (t := t) (e := none) (new := []) (mod := ρs) (c := []) hw
          (by simp [branchStatements, htr, Eval.exec]) (Frame.refl _ _)
        simp [Eval.exec, hif, this]
      | some f =>
        rw [hrest rfl] at this ⊢
        simp only [Option.map_some, Option.getD_some, List.append_nil] at this
        have hif := if_ret m fuel (sp := sp) (t := t) (e := some f) hw (by simpa [branchStatements, htr] using this)
        simp [Eval.exec, hif]
    · have := (hwt ρs ρo ha hsT).1 v hb
      have hif := if_ret m fuel (sp := sp) (e := e) hw (by simpa [branchStatements, htr] using this)
      simp [Eval.exec, hif]
  · intro brk ρo' hv
    obtain ⟨w, hw, hb⟩ := hbr ρs ρo _ ha hs hv
    cases htr : w.truthy <;> simp only [htr, Bool.false_eq_true, ↓reduceIte] at hb
    · obtain ⟨htl, new, out, mod, hex, hag, hnew, hout, hfr⟩ := (hwf ρs ρo ha hsF).2 brk ρo' hb
      cases e with
      | none =>
        simp only [Option.map_none, Option.getD_none, List.nil_append] at hex hfr
        have hif := if_normal m fuel (sp := sp) (t := t) (e := none) (new := []) (mod := ρs) (c := []) hw
          (by simp [branchStatements, htr, Eval.exec]) (Frame.refl _ _)
        refine ⟨htl, new, out, mod, Ends.congr (by simp [Eval.exec, hif]) hex, hag,
          fun p hp => (hF p.1) ▸ hnew p hp, fun p hp => (hF p.1) ▸ hout p hp,
          hfr.mono fun n hn => by simp [stmtsChanges, hn]⟩
      | some f =>
        obtain rfl := hrest rfl
        simp only [Option.map_some, Option.getD_some, List.append_nil] at hex hfr
        -- The `if` drops what its branch declares.
        have hif := if_ends m fuel (sp := sp) (t := t) (e := some f) hw
          (by simpa [branchStatements, htr] using hex) hfr
        refine ⟨htl, [], out, mod, by simpa [exec_single] using hif, hag, by simp,
          fun p hp => (hF p.1) ▸ hout p hp, hfr.mono fun n hn => ?_⟩
        rw [stmtsChanges_block] at hn
        simp [stmtsChanges, stmtChanges, hn]
    · -- The first branch ends in a `continue` or a `break`, which ends the
      -- statements.
      obtain ⟨htl0, new, out, mod, hex, hag, -, hout, hfr⟩ := (hwt ρs ρo ha hsT).2 brk ρo' hb
      have htl := htail.1 htl0
      have hfr' : Frame (stmtsChanges env.fnChanges (.ifStmt sp test t e :: rest)) mod ρs := hfr.mono fun n hn => by
        rw [stmtsChanges_block] at hn
        cases e <;> simp [stmtsChanges, stmtChanges, hn]
      cases brk
      · obtain ⟨hcont, -, hends⟩ := htail.2 _ _ hex
        have hif := if_jump m fuel (sp := sp) (e := e) (.inl rfl) hw
          (by simpa [branchStatements, htr] using hcont) hfr
        exact ⟨htl, [], out, mod, Ends.congr (by simp [Eval.exec, hif]) (hends mod), hag, by simp,
          fun p hp => (hT p.1) ▸ hout p hp, hfr'⟩
      · have hif := if_jump m fuel (sp := sp) (e := e) (.inr rfl) hw
          (by simpa [branchStatements, htr] using hex.brk) hfr
        exact ⟨htl, [], out, mod, Ends.congr (by simp [Eval.exec, hif]) (Ends.of_brk htl mod), hag, by simp,
          fun p hp => (hT p.1) ▸ hout p hp, hfr'⟩

/-- An `if` whose branches end in the state of the locals they change. -/
theorem if_state_sim {env envT envF : Translate.Env} {sp : Span} {test : Expr} {t : Stmt}
    {e : Option Stmt} {rest : List Stmt} {tail : Tail} {br wt wf rb : IR.Body} {names : List String}
    (hT : ∀ x, envT.has x = env.has x) (hF : ∀ x, envF.has x = env.has x)
    (hTf : globals envT = globals env) (hFf : globals envF = globals env)
    (hnames : names = changedNames (blockStatements t ++ (e.map blockStatements).getD []) env)
    (hbr : BranchSim (N := N) m fs fuel env test br wt wf)
    (hwt : StmtSim (N := N) m fs fuel envT (.state names) (blockStatements t) wt)
    (hwf : StmtSim (N := N) m fs fuel envF (.state names) ((e.map blockStatements).getD []) wf)
    (hrest : StmtSim (N := N) m fs fuel env tail rest rb) :
    StmtSim (N := N) m fs fuel env tail (.ifStmt sp test t e :: rest) (.letState names br rb) := by
  simp only [StmtSim, fnChanges_congr hTf] at hwt
  simp only [StmtSim, fnChanges_congr hFf] at hwf
  intro ρs ρo ha hs
  have hsT : Scoped m envT ρs := ⟨fun x => (hs.1 x).trans (hT x).symm, hs.2.congr hTf⟩
  have hsF : Scoped m envF ρs := ⟨fun x => (hs.1 x).trans (hF x).symm, hs.2.congr hFf⟩
  -- The `if` ends in `mod`, which agrees with the output's state after the
  -- `letState`.
  have key : ∀ o, IR.Body.exec fs fuel ρo (.letState names br rb) = some o →
      ∃ mod ρo₂, Eval.execStmt m fuel ρs (.ifStmt sp test t e) = some (.normal mod) ∧
        Agree mod ρo₂ ∧ Frame (stmtChanges env.fnChanges (.ifStmt sp test t e)) mod ρs ∧
        IR.Body.exec fs fuel ρo₂ rb = some o := by
    intro o ho
    simp only [IR.Body.exec] at ho
    cases hb : IR.Body.exec fs fuel ρo br with
    | none => simp [hb] at ho
    | some ob =>
      cases ob with
      | ret _ | brk _ | cont _ => simp [hb] at ho
      | normal inner =>
        cases hbs : IR.bindState names inner ρo with
        | none => simp [hb, hbs] at ho
        | some ρo₂ =>
          simp only [hb, hbs, Option.bind_eq_bind, Option.bind_some] at ho
          obtain ⟨w, hw, hbw⟩ := hbr ρs ρo _ ha hs hb
          have hside : ∃ new out mod,
              Eval.exec m fuel ρs (branchStatements w t e) = some (.normal (new ++ mod)) ∧
              Agree (out ++ mod) inner ∧ (∀ p ∈ out, env.has p.1 = false) ∧
              Frame (stmtsChanges env.fnChanges (branchStatements w t e)) mod ρs := by
            unfold branchStatements
            cases htr : w.truthy <;> simp only [htr, Bool.false_eq_true, ↓reduceIte] at hbw ⊢
            · obtain ⟨-, new, out, mod, h1, h2, -, h3, h4⟩ := (hwf ρs ρo ha hsF).2 false inner hbw
              exact ⟨new, out, mod, h1, h2, fun p hp => (hF p.1) ▸ h3 p hp, h4⟩
            · obtain ⟨-, new, out, mod, h1, h2, -, h3, h4⟩ := (hwt ρs ρo ha hsT).2 false inner hbw
              exact ⟨new, out, mod, h1, h2, fun p hp => (hT p.1) ▸ h3 p hp, h4⟩
          obtain ⟨new, out, mod, hex, hag, hnew, hfr⟩ := hside
          have hsub : ∀ n, n ∈ stmtsChanges env.fnChanges (branchStatements w t e) →
              n ∈ stmtsChanges env.fnChanges (blockStatements t ++ (e.map blockStatements).getD []) := by
            intro n hn
            unfold branchStatements at hn
            rw [stmtsChanges_append]
            split at hn <;> simp [hn]
          have hsub2 : ∀ n, n ∈ stmtsChanges env.fnChanges (blockStatements t ++ (e.map blockStatements).getD []) →
              n ∈ stmtChanges env.fnChanges (.ifStmt sp test t e) := by
            intro n hn
            rw [stmtsChanges_append, stmtsChanges_block, List.mem_append] at hn
            cases e with
            | none =>
              simp only [Option.map_none, Option.getD_none, stmtsChanges, List.not_mem_nil, or_false] at hn
              simp [stmtChanges, hn]
            | some f =>
              simp only [Option.map_some, Option.getD_some, stmtsChanges_block] at hn
              simp only [stmtChanges, List.mem_append]
              rcases hn with h | h <;> simp [h]
          refine ⟨mod, ρo₂, if_normal m fuel hw hex hfr, ?_, hfr.mono fun n hn => hsub2 n (hsub n hn), ho⟩
          intro n
          rw [bindState_lookup hbs n]
          split
          · rename_i hn
            rw [hnames, mem_changedNames] at hn
            rw [← hag n, lookup_append_fresh mod fun p hp hk => by
              have := hnew p hp; rw [hk, hn.1] at this; exact absurd this (by simp)]
          · rename_i hn
            rw [← ha n]
            by_cases hhas : env.has n = true
            · have hnc : n ∉ stmtsChanges env.fnChanges (branchStatements w t e) := fun hc =>
                hn (by rw [hnames, mem_changedNames]; exact ⟨hhas, hsub n hc⟩)
              exact hfr.lookup hnc
            · have h1 := hs.none (by simpa using hhas)
              have h2 := hfr.isSome n
              rw [h1] at h2 ⊢
              simpa using h2
  constructor
  · intro v hv
    obtain ⟨mod, ρo₂, hif, hag, hfr, hb⟩ := key _ hv
    have := (hrest mod ρo₂ hag (scoped_frame hs hfr)).1 v hb
    simp [Eval.exec, hif, this]
  · intro brk ρo' hv
    obtain ⟨mod, ρo₂, hif, hag, hfr, hb⟩ := key _ hv
    obtain ⟨htail, new, out, mod₂, hex, hag₂, hnew, hout, hfr₂⟩ :=
      (hrest mod ρo₂ hag (scoped_frame hs hfr)).2 brk ρo' hb
    refine ⟨htail, new, out, mod₂, Ends.congr (by simp [Eval.exec, hif]) hex, hag₂, hnew, hout, ?_⟩
    simpa [stmtsChanges] using hfr₂.trans hfr

theorem branch_ite {env : Translate.Env} {test : Expr} {c : IR.Expr} {wt wf : IR.Body}
    (hsim : Sim (N := N) m fs fuel env test c) : BranchSim (N := N) m fs fuel env test (.ite c wt wf) wt wf := by
  intro ρs ρo o ha hs ho
  simp only [IR.Body.exec] at ho
  cases hc : IR.Expr.eval fs fuel ρo c with
  | none => simp [hc] at ho
  | some u =>
    cases u <;> simp [hc] at ho
    rename_i b
    refine ⟨.bool b, hsim ρs ρo _ ha hs hc, ?_⟩
    cases b <;> simpa [Val.truthy] using ho

/-- A test of `null` on a nullable local, or of `undefined` on an optional
one, and the `match` that the output writes for it. -/
theorem branch_none {env : Translate.Env} {test : Expr} {name : String} {isNullTest : Bool} {value : Ty}
    {optional : Bool} {wt wf : IR.Body} (hn : noneTestOf env test = some (name, isNullTest, value, optional)) :
    BranchSim (N := N) m fs fuel env test
      (if isNullTest then .matchNull name optional wt wf else .matchNull name optional wf wt) wt wf := by
  unfold noneTestOf at hn
  split at hn
  · rename_i name' isEq value' hnull
    simp only [Option.some.injEq, Prod.mk.injEq] at hn
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hn
    intro ρs ρo o ha hs ho
    obtain ⟨w, hw, hl⟩ := nullTestOf_eval m fuel hnull hs
    have hwo : ρo.lookup name' = some w := by rw [← ha]; exact hw
    by_cases hu : w = .undefined
    · subst hu
      cases isEq <;> simp [IR.Body.exec, hwo] at ho
    refine ⟨_, hl hu, ?_⟩
    cases isEq <;> simp only [Bool.false_eq_true, ↓reduceIte, IR.Body.exec, hwo,
      Option.bind_eq_bind, Option.bind_some] at ho <;> cases w <;>
      first | exact absurd rfl hu | simpa [isNullVal, Val.truthy] using ho
  · obtain ⟨⟨name', isEq, value'⟩, hu, heq⟩ := Option.map_eq_some_iff.mp hn
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl, rfl, rfl⟩ := heq
    intro ρs ρo o ha hs ho
    obtain ⟨w, hw, hl⟩ := undefinedTestOf_eval m fuel hu hs
    have hwo : ρo.lookup name' = some w := by rw [← ha]; exact hw
    refine ⟨_, hl, ?_⟩
    cases isEq <;> simp only [Bool.false_eq_true, ↓reduceIte, IR.Body.exec, hwo,
      Option.bind_eq_bind, Option.bind_some] at ho <;> cases w <;> simp_all [isUndefVal, Val.truthy]

theorem branch_tag {env : Translate.Env} {test : Expr} {t : TagTest} {wt wf : IR.Body}
    (ht : tagTestOf env test = some t) :
    BranchSim (N := N) m fs fuel env test
      (if t.isEq then .matchTag t.name t.ref t.field t.tag t.other wt wf
        else .matchTag t.name t.ref t.field t.tag t.other wf wt) wt wf := by
  intro ρs ρo o ha hs ho
  obtain ⟨w, hw, hl⟩ := tagTestOf_eval m fuel ht hs
  have hwo : ρo.lookup t.name = some w := by rw [← ha]; exact hw
  cases hie : t.isEq <;> simp only [hie, Bool.false_eq_true, ↓reduceIte] at ho hl
  all_goals
    cases hk : IR.tagOf t.field w with
    | none => simp [IR.Body.exec, hwo, hk] at ho
    | some k =>
      refine ⟨_, hl k hk, ?_⟩
      simp only [IR.Body.exec, hwo, hk, Option.bind_eq_bind, Option.bind_some] at ho
      by_cases hkt : (k == t.tag) = true <;> simp_all [Val.truthy]

/-- The loop `for (const x of …)` over `vs` means what the output's fold means,
when the body does. -/
theorem loop_sim {env bodyEnv : Translate.Env} {x : String} {elemType : Ty} {names : List String}
    {b r : Bool} {bodyS : Stmt} {bodyOut : IR.Body}
    (hbody : StmtSim (N := N) m fs fuel bodyEnv (.loop names b r) (blockStatements bodyS) bodyOut)
    (henv : bodyEnv = env.add { name := x, binding := .const, type := elemType })
    (hfresh : env.has x = false)
    (hnames : names = changedNames (blockStatements bodyS) env) :
    ∀ (vs : List (Val N)) (ρs ρo : Eval.Env N) (o : Outcome N), Agree ρs ρo → Scoped m env ρs →
      IR.Body.runFold fs fuel names x bodyOut ρo vs = some o →
      (∀ w, o = .ret w → Eval.execLoop m fuel ρs (fun v => some [(x, v)]) bodyS vs = some (.ret w)) ∧
      ∀ ρo', o = .normal ρo' → ∃ mod, Eval.execLoop m fuel ρs (fun v => some [(x, v)]) bodyS vs = some (.normal mod) ∧
        Agree mod ρo' ∧ Frame (stmtChanges env.fnChanges bodyS) mod ρs := by
  subst henv
  intro vs
  induction vs with
  | nil =>
    intro ρs ρo o ha hs h
    simp only [IR.Body.runFold, Option.some.injEq] at h
    subst h
    refine ⟨fun w hw => (by cases hw), fun ρo' hρ => ?_⟩
    cases hρ
    exact ⟨ρs, by simp [Eval.execLoop], ha, Frame.refl _ _⟩
  | cons v vs ih =>
    intro ρs ρo o ha hs h
    have ha' : Agree ((x, v) :: ρs) ((x, v) :: ρo) := fun n => by
      simp only [List.lookup]; split
      · rfl
      · exact ha n
    have hs' : Scoped m (env.add { name := x, binding := .const, type := elemType }) ((x, v) :: ρs) :=
      ⟨fun n => by
        rw [has_add, ← hs.1 n]
        simp only [List.lookup]
        by_cases hn : n = x
        · subst hn; simp
        · have h1 : (n == x) = false := by simpa using hn
          have h2 : (x == n) = false := by simpa using Ne.symm hn
          simp [h1, h2], hs.2⟩
    simp only [IR.Body.runFold] at h
    cases hb : IR.Body.exec fs fuel ((x, v) :: ρo) bodyOut with
    | none => simp [hb] at h
    | some ob =>
      -- A `return` in the body ends the loop, and the function.
      by_cases hr : ∃ w, ob = .ret w
      · obtain ⟨w, rfl⟩ := hr
        simp [hb] at h
        subst h
        refine ⟨fun w' hw => ?_, fun ρo' hρ => by cases hρ⟩
        cases hw
        simp [Eval.execLoop, block_ret m fuel bodyS ((hbody _ _ ha' hs').1 w hb)]
      -- Otherwise the body ends in its state, or in a `break`.
      obtain ⟨brk, inner, rfl⟩ : ∃ brk inner, ob = endOf brk inner := by
        cases ob with
        | ret w => exact absurd ⟨w, rfl⟩ hr
        | cont _ => simp [hb] at h
        | normal inner => exact ⟨false, inner, rfl⟩
        | brk inner => exact ⟨true, inner, rfl⟩
      · cases hbs : IR.bindState names inner ρo with
        | none => cases brk <;> simp [endOf, hb, hbs] at h
        | some ρo₁ =>
          obtain ⟨-, new, out, mod, hex, hag, -, hnew, hfr⟩ := (hbody _ _ ha' hs').2 brk inner hb
          -- The body runs to its end or to a `continue`, and the loop goes on,
          -- or it runs to a `break`, and the loop ends.
          obtain ⟨e, he, hdrop, hlen⟩ : ∃ e,
              ((Eval.execStmt m fuel ((x, v) :: ρs) bodyS = some (.normal e) ∨
                Eval.execStmt m fuel ((x, v) :: ρs) bodyS = some (.cont e)) ∧ brk = false ∨
                Eval.execStmt m fuel ((x, v) :: ρs) bodyS = some (.brk e) ∧ brk = true) ∧
              e.drop (e.length - ((x, v) :: ρs).length) = mod ∧ ((x, v) :: ρs).length ≤ e.length := by
            cases brk
            · rcases hex with hex | hex
              · obtain ⟨e, h1, h2, h3⟩ := block_normal m fuel bodyS hex hfr
                exact ⟨e, .inl ⟨.inl h1, rfl⟩, h2, h3⟩
              · obtain ⟨e, h1, h2, h3⟩ := block_jump m fuel bodyS (.inl rfl) hex hfr
                exact ⟨e, .inl ⟨.inr h1, rfl⟩, h2, h3⟩
            · obtain ⟨e, h1, h2, h3⟩ := block_jump m fuel bodyS (.inr rfl) hex hfr
              exact ⟨e, .inr ⟨h1, rfl⟩, h2, h3⟩
          -- `mod` is the loop variable in front of the outer names.
          obtain ⟨⟨k, w⟩, mod', rfl⟩ : ∃ p mod', mod = p :: mod' := by
            cases mod with
            | nil => exact absurd hfr.length (by simp)
            | cons p mod' => exact ⟨p, mod', rfl⟩
          obtain ⟨hk, -, hfr'⟩ := hfr
          simp only at hk
          subst hk
          have hnext : e.drop (e.length - ρs.length) = mod' := by
            have : e.length - ρs.length = (e.length - (ρs.length + 1)) + 1 := by
              simp only [List.length_cons] at hlen; omega
            simp only [List.length_cons] at hdrop
            rw [this, ← List.drop_drop, hdrop]
            rfl
          have hag' : Agree mod' ρo₁ := by
            intro n
            rw [bindState_lookup hbs n]
            split
            · rename_i hn
              rw [hnames, mem_changedNames] at hn
              have hnx : n ≠ k := fun h => by rw [h, hfresh] at hn; exact absurd hn.1 (by simp)
              rw [← hag n, lookup_append_fresh _ fun p hp hpn => by
                have := hnew p hp
                rw [has_add, hpn, hn.1] at this
                exact absurd this (by simp)]
              have : (n == k) = false := by simpa using hnx
              simp [List.lookup, this]
            · rename_i hn
              rw [← ha n]
              by_cases hhas : env.has n = true
              · have hnc : n ∉ stmtsChanges env.fnChanges (blockStatements bodyS) := fun hc =>
                  hn (by rw [hnames, mem_changedNames]; exact ⟨hhas, hc⟩)
                exact hfr'.lookup hnc
              · have h1 := hs.none (by simpa using hhas)
                have h2 := hfr'.isSome n
                rw [h1] at h2 ⊢
                simpa using h2
          rw [stmtsChanges_block] at hfr'
          rcases he with ⟨he, rfl⟩ | ⟨he, rfl⟩
          · simp only [endOf, hb, hbs, Option.bind_eq_bind, Option.bind_some] at h
            obtain ⟨hret, hnorm⟩ := ih mod' ρo₁ o hag' (scoped_frame hs hfr') h
            refine ⟨fun w hw => ?_, fun ρo' hρ => ?_⟩
            · rcases he with he | he <;> simp [Eval.execLoop, he, hnext, hret w hw]
            · obtain ⟨mod₂, hloop, hag₂, hfr₂⟩ := hnorm ρo' hρ
              refine ⟨mod₂, ?_, hag₂, (hfr₂.trans hfr').mono fun n hn => by simp at hn; exact hn⟩
              rcases he with he | he <;> simp [Eval.execLoop, he, hnext, hloop]
          · simp [endOf, hb, hbs] at h
            subst h
            refine ⟨fun w hw => (by cases hw), fun ρo' hρ => ?_⟩
            cases hρ
            exact ⟨mod', by simp [Eval.execLoop, he, hnext], hag', hfr'⟩

/-! ### `switch` -/

omit [JSNumber N] in
/-- A `break` assigns nothing, so leaving it out changes no assignment. -/
theorem assignsList_dropBreak (n : String) : ∀ l : List Stmt,
    Stmt.assignsList n (dropBreak l) = Stmt.assignsList n l
  | [] => rfl
  | [s] => by
    by_cases hb : s.isBreak = true
    · obtain ⟨sp, rfl⟩ : ∃ sp, s = .breakStmt sp := by
        cases s <;> simp [Stmt.isBreak] at hb; exact ⟨_, rfl⟩
      simp [dropBreak, Stmt.isBreak, Stmt.assignsList, Stmt.assigns]
    · simp [dropBreak, hb]
  | s :: t :: rest => by
    simp only [dropBreak, Stmt.assignsList, assignsList_dropBreak n (t :: rest)]

omit [JSNumber N] in
theorem constAssignedIn_dropBreak (s : Stmt) (l : List Stmt) :
    s.constAssignedIn (dropBreak l) = s.constAssignedIn l := by
  cases s <;> simp [Stmt.constAssignedIn, assignsList_dropBreak]


/-- A clause that returns, with no `break` before its `return`, returns from
the case block. -/
theorem execCase_ret {v : Except (Val N) (Val N)} : ∀ {ss : List Stmt} {ρ : Eval.Env N},
    Eval.exec m fuel ρ ss = some (.ret v) → Eval.execCase m fuel ρ ss = some (.ret v, false)
  | [], ρ, h => by simp [Eval.exec] at h
  | s :: rest, ρ, h => by
    have hnb : ∀ sp, s ≠ .breakStmt sp := by
      rintro sp rfl; simp [Eval.exec, Eval.execStmt] at h
    simp only [Eval.exec] at h
    rw [Eval.execCase.eq_3 _ _ _ _ _ hnb]
    simp only [Bool.false_eq_true, ↓reduceIte]
    by_cases hc : s.constAssignedIn rest = true
    · simp [hc] at h
    simp only [hc, Bool.false_eq_true, ↓reduceIte] at h ⊢
    cases hs : Eval.execStmt m fuel ρ s with
    | none => simp [hs] at h
    | some o =>
      cases o with
      | ret r => simp [hs] at h ⊢; exact h
      | brk _ | cont _ => simp [hs] at h
      | normal ρ' =>
        simp only [hs, Option.bind_eq_bind, Option.bind_some, pure_bind] at h ⊢
        exact execCase_ret h

theorem exec_clauseStatements {v : Except (Val N) (Val N)} {ρ : Eval.Env N} {body : List Stmt}
    (h : Eval.exec m fuel ρ (clauseStatements body) = some (.ret v)) : Eval.exec m fuel ρ body = some (.ret v) := by
  unfold clauseStatements at h
  split at h
  · rename_i sp ss
    rw [exec_single, execStmt_block, h]; rfl
  · exact h

/-- A clause that returns, from the clause the test selected. -/
theorem execFrom_ret {v : Except (Val N) (Val N)} {ρ : Eval.Env N} {t : Option Expr} {body : List Stmt}
    {more : List (Option Expr × List Stmt)} (h : Eval.exec m fuel ρ (clauseStatements body) = some (.ret v)) :
    Eval.execFrom m fuel ρ ((t, body) :: more) = some (.ret v) := by
  rw [Eval.execFrom, execCase_ret m fuel (exec_clauseStatements m fuel h)]
  rfl

/-- A `case` whose test is a string: the clause runs for that tag, and the
later clauses decide for every other. -/
theorem execSwitch_case {ρ : Eval.Env N} {test : Expr} {body : List Stmt}
    {more : List (Option Expr × List Stmt)} {tsp : Span} {k : JSString} {tag : String}
    (hst : test.stripParens = .string tsp tag) :
    Eval.execSwitch m fuel ρ (.str k) ((some test, body) :: more) =
      if k = .ofString tag then Eval.execFrom m fuel ρ ((some test, body) :: more)
      else Eval.execSwitch m fuel ρ (.str k) more := by
  have ht : Eval.eval m fuel ρ test = some (.str (.ofString tag)) := by
    rw [← eval_stripParens, hst]; simp [Eval.eval]
  rw [Eval.execSwitch]
  simp only [ht, Option.bind_eq_bind, Option.bind_some, Eval.strictEq]
  by_cases hk : k = .ofString tag <;> simp [hk]

/-- What `matchTag` runs: the arm of the tag, or the other arm, only for
the member that it names when it names one. -/
theorem matchTag_exec {n f tag : String} {r : DeclRef} {other : Option String} {wt wo : IR.Body}
    {ρ : Eval.Env N} {o : Outcome N} (h : IR.Body.exec fs fuel ρ (.matchTag n r (some f) tag other wt wo) = some o) :
    ∃ fields k, ρ.lookup n = some (.obj fields) ∧ fields.lookup f = some (.str k) ∧
      ((k = .ofString tag ∧ IR.Body.exec fs fuel ρ wt = some o) ∨
        (k ≠ .ofString tag ∧ (∀ x, other = some x → k = .ofString x) ∧
          IR.Body.exec fs fuel ρ wo = some o)) := by
  simp only [IR.Body.exec, IR.tagOf] at h
  cases hl : ρ.lookup n with
  | none => simp [hl] at h
  | some w =>
    cases w <;> simp [hl] at h
    rename_i fields
    cases hk : fields.lookup f with
    | none => simp [hk] at h
    | some u =>
      cases u <;> simp [hk] at h
      rename_i k
      refine ⟨fields, k, rfl, hk, ?_⟩
      by_cases hkt : k = .ofString tag
      · simp [hkt] at h; exact .inl ⟨hkt, h⟩
      · simp only [hkt, ↓reduceIte] at h
        split at h
        · rename_i hall
          refine .inr ⟨hkt, fun x hx => ?_, h⟩
          subst hx
          have : JSString.ofString x = k := by simpa using hall
          exact this.symm
        · simp at h

/-- `switch (x.kind)` evaluates the tag of `x`. -/
theorem switchOf_eval {env : Translate.Env} {disc : Expr} {sw : SwitchOn} (h : switchOf env disc = some sw)
    {ρ : Eval.Env N} {fields : List (String × Val N)} {k : JSString}
    (hl : ρ.lookup sw.name = some (.obj fields)) (hk : fields.lookup sw.field = some (.str k)) :
    Eval.eval m fuel ρ disc = some (.str k) := by
  unfold switchOf at h
  rw [← eval_stripParens]
  generalize disc.stripParens = d at h ⊢
  cases d with
  | member sp o f =>
    cases o with
    | ident sp' n =>
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨loc, hloc, h⟩ := h
      split at h
      · rename_i ref tags hty
        simp only [Option.bind_eq_some_iff] at h
        obtain ⟨u, hu, h⟩ := h
        split at h
        · simp only [Option.pure_def, Option.bind_some, Option.some.injEq] at h
          subst h
          simp only at hl hk
          simp [Eval.eval, Eval.getProp, hl, hk, Expr.optSpine]
        · simp at h
      · simp at h
    | _ => simp at h
  | _ => simp at h

/-- The output `body` of the clauses `cs` of a `switch` on `sw`, and of the
statements `rest` after it, where an outer `match` has found that the tag is
`known`. The body never ends without a return. When it returns a value, the
local is an object with a string in its tag field, if the first clause is a
case and no outer `match` came before. For that tag, the case block returns
the value, or ends, and then `rest` returns it. -/
def ClauseSim (env : Translate.Env) (sw : SwitchOn) (known : Option String)
    (cs : List (Option Expr × List Stmt)) (rest : List Stmt) (body : IR.Body) : Prop :=
  ∀ (ρs ρo : Eval.Env N), Agree ρs ρo → Scoped m env ρs →
    (∀ brk ρo', IR.Body.exec fs fuel ρo body ≠ some (endOf brk ρo')) ∧
    ∀ v, IR.Body.exec fs fuel ρo body = some (.ret v) →
      (known = none → (∃ t b more, cs = (some t, b) :: more) →
        ∃ fields k, ρs.lookup sw.name = some (.obj fields) ∧ fields.lookup sw.field = some (.str k)) ∧
      ∀ fields k, ρs.lookup sw.name = some (.obj fields) → fields.lookup sw.field = some (.str k) →
        (∀ o, known = some o → k = o) →
        Eval.execSwitch m fuel ρs (.str k) cs = some (.ret v) ∨
          (Eval.execSwitch m fuel ρs (.str k) cs = some (.normal ρs) ∧ Eval.exec m fuel ρs rest = some (.ret v))

/-- No clause is left: the statements after the `switch` run. -/
theorem clauses_nil_sim {env : Translate.Env} {sw : SwitchOn} {known : Option String} {rest : List Stmt}
    {b : IR.Body} (hrest : StmtSim (N := N) m fs fuel env .ret rest b) :
    ClauseSim (N := N) m fs fuel env sw known [] rest b := by
  intro ρs ρo ha hs
  refine ⟨fun brk ρo' hv => absurd ((hrest ρs ρo ha hs).2 brk ρo' hv).1 (by simp [Tail.isRet]), fun v hv => ⟨?_, ?_⟩⟩
  · intro _ ⟨_, _, _, h⟩; cases h
  · intro _ _ _ _ _
    exact .inr ⟨by simp [Eval.execSwitch], (hrest ρs ρo ha hs).1 v hv⟩

/-- The `default` clause, last. -/
theorem clauses_default_sim {env : Translate.Env} {sw : SwitchOn} {known : Option String} {body : List Stmt}
    {rest : List Stmt} {b : IR.Body} (hb : StmtSim (N := N) m fs fuel env .ret (clauseStatements body) b) :
    ClauseSim (N := N) m fs fuel env sw known [(none, body)] rest b := by
  intro ρs ρo ha hs
  refine ⟨fun brk ρo' hv => absurd ((hb ρs ρo ha hs).2 brk ρo' hv).1 (by simp [Tail.isRet]), fun v hv => ⟨?_, ?_⟩⟩
  · intro _ ⟨_, _, _, h⟩; cases h
  · intro _ _ _ _ _
    left
    rw [Eval.execSwitch]
    exact execFrom_ret m fuel ((hb ρs ρo ha hs).1 v hv)

/-- The case of the one member left, which an outer `match` has tested. -/
theorem clauses_last_sim {env envT : Translate.Env} {sw : SwitchOn} {test : Expr} {body : List Stmt}
    {more : List (Option Expr × List Stmt)} {rest : List Stmt} {tsp : Span} {tag : String} {b : IR.Body}
    (hT : ∀ x, envT.has x = env.has x) (hTf : globals envT = globals env)
    (hst : test.stripParens = .string tsp tag)
    (hb : StmtSim (N := N) m fs fuel envT .ret (clauseStatements body) b) :
    ClauseSim (N := N) m fs fuel env sw (some tag) ((some test, body) :: more) rest b := by
  intro ρs ρo ha hs
  have hsT : Scoped m envT ρs := ⟨fun x => (hs.1 x).trans (hT x).symm, hs.2.congr hTf⟩
  refine ⟨fun brk ρo' hv => absurd ((hb ρs ρo ha hsT).2 brk ρo' hv).1 (by simp [Tail.isRet]), fun v hv => ⟨?_, ?_⟩⟩
  · intro h; cases h
  · intro fields k _ _ hknown
    left
    rw [execSwitch_case m fuel hst, if_pos (hknown tag rfl)]
    exact execFrom_ret m fuel ((hb ρs ρo ha hsT).1 v hv)

/-- A case with members left after it: a `match` on its tag. -/
theorem clauses_case_sim {env envT envO : Translate.Env} {sw : SwitchOn} {known other : Option String}
    {test : Expr} {body : List Stmt} {more : List (Option Expr × List Stmt)} {rest : List Stmt} {tsp : Span}
    {tag : String} {wt wo : IR.Body}
    (hT : ∀ x, envT.has x = env.has x) (hTf : globals envT = globals env)
    (hO : ∀ x, envO.has x = env.has x) (hOf : globals envO = globals env)
    (hst : test.stripParens = .string tsp tag)
    (hwt : StmtSim (N := N) m fs fuel envT .ret (clauseStatements body) wt)
    (hwo : ClauseSim (N := N) m fs fuel envO sw other more rest wo) :
    ClauseSim (N := N) m fs fuel env sw known ((some test, body) :: more) rest
      (.matchTag sw.name sw.ref sw.field tag other wt wo) := by
  intro ρs ρo ha hs
  have hsT : Scoped m envT ρs := ⟨fun x => (hs.1 x).trans (hT x).symm, hs.2.congr hTf⟩
  have hsO : Scoped m envO ρs := ⟨fun x => (hs.1 x).trans (hO x).symm, hs.2.congr hOf⟩
  refine ⟨fun brk ρo' hv => ?_, fun v hv => ?_⟩
  · obtain ⟨_, _, _, _, ⟨_, h⟩ | ⟨_, _, h⟩⟩ := matchTag_exec fs fuel hv
    · exact absurd ((hwt ρs ρo ha hsT).2 brk ρo' h).1 (by simp [Tail.isRet])
    · exact (hwo ρs ρo ha hsO).1 brk ρo' h
  · obtain ⟨fields, k, hl, hk, hbr⟩ := matchTag_exec fs fuel hv
    have hl' : ρs.lookup sw.name = some (.obj fields) := by rw [ha]; exact hl
    refine ⟨fun _ _ => ⟨fields, k, hl', hk⟩, fun fields' k' hl2 hk2 _ => ?_⟩
    rw [hl'] at hl2
    cases hl2
    rw [hk] at hk2
    cases hk2
    rcases hbr with ⟨rfl, h⟩ | ⟨hne, hother, h⟩
    · left
      rw [execSwitch_case m fuel hst, if_pos rfl]
      exact execFrom_ret m fuel ((hwt ρs ρo ha hsT).1 v h)
    · rw [execSwitch_case m fuel hst, if_neg hne]
      exact ((hwo ρs ρo ha hsO).2 v h).2 fields k hl' hk hother

/-- A `switch` whose first clause is a case, in a body that returns. -/
theorem switch_sim {env : Translate.Env} {sp : Span} {disc : Expr} {sw : SwitchOn} {test : Expr}
    {body : List Stmt} {more : List (Option Expr × List Stmt)} {rest : List Stmt} {tail : Tail} {b : IR.Body}
    (hsw : switchOf env disc = some sw) (hdecl : clausesDeclare ((some test, body) :: more) = false)
    (hc : ClauseSim (N := N) m fs fuel env sw none ((some test, body) :: more) rest b) :
    StmtSim (N := N) m fs fuel env tail (.switchStmt sp disc ((some test, body) :: more) :: rest) b := by
  intro ρs ρo ha hs
  refine ⟨fun v hv => ?_, fun brk ρo' hv => absurd hv ((hc ρs ρo ha hs).1 brk ρo')⟩
  obtain ⟨hfirst, hmain⟩ := (hc ρs ρo ha hs).2 v hv
  obtain ⟨fields, k, hl, hk⟩ := hfirst rfl ⟨test, body, more, rfl⟩
  have hd := switchOf_eval m fuel hsw hl hk
  rcases hmain fields k hl hk (fun _ h => by cases h) with h1 | ⟨h1, h2⟩
  · simp [Eval.exec, Eval.execStmt, hdecl, hd, h1]
  · simp [Eval.exec, Eval.execStmt, hdecl, hd, h1, h2]

/-! ### `switch` clauses that end in `break` -/

/-- A clause whose statements before its `break` end normally ends normally,
and says whether a `break` ended it. -/
theorem execCase_drop {e : Eval.Env N} : ∀ {body : List Stmt} {ρ : Eval.Env N},
    Eval.exec m fuel ρ (dropBreak body) = some (.normal e) →
      Eval.execCase m fuel ρ body = some (.normal e, endsInBreak body)
  | [], ρ, h => by
    simp [dropBreak, Eval.exec] at h; subst h; simp [Eval.execCase, endsInBreak]
  | [s], ρ, h => by
    by_cases hb : s.isBreak = true
    · obtain ⟨sp, rfl⟩ : ∃ sp, s = .breakStmt sp := by
        cases s <;> simp [Stmt.isBreak] at hb; exact ⟨_, rfl⟩
      simp [dropBreak, Stmt.isBreak, Eval.exec] at h; subst h
      simp [Eval.execCase, endsInBreak, Stmt.isBreak]
    · have hnb : ∀ sp, s ≠ .breakStmt sp := by rintro sp rfl; simp [Stmt.isBreak] at hb
      simp only [dropBreak, hb, Bool.false_eq_true, ↓reduceIte] at h
      rw [exec_single] at h
      rw [Eval.execCase.eq_3 _ _ _ _ _ hnb]
      simp only [Bool.false_eq_true, ↓reduceIte, h, Option.bind_eq_bind, Option.bind_some]
      simp [Eval.execCase, endsInBreak, hb]
  | s :: t :: rest, ρ, h => by
    have hnb : ∀ sp, s ≠ .breakStmt sp := by
      rintro sp rfl; simp [dropBreak, Eval.exec, Eval.execStmt] at h
    simp only [dropBreak, Eval.exec] at h
    rw [Eval.execCase.eq_3 _ _ _ _ _ hnb]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [← constAssignedIn_dropBreak s (t :: rest)]
    by_cases hc : s.constAssignedIn (dropBreak (t :: rest)) = true
    · simp [hc] at h
    simp only [hc, Bool.false_eq_true, ↓reduceIte] at h ⊢
    cases hs : Eval.execStmt m fuel ρ s with
    | none => simp [hs] at h
    | some o =>
      cases o with
      | ret _ | brk _ | cont _ => simp [hs] at h
      | normal ρ' =>
        simp only [hs, Option.bind_eq_bind, Option.bind_some, pure_bind] at h ⊢
        rw [execCase_drop h]
        simp [endsInBreak]

/-- The selected clause ends normally, and the `switch` with it: by its `break`,
or because no clause comes after it. -/
theorem execFrom_normal {e ρ : Eval.Env N} {t : Option Expr} {body : List Stmt}
    {more : List (Option Expr × List Stmt)} (h : Eval.exec m fuel ρ (dropBreak body) = some (.normal e))
    (hlast : more = [] ∨ endsInBreak body = true) :
    Eval.execFrom m fuel ρ ((t, body) :: more) = some (.normal e) := by
  rw [Eval.execFrom, execCase_drop m fuel h]
  cases hb : endsInBreak body
  · rcases hlast with rfl | h'
    · simp [Eval.execFrom]
    · rw [hb] at h'; cases h'
  · rfl

omit [JSNumber N] in
/-- A `break` changes no local. -/
theorem stmtsChanges_dropBreak (fns : List (String × List String)) :
    ∀ (body : List Stmt), stmtsChanges fns (dropBreak body) = stmtsChanges fns body
  | [] => rfl
  | [s] => by
    by_cases hb : s.isBreak = true
    · obtain ⟨sp, rfl⟩ : ∃ sp, s = .breakStmt sp := by
        cases s <;> simp [Stmt.isBreak] at hb; exact ⟨_, rfl⟩
      rfl
    · simp [dropBreak, hb]
  | s :: t :: rest => by
    simp only [dropBreak, stmtsChanges, stmtsChanges_dropBreak fns (t :: rest)]

omit [JSNumber N] in
theorem stmtsChanges_flatMap (fns : List (String × List String)) : ∀ (cs : List (Option Expr × List Stmt)),
    ∀ n ∈ stmtsChanges fns (cs.flatMap (·.2)), n ∈ clausesChanges fns cs
  | [], n, h => by simp [stmtsChanges] at h
  | (t, b) :: cs, n, h => by
    simp only [List.flatMap_cons, stmtsChanges_append, List.mem_append] at h
    simp only [clausesChanges, List.mem_append]
    rcases h with h | h
    · exact .inl (.inr h)
    · exact .inr (stmtsChanges_flatMap fns cs n h)

/-- A statement that ends in the state of the locals `names`, as an `if`
without a return or a `switch` whose clauses end in `break` does, and then
`rest`: `let (x, y) := br`, then `rb`. -/
theorem letState_sim {env : Translate.Env} {st : Stmt} {rest : List Stmt} {tail : Tail} {br rb : IR.Body}
    {names : List String} {ss : List Stmt} (hst0 : st.constAssignedIn rest = false)
    (hnames : names = changedNames ss env)
    (hsub : ∀ n, n ∈ stmtsChanges env.fnChanges ss → n ∈ stmtChanges env.fnChanges st)
    (hbr : ∀ (ρs ρo inner : Eval.Env N), Agree ρs ρo → Scoped m env ρs →
      IR.Body.exec fs fuel ρo br = some (.normal inner) →
      ∃ new mod, Eval.execStmt m fuel ρs st = some (.normal mod) ∧ Agree (new ++ mod) inner ∧
        (∀ p ∈ new, env.has p.1 = false) ∧ Frame (stmtsChanges env.fnChanges ss) mod ρs)
    (hrest : StmtSim (N := N) m fs fuel env tail rest rb) :
    StmtSim (N := N) m fs fuel env tail (st :: rest) (.letState names br rb) := by
  intro ρs ρo ha hs
  have key : ∀ o, IR.Body.exec fs fuel ρo (.letState names br rb) = some o →
      ∃ mod ρo₂, Eval.execStmt m fuel ρs st = some (.normal mod) ∧
        Agree mod ρo₂ ∧ Frame (stmtChanges env.fnChanges st) mod ρs ∧ IR.Body.exec fs fuel ρo₂ rb = some o := by
    intro o ho
    simp only [IR.Body.exec] at ho
    cases hb : IR.Body.exec fs fuel ρo br with
    | none => simp [hb] at ho
    | some ob =>
      cases ob with
      | ret _ | brk _ | cont _ => simp [hb] at ho
      | normal inner =>
        cases hbs : IR.bindState names inner ρo with
        | none => simp [hb, hbs] at ho
        | some ρo₂ =>
          simp only [hb, hbs, Option.bind_eq_bind, Option.bind_some] at ho
          obtain ⟨new, mod, hex, hag, hnew, hfr⟩ := hbr ρs ρo inner ha hs hb
          refine ⟨mod, ρo₂, hex, ?_, hfr.mono fun n hn => hsub n hn, ho⟩
          intro n
          rw [bindState_lookup hbs n]
          split
          · rename_i hn
            rw [hnames, mem_changedNames] at hn
            rw [← hag n, lookup_append_fresh mod fun p hp hk => by
              have := hnew p hp; rw [hk, hn.1] at this; exact absurd this (by simp)]
          · rename_i hn
            rw [← ha n]
            by_cases hhas : env.has n = true
            · have hnc : n ∉ stmtsChanges env.fnChanges ss := fun hc =>
                hn (by rw [hnames, mem_changedNames]; exact ⟨hhas, hc⟩)
              exact hfr.lookup hnc
            · have h1 := hs.none (by simpa using hhas)
              have h2 := hfr.isSome n
              rw [h1] at h2 ⊢
              simpa using h2
  constructor
  · intro v hv
    obtain ⟨mod, ρo₂, hst, hag, hfr, hb⟩ := key _ hv
    have := (hrest mod ρo₂ hag (scoped_frame hs hfr)).1 v hb
    simp [Eval.exec, hst0, hst, this]
  · intro brk ρo' hv
    obtain ⟨mod, ρo₂, hst, hag, hfr, hb⟩ := key _ hv
    obtain ⟨htail, new, out, mod₂, hex, hag₂, hnew, hout, hfr₂⟩ :=
      (hrest mod ρo₂ hag (scoped_frame hs hfr)).2 brk ρo' hb
    refine ⟨htail, new, out, mod₂, Ends.congr (by simp [Eval.exec, hst0, hst]) hex, hag₂, hnew, hout, ?_⟩
    simpa [stmtsChanges] using hfr₂.trans hfr

/-- The output `body` of the clauses `cs` of a `switch` on `sw` whose clauses
end in `break`, where an outer `match` has found that the tag is `known`.
When the body ends in a state, the local is an object with a string in its
tag field, if the first clause is a case and no outer `match` came before.
For that tag, the case block ends, with environments that agree, as
`StmtSim` states for a branch. -/
def StateClauseSim (env : Translate.Env) (sw : SwitchOn) (known : Option String)
    (cs : List (Option Expr × List Stmt)) (body : IR.Body) : Prop :=
  ∀ (ρs ρo inner : Eval.Env N), Agree ρs ρo → Scoped m env ρs →
    IR.Body.exec fs fuel ρo body = some (.normal inner) →
      (known = none → (∃ t b more, cs = (some t, b) :: more) →
        ∃ fields k, ρs.lookup sw.name = some (.obj fields) ∧ fields.lookup sw.field = some (.str k)) ∧
      ∀ fields k, ρs.lookup sw.name = some (.obj fields) → fields.lookup sw.field = some (.str k) →
        (∀ o, known = some o → k = o) →
        ∃ new out mod, Eval.execSwitch m fuel ρs (.str k) cs = some (.normal (new ++ mod)) ∧
          Agree (out ++ mod) inner ∧ (∀ p ∈ out, env.has p.1 = false) ∧
          Frame (stmtsChanges env.fnChanges (cs.flatMap (·.2))) mod ρs

/-- No clause is left: the locals keep their values. -/
theorem state_nil_sim {env : Translate.Env} {sw : SwitchOn} {known : Option String} {names : List String} :
    StateClauseSim (N := N) m fs fuel env sw known [] (.state names) := by
  intro ρs ρo inner ha hs hv
  simp only [IR.Body.exec, Option.some.injEq, Outcome.normal.injEq] at hv
  subst hv
  refine ⟨fun _ h => (by obtain ⟨_, _, _, h⟩ := h; cases h), fun _ _ _ _ _ =>
    ⟨[], [], ρs, by simp [Eval.execSwitch], by simpa using ha, by simp, Frame.refl _ _⟩⟩

/-- The `default` clause, last. -/
theorem state_default_sim {env : Translate.Env} {sw : SwitchOn} {known : Option String} {body : List Stmt}
    {b : IR.Body} {names : List String}
    (hb : StmtSim (N := N) m fs fuel env (.state names) (dropBreak body) b) :
    StateClauseSim (N := N) m fs fuel env sw known [(none, body)] b := by
  intro ρs ρo inner ha hs hv
  obtain ⟨-, new, out, mod, hex, hag, -, hnew, hfr⟩ := (hb ρs ρo ha hs).2 false inner hv
  refine ⟨fun _ h => (by obtain ⟨_, _, _, h⟩ := h; cases h), fun _ _ _ _ _ => ⟨new, out, mod, ?_, hag, hnew, ?_⟩⟩
  · rw [Eval.execSwitch]; exact execFrom_normal m fuel hex (.inl rfl)
  · exact hfr.mono fun n hn => by simpa [stmtsChanges] using (stmtsChanges_dropBreak _ body ▸ hn)

/-- The case of the one member left, which an outer `match` has tested. -/
theorem state_last_sim {env envT : Translate.Env} {sw : SwitchOn} {test : Expr} {body : List Stmt}
    {more : List (Option Expr × List Stmt)} {tsp : Span} {tag : String} {b : IR.Body} {names : List String}
    (hT : ∀ x, envT.has x = env.has x) (hTf : globals envT = globals env)
    (hst : test.stripParens = .string tsp tag) (hlast : more = [] ∨ endsInBreak body = true)
    (hb : StmtSim (N := N) m fs fuel envT (.state names) (dropBreak body) b) :
    StateClauseSim (N := N) m fs fuel env sw (some tag) ((some test, body) :: more) b := by
  simp only [StmtSim, fnChanges_congr hTf] at hb
  intro ρs ρo inner ha hs hv
  have hsT : Scoped m envT ρs := ⟨fun x => (hs.1 x).trans (hT x).symm, hs.2.congr hTf⟩
  obtain ⟨-, new, out, mod, hex, hag, -, hnew, hfr⟩ := (hb ρs ρo ha hsT).2 false inner hv
  refine ⟨fun h => (by cases h), fun fields k _ _ hknown =>
    ⟨new, out, mod, ?_, hag, fun p hp => by rw [← hT]; exact hnew p hp, hfr.mono fun n hn => ?_⟩⟩
  · rw [execSwitch_case m fuel hst, if_pos (hknown tag rfl)]
    exact execFrom_normal m fuel hex hlast
  · simp only [List.flatMap_cons, stmtsChanges_append, List.mem_append]
    exact .inl ((stmtsChanges_dropBreak _ body ▸ hn))

/-- A case with members left after it: a `match` on its tag. -/
theorem state_case_sim {env envT envO : Translate.Env} {sw : SwitchOn} {known other : Option String}
    {test : Expr} {body : List Stmt} {more : List (Option Expr × List Stmt)} {tsp : Span} {tag : String}
    {wt wo : IR.Body} {names : List String}
    (hT : ∀ x, envT.has x = env.has x) (hTf : globals envT = globals env)
    (hO : ∀ x, envO.has x = env.has x) (hOf : globals envO = globals env)
    (hst : test.stripParens = .string tsp tag) (hlast : more = [] ∨ endsInBreak body = true)
    (hwt : StmtSim (N := N) m fs fuel envT (.state names) (dropBreak body) wt)
    (hwo : StateClauseSim (N := N) m fs fuel envO sw other more wo) :
    StateClauseSim (N := N) m fs fuel env sw known ((some test, body) :: more)
      (.matchTag sw.name sw.ref sw.field tag other wt wo) := by
  simp only [StmtSim, fnChanges_congr hTf] at hwt
  simp only [StateClauseSim, fnChanges_congr hOf] at hwo
  intro ρs ρo inner ha hs hv
  have hsT : Scoped m envT ρs := ⟨fun x => (hs.1 x).trans (hT x).symm, hs.2.congr hTf⟩
  have hsO : Scoped m envO ρs := ⟨fun x => (hs.1 x).trans (hO x).symm, hs.2.congr hOf⟩
  obtain ⟨fields, k, hl, hk, hbr⟩ := matchTag_exec fs fuel hv
  have hl' : ρs.lookup sw.name = some (.obj fields) := by rw [ha]; exact hl
  refine ⟨fun _ _ => ⟨fields, k, hl', hk⟩, fun fields' k' hl2 hk2 _ => ?_⟩
  rw [hl'] at hl2
  cases hl2
  rw [hk] at hk2
  cases hk2
  rcases hbr with ⟨rfl, h⟩ | ⟨hne, hother, h⟩
  · obtain ⟨-, new, out, mod, hex, hag, -, hnew, hfr⟩ := (hwt ρs ρo ha hsT).2 false inner h
    refine ⟨new, out, mod, ?_, hag, fun p hp => by rw [← hT]; exact hnew p hp, hfr.mono fun n hn => ?_⟩
    · rw [execSwitch_case m fuel hst, if_pos rfl]; exact execFrom_normal m fuel hex hlast
    · simp only [List.flatMap_cons, stmtsChanges_append, List.mem_append]
      exact .inl ((stmtsChanges_dropBreak _ body ▸ hn))
  · obtain ⟨-, hmain⟩ := hwo ρs ρo inner ha hsO h
    obtain ⟨new, out, mod, hex, hag, hnew, hfr⟩ := hmain fields k hl' hk hother
    refine ⟨new, out, mod, ?_, hag, fun p hp => by rw [← hO]; exact hnew p hp, hfr.mono fun n hn => ?_⟩
    · rw [execSwitch_case m fuel hst, if_neg hne]; exact hex
    · simp only [List.flatMap_cons, stmtsChanges_append, List.mem_append]; exact .inr hn

/-- A `switch` whose clauses end in `break`, and the statements after it. -/
theorem switch_state_sim {env : Translate.Env} {sp : Span} {disc : Expr} {sw : SwitchOn} {test : Expr}
    {body : List Stmt} {more : List (Option Expr × List Stmt)} {rest : List Stmt} {tail : Tail}
    {b rb : IR.Body} {names : List String}
    (hsw : switchOf env disc = some sw) (hdecl : clausesDeclare ((some test, body) :: more) = false)
    (hnames : names = changedNames (((some test, body) :: more).flatMap (·.2)) env)
    (hc : StateClauseSim (N := N) m fs fuel env sw none ((some test, body) :: more) b)
    (hrest : StmtSim (N := N) m fs fuel env tail rest rb) :
    StmtSim (N := N) m fs fuel env tail (.switchStmt sp disc ((some test, body) :: more) :: rest)
      (.letState names b rb) := by
  refine letState_sim m fs fuel rfl hnames (fun n hn => ?_) (fun ρs ρo inner ha hs hv => ?_) hrest
  · simp only [stmtChanges, List.mem_append]; exact .inr (stmtsChanges_flatMap _ _ n hn)
  · obtain ⟨hfirst, hmain⟩ := hc ρs ρo inner ha hs hv
    obtain ⟨fields, k, hl, hk⟩ := hfirst rfl ⟨test, body, more, rfl⟩
    obtain ⟨new, out, mod, hex, hag, hnew, hfr⟩ := hmain fields k hl hk (fun _ h => by cases h)
    refine ⟨out, mod, ?_, hag, hnew, hfr⟩
    simp [Eval.execStmt, hdecl, switchOf_eval m fuel hsw hl hk, hex, hfr.length]

/-- `translateStateClause` is sound, when `translateStatements` is with one unit of fuel less. -/
theorem translateStateClause_sound {F : Nat}
    (ihS : ∀ env tail ss ctx body ctx', translateStatements F env tail ss ctx = .ok body ctx' →
      StmtSim (N := N) m fs fuel env tail ss body) :
    ∀ env s names last body ctx b ctx', translateStateClause (F + 1) env s names last body ctx = .ok b ctx' →
      (last = true ∨ endsInBreak body = true) ∧
        StmtSim (N := N) m fs fuel env (.state names) (dropBreak body) b := by
  intro env s names last body ctx b ctx' h
  unfold translateStateClause at h
  simp only [ite_state] at h
  split at h
  · simp at h
  rename_i hl
  split at h
  · simp at h
  refine ⟨?_, ihS _ _ _ _ _ _ h⟩
  revert hl
  cases last <;> cases endsInBreak body <;> simp

/-- `translateStateClauses` is sound, when it and `translateStateClause` are with one unit of fuel less. -/
theorem translateStateClauses_sound {F : Nat}
    (ihSC : ∀ env s sw tags known names cs ctx body ctx',
      translateStateClauses F env s sw tags known names cs ctx = .ok body ctx' →
      StateClauseSim (N := N) m fs fuel env sw known cs body)
    (ihA : ∀ env s names last body ctx b ctx', translateStateClause F env s names last body ctx = .ok b ctx' →
      (last = true ∨ endsInBreak body = true) ∧
        StmtSim (N := N) m fs fuel env (.state names) (dropBreak body) b) :
    ∀ env s sw tags known names cs ctx body ctx',
      translateStateClauses (F + 1) env s sw tags known names cs ctx = .ok body ctx' →
      StateClauseSim (N := N) m fs fuel env sw known cs body := by
  intro env s sw tags known names cs ctx body ctx' h
  unfold translateStateClauses at h
  rcases cs with _ | ⟨⟨_ | test, cb⟩, more⟩
  · simp only [ite_state] at h
    split at h
    · simp at h
    simp only [pure_ok] at h
    obtain ⟨rfl, -⟩ := h
    exact state_nil_sim m fs fuel
  · cases more with
    | nil =>
      simp only [ite_state] at h
      split at h
      · simp at h
      exact state_default_sim m fs fuel (ihA _ _ _ _ _ _ _ _ h).2
    | cons _ _ => simp at h
  · simp only at h
    generalize hst : test.stripParens = st at h
    cases st with
    | string tsp tag =>
      simp only at h
      cases hmem : sw.union.members.lookup tag with
      | none => simp [hmem] at h
      | some member =>
        simp only [hmem, ite_state] at h
        split at h
        · simp at h
        simp only [bind_ok] at h
        obtain ⟨wt, s₁, hwt, h⟩ := h
        have hA := ihA _ _ _ _ _ _ _ _ hwt
        have hlast : more = [] ∨ endsInBreak cb = true := hA.1.imp (by simpa using ·) id
        simp only [ite_state] at h
        split at h
        · split at h
          · simp at h
          rename_i hknown
          split at h
          · simp at h
          simp only [pure_ok] at h
          obtain ⟨rfl, -⟩ := h
          have hk : known = some tag := by simpa using hknown
          subst hk
          exact state_last_sim m fs fuel (narrow_has _ _ _) rfl hst hlast hA.2
        · simp only [bind_ok] at h
          obtain ⟨wo, s₂, hwo, h⟩ := h
          simp only [ite_state] at h
          split at h
          · simp at h
          simp only [pure_ok] at h
          obtain ⟨rfl, -⟩ := h
          exact state_case_sim m fs fuel (narrow_has _ _ _) rfl (narrow_has _ _ _) rfl hst hlast hA.2
            (ihSC _ _ _ _ _ _ _ _ _ _ hwo)
    | _ => simp at h

/-- `translateIf` is sound, when `translateStatements` is with one unit of fuel less. -/
theorem translateIf_sound (hc : CallsAgree (N := N) m.program fs fuel) {F : Nat}
    (ihS : ∀ env tail ss ctx body ctx', translateStatements F env tail ss ctx = .ok body ctx' →
      StmtSim (N := N) m fs fuel env tail ss body) :
    ∀ env s test t e rest tail ctx body ctx', translateIf (F + 1) env s test t e rest tail ctx = .ok body ctx' →
      StmtSim (N := N) m fs fuel env tail (.ifStmt s test t e :: rest) body := by
  intro env s test t e rest tail ctx body ctx' h
  unfold translateIf at h
  cases hn : noneTestOf env test with
  | none =>
    cases ht : tagTestOf env test with
    | some tt =>
      -- `if (x.kind === 'a')`: a match on the member.
      have hb := fun wt wf => branch_tag (N := N) (wt := wt) (wf := wf) m fs fuel ht
      cases hie : tt.isEq <;> simp only [hn, ht, hie, Bool.false_eq_true, ↓reduceIte] at h hb
      all_goals
        split at h
        · rename_i hearly
          split at h
          · simp only [bind_ok, reject_ne_ok, false_and, exists_false, reject_ne_ok] at h
          · rename_i hrest
            simp only [pure_bind, bind_ok] at h
            obtain ⟨wt, s₁, hwt, wf, s₂, hwf, h⟩ := h
            split at h
            · simp only [bind_ok, reject_ne_ok, false_and, exists_false, reject_ne_ok] at h
            · simp only [pure_ok] at h
              obtain ⟨_, _, ⟨rfl, rfl⟩, rfl, -⟩ := h
              exact if_early_sim m fs fuel (narrow_has _ _ _) (narrow_has _ _ _) rfl rfl (earlyTail_ends hearly)
                (fun he => by simpa [he] using hrest) (hb wt wf) (ihS _ _ _ _ _ _ hwt)
                (ihS _ _ _ _ _ _ hwf)
        · simp only [pure_bind, ite_state] at h
          split at h
          · simp only [bind_ok, reject_ne_ok, false_and, exists_false, reject_ne_ok] at h
          · try simp only [pure_bind, ite_state] at h
            split at h
            · simp only [bind_ok, reject_ne_ok, false_and, exists_false, reject_ne_ok] at h
            · try simp only [pure_bind, ite_state] at h
              split at h
              · simp only [bind_ok, reject_ne_ok, false_and, exists_false, reject_ne_ok] at h
              · simp only [bind_ok] at h
                obtain ⟨wt, s₁, hwt, wf, s₂, hwf, br, s₃, hbr, rb, s₄, hrb, rfl, -⟩ := h
                simp only [ite_state] at hbr
                split at hbr
                · simp at hbr
                · simp only [pure_ok] at hbr
                  obtain ⟨rfl, -⟩ := hbr
                  exact if_state_sim m fs fuel (narrow_has _ _ _) (narrow_has _ _ _) rfl rfl rfl
                    (hb wt wf) (ihS _ _ _ _ _ _ hwt) (ihS _ _ _ _ _ _ hwf) (ihS _ _ _ _ _ _ hrb)
    | none =>
      simp only [hn, ht] at h
      split at h
      · rename_i hearly
        split at h
        · simp at h
        · rename_i hrest
          simp only [pure_bind, bind_ok, fuelLimit_ok, pure_ok] at h
          obtain ⟨wt, s₁, hwt, wf, s₂, hwf, br, s₃, hbr, rfl, -⟩ := h
          obtain ⟨_, _, ⟨rfl, rfl⟩, c, s₄, hce, hbr⟩ := hbr
          simp only [ite_state] at hbr
          split at hbr
          · simp only [pure_ok] at hbr
            obtain ⟨rfl, -⟩ := hbr
            exact if_early_sim m fs fuel (fun _ => rfl) (fun _ => rfl) rfl rfl (earlyTail_ends hearly)
              (fun he => by simpa [he] using hrest)
              (branch_ite m fs fuel ((expr_sound m fs fuel hc _).1 _ _ _ _ _ _ hce))
              (ihS _ _ _ _ _ _ hwt) (ihS _ _ _ _ _ _ hwf)
          · simp at hbr
      · simp only [pure_bind, ite_state] at h
        split at h
        · simp at h
        · try simp only [pure_bind, ite_state] at h
          split at h
          · simp at h
          · simp only [bind_ok, fuelLimit_ok, pure_ok] at h
            obtain ⟨wt, s₁, hwt, wf, s₂, hwf, br, s₃, hbr, rb, s₄, hrb, rfl, -⟩ := h
            obtain ⟨_, _, ⟨rfl, rfl⟩, c, s₅, hce, hbr⟩ := hbr
            simp only [ite_state] at hbr
            split at hbr
            · simp only [pure_ok] at hbr
              obtain ⟨rfl, -⟩ := hbr
              exact if_state_sim m fs fuel (fun _ => rfl) (fun _ => rfl) rfl rfl rfl
                (branch_ite m fs fuel ((expr_sound m fs fuel hc _).1 _ _ _ _ _ _ hce))
                (ihS _ _ _ _ _ _ hwt) (ihS _ _ _ _ _ _ hwf) (ihS _ _ _ _ _ _ hrb)
            · simp at hbr
  | some nt =>
    obtain ⟨name, isNullTest, value, optional⟩ := nt
    have hb := fun wt wf => branch_none (N := N) (wt := wt) (wf := wf) m fs fuel hn
    cases isNullTest <;> simp only [hn, Bool.false_eq_true, ↓reduceIte] at h hb
    all_goals
      split at h
      · rename_i hearly
        split at h
        · simp at h
        · rename_i hrest
          simp only [pure_bind, bind_ok, pure_ok] at h
          obtain ⟨wt, s₁, hwt, wf, s₂, hwf, rfl, -⟩ := h
          exact if_early_sim m fs fuel (narrow_has _ _ _) (narrow_has _ _ _) rfl rfl (earlyTail_ends hearly)
            (fun he => by simpa [he] using hrest) (hb wt wf) (ihS _ _ _ _ _ _ hwt) (ihS _ _ _ _ _ _ hwf)
      · simp only [pure_bind, ite_state] at h
        split at h
        · simp at h
        · try simp only [pure_bind, ite_state] at h
          split at h
          · simp at h
          · try simp only [pure_bind, ite_state] at h
            split at h
            · simp at h
            · simp only [bind_ok, pure_ok] at h
              obtain ⟨wt, s₁, hwt, wf, s₂, hwf, rb, s₄, hrb, rfl, -⟩ := h
              exact if_state_sim m fs fuel (narrow_has _ _ _) (narrow_has _ _ _) rfl rfl rfl (hb wt wf)
                (ihS _ _ _ _ _ _ hwt) (ihS _ _ _ _ _ _ hwf) (ihS _ _ _ _ _ _ hrb)

/-- `translateLoop` is sound, when `translateStatements` is with one unit of fuel less. -/
theorem translateLoop_sound (hc : CallsAgree (N := N) m.program fs fuel) {F : Nat}
    (ihS : ∀ env tail ss ctx body ctx', translateStatements F env tail ss ctx = .ok body ctx' →
      StmtSim (N := N) m fs fuel env tail ss body) :
    ∀ env s head b rest tail ctx body ctx',
      translateLoop (F + 1) env s head b rest tail ctx = .ok body ctx' →
      StmtSim (N := N) m fs fuel env tail (head.stmt s b :: rest) body := by
  intro env s head b rest tail ctx body ctx' h
  unfold translateLoop at h
  simp only [ite_state] at h
  split at h
  · simp at h
  · try simp only [pure_bind, ite_state] at h
    split at h
    · simp at h
    · simp only [bind_ok] at h
      obtain ⟨⟨x, elemType, li⟩, s₁, hhead, h⟩ := h
      have hhs := loopHead_sim m fs fuel hc hhead
      simp at h
      obtain ⟨bodyEnv, s₂, hdecl, bodyOut, s₃, hbody, _, _, ⟨rfl, rfl⟩, _, _, ⟨rfl, rfl⟩, rb, hrb, hbodyEq⟩ := h
      obtain ⟨hfresh, rfl, -⟩ := declare_ok hdecl
      have hloop := loop_sim m fs fuel (ihS _ _ _ _ _ _ hbody) rfl hfresh rfl
      have hrest := ihS _ _ _ _ _ _ hrb
      intro ρs ρo ha hs
      -- The loop returns from the function, or it ends and the statements
      -- after it run.
      have key : ∀ o, IR.Body.exec fs fuel ρo body = some o →
          (∃ w, o = .ret w ∧ Eval.execStmt m fuel ρs (head.stmt s b) = some (.ret w)) ∨
          ∃ mod ρo₂, Eval.execStmt m fuel ρs (head.stmt s b) = some (.normal mod) ∧
            Agree mod ρo₂ ∧ Frame (stmtChanges env.fnChanges (head.stmt s b)) mod ρs ∧
            IR.Body.exec fs fuel ρo₂ rb = some o := by
        intro o ho
        rw [← hbodyEq] at ho
        simp only [IR.Body.exec] at ho
        cases hi : IR.Expr.eval fs fuel ρo li with
        | none => simp [hi] at ho
        | some u =>
          cases u <;> simp [hi] at ho
          rename_i vs
          have hst := hhs ρs ρo vs ha hs hi
          cases hf : IR.Body.runFold fs fuel (changedNames (blockStatements b) env) x bodyOut ρo vs with
          | none => simp [hf] at ho
          | some ro =>
            obtain ⟨hret, hnorm⟩ := hloop vs ρs ρo ro ha hs hf
            cases ro with
            | normal ρo₂ =>
              simp [hf] at ho
              obtain ⟨mod, hl, hag, hfr⟩ := hnorm ρo₂ rfl
              refine .inr ⟨mod, ρo₂, by rw [hst, hl], hag, hfr.mono fun n hn => ?_, ho⟩
              cases head <;> simp [LoopHead.stmt, stmtChanges, hn]
            | ret w =>
              simp [hf] at ho
              subst ho
              exact .inl ⟨w, rfl, by rw [hst, hret w rfl]⟩
            | brk _ | cont _ => simp [hf] at ho
      constructor
      · intro v hv
        rcases key _ hv with ⟨w, hw, hst⟩ | ⟨mod, ρo₂, hst, hag, hfr, hb⟩
        · cases hw
          simp [Eval.exec, hst]
        have := (hrest mod ρo₂ hag (scoped_frame hs hfr)).1 v hb
        simp [Eval.exec, hst, this]
      · intro brk ρo' hv
        rcases key _ hv with ⟨w, hw, -⟩ | ⟨mod, ρo₂, hst, hag, hfr, hb⟩
        · cases brk <;> cases hw
        obtain ⟨htail, new, out, mod₂, hex, hag₂, hnew, hout, hfr₂⟩ :=
          (hrest mod ρo₂ hag (scoped_frame hs hfr)).2 brk ρo' hb
        refine ⟨htail, new, out, mod₂, Ends.congr (by simp [Eval.exec, hst]) hex, hag₂, hnew, hout, ?_⟩
        simpa [stmtsChanges] using hfr₂.trans hfr

/-- `translateSwitch` is sound, when the functions it calls are with one unit of fuel less. -/
theorem translateSwitch_sound {F : Nat}
    (ihS : ∀ env tail ss ctx body ctx', translateStatements F env tail ss ctx = .ok body ctx' →
      StmtSim (N := N) m fs fuel env tail ss body)
    (ihC : ∀ env s sw tags known cs rest ctx body ctx',
      translateClauses F env s sw tags known cs rest ctx = .ok body ctx' →
      ClauseSim (N := N) m fs fuel env sw known cs rest body)
    (ihSC : ∀ env s sw tags known names cs ctx body ctx',
      translateStateClauses F env s sw tags known names cs ctx = .ok body ctx' →
      StateClauseSim (N := N) m fs fuel env sw known cs body) :
    ∀ env s disc cs rest tail ctx body ctx', translateSwitch (F + 1) env s disc cs rest tail ctx = .ok body ctx' →
      StmtSim (N := N) m fs fuel env tail (.switchStmt s disc cs :: rest) body := by
  intro env s disc cs rest tail ctx body ctx' h
  unfold translateSwitch at h
  cases hsw : switchOf env disc with
  | none => simp [hsw] at h
  | some sw =>
    simp only [hsw, ite_state] at h
    split at h
    · simp at h
    rename_i hdecl
    try simp only [pure_bind, ite_state] at h
    split at h <;> (try (simp at h; done))
    rcases cs with _ | ⟨⟨_ | test, cb⟩, more⟩
    · simp at h
    · simp at h
    · simp only at h
      split at h
      · exact switch_sim m fs fuel hsw (by simpa using hdecl) (ihC _ _ _ _ _ _ _ _ _ _ h)
      · split at h
        · simp at h
        split at h
        · simp at h
        split at h
        · simp at h
        simp only [bind_ok] at h
        obtain ⟨br, s₁, hbr, rb, s₂, hrb, h⟩ := h
        simp only [pure_ok] at h
        obtain ⟨rfl, -⟩ := h
        exact switch_state_sim m fs fuel hsw (by simpa using hdecl) rfl (ihSC _ _ _ _ _ _ _ _ _ _ hbr) (ihS _ _ _ _ _ _ hrb)

/-- `translateClauses` is sound, when the statement functions are with one unit of fuel less. -/
theorem translateClauses_sound {F : Nat}
    (ihS : ∀ env tail ss ctx body ctx', translateStatements F env tail ss ctx = .ok body ctx' →
      StmtSim (N := N) m fs fuel env tail ss body)
    (ihC : ∀ env s sw tags known cs rest ctx body ctx',
      translateClauses F env s sw tags known cs rest ctx = .ok body ctx' →
      ClauseSim (N := N) m fs fuel env sw known cs rest body) :
    ∀ env s sw tags known cs rest ctx body ctx',
      translateClauses (F + 1) env s sw tags known cs rest ctx = .ok body ctx' →
      ClauseSim (N := N) m fs fuel env sw known cs rest body := by
  intro env s sw tags known cs rest ctx body ctx' h
  unfold translateClauses at h
  rcases cs with _ | ⟨⟨_ | test, cb⟩, more⟩
  · simp only [ite_state] at h
    split at h
    · simp at h
    exact clauses_nil_sim m fs fuel (ihS _ _ _ _ _ _ h)
  · cases more with
    | nil =>
      simp only [ite_state] at h
      split at h
      · simp at h
      split at h
      · simp at h
      split at h
      · simp at h
      exact clauses_default_sim m fs fuel (ihS _ _ _ _ _ _ h)
    | cons _ _ => simp at h
  · simp only at h
    generalize hst : test.stripParens = st at h
    cases st with
    | string tsp tag =>
      simp only at h
      cases hmem : sw.union.members.lookup tag with
      | none => simp [hmem] at h
      | some member =>
        simp only [hmem, ite_state] at h
        split at h
        · simp at h
        split at h
        · simp at h
        simp only [bind_ok] at h
        obtain ⟨wt, s₁, hwt, h⟩ := h
        simp only [ite_state] at h
        split at h
        · split at h <;> (try (simp at h; done))
          rename_i hknown
          split at h
          · simp at h
          split at h
          · simp at h
          simp only [pure_ok] at h
          obtain ⟨rfl, -⟩ := h
          have hk : known = some tag := by simpa using hknown
          subst hk
          exact clauses_last_sim m fs fuel (narrow_has _ _ _) rfl hst (ihS _ _ _ _ _ _ hwt)
        · simp only [bind_ok] at h
          obtain ⟨wo, s₂, hwo, h⟩ := h
          simp only [ite_state] at h
          split at h
          · simp at h
          simp only [pure_ok] at h
          obtain ⟨rfl, -⟩ := h
          exact clauses_case_sim m fs fuel (narrow_has _ _ _) rfl (narrow_has _ _ _) rfl hst
            (ihS _ _ _ _ _ _ hwt) (ihC _ _ _ _ _ _ _ _ _ _ hwo)
    | _ => simp at h


omit [JSNumber N] in
theorem throwingCall?_some {fns : List FnInfo} {e : Expr} {cs sp : Span} {name : String} {args : List Expr}
    (h : throwingCall? fns e = some (cs, sp, name, args)) : e = .call cs (.ident sp name) args := by
  unfold throwingCall? at h
  split at h
  · split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      rfl
    · simp at h
  · simp at h

/-- What `translateBindHead` checks and gives: the declaration ends the
function, the call is a translated call, and the scope after it has the
declared name. -/
theorem translateBindHead_ok {env env' : Translate.Env} {s cs sp : Span} {d : VarDecl} {tail : Tail}
    {name : String} {args : List Expr} {ctx ctx' : Ctx} {ref : DeclRef} {outs : List IR.Expr}
    (h : translateBindHead env s d tail cs sp name args ctx = .ok (ref, outs, env') ctx') :
    tail = .ret ∧ ∃ F c ctx₁ ctx₂, translateCall F env cs (.ident sp name) args true ctx₁ = .ok c ctx₂ ∧
      c.code = .call ref outs ∧ env.has d.name = false ∧
      env' = env.add { name := d.name, binding := (if d.kind == .const then .const else .«let»), type := c.type } := by
  unfold translateBindHead at h
  simp only [ite_state] at h
  split at h
  · rename_i ht
    simp only [pure_bind, bind_ok, fuelLimit_ok] at h
    obtain ⟨_, _, ⟨rfl, rfl⟩, c, s₁, hc, declared, s₂, -, h⟩ := h
    simp only [ite_state] at h
    split at h
    · cases hcode : c.code
      all_goals simp only [hcode] at h
      all_goals try (simp at h; done)
      simp only [bind_ok, pure_ok, Prod.mk.injEq] at h
      obtain ⟨env'', s₃, hdecl, ⟨rfl, rfl, rfl⟩, -⟩ := h
      obtain ⟨hfresh, rfl, -⟩ := declare_ok hdecl
      exact ⟨by cases tail <;> simp_all [Tail.isRet], _, c, _, _, hc, hcode, hfresh, rfl⟩
    · simp at h
  · simp at h

/-- What `translateReturnCall` checks and gives: the `return` ends the
function, and the call is a translated call. -/
theorem translateReturnCall_ok {env : Translate.Env} {s cs sp : Span} {tail : Tail}
    {name : String} {args : List Expr} {ctx ctx' : Ctx} {ref : DeclRef} {outs : List IR.Expr}
    (h : translateReturnCall env s tail cs sp name args ctx = .ok (ref, outs) ctx') :
    tail = .ret ∧ ∃ F c ctx₁ ctx₂, translateCall F env cs (.ident sp name) args true ctx₁ = .ok c ctx₂ ∧
      c.code = .call ref outs := by
  unfold translateReturnCall at h
  simp only [ite_state] at h
  split at h
  · rename_i ht
    simp only [pure_bind, bind_ok, get_ok, fuelLimit_ok] at h
    obtain ⟨_, _, ⟨rfl, rfl⟩, _, _, ⟨rfl, rfl⟩, c, s₁, hc, h⟩ := h
    simp only [ite_state] at h
    split at h
    · cases hcode : c.code
      all_goals simp only [hcode] at h
      all_goals try (simp at h; done)
      simp only [pure_ok, Prod.mk.injEq] at h
      obtain ⟨⟨rfl, rfl⟩, -⟩ := h
      exact ⟨by cases tail <;> simp_all [Tail.isRet], _, c, _, _, hc, hcode⟩
    · simp at h
  · simp at h

/-- The call of a translated call that `CallSim` covers returns or throws what
the source's call does. -/
theorem translateCall_callSim (hc : CallsAgree (N := N) m.program fs fuel) {F : Nat} {env : Translate.Env}
    {cs sp : Span} {name : String} {args : List Expr} {ctx₁ ctx₂ : Ctx} {c : Code} {ref : DeclRef}
    {outs : List IR.Expr} (h : translateCall F env cs (.ident sp name) args true ctx₁ = .ok c ctx₂)
    (hcode : c.code = .call ref outs) :
    ∀ (ρs ρo : Eval.Env N) r, Agree ρs ρo → Scoped m env ρs →
      IR.Expr.evalCall fs fuel ρo ref outs = some r → Eval.evalCall m fuel ρs name args = some r := by
  obtain ⟨sp', name', he, hcall⟩ := ((expr_sound m fs fuel hc F).2.2.2.1 _ _ _ _ _ _ _ _ h).2 ref outs hcode
  injection he with _ hn
  subst hn
  exact hcall

/-- `const x = f(a)` where `f` can throw, at the end of a function: the output
passes the error of the call on, and binds `x` to its value otherwise. -/
theorem bind_sim {env env' : Translate.Env} {s cs sp : Span} {d : VarDecl} {name : String} {args : List Expr}
    {rest : List Stmt} {ref : DeclRef} {outs : List IR.Expr} {rb : IR.Body} {b : Binding} {ty : Ty}
    (hinit : d.init = some (.call cs (.ident sp name) args))
    (hconst : (Stmt.varDecl s d).constAssignedIn rest = false) (hfresh : env.has d.name = false)
    (henv : env' = env.add { name := d.name, binding := b, type := ty })
    (hcall : ∀ (ρs ρo : Eval.Env N) r, Agree ρs ρo → Scoped m env ρs →
      IR.Expr.evalCall fs fuel ρo ref outs = some r → Eval.evalCall m fuel ρs name args = some r)
    (hrest : StmtSim (N := N) m fs fuel env' .ret rest rb) :
    StmtSim (N := N) m fs fuel env .ret (.varDecl s d :: rest) (.bind d.name ref outs rb) := by
  subst henv
  obtain ⟨kind, x, type, init?⟩ := d
  simp only at hinit hfresh ⊢
  subst hinit
  intro ρs ρo ha hs
  have ha' : ∀ w, Agree ((x, w) :: ρs) ((x, w) :: ρo) := fun w y => by
    simp only [List.lookup]; split
    · rfl
    · exact ha y
  have hs' : ∀ w, Scoped m (env.add { name := x, binding := b, type := ty }) ((x, w) :: ρs) :=
    fun w => ⟨fun y => by
    rw [has_add, ← hs.1 y]
    simp only [List.lookup]
    by_cases hy : y = x
    · subst hy; simp
    · have h1 : (y == x) = false := by simpa using hy
      have h2 : (x == y) = false := by simpa using Ne.symm hy
      simp [h1, h2], hs.2⟩
  constructor
  · intro v hv
    simp only [IR.Body.exec] at hv
    cases hr : IR.Expr.evalCall fs fuel ρo ref outs with
    | none => simp [hr] at hv
    | some r =>
      have hsc := hcall ρs ρo r ha hs hr
      cases r with
      | error t =>
        simp only [hr, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hv
        cases hv
        simp [Eval.exec, Eval.execStmt, evalTop_call, hsc, hconst]
      | ok w =>
        simp only [hr, Option.bind_eq_bind, Option.bind_some] at hv
        have := (hrest _ _ (ha' w) (hs' w)).1 v hv
        simp [Eval.exec, Eval.execStmt, evalTop_call, hsc, hconst, this]
  · intro brk ρo' hv
    simp only [IR.Body.exec] at hv
    cases hr : IR.Expr.evalCall fs fuel ρo ref outs with
    | none => simp [hr] at hv
    | some r =>
      cases r with
      | error t => cases brk <;> simp [hr, endOf] at hv
      | ok w =>
        simp only [hr, Option.bind_eq_bind, Option.bind_some] at hv
        exact absurd ((hrest _ _ (ha' w) (hs' w)).2 brk ρo' hv).1 (by simp [Tail.isRet])

/-- `return f(a)` where `f` can throw: the output returns or throws what the
call returns or throws. -/
theorem returnCall_sim {env : Translate.Env} {s cs sp : Span} {name : String} {args : List Expr}
    {ref : DeclRef} {outs : List IR.Expr}
    (hcall : ∀ (ρs ρo : Eval.Env N) r, Agree ρs ρo → Scoped m env ρs →
      IR.Expr.evalCall fs fuel ρo ref outs = some r → Eval.evalCall m fuel ρs name args = some r) :
    StmtSim (N := N) m fs fuel env .ret [.returnStmt s (some (.call cs (.ident sp name) args))]
      (.bind "r" ref outs (.value (IR.Expr.pure (.var "r")))) := by
  intro ρs ρo ha hs
  have hout : ∀ o, IR.Body.exec fs fuel ρo (.bind "r" ref outs (.value (IR.Expr.pure (.var "r")))) = some o →
      ∃ r, o = .ret r ∧ IR.Expr.evalCall fs fuel ρo ref outs = some r := by
    intro o ho
    simp only [IR.Body.exec] at ho
    cases hr : IR.Expr.evalCall fs fuel ρo ref outs with
    | none => simp [hr] at ho
    | some r =>
      cases r <;> simp [hr, IR.Expr.eval, IR.Expr.evalList, IR.ExprExt.apply, List.lookup] at ho <;>
        exact ⟨_, ho.symm, rfl⟩
  constructor
  · intro v hv
    obtain ⟨r, hr, he⟩ := hout _ hv
    cases hr
    rw [exec_single]
    simp [Eval.execStmt, evalTop_call, hcall ρs ρo _ ha hs he]
  · intro brk ρo' hv
    obtain ⟨r, hr, -⟩ := hout _ hv
    cases brk <;> simp [endOf] at hr

/-- `throw new Error(m)`: the output throws the error that the source's
`new Error(m)` makes. -/
theorem throw_sim {env : Translate.Env} {s sn : Span} {msg : Expr} {code : IR.Expr}
    (hsim : Sim (N := N) m fs fuel env msg code) (herr : env.has "Error" = false) :
    StmtSim (N := N) m fs fuel env .ret [.throwStmt s (.new sn "Error" [] [msg])] (.throw (IR.Expr.error code)) := by
  intro ρs ρo ha hs
  have hout : ∀ o, IR.Body.exec fs fuel ρo (.throw (IR.Expr.error code)) = some o →
      ∃ t, o = .ret (.error (.error "Error" [("message", .str t)])) ∧
        IR.Expr.eval fs fuel ρo code = some (.str t) := by
    intro o ho
    simp only [IR.Body.exec, IR.Expr.eval, IR.Expr.evalList] at ho
    cases hm : IR.Expr.eval fs fuel ρo code with
    | none => simp [hm] at ho
    | some w =>
      cases w <;> simp [hm, IR.ExprExt.apply] at ho
      exact ⟨_, ho.symm, rfl⟩
  constructor
  · intro v hv
    obtain ⟨t, ho, hm⟩ := hout _ hv
    cases ho
    rw [exec_single]
    simp [Eval.execStmt, Eval.eval, hs.none herr, hsim ρs ρo _ ha hs hm]
  · intro brk ρo' hv
    obtain ⟨t, ho, -⟩ := hout _ hv
    cases brk <;> simp [endOf] at ho

omit [JSNumber N] in
theorem lookup_isSome_zip {x : String} :
    ∀ {names : List String} {ws : List (Val N)}, ws.length = names.length →
      ((names.zip ws).lookup x).isSome = names.contains x
  | [], _, _ => by simp
  | _ :: _, [], h => by simp at h
  | n :: names, w :: ws, h => by
    simp only [List.zip_cons_cons, List.lookup, List.contains_cons]
    by_cases hx : x = n
    · subst hx; simp
    · have h1 : (x == n) = false := by simpa using hx
      simp only [h1, Bool.false_or]
      exact lookup_isSome_zip (by simpa using h)

omit [JSNumber N] in
theorem lookup_isSome_append {x : String} (a b : Eval.Env N) :
    ((a ++ b).lookup x).isSome = ((a.lookup x).isSome || (b.lookup x).isSome) := by
  induction a with
  | nil => simp
  | cons p a ih =>
    obtain ⟨k, v⟩ := p
    simp only [List.cons_append, List.lookup]
    split <;> simp_all

omit [JSNumber N] in
theorem lookup_isSome_reverse {x : String} (a : Eval.Env N) :
    (a.reverse.lookup x).isSome = (a.lookup x).isSome := by
  induction a with
  | nil => simp
  | cons p a ih =>
    obtain ⟨k, v⟩ := p
    rw [List.reverse_cons, lookup_isSome_append, ih]
    simp only [List.lookup]
    split <;> simp_all

theorem evalList_append_inv {a b : List IR.Expr} {ρo : Eval.Env N} {ws : List (Val N)} :
    IR.Expr.evalList fs fuel ρo (a ++ b) = some ws →
      ∃ w₁ w₂, ws = w₁ ++ w₂ ∧ IR.Expr.evalList fs fuel ρo a = some w₁ ∧
        IR.Expr.evalList fs fuel ρo b = some w₂ ∧ w₁.length = a.length := by
  induction a generalizing ws with
  | nil => intro h; exact ⟨[], ws, rfl, by simp [IR.Expr.evalList], h, rfl⟩
  | cons e a ih =>
    intro h
    simp only [List.cons_append, IR.Expr.evalList] at h
    cases he : IR.Expr.eval fs fuel ρo e with
    | none => simp [he] at h
    | some w =>
      cases hr : IR.Expr.evalList fs fuel ρo (a ++ b) with
      | none => simp [he, hr] at h
      | some rs =>
        simp [he, hr] at h
        subst h
        obtain ⟨w₁, w₂, rfl, h₁, h₂, hl⟩ := ih hr
        exact ⟨w :: w₁, w₂, rfl, by simp [IR.Expr.evalList, he, h₁], h₂, by simp [hl]⟩

/-! ### Local functions: what the translator checks -/

theorem localCall?_some {env : Translate.Env} {e : Expr} {args : List Expr} {fn : LocalFn}
    (h : localCall? env e = some (args, fn)) :
    ∃ cs sp, e = .call cs (.ident sp fn.name) args ∧ env.localFns.find? (·.name == fn.name) = some fn := by
  unfold localCall? at h
  split at h
  · rename_i cs sp name args'
    simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨fn', hf, rfl, rfl⟩ := h
    have := List.find?_some hf
    have hn : fn'.name = name := by simpa using this
    subst hn
    exact ⟨cs, sp, rfl, hf⟩
  · simp at h

theorem fnChanges_lookup {env : Translate.Env} {fn : LocalFn}
    (h : env.localFns.find? (·.name == fn.name) = some fn) : env.fnChanges.lookup fn.name = some fn.changes := by
  unfold Env.fnChanges
  generalize env.localFns = fns at h
  induction fns with
  | nil => simp at h
  | cons f fns ih =>
    simp only [List.find?_cons] at h
    simp only [List.map_cons, List.lookup_cons]
    split at h
    · rename_i hf
      simp only [Option.some.injEq] at h
      subst h
      simp
    · rename_i hf
      have hne : (fn.name == f.name) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]
        intro he; simp [he] at hf
      simp only [hne]
      exact ih h

theorem withLocalBody_ok {ret : Ty} {x : TM IR.Body} {ctx ctx' : Ctx} {b : IR.Body}
    (h : withLocalBody ret x ctx = .ok b ctx') : ∃ c₁ c₂, x c₁ = .ok b c₂ := by
  simp only [withLocalBody, bind_ok, get_ok, modify_ok, pure_ok] at h
  obtain ⟨_, _, ⟨rfl, rfl⟩, _, _, rfl, b', c₂, hx, _, _, rfl, rfl, -⟩ := h
  exact ⟨_, _, hx⟩

/-- The facts that a call of a local function needs. -/
theorem localCallProblem_none {env : Translate.Env} {fn : LocalFn} {args : List Expr}
    (h : localCallProblem env fn args = none) :
    (∃ sp ss, fn.body = .block sp ss) ∧
    (fn.captured.all fun l => fn.body.mentions l.name && (env.lookup l.name).any (·.type == l.type) &&
      !fn.params.any (·.name == l.name)) = true ∧
    env.locals.any fn.late = false ∧
    (fn.changes.all (fun c => fn.captured.any (·.name == c)) &&
      fn.captured.all (fun l => fn.changes.contains l.name ||
        !(stmtsChanges [] (blockStatements fn.body)).contains l.name)) = true ∧
    (fn.ret.isSome && fn.captured.any (fun l => fn.body.assigns l.name || fn.body.mutates l.name)) = false ∧
    args.length = fn.params.length := by
  unfold localCallProblem at h
  by_cases h0 : isBlockBody fn.body = true
  · rw [if_neg (by rw [h0]; decide)] at h
    by_cases h1 : (fn.captured.all fun l => fn.body.mentions l.name && (env.lookup l.name).any (·.type == l.type) &&
        !fn.params.any (·.name == l.name)) = true
    · rw [if_neg (by rw [h1]; decide)] at h
      by_cases h2 : env.locals.any fn.late = true
      · rw [if_pos h2] at h; simp at h
      rw [if_neg h2] at h
      by_cases h3 : (fn.changes.all (fun c => fn.captured.any (·.name == c)) &&
          fn.captured.all (fun l => fn.changes.contains l.name ||
            !(stmtsChanges [] (blockStatements fn.body)).contains l.name)) = true
      · rw [if_neg (by rw [h3]; decide)] at h
        by_cases h4 : (fn.ret.isSome && fn.captured.any (fun l => fn.body.assigns l.name || fn.body.mutates l.name)) = true
        · rw [if_pos h4] at h; simp at h
        rw [if_neg h4] at h
        by_cases h5 : (args.length != fn.params.length) = true
        · rw [if_pos h5] at h; simp at h
        have hblk : ∃ sp ss, fn.body = .block sp ss := by
          revert h0; cases fn.body <;> simp [isBlockBody]
        exact ⟨hblk, h1, Bool.eq_false_iff.mpr h2, h3, Bool.eq_false_iff.mpr h4, by simpa using h5⟩
      · rw [if_pos (by rw [Bool.eq_false_iff.mpr h3]; rfl)] at h; simp at h
    · rw [if_pos (by rw [Bool.eq_false_iff.mpr h1]; rfl)] at h; simp at h
  · rw [if_pos (by rw [Bool.eq_false_iff.mpr h0]; rfl)] at h; simp at h

/-- What `translateLocalCall` checks and gives. -/
theorem translateLocalCall_ok {env : Translate.Env} {s : Span} {fn : LocalFn} {args : List Expr}
    {body : TM IR.Body} {ctx ctx' : Ctx} {b : IR.Body} {outs : List IR.Expr}
    (h : translateLocalCall env s fn args body ctx = .ok (b, outs) ctx') :
    localCallProblem env fn args = none ∧ (∃ c₁ c₂, body c₁ = .ok b c₂) ∧
    ∃ outs' c₁ c₂, translateLocalArgs env fn.params args c₁ = .ok outs' c₂ ∧
      outs = fn.captured.map (fun l => IR.Expr.var l.name) ++ outs' := by
  unfold translateLocalCall at h
  cases hp : localCallProblem env fn args with
  | some why => simp [hp] at h
  | none =>
    simp only [hp, pure_bind, bind_ok] at h
    obtain ⟨outs', c₂, ho, b', c₃, hb, h⟩ := h
    simp only [ite_state] at h
    split at h
    · simp only [pure_ok, Prod.mk.injEq] at h
      obtain ⟨⟨rfl, rfl⟩, -⟩ := h
      obtain ⟨c₄, c₅, hx⟩ := withLocalBody_ok hb
      exact ⟨rfl, ⟨_, _, hx⟩, outs', _, _, ho, rfl⟩
    · simp at h


/-- The arguments of a call of a local function mean what the source's
arguments mean. -/
theorem translateLocalArgs_sim (hc : CallsAgree (N := N) m.program fs fuel) {env : Translate.Env} :
    ∀ (ps : List Local) (args : List Expr) (ctx : Ctx) (outs : List IR.Expr) (ctx' : Ctx),
      args.length = ps.length → translateLocalArgs env ps args ctx = .ok outs ctx' →
      SimList (N := N) m fs fuel env args outs
  | [], [], _, outs, _, _, h => by
    simp only [translateLocalArgs, pure_ok] at h
    obtain ⟨rfl, -⟩ := h
    intro ρs ρo vs _ _ hv
    simp [IR.Expr.evalList] at hv
    subst hv; simp [Eval.evalList]
  | p :: ps, a :: as, ctx, outs, ctx', hlen, h => by
    simp only [translateLocalArgs, bind_ok, fuelLimit_ok, ite_state] at h
    obtain ⟨_, _, ⟨rfl, rfl⟩, code, s₁, hcode, h⟩ := h
    split at h
    rotate_left
    · simp at h
    simp only [bind_ok, pure_ok] at h
    obtain ⟨_, _, ⟨-, rfl⟩, outs', s₂, hrest, hout, -⟩ := h
    subst hout
    have hsim := (expr_sound m fs fuel hc _).1 _ _ _ _ _ _ hcode
    have ih := translateLocalArgs_sim hc ps as _ _ _ (by simpa using hlen) hrest
    intro ρs ρo vs ha hs hv
    simp only [IR.Expr.evalList] at hv
    cases hx : IR.Expr.eval fs fuel ρo (withType code.value p.type code.type) with
    | none => simp [hx] at hv
    | some x =>
      cases hxs : IR.Expr.evalList fs fuel ρo outs' with
      | none => simp [hx, hxs] at hv
      | some xs =>
        simp [hx, hxs] at hv
        subst hv
        rw [eval_withType, eval_value] at hx
        simp [Eval.evalList, hsim ρs ρo x ha hs hx, ih ρs ρo xs ha hs hxs]
  | [], _ :: _, _, _, _, hlen, _ | _ :: _, [], _, _, _, hlen, _ => by simp at hlen


/-! ### Local functions: the spec's call -/

omit [JSNumber N] in
theorem lookup_captures (ρ : Eval.Env N) (ps : List String) (body : Stmt) (n : String) :
    (Eval.captures ρ ps body).lookup n =
      if (body.mentions n && !ps.contains n) = true then ρ.lookup n else none := by
  unfold Eval.captures
  induction ρ with
  | nil => simp
  | cons p ρ ih =>
    obtain ⟨k, v⟩ := p
    by_cases hk : (body.mentions k && !ps.contains k) = true
    · simp only [List.filter_cons, hk, ↓reduceIte, List.lookup_cons, ih]
      by_cases hn : n = k
      · subst hn; simp only [beq_self_eq_true, if_pos hk]
      · have : (n == k) = false := by simpa using hn
        simp [this]
    · simp only [List.filter_cons, hk, Bool.false_eq_true, ↓reduceIte, ih, List.lookup_cons]
      by_cases hn : n = k
      · subst hn; rw [if_neg hk, if_neg hk]
      · have : (n == k) = false := by simpa using hn
        simp [this]

omit [JSNumber N] in
theorem Env.set_none {ρ : Eval.Env N} {n : String} {v : Val N} (h : ρ.lookup n = none) : ρ.set n v = ρ := by
  induction ρ with
  | nil => rfl
  | cons p ρ ih =>
    obtain ⟨k, w⟩ := p
    by_cases hk : k = n
    · subst hk; simp at h
    · have h2 : (n == k) = false := by simpa using Ne.symm hk
      simp [Eval.Env.set_cons, hk, ih (by simpa [List.lookup, h2] using h)]

omit [JSNumber N] in
theorem lookup_set (ρ : Eval.Env N) (k n : String) (v : Val N) :
    (ρ.set k v).lookup n = if n = k ∧ (ρ.lookup k).isSome then some v else ρ.lookup n := by
  by_cases hn : n = k
  · subst hn
    cases hl : ρ.lookup n with
    | none => simp [Env.set_none hl, hl]
    | some w => rw [Eval.Env.lookup_set_same _ _ _ (by rw [hl]; rfl)]; simp
  · simp [hn, Eval.Env.lookup_set_ne _ _ _ _ (Ne.symm hn)]

/-- One step of `writeBack`. -/
abbrev writeStep (after : Eval.Env N) (e : Eval.Env N) (p : String × Val N) : Eval.Env N :=
  match after.lookup p.1 with
  | some v => e.set p.1 v
  | none => e

omit [JSNumber N] in
theorem lookup_foldl_writeStep (after : Eval.Env N) (n : String) :
    ∀ (L e : Eval.Env N), (L.foldl (writeStep after) e).lookup n =
      if n ∈ L.map (·.1) ∧ (after.lookup n).isSome ∧ (e.lookup n).isSome then after.lookup n else e.lookup n
  | [], e => by simp
  | (k, w) :: L, e => by
    rw [List.foldl_cons, lookup_foldl_writeStep after n L]
    have hs : ((writeStep after e (k, w)).lookup n).isSome = (e.lookup n).isSome := by
      simp only [writeStep]
      split
      · rw [lookup_set]; split <;> simp_all
      · rfl
    rw [hs]
    by_cases hnk : n = k
    · subst hnk
      cases ha : after.lookup n with
      | none => simp [writeStep, ha]
      | some v =>
        cases he : e.lookup n with
        | none => simp [writeStep, ha, he, lookup_set]
        | some u => simp [writeStep, ha, he, lookup_set]
    · have hw : (writeStep after e (k, w)).lookup n = e.lookup n := by
        simp only [writeStep]; split
        · rw [lookup_set]; simp [hnk]
        · rfl
      simp only [hw, List.map_cons, List.mem_cons, hnk, false_or]

theorem lookup_isSome_of_mem {β : Type} {k : String} {v : β} :
    ∀ {l : List (String × β)}, (k, v) ∈ l → (l.lookup k).isSome
  | (j, w) :: l, h => by
    by_cases hj : k = j
    · subst hj; simp
    · have : (k == j) = false := by simpa using hj
      simp only [List.lookup_cons, this]
      rcases List.mem_cons.mp h with h | h
      · simp at h; exact absurd h.1 hj
      · exact lookup_isSome_of_mem h

theorem mem_of_lookup {β : Type} {k : String} {v : β} :
    ∀ {l : List (String × β)}, l.lookup k = some v → (k, v) ∈ l
  | [], h => by simp at h
  | (j, w) :: l, h => by
    by_cases hj : k = j
    · subst hj; simp at h; subst h; simp
    · have : (k == j) = false := by simpa using hj
      simp only [List.lookup_cons, this] at h
      exact List.mem_cons_of_mem _ (mem_of_lookup h)

omit [JSNumber N] in
theorem lookup_writeBack (ρ after : Eval.Env N) (ps : List String) (body : Stmt) (n : String) :
    (Eval.writeBack ρ after ps body).lookup n =
      if (body.mentions n && !ps.contains n) = true ∧ (after.lookup n).isSome ∧ (ρ.lookup n).isSome then
        after.lookup n else ρ.lookup n := by
  have h := lookup_foldl_writeStep after n (Eval.captures ρ ps body) ρ
  unfold Eval.writeBack
  change (List.foldl (writeStep after) ρ (Eval.captures ρ ps body)).lookup n = _
  rw [h]
  have hmem : n ∈ (Eval.captures ρ ps body).map (·.1) ↔
      (body.mentions n && !ps.contains n) = true ∧ (ρ.lookup n).isSome := by
    constructor
    · intro hm
      obtain ⟨⟨k, v⟩, hp, rfl⟩ := List.mem_map.mp hm
      unfold Eval.captures at hp
      obtain ⟨hp, hk⟩ := List.mem_filter.mp hp
      exact ⟨hk, lookup_isSome_of_mem hp⟩
    · rintro ⟨hm, hs⟩
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hs
      have := lookup_captures ρ ps body n
      rw [hm, if_pos rfl, hv] at this
      exact List.mem_map.mpr ⟨(n, v), mem_of_lookup this, rfl⟩
  simp only [hmem]
  by_cases h1 : (body.mentions n && !ps.contains n) = true <;> by_cases h2 : (after.lookup n).isSome = true <;>
    by_cases h3 : (ρ.lookup n).isSome = true <;> simp [h2, h3]

omit [JSNumber N] in
theorem frame_foldl_writeStep {c : List String} {ρ after : Eval.Env N} {P : String → Prop}
    (h : ∀ n, n ∉ c → P n → ∀ v, after.lookup n = some v → (ρ.lookup n).isSome = true → ρ.lookup n = some v) :
    ∀ (L e : Eval.Env N), (∀ p ∈ L, P p.1 ∧ (ρ.lookup p.1).isSome = true) → Frame c e ρ →
      Frame c (L.foldl (writeStep after) e) ρ
  | [], _, _, he => he
  | (k, w) :: L, e, hL, he => by
    rw [List.foldl_cons]
    refine frame_foldl_writeStep h L _ (fun p hp => hL p (List.mem_cons_of_mem _ hp)) ?_
    simp only [writeStep]
    split
    · rename_i v hv
      by_cases hk : k ∈ c
      · exact ((Frame.set hk e).trans he).mono fun n hn => by simpa using hn
      · have hkL := hL (k, w) (by simp)
        have hρ := h k hk hkL.1 v hv hkL.2
        rw [Eval.Env.set_of_lookup e k v (by rw [he.lookup hk, hρ])]
        exact he
    · exact he

omit [JSNumber N] in
theorem frame_writeBack {c : List String} {ρ after : Eval.Env N} {ps : List String} {body : Stmt}
    (h : ∀ n, n ∉ c → (body.mentions n && !ps.contains n) = true → ∀ v, after.lookup n = some v →
      (ρ.lookup n).isSome = true → ρ.lookup n = some v) :
    Frame c (Eval.writeBack ρ after ps body) ρ := by
  unfold Eval.writeBack
  change Frame c (List.foldl (writeStep after) ρ (Eval.captures ρ ps body)) ρ
  refine frame_foldl_writeStep (P := fun n => (body.mentions n && !ps.contains n) = true) h _ ρ
    (fun p hp => ?_) (Frame.refl c ρ)
  unfold Eval.captures at hp
  exact ⟨(List.mem_filter.mp hp).2, lookup_isSome_of_mem (List.mem_filter.mp hp).1⟩

omit [JSNumber N] in
theorem lookup_of_all {L : Eval.Env N} {ρ : Eval.Env N} (h : ∀ p ∈ L, ρ.lookup p.1 = some p.2) (n : String) :
    L.lookup n = if (L.lookup n).isSome then ρ.lookup n else none := by
  cases hl : L.lookup n with
  | none => simp
  | some v => simp [h (n, v) (mem_of_lookup hl)]

theorem find_name_isSome (l : List Local) (n : String) :
    (l.find? (·.name == n)).isSome = (l.map (·.name)).contains n := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    by_cases hx : x.name = n
    · simp [hx]
    · have : (x.name == n) = false := by simpa using hx
      simp only [List.find?_cons, this, List.map_cons, List.contains_cons, ih]
      simp [Ne.symm hx]


theorem evalList_vars {ρo : Eval.Env N} :
    ∀ {names : List String} {cvals : List (Val N)},
      IR.Expr.evalList fs fuel ρo (names.map IR.Expr.var) = some cvals →
        cvals.length = names.length ∧ ∀ p ∈ names.zip cvals, ρo.lookup p.1 = some p.2
  | [], cvals, h => by simp [IR.Expr.evalList] at h; subst h; simp
  | n :: names, cvals, h => by
    simp only [List.map_cons, IR.Expr.evalList, IR.Expr.eval] at h
    cases hn : ρo.lookup n with
    | none => simp [hn] at h
    | some v =>
      cases hr : IR.Expr.evalList fs fuel ρo (names.map IR.Expr.var) with
      | none => simp [hn, hr] at h
      | some vs =>
        simp [hn, hr] at h
        subst h
        obtain ⟨hl, hall⟩ := evalList_vars hr
        refine ⟨by simp [hl], fun p hp => ?_⟩
        simp only [List.zip_cons_cons, List.mem_cons] at hp
        rcases hp with rfl | hp
        · exact hn
        · exact hall p hp

/-- The environment in which the spec runs the body of a local function, and
the one in which the output runs the lifted function, give every name the
same value, and the first binds the names that the body's scope has. -/
theorem localBody_env {env : Translate.Env} {fn : LocalFn} {ρs ρo : Eval.Env N} {vs cvals : List (Val N)}
    (h1 : (fn.captured.all fun l => fn.body.mentions l.name && (env.lookup l.name).any (·.type == l.type)) = true)
    (h2 : env.locals.any (fun l => fn.body.mentions l.name &&
      !(fn.captured.any (·.name == l.name) || fn.params.any (·.name == l.name))) = false)
    (ha : Agree ρs ρo) (hs : Scoped m env ρs)
    (hcv : IR.Expr.evalList fs fuel ρo (fn.captured.map (fun l => IR.Expr.var l.name)) = some cvals)
    (hlen : vs.length = fn.params.length) :
    Agree (((fn.params.map (·.name)).zip vs).reverse ++ Eval.captures ρs (fn.params.map (·.name)) fn.body)
        (((fn.leanParams.map (·.1)).zip (cvals ++ vs)).reverse) ∧
      Scoped m (fn.bodyEnv env) (((fn.params.map (·.name)).zip vs).reverse ++ Eval.captures ρs (fn.params.map (·.name)) fn.body) := by
  have hcv' : IR.Expr.evalList fs fuel ρo ((fn.captured.map (·.name)).map IR.Expr.var) = some cvals := by
    simpa [List.map_map, Function.comp_def] using hcv
  obtain ⟨hcl, hcall⟩ := evalList_vars fs fuel hcv'
  have hzip : ((fn.leanParams.map (·.1)).zip (cvals ++ vs)).reverse =
      ((fn.params.map (·.name)).zip vs).reverse ++ ((fn.captured.map (·.name)).zip cvals).reverse := by
    simp only [LocalFn.leanParams, List.map_map, List.map_append]
    rw [List.zip_append (by simpa [Function.comp_def] using hcl.symm), List.reverse_append]
    simp [Function.comp_def]
  rw [hzip]
  simp only [List.all_eq_true, Bool.and_eq_true] at h1
  have h2' : ∀ l ∈ env.locals, fn.body.mentions l.name = true →
      (fn.captured.any (·.name == l.name) || fn.params.any (·.name == l.name)) = true := by
    intro l hl hm
    have := List.any_eq_false.mp h2 l hl
    simp only [hm, Bool.true_and, Bool.not_eq_eq_eq_not, Bool.not_true] at this
    cases h : (fn.captured.any (·.name == l.name) || fn.params.any (·.name == l.name)) <;> simp_all
  -- For a name that is not a parameter, both sides look in what the body captures.
  have hrest : ∀ n, n ∉ fn.params.map (·.name) →
      (Eval.captures ρs (fn.params.map (·.name)) fn.body).lookup n = (((fn.captured.map (·.name)).zip cvals).reverse).lookup n := by
    intro n hnp
    rw [lookup_captures]
    have hL : ∀ p ∈ ((fn.captured.map (·.name)).zip cvals).reverse, ρo.lookup p.1 = some p.2 :=
      fun p hp => hcall p (List.mem_reverse.mp hp)
    rw [lookup_of_all hL n, lookup_isSome_reverse, lookup_isSome_zip hcl]
    by_cases hnc : n ∈ fn.captured.map (·.name)
    · have hpc : (fn.params.map (·.name)).contains n = false := by simpa using hnp
      obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hnc
      simp only [hnc, (h1 l hl).1, Bool.true_and, hpc, Bool.not_false, ↓reduceIte, ha l.name,
        List.contains_iff_mem]
    · have hcf : (fn.captured.map (·.name)).contains n = false := by simpa using hnc
      rw [hcf]
      simp only [Bool.false_eq_true, ↓reduceIte, ite_eq_right_iff]
      intro hm'
      have hm : fn.body.mentions n = true := by simp only [Bool.and_eq_true] at hm'; exact hm'.1
      cases hlk : ρs.lookup n with
      | none => rfl
      | some w =>
        exfalso
        have hhas : env.has n = true := by rw [← hs.1 n, hlk]; rfl
        simp only [Translate.Env.has, Translate.Env.lookup, Option.isSome_iff_exists] at hhas
        obtain ⟨l, hl⟩ := hhas
        have hln := List.find?_some hl
        simp only [beq_iff_eq] at hln
        subst hln
        have := h2' l (List.mem_of_find?_eq_some hl) hm
        simp only [Bool.or_eq_true, List.any_eq_true, beq_iff_eq] at this
        rcases this with ⟨l', hl', he⟩ | ⟨l', hl', he⟩
        · exact hnc (List.mem_map.mpr ⟨l', hl', he⟩)
        · exact hnp (List.mem_map.mpr ⟨l', hl', he⟩)
  refine ⟨fun n => ?_, fun n => ?_, ?_⟩
  · simp only [List.lookup_append]
    cases hp : (((fn.params.map (·.name)).zip vs).reverse).lookup n with
    | some w => rfl
    | none =>
      have hnp : n ∉ fn.params.map (·.name) := by
        intro hn
        have := lookup_isSome_reverse (N := N) (x := n) ((fn.params.map (·.name)).zip vs)
        rw [hp, lookup_isSome_zip (by simpa using hlen)] at this
        simp [hn] at this
      simp [hrest n hnp]
  · rw [lookup_isSome_append, lookup_isSome_reverse, lookup_isSome_zip (by simpa using hlen)]
    have hhas : (fn.bodyEnv env).has n =
        ((fn.params.map (·.name)).contains n || (fn.captured.map (·.name)).contains n) := by
      simp only [Translate.Env.has, Translate.Env.lookup, LocalFn.bodyEnv, find_name_isSome, List.map_append,
        List.contains_append]
    rw [hhas]
    cases hp : (fn.params.map (·.name)).contains n with
    | true => rfl
    | false =>
      have hnp : n ∉ fn.params.map (·.name) := by simpa using hp
      rw [hrest n hnp, lookup_isSome_reverse, lookup_isSome_zip hcl]
  · exact hs.2

/-- What the output's lifted call does. -/
theorem exec_letCall {names : List String} {ref : DeclRef} {g : String} {value : IR.Expr}
    {params : List (String × IR.Ty)} {ret : IR.Ty} {returns : Bool} {body rest : IR.Body} {args : List IR.Expr}
    {ρo : Eval.Env N} {o : Outcome N}
    (h : IR.Body.exec fs fuel ρo (.letCall names ref g value params ret returns body args rest) = some o) :
    ∃ ps b0 vsAll k inner ρo₂, IR.Expr.eval fs fuel ρo value = some (.closure ps b0) ∧
      ρo.lookup g = some (.closure ps b0) ∧ IR.Expr.evalList fs fuel ρo args = some vsAll ∧
      fuel = k + 1 ∧ params.length = vsAll.length ∧
      ((returns = false ∧ IR.Body.exec fs k ((params.map (·.1)).zip vsAll).reverse body = some (.normal inner)) ∨
        (returns = true ∧ ∃ w, IR.Body.exec fs k ((params.map (·.1)).zip vsAll).reverse body = some (.ret (.ok w)) ∧
          IR.callResult names w = some inner)) ∧
      IR.bindState names inner ρo = some ρo₂ ∧ IR.Body.exec fs fuel ρo₂ rest = some o := by
  simp only [IR.Body.exec] at h
  cases hv : IR.Expr.eval fs fuel ρo value with
  | none => simp [hv] at h
  | some v =>
    cases v
    all_goals try (simp [hv] at h; done)
    rename_i ps b0
    cases hg : ρo.lookup g with
    | none => simp [hv, hg] at h
    | some u =>
      cases u
      all_goals try (simp [hv, hg] at h; done)
      rename_i ps' b'
      by_cases hpb : (ps == ps' && b0 == b') = true
      · simp only [Bool.and_eq_true, beq_iff_eq] at hpb
        obtain ⟨rfl, rfl⟩ := hpb
        cases hvs : IR.Expr.evalList fs fuel ρo args with
        | none => simp [hv, hg, hvs] at h
        | some vsAll =>
          cases fuel with
          | zero => simp [hv, hg, hvs] at h
          | succ k =>
            by_cases hl : params.length = vsAll.length
            · cases hb : IR.Body.exec fs k ((params.map (·.1)).zip vsAll).reverse body with
              | none => cases returns <;> simp [hv, hg, hvs, hl, hb] at h
              | some ob =>
                cases returns with
                | false =>
                  cases ob with
                  | normal inner =>
                    cases hbs : IR.bindState names inner ρo with
                    | none => simp [hv, hg, hvs, hl, hb, hbs] at h
                    | some ρo₂ =>
                      simp [hv, hg, hvs, hl, hb, hbs] at h
                      exact ⟨ps, b0, vsAll, k, inner, ρo₂, rfl, rfl, rfl, rfl, hl, .inl ⟨rfl, hb⟩, hbs, h⟩
                  | ret _ | brk _ | cont _ => simp [hv, hg, hvs, hl, hb] at h
                | true =>
                  cases ob with
                  | ret r =>
                    cases r with
                    | error t => simp [hv, hg, hvs, hl, hb] at h
                    | ok w =>
                      cases hcr : IR.callResult names w with
                      | none => simp [hv, hg, hvs, hl, hb, hcr] at h
                      | some inner =>
                        cases hbs : IR.bindState names inner ρo with
                        | none => simp [hv, hg, hvs, hl, hb, hcr, hbs] at h
                        | some ρo₂ =>
                          simp [hv, hg, hvs, hl, hb, hcr, hbs] at h
                          exact ⟨ps, b0, vsAll, k, inner, ρo₂, rfl, rfl, rfl, rfl, hl, .inr ⟨rfl, w, hb, hcr⟩,
                            hbs, h⟩
                  | normal _ | brk _ | cont _ => simp [hv, hg, hvs, hl, hb] at h
            · simp [hv, hg, hvs, hl] at h
      · simp [hv, hg] at h
        exact absurd (by simp [h.1.1, h.1.2]) hpb

omit [JSNumber N] in
theorem bindArgs_eq {ps : List String} {vs : List (Val N)} (h : vs.length = ps.length) :
    Eval.bindArgs ps vs = some (ps.zip vs).reverse := by
  simp [Eval.bindArgs, h]

theorem execStmt_localCall (sp cs sp' : Span) (g : String) (args : List Expr) (ρ : Eval.Env N) (k : Nat) :
    Eval.execStmt m (k + 1) ρ (.exprStmt sp (.call cs (.ident sp' g) args)) = (do
      let vs ← Eval.evalList m (k + 1) ρ args
      let .closure params body ← ρ.lookup g | none
      match ← Eval.callLocal m k ρ params body vs with
      | (.ok _, after) => some (.normal after)
      | (.error t, _) => some (.ret (.error t))) := by
  rw [Eval.execStmt]; rfl

theorem callLocal_block (ps : List String) (sp : Span) (ss : List Stmt) (vs : List (Val N)) (ρ : Eval.Env N)
    (k : Nat) :
    Eval.callLocal m k ρ ps (.block sp ss) vs = (do
      match ← Eval.execStmt m k ((← Eval.bindArgs ps vs) ++ Eval.captures ρ ps (.block sp ss)) (.block sp ss) with
      | .normal after => some (.ok .undefined, Eval.writeBack ρ after ps (.block sp ss))
      | .ret r => if Eval.changesCaptured ρ ps (.block sp ss) then none else some (r, ρ)
      | .brk _ | .cont _ => none) := by
  rw [Eval.callLocal]; rfl

/-- A call of a local function that returns nothing. When the output's lifted
body ends with the locals `inner`, the spec's call ends too: each local that
the function changes gets the value that `inner` gives it, and every other
local of the caller keeps its value. -/
theorem localCall_void {env : Translate.Env} {fn : LocalFn} {k : Nat} {b : IR.Body}
    {ρs ρo inner : Eval.Env N} {vs cvals : List (Val N)} {sp : Span} {ss : List Stmt}
    (hblk : fn.body = .block sp ss)
    (h1 : (fn.captured.all fun l => fn.body.mentions l.name && (env.lookup l.name).any (·.type == l.type) &&
      !fn.params.any (·.name == l.name)) = true)
    (h2 : env.locals.any fn.late = false)
    (h3 : (fn.changes.all (fun c => fn.captured.any (·.name == c)) &&
      fn.captured.all (fun l => fn.changes.contains l.name ||
        !(stmtsChanges [] (blockStatements fn.body)).contains l.name)) = true)
    (hbody : StmtSim (N := N) m fs k (fn.bodyEnv env) (.state fn.changes) (blockStatements fn.body) b)
    (ha : Agree ρs ρo) (hs : Scoped m env ρs)
    (hcv : IR.Expr.evalList fs fuel ρo (fn.captured.map (fun l => IR.Expr.var l.name)) = some cvals)
    (hlen : vs.length = fn.params.length)
    (hrun : IR.Body.exec fs k (((fn.leanParams.map (·.1)).zip (cvals ++ vs)).reverse) b =
      some (.normal inner)) :
    ∃ mod, Eval.callLocal m k ρs (fn.params.map (·.name)) fn.body vs =
        some (.ok .undefined, Eval.writeBack ρs mod (fn.params.map (·.name)) fn.body) ∧
      (∀ n ∈ fn.changes, (inner.lookup n).isSome →
        (Eval.writeBack ρs mod (fn.params.map (·.name)) fn.body).lookup n = inner.lookup n) ∧
      Frame fn.changes (Eval.writeBack ρs mod (fn.params.map (·.name)) fn.body) ρs := by
  simp only [List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true', List.any_eq_false] at h1 h3
  have h1' : (fn.captured.all fun l => fn.body.mentions l.name && (env.lookup l.name).any (·.type == l.type)) =
      true := by
    simp only [List.all_eq_true, Bool.and_eq_true]; exact fun l hl => (h1 l hl).1
  obtain ⟨hag, hsc⟩ := localBody_env m fs fuel h1' h2 ha hs hcv hlen
  obtain ⟨-, new, out, mod, hex, hag', hnew, hout, hfr⟩ :=
    (hbody _ _ hag hsc).2 false inner (by simpa [endOf] using hrun)
  simp only [Ends] at hex
  have hlenm := hfr.length
  have hst : Eval.execStmt m k ((((fn.params.map (·.name)).zip vs).reverse) ++
      Eval.captures ρs (fn.params.map (·.name)) fn.body) fn.body = some (.normal mod) := by
    rw [hblk] at hex hlenm ⊢
    simp only [blockStatements] at hex
    rw [execStmt_block m k sp ss, hex]
    simp only [hlenm, List.length_append, Nat.add_sub_cancel, List.drop_left, Option.bind_eq_bind,
      Option.bind_some]
  -- The captured locals that the function changes are in the body's scope.
  have hcapt : ∀ n, n ∈ fn.captured.map (·.name) → (fn.bodyEnv env).has n = true := by
    intro n hn
    rw [show (fn.bodyEnv env).has n = ((fn.params ++ fn.captured).map (·.name)).contains n from
      find_name_isSome _ _]
    simp [hn]
  -- A name that no parameter has finds the captured variable.
  have hnotp : ∀ n, (fn.params.map (·.name)).contains n = false →
      (((fn.params.map (·.name)).zip vs).reverse).lookup n = none := by
    intro n hn
    have := lookup_isSome_reverse (N := N) (x := n) ((fn.params.map (·.name)).zip vs)
    rw [lookup_isSome_zip (by simpa using hlen), hn] at this
    simpa using this
  -- A captured local is in scope, and no parameter has its name.
  have hcl : ∀ l ∈ fn.captured, fn.body.mentions l.name = true ∧ (fn.params.map (·.name)).contains l.name = false ∧
      (ρs.lookup l.name).isSome = true := by
    intro l hl
    obtain ⟨⟨hm, hty⟩, hnp⟩ := h1 l hl
    refine ⟨hm, ?_, ?_⟩
    · simpa using hnp
    · rw [hs.1 l.name]
      simp only [Translate.Env.has]
      cases h : env.lookup l.name <;> simp_all
  refine ⟨mod, ?_, fun n hn hin => ?_, frame_writeBack fun n hnc hcap v hv hsn => ?_⟩
  · rw [hblk] at hst ⊢
    rw [callLocal_block, bindArgs_eq (by simpa using hlen)]
    simp [hst]
  · obtain ⟨l, hl, hln⟩ := List.any_eq_true.mp (h3.1 n hn)
    simp only [beq_iff_eq] at hln
    subst hln
    obtain ⟨hm, hnp, hsome⟩ := hcl l hl
    have hin' : inner.lookup l.name = mod.lookup l.name := by
      rw [← hag' l.name, lookup_append_fresh mod fun p hp hk => by
        have := hout p hp; rw [hk, hcapt l.name (List.mem_map.mpr ⟨l, hl, rfl⟩)] at this; exact absurd this (by simp)]
    rw [lookup_writeBack, if_pos ⟨by rw [hm, hnp]; rfl, by rw [← hin']; exact hin, hsome⟩, hin']
  · simp only [Bool.and_eq_true, Bool.not_eq_true'] at hcap
    obtain ⟨hm, hnp⟩ := hcap
    have hhas : env.has n = true := by rw [← hs.1 n]; exact hsn
    simp only [Translate.Env.has, Translate.Env.lookup, Option.isSome_iff_exists] at hhas
    obtain ⟨l, hl⟩ := hhas
    have hln : l.name = n := by simpa using List.find?_some hl
    have hlate := List.any_eq_false.mp h2 l (List.mem_of_find?_eq_some hl)
    have hlate' : (fn.captured.any (·.name == n) || fn.params.any (·.name == n)) = true := by
      simp only [LocalFn.late, hln, hm, Bool.true_and] at hlate
      cases h : (fn.captured.any (·.name == n) || fn.params.any (·.name == n)) <;> simp_all
    simp only [Bool.or_eq_true, List.any_eq_true, beq_iff_eq] at hlate'
    obtain ⟨l', hl', hl'n⟩ : ∃ l' ∈ fn.captured, l'.name = n := by
      rcases hlate' with h | ⟨q, hq, hqn⟩
      · exact h
      · exact absurd (List.mem_map.mpr ⟨q, hq, hqn⟩) (by simpa using hnp)
    have hnc' : n ∉ stmtsChanges [] (blockStatements fn.body) := by
      have := (h3.2 l' hl')
      rw [hl'n] at this
      simp only [Bool.or_eq_true] at this
      cases hc : fn.changes.contains n
      · rw [hc] at this; simpa using this
      · exact absurd (by simpa using hc) hnc
    have hmod := hfr.lookup (show n ∉ stmtsChanges (fn.bodyEnv env).fnChanges (blockStatements fn.body) from hnc')
    rw [List.lookup_append, hnotp n hnp, Option.none_or, lookup_captures, if_pos (by rw [hm, hnp]; rfl)] at hmod
    rw [← hmod, hv]

omit [JSNumber N] in
theorem bindState_isSome {inner : Eval.Env N} :
    ∀ {names : List String} {outer ρ : Eval.Env N}, IR.bindState names inner outer = some ρ →
      ∀ n ∈ names, (inner.lookup n).isSome = true
  | [], _, _, _, n, hn => by simp at hn
  | k :: ks, outer, ρ, h, n, hn => by
    simp only [IR.bindState, List.foldlM_cons] at h
    cases hk : inner.lookup k with
    | none => simp [hk] at h
    | some w =>
      simp only [hk] at h
      rcases List.mem_cons.mp hn with rfl | hn
      · simp [hk]
      · exact bindState_isSome (names := ks) (by simpa [IR.bindState] using h) n hn

/-- A statement whose output runs `body`, which binds `names` again to the
values in `inner`, as `letState` binds the state of a branch, and then `rb`,
means what the source means, when the rest does. -/
theorem rebind_sim {env : Translate.Env} {st : Stmt} {rest : List Stmt} {tail : Tail} {body rb : IR.Body}
    {names : List String} (hst0 : st.constAssignedIn rest = false)
    (hsub : ∀ n, n ∈ names → n ∈ stmtChanges env.fnChanges st)
    (hbody : ∀ (ρs ρo : Eval.Env N) (o : Outcome N), Agree ρs ρo → Scoped m env ρs →
      IR.Body.exec fs fuel ρo body = some o →
      ∃ inner mod ρo₂, IR.bindState names inner ρo = some ρo₂ ∧ IR.Body.exec fs fuel ρo₂ rb = some o ∧
        Eval.execStmt m fuel ρs st = some (.normal mod) ∧ (∀ n ∈ names, mod.lookup n = inner.lookup n) ∧
        Frame names mod ρs)
    (hrest : StmtSim (N := N) m fs fuel env tail rest rb) :
    StmtSim (N := N) m fs fuel env tail (st :: rest) body := by
  intro ρs ρo ha hs
  have key : ∀ o, IR.Body.exec fs fuel ρo body = some o →
      ∃ mod ρo₂, Eval.execStmt m fuel ρs st = some (.normal mod) ∧
        Agree mod ρo₂ ∧ Frame (stmtChanges env.fnChanges st) mod ρs ∧ IR.Body.exec fs fuel ρo₂ rb = some o := by
    intro o ho
    obtain ⟨inner, mod, ρo₂, hbs, hrb, hst, hnames, hfr⟩ := hbody ρs ρo o ha hs ho
    refine ⟨mod, ρo₂, hst, fun n => ?_, hfr.mono fun n hn => hsub n hn, hrb⟩
    rw [bindState_lookup hbs n]
    split
    · rename_i hn; exact hnames n hn
    · rename_i hn; rw [← ha n]; exact hfr.lookup hn
  constructor
  · intro v hv
    obtain ⟨mod, ρo₂, hst, hag, hfr, hb⟩ := key _ hv
    have := (hrest mod ρo₂ hag (scoped_frame hs hfr)).1 v hb
    simp [Eval.exec, hst0, hst, this]
  · intro brk ρo' hv
    obtain ⟨mod, ρo₂, hst, hag, hfr, hb⟩ := key _ hv
    obtain ⟨htail, new, out, mod₂, hex, hag₂, hnew, hout, hfr₂⟩ :=
      (hrest mod ρo₂ hag (scoped_frame hs hfr)).2 brk ρo' hb
    refine ⟨htail, new, out, mod₂, Ends.congr (by simp [Eval.exec, hst0, hst]) hex, hag₂, hnew, hout, ?_⟩
    simpa [stmtsChanges] using hfr₂.trans hfr

/-- `g(args);`, where `g` is a local function that returns nothing: the output
calls the lifted function and binds the locals that it changes again. -/
theorem localCallStmt_sim {env : Translate.Env} {sp cs sp' : Span} {args : List Expr} {rest : List Stmt}
    {tail : Tail} {fn : LocalFn} {b rb : IR.Body} {outs : List IR.Expr}
    (hfind : env.localFns.find? (·.name == fn.name) = some fn)
    (hp : localCallProblem env fn args = none)
    (hbody : ∀ k, fuel = k + 1 →
      StmtSim (N := N) m fs k (fn.bodyEnv env) (.state fn.changes) (blockStatements fn.body) b)
    (hargs : SimList (N := N) m fs fuel env args outs)
    (hrest : StmtSim (N := N) m fs fuel env tail rest rb) :
    StmtSim (N := N) m fs fuel env tail (.exprStmt sp (.call cs (.ident sp' fn.name) args) :: rest)
      (.letCall fn.changes fn.ref fn.name fn.closure fn.leanParams fn.leanRet false b
        (fn.captured.map (fun l => IR.Expr.var l.name) ++ outs) rb) := by
  obtain ⟨⟨bsp, bss, hblk⟩, h1, h2, h3, -, -⟩ := localCallProblem_none hp
  refine rebind_sim m fs fuel (names := fn.changes) (by simp) (fun n hn => ?_) (fun ρs ρo o ha hs ho => ?_) hrest
  · simp [stmtChanges, exprChanges, calleeChanges, fnChanges_lookup hfind, hn]
  obtain ⟨ps, b0, vsAll, k, inner, ρo₂, hval, hg, hvs, rfl, hl, hrun, hbs, hrb⟩ := exec_letCall fs _ ho
  simp only [LocalFn.closure, IR.Expr.eval, IR.Expr.evalList, IR.ExprExt.apply, Option.bind_eq_bind,
    Option.bind_some, Option.some.injEq, Val.closure.injEq] at hval
  obtain ⟨rfl, rfl⟩ := hval
  rcases hrun with ⟨-, hrun⟩ | ⟨h, -⟩
  rotate_left
  · cases h
  obtain ⟨cvals, vs, rfl, hcv, hvo, hcl⟩ := evalList_append_inv fs (k + 1) hvs
  have hlen : vs.length = fn.params.length := by
    simp only [LocalFn.leanParams, List.length_map, List.length_append] at hl
    simp only [List.length_map] at hcl
    omega
  obtain ⟨mod, hcall, hch, hfr⟩ := localCall_void m fs (k + 1) hblk h1 h2 h3 (hbody k rfl) ha hs hcv hlen hrun
  refine ⟨inner, Eval.writeBack ρs mod (fn.params.map (·.name)) fn.body, ρo₂, hbs, hrb, ?_,
    fun n hn => hch n hn (bindState_isSome hbs n hn), hfr⟩
  have hgs : ρs.lookup fn.name = some (.closure (fn.params.map (·.name)) fn.body) := by rw [ha]; exact hg
  rw [execStmt_localCall, hargs ρs ρo vs ha hs hvo]
  simp [hgs, hcall]

omit [JSNumber N] in
/-- A local that a local function captures is one of the locals that it took
where it was declared, when no later declaration hides its name. -/
theorem captured_of_captures {env : Translate.Env} {fn : LocalFn} {ρs : Eval.Env N} {m : Eval.Scope}
    (h2 : env.locals.any fn.late = false) (hs : Scoped m env ρs) {p : String × Val N}
    (hp : p ∈ Eval.captures ρs (fn.params.map (·.name)) fn.body) : ∃ l ∈ fn.captured, l.name = p.1 := by
  unfold Eval.captures at hp
  obtain ⟨hp, hk⟩ := List.mem_filter.mp hp
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hk
  have hhas : env.has p.1 = true := by rw [← hs.1 p.1]; exact lookup_isSome_of_mem hp
  simp only [Translate.Env.has, Translate.Env.lookup, Option.isSome_iff_exists] at hhas
  obtain ⟨l, hl⟩ := hhas
  have hln : l.name = p.1 := by simpa using List.find?_some hl
  have hlate := List.any_eq_false.mp h2 l (List.mem_of_find?_eq_some hl)
  have hlate' : (fn.captured.any (·.name == p.1) || fn.params.any (·.name == p.1)) = true := by
    simp only [LocalFn.late, hln, hk.1, Bool.true_and] at hlate
    cases h : (fn.captured.any (·.name == p.1) || fn.params.any (·.name == p.1)) <;> simp_all
  simp only [Bool.or_eq_true, List.any_eq_true, beq_iff_eq] at hlate'
  rcases hlate' with h | ⟨q, hq, hqn⟩
  · exact h
  · exact absurd (List.mem_map.mpr ⟨q, hq, hqn⟩) (by simpa using hk.2)

/-- A call of a local function that returns a value and changes nothing
around it: when the output's lifted body returns `w`, so does the spec's call. -/
theorem localCall_value {env : Translate.Env} {fn : LocalFn} {k : Nat} {b : IR.Body} {args : List Expr}
    {ρs ρo : Eval.Env N} {vs cvals : List (Val N)} {w : Val N}
    (hp : localCallProblem env fn args = none) (hret : fn.ret.isSome = true)
    (hbody : StmtSim (N := N) m fs k (fn.bodyEnv env) .ret (blockStatements fn.body) b)
    (ha : Agree ρs ρo) (hs : Scoped m env ρs)
    (hcv : IR.Expr.evalList fs fuel ρo (fn.captured.map (fun l => IR.Expr.var l.name)) = some cvals)
    (hlen : vs.length = fn.params.length)
    (hrun : IR.Body.exec fs k (((fn.leanParams.map (·.1)).zip (cvals ++ vs)).reverse) b = some (.ret (.ok w)))
    (hgs : ρs.lookup fn.name = some (.closure (fn.params.map (·.name)) fn.body))
    (hvs : Eval.evalList m (k + 1) ρs args = some vs) :
    Eval.evalCall m (k + 1) ρs fn.name args = some (.ok w) := by
  obtain ⟨⟨bsp, bss, hblk⟩, h1, h2, -, h4, -⟩ := localCallProblem_none hp
  have h1' : (fn.captured.all fun l => fn.body.mentions l.name && (env.lookup l.name).any (·.type == l.type)) =
      true := by
    simp only [List.all_eq_true, Bool.and_eq_true] at h1 ⊢; exact fun l hl => (h1 l hl).1
  obtain ⟨hag, hsc⟩ := localBody_env m fs fuel h1' h2 ha hs hcv hlen
  have hex := (hbody _ _ hag hsc).1 _ hrun
  have hst := block_ret m k fn.body hex
  have hchg : Eval.changesCaptured ρs (fn.params.map (·.name)) fn.body = false := by
    unfold Eval.changesCaptured
    rw [List.any_eq_false]
    intro p hp
    obtain ⟨l, hl, hln⟩ := captured_of_captures h2 hs hp
    simp only [hret, Bool.true_and, List.any_eq_false] at h4
    have := h4 l hl
    rw [← hln]
    simpa using this
  have hnum : (ρs.lookup "Number").isNone = false ∨ fn.name ≠ "Number" := by
    by_cases hn : fn.name = "Number"
    · left; rw [← hn, hgs]; rfl
    · right; exact hn
  rw [Eval.evalCall, hvs]
  rw [hblk] at hst hgs hchg
  have hnum' : (fn.name == "Number" && (ρs.lookup "Number").isNone) = false := by
    rcases hnum with h | h
    · rw [← hblk] at hgs; simp [h]
    · simp [h]
  simp only [Option.bind_eq_bind, Option.bind_some, hnum', Bool.false_eq_true, ↓reduceIte, hgs, hchg,
    callLocal_block, bindArgs_eq (show vs.length = (fn.params.map (·.name)).length by simpa using hlen)]
  simp [hst]

theorem decl_sim_gen {env env' : Translate.Env} {s : Span} {d : VarDecl} {init : Expr} {rest : List Stmt}
    {tail : Tail} {body rb : IR.Body} {b : Binding} {ty : Ty}
    (hinit : d.init = some init) (hconst : (Stmt.varDecl s d).constAssignedIn rest = false)
    (hfresh : env.has d.name = false)
    (henv : env' = env.add { name := d.name, binding := b, type := ty })
    (hbody : ∀ (ρs ρo : Eval.Env N) (o : Outcome N), Agree ρs ρo → Scoped m env ρs →
      IR.Body.exec fs fuel ρo body = some o → ∃ w,
        Eval.eval m fuel ρs init = some w ∧ IR.Body.exec fs fuel ((d.name, w) :: ρo) rb = some o)
    (hrest : StmtSim (N := N) m fs fuel env' tail rest rb) :
    StmtSim (N := N) m fs fuel env tail (.varDecl s d :: rest) body := by
  subst henv
  obtain ⟨kind, name, type, init?⟩ := d
  simp only at hinit hfresh hbody ⊢
  subst hinit
  intro ρs ρo ha hs
  have ha' : ∀ w, Agree ((name, w) :: ρs) ((name, w) :: ρo) := fun w x => by
    simp only [List.lookup]; split
    · rfl
    · exact ha x
  have hs' : ∀ w, Scoped m (env.add { name, binding := b, type := ty }) ((name, w) :: ρs) :=
    fun w => ⟨fun x => by
    rw [has_add, ← hs.1 x]
    simp only [List.lookup]
    by_cases hx : x = name
    · subst hx; simp
    · have h1 : (x == name) = false := by simpa using hx
      have h2 : (name == x) = false := by simpa using Ne.symm hx
      simp [h1, h2], hs.2⟩
  have hstep : ∀ w, Eval.eval m fuel ρs init = some w →
      Eval.exec m fuel ρs (.varDecl s { kind, name, type, init := some init } :: rest) =
        Eval.exec m fuel ((name, w) :: ρs) rest := by
    intro w hw
    simp [Eval.exec, Eval.execStmt, evalTop_ok m fuel hw, hconst]
  constructor
  · intro v hv
    obtain ⟨w, hw, hb⟩ := hbody ρs ρo _ ha hs hv
    rw [hstep w hw]
    exact ((hrest _ _ (ha' w) (hs' w)).1 v hb)
  · intro brk ρo' hv
    obtain ⟨w, hw, hb⟩ := hbody ρs ρo _ ha hs hv
    obtain ⟨htail, new, out, mod, hex, hag, hnew, hout, hfr⟩ := (hrest _ _ (ha' w) (hs' w)).2 brk ρo' hb
    obtain ⟨ρ₁, ρ₂, rfl, h₁, h₂⟩ := Frame.split (a := [(name, w)]) (b := ρs) hfr
    -- The new bindings of either side, and the declared name, are not in `env`.
    have hfr₁ : ∀ l : Eval.Env N,
        (∀ p ∈ l, (env.add { name, binding := b, type := ty }).has p.1 = false) →
        ∀ p ∈ l ++ ρ₁, env.has p.1 = false := by
      intro l hl p hp
      rcases List.mem_append.mp hp with hp | hp
      · have := hl p hp
        rw [has_add] at this
        simp only [Bool.or_eq_false_iff] at this
        exact this.1
      · obtain ⟨q, hq, hk⟩ := Frame.mem h₁ hp
        simp only [List.mem_singleton] at hq
        subst hq
        rw [hk]; exact hfresh
    refine ⟨htail, new ++ ρ₁, out ++ ρ₁, ρ₂, ?_, ?_, hfr₁ new hnew, hfr₁ out hout, ?_⟩
    · rw [hstep w hw, List.append_assoc]; exact hex
    · rwa [List.append_assoc]
    · exact h₂.mono fun n hn => by simp only [Env.fnChanges_add] at hn; simp [stmtsChanges, hn]

omit [JSNumber N] in
theorem bindState_fresh {x : String} {w : Val N} {ρ : Eval.Env N} (h : ρ.lookup x = none) :
    IR.bindState [x] [(x, w)] ρ = some ((x, w) :: ρ) := by
  simp [IR.bindState, h]

/-- `const x = g(args)`, where `g` is a local function that returns a value:
the output calls the lifted function and binds `x` to what it returns. -/
theorem localDecl_sim {env env' : Translate.Env} {s cs sp' : Span} {d : VarDecl} {args : List Expr}
    {rest : List Stmt} {tail : Tail} {fn : LocalFn} {b rb : IR.Body} {outs : List IR.Expr} {bnd : Binding}
    {ty : Ty}
    (hinit : d.init = some (.call cs (.ident sp' fn.name) args))
    (hconst : (Stmt.varDecl s d).constAssignedIn rest = false) (hfresh : env.has d.name = false)
    (henv : env' = env.add { name := d.name, binding := bnd, type := ty })
    (hp : localCallProblem env fn args = none) (hret : fn.ret.isSome = true)
    (hbody : ∀ k, fuel = k + 1 → StmtSim (N := N) m fs k (fn.bodyEnv env) .ret (blockStatements fn.body) b)
    (hargs : SimList (N := N) m fs fuel env args outs)
    (hrest : StmtSim (N := N) m fs fuel env' tail rest rb) :
    StmtSim (N := N) m fs fuel env tail (.varDecl s d :: rest)
      (.letCall [d.name] fn.ref fn.name fn.closure fn.leanParams fn.leanRet true b
        (fn.captured.map (fun l => IR.Expr.var l.name) ++ outs) rb) := by
  refine decl_sim_gen m fs fuel hinit hconst hfresh henv (fun ρs ρo o ha hs ho => ?_) hrest
  obtain ⟨ps, b0, vsAll, k, inner, ρo₂, hval, hg, hvs, rfl, hl, hrun, hbs, hrb⟩ := exec_letCall fs _ ho
  simp only [LocalFn.closure, IR.Expr.eval, IR.Expr.evalList, IR.ExprExt.apply, Option.bind_eq_bind,
    Option.bind_some, Option.some.injEq, Val.closure.injEq] at hval
  obtain ⟨rfl, rfl⟩ := hval
  rcases hrun with ⟨h, -⟩ | ⟨-, w, hrun, hcr⟩
  · cases h
  simp only [IR.callResult, Option.some.injEq] at hcr
  subst hcr
  have hnone : ρo.lookup d.name = none := by rw [← ha]; exact hs.none hfresh
  rw [bindState_fresh hnone] at hbs
  cases hbs
  obtain ⟨cvals, vs, rfl, hcv, hvo, hcl⟩ := evalList_append_inv fs (k + 1) hvs
  have hlen : vs.length = fn.params.length := by
    simp only [LocalFn.leanParams, List.length_map, List.length_append] at hl
    simp only [List.length_map] at hcl
    omega
  have hgs : ρs.lookup fn.name = some (.closure (fn.params.map (·.name)) fn.body) := by rw [ha]; exact hg
  have hcall := localCall_value m fs (k + 1) hp hret (hbody k rfl) ha hs hcv hlen hrun hgs
    (hargs ρs ρo vs ha hs hvo)
  refine ⟨w, ?_, hrb⟩
  simp [Eval.eval, hcall, Except.toOption]

/-- `return g(args)`, where `g` is a local function that returns a value: the
output calls the lifted function and returns what it returns. -/
theorem localReturn_sim {env : Translate.Env} {s cs sp' : Span} {args : List Expr} {tail : Tail}
    {fn : LocalFn} {b : IR.Body} {outs : List IR.Expr} {throws : Bool}
    (hp : localCallProblem env fn args = none) (hret : fn.ret.isSome = true)
    (hbody : ∀ k, fuel = k + 1 → StmtSim (N := N) m fs k (fn.bodyEnv env) .ret (blockStatements fn.body) b)
    (hargs : SimList (N := N) m fs fuel env args outs) :
    StmtSim (N := N) m fs fuel env tail [.returnStmt s (some (.call cs (.ident sp' fn.name) args))]
      (.letCall [fn.name] fn.ref fn.name fn.closure fn.leanParams fn.leanRet true b
        (fn.captured.map (fun l => IR.Expr.var l.name) ++ outs)
        (tail.returnBody (if throws then IR.Expr.pure (.var fn.name) else .var fn.name))) := by
  have hretb : ∀ (ρ : Eval.Env N) (c : IR.Expr), IR.Body.exec fs fuel ρ (tail.returnBody c) =
      (do return .ret (.ok (← IR.Expr.eval fs fuel ρ c))) := by
    intro ρ c
    cases tail <;> simp [Tail.returnBody, IR.Body.exec]
  intro ρs ρo ha hs
  have key : ∀ o, IR.Body.exec fs fuel ρo (.letCall [fn.name] fn.ref fn.name fn.closure fn.leanParams fn.leanRet
      true b (fn.captured.map (fun l => IR.Expr.var l.name) ++ outs)
      (tail.returnBody (if throws then IR.Expr.pure (.var fn.name) else .var fn.name))) = some o →
      ∃ w, o = .ret (.ok w) ∧ Eval.evalCall m fuel ρs fn.name args = some (.ok w) := by
    intro o ho
    obtain ⟨ps, b0, vsAll, k, inner, ρo₂, hval, hg, hvs, rfl, hl, hrun, hbs, hrb⟩ := exec_letCall fs _ ho
    simp only [LocalFn.closure, IR.Expr.eval, IR.Expr.evalList, IR.ExprExt.apply, Option.bind_eq_bind,
      Option.bind_some, Option.some.injEq, Val.closure.injEq] at hval
    obtain ⟨rfl, rfl⟩ := hval
    rcases hrun with ⟨h, -⟩ | ⟨-, w, hrun, hcr⟩
    · cases h
    simp only [IR.callResult, Option.some.injEq] at hcr
    subst hcr
    have hlk : ρo₂.lookup fn.name = some w := by rw [bindState_lookup hbs]; simp
    rw [hretb, eval_pureIf] at hrb
    simp only [IR.Expr.eval, hlk, Option.bind_eq_bind, Option.bind_some] at hrb
    obtain ⟨cvals, vs, rfl, hcv, hvo, hcl⟩ := evalList_append_inv fs (k + 1) hvs
    have hlen : vs.length = fn.params.length := by
      simp only [LocalFn.leanParams, List.length_map, List.length_append] at hl
      simp only [List.length_map] at hcl
      omega
    have hgs : ρs.lookup fn.name = some (.closure (fn.params.map (·.name)) fn.body) := by rw [ha]; exact hg
    exact ⟨w, by simpa [pure] using hrb.symm, localCall_value m fs (k + 1) hp hret (hbody k rfl) ha hs hcv hlen hrun hgs
      (hargs ρs ρo vs ha hs hvo)⟩
  constructor
  · intro v hv
    obtain ⟨w, hw, hcall⟩ := key _ hv
    cases hw
    rw [exec_single]
    simp [Eval.execStmt, evalTop_call, hcall]
  · intro brk ρo' hv
    obtain ⟨w, hw, -⟩ := key _ hv
    cases brk <;> simp [endOf] at hw

/-- `function g(params): T { body }` in the body of the function: the spec binds
`g` to the function, and so does the IR's meaning of the output, which lifts
it out. -/
theorem funDecl_sim {env env' : Translate.Env} {s : Span} {name : String} {tps : List String}
    {params : List Param} {rt : Option TypeExpr} {body : Stmt} {rest : List Stmt} {rb : IR.Body}
    (hhas : ∀ x, env'.has x = (env.has x || x == name)) (hfun : env'.functions = env.functions)
    (henum : env'.enums = env.enums)
    (hrest : StmtSim (N := N) m fs fuel env' .ret rest rb) :
    StmtSim (N := N) m fs fuel env .ret (.funDecl s name tps params rt body :: rest)
      (.letLifted name (IR.Expr.closure (params.map (·.name)) body) rb) := by
  intro ρs ρo ha hs
  let w : Val N := .closure (params.map (·.name)) body
  have ha' : Agree ((name, w) :: ρs) ((name, w) :: ρo) := fun x => by
    simp only [List.lookup]; split
    · rfl
    · exact ha x
  have hs' : Scoped m env' ((name, w) :: ρs) := by
    refine ⟨fun x => ?_, ?_, ?_⟩
    · rw [hhas, ← hs.1 x]
      simp only [List.lookup]
      by_cases hx : x = name
      · subst hx; simp
      · have h1 : (x == name) = false := by simpa using hx
        simp [h1]
    · intro f hf; rw [hfun] at hf; exact hs.2.1 f hf
    · intro e he; rw [henum] at he; exact hs.2.2 e he
  have hexec : ∀ o, IR.Body.exec fs fuel ρo (.letLifted name (IR.Expr.closure (params.map (·.name)) body) rb) =
      some o → IR.Body.exec fs fuel ((name, w) :: ρo) rb = some o := by
    intro o ho
    simpa [IR.Body.exec, IR.Expr.eval, IR.Expr.evalList, IR.ExprExt.apply] using ho
  have hstep : Eval.exec m fuel ρs (.funDecl s name tps params rt body :: rest) =
      Eval.exec m fuel ((name, w) :: ρs) rest := by
    simp [Eval.exec, Eval.execStmt, w]
  constructor
  · intro v hv
    rw [hstep]
    exact (hrest _ _ ha' hs').1 v (hexec _ hv)
  · intro brk ρo' hv
    exact absurd ((hrest _ _ ha' hs').2 brk ρo' (hexec _ hv)).1 (by simp [Tail.isRet])

omit [JSNumber N] in
/-- A local function stands where its function returns. -/
theorem translateLocalHead_tail {env : Translate.Env} {s : Span} {name : String} {tps : List String}
    {params : List Param} {rt : Option TypeExpr} {body : Stmt} {tail : Tail} {ctx ctx' : Ctx} {fn : LocalFn}
    (h : translateLocalHead env s name tps params rt body tail ctx = .ok fn ctx') : tail = .ret := by
  cases tail
  · rfl
  all_goals
    unfold translateLocalHead at h
    rw [bind_ok] at h
    obtain ⟨_, _, hget, h⟩ := h
    rw [get_ok] at hget
    obtain ⟨rfl, rfl⟩ := hget
    simp only [Tail.isRet, Bool.false_and, Bool.false_eq_true, ↓reduceIte] at h
    rw [bind_ok] at h
    obtain ⟨_, _, hr, -⟩ := h
    simp [reject] at hr

/-- `g(a);`, where `g` is a local function, a case of `stmts_sound`. -/
theorem translateLocalStmt_sound (hc : CallsAgree (N := N) m.program fs fuel) {F : Nat}
    (ihS : ∀ env tail ss ctx body ctx', translateStatements F env tail ss ctx = .ok body ctx' →
      StmtSim (N := N) m fs fuel env tail ss body)
    (ihL : ∀ k, fuel = k + 1 → ∀ env tail ss ctx body ctx', translateStatements F env tail ss ctx = .ok body ctx' →
      StmtSim (N := N) m fs k env tail ss body)
    {env : Translate.Env} {tail : Tail} {s : Span} {e : Expr} {rest : List Stmt} {largs : List Expr}
    {lfn : LocalFn} {ctx ctx' : Ctx} {body : IR.Body}
    (hlc : localCall? env e = some (largs, lfn))
    (h : translateStatements (F + 1) env tail (.exprStmt s e :: rest) ctx = .ok body ctx') :
    StmtSim (N := N) m fs fuel env tail (.exprStmt s e :: rest) body := by
  obtain ⟨cs, sp', rfl, hfind⟩ := localCall?_some hlc
  unfold translateStatements at h
  simp only [hlc, ite_state] at h
  split at h
  rotate_left
  · simp at h
  rename_i hnone
  simp only [pure_bind, bind_ok] at h
  obtain ⟨⟨b, outs⟩, c₁, hcall, rb, c₂, hrb, h⟩ := h
  simp only [pure_ok] at h
  obtain ⟨rfl, -⟩ := h
  obtain ⟨hp, ⟨d₁, d₂, hb⟩, outs', e₁, e₂, hargs, rfl⟩ := translateLocalCall_ok hcall
  have htail : lfn.tail = .state lfn.changes := by
    cases hr : lfn.ret <;> simp_all [LocalFn.tail]
  rw [htail] at hb
  obtain ⟨-, -, -, -, -, hlen⟩ := localCallProblem_none hp
  exact localCallStmt_sim m fs fuel hfind hp (fun k hk => ihL k hk _ _ _ _ _ _ hb)
    (translateLocalArgs_sim m fs fuel hc _ _ _ _ _ hlen hargs) (ihS _ _ _ _ _ _ hrb)

/-- `return g(a)`, where `g` is a local function, a case of `stmts_sound`. -/
theorem translateLocalReturn_sound (hc : CallsAgree (N := N) m.program fs fuel) {F : Nat}
    (ihL : ∀ k, fuel = k + 1 → ∀ env tail ss ctx body ctx', translateStatements F env tail ss ctx = .ok body ctx' →
      StmtSim (N := N) m fs k env tail ss body)
    {env : Translate.Env} {tail : Tail} {s : Span} {v : Expr} {largs : List Expr}
    {lfn : LocalFn} {ctx ctx' : Ctx} {body : IR.Body}
    (hcr : tail.canReturn = true) (hlc : localCall? env v = some (largs, lfn))
    (h : translateStatements (F + 1) env tail [.returnStmt s (some v)] ctx = .ok body ctx') :
    StmtSim (N := N) m fs fuel env tail [.returnStmt s (some v)] body := by
  obtain ⟨cs, sp', rfl, hfind⟩ := localCall?_some hlc
  unfold translateStatements at h
  simp only [hcr, hlc] at h
  cases hr : lfn.ret with
  | none => simp [hr] at h
  | some r =>
    simp only [hr, bind_ok, get_ok, ite_state] at h
    obtain ⟨_, _, ⟨rfl, rfl⟩, h⟩ := h
    split at h
    rotate_left
    · simp at h
    simp only [pure_bind, bind_ok, get_ok, pure_ok] at h
    obtain ⟨⟨b, outs⟩, c₁, hcall, _, _, ⟨rfl, rfl⟩, rfl, -⟩ := h
    obtain ⟨hp, ⟨d₁, d₂, hb⟩, outs', e₁, e₂, hargs, rfl⟩ := translateLocalCall_ok hcall
    have htail : lfn.tail = .ret := by simp [LocalFn.tail, hr]
    rw [htail] at hb
    obtain ⟨-, -, -, -, -, hlen⟩ := localCallProblem_none hp
    exact localReturn_sim m fs fuel hp (by simp [hr]) (fun k hk => ihL k hk _ _ _ _ _ _ hb)
      (translateLocalArgs_sim m fs fuel hc _ _ _ _ _ hlen hargs)

/-- `function g(…) { … }` in the body of the function, a case of
`stmts_sound`. -/
theorem translateFunDecl_sound {F : Nat}
    (ihS : ∀ env tail ss ctx body ctx', translateStatements F env tail ss ctx = .ok body ctx' →
      StmtSim (N := N) m fs fuel env tail ss body)
    {env : Translate.Env} {tail : Tail} {s : Span} {name : String} {tps : List String} {params : List Param}
    {rt : Option TypeExpr} {fbody : Stmt} {rest : List Stmt} {ctx ctx' : Ctx} {body : IR.Body}
    (h : translateStatements (F + 1) env tail (.funDecl s name tps params rt fbody :: rest) ctx = .ok body ctx') :
    StmtSim (N := N) m fs fuel env tail (.funDecl s name tps params rt fbody :: rest) body := by
  unfold translateStatements at h
  simp only [bind_ok, pure_ok] at h
  obtain ⟨fn, c₁, hhead, b, c₂, hb, env', c₃, hdecl, rb, c₄, hrb, rfl, -⟩ := h
  obtain rfl := translateLocalHead_tail hhead
  obtain ⟨-, rfl, -⟩ := declare_ok hdecl
  refine funDecl_sim m fs fuel (fun x => ?_) ?_ ?_ (ihS _ _ _ _ _ _ hrb)
  rotate_left
  · rfl
  · rfl
  change (env.add _).has x = _
  rw [has_add]
  by_cases hx : x = name
  · subst hx; simp
  · have h1 : (name == x) = false := by simpa using Ne.symm hx
    have h2 : (x == name) = false := by simpa using hx
    rw [h1, h2]

/-- A declaration, a case of `stmts_sound`, on its own so that the mutual
proof stays within its heartbeat budget. -/
theorem translateVariable_sound (hc : CallsAgree (N := N) m.program fs fuel) {F : Nat}
    (ihS : ∀ env tail ss ctx body ctx', translateStatements F env tail ss ctx = .ok body ctx' →
      StmtSim (N := N) m fs fuel env tail ss body)
    (ihL : ∀ k, fuel = k + 1 → ∀ env tail ss ctx body ctx', translateStatements F env tail ss ctx = .ok body ctx' →
      StmtSim (N := N) m fs k env tail ss body) :
    ∀ env s d rest tail ctx body ctx', translateVariable (F + 1) env s d rest tail ctx = .ok body ctx' →
      StmtSim (N := N) m fs fuel env tail (.varDecl s d :: rest) body := by
  intro env s d rest tail ctx body ctx' h
  obtain ⟨kind, name, type, init?⟩ := d
  unfold translateVariable at h
  simp only [ite_state] at h
  split at h
  · simp at h
  rename_i hconst
  simp only [pure_bind] at h
  simp only [bind_ok, orReject_ok] at h
  obtain ⟨init, s₁, ⟨rfl, rfl⟩, h⟩ := h
  rcases hlc : localCall? env init with _ | ⟨largs, lfn⟩
  rotate_left
  · -- `const x = g(a)`, where `g` is a local function.
    simp only [hlc] at h
    obtain ⟨cs, sp', rfl, hfind⟩ := localCall?_some hlc
    cases hr : lfn.ret with
    | none => simp [hr] at h
    | some r =>
      simp only [hr, bind_ok, ite_state] at h
      obtain ⟨declared, c₁, hdecl, h⟩ := h
      split at h
      rotate_left
      · simp at h
      simp only [bind_ok] at h
      obtain ⟨⟨b, outs⟩, c₂, hcall, env', c₃, hdeclare, rb, c₄, hrb, h⟩ := h
      simp only [pure_ok] at h
      obtain ⟨rfl, -⟩ := h
      obtain ⟨hp, ⟨d₁, d₂, hb⟩, outs', e₁, e₂, hargs, rfl⟩ := translateLocalCall_ok hcall
      have htail : lfn.tail = .ret := by simp [LocalFn.tail, hr]
      rw [htail] at hb
      obtain ⟨-, -, -, -, -, hlen⟩ := localCallProblem_none hp
      obtain ⟨hfresh, henv, -⟩ := declare_ok hdeclare
      exact localDecl_sim m fs fuel (d := ⟨kind, name, type, some _⟩) rfl (by simpa using hconst) hfresh henv hp
        (by simp [hr]) (fun k hk => ihL k hk _ _ _ _ _ _ hb)
        (translateLocalArgs_sim m fs fuel hc _ _ _ _ _ hlen hargs) (ihS _ _ _ _ _ _ hrb)
  simp only [hlc] at h
  rcases htc : throwingCall? env.functions init with _ | ⟨cs, sp, fname, args⟩
  rotate_left
  · -- `const x = f(a)`, where `f` can throw.
    simp only [htc] at h
    obtain rfl := throwingCall?_some htc
    simp only [bind_ok] at h
    obtain ⟨⟨ref, outs, env'⟩, s₂, hbh, h⟩ := h
    simp only [pure_ok] at h
    obtain ⟨rb, s₃, hrb, rfl, -⟩ := h
    obtain ⟨rfl, F', c, ctx₁, ctx₂, htr, hcode, hfresh, rfl⟩ := translateBindHead_ok hbh
    exact bind_sim m fs fuel (d := ⟨kind, name, type, some _⟩) rfl (by simpa using hconst) hfresh rfl
      (translateCall_callSim m fs fuel hc htr hcode) (ihS _ _ _ _ _ _ hrb)
  simp only [htc] at h
  simp only [ite_state] at h
  cases type with
  | none =>
    simp only [Bool.false_eq_true, ite_false, ite_self] at h
    simp only [bind_ok, fuelLimit_ok] at h
    obtain ⟨_, _, ⟨rfl, rfl⟩, code, s₂, hcode, env', s₃, hdecl, rb, s₄, hrb, h⟩ := h
    simp only [pure_ok] at h
    obtain ⟨rfl, -⟩ := h
    obtain ⟨hfresh, rfl, -⟩ := declare_ok hdecl
    have hsim := (expr_sound m fs fuel hc _).1 _ _ _ _ _ _ hcode
    exact decl_sim m fs fuel (d := ⟨kind, name, none, some init⟩) rfl (by simpa using hconst) hfresh rfl
      (fun ρo o ho => by
        simp only [IR.Body.exec, eval_withType] at ho
        cases hw : IR.Expr.eval fs fuel ρo code.value with
        | none => simp [hw] at ho
        | some w =>
          exact ⟨w, fun ρs ha hs => hsim ρs ρo w ha hs (by rwa [eval_value] at hw),
            by simpa [hw] using ho⟩)
      (ihS _ _ _ _ _ _ hrb)
  | some annotation =>
    simp only at h
    repeat' split at h
    all_goals first
      | (simp at h; done)
      | (simp only [bind_ok, map_ok, fuelLimit_ok] at h
         obtain ⟨ty, s₂, hty, _, _, ⟨rfl, rfl⟩, code, s₃, hcode, h⟩ := h
         simp only [ite_state] at h
         split at h
         · simp only [bind_ok, map_ok] at h
           obtain ⟨env', s₄, hdecl, rb, hrb, rfl⟩ := h
           obtain ⟨hfresh, rfl, -⟩ := declare_ok hdecl
           have hsim := (expr_sound m fs fuel hc _).1 _ _ _ _ _ _ hcode
           exact decl_sim m fs fuel (d := ⟨kind, name, some annotation, some init⟩) rfl (by simpa using hconst) hfresh rfl
             (fun ρo o ho => by
               simp only [IR.Body.exec, eval_withType] at ho
               cases hw : IR.Expr.eval fs fuel ρo code.value with
               | none => simp [hw] at ho
               | some w =>
                 exact ⟨w, fun ρs ha hs => hsim ρs ρo w ha hs (by rwa [eval_value] at hw),
                   by simpa [hw] using ho⟩)
             (ihS _ _ _ _ _ _ hrb)
         · simp at h)
      | (simp only [bind_ok, map_ok, fuelLimit_ok] at h
         obtain ⟨_, s₂, ⟨ty, hty, rfl⟩, _, _, ⟨rfl, rfl⟩, code, s₃, hcode, h⟩ := h
         simp only [ite_state] at h
         split at h
         · simp only [bind_ok, pure_ok] at h
           obtain ⟨env', s₄, hdecl, rb, s₅, hrb, rfl, -⟩ := h
           obtain ⟨hfresh, rfl, -⟩ := declare_ok hdecl
           have hsim := (expr_sound m fs fuel hc _).1 _ _ _ _ _ _ hcode
           exact decl_sim m fs fuel (d := ⟨kind, name, some annotation, some init⟩) rfl (by simpa using hconst) hfresh rfl
             (fun ρo o ho => by
               simp only [IR.Body.exec, eval_withType] at ho
               cases hw : IR.Expr.eval fs fuel ρo code.value with
               | none => simp [hw] at ho
               | some w =>
                 exact ⟨w, fun ρs ha hs => hsim ρs ρo w ha hs (by rwa [eval_value] at hw),
                   by simpa [hw] using ho⟩)
             (ihS _ _ _ _ _ _ hrb)
         · simp at h)
      | (exfalso; cases init <;> simp_all [Expr.isArrayLiteral])
      | (simp only [bind_ok, fuelLimit_ok, pure_ok] at h
         obtain ⟨ty, s₂, hty, _, _, ⟨rfl, rfl⟩, code, s₃, hcode, env', s₄, hdecl, rb, s₅, hrb,
           rfl, -⟩ := h
         obtain ⟨hfresh, rfl, -⟩ := declare_ok hdecl
         have hsim := (expr_sound m fs fuel hc _).2.2.1 _ _ _ _ _ _ _ hcode
         exact decl_sim m fs fuel (d := ⟨kind, name, some annotation, some _⟩) rfl (by simpa using hconst) hfresh rfl
           (fun ρo o ho => by
             simp only [IR.Body.exec] at ho
             cases hw : IR.Expr.eval fs fuel ρo code.value with
             | none => simp [hw] at ho
             | some w =>
               exact ⟨w, fun ρs ha hs => hsim ρs ρo w ha hs (by rwa [eval_value] at hw),
                 by simpa [hw] using ho⟩)
           (ihS _ _ _ _ _ _ hrb))
      | (simp only [bind_ok, fuelLimit_ok, pure_ok] at h
         obtain ⟨ty, s₂, hty, _, _, ⟨rfl, rfl⟩, r, s₃, hel, env', s₄, hdecl, rb, s₅, hrb,
           rfl, -⟩ := h
         obtain ⟨hfresh, rfl, -⟩ := declare_ok hdecl
         have hsim := (expr_sound m fs fuel hc _).2.1 _ _ _ _ _ _ _ hel
         exact decl_sim m fs fuel (d := ⟨kind, name, some annotation, some _⟩) rfl (by simpa using hconst) hfresh rfl
           (fun ρo o ho => by
             simp only [IR.Body.exec] at ho
             cases hw : IR.Expr.evalList fs fuel ρo r.1 with
             | none => simp [hw] at ho
             | some ws =>
               exact ⟨.list ws, fun ρs ha hs => by
                 rw [Eval.eval]; simp [evalElems_of_evalList m fuel (hsim ρs ρo ws ha hs hw)], by simpa [hw] using ho⟩)
           (ihS _ _ _ _ _ _ hrb))

/-! ### Array destructuring -/

omit [JSNumber N] in
/-- `xs.slice(n)` is the list after the first `n` elements. -/
theorem sliceList_drop {α : Type} (items : List α) (n : Nat) :
    Eval.sliceList items (n : Int) none = items.drop n := by
  simp only [Eval.sliceList, Eval.relIndex]
  have hn : ¬ ((n : Int) < 0) := by omega
  simp only [hn, if_false, Int.toNat_natCast]
  rw [List.take_of_length_le (by simp)]
  by_cases h : n ≤ items.length
  · rw [Nat.min_eq_left h]
  · rw [Nat.min_eq_right (by omega), List.drop_length, List.drop_eq_nil_of_le (by omega)]

omit [JSNumber N] in
theorem Agree.append {ρs ρo : Eval.Env N} (ha : Agree ρs ρo) :
    ∀ bs : Eval.Env N, Agree (bs ++ ρs) (bs ++ ρo)
  | [] => ha
  | (k, v) :: bs => fun x => by
    simp only [List.cons_append, List.lookup]
    split
    · rfl
    · exact Agree.append ha bs x

/-- A statement whose output binds `names` to values `ws`, all at once, means
what the source means, when the rest does: the source binds the same names to
the same values, in the same order. -/
theorem binds_sim {env env' : Translate.Env} {stmt : Stmt} {rest : List Stmt} {tail : Tail}
    {body rb : IR.Body} (names : List String)
    (hfresh : ∀ n ∈ names, env.has n = false)
    (hhas : ∀ x, env'.has x = (env.has x || names.contains x))
    (hglob : globals env' = globals env)
    (hch : ∀ n, n ∈ stmtsChanges env.fnChanges rest → n ∈ stmtsChanges env.fnChanges (stmt :: rest))
    (hbody : ∀ (ρo : Eval.Env N) (o : Outcome N), IR.Body.exec fs fuel ρo body = some o → ∃ ws,
      ws.length = names.length ∧
      (∀ ρs, Agree ρs ρo → Scoped m env ρs →
        Eval.exec m fuel ρs (stmt :: rest) = Eval.exec m fuel ((names.zip ws).reverse ++ ρs) rest) ∧
        IR.Body.exec fs fuel ((names.zip ws).reverse ++ ρo) rb = some o)
    (hrest : StmtSim (N := N) m fs fuel env' tail rest rb) :
    StmtSim (N := N) m fs fuel env tail (stmt :: rest) body := by
  simp only [StmtSim, fnChanges_congr hglob] at hrest
  intro ρs ρo ha hs
  have hs' : ∀ ws : List (Val N), ws.length = names.length →
      Scoped m env' ((names.zip ws).reverse ++ ρs) := fun ws hl =>
    ⟨fun x => by
      rw [lookup_isSome_append, lookup_isSome_reverse, lookup_isSome_zip hl, hhas x,
        hs.1 x, Bool.or_comm],
     Resolves.congr hs.2 hglob⟩
  have hkeys : ∀ ws : List (Val N), ∀ q ∈ (names.zip ws).reverse, env.has q.1 = false := by
    intro ws q hq
    rw [List.mem_reverse] at hq
    exact hfresh _ (List.of_mem_zip hq).1
  constructor
  · intro v hv
    obtain ⟨ws, hl, hw, hb⟩ := hbody ρo _ hv
    rw [hw ρs ha hs]
    exact (hrest _ _ (ha.append _) (hs' ws hl)).1 v hb
  · intro brk ρo' hv
    obtain ⟨ws, hl, hw, hb⟩ := hbody ρo _ hv
    obtain ⟨htail, new, out, mod, hex, hag, hnew, hout, hfr⟩ :=
      (hrest _ _ (ha.append _) (hs' ws hl)).2 brk ρo' hb
    obtain ⟨ρ₁, ρ₂, rfl, h₁, h₂⟩ := Frame.split (a := (names.zip ws).reverse) (b := ρs) hfr
    have hfr₁ : ∀ l : Eval.Env N, (∀ p ∈ l, env'.has p.1 = false) →
        ∀ p ∈ l ++ ρ₁, env.has p.1 = false := by
      intro l hl p hp
      rcases List.mem_append.mp hp with hp | hp
      · have := hl p hp
        rw [hhas] at this
        simp only [Bool.or_eq_false_iff] at this
        exact this.1
      · obtain ⟨q, hq, hk⟩ := Frame.mem h₁ hp
        rw [hk]; exact hkeys ws q hq
    refine ⟨htail, new ++ ρ₁, out ++ ρ₁, ρ₂, ?_, ?_, hfr₁ new hnew, hfr₁ out hout, ?_⟩
    · rw [hw ρs ha hs, List.append_assoc]; exact hex
    · rwa [List.append_assoc]
    · exact h₂.mono hch

theorem declarePlaces_ok {s : Span} {b : Binding} :
    ∀ {env env' : Translate.Env} {reads : List (String × Ty × IR.Expr)} {ctx ctx' : Ctx},
      declarePlaces s b env reads ctx = .ok env' ctx' →
      (∀ n ∈ reads.map (·.1), env.has n = false) ∧
        (∀ x, env'.has x = (env.has x || (reads.map (·.1)).contains x)) ∧ globals env' = globals env
  | env, env', [], ctx, ctx', h => by
    simp only [declarePlaces, pure_ok] at h
    obtain ⟨rfl, -⟩ := h
    simp
  | env, env', (n, t, e) :: reads, ctx, ctx', h => by
    simp only [declarePlaces, bind_ok] at h
    obtain ⟨env₁, s₁, hd, h⟩ := h
    obtain ⟨hn, rfl, -⟩ := declare_ok hd
    obtain ⟨hf, hh, hg⟩ := declarePlaces_ok h
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      simp only [List.map_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hn
      · have := hf x hx
        rw [has_add] at this
        simp only [Bool.or_eq_false_iff] at this
        exact this.1
    · intro x
      rw [hh x, has_add]
      simp only [List.map_cons, List.contains_cons]
      by_cases hx : x = n
      · subst hx; simp
      · have h1 : (n == x) = false := by simpa using Ne.symm hx
        have h2 : (x == n) = false := by simpa using hx
        simp [h1, h2]
    · rw [hg]; rfl

/-- Each read of a place of a pattern on a list gives the value that the
interpreter binds to its name. -/
theorem listPlaces_sim {elem : Ty} {li : IR.Expr} {ρo : Eval.Env N} {items : List (Val N)}
    (hli : IR.Expr.eval fs fuel ρo li = some (.list items)) :
    ∀ (xs : List (Option String)) (i : Nat) (ws : List (Val N)),
      IR.Expr.evalList fs fuel ρo ((listPlaces elem li xs i).map (·.2.2)) = some ws →
      Eval.placeBindings xs (items.drop i) = ((listPlaces elem li xs i).map (·.1)).zip ws
  | [], i, ws, h => by simp [listPlaces, Eval.placeBindings]
  | none :: xs, i, ws, h => by
    simp only [listPlaces, Option.map_none, Option.toList_none, List.nil_append] at h ⊢
    simp only [Eval.placeBindings, Option.map_none, Option.toList_none, List.nil_append, List.tail_drop]
    exact listPlaces_sim hli xs (i + 1) ws h
  | some n :: xs, i, ws, h => by
    simp only [listPlaces, Option.map_some, Option.toList_some, List.singleton_append, List.map_cons,
      IR.Expr.evalList] at h ⊢
    cases hw : IR.Expr.eval fs fuel ρo (.ascribe (.ext (.indexLit i) [li]) (Ty.optional elem).lean) with
    | none => simp [hw] at h
    | some w =>
      cases hws : IR.Expr.evalList fs fuel ρo ((listPlaces elem li xs (i + 1)).map (·.2.2)) with
      | none => simp [hw, hws] at h
      | some ws' =>
        simp only [hw, hws, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at h
        subst h
        have ih := listPlaces_sim hli xs (i + 1) ws' hws
        simp [IR.Expr.eval, IR.Expr.evalList, hli, IR.ExprExt.apply] at hw
        subst hw
        simp only [Eval.placeBindings, Option.map_some, Option.toList_some, List.singleton_append,
          List.tail_drop, ih, List.zip_cons_cons, Eval.elementAt]
        simp [List.headD_eq_head?_getD, List.head?_drop]

/-- The reads of a pattern on a list evaluate only when the list does. -/
theorem listPlaces_items {elem : Ty} {li : IR.Expr} {ρo : Eval.Env N} :
    ∀ (xs : List (Option String)) (i : Nat) (ws : List (Val N)), listPlaces elem li xs i ≠ [] →
      IR.Expr.evalList fs fuel ρo ((listPlaces elem li xs i).map (·.2.2)) = some ws →
      ∃ items, IR.Expr.eval fs fuel ρo li = some (.list items)
  | [], _, _, hne, _ => by simp [listPlaces] at hne
  | none :: xs, i, ws, hne, h => by
    simp only [listPlaces, Option.map_none, Option.toList_none, List.nil_append] at hne h
    exact listPlaces_items xs (i + 1) ws hne h
  | some n :: xs, i, ws, _, h => by
    simp only [listPlaces, Option.map_some, Option.toList_some, List.singleton_append, List.map_cons,
      IR.Expr.evalList] at h
    cases hw : IR.Expr.eval fs fuel ρo (.ascribe (.ext (.indexLit i) [li]) (Ty.optional elem).lean) with
    | none => simp [hw] at h
    | some w =>
      simp only [IR.Expr.eval, IR.Expr.evalList] at hw
      cases hl : IR.Expr.eval fs fuel ρo li with
      | none => simp [hl] at hw
      | some l =>
        cases l <;> simp [hl, IR.ExprExt.apply] at hw
        exact ⟨_, rfl⟩

/-- Each read of a place of a pattern on a tuple gives the value that the
interpreter binds to its name. -/
theorem tuplePlaces_sim {v : IR.Expr} {size : Nat} {ρo : Eval.Env N} {items : List (Val N)}
    (hv : IR.Expr.eval fs fuel ρo v = some (.list items)) :
    ∀ (xs : List (Option String)) (tys : List Ty) (i : Nat) (ws : List (Val N)),
      xs.length ≤ tys.length →
      IR.Expr.evalList fs fuel ρo ((tuplePlaces v size xs tys i).map (·.2.2)) = some ws →
      Eval.placeBindings xs (items.drop i) = ((tuplePlaces v size xs tys i).map (·.1)).zip ws
  | [], _, i, ws, _, h => by simp [tuplePlaces, Eval.placeBindings]
  | _ :: _, [], _, _, hl, _ => by simp at hl
  | none :: xs, t :: ts, i, ws, hl, h => by
    simp only [tuplePlaces, Option.map_none, Option.toList_none, List.nil_append] at h ⊢
    simp only [Eval.placeBindings, Option.map_none, Option.toList_none, List.nil_append, List.tail_drop]
    exact tuplePlaces_sim (size := size) hv xs ts (i + 1) ws (by simpa using hl) h
  | some n :: xs, t :: ts, i, ws, hl, h => by
    simp only [tuplePlaces, Option.map_some, Option.toList_some, List.singleton_append, List.map_cons,
      IR.Expr.evalList] at h ⊢
    cases hw : IR.Expr.eval fs fuel ρo (.proj v i size) with
    | none => simp [hw] at h
    | some w =>
      cases hws : IR.Expr.evalList fs fuel ρo ((tuplePlaces v size xs ts (i + 1)).map (·.2.2)) with
      | none => simp [hw, hws] at h
      | some ws' =>
        simp only [hw, hws, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at h
        subst h
        have ih := tuplePlaces_sim (size := size) hv xs ts (i + 1) ws' (by simpa using hl) hws
        simp only [IR.Expr.eval, hv, Option.bind_eq_bind, Option.bind_some] at hw
        simp only [Eval.placeBindings, Option.map_some, Option.toList_some, List.singleton_append,
          List.tail_drop, ih, List.zip_cons_cons]
        simp [List.headD_eq_head?_getD, List.head?_drop, hw]

/-- The reads of a pattern on a tuple evaluate only when the tuple does. -/
theorem tuplePlaces_items {v : IR.Expr} {size : Nat} {ρo : Eval.Env N} :
    ∀ (xs : List (Option String)) (tys : List Ty) (i : Nat) (ws : List (Val N)),
      tuplePlaces v size xs tys i ≠ [] →
      IR.Expr.evalList fs fuel ρo ((tuplePlaces v size xs tys i).map (·.2.2)) = some ws →
      ∃ items, IR.Expr.eval fs fuel ρo v = some (.list items)
  | [], _, _, _, hne, _ => by simp [tuplePlaces] at hne
  | _ :: _, [], _, _, hne, _ => by simp [tuplePlaces] at hne
  | none :: xs, t :: ts, i, ws, hne, h => by
    simp only [tuplePlaces, Option.map_none, Option.toList_none, List.nil_append] at hne h
    exact tuplePlaces_items xs ts (i + 1) ws hne h
  | some n :: xs, t :: ts, i, ws, _, h => by
    simp only [tuplePlaces, Option.map_some, Option.toList_some, List.singleton_append, List.map_cons,
      IR.Expr.evalList] at h
    cases hw : IR.Expr.eval fs fuel ρo (.proj v i size) with
    | none => simp [hw] at h
    | some w =>
      simp only [IR.Expr.eval] at hw
      cases hl : IR.Expr.eval fs fuel ρo v with
      | none => simp [hl] at hw
      | some l => cases l <;> simp [hl] at hw; exact ⟨_, rfl⟩

omit [JSNumber N] in
/-- A pattern with a name in each place of a tuple has one read for each. -/
theorem tuplePlaces_length {v : IR.Expr} {size : Nat} :
    ∀ (xs : List (Option String)) (tys : List Ty) (i : Nat), xs.all Option.isSome = true →
      xs.length ≤ tys.length → (tuplePlaces v size xs tys i).length = xs.length
  | [], _, _, _, _ => by simp [tuplePlaces]
  | _ :: _, [], _, _, hl => by simp at hl
  | none :: _, _ :: _, _, ha, _ => by simp at ha
  | some n :: xs, t :: ts, i, ha, hl => by
    simp only [List.all_cons, Option.isSome_some, Bool.true_and] at ha
    have := tuplePlaces_length (v := v) (size := size) xs ts (i + 1) ha (by simpa using hl)
    simp [tuplePlaces, this]

/-- A pattern with a name in each place of a tuple reads every element. -/
theorem tuplePlaces_all {v : IR.Expr} {size : Nat} {ρo : Eval.Env N} {items : List (Val N)}
    (hv : IR.Expr.eval fs fuel ρo v = some (.list items)) :
    ∀ (xs : List (Option String)) (tys : List Ty) (i : Nat), xs.all Option.isSome = true →
      xs.length ≤ tys.length → i + xs.length = items.length →
      IR.Expr.evalList fs fuel ρo ((tuplePlaces v size xs tys i).map (·.2.2)) = some (items.drop i) ∧
        (tuplePlaces v size xs tys i).length = xs.length
  | [], _, i, _, _, hi => by
    simp only [List.length_nil, Nat.add_zero] at hi
    simp [tuplePlaces, IR.Expr.evalList, List.drop_eq_nil_of_le (by omega : items.length ≤ i)]
  | _ :: _, [], _, _, hl, _ => by simp at hl
  | none :: _, _ :: _, _, ha, _, _ => by simp at ha
  | some n :: xs, t :: ts, i, ha, hl, hi => by
    simp only [List.all_cons, Option.isSome_some, Bool.true_and] at ha
    obtain ⟨ih, hlen⟩ := tuplePlaces_all (size := size) hv xs ts (i + 1) ha (by simpa using hl) (by simp at hi; omega)
    refine ⟨?_, by simp [tuplePlaces, hlen]⟩
    simp only [tuplePlaces, Option.map_some, Option.toList_some, List.singleton_append, List.map_cons,
      IR.Expr.evalList]
    have hlt : i < items.length := by simp at hi; omega
    rw [List.drop_eq_getElem_cons hlt]
    simp [IR.Expr.eval, hv, ih, List.getElem?_eq_getElem hlt]

/-- The list that a loop over `items` visits is what the interpreter iterates
in the value of `items`. -/
theorem loopOver_vals {items : Code} {elem : Ty} {li : IR.Expr} (hlo : loopOver items = some (elem, li))
    {ρo : Eval.Env N} {vs : List (Val N)} (hi : IR.Expr.eval fs fuel ρo li = some (.list vs)) :
    ∃ v, IR.Expr.eval fs fuel ρo items.code = some v ∧ Eval.iterValues v = some vs := by
  unfold loopOver at hlo
  split at hlo <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hlo
  · obtain ⟨-, rfl⟩ := hlo
    exact ⟨_, hi, rfl⟩
  all_goals
    obtain ⟨-, rfl⟩ := hlo
    obtain ⟨ws, hws, happ⟩ := out_ext fs fuel hi
    simp only [IR.Expr.evalList] at hws
    cases hx : IR.Expr.eval fs fuel ρo items.value with
    | none => simp [hx] at hws
    | some w =>
      simp [hx] at hws
      subst hws
      rw [eval_value] at hx
      refine ⟨w, hx, ?_⟩
      cases w <;> simp [IR.ExprExt.apply] at happ
      subst happ
      rfl

/-- What the reads of a pattern give is what iterating the value of `c`
binds: the same names, with the same values. -/
theorem patternReads_vals {s : Span} {p : ArrayPattern} {c : Code}
    {reads : List (String × Ty × IR.Expr)} {ctx ctx' : Ctx}
    (h : patternReads s p c ctx = .ok reads ctx') (hne : reads ≠ [])
    {ρo : Eval.Env N} {ws : List (Val N)}
    (hws : IR.Expr.evalList fs fuel ρo (reads.map (·.2.2)) = some ws) :
    ∃ v vs, IR.Expr.eval fs fuel ρo c.code = some v ∧ Eval.iterValues v = some vs ∧
      Eval.patternBindings p vs = (reads.map (·.1)).zip ws := by
  cases hct : c.type.tupleElems? with
  | some tys =>
    simp only [patternReads, hct, ite_state] at h
    split at h
    · simp at h
    rename_i hrest
    simp only [pure_bind] at h
    split at h
    · rename_i hlen
      simp only [pure_ok] at h
      obtain ⟨rfl, -⟩ := h
      obtain ⟨items, hv⟩ := tuplePlaces_items fs fuel p.elems tys 0 ws hne hws
      refine ⟨_, items, by rwa [eval_value] at hv, rfl, ?_⟩
      have hp := tuplePlaces_sim fs fuel hv p.elems tys 0 ws (by simpa using hlen) hws
      simp only [List.drop_zero] at hp
      cases hr : p.rest with
      | some r => simp [hr] at hrest
      | none => simp [Eval.patternBindings, hr, hp]
    · simp at h
  | none =>
    simp only [patternReads, hct, bind_ok, orReject_ok] at h
    obtain ⟨⟨elem, li⟩, s₁, ⟨hlo, -⟩, h⟩ := h
    simp only [ite_state] at h
    split at h
    · simp at h
    simp only [pure_bind, pure_ok] at h
    obtain ⟨rfl, -⟩ := h
    simp only [List.map_append] at hws
    obtain ⟨w₁, w₂, rfl, h₁, h₂, hl₁⟩ := evalList_append_inv fs fuel hws
    -- Some read evaluates, so the list does.
    have hitems : ∃ items, IR.Expr.eval fs fuel ρo li = some (.list items) := by
      by_cases hn : listPlaces elem li p.elems 0 = []
      · cases hr : p.rest with
        | none => simp [hn, hr] at hne
        | some r =>
          simp only [hr, Option.map_some, Option.toList_some, List.map_cons, List.map_nil,
            IR.Expr.evalList] at h₂
          cases hw : IR.Expr.eval fs fuel ρo (.ext (.slice p.elems.length none) [li]) with
          | none => simp [hw] at h₂
          | some w =>
            obtain ⟨vs, hvs, happ⟩ := out_ext fs fuel hw
            simp only [IR.Expr.evalList] at hvs
            cases hx : IR.Expr.eval fs fuel ρo li with
            | none => simp [hx] at hvs
            | some x =>
              simp [hx] at hvs
              subst hvs
              cases x <;> simp [IR.ExprExt.apply] at happ
              exact ⟨_, rfl⟩
      · exact listPlaces_items fs fuel p.elems 0 w₁ hn h₁
    obtain ⟨items, hli⟩ := hitems
    obtain ⟨v, hv, hiter⟩ := loopOver_vals fs fuel hlo hli
    refine ⟨v, items, hv, hiter, ?_⟩
    have hp := listPlaces_sim fs fuel hli p.elems 0 w₁ h₁
    simp only [List.drop_zero] at hp
    have hlen : (listPlaces elem li p.elems 0).length = w₁.length := by
      rw [hl₁]; simp
    simp only [Eval.patternBindings, hp, List.map_append]
    cases hr : p.rest with
    | none =>
      simp only [hr, Option.map_none, Option.toList_none, List.map_nil, IR.Expr.evalList] at h₂ ⊢
      simp at h₂
      subst h₂
      simp
    | some r =>
      simp only [hr, Option.map_some, Option.toList_some, List.map_cons, List.map_nil,
        IR.Expr.evalList] at h₂ ⊢
      cases hw : IR.Expr.eval fs fuel ρo (.ext (.slice p.elems.length none) [li]) with
      | none => simp [hw] at h₂
      | some w =>
        simp [hw] at h₂
        subst h₂
        simp [IR.Expr.eval, IR.Expr.evalList, hli, IR.ExprExt.apply, sliceList_drop] at hw
        subst hw
        rw [List.zip_append (by simpa using hlen)]; rfl

/-- What the reads of a pattern give is what the interpreter binds: the value
of the initializer, iterated, gives the same names the same values. -/
theorem patternReads_sim {env : Translate.Env} {s : Span} {p : ArrayPattern} {c : Code}
    {reads : List (String × Ty × IR.Expr)} {ctx ctx' : Ctx} {init : Expr}
    (h : patternReads s p c ctx = .ok reads ctx')
    (hsim : Sim (N := N) m fs fuel env init c.code) (hne : reads ≠ [])
    {ρs ρo : Eval.Env N} (ha : Agree ρs ρo) (hs : Scoped m env ρs) {ws : List (Val N)}
    (hws : IR.Expr.evalList fs fuel ρo (reads.map (·.2.2)) = some ws) :
    ∃ v vs, Eval.eval m fuel ρs init = some v ∧ Eval.iterValues v = some vs ∧
      Eval.patternBindings p vs = (reads.map (·.1)).zip ws := by
  obtain ⟨v, vs, hv, hit, hp⟩ := patternReads_vals fs fuel h hne hws
  exact ⟨v, vs, hsim ρs ρo v ha hs hv, hit, hp⟩

omit [JSNumber N] in
theorem exactTuple_true {p : ArrayPattern} {t : Ty} (h : exactTuple p t = true) :
    ∃ tys, t = .tuple tys ∧ p.rest = none ∧ p.elems.all Option.isSome = true ∧
      p.elems.length = tys.length := by
  unfold exactTuple at h
  split at h
  · rename_i tys
    simp only [Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none] at h
    exact ⟨tys, rfl, h.1.1, h.1.2, h.2⟩
  · simp at h

/-- A `let (a, b) := e` binds the names to the elements of `e`, when `e` has
one element for each name. -/
theorem letTuple_exec {names : List String} {e : IR.Expr} {rb : IR.Body} {ρo : Eval.Env N}
    {o : Outcome N} (ho : IR.Body.exec fs fuel ρo (.letTuple names e rb) = some o) :
    ∃ vs, IR.Expr.eval fs fuel ρo e = some (.list vs) ∧ names.length = vs.length ∧
      IR.Body.exec fs fuel ((names.zip vs).reverse ++ ρo) rb = some o := by
  simp only [IR.Body.exec] at ho
  cases hw : IR.Expr.eval fs fuel ρo e with
  | none => simp [hw] at ho
  | some w =>
    cases w with
    | list vs =>
      simp only [hw, Option.bind_eq_bind, Option.bind_some] at ho
      split at ho
      · simp at ho
      · rename_i hl
        exact ⟨vs, rfl, by simpa using hl, ho⟩
    | _ => simp [hw] at ho

/-- The output of a pattern binds its names to what its reads give, all at
once, and then runs `rest`. -/
theorem destructureBody_exec {s : Span} {p : ArrayPattern} {t : Ty} {value : IR.Expr}
    {reads : List (String × Ty × IR.Expr)} {rest body : IR.Body} {ctx ctx' : Ctx}
    (hreads : patternReads s p ⟨value, false, t⟩ ctx = .ok reads ctx')
    (hbody : destructureBody p t value reads rest = some body)
    {ρo : Eval.Env N} {o : Outcome N} (ho : IR.Body.exec fs fuel ρo body = some o) :
    reads ≠ [] ∧ ∃ ws, ws.length = reads.length ∧ IR.Expr.evalList fs fuel ρo (reads.map (·.2.2)) = some ws ∧
      IR.Body.exec fs fuel (((reads.map (·.1)).zip ws).reverse ++ ρo) rest = some o := by
  unfold destructureBody at hbody
  split at hbody
  · simp at hbody
  · rename_i n ty e
    simp only [Option.some.injEq] at hbody
    subst hbody
    simp only [IR.Body.exec] at ho
    cases hw : IR.Expr.eval fs fuel ρo e with
    | none => simp [hw] at ho
    | some w =>
      simp only [hw, Option.bind_eq_bind, Option.bind_some] at ho
      exact ⟨by simp, [w], rfl, by simp [IR.Expr.evalList, hw], by simpa using ho⟩
  · rename_i hn1 _
    have hne : reads ≠ [] := hn1
    simp only [Option.some.injEq] at hbody
    subst hbody
    obtain ⟨vs, hv, hl, hb⟩ := letTuple_exec fs fuel ho
    refine ⟨hne, vs, by simpa using hl.symm, ?_, hb⟩
    split at hv
    · rename_i hex
      obtain ⟨tys, rfl, hnr, hsome, hlen⟩ := exactTuple_true hex
      -- The reads are the elements, in order.
      simp [patternReads, Ty.tupleElems?, hnr, hlen, Code.value] at hreads
      obtain ⟨rfl, -⟩ := hreads
      rw [List.length_map, tuplePlaces_length p.elems tys 0 hsome (by omega)] at hl
      obtain ⟨hev, -⟩ := tuplePlaces_all fs fuel hv p.elems tys 0 hsome (by omega) (by omega)
      simpa using hev
    · simp only [IR.Expr.eval] at hv
      cases he : IR.Expr.evalList fs fuel ρo (reads.map (·.2.2)) with
      | none => simp [he] at hv
      | some ws =>
        simp only [he, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq,
          Val.list.injEq] at hv
        subst hv
        rfl

/-- `const [a, b] = e` means what the source means, when the statements
after it do. -/
theorem translateDestructure_sound {tr : Option Ty → Expr → TM Code} {k : Translate.Env → TM IR.Body}
    {env : Translate.Env} {s : Span} {kind : VarKind} {p : ArrayPattern} {type : Option TypeExpr}
    {init : Expr} {rest : List Stmt} {tail : Tail} {ctx ctx' : Ctx} {body : IR.Body}
    (htr : ∀ exp e ctx c ctx', tr exp e ctx = .ok c ctx' → Sim (N := N) m fs fuel env e c.code)
    (hk : ∀ env' ctx b ctx', k env' ctx = .ok b ctx' → StmtSim (N := N) m fs fuel env' tail rest b)
    (hconst : (Stmt.destructure s kind p type init).constAssignedIn rest = false)
    (h : translateDestructure tr k env s kind p type init ctx = .ok body ctx') :
    StmtSim (N := N) m fs fuel env tail (.destructure s kind p type init :: rest) body := by
  simp only [translateDestructure, bind_ok, orReject_ok] at h
  obtain ⟨declared, s₁, -, code, s₂, hcode, t, s₃, -, reads, s₄, hreads, env', s₅, hdecl, rb, s₆, hrb,
    hbody, -⟩ := h
  have hsim := htr _ _ _ _ _ hcode
  have hsim' : Sim (N := N) m fs fuel env init (⟨withType code.value t code.type, false, t⟩ : Code).code := by
    intro ρs ρo w ha hs hw
    simp only at hw
    rw [eval_withType, eval_value] at hw
    exact hsim ρs ρo w ha hs hw
  obtain ⟨hfresh, hhas, hglob⟩ := declarePlaces_ok hdecl
  have hrest := hk _ _ _ _ hrb
  refine binds_sim m fs fuel (reads.map (·.1)) hfresh hhas hglob (fun n hn => by simp [stmtsChanges, hn]) ?_ hrest
  intro ρo o ho
  obtain ⟨hne, ws, hlen, hws, hb⟩ := destructureBody_exec fs fuel hreads hbody ho
  refine ⟨ws, by simpa using hlen, fun ρs ha hs => ?_, hb⟩
  obtain ⟨v, vs, hv, hit, hpb⟩ := patternReads_sim m fs fuel hreads hsim' hne ha hs hws
  simp [Eval.exec, Eval.execStmt, evalTop_ok m fuel hv, hit, hpb, hconst]

/-! ### Array destructuring in the head of a loop -/

omit [JSNumber N] in
theorem tuplePlaces_names {v : IR.Expr} {size : Nat} :
    ∀ (xs : List (Option String)) (tys : List Ty) (i : Nat), xs.length ≤ tys.length →
      (tuplePlaces v size xs tys i).map (·.1) = xs.filterMap id
  | [], _, _, _ => by simp [tuplePlaces]
  | _ :: _, [], _, hl => by simp at hl
  | none :: xs, _ :: ts, i, hl => by
    simp only [tuplePlaces, Option.map_none, Option.toList_none, List.nil_append]
    simpa using tuplePlaces_names (v := v) (size := size) xs ts (i + 1) (by simpa using hl)
  | some n :: xs, _ :: ts, i, hl => by
    simp [tuplePlaces, tuplePlaces_names (v := v) (size := size) xs ts (i + 1) (by simpa using hl)]

omit [JSNumber N] in
theorem listPlaces_names {elem : Ty} {li : IR.Expr} :
    ∀ (xs : List (Option String)) (i : Nat), (listPlaces elem li xs i).map (·.1) = xs.filterMap id
  | [], _ => rfl
  | none :: xs, i => by
    simp only [listPlaces, Option.map_none, Option.toList_none, List.nil_append]
    simpa using listPlaces_names (elem := elem) (li := li) xs (i + 1)
  | some n :: xs, i => by simp [listPlaces, listPlaces_names (elem := elem) (li := li) xs (i + 1)]

omit [JSNumber N] in
/-- The reads of a pattern bind its names, in order. -/
theorem patternReads_names {s : Span} {p : ArrayPattern} {c : Code}
    {reads : List (String × Ty × IR.Expr)} {ctx ctx' : Ctx}
    (h : patternReads s p c ctx = .ok reads ctx') : reads.map (·.1) = p.names := by
  unfold ArrayPattern.names
  cases hct : c.type.tupleElems? with
  | some tys =>
    simp only [patternReads, hct, ite_state] at h
    split at h
    · simp at h
    rename_i hrest
    simp only [pure_bind] at h
    split at h
    · rename_i hlen
      simp only [pure_ok] at h
      obtain ⟨rfl, -⟩ := h
      cases hr : p.rest with
      | some r => simp [hr] at hrest
      | none => simp [tuplePlaces_names _ _ _ (by simpa using hlen)]
    · simp at h
  | none =>
    simp only [patternReads, hct, bind_ok, orReject_ok] at h
    obtain ⟨⟨elem, li⟩, s₁, ⟨-, -⟩, h⟩ := h
    simp only [ite_state] at h
    split at h
    · simp at h
    simp only [pure_bind, pure_ok] at h
    obtain ⟨rfl, -⟩ := h
    cases p.rest <;> simp [listPlaces_names]

omit [JSNumber N] in
theorem lookup_append_or {n : String} : ∀ (a b : Eval.Env N), (a ++ b).lookup n = (a.lookup n).or (b.lookup n)
  | [], b => by simp
  | (k, v) :: a, b => by
    by_cases h : n = k
    · subst h; simp [List.lookup]
    · have h' : (n == k) = false := by simpa using h
      simp [List.lookup, h', lookup_append_or a b]

omit [JSNumber N] in
/-- The names of a pattern hide the loop element's own binding, which is one
of them. -/
theorem Agree.shadow {ρs ρo : Eval.Env N} (ha : Agree ρs ρo) {names : List String} {ws : List (Val N)}
    (hl : ws.length = names.length) {x : String} (hx : x ∈ names) (v : Val N) :
    Agree ((names.zip ws).reverse ++ ρs) ((names.zip ws).reverse ++ (x, v) :: ρo) := fun n => by
  rw [lookup_append_or, lookup_append_or]
  cases hb : ((names.zip ws).reverse).lookup n with
  | some w => rfl
  | none =>
    have hin : names.contains n = false := by
      have := lookup_isSome_reverse (x := n) (names.zip ws)
      rw [hb, lookup_isSome_zip hl] at this
      simpa using this.symm
    have hnx : (n == x) = false := by
      have : n ≠ x := fun h => by subst h; simp [hx] at hin
      simpa using this
    simp [List.lookup, hnx, ha n]

/-- One run of the body of a loop with a pattern: the output binds the names
of the pattern to what iterating the element gives, and then runs `inner`. -/
theorem patternStep_exec {s : Span} {p : ArrayPattern} {x : String} {elemType : Ty}
    {reads : List (String × Ty × IR.Expr)} {inner step : IR.Body} {ctx ctx' : Ctx}
    (hreads : patternReads s p ⟨.var x, false, elemType⟩ ctx = .ok reads ctx')
    (hstep : destructureBody p elemType (.var x) reads inner = some step)
    {v : Val N} {ρo : Eval.Env N} {ob : Outcome N}
    (h : IR.Body.exec fs fuel ((x, v) :: ρo) step = some ob) :
    ∃ ws vs, ws.length = reads.length ∧ Eval.iterValues v = some vs ∧
      Eval.patternBindings p vs = (reads.map (·.1)).zip ws ∧
      IR.Body.exec fs fuel (((reads.map (·.1)).zip ws).reverse ++ (x, v) :: ρo) inner = some ob := by
  obtain ⟨hne, ws, hlen, hws, hb⟩ := destructureBody_exec fs fuel hreads hstep h
  obtain ⟨w, vs, hw, hit, hpb⟩ := patternReads_vals fs fuel hreads hne hws
  simp [IR.Expr.eval, List.lookup] at hw
  subst hw
  exact ⟨ws, vs, hlen, hit, hpb, hb⟩

/-- The loop `for (const [k, v] of …)` over `vs` means what the output's fold
means, when the body does. The fold binds each element to the first name of
the pattern, and the body starts by binding all the names. -/
theorem loopPattern_sim {env bodyEnv : Translate.Env} {x : String} {p : ArrayPattern} {elemType : Ty}
    {reads : List (String × Ty × IR.Expr)} {names : List String} {b r : Bool} {bodyS : Stmt}
    {inner step : IR.Body} {s : Span} {ctx ctx' : Ctx}
    (hbody : StmtSim (N := N) m fs fuel bodyEnv (.loop names b r) (blockStatements bodyS) inner)
    (hreads : patternReads s p ⟨.var x, false, elemType⟩ ctx = .ok reads ctx')
    (hstep : destructureBody p elemType (.var x) reads inner = some step)
    (hx : x ∈ reads.map (·.1))
    (hfresh : ∀ n ∈ reads.map (·.1), env.has n = false)
    (hhas : ∀ n, bodyEnv.has n = (env.has n || (reads.map (·.1)).contains n))
    (hglob : globals bodyEnv = globals env)
    (hnames : names = changedNames (blockStatements bodyS) env) :
    ∀ (vs : List (Val N)) (ρs ρo : Eval.Env N) (o : Outcome N), Agree ρs ρo → Scoped m env ρs →
      IR.Body.runFold fs fuel names x step ρo vs = some o →
      (∀ w, o = .ret w → Eval.execLoop m fuel ρs
          (fun v => do return (Eval.patternBindings p (← Eval.iterValues v)).reverse) bodyS vs =
            some (.ret w)) ∧
      ∀ ρo', o = .normal ρo' → ∃ mod, Eval.execLoop m fuel ρs
          (fun v => do return (Eval.patternBindings p (← Eval.iterValues v)).reverse) bodyS vs =
            some (.normal mod) ∧
        Agree mod ρo' ∧ Frame (stmtChanges env.fnChanges bodyS) mod ρs := by
  simp only [StmtSim, fnChanges_congr hglob] at hbody
  intro vs
  induction vs with
  | nil =>
    intro ρs ρo o ha hs h
    simp only [IR.Body.runFold, Option.some.injEq] at h
    subst h
    refine ⟨fun w hw => (by cases hw), fun ρo' hρ => ?_⟩
    cases hρ
    exact ⟨ρs, by simp [Eval.execLoop], ha, Frame.refl _ _⟩
  | cons v vs ih =>
    intro ρs ρo o ha hs h
    simp only [IR.Body.runFold] at h
    cases hb0 : IR.Body.exec fs fuel ((x, v) :: ρo) step with
    | none => simp [hb0] at h
    | some ob =>
      obtain ⟨ws, ivs, hl, hit, hpb, hb⟩ := patternStep_exec fs fuel hreads hstep hb0
      have hl' : ws.length = (reads.map (·.1)).length := by simpa using hl
      have ha' := Agree.shadow ha hl' hx v
      have hs' : Scoped m bodyEnv (((reads.map (·.1)).zip ws).reverse ++ ρs) :=
        ⟨fun n => by
          rw [lookup_isSome_append, lookup_isSome_reverse, lookup_isSome_zip hl', hhas n, hs.1 n,
            Bool.or_comm],
         Resolves.congr hs.2 hglob⟩
      have hkeys : ∀ q ∈ ((reads.map (·.1)).zip ws).reverse, env.has q.1 = false := by
        intro q hq
        rw [List.mem_reverse] at hq
        exact hfresh _ (List.of_mem_zip hq).1
      -- A `return` in the body ends the loop, and the function.
      by_cases hr : ∃ w, ob = .ret w
      · obtain ⟨w, rfl⟩ := hr
        simp [hb0] at h
        subst h
        refine ⟨fun w' hw => ?_, fun ρo' hρ => by cases hρ⟩
        cases hw
        simp [Eval.execLoop, hit, hpb, block_ret m fuel bodyS ((hbody _ _ ha' hs').1 w hb)]
      -- Otherwise the body ends in its state, or in a `break`.
      obtain ⟨brk, inner', rfl⟩ : ∃ brk inner', ob = endOf brk inner' := by
        cases ob with
        | ret w => exact absurd ⟨w, rfl⟩ hr
        | cont _ => simp [hb0] at h
        | normal inner' => exact ⟨false, inner', rfl⟩
        | brk inner' => exact ⟨true, inner', rfl⟩
      · cases hbs : IR.bindState names inner' ρo with
        | none => cases brk <;> simp [endOf, hb0, hbs] at h
        | some ρo₁ =>
          obtain ⟨-, new, out, mod, hex, hag, -, hnew, hfr⟩ := (hbody _ _ ha' hs').2 brk inner' hb
          -- The body runs to its end or to a `continue`, and the loop goes on,
          -- or it runs to a `break`, and the loop ends.
          obtain ⟨e, he, hdrop, hlen⟩ : ∃ e,
              ((Eval.execStmt m fuel (((reads.map (·.1)).zip ws).reverse ++ ρs) bodyS = some (.normal e) ∨
                Eval.execStmt m fuel (((reads.map (·.1)).zip ws).reverse ++ ρs) bodyS = some (.cont e)) ∧
                  brk = false ∨
                Eval.execStmt m fuel (((reads.map (·.1)).zip ws).reverse ++ ρs) bodyS = some (.brk e) ∧
                  brk = true) ∧
              e.drop (e.length - (((reads.map (·.1)).zip ws).reverse ++ ρs).length) = mod ∧
              (((reads.map (·.1)).zip ws).reverse ++ ρs).length ≤ e.length := by
            cases brk
            · rcases hex with hex | hex
              · obtain ⟨e, h1, h2, h3⟩ := block_normal m fuel bodyS hex hfr
                exact ⟨e, .inl ⟨.inl h1, rfl⟩, h2, h3⟩
              · obtain ⟨e, h1, h2, h3⟩ := block_jump m fuel bodyS (.inl rfl) hex hfr
                exact ⟨e, .inl ⟨.inr h1, rfl⟩, h2, h3⟩
            · obtain ⟨e, h1, h2, h3⟩ := block_jump m fuel bodyS (.inr rfl) hex hfr
              exact ⟨e, .inr ⟨h1, rfl⟩, h2, h3⟩
          -- `mod` is the names of the pattern in front of the outer names.
          obtain ⟨ρ₁, ρ₂, rfl, h₁, h₂⟩ := Frame.split (a := ((reads.map (·.1)).zip ws).reverse) (b := ρs) hfr
          have hnext : e.drop (e.length - ρs.length) = ρ₂ := by
            have hl₁ := h₁.length
            have : e.length - ρs.length =
                (e.length - (((reads.map (·.1)).zip ws).reverse ++ ρs).length) + ρ₁.length := by
              simp only [List.length_append] at hlen ⊢; omega
            rw [this, ← List.drop_drop, hdrop, List.drop_left]
          have hag' : Agree ρ₂ ρo₁ := by
            intro n
            rw [bindState_lookup hbs n]
            split
            · rename_i hn
              rw [hnames, mem_changedNames] at hn
              rw [← hag n, lookup_append_fresh _ fun q hq hqn => by
                have := hnew q hq
                rw [hhas, hqn, hn.1] at this
                exact absurd this (by simp)]
              rw [lookup_append_fresh _ fun q hq hqn => by
                obtain ⟨q', hq', hk⟩ := Frame.mem h₁ hq
                have := hkeys q' hq'
                rw [← hk, hqn, hn.1] at this
                exact absurd this (by simp)]
            · rename_i hn
              rw [← ha n]
              by_cases hhas' : env.has n = true
              · have hnc : n ∉ stmtsChanges env.fnChanges (blockStatements bodyS) := fun hc =>
                  hn (by rw [hnames, mem_changedNames]; exact ⟨hhas', hc⟩)
                exact h₂.lookup hnc
              · have h1 := hs.none (by simpa using hhas')
                have h2 := h₂.isSome n
                rw [h1] at h2 ⊢
                simpa using h2
          rw [stmtsChanges_block] at h₂
          rcases he with ⟨he, rfl⟩ | ⟨he, rfl⟩
          · simp only [endOf, hb0, hbs, Option.bind_eq_bind, Option.bind_some] at h
            obtain ⟨hret, hnorm⟩ := ih ρ₂ ρo₁ o hag' (scoped_frame hs h₂) h
            refine ⟨fun w hw => ?_, fun ρo' hρ => ?_⟩
            · rcases he with he | he <;> simp [Eval.execLoop, hit, hpb, he, hnext] <;> exact hret w hw
            · obtain ⟨mod₂, hloop, hag₂, hfr₂⟩ := hnorm ρo' hρ
              refine ⟨mod₂, ?_, hag₂, (hfr₂.trans h₂).mono fun n hn => by simp at hn; exact hn⟩
              rcases he with he | he <;> simp [Eval.execLoop, hit, hpb, he, hnext] <;> exact hloop
          · simp [endOf, hb0, hbs] at h
            subst h
            refine ⟨fun w hw => (by cases hw), fun ρo' hρ => ?_⟩
            cases hρ
            exact ⟨ρ₂, by simp [Eval.execLoop, hit, hpb, he, hnext], hag', h₂⟩

/-- `translateForOfPattern` is sound, when what it calls is. -/
theorem translateForOfPattern_sound
    {items : TM Code} {kBody : Translate.Env → Tail → List Stmt → TM IR.Body} {kRest : TM IR.Body}
    {env : Translate.Env} {s : Span} {kind : VarKind} {p : ArrayPattern} {iterable : Expr} {b : Stmt}
    {rest : List Stmt} {tail : Tail} {ctx ctx' : Ctx} {body : IR.Body}
    (hitems : ∀ ctx c ctx', items ctx = .ok c ctx' → Sim (N := N) m fs fuel env iterable c.code)
    (hkBody : ∀ env' t ss ctx b ctx', kBody env' t ss ctx = .ok b ctx' →
      StmtSim (N := N) m fs fuel env' t ss b)
    (hkRest : ∀ ctx b ctx', kRest ctx = .ok b ctx' → StmtSim (N := N) m fs fuel env tail rest b)
    (h : translateForOfPattern items kBody kRest env s kind p iterable b tail ctx = .ok body ctx') :
    StmtSim (N := N) m fs fuel env tail (.forOfPattern s kind p iterable b :: rest) body := by
  unfold translateForOfPattern at h
  simp only [ite_state] at h
  split at h
  · rename_i hkind
    obtain rfl : kind = .const := by
      cases kind <;> first | rfl | simp +decide at hkind
    simp only [pure_bind, ite_state] at h
    split at h
    · simp at h
    · try simp only [pure_bind, ite_state] at h
      split at h
      · simp at h
      · simp only [bind_ok] at h
        obtain ⟨c, s₁, hc, h⟩ := h
        obtain ⟨⟨elemType, li⟩, s₁', hli, h⟩ := h
        obtain ⟨hmut, hlo, rfl⟩ := loopItems_ok hli
        simp only [orReject_ok] at h
        obtain ⟨x, s₂, ⟨hxh, rfl⟩, reads, s₃, hreads, bodyEnv, s₄, hdecl, bodyOut, s₅, hbody, step, s₆,
          ⟨hstep, rfl⟩, h⟩ := h
        simp at h
        obtain ⟨_, _, ⟨rfl, rfl⟩, _, _, ⟨rfl, rfl⟩, rb, hrb, hbodyEq⟩ := h
        obtain ⟨hfresh, hhas, hglob⟩ := declarePlaces_ok hdecl
        have hx : x ∈ reads.map (·.1) := by
          rw [patternReads_names hreads]
          exact List.mem_of_mem_head? hxh
        have hsimI := hitems _ _ _ hc
        have hloop := loopPattern_sim m fs fuel (hkBody _ _ _ _ _ _ hbody) hreads hstep hx hfresh hhas hglob rfl
        have hrest := hkRest _ _ _ hrb
        intro ρs ρo ha hs
        -- The loop returns from the function, or it ends and the statements
        -- after it run.
        have key : ∀ o, IR.Body.exec fs fuel ρo body = some o →
            (∃ w, o = .ret w ∧ Eval.execStmt m fuel ρs (.forOfPattern s .const p iterable b) = some (.ret w)) ∨
            ∃ mod ρo₂, Eval.execStmt m fuel ρs (.forOfPattern s .const p iterable b) = some (.normal mod) ∧
              Agree mod ρo₂ ∧ Frame (stmtChanges env.fnChanges (.forOfPattern s .const p iterable b)) mod ρs ∧
              IR.Body.exec fs fuel ρo₂ rb = some o := by
          intro o ho
          rw [← hbodyEq] at ho
          simp only [IR.Body.exec] at ho
          cases hi : IR.Expr.eval fs fuel ρo li with
          | none => simp [hi] at ho
          | some u =>
            cases u <;> simp [hi] at ho
            rename_i vs
            obtain ⟨vi, hvi, hiter⟩ := loopOver_sim m fs fuel hsimI hlo ha hs hi
            cases hf : IR.Body.runFold fs fuel (changedNames (blockStatements b) env) x step ρo vs with
            | none => simp [hf] at ho
            | some ro =>
              obtain ⟨hret, hnorm⟩ := hloop vs ρs ρo ro ha hs hf
              cases ro with
              | normal ρo₂ =>
                simp [hf] at ho
                obtain ⟨mod, hl, hag, hfr⟩ := hnorm ρo₂ rfl
                refine .inr ⟨mod, ρo₂, ?_, hag, hfr.mono fun n hn => by simp [stmtChanges, hn], ho⟩
                simp [Eval.execStmt, hmut, hvi, hiter]; exact hl
              | ret w =>
                simp [hf] at ho
                subst ho
                exact .inl ⟨w, rfl, by simp [Eval.execStmt, hmut, hvi, hiter]; exact hret w rfl⟩
              | brk _ | cont _ => simp [hf] at ho
        constructor
        · intro v hv
          rcases key _ hv with ⟨w, hw, hst⟩ | ⟨mod, ρo₂, hst, hag, hfr, hb⟩
          · cases hw
            simp [Eval.exec, hst]
          have := (hrest mod ρo₂ hag (scoped_frame hs hfr)).1 v hb
          simp [Eval.exec, hst, this]
        · intro brk ρo' hv
          rcases key _ hv with ⟨w, hw, -⟩ | ⟨mod, ρo₂, hst, hag, hfr, hb⟩
          · cases brk <;> cases hw
          obtain ⟨htail, new, out, mod₂, hex, hag₂, hnew, hout, hfr₂⟩ :=
            (hrest mod ρo₂ hag (scoped_frame hs hfr)).2 brk ρo' hb
          refine ⟨htail, new, out, mod₂, Ends.congr (by simp [Eval.exec, hst]) hex, hag₂, hnew, hout, ?_⟩
          simpa [stmtsChanges] using hfr₂.trans hfr
  · simp at h

/-- The statement functions of the translator are sound, at every fuel for
which calls agree at that fuel and below. The body of a local function runs
with less fuel than its call, so the induction on `F` keeps the fuel general. -/
theorem stmts_sound (F : Nat) : ∀ fuel, (∀ k ≤ fuel, CallsAgree (N := N) m.program fs k) →
    (∀ env tail ss ctx body ctx', translateStatements F env tail ss ctx = .ok body ctx' →
      StmtSim (N := N) m fs fuel env tail ss body) ∧
    (∀ env s d rest tail ctx body ctx', translateVariable F env s d rest tail ctx = .ok body ctx' →
      StmtSim (N := N) m fs fuel env tail (.varDecl s d :: rest) body) ∧
    (∀ env s test t e rest tail ctx body ctx', translateIf F env s test t e rest tail ctx = .ok body ctx' →
      StmtSim (N := N) m fs fuel env tail (.ifStmt s test t e :: rest) body) ∧
    (∀ env s head b rest tail ctx body ctx',
      translateLoop F env s head b rest tail ctx = .ok body ctx' →
      StmtSim (N := N) m fs fuel env tail (head.stmt s b :: rest) body) ∧
    (∀ env s disc cs rest tail ctx body ctx', translateSwitch F env s disc cs rest tail ctx = .ok body ctx' →
      StmtSim (N := N) m fs fuel env tail (.switchStmt s disc cs :: rest) body) ∧
    (∀ env s sw tags known cs rest ctx body ctx',
      translateClauses F env s sw tags known cs rest ctx = .ok body ctx' →
      ClauseSim (N := N) m fs fuel env sw known cs rest body) ∧
    (∀ env s sw tags known names cs ctx body ctx',
      translateStateClauses F env s sw tags known names cs ctx = .ok body ctx' →
      StateClauseSim (N := N) m fs fuel env sw known cs body) ∧
    (∀ env s names last body ctx b ctx', translateStateClause F env s names last body ctx = .ok b ctx' →
      (last = true ∨ endsInBreak body = true) ∧
        StmtSim (N := N) m fs fuel env (.state names) (dropBreak body) b) := by
  induction F with
  | zero =>
    intro fuel _
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro _ _ _ _ _ _ h; simp [translateStatements] at h
    · intro _ _ _ _ _ _ _ _ h; simp [translateVariable] at h
    · intro _ _ _ _ _ _ _ _ _ _ h; simp [translateIf] at h
    · intro _ _ _ _ _ _ _ _ _ h; simp [translateLoop] at h
    · intro _ _ _ _ _ _ _ _ _ h; simp [translateSwitch] at h
    · intro _ _ _ _ _ _ _ _ _ _ h; simp [translateClauses] at h
    · intro _ _ _ _ _ _ _ _ _ _ h; simp [translateStateClauses] at h
    · intro _ _ _ _ _ _ _ _ h; simp [translateStateClause] at h
  | succ F ih =>
    intro fuel hcA
    have hc := hcA fuel (Nat.le_refl _)
    obtain ⟨ihS, ihV, ihI, ihF, ihW, ihC, ihSC, ihA⟩ := ih fuel hcA
    -- The body of a local function, at the fuel that its call leaves.
    have ihL : ∀ k, fuel = k + 1 → ∀ env tail ss ctx body ctx',
        translateStatements F env tail ss ctx = .ok body ctx' → StmtSim (N := N) m fs k env tail ss body :=
      fun k hk => (ih k fun j hj => hcA j (by omega)).1
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro env tail ss ctx body ctx' h
      have h₀ := h
      unfold translateStatements at h
      cases ss with
      | nil =>
        cases tail with
        | ret | cont _ _ _ => simp at h
        | state names | loop names _ _ =>
          simp only [pure_ok] at h
          obtain ⟨rfl, -⟩ := h
          intro ρs ρo ha hs
          refine ⟨fun v hv => by simp [IR.Body.exec, exec_stepEnd] at hv, fun brk ρo' hv => ?_⟩
          simp only [IR.Body.exec, exec_stepEnd] at hv
          obtain ⟨rfl, rfl⟩ := endOf_normal hv
          exact ⟨rfl, [], [], ρs, by simp [Ends, Eval.exec], ha, by simp, by simp, Frame.refl _ _⟩
      | cons stmt rest =>
        cases stmt with
        | varDecl sp d => exact ihV _ _ _ _ _ _ _ _ h
        | destructure sp kind p type init =>
          simp only [ite_state] at h
          split at h
          · simp at h
          rename_i hconst
          simp only [pure_bind, ite_state] at h
          split at h
          · simp at h
          exact translateDestructure_sound m fs fuel
            (fun _ _ _ _ _ hx => by
              simp only [bind_ok, fuelLimit_ok] at hx
              obtain ⟨_, _, ⟨rfl, rfl⟩, hx⟩ := hx
              exact (expr_sound m fs fuel hc _).1 _ _ _ _ _ _ hx)
            (fun _ _ _ _ hb => ihS _ _ _ _ _ _ hb) (by simpa using hconst) h
        | ifStmt sp test t e => exact ihI _ _ _ _ _ _ _ _ _ _ h
        | forOfStmt sp kind x iterable b => exact ihF _ _ (.forOf kind x iterable) _ _ _ _ _ _ h
        | forStmt sp init test update b => exact ihF _ _ (.counted init test update) _ _ _ _ _ _ h
        | forOfPattern sp kind p iterable b =>
          exact translateForOfPattern_sound m fs fuel
            (fun _ _ _ hx => by
              simp only [bind_ok, fuelLimit_ok] at hx
              obtain ⟨_, _, ⟨rfl, rfl⟩, hx⟩ := hx
              exact translateRecv_sim m fs fuel
                (fun _ _ _ hx => (expr_sound m fs fuel hc _).1 _ _ _ _ _ _ hx) hx)
            (fun _ _ _ _ _ _ hb => ihS _ _ _ _ _ _ hb) (fun _ _ _ hb => ihS _ _ _ _ _ _ hb) h
        | returnStmt sp value =>
          cases rest <;> cases value <;> simp only at h <;> try (simp at h; done)
          cases hcr : tail.canReturn <;> simp only [hcr] at h <;> try (simp at h; done)
          rename_i v
          rcases hlc : localCall? env v with _ | ⟨largs, lfn⟩
          rotate_left
          · -- `return g(a)`, where `g` is a local function.
            exact translateLocalReturn_sound m fs fuel hc ihL hcr hlc h₀
          simp only [hlc, pure_bind] at h
          rcases htc : throwingCall? env.functions v with _ | ⟨cs, sp', name, args⟩
          rotate_left
          · -- `return f(a)`, where `f` can throw: the output passes its error on.
            simp only [htc] at h
            obtain rfl := throwingCall?_some htc
            simp only [bind_ok, pure_ok] at h
            obtain ⟨⟨ref, outs⟩, s₁, hrc, rfl, -⟩ := h
            obtain ⟨rfl, F', c, ctx₁, ctx₂, htr, hcode⟩ := translateReturnCall_ok hrc
            exact returnCall_sim m fs fuel (translateCall_callSim m fs fuel hc htr hcode)
          simp only [htc] at h
          -- The output returns the value of the code, from the function or
          -- from its loop.
          have hret : ∀ (ρ : Eval.Env N) (c : IR.Expr), IR.Body.exec fs fuel ρ (tail.returnBody c) =
              (do return .ret (.ok (← IR.Expr.eval fs fuel ρ c))) := by
            intro ρ c
            cases tail <;> simp [Tail.returnBody, IR.Body.exec]
          simp only [bind_ok, modify_ok, get_ok, fuelLimit_ok, ite_state] at h
          obtain ⟨_, s₁, rfl, _, _, ⟨rfl, rfl⟩, _, _, ⟨rfl, rfl⟩, code, s₂, hcode, h⟩ := h
          split at h
          · simp only [bind_ok, modify_ok, get_ok, pure_ok] at h
            obtain ⟨_, _, rfl, _, _, ⟨rfl, rfl⟩, rfl, -⟩ := h
            have hsim := (expr_sound m fs fuel hc _).1 _ _ _ _ _ _ hcode
            intro ρs ρo ha hs
            constructor
            · intro w hw
              simp only [hret, eval_pureIf, eval_value] at hw
              cases hv : IR.Expr.eval fs fuel ρo code.code with
              | none => simp [hv] at hw
              | some u =>
                simp [hv] at hw
                subst hw
                simp [Eval.exec, Eval.execStmt, evalTop_ok m fuel (hsim ρs ρo u ha hs hv)]
            · intro brk ρo' hv
              simp only [hret, eval_pureIf] at hv
              cases hv' : IR.Expr.eval fs fuel ρo code.value <;> cases brk <;> simp [hv', endOf] at hv
          · simp at h
        | exprStmt sp e =>
          rcases hlc : localCall? env e with _ | ⟨largs, lfn⟩
          rotate_left
          · -- `g(a);`, where `g` is a local function.
            exact translateLocalStmt_sound m fs fuel hc ihS ihL hlc h₀
          simp only [hlc, pure_bind] at h
          simp only [bind_ok] at h
          obtain ⟨⟨name, upd⟩, s₁, hu, rb, s₂, hr, h⟩ := h
          simp only [pure_ok] at h
          obtain ⟨rfl, -⟩ := h
          have hrest := ihS _ _ _ _ _ _ hr
          intro ρs ρo ha hs
          have key : ∀ o, IR.Body.exec fs fuel ρo (.let name upd rb) = some o →
              ∃ w, IR.Expr.eval fs fuel ρo upd = some w ∧
                IR.Body.exec fs fuel ((name, w) :: ρo) rb = some o := by
            intro o ho
            simp only [IR.Body.exec] at ho
            cases hw : IR.Expr.eval fs fuel ρo upd with
            | none => simp [hw] at ho
            | some w => exact ⟨w, rfl, by simpa [hw] using ho⟩
          have hs' : ∀ w, Scoped m env (ρs.set name w) := fun w =>
            scoped_frame hs (Frame.set (c := [name]) (by simp) ρs)
          constructor
          · intro v hv
            obtain ⟨w, hw, hb⟩ := key _ hv
            obtain ⟨hhas, -, hex⟩ := update_sound m fs fuel hc hu ha hs hw
            have := (hrest _ _ (agree_set ha (hs.some hhas)) (hs' w)).1 v hb
            simp [Eval.exec, hex, this]
          · intro brk ρo' hv
            obtain ⟨w, hw, hb⟩ := key _ hv
            obtain ⟨hhas, hch, hex⟩ := update_sound m fs fuel hc hu ha hs hw
            obtain ⟨htail, new, out, mod, hexr, ha', hnew, hout, hfr⟩ :=
              (hrest _ _ (agree_set ha (hs.some hhas)) (hs' w)).2 brk ρo' hb
            refine ⟨htail, new, out, mod, Ends.congr (by simp [Eval.exec, hex]) hexr, ha', hnew, hout, ?_⟩
            refine (hfr.trans (Frame.set (c := [name]) (by simp) ρs)).mono ?_
            intro n hn
            simp only [List.mem_append, List.mem_singleton] at hn
            simp only [stmtsChanges, stmtChanges, List.mem_append]
            rcases hn with rfl | hn
            · exact .inl hch
            · exact .inr hn
        | switchStmt sp disc cs => exact ihW _ _ _ _ _ _ _ _ _ h
        | continueStmt sp =>
          -- `continue` ends the loop body in its state as it is.
          cases htc : tail.continues with
          | none => simp [htc] at h
          | some next =>
            cases rest with
            | cons _ _ => simp [htc] at h
            | nil =>
              simp [htc] at h
              obtain ⟨rfl, -⟩ := h
              -- `next` ends the run of the body in its state as it is.
              obtain ⟨names, b, r, rfl, htl, hends⟩ : ∃ names b r, next = stepEnd names b r ∧
                  tail.isRet = false ∧ ∀ e : Eval.Env N, Ends tail false (some (.cont e)) e := by
                cases tail <;> simp [Tail.continues] at htc
                all_goals exact ⟨_, _, _, htc.symm, rfl, fun e => by simp [Ends]⟩
              intro ρs ρo ha hs
              refine ⟨fun v hv => by simp [exec_stepEnd] at hv, fun brk ρo' hv => ?_⟩
              rw [exec_stepEnd] at hv
              obtain ⟨rfl, rfl⟩ := endOf_normal hv
              exact ⟨htl, [], [], ρs, Ends.congr (by simp [Eval.exec, Eval.execStmt]) (hends ρs), ha,
                by simp, by simp, Frame.refl _ _⟩
        | breakStmt sp =>
          -- `break` ends the loop in its state as it is.
          cases htb : tail.breaks with
          | none => simp [htb] at h
          | some done =>
            cases rest with
            | cons _ _ => simp [htb] at h
            | nil =>
              simp [htb] at h
              obtain ⟨rfl, -⟩ := h
              obtain ⟨names, r, rfl, htl⟩ : ∃ names r, done = .done names r ∧ tail.isRet = false := by
                cases tail with
                | loop _ b _ | cont _ b _ =>
                  cases b <;> simp [Tail.breaks] at htb
                  exact ⟨_, _, htb.symm, rfl⟩
                | _ => simp [Tail.breaks] at htb
              intro ρs ρo ha hs
              refine ⟨fun v hv => by simp [IR.Body.exec] at hv, fun brk ρo' hv => ?_⟩
              cases brk <;> simp [IR.Body.exec, endOf] at hv
              subst hv
              exact ⟨htl, [], [], ρs, Ends.congr (by simp [Eval.exec, Eval.execStmt]) (Ends.of_brk htl ρs), ha,
                by simp, by simp, Frame.refl _ _⟩
        | throwStmt sp value =>
          simp only [Bool.and_eq_true, ite_state] at h
          split at h
          · rename_i hok
            obtain ⟨hrest, hret⟩ := hok
            cases rest <;> simp at hrest
            cases tail <;> simp [Tail.isRet] at hret
            simp only [pure_bind] at h
            split at h
            · next sn msg =>
              simp only [ite_state] at h
              split at h
              · simp at h
              · rename_i herr
                simp only [bind_ok, fuelLimit_ok] at h
                obtain ⟨_, _, ⟨rfl, rfl⟩, code, s₁, hcode, h⟩ := h
                simp only [ite_state] at h
                split at h
                · simp only [pure_ok] at h
                  obtain ⟨rfl, -⟩ := h
                  have hsim := (expr_sound m fs fuel hc _).1 _ _ _ _ _ _ hcode
                  exact throw_sim m fs fuel (fun ρs ρo w ha hs hw => hsim ρs ρo w ha hs (by rwa [eval_value] at hw))
                    (by simpa using herr)
                · simp at h
            · simp at h
          · simp at h
        | funDecl sp name tps params rt fbody => exact translateFunDecl_sound m fs fuel ihS h₀
        | _ => simp at h
    · exact translateVariable_sound m fs fuel hc ihS ihL
    · exact translateIf_sound m fs fuel hc ihS
    · exact translateLoop_sound m fs fuel hc ihS
    · exact translateSwitch_sound m fs fuel ihS ihC ihSC
    · exact translateClauses_sound m fs fuel ihS ihC
    · exact translateStateClauses_sound m fs fuel ihSC ihA
    · exact translateStateClause_sound m fs fuel ihS

end tolean.TypeScript.Proof
