import tolean.TypeScript.Proof.Expr
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

theorem has_add (env : Translate.Env) (l : Local) (x : String) :
    (env.add l).has x = (env.has x || l.name == x) := by
  simp only [Env.has, Env.lookup, Env.add, List.find?_append]
  cases env.locals.find? (·.name == x) <;> simp [List.find?]
  split <;> simp_all

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

@[simp] theorem fuelLimit_ok {s s' : Ctx} {n : Nat} : fuelLimit s = .ok n s' ↔ n = s.fuel ∧ s' = s := by
  simp only [fuelLimit, bind_ok, get_ok, pure_ok]
  constructor
  · rintro ⟨c, s₁, ⟨rfl, rfl⟩, rfl, rfl⟩; exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩; exact ⟨_, _, ⟨rfl, rfl⟩, rfl, rfl⟩

@[simp] theorem throw_ne_ok {e : String} {s s' : Ctx} {a : α} : (throw e : TM α) s ≠ .ok a s' := by
  simp [throw, throwThe, MonadExceptOf.throw, EStateM.throw]

theorem checkName_ok {sp : Span} {name r : String} {s s' : Ctx} :
    checkName sp name s = .ok r s' → r = name ∧ s' = s := by
  simp only [checkName, ite_state]
  split
  · simp
  · simp only [pure_bind, pure_ok]; rintro ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩

theorem checkLocalName_ok {sp : Span} {name r : String} {s s' : Ctx}
    (h : checkLocalName sp name s = .ok r s') : r = name ∧ s' = s := by
  simp only [checkLocalName, bind_ok, get_ok, ite_state] at h
  obtain ⟨c, s₁, ⟨rfl, rfl⟩, h⟩ := h
  split at h
  · simp at h
  · simp only [pure_bind, ite_state] at h
    split at h
    · simp at h
    · exact checkName_ok h

theorem declare_ok {env env' : Translate.Env} {sp : Span} {name : String} {b : Binding} {t : Ty}
    {s s' : Ctx} (h : declare env sp name b t s = .ok env' s') :
    env.has name = false ∧ env' = env.add { name, binding := b, type := t } ∧ s' = s := by
  simp only [declare, ite_state] at h
  split at h
  · simp at h
  · rename_i hn
    simp only [pure_bind, ite_state] at h
    split at h
    · simp at h
    · simp only [bind_ok] at h
      obtain ⟨r, s₁, hr, h⟩ := h
      obtain ⟨-, rfl⟩ := checkLocalName_ok hr
      simp only [pure_ok] at h
      exact ⟨by simpa using hn, h.1.symm, h.2.symm⟩

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

/-- An update statement sets a name in scope to the value of the output's
update. -/
theorem update_sound (hc : CallsAgree (N := N) m.program fs fuel) {env : Translate.Env} {sp : Span} {e : Expr}
    {ctx ctx' : Ctx} {name : String} {upd : IR.Expr}
    (h : translateUpdate env sp e ctx = .ok (name, upd) ctx')
    {ρs ρo : Eval.Env N} (ha : Agree ρs ρo) (hs : Scoped m env ρs) {w : Val N}
    (hw : IR.Expr.eval fs fuel ρo upd = some w) :
    env.has name = true ∧ name ∈ exprChanges e ∧
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
          refine ⟨by simp [Env.has, hl], by simp [exprChanges], ?_⟩
          simp [Eval.execStmt, hx, hsim ρs ρo va ha hs hva]
        · simp at h
    · simp [hf] at h
  case assign sp' op target right =>
    cases target <;> (try simp only at h) <;> try (simp at h; done)
    rename_i sp1 x
    simp only [ite_state] at h
    split at h
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
        all_goals obtain ⟨⟨rfl, rfl⟩, -⟩ := h
        all_goals refine ⟨hhas, by simp [exprChanges, AssignOp.isSimple], ?_⟩
        · rw [eval_value] at hw
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

/-- The output body `body` means what the statements `ss` mean. A return gives
the same value. An end, which only a body for a branch or a loop has, gives
environments that agree: the interpreter's has new bindings, which `env`
does not have, in front of the old names, and it changes only the names that
`ss` change. -/
def StmtSim (env : Translate.Env) (tail : Tail) (ss : List Stmt) (body : IR.Body) : Prop :=
  ∀ (ρs ρo : Eval.Env N), Agree ρs ρo → Scoped m env ρs →
    (∀ v, IR.Body.exec fs fuel ρo body = some (.ret v) → Eval.exec m fuel ρs ss = some (.ret v)) ∧
    (∀ ρo', IR.Body.exec fs fuel ρo body = some (.normal ρo') →
      tail.isRet = false ∧ ∃ new mod, Eval.exec m fuel ρs ss = some (.normal (new ++ mod)) ∧
        Agree (new ++ mod) ρo' ∧ (∀ p ∈ new, env.has p.1 = false) ∧ Frame (stmtsChanges ss) mod ρs)

/-! ### The interpreter on statements -/

theorem exec_single (t : Stmt) (ρ : Eval.Env N) : Eval.exec m fuel ρ [t] = Eval.execStmt m fuel ρ t := by
  simp only [Eval.exec]
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
      | .normal ρ' => some (.normal (ρ'.drop (ρ'.length - ρ.length)))) := by
  rw [Eval.execStmt]; rfl

theorem block_ret (t : Stmt) {ρ : Eval.Env N} {v : Val N}
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
      | .normal ρ' => some (.normal (ρ'.drop (ρ'.length - ρ.length)))) := by
  rw [Eval.execStmt]; rfl

/-- The statements of the branch that the test picks. -/
def branchStatements (w : Val N) (t : Stmt) (e : Option Stmt) : List Stmt :=
  if w.truthy then blockStatements t else (e.map blockStatements).getD []

theorem if_ret {sp : Span} {test : Expr} {t : Stmt} {e : Option Stmt} {ρ : Eval.Env N} {w v : Val N}
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

omit [JSNumber N] in
theorem stmtsChanges_append (a b : List Stmt) : stmtsChanges (a ++ b) = stmtsChanges a ++ stmtsChanges b := by
  induction a with
  | nil => simp [stmtsChanges]
  | cons s rest ih => simp [stmtsChanges, ih]

omit [JSNumber N] in
theorem stmtsChanges_block (t : Stmt) : stmtsChanges (blockStatements t) = stmtChanges t := by
  cases t <;> simp [blockStatements, stmtsChanges, stmtChanges]

omit [JSNumber N] in
theorem mem_changedNames {ss : List Stmt} {env : Translate.Env} {n : String} :
    n ∈ changedNames ss env ↔ env.has n = true ∧ n ∈ stmtsChanges ss := by
  simp only [changedNames, List.mem_map, List.mem_filter, Env.has, Env.lookup, List.find?_isSome,
    List.contains_iff_mem, beq_iff_eq]
  constructor
  · rintro ⟨l, ⟨hl, hc⟩, rfl⟩; exact ⟨⟨l, hl, rfl⟩, hc⟩
  · rintro ⟨⟨l, hl, rfl⟩, hc⟩; exact ⟨l, ⟨hl, hc⟩, rfl⟩

/-- A declaration, whose output binds `d.name` to the value of the
initializer, means what the source means, when the rest does. -/
theorem decl_sim {env env' : Translate.Env} {s : Span} {d : VarDecl} {init : Expr} {rest : List Stmt}
    {tail : Tail} {body rb : IR.Body} {b : Binding} {ty : Ty}
    (hinit : d.init = some init) (hfresh : env.has d.name = false)
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
    simp [Eval.exec, Eval.execStmt, hw]
  constructor
  · intro v hv
    obtain ⟨w, hw, hb⟩ := hbody ρo _ hv
    rw [hstep w (hw ρs ha hs)]
    exact ((hrest _ _ (ha' w) (hs' w)).1 v hb)
  · intro ρo' hv
    obtain ⟨w, hw, hb⟩ := hbody ρo _ hv
    obtain ⟨htail, new, mod, hex, hag, hnew, hfr⟩ := (hrest _ _ (ha' w) (hs' w)).2 ρo' hb
    obtain ⟨ρ₁, ρ₂, rfl, h₁, h₂⟩ := Frame.split (a := [(name, w)]) (b := ρs) hfr
    refine ⟨htail, new ++ ρ₁, ρ₂, ?_, ?_, ?_, ?_⟩
    · rw [hstep w (hw ρs ha hs), hex, List.append_assoc]
    · rwa [List.append_assoc]
    · intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · have := hnew p hp
        rw [has_add] at this
        simp only [Bool.or_eq_false_iff] at this
        exact this.1
      · obtain ⟨q, hq, hk⟩ := Frame.mem h₁ hp
        simp only [List.mem_singleton] at hq
        subst hq
        rw [hk]; exact hfresh
    · exact h₂.mono fun n hn => by simp [stmtsChanges, hn]

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

/-- An `if` whose branches both return. -/
theorem if_ret_sim {env envT envF : Translate.Env} {sp : Span} {test : Expr} {t : Stmt}
    {e : Option Stmt} {rest : List Stmt} {tail : Tail} {br wt wf : IR.Body}
    (hT : ∀ x, envT.has x = env.has x) (hF : ∀ x, envF.has x = env.has x)
    (hTf : envT.functions = env.functions) (hFf : envF.functions = env.functions)
    (htail : tail.isRet = true) (hrest : e.isSome = true → rest = [])
    (hbr : BranchSim (N := N) m fs fuel env test br wt wf)
    (hwt : StmtSim (N := N) m fs fuel envT tail (blockStatements t) wt)
    (hwf : StmtSim (N := N) m fs fuel envF tail ((e.map blockStatements).getD [] ++ rest) wf) :
    StmtSim (N := N) m fs fuel env tail (.ifStmt sp test t e :: rest) br := by
  intro ρs ρo ha hs
  have hsT : Scoped m envT ρs := ⟨fun x => (hs.1 x).trans (hT x).symm, fun f hf => hs.2 f (hTf ▸ hf)⟩
  have hsF : Scoped m envF ρs := ⟨fun x => (hs.1 x).trans (hF x).symm, fun f hf => hs.2 f (hFf ▸ hf)⟩
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
  · intro ρo' hv
    obtain ⟨w, hw, hb⟩ := hbr ρs ρo _ ha hs hv
    cases htr : w.truthy <;> simp only [htr, Bool.false_eq_true, ↓reduceIte] at hb
    · have := ((hwf ρs ρo ha hsF).2 ρo' hb).1
      rw [htail] at this; exact absurd this (by simp)
    · have := ((hwt ρs ρo ha hsT).2 ρo' hb).1
      rw [htail] at this; exact absurd this (by simp)

/-- An `if` whose branches end in the state of the locals they change. -/
theorem if_state_sim {env envT envF : Translate.Env} {sp : Span} {test : Expr} {t : Stmt}
    {e : Option Stmt} {rest : List Stmt} {tail : Tail} {br wt wf rb : IR.Body} {names : List String}
    (hT : ∀ x, envT.has x = env.has x) (hF : ∀ x, envF.has x = env.has x)
    (hTf : envT.functions = env.functions) (hFf : envF.functions = env.functions)
    (hnames : names = changedNames (blockStatements t ++ (e.map blockStatements).getD []) env)
    (hbr : BranchSim (N := N) m fs fuel env test br wt wf)
    (hwt : StmtSim (N := N) m fs fuel envT (.state names) (blockStatements t) wt)
    (hwf : StmtSim (N := N) m fs fuel envF (.state names) ((e.map blockStatements).getD []) wf)
    (hrest : StmtSim (N := N) m fs fuel env tail rest rb) :
    StmtSim (N := N) m fs fuel env tail (.ifStmt sp test t e :: rest) (.letState names br rb) := by
  intro ρs ρo ha hs
  have hsT : Scoped m envT ρs := ⟨fun x => (hs.1 x).trans (hT x).symm, fun f hf => hs.2 f (hTf ▸ hf)⟩
  have hsF : Scoped m envF ρs := ⟨fun x => (hs.1 x).trans (hF x).symm, fun f hf => hs.2 f (hFf ▸ hf)⟩
  -- The `if` ends in `mod`, which agrees with the output's state after the
  -- `letState`.
  have key : ∀ o, IR.Body.exec fs fuel ρo (.letState names br rb) = some o →
      ∃ mod ρo₂, Eval.execStmt m fuel ρs (.ifStmt sp test t e) = some (.normal mod) ∧
        Agree mod ρo₂ ∧ Frame (stmtChanges (.ifStmt sp test t e)) mod ρs ∧
        IR.Body.exec fs fuel ρo₂ rb = some o := by
    intro o ho
    simp only [IR.Body.exec] at ho
    cases hb : IR.Body.exec fs fuel ρo br with
    | none => simp [hb] at ho
    | some ob =>
      cases ob with
      | ret v => simp [hb] at ho
      | normal inner =>
        cases hbs : IR.bindState names inner ρo with
        | none => simp [hb, hbs] at ho
        | some ρo₂ =>
          simp only [hb, hbs, Option.bind_eq_bind, Option.bind_some] at ho
          obtain ⟨w, hw, hbw⟩ := hbr ρs ρo _ ha hs hb
          have hside : ∃ new mod, Eval.exec m fuel ρs (branchStatements w t e) = some (.normal (new ++ mod)) ∧
              Agree (new ++ mod) inner ∧ (∀ p ∈ new, env.has p.1 = false) ∧
              Frame (stmtsChanges (branchStatements w t e)) mod ρs := by
            unfold branchStatements
            cases htr : w.truthy <;> simp only [htr, Bool.false_eq_true, ↓reduceIte] at hbw ⊢
            · obtain ⟨-, new, mod, h1, h2, h3, h4⟩ := (hwf ρs ρo ha hsF).2 inner hbw
              exact ⟨new, mod, h1, h2, fun p hp => (hF p.1) ▸ h3 p hp, h4⟩
            · obtain ⟨-, new, mod, h1, h2, h3, h4⟩ := (hwt ρs ρo ha hsT).2 inner hbw
              exact ⟨new, mod, h1, h2, fun p hp => (hT p.1) ▸ h3 p hp, h4⟩
          obtain ⟨new, mod, hex, hag, hnew, hfr⟩ := hside
          have hsub : ∀ n, n ∈ stmtsChanges (branchStatements w t e) →
              n ∈ stmtsChanges (blockStatements t ++ (e.map blockStatements).getD []) := by
            intro n hn
            unfold branchStatements at hn
            rw [stmtsChanges_append]
            split at hn <;> simp [hn]
          have hsub2 : ∀ n, n ∈ stmtsChanges (blockStatements t ++ (e.map blockStatements).getD []) →
              n ∈ stmtChanges (.ifStmt sp test t e) := by
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
            · have hnc : n ∉ stmtsChanges (branchStatements w t e) := fun hc =>
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
  · intro ρo' hv
    obtain ⟨mod, ρo₂, hif, hag, hfr, hb⟩ := key _ hv
    obtain ⟨htail, new, mod₂, hex, hag₂, hnew, hfr₂⟩ := (hrest mod ρo₂ hag (scoped_frame hs hfr)).2 ρo' hb
    refine ⟨htail, new, mod₂, by simp [Eval.exec, hif, hex], hag₂, hnew, ?_⟩
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

theorem branch_null {env : Translate.Env} {test : Expr} {name : String} {isNullTest : Bool} {value : Ty}
    {wt wf : IR.Body} (hn : nullTestOf env test = some (name, isNullTest, value)) :
    BranchSim (N := N) m fs fuel env test
      (if isNullTest then .matchNull name wt wf else .matchNull name wf wt) wt wf := by
  intro ρs ρo o ha hs ho
  obtain ⟨w, hw, hl⟩ := nullTestOf_eval m fuel hn hs
  have hwo : ρo.lookup name = some w := by rw [← ha]; exact hw
  refine ⟨_, hl, ?_⟩
  cases isNullTest <;> simp only [Bool.false_eq_true, ↓reduceIte, IR.Body.exec, hwo,
    Option.bind_eq_bind, Option.bind_some] at ho <;> cases w <;> simpa [isNullVal, Val.truthy] using ho

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
    {bodyS : Stmt} {bodyOut : IR.Body}
    (hbody : StmtSim (N := N) m fs fuel bodyEnv (.state names) (blockStatements bodyS) bodyOut)
    (henv : bodyEnv = env.add { name := x, binding := .const, type := elemType })
    (hfresh : env.has x = false)
    (hnames : names = changedNames (blockStatements bodyS) env) :
    ∀ (vs : List (Val N)) (ρs ρo ρo' : Eval.Env N), Agree ρs ρo → Scoped m env ρs →
      IR.Body.runFold fs fuel names x bodyOut ρo vs = some ρo' →
      ∃ mod, Eval.execLoop m fuel ρs x bodyS vs = some (.normal mod) ∧ Agree mod ρo' ∧
        Frame (stmtChanges bodyS) mod ρs := by
  subst henv
  intro vs
  induction vs with
  | nil =>
    intro ρs ρo ρo' ha hs h
    simp only [IR.Body.runFold, Option.some.injEq] at h
    subst h
    exact ⟨ρs, by simp [Eval.execLoop], ha, Frame.refl _ _⟩
  | cons v vs ih =>
    intro ρs ρo ρo' ha hs h
    simp only [IR.Body.runFold] at h
    cases hb : IR.Body.exec fs fuel ((x, v) :: ρo) bodyOut with
    | none => simp [hb] at h
    | some ob =>
      cases ob with
      | ret _ => simp [hb] at h
      | normal inner =>
        cases hbs : IR.bindState names inner ρo with
        | none => simp [hb, hbs] at h
        | some ρo₁ =>
          simp only [hb, hbs, Option.bind_eq_bind, Option.bind_some] at h
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
          obtain ⟨-, new, mod, hex, hag, hnew, hfr⟩ := (hbody _ _ ha' hs').2 inner hb
          obtain ⟨e, he, hdrop, hlen⟩ := block_normal m fuel bodyS hex hfr
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
              · have hnc : n ∉ stmtsChanges (blockStatements bodyS) := fun hc =>
                  hn (by rw [hnames, mem_changedNames]; exact ⟨hhas, hc⟩)
                exact hfr'.lookup hnc
              · have h1 := hs.none (by simpa using hhas)
                have h2 := hfr'.isSome n
                rw [h1] at h2 ⊢
                simpa using h2
          obtain ⟨mod₂, hloop, hag₂, hfr₂⟩ := ih mod' ρo₁ ρo' hag' (scoped_frame hs hfr') h
          refine ⟨mod₂, ?_, hag₂, ?_⟩
          · simp [Eval.execLoop, he, hnext, hloop]
          · rw [stmtsChanges_block] at hfr'
            exact (hfr₂.trans hfr').mono fun n hn => by simp at hn; exact hn

/-! ### `switch` -/

/-- A clause that returns, with no `break` before its `return`, returns from
the case block. -/
theorem execCase_ret {v : Val N} : ∀ {ss : List Stmt} {ρ : Eval.Env N},
    Eval.exec m fuel ρ ss = some (.ret v) → Eval.execCase m fuel ρ ss = some (.ret v, false)
  | [], ρ, h => by simp [Eval.exec] at h
  | s :: rest, ρ, h => by
    have hnb : ∀ sp, s ≠ .breakStmt sp := by
      rintro sp rfl; simp [Eval.exec, Eval.execStmt] at h
    simp only [Eval.exec] at h
    rw [Eval.execCase.eq_3 _ _ _ _ _ hnb]
    simp only [Bool.false_eq_true, ↓reduceIte]
    cases hs : Eval.execStmt m fuel ρ s with
    | none => simp [hs] at h
    | some o =>
      cases o with
      | ret r => simp [hs] at h ⊢; exact h
      | normal ρ' =>
        simp only [hs, Option.bind_eq_bind, Option.bind_some] at h ⊢
        exact execCase_ret h

theorem exec_clauseStatements {v : Val N} {ρ : Eval.Env N} {body : List Stmt}
    (h : Eval.exec m fuel ρ (clauseStatements body) = some (.ret v)) : Eval.exec m fuel ρ body = some (.ret v) := by
  unfold clauseStatements at h
  split at h
  · rename_i sp ss
    rw [exec_single, execStmt_block, h]; rfl
  · exact h

/-- A clause that returns, from the clause the test selected. -/
theorem execFrom_ret {v : Val N} {ρ : Eval.Env N} {t : Option Expr} {body : List Stmt}
    {more : List (Option Expr × List Stmt)} (h : Eval.exec m fuel ρ (clauseStatements body) = some (.ret v)) :
    Eval.execFrom m fuel ρ ((t, body) :: more) = some (.ret v) := by
  rw [Eval.execFrom, execCase_ret m fuel (exec_clauseStatements m fuel h)]
  rfl

/-- A `case` whose test is a string: the clause runs for that tag, and the
later clauses decide for every other. -/
theorem execSwitch_case {ρ : Eval.Env N} {test : Expr} {body : List Stmt}
    {more : List (Option Expr × List Stmt)} {tsp : Span} {k tag : String}
    (hst : test.stripParens = .string tsp tag) :
    Eval.execSwitch m fuel ρ (.str k) ((some test, body) :: more) =
      if k = tag then Eval.execFrom m fuel ρ ((some test, body) :: more)
      else Eval.execSwitch m fuel ρ (.str k) more := by
  have ht : Eval.eval m fuel ρ test = some (.str tag) := by
    rw [← eval_stripParens, hst]; simp [Eval.eval]
  rw [Eval.execSwitch]
  simp only [ht, Option.bind_eq_bind, Option.bind_some, Eval.strictEq]
  by_cases hk : k = tag <;> simp [hk]

/-- What `matchTag` runs: the arm of the tag, or the other arm, only for
the member that it names when it names one. -/
theorem matchTag_exec {n f tag : String} {r : DeclRef} {other : Option String} {wt wo : IR.Body}
    {ρ : Eval.Env N} {o : Outcome N} (h : IR.Body.exec fs fuel ρ (.matchTag n r (some f) tag other wt wo) = some o) :
    ∃ fields k, ρ.lookup n = some (.obj fields) ∧ fields.lookup f = some (.str k) ∧
      ((k = tag ∧ IR.Body.exec fs fuel ρ wt = some o) ∨
        (k ≠ tag ∧ (∀ x, other = some x → k = x) ∧ IR.Body.exec fs fuel ρ wo = some o)) := by
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
      by_cases hkt : k = tag
      · simp [hkt] at h; exact .inl ⟨hkt, h⟩
      · simp only [hkt, ↓reduceIte] at h
        split at h
        · rename_i hall
          refine .inr ⟨hkt, fun x hx => ?_, h⟩
          subst hx
          have : x = k := by simpa using hall
          exact this.symm
        · simp at h

/-- `switch (x.kind)` evaluates the tag of `x`. -/
theorem switchOf_eval {env : Translate.Env} {disc : Expr} {sw : SwitchOn} (h : switchOf env disc = some sw)
    {ρ : Eval.Env N} {fields : List (String × Val N)} {k : String}
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
          simp [Eval.eval, hl, hk]
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
    (∀ ρo', IR.Body.exec fs fuel ρo body ≠ some (.normal ρo')) ∧
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
  refine ⟨fun ρo' hv => absurd ((hrest ρs ρo ha hs).2 ρo' hv).1 (by simp [Tail.isRet]), fun v hv => ⟨?_, ?_⟩⟩
  · intro _ ⟨_, _, _, h⟩; cases h
  · intro _ _ _ _ _
    exact .inr ⟨by simp [Eval.execSwitch], (hrest ρs ρo ha hs).1 v hv⟩

/-- The `default` clause, last. -/
theorem clauses_default_sim {env : Translate.Env} {sw : SwitchOn} {known : Option String} {body : List Stmt}
    {rest : List Stmt} {b : IR.Body} (hb : StmtSim (N := N) m fs fuel env .ret (clauseStatements body) b) :
    ClauseSim (N := N) m fs fuel env sw known [(none, body)] rest b := by
  intro ρs ρo ha hs
  refine ⟨fun ρo' hv => absurd ((hb ρs ρo ha hs).2 ρo' hv).1 (by simp [Tail.isRet]), fun v hv => ⟨?_, ?_⟩⟩
  · intro _ ⟨_, _, _, h⟩; cases h
  · intro _ _ _ _ _
    left
    rw [Eval.execSwitch]
    exact execFrom_ret m fuel ((hb ρs ρo ha hs).1 v hv)

/-- The case of the one member left, which an outer `match` has tested. -/
theorem clauses_last_sim {env envT : Translate.Env} {sw : SwitchOn} {test : Expr} {body : List Stmt}
    {more : List (Option Expr × List Stmt)} {rest : List Stmt} {tsp : Span} {tag : String} {b : IR.Body}
    (hT : ∀ x, envT.has x = env.has x) (hTf : envT.functions = env.functions)
    (hst : test.stripParens = .string tsp tag)
    (hb : StmtSim (N := N) m fs fuel envT .ret (clauseStatements body) b) :
    ClauseSim (N := N) m fs fuel env sw (some tag) ((some test, body) :: more) rest b := by
  intro ρs ρo ha hs
  have hsT : Scoped m envT ρs := ⟨fun x => (hs.1 x).trans (hT x).symm, fun f hf => hs.2 f (hTf ▸ hf)⟩
  refine ⟨fun ρo' hv => absurd ((hb ρs ρo ha hsT).2 ρo' hv).1 (by simp [Tail.isRet]), fun v hv => ⟨?_, ?_⟩⟩
  · intro h; cases h
  · intro fields k _ _ hknown
    left
    rw [execSwitch_case m fuel hst, if_pos (hknown tag rfl)]
    exact execFrom_ret m fuel ((hb ρs ρo ha hsT).1 v hv)

/-- A case with members left after it: a `match` on its tag. -/
theorem clauses_case_sim {env envT envO : Translate.Env} {sw : SwitchOn} {known other : Option String}
    {test : Expr} {body : List Stmt} {more : List (Option Expr × List Stmt)} {rest : List Stmt} {tsp : Span}
    {tag : String} {wt wo : IR.Body}
    (hT : ∀ x, envT.has x = env.has x) (hTf : envT.functions = env.functions)
    (hO : ∀ x, envO.has x = env.has x) (hOf : envO.functions = env.functions)
    (hst : test.stripParens = .string tsp tag)
    (hwt : StmtSim (N := N) m fs fuel envT .ret (clauseStatements body) wt)
    (hwo : ClauseSim (N := N) m fs fuel envO sw other more rest wo) :
    ClauseSim (N := N) m fs fuel env sw known ((some test, body) :: more) rest
      (.matchTag sw.name sw.ref sw.field tag other wt wo) := by
  intro ρs ρo ha hs
  have hsT : Scoped m envT ρs := ⟨fun x => (hs.1 x).trans (hT x).symm, fun f hf => hs.2 f (hTf ▸ hf)⟩
  have hsO : Scoped m envO ρs := ⟨fun x => (hs.1 x).trans (hO x).symm, fun f hf => hs.2 f (hOf ▸ hf)⟩
  refine ⟨fun ρo' hv => ?_, fun v hv => ?_⟩
  · obtain ⟨_, _, _, _, ⟨_, h⟩ | ⟨_, _, h⟩⟩ := matchTag_exec fs fuel hv
    · exact absurd ((hwt ρs ρo ha hsT).2 ρo' h).1 (by simp [Tail.isRet])
    · exact (hwo ρs ρo ha hsO).1 ρo' h
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
  refine ⟨fun v hv => ?_, fun ρo' hv => absurd hv ((hc ρs ρo ha hs).1 ρo')⟩
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
    cases hs : Eval.execStmt m fuel ρ s with
    | none => simp [hs] at h
    | some o =>
      cases o with
      | ret r => simp [hs] at h
      | normal ρ' =>
        simp only [hs, Option.bind_eq_bind, Option.bind_some] at h ⊢
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
theorem stmtsChanges_dropBreak : ∀ (body : List Stmt), stmtsChanges (dropBreak body) = stmtsChanges body
  | [] => rfl
  | [s] => by
    by_cases hb : s.isBreak = true
    · obtain ⟨sp, rfl⟩ : ∃ sp, s = .breakStmt sp := by
        cases s <;> simp [Stmt.isBreak] at hb; exact ⟨_, rfl⟩
      rfl
    · simp [dropBreak, hb]
  | s :: t :: rest => by
    simp only [dropBreak, stmtsChanges, stmtsChanges_dropBreak (t :: rest)]

omit [JSNumber N] in
theorem stmtsChanges_flatMap : ∀ (cs : List (Option Expr × List Stmt)),
    ∀ n ∈ stmtsChanges (cs.flatMap (·.2)), n ∈ clausesChanges cs
  | [], n, h => by simp [stmtsChanges] at h
  | (t, b) :: cs, n, h => by
    simp only [List.flatMap_cons, stmtsChanges_append, List.mem_append] at h
    simp only [clausesChanges, List.mem_append]
    rcases h with h | h
    · exact .inl (.inr h)
    · exact .inr (stmtsChanges_flatMap cs n h)

/-- A statement that ends in the state of the locals `names`, as an `if`
without a return or a `switch` whose clauses end in `break` does, and then
`rest`: `let (x, y) := br`, then `rb`. -/
theorem letState_sim {env : Translate.Env} {st : Stmt} {rest : List Stmt} {tail : Tail} {br rb : IR.Body}
    {names : List String} {ss : List Stmt}
    (hnames : names = changedNames ss env)
    (hsub : ∀ n, n ∈ stmtsChanges ss → n ∈ stmtChanges st)
    (hbr : ∀ (ρs ρo inner : Eval.Env N), Agree ρs ρo → Scoped m env ρs →
      IR.Body.exec fs fuel ρo br = some (.normal inner) →
      ∃ new mod, Eval.execStmt m fuel ρs st = some (.normal mod) ∧ Agree (new ++ mod) inner ∧
        (∀ p ∈ new, env.has p.1 = false) ∧ Frame (stmtsChanges ss) mod ρs)
    (hrest : StmtSim (N := N) m fs fuel env tail rest rb) :
    StmtSim (N := N) m fs fuel env tail (st :: rest) (.letState names br rb) := by
  intro ρs ρo ha hs
  have key : ∀ o, IR.Body.exec fs fuel ρo (.letState names br rb) = some o →
      ∃ mod ρo₂, Eval.execStmt m fuel ρs st = some (.normal mod) ∧
        Agree mod ρo₂ ∧ Frame (stmtChanges st) mod ρs ∧ IR.Body.exec fs fuel ρo₂ rb = some o := by
    intro o ho
    simp only [IR.Body.exec] at ho
    cases hb : IR.Body.exec fs fuel ρo br with
    | none => simp [hb] at ho
    | some ob =>
      cases ob with
      | ret v => simp [hb] at ho
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
            · have hnc : n ∉ stmtsChanges ss := fun hc =>
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
    simp [Eval.exec, hst, this]
  · intro ρo' hv
    obtain ⟨mod, ρo₂, hst, hag, hfr, hb⟩ := key _ hv
    obtain ⟨htail, new, mod₂, hex, hag₂, hnew, hfr₂⟩ := (hrest mod ρo₂ hag (scoped_frame hs hfr)).2 ρo' hb
    refine ⟨htail, new, mod₂, by simp [Eval.exec, hst, hex], hag₂, hnew, ?_⟩
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
        ∃ new mod, Eval.execSwitch m fuel ρs (.str k) cs = some (.normal (new ++ mod)) ∧
          Agree (new ++ mod) inner ∧ (∀ p ∈ new, env.has p.1 = false) ∧
          Frame (stmtsChanges (cs.flatMap (·.2))) mod ρs

/-- No clause is left: the locals keep their values. -/
theorem state_nil_sim {env : Translate.Env} {sw : SwitchOn} {known : Option String} {names : List String} :
    StateClauseSim (N := N) m fs fuel env sw known [] (.state names) := by
  intro ρs ρo inner ha hs hv
  simp only [IR.Body.exec, Option.some.injEq, Outcome.normal.injEq] at hv
  subst hv
  refine ⟨fun _ h => (by obtain ⟨_, _, _, h⟩ := h; cases h), fun _ _ _ _ _ =>
    ⟨[], ρs, by simp [Eval.execSwitch], by simpa using ha, by simp, Frame.refl _ _⟩⟩

/-- The `default` clause, last. -/
theorem state_default_sim {env : Translate.Env} {sw : SwitchOn} {known : Option String} {body : List Stmt}
    {b : IR.Body} {names : List String}
    (hb : StmtSim (N := N) m fs fuel env (.state names) (dropBreak body) b) :
    StateClauseSim (N := N) m fs fuel env sw known [(none, body)] b := by
  intro ρs ρo inner ha hs hv
  obtain ⟨-, new, mod, hex, hag, hnew, hfr⟩ := (hb ρs ρo ha hs).2 inner hv
  refine ⟨fun _ h => (by obtain ⟨_, _, _, h⟩ := h; cases h), fun _ _ _ _ _ => ⟨new, mod, ?_, hag, hnew, ?_⟩⟩
  · rw [Eval.execSwitch]; exact execFrom_normal m fuel hex (.inl rfl)
  · exact hfr.mono fun n hn => by simpa [stmtsChanges] using (stmtsChanges_dropBreak body ▸ hn)

/-- The case of the one member left, which an outer `match` has tested. -/
theorem state_last_sim {env envT : Translate.Env} {sw : SwitchOn} {test : Expr} {body : List Stmt}
    {more : List (Option Expr × List Stmt)} {tsp : Span} {tag : String} {b : IR.Body} {names : List String}
    (hT : ∀ x, envT.has x = env.has x) (hTf : envT.functions = env.functions)
    (hst : test.stripParens = .string tsp tag) (hlast : more = [] ∨ endsInBreak body = true)
    (hb : StmtSim (N := N) m fs fuel envT (.state names) (dropBreak body) b) :
    StateClauseSim (N := N) m fs fuel env sw (some tag) ((some test, body) :: more) b := by
  intro ρs ρo inner ha hs hv
  have hsT : Scoped m envT ρs := ⟨fun x => (hs.1 x).trans (hT x).symm, fun f hf => hs.2 f (hTf ▸ hf)⟩
  obtain ⟨-, new, mod, hex, hag, hnew, hfr⟩ := (hb ρs ρo ha hsT).2 inner hv
  refine ⟨fun h => (by cases h), fun fields k _ _ hknown =>
    ⟨new, mod, ?_, hag, fun p hp => by rw [← hT]; exact hnew p hp, hfr.mono fun n hn => ?_⟩⟩
  · rw [execSwitch_case m fuel hst, if_pos (hknown tag rfl)]
    exact execFrom_normal m fuel hex hlast
  · simp only [List.flatMap_cons, stmtsChanges_append, List.mem_append]
    exact .inl ((stmtsChanges_dropBreak body ▸ hn))

/-- A case with members left after it: a `match` on its tag. -/
theorem state_case_sim {env envT envO : Translate.Env} {sw : SwitchOn} {known other : Option String}
    {test : Expr} {body : List Stmt} {more : List (Option Expr × List Stmt)} {tsp : Span} {tag : String}
    {wt wo : IR.Body} {names : List String}
    (hT : ∀ x, envT.has x = env.has x) (hTf : envT.functions = env.functions)
    (hO : ∀ x, envO.has x = env.has x) (hOf : envO.functions = env.functions)
    (hst : test.stripParens = .string tsp tag) (hlast : more = [] ∨ endsInBreak body = true)
    (hwt : StmtSim (N := N) m fs fuel envT (.state names) (dropBreak body) wt)
    (hwo : StateClauseSim (N := N) m fs fuel envO sw other more wo) :
    StateClauseSim (N := N) m fs fuel env sw known ((some test, body) :: more)
      (.matchTag sw.name sw.ref sw.field tag other wt wo) := by
  intro ρs ρo inner ha hs hv
  have hsT : Scoped m envT ρs := ⟨fun x => (hs.1 x).trans (hT x).symm, fun f hf => hs.2 f (hTf ▸ hf)⟩
  have hsO : Scoped m envO ρs := ⟨fun x => (hs.1 x).trans (hO x).symm, fun f hf => hs.2 f (hOf ▸ hf)⟩
  obtain ⟨fields, k, hl, hk, hbr⟩ := matchTag_exec fs fuel hv
  have hl' : ρs.lookup sw.name = some (.obj fields) := by rw [ha]; exact hl
  refine ⟨fun _ _ => ⟨fields, k, hl', hk⟩, fun fields' k' hl2 hk2 _ => ?_⟩
  rw [hl'] at hl2
  cases hl2
  rw [hk] at hk2
  cases hk2
  rcases hbr with ⟨rfl, h⟩ | ⟨hne, hother, h⟩
  · obtain ⟨-, new, mod, hex, hag, hnew, hfr⟩ := (hwt ρs ρo ha hsT).2 inner h
    refine ⟨new, mod, ?_, hag, fun p hp => by rw [← hT]; exact hnew p hp, hfr.mono fun n hn => ?_⟩
    · rw [execSwitch_case m fuel hst, if_pos rfl]; exact execFrom_normal m fuel hex hlast
    · simp only [List.flatMap_cons, stmtsChanges_append, List.mem_append]
      exact .inl ((stmtsChanges_dropBreak body ▸ hn))
  · obtain ⟨-, hmain⟩ := hwo ρs ρo inner ha hsO h
    obtain ⟨new, mod, hex, hag, hnew, hfr⟩ := hmain fields k hl' hk hother
    refine ⟨new, mod, ?_, hag, fun p hp => by rw [← hO]; exact hnew p hp, hfr.mono fun n hn => ?_⟩
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
  refine letState_sim m fs fuel hnames (fun n hn => ?_) (fun ρs ρo inner ha hs hv => ?_) hrest
  · simp only [stmtChanges, List.mem_append]; exact .inr (stmtsChanges_flatMap _ n hn)
  · obtain ⟨hfirst, hmain⟩ := hc ρs ρo inner ha hs hv
    obtain ⟨fields, k, hl, hk⟩ := hfirst rfl ⟨test, body, more, rfl⟩
    obtain ⟨new, mod, hex, hag, hnew, hfr⟩ := hmain fields k hl hk (fun _ h => by cases h)
    refine ⟨new, mod, ?_, hag, hnew, hfr⟩
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
    | nil => exact state_default_sim m fs fuel (ihA _ _ _ _ _ _ _ _ h).2
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
  cases hn : nullTestOf env test with
  | none =>
    cases ht : tagTestOf env test with
    | some tt =>
      -- `if (x.kind === 'a')`: a match on the member.
      have hb := fun wt wf => branch_tag (N := N) (wt := wt) (wf := wf) m fs fuel ht
      cases hie : tt.isEq <;> simp only [hn, ht, hie, ite_state, Bool.false_eq_true, ↓reduceIte] at h hb
      all_goals
        split at h
        · rename_i hret
          simp only [Bool.and_eq_true] at hret
          split at h
          · simp only [bind_ok, reject_ne_ok, false_and, exists_false, reject_ne_ok] at h
          · rename_i hrest
            simp only [pure_bind, bind_ok] at h
            obtain ⟨wt, s₁, hwt, wf, s₂, hwf, h⟩ := h
            split at h
            · simp only [bind_ok, reject_ne_ok, false_and, exists_false, reject_ne_ok] at h
            · simp only [pure_ok] at h
              obtain ⟨_, _, ⟨rfl, rfl⟩, rfl, -⟩ := h
              exact if_ret_sim m fs fuel (narrow_has _ _ _) (narrow_has _ _ _) rfl rfl hret.1
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
      simp only [hn, ht, ite_state] at h
      split at h
      · rename_i hret
        simp only [Bool.and_eq_true] at hret
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
            exact if_ret_sim m fs fuel (fun _ => rfl) (fun _ => rfl) rfl rfl hret.1
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
    obtain ⟨name, isNullTest, value⟩ := nt
    have hb := fun wt wf => branch_null (N := N) (wt := wt) (wf := wf) m fs fuel hn
    cases isNullTest <;> simp only [hn, ite_state, Bool.false_eq_true, ↓reduceIte] at h hb
    all_goals
      split at h
      · rename_i hret
        simp only [Bool.and_eq_true] at hret
        split at h
        · simp at h
        · rename_i hrest
          simp only [pure_bind, bind_ok, pure_ok] at h
          obtain ⟨wt, s₁, hwt, wf, s₂, hwf, rfl, -⟩ := h
          exact if_ret_sim m fs fuel (narrow_has _ _ _) (narrow_has _ _ _) rfl rfl hret.1
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

/-- `translateForOf` is sound, when `translateStatements` is with one unit of fuel less. -/
theorem translateForOf_sound (hc : CallsAgree (N := N) m.program fs fuel) {F : Nat}
    (ihS : ∀ env tail ss ctx body ctx', translateStatements F env tail ss ctx = .ok body ctx' →
      StmtSim (N := N) m fs fuel env tail ss body) :
    ∀ env s kind x iterable b rest tail ctx body ctx',
      translateForOf (F + 1) env s kind x iterable b rest tail ctx = .ok body ctx' →
      StmtSim (N := N) m fs fuel env tail (.forOfStmt s kind x iterable b :: rest) body := by
  intro env s kind x iterable b rest tail ctx body ctx' h
  unfold translateForOf at h
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
      · simp only [bind_ok, fuelLimit_ok] at h
        obtain ⟨_, _, ⟨rfl, rfl⟩, items, s₁, hitems, h⟩ := h
        cases hty : items.type <;> simp [hty] at h
        rename_i elemType
        obtain ⟨bodyEnv, s₂, hdecl, bodyOut, s₃, hbody, rb, hrb, hbodyEq⟩ := h
        obtain ⟨hfresh, rfl, -⟩ := declare_ok hdecl
        have hsimI := (expr_sound m fs fuel hc _).1 _ _ _ _ _ _ hitems
        have hloop := loop_sim m fs fuel (ihS _ _ _ _ _ _ hbody) rfl hfresh rfl
        have hrest := ihS _ _ _ _ _ _ hrb
        intro ρs ρo ha hs
        have key : ∀ o, IR.Body.exec fs fuel ρo body = some o →
            ∃ mod ρo₂, Eval.execStmt m fuel ρs (.forOfStmt s .const x iterable b) = some (.normal mod) ∧
              Agree mod ρo₂ ∧ Frame (stmtChanges (.forOfStmt s .const x iterable b)) mod ρs ∧
              IR.Body.exec fs fuel ρo₂ rb = some o := by
          intro o ho
          rw [← hbodyEq] at ho
          simp only [IR.Body.exec] at ho
          cases hi : IR.Expr.eval fs fuel ρo items.code with
          | none => simp [hi] at ho
          | some u =>
            cases u <;> simp [hi] at ho
            rename_i vs
            cases hf : IR.Body.runFold fs fuel (changedNames (blockStatements b) env) x bodyOut ρo vs with
            | none => simp [hf] at ho
            | some ρo₂ =>
              simp [hf] at ho
              obtain ⟨mod, hl, hag, hfr⟩ := hloop vs ρs ρo ρo₂ ha hs hf
              refine ⟨mod, ρo₂, ?_, hag, hfr.mono fun n hn => by simp [stmtChanges, hn], ho⟩
              simp [Eval.execStmt, hsimI ρs ρo _ ha hs hi, hl]
        constructor
        · intro v hv
          obtain ⟨mod, ρo₂, hst, hag, hfr, hb⟩ := key _ hv
          have := (hrest mod ρo₂ hag (scoped_frame hs hfr)).1 v hb
          simp [Eval.exec, hst, this]
        · intro ρo' hv
          obtain ⟨mod, ρo₂, hst, hag, hfr, hb⟩ := key _ hv
          obtain ⟨htail, new, mod₂, hex, hag₂, hnew, hfr₂⟩ :=
            (hrest mod ρo₂ hag (scoped_frame hs hfr)).2 ρo' hb
          refine ⟨htail, new, mod₂, by simp [Eval.exec, hst, hex], hag₂, hnew, ?_⟩
          simpa [stmtsChanges] using hfr₂.trans hfr
  · simp at h

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


theorem stmts_sound (hc : CallsAgree (N := N) m.program fs fuel) (F : Nat) :
    (∀ env tail ss ctx body ctx', translateStatements F env tail ss ctx = .ok body ctx' →
      StmtSim (N := N) m fs fuel env tail ss body) ∧
    (∀ env s d rest tail ctx body ctx', translateVariable F env s d rest tail ctx = .ok body ctx' →
      StmtSim (N := N) m fs fuel env tail (.varDecl s d :: rest) body) ∧
    (∀ env s test t e rest tail ctx body ctx', translateIf F env s test t e rest tail ctx = .ok body ctx' →
      StmtSim (N := N) m fs fuel env tail (.ifStmt s test t e :: rest) body) ∧
    (∀ env s kind x iterable b rest tail ctx body ctx',
      translateForOf F env s kind x iterable b rest tail ctx = .ok body ctx' →
      StmtSim (N := N) m fs fuel env tail (.forOfStmt s kind x iterable b :: rest) body) ∧
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
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro _ _ _ _ _ _ h; simp [translateStatements] at h
    · intro _ _ _ _ _ _ _ _ h; simp [translateVariable] at h
    · intro _ _ _ _ _ _ _ _ _ _ h; simp [translateIf] at h
    · intro _ _ _ _ _ _ _ _ _ _ _ h; simp [translateForOf] at h
    · intro _ _ _ _ _ _ _ _ _ h; simp [translateSwitch] at h
    · intro _ _ _ _ _ _ _ _ _ _ h; simp [translateClauses] at h
    · intro _ _ _ _ _ _ _ _ _ _ h; simp [translateStateClauses] at h
    · intro _ _ _ _ _ _ _ _ h; simp [translateStateClause] at h
  | succ F ih =>
    obtain ⟨ihS, ihV, ihI, ihF, ihW, ihC, ihSC, ihA⟩ := ih
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro env tail ss ctx body ctx' h
      unfold translateStatements at h
      cases ss with
      | nil =>
        cases tail with
        | ret => simp at h
        | state names =>
          simp only [pure_ok] at h
          obtain ⟨rfl, -⟩ := h
          intro ρs ρo ha hs
          refine ⟨fun v hv => by simp [IR.Body.exec] at hv, fun ρo' hv => ?_⟩
          simp only [IR.Body.exec, Option.some.injEq, Outcome.normal.injEq] at hv
          subst hv
          exact ⟨rfl, [], ρs, by simp [Eval.exec], ha, by simp, Frame.refl _ _⟩
      | cons stmt rest =>
        cases stmt with
        | varDecl sp d => exact ihV _ _ _ _ _ _ _ _ h
        | ifStmt sp test t e => exact ihI _ _ _ _ _ _ _ _ _ _ h
        | forOfStmt sp kind x iterable b => exact ihF _ _ _ _ _ _ _ _ _ _ _ h
        | returnStmt sp value =>
          simp only at h
          cases tail <;> cases rest <;> cases value <;> simp only at h <;> try (simp at h; done)
          simp only [bind_ok, modify_ok, get_ok, fuelLimit_ok, ite_state] at h
          rename_i v
          obtain ⟨_, s₁, rfl, _, _, ⟨rfl, rfl⟩, _, _, ⟨rfl, rfl⟩, code, s₂, hcode, h⟩ := h
          split at h
          · simp only [pure_bind, bind_ok, modify_ok, pure_ok] at h
            obtain ⟨_, _, rfl, rfl, -⟩ := h
            have hsim := (expr_sound m fs fuel hc _).1 _ _ _ _ _ _ hcode
            intro ρs ρo ha hs
            constructor
            · intro w hw
              simp only [IR.Body.exec, eval_value] at hw
              cases hv : IR.Expr.eval fs fuel ρo code.code with
              | none => simp [hv] at hw
              | some u =>
                simp [hv] at hw
                subst hw
                simp [Eval.exec, Eval.execStmt, hsim ρs ρo u ha hs hv]
            · intro ρo' hv
              simp only [IR.Body.exec] at hv
              cases hv' : IR.Expr.eval fs fuel ρo code.value <;> simp [hv'] at hv
          · simp at h
        | exprStmt sp e =>
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
          · intro ρo' hv
            obtain ⟨w, hw, hb⟩ := key _ hv
            obtain ⟨hhas, hch, hex⟩ := update_sound m fs fuel hc hu ha hs hw
            obtain ⟨htail, new, mod, hexr, ha', hnew, hfr⟩ :=
              (hrest _ _ (agree_set ha (hs.some hhas)) (hs' w)).2 ρo' hb
            refine ⟨htail, new, mod, by simp [Eval.exec, hex, hexr], ha', hnew, ?_⟩
            refine (hfr.trans (Frame.set (c := [name]) (by simp) ρs)).mono ?_
            intro n hn
            simp only [List.mem_append, List.mem_singleton] at hn
            simp only [stmtsChanges, stmtChanges, List.mem_append]
            rcases hn with rfl | hn
            · exact .inl hch
            · exact .inr hn
        | switchStmt sp disc cs => exact ihW _ _ _ _ _ _ _ _ _ h
        | _ => simp at h
    · intro env s d rest tail ctx body ctx' h
      obtain ⟨kind, name, type, init?⟩ := d
      unfold translateVariable at h
      simp only [bind_ok, orReject_ok] at h
      obtain ⟨init, s₁, ⟨rfl, rfl⟩, h⟩ := h
      simp only [ite_state] at h
      cases type with
      | none =>
        simp only [Bool.false_eq_true, ite_false, ite_self] at h
        simp only [pure_bind, bind_ok, fuelLimit_ok] at h
        obtain ⟨_, _, ⟨rfl, rfl⟩, code, s₂, hcode, env', s₃, hdecl, rb, s₄, hrb, h⟩ := h
        simp only [pure_ok] at h
        obtain ⟨rfl, -⟩ := h
        obtain ⟨hfresh, rfl, -⟩ := declare_ok hdecl
        have hsim := (expr_sound m fs fuel hc _).1 _ _ _ _ _ _ hcode
        exact decl_sim m fs fuel (d := ⟨kind, name, none, some init⟩) rfl hfresh rfl
          (fun ρo o ho => by
            simp only [IR.Body.exec] at ho
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
          | (simp only [bind_ok, map_ok, fuelLimit_ok, pure_bind] at h
             obtain ⟨ty, s₂, hty, _, _, ⟨rfl, rfl⟩, code, s₃, hcode, h⟩ := h
             simp only [ite_state] at h
             split at h
             · simp only [bind_ok, map_ok] at h
               obtain ⟨env', s₄, hdecl, rb, hrb, rfl⟩ := h
               obtain ⟨hfresh, rfl, -⟩ := declare_ok hdecl
               have hsim := (expr_sound m fs fuel hc _).1 _ _ _ _ _ _ hcode
               exact decl_sim m fs fuel (d := ⟨kind, name, some annotation, some init⟩) rfl hfresh rfl
                 (fun ρo o ho => by
                   simp only [IR.Body.exec] at ho
                   cases hw : IR.Expr.eval fs fuel ρo code.value with
                   | none => simp [hw] at ho
                   | some w =>
                     exact ⟨w, fun ρs ha hs => hsim ρs ρo w ha hs (by rwa [eval_value] at hw),
                       by simpa [hw] using ho⟩)
                 (ihS _ _ _ _ _ _ hrb)
             · simp at h)
          | (simp only [pure_bind, bind_ok, map_ok, fuelLimit_ok] at h
             obtain ⟨_, s₂, ⟨ty, hty, rfl⟩, _, _, ⟨rfl, rfl⟩, code, s₃, hcode, h⟩ := h
             simp only [ite_state] at h
             split at h
             · simp only [bind_ok, pure_ok] at h
               obtain ⟨env', s₄, hdecl, rb, s₅, hrb, rfl, -⟩ := h
               obtain ⟨hfresh, rfl, -⟩ := declare_ok hdecl
               have hsim := (expr_sound m fs fuel hc _).1 _ _ _ _ _ _ hcode
               exact decl_sim m fs fuel (d := ⟨kind, name, some annotation, some init⟩) rfl hfresh rfl
                 (fun ρo o ho => by
                   simp only [IR.Body.exec] at ho
                   cases hw : IR.Expr.eval fs fuel ρo code.value with
                   | none => simp [hw] at ho
                   | some w =>
                     exact ⟨w, fun ρs ha hs => hsim ρs ρo w ha hs (by rwa [eval_value] at hw),
                       by simpa [hw] using ho⟩)
                 (ihS _ _ _ _ _ _ hrb)
             · simp at h)
          | (exfalso; cases init <;> simp_all [Expr.isArrayLiteral])
          | (simp only [pure_bind, bind_ok, fuelLimit_ok, pure_ok] at h
             obtain ⟨ty, s₂, hty, _, _, ⟨rfl, rfl⟩, r, s₃, hel, env', s₄, hdecl, rb, s₅, hrb,
               rfl, -⟩ := h
             obtain ⟨hfresh, rfl, -⟩ := declare_ok hdecl
             have hsim := (expr_sound m fs fuel hc _).2.1 _ _ _ _ _ _ _ hel
             exact decl_sim m fs fuel (d := ⟨kind, name, some annotation, some _⟩) rfl hfresh rfl
               (fun ρo o ho => by
                 simp only [IR.Body.exec] at ho
                 cases hw : IR.Expr.evalList fs fuel ρo r.1 with
                 | none => simp [hw] at ho
                 | some ws =>
                   exact ⟨.list ws, fun ρs ha hs => by
                     rw [Eval.eval]; simp [hsim ρs ρo ws ha hs hw], by simpa [hw] using ho⟩)
               (ihS _ _ _ _ _ _ hrb))
    · exact translateIf_sound m fs fuel hc ihS
    · exact translateForOf_sound m fs fuel hc ihS
    · exact translateSwitch_sound m fs fuel ihS ihC ihSC
    · exact translateClauses_sound m fs fuel ihS ihC
    · exact translateStateClauses_sound m fs fuel ihSC ihA
    · exact translateStateClause_sound m fs fuel ihS

end tolean.TypeScript.Proof
