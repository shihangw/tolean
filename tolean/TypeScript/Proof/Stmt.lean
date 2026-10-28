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
    ∀ {names : List String} {outer ρ : Eval.Env N}, Output.bindState names inner outer = some ρ →
      ∀ n, ρ.lookup n = if n ∈ names then inner.lookup n else outer.lookup n
  | [], outer, ρ, h, n => by
    simp [Output.bindState] at h; subst h; simp
  | k :: ks, outer, ρ, h, n => by
    simp only [Output.bindState, List.foldlM_cons] at h
    cases hk : inner.lookup k with
    | none => simp [hk] at h
    | some w =>
      simp only [hk] at h
      have := bindState_lookup (names := ks) (outer := (k, w) :: outer) (by simpa [Output.bindState] using h) n
      rw [this]
      by_cases hn : n = k
      · subst hn; by_cases hm : n ∈ ks <;> simp [hm, hk, List.lookup]
      · have : (n == k) = false := by simpa using hn
        by_cases hm : n ∈ ks <;> simp [hm, hn, this, List.lookup]

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
  · simp only [pure_bind] at h
    exact checkName_ok h

theorem declare_ok {env env' : Translate.Env} {sp : Span} {name : String} {b : Binding} {t : Ty}
    {s s' : Ctx} (h : declare env sp name b t s = .ok env' s') :
    env.has name = false ∧ env' = env.add { name, binding := b, type := t } ∧ s' = s := by
  simp only [declare, ite_state] at h
  split at h
  · simp at h
  · rename_i hn
    simp only [pure_bind, bind_ok] at h
    obtain ⟨r, s₁, hr, h⟩ := h
    obtain ⟨-, rfl⟩ := checkLocalName_ok hr
    simp only [pure_ok] at h
    exact ⟨by simpa using hn, h.1.symm, h.2.symm⟩

end Monad

/-! ### The statement -/

variable [JSNumber N]
variable (m : Eval.Scope) (fs : List (DeclRef × List String × Output.Body)) (fuel : Nat)

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

theorem out_push {ρ : Eval.Env N} {name : String} {a : Output.Expr} {w : Val N}
    (h : Output.Expr.eval fs fuel ρ (.push name a) = some w) :
    ∃ xs va, ρ.lookup name = some (.list xs) ∧ Output.Expr.eval fs fuel ρ a = some va ∧
      w = .list (xs ++ [va]) := by
  simp only [Output.Expr.eval] at h
  cases hx : ρ.lookup name with
  | none => simp [hx] at h
  | some u =>
    cases u <;> simp [hx] at h
    rename_i xs
    cases hy : Output.Expr.eval fs fuel ρ a with
    | none => simp [hy] at h
    | some va => simp [hy] at h; exact ⟨xs, va, rfl, rfl, h.symm⟩

theorem out_update {ρ : Eval.Env N} {op : Output.IntOp} {name : String} {a : Output.Expr} {w : Val N}
    (h : Output.Expr.eval fs fuel ρ (.update op name a) = some w) :
    ∃ x y, ρ.lookup name = some (.int x) ∧ Output.Expr.eval fs fuel ρ a = some (.int y) ∧
      w = .int (op.apply x y) := by
  simp only [Output.Expr.eval] at h
  cases hx : ρ.lookup name with
  | none => simp [hx] at h
  | some u =>
    cases u <;> simp [hx] at h
    rename_i x
    cases hy : Output.Expr.eval fs fuel ρ a with
    | none => simp [hy] at h
    | some u => cases u <;> simp_all

/-- An update statement sets a name in scope to the value of the output's
update. -/
theorem update_sound (hc : CallsAgree (N := N) m.program fs fuel) {env : Translate.Env} {sp : Span} {e : Expr}
    {ctx ctx' : Ctx} {name : String} {upd : Output.Expr}
    (h : translateUpdate env sp e ctx = .ok (name, upd) ctx')
    {ρs ρo : Eval.Env N} (ha : Agree ρs ρo) (hs : Scoped m env ρs) {w : Val N}
    (hw : Output.Expr.eval fs fuel ρo upd = some w) :
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
             simp only [Output.Expr.eval] at hp
             rw [eval_value] at hq
             rw [← ha x] at hp
             simp [Eval.execStmt, hp, hsim ρs ρo _ ha hs hq, Eval.binary, Output.NumberOp.apply])
          | (obtain ⟨p, q, hp, hq, rfl⟩ := out_update fs fuel hw
             rw [eval_value] at hq
             rw [← ha x] at hp
             simp [Eval.execStmt, hp, hsim ρs ρo _ ha hs hq, Eval.binary, Output.IntOp.apply])
    · simp at h

/-- The output body `body` means what the statements `ss` mean. A return gives
the same value. An end, which only a body for a branch or a loop has, gives
environments that agree: the interpreter's has new bindings, which `env`
does not have, in front of the old names, and it changes only the names that
`ss` change. -/
def StmtSim (env : Translate.Env) (tail : Tail) (ss : List Stmt) (body : Output.Body) : Prop :=
  ∀ (ρs ρo : Eval.Env N), Agree ρs ρo → Scoped m env ρs →
    (∀ v, Output.Body.exec fs fuel ρo body = some (.ret v) → Eval.exec m fuel ρs ss = some (.ret v)) ∧
    (∀ ρo', Output.Body.exec fs fuel ρo body = some (.normal ρo') →
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
    {tail : Tail} {body rb : Output.Body} {b : Binding} {ty : Ty}
    (hinit : d.init = some init) (hfresh : env.has d.name = false)
    (henv : env' = env.add { name := d.name, binding := b, type := ty })
    (hbody : ∀ (ρo : Eval.Env N) (o : Outcome N), Output.Body.exec fs fuel ρo body = some o → ∃ w,
      (∀ ρs, Agree ρs ρo → Scoped m env ρs → Eval.eval m fuel ρs init = some w) ∧
        Output.Body.exec fs fuel ((d.name, w) :: ρo) rb = some o)
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
def BranchSim (env : Translate.Env) (test : Expr) (br whenTrue whenFalse : Output.Body) : Prop :=
  ∀ (ρs ρo : Eval.Env N) (o : Outcome N), Agree ρs ρo → Scoped m env ρs →
    Output.Body.exec fs fuel ρo br = some o →
    ∃ w, Eval.eval m fuel ρs test = some w ∧
      Output.Body.exec fs fuel ρo (if w.truthy then whenTrue else whenFalse) = some o

/-- An `if` whose branches both return. -/
theorem if_ret_sim {env envT envF : Translate.Env} {sp : Span} {test : Expr} {t : Stmt}
    {e : Option Stmt} {rest : List Stmt} {tail : Tail} {br wt wf : Output.Body}
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
    {e : Option Stmt} {rest : List Stmt} {tail : Tail} {br wt wf rb : Output.Body} {names : List String}
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
  have key : ∀ o, Output.Body.exec fs fuel ρo (.letState names br rb) = some o →
      ∃ mod ρo₂, Eval.execStmt m fuel ρs (.ifStmt sp test t e) = some (.normal mod) ∧
        Agree mod ρo₂ ∧ Frame (stmtChanges (.ifStmt sp test t e)) mod ρs ∧
        Output.Body.exec fs fuel ρo₂ rb = some o := by
    intro o ho
    simp only [Output.Body.exec] at ho
    cases hb : Output.Body.exec fs fuel ρo br with
    | none => simp [hb] at ho
    | some ob =>
      cases ob with
      | ret v => simp [hb] at ho
      | normal inner =>
        cases hbs : Output.bindState names inner ρo with
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

theorem branch_ite {env : Translate.Env} {test : Expr} {c : Output.Expr} {wt wf : Output.Body}
    (hsim : Sim (N := N) m fs fuel env test c) : BranchSim (N := N) m fs fuel env test (.ite c wt wf) wt wf := by
  intro ρs ρo o ha hs ho
  simp only [Output.Body.exec] at ho
  cases hc : Output.Expr.eval fs fuel ρo c with
  | none => simp [hc] at ho
  | some u =>
    cases u <;> simp [hc] at ho
    rename_i b
    refine ⟨.bool b, hsim ρs ρo _ ha hs hc, ?_⟩
    cases b <;> simpa [Val.truthy] using ho

theorem branch_null {env : Translate.Env} {test : Expr} {name : String} {isNullTest : Bool} {value : Ty}
    {wt wf : Output.Body} (hn : nullTestOf env test = some (name, isNullTest, value)) :
    BranchSim (N := N) m fs fuel env test
      (if isNullTest then .matchNull name wt wf else .matchNull name wf wt) wt wf := by
  intro ρs ρo o ha hs ho
  obtain ⟨w, hw, hl⟩ := nullTestOf_eval m fuel hn hs
  have hwo : ρo.lookup name = some w := by rw [← ha]; exact hw
  refine ⟨_, hl, ?_⟩
  cases isNullTest <;> simp only [Bool.false_eq_true, ↓reduceIte, Output.Body.exec, hwo,
    Option.bind_eq_bind, Option.bind_some] at ho <;> cases w <;> simpa [isNullVal, Val.truthy] using ho

/-- The loop `for (const x of …)` over `vs` means what the output's fold means,
when the body does. -/
theorem loop_sim {env bodyEnv : Translate.Env} {x : String} {elemType : Ty} {names : List String}
    {bodyS : Stmt} {bodyOut : Output.Body}
    (hbody : StmtSim (N := N) m fs fuel bodyEnv (.state names) (blockStatements bodyS) bodyOut)
    (henv : bodyEnv = env.add { name := x, binding := .const, type := elemType })
    (hfresh : env.has x = false)
    (hnames : names = changedNames (blockStatements bodyS) env) :
    ∀ (vs : List (Val N)) (ρs ρo ρo' : Eval.Env N), Agree ρs ρo → Scoped m env ρs →
      Output.Body.runFold fs fuel names x bodyOut ρo vs = some ρo' →
      ∃ mod, Eval.execLoop m fuel ρs x bodyS vs = some (.normal mod) ∧ Agree mod ρo' ∧
        Frame (stmtChanges bodyS) mod ρs := by
  subst henv
  intro vs
  induction vs with
  | nil =>
    intro ρs ρo ρo' ha hs h
    simp only [Output.Body.runFold, Option.some.injEq] at h
    subst h
    exact ⟨ρs, by simp [Eval.execLoop], ha, Frame.refl _ _⟩
  | cons v vs ih =>
    intro ρs ρo ρo' ha hs h
    simp only [Output.Body.runFold] at h
    cases hb : Output.Body.exec fs fuel ((x, v) :: ρo) bodyOut with
    | none => simp [hb] at h
    | some ob =>
      cases ob with
      | ret _ => simp [hb] at h
      | normal inner =>
        cases hbs : Output.bindState names inner ρo with
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

theorem stmts_sound (hc : CallsAgree (N := N) m.program fs fuel) (F : Nat) :
    (∀ env tail ss ctx body ctx', translateStatements F env tail ss ctx = .ok body ctx' →
      StmtSim (N := N) m fs fuel env tail ss body) ∧
    (∀ env s d rest tail ctx body ctx', translateVariable F env s d rest tail ctx = .ok body ctx' →
      StmtSim (N := N) m fs fuel env tail (.varDecl s d :: rest) body) ∧
    (∀ env s test t e rest tail ctx body ctx', translateIf F env s test t e rest tail ctx = .ok body ctx' →
      StmtSim (N := N) m fs fuel env tail (.ifStmt s test t e :: rest) body) ∧
    (∀ env s kind x iterable b rest tail ctx body ctx',
      translateForOf F env s kind x iterable b rest tail ctx = .ok body ctx' →
      StmtSim (N := N) m fs fuel env tail (.forOfStmt s kind x iterable b :: rest) body) := by
  induction F with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;>
      simp_all [translateStatements, translateVariable, translateIf, translateForOf]
  | succ F ih =>
    obtain ⟨ihS, ihV, ihI, ihF⟩ := ih
    refine ⟨?_, ?_, ?_, ?_⟩
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
          refine ⟨fun v hv => by simp [Output.Body.exec] at hv, fun ρo' hv => ?_⟩
          simp only [Output.Body.exec, Option.some.injEq, Outcome.normal.injEq] at hv
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
              simp only [Output.Body.exec, eval_value] at hw
              cases hv : Output.Expr.eval fs fuel ρo code.code with
              | none => simp [hv] at hw
              | some u =>
                simp [hv] at hw
                subst hw
                simp [Eval.exec, Eval.execStmt, hsim ρs ρo u ha hs hv]
            · intro ρo' hv
              simp only [Output.Body.exec] at hv
              cases hv' : Output.Expr.eval fs fuel ρo code.value <;> simp [hv'] at hv
          · simp at h
        | exprStmt sp e =>
          simp only [bind_ok] at h
          obtain ⟨⟨name, upd⟩, s₁, hu, rb, s₂, hr, h⟩ := h
          simp only [pure_ok] at h
          obtain ⟨rfl, -⟩ := h
          have hrest := ihS _ _ _ _ _ _ hr
          intro ρs ρo ha hs
          have key : ∀ o, Output.Body.exec fs fuel ρo (.let name upd rb) = some o →
              ∃ w, Output.Expr.eval fs fuel ρo upd = some w ∧
                Output.Body.exec fs fuel ((name, w) :: ρo) rb = some o := by
            intro o ho
            simp only [Output.Body.exec] at ho
            cases hw : Output.Expr.eval fs fuel ρo upd with
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
            simp only [Output.Body.exec] at ho
            cases hw : Output.Expr.eval fs fuel ρo code.value with
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
                   simp only [Output.Body.exec] at ho
                   cases hw : Output.Expr.eval fs fuel ρo code.value with
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
                   simp only [Output.Body.exec] at ho
                   cases hw : Output.Expr.eval fs fuel ρo code.value with
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
                 simp only [Output.Body.exec] at ho
                 cases hw : Output.Expr.evalList fs fuel ρo r.1 with
                 | none => simp [hw] at ho
                 | some ws =>
                   exact ⟨.list ws, fun ρs ha hs => by
                     rw [Eval.eval]; simp [hsim ρs ρo ws ha hs hw], by simpa [hw] using ho⟩)
               (ihS _ _ _ _ _ _ hrb))
    · intro env s test t e rest tail ctx body ctx' h
      unfold translateIf at h
      cases hn : nullTestOf env test with
      | none =>
        simp only [hn, ite_state] at h
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
    · intro env s kind x iterable b rest tail ctx body ctx' h
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
            have key : ∀ o, Output.Body.exec fs fuel ρo body = some o →
                ∃ mod ρo₂, Eval.execStmt m fuel ρs (.forOfStmt s .const x iterable b) = some (.normal mod) ∧
                  Agree mod ρo₂ ∧ Frame (stmtChanges (.forOfStmt s .const x iterable b)) mod ρs ∧
                  Output.Body.exec fs fuel ρo₂ rb = some o := by
              intro o ho
              rw [← hbodyEq] at ho
              simp only [Output.Body.exec] at ho
              cases hi : Output.Expr.eval fs fuel ρo items.code with
              | none => simp [hi] at ho
              | some u =>
                cases u <;> simp [hi] at ho
                rename_i vs
                cases hf : Output.Body.runFold fs fuel (changedNames (blockStatements b) env) x bodyOut ρo vs with
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

end tolean.TypeScript.Proof
