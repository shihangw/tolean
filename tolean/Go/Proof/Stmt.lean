import tolean.Go.Proof.Expr

/-!
The translation of a statement list means what the statements mean.

`stmts_sound` states it for `translateStmts`, with `StmtSim`. When the output
body returns a value, the interpreter returns the same value. When the output
body ends, as the body of a branch does, the interpreter ends too, and its
environment agrees with the output's.

The interpreter keeps one environment and changes a variable in place, while
the output binds a new name for each change. So the proof tracks where the
interpreter's environment differs from the one it started with. A `Frame`
says that the names are the same and in the same places, and that only the
names the statements may assign have new values. The bindings that a
statement list declares come in front, and the translator's `declare` makes
sure that none of them is a name already in scope.

The proof follows the one for TypeScript in `tolean/TypeScript/Proof/Stmt.lean`.
Calls are still the hypothesis `CallsAgree`, as in `Proof/Expr.lean`.
-/
namespace tolean.Go.Proof

open tolean.Go tolean.Go.Syntax tolean.Go.Pure
open tolean.Go.Eval (Val Outcome BinOp AssignKind)

/-! ### Environments -/

theorem lookup_cons_eq (x : String) (w : Val) (ρ : Eval.Env) :
    List.lookup x ((x, w) :: ρ) = some w := by
  simp [List.lookup]

theorem lookup_cons_ne {x n : String} (w : Val) (ρ : Eval.Env) (h : n ≠ x) :
    List.lookup n ((x, w) :: ρ) = List.lookup n ρ := by
  have : (n == x) = false := by simpa using h
  simp [List.lookup, this]

theorem Env.lookup_set_same : ∀ (ρ : Eval.Env) (n : String) (v : Val), (ρ.lookup n).isSome →
    (ρ.set n v).lookup n = some v
  | [], _, _, h => by simp at h
  | (k, w) :: rest, n, v, h => by
    simp only [Eval.Env.set]
    by_cases hk : k = n
    · subst hk; simp
    · have h1 : (k == n) = false := by simpa using hk
      simp only [h1, Bool.false_eq_true, ↓reduceIte, lookup_cons_ne _ _ (Ne.symm hk)]
      rw [lookup_cons_ne _ _ (Ne.symm hk)] at h
      exact Env.lookup_set_same rest n v h

theorem Env.lookup_set_ne : ∀ (ρ : Eval.Env) (n k : String) (v : Val), n ≠ k →
    (ρ.set n v).lookup k = ρ.lookup k
  | [], _, _, _, _ => rfl
  | (j, w) :: rest, n, k, v, h => by
    simp only [Eval.Env.set]
    by_cases hj : j = n
    · subst hj
      simp [lookup_cons_ne _ _ (Ne.symm h)]
    · have h1 : (j == n) = false := by simpa using hj
      simp only [h1, Bool.false_eq_true, ↓reduceIte]
      by_cases hk : k = j
      · subst hk; simp
      · rw [lookup_cons_ne _ _ hk, lookup_cons_ne _ _ hk]
        exact Env.lookup_set_ne rest n k v h

/-! ### Frames -/

/-- `ρ'` has the names of `ρ` in the same places, and the same value for each
name outside `changes`. -/
def Frame (changes : List String) : Eval.Env → Eval.Env → Prop
  | [], [] => True
  | p :: ρ', q :: ρ => p.1 = q.1 ∧ (p.1 ∉ changes → p.2 = q.2) ∧ Frame changes ρ' ρ
  | _, _ => False

variable {c c₁ c₂ : List String}

theorem Frame.refl (c : List String) : ∀ ρ : Eval.Env, Frame c ρ ρ
  | [] => trivial
  | _ :: ρ => ⟨rfl, fun _ => rfl, Frame.refl c ρ⟩

theorem Frame.length : ∀ {ρ' ρ : Eval.Env}, Frame c ρ' ρ → ρ'.length = ρ.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, ⟨_, _, h⟩ => by simp [h.length]
  | [], _ :: _, h | _ :: _, [], h => h.elim

theorem Frame.mono (hc : ∀ n, n ∈ c → n ∈ c₁) : ∀ {ρ' ρ : Eval.Env}, Frame c ρ' ρ → Frame c₁ ρ' ρ
  | [], [], _ => trivial
  | _ :: _, _ :: _, ⟨hk, hv, h⟩ => ⟨hk, fun hn => hv fun hn' => hn (hc _ hn'), h.mono hc⟩
  | [], _ :: _, h | _ :: _, [], h => h.elim

theorem Frame.trans : ∀ {ρ₂ ρ₁ ρ : Eval.Env}, Frame c₂ ρ₂ ρ₁ → Frame c₁ ρ₁ ρ → Frame (c₁ ++ c₂) ρ₂ ρ
  | [], [], [], _, _ => trivial
  | _ :: _, _ :: _, _ :: _, ⟨hk, hv, h⟩, ⟨hk', hv', h'⟩ =>
    ⟨hk.trans hk', fun hn => by
      simp only [List.mem_append, not_or] at hn
      rw [hv hn.2, hv' (hk ▸ hn.1)], h.trans h'⟩
  | [], _ :: _, _, h, _ | _ :: _, [], _, h, _ => h.elim
  | [], [], _ :: _, _, h | _ :: _, _ :: _, [], _, h => h.elim

theorem Frame.lookup {n : String} (hn : n ∉ c) :
    ∀ {ρ' ρ : Eval.Env}, Frame c ρ' ρ → ρ'.lookup n = ρ.lookup n
  | [], [], _ => rfl
  | (k, v) :: _, (k', v') :: _, ⟨hk, hv, h⟩ => by
    simp only at hk hv
    subst hk
    by_cases hnk : n = k
    · subst hnk; simp [hv hn]
    · rw [lookup_cons_ne _ _ hnk, lookup_cons_ne _ _ hnk]
      exact h.lookup hn
  | [], _ :: _, h | _ :: _, [], h => h.elim

theorem Frame.isSome (n : String) :
    ∀ {ρ' ρ : Eval.Env}, Frame c ρ' ρ → (ρ'.lookup n).isSome = (ρ.lookup n).isSome
  | [], [], _ => rfl
  | (k, v) :: _, (k', v') :: _, ⟨hk, _, h⟩ => by
    simp only at hk
    subst hk
    by_cases hnk : n = k
    · subst hnk; simp
    · rw [lookup_cons_ne _ _ hnk, lookup_cons_ne _ _ hnk]
      exact h.isSome n
  | [], _ :: _, h | _ :: _, [], h => h.elim

theorem Frame.set {n : String} {v : Val} (hn : n ∈ c) : ∀ ρ : Eval.Env, Frame c (ρ.set n v) ρ
  | [] => trivial
  | (k, w) :: ρ => by
    simp only [Eval.Env.set]
    split
    · rename_i hk
      have : k = n := by simpa using hk
      subst this
      exact ⟨rfl, fun h => absurd hn h, Frame.refl c ρ⟩
    · exact ⟨rfl, fun _ => rfl, Frame.set hn ρ⟩

theorem Frame.mem {p : String × Val} :
    ∀ {ρ' ρ : Eval.Env}, Frame c ρ' ρ → p ∈ ρ' → ∃ q ∈ ρ, p.1 = q.1
  | _ :: _, q :: _, ⟨hk, _, h⟩, hp => by
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨q, List.mem_cons_self .., hk⟩
    · obtain ⟨q', hq', hk'⟩ := Frame.mem h hp
      exact ⟨q', List.mem_cons_of_mem _ hq', hk'⟩
  | [], _, _, hp => by simp at hp
  | _ :: _, [], h, _ => h.elim

theorem Frame.split : ∀ {ρ' a b : Eval.Env}, Frame c ρ' (a ++ b) →
    ∃ ρ₁ ρ₂, ρ' = ρ₁ ++ ρ₂ ∧ Frame c ρ₁ a ∧ Frame c ρ₂ b
  | ρ', [], b, h => ⟨[], ρ', rfl, trivial, h⟩
  | p :: ρ', q :: a, b, ⟨hk, hv, h⟩ => by
    obtain ⟨ρ₁, ρ₂, rfl, h₁, h₂⟩ := Frame.split h
    exact ⟨p :: ρ₁, ρ₂, rfl, ⟨hk, hv, h₁⟩, h₂⟩
  | [], _ :: _, _, h => h.elim

theorem lookup_append_fresh {n : String} :
    ∀ {new : Eval.Env} (mod : Eval.Env), (∀ p ∈ new, p.1 ≠ n) → (new ++ mod).lookup n = mod.lookup n
  | [], _, _ => rfl
  | (k, v) :: new, mod, h => by
    have hk : n ≠ k := Ne.symm (h (k, v) (List.mem_cons_self ..))
    rw [List.cons_append, lookup_cons_ne _ _ hk]
    exact lookup_append_fresh mod fun p hp => h p (List.mem_cons_of_mem _ hp)

theorem bindState_lookup {inner : Eval.Env} :
    ∀ {names : List String} {outer ρ : Eval.Env}, IR.bindState names inner outer = some ρ →
      ∀ n, ρ.lookup n = if n ∈ names then inner.lookup n else outer.lookup n
  | [], outer, ρ, h, n => by
    simp [IR.bindState] at h; subst h; simp
  | k :: ks, outer, ρ, h, n => by
    simp only [IR.bindState, List.foldlM_cons] at h
    cases hk : inner.lookup k with
    | none => simp [hk] at h
    | some w =>
      simp only [hk] at h
      have hmid : ∀ m, (if (outer.lookup k).isSome then Eval.Env.set outer k w else (k, w) :: outer).lookup m =
          if m = k then some w else outer.lookup m := by
        intro m
        split
        · next hs =>
          by_cases hm : m = k
          · subst hm; simp [Env.lookup_set_same _ _ _ hs]
          · simp [hm, Env.lookup_set_ne _ _ _ _ (Ne.symm hm)]
        · by_cases hm : m = k
          · subst hm; simp
          · simp [hm, lookup_cons_ne _ _ hm]
      have := bindState_lookup (names := ks) (by simpa [IR.bindState] using h) n
      rw [this, hmid]
      by_cases hn : n = k
      · subst hn; by_cases hm : n ∈ ks <;> simp [hm, hk]
      · by_cases hm : n ∈ ks <;> simp [hm, hn]

/-! ### The translator's scope -/

theorem has_append (env : Pure.Env) (x : String) (ty : Ty) (n : String) :
    (env ++ [Local.mk x ty]).has n = (env.has n || x == n) := by
  simp only [Pure.Env.has, Pure.Env.lookup, List.find?_append]
  cases env.find? (·.name == n) <;> simp [List.find?]
  split <;> simp_all

theorem has_iff (env : Pure.Env) (n : String) : env.has n = true ↔ ∃ l ∈ env, l.name = n := by
  simp [Pure.Env.has, Pure.Env.lookup, List.find?_isSome]

theorem mem_changedNames {ss : List Stmt} {env : Pure.Env} {n : String} :
    n ∈ changedNames ss env ↔ env.has n = true ∧ n ∈ changesList ss := by
  rw [has_iff]
  simp only [changedNames, List.mem_map, List.mem_filter, List.contains_iff_mem]
  constructor
  · rintro ⟨l, ⟨hl, hc⟩, rfl⟩; exact ⟨⟨l, hl, rfl⟩, by simpa using hc⟩
  · rintro ⟨⟨l, hl, rfl⟩, hc⟩; exact ⟨l, ⟨hl, by simpa using hc⟩, rfl⟩

theorem changesList_append (a b : List Stmt) : changesList (a ++ b) = changesList a ++ changesList b := by
  induction a with
  | nil => simp [changesList]
  | cons s rest ih => simp [changesList, ih]

theorem changesList_block (t : Stmt) : changesList (blockStatements t) = stmtChanges t := by
  cases t <;> simp [blockStatements, changesList, stmtChanges]

theorem changesList_else (els : Option Stmt) : changesList (elseStatements els) = changesOption els := by
  cases els <;> simp [elseStatements, changesOption, changesList_block, changesList]

/-! ### The interpreter on statements -/

variable (p : Eval.Program) (fs : Funcs) (fuel : Nat)

theorem exec_nil (ρ : Eval.Env) : Eval.exec p fuel ρ [] = some (.normal ρ) := by
  rw [Eval.exec]

theorem exec_cons (s : Stmt) (rest : List Stmt) (ρ : Eval.Env) :
    Eval.exec p fuel ρ (s :: rest) = (Eval.execStmt p fuel ρ s).bind fun
      | .ret v => some (.ret v)
      | .normal ρ' => Eval.exec p fuel ρ' rest := by
  rw [Eval.exec]; rfl

theorem exec_cons_normal {s : Stmt} {rest : List Stmt} {ρ ρ' : Eval.Env}
    (h : Eval.execStmt p fuel ρ s = some (.normal ρ')) :
    Eval.exec p fuel ρ (s :: rest) = Eval.exec p fuel ρ' rest := by
  rw [exec_cons, h]; rfl

theorem exec_cons_ret {s : Stmt} {rest : List Stmt} {ρ : Eval.Env} {v : Val}
    (h : Eval.execStmt p fuel ρ s = some (.ret v)) :
    Eval.exec p fuel ρ (s :: rest) = some (.ret v) := by
  rw [exec_cons, h]; rfl

theorem exec_single (t : Stmt) (ρ : Eval.Env) : Eval.exec p fuel ρ [t] = Eval.execStmt p fuel ρ t := by
  rw [exec_cons]
  cases h : Eval.execStmt p fuel ρ t with
  | none => rfl
  | some o => cases o <;> simp [exec_nil]

theorem blockStatements_eq (t : Stmt) :
    blockStatements t = [t] ∨ ∃ sp body, t = .block sp body ∧ blockStatements t = body := by
  cases t <;> simp [blockStatements]

theorem execStmt_block (sp : Span) (body : List Stmt) (ρ : Eval.Env) :
    Eval.execStmt p fuel ρ (.block sp body) = (Eval.exec p fuel ρ body).bind fun
      | .ret v => some (.ret v)
      | .normal ρ' => some (.normal (ρ'.drop (ρ'.length - ρ.length))) := by
  rw [Eval.execStmt]; rfl

theorem block_ret (t : Stmt) {ρ : Eval.Env} {v : Val}
    (h : Eval.exec p fuel ρ (blockStatements t) = some (.ret v)) :
    Eval.execStmt p fuel ρ t = some (.ret v) := by
  rcases blockStatements_eq t with h1 | ⟨sp, body, rfl, h1⟩
  · rwa [h1, exec_single] at h
  · rw [h1] at h
    rw [execStmt_block, h]
    rfl

theorem block_normal (t : Stmt) {ρ new mod : Eval.Env} {c : List String}
    (h : Eval.exec p fuel ρ (blockStatements t) = some (.normal (new ++ mod))) (hf : Frame c mod ρ) :
    ∃ e, Eval.execStmt p fuel ρ t = some (.normal e) ∧ e.drop (e.length - ρ.length) = mod := by
  have hlen := hf.length
  rcases blockStatements_eq t with h1 | ⟨sp, body, rfl, h1⟩
  · rw [h1, exec_single] at h
    refine ⟨new ++ mod, h, ?_⟩
    have : (new ++ mod).length - ρ.length = new.length := by simp [hlen]
    rw [this, List.drop_left]
  · rw [h1] at h
    refine ⟨mod, by rw [execStmt_block, h]; simp [hlen], by simp [hlen]⟩

theorem execStmt_if (sp : Span) (c : Expr) (t : Stmt) (els : Option Stmt) (ρ : Eval.Env) (b : Bool)
    (hc : Eval.eval p fuel ρ c = some (.bool b)) :
    Eval.execStmt p fuel ρ (.ifStmt sp none c t els) = (do
      let out ← if b then Eval.execStmt p fuel ρ t
        else match els with
          | some f => Eval.execStmt p fuel ρ f
          | none => some (.normal ρ)
      match out with
      | .ret v => some (.ret v)
      | .normal ρ' => some (.normal (ρ'.drop (ρ'.length - ρ.length)))) := by
  rw [Eval.execStmt, hc]; rfl

/-- The statements of the branch that the test picks. -/
def branchOf (b : Bool) (t : Stmt) (els : Option Stmt) : List Stmt :=
  if b then blockStatements t else elseStatements els

theorem if_ret {sp : Span} {c : Expr} {t : Stmt} {els : Option Stmt} {ρ : Eval.Env} {b : Bool}
    {v : Val} (hc : Eval.eval p fuel ρ c = some (.bool b))
    (hex : Eval.exec p fuel ρ (branchOf b t els) = some (.ret v)) :
    Eval.execStmt p fuel ρ (.ifStmt sp none c t els) = some (.ret v) := by
  rw [execStmt_if p fuel sp c t els ρ b hc]
  unfold branchOf at hex
  cases b
  · cases els with
    | none => simp [elseStatements, exec_nil] at hex
    | some f =>
      simp only [elseStatements, Bool.false_eq_true, ↓reduceIte] at hex ⊢
      simp [block_ret p fuel f hex]
  · simp only [↓reduceIte] at hex ⊢
    simp [block_ret p fuel t hex]

theorem if_normal {sp : Span} {c : Expr} {t : Stmt} {els : Option Stmt} {ρ new mod : Eval.Env}
    {b : Bool} {cs : List String} (hc : Eval.eval p fuel ρ c = some (.bool b))
    (hex : Eval.exec p fuel ρ (branchOf b t els) = some (.normal (new ++ mod)))
    (hf : Frame cs mod ρ) :
    Eval.execStmt p fuel ρ (.ifStmt sp none c t els) = some (.normal mod) := by
  rw [execStmt_if p fuel sp c t els ρ b hc]
  unfold branchOf at hex
  have hlen := hf.length
  cases b
  · cases els with
    | none =>
      simp only [elseStatements, Bool.false_eq_true, ↓reduceIte, exec_nil, Option.some.injEq,
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
      simp only [elseStatements, Bool.false_eq_true, ↓reduceIte] at hex ⊢
      obtain ⟨e', h1, h2⟩ := block_normal p fuel f hex hf
      simp [h1, h2]
  · simp only [↓reduceIte] at hex ⊢
    obtain ⟨e', h1, h2⟩ := block_normal p fuel t hex hf
    simp [h1, h2]

/-! ### The output on bodies -/

theorem out_value {e : IR.Expr} {ρ : Eval.Env} {o : Outcome}
    (h : IR.Body.exec fs fuel ρ (.value e) = some o) :
    ∃ v, IR.Expr.eval fs fuel ρ e = some v ∧ o = .ret v := by
  simp only [IR.Body.exec] at h
  cases he : IR.Expr.eval fs fuel ρ e with
  | none => simp [he] at h
  | some v => simp [he] at h; exact ⟨v, rfl, h.symm⟩

theorem out_let {x : String} {e : IR.Expr} {rest : IR.Body} {ρ : Eval.Env} {o : Outcome}
    (h : IR.Body.exec fs fuel ρ (.let x e rest) = some o) :
    ∃ w, IR.Expr.eval fs fuel ρ e = some w ∧ IR.Body.exec fs fuel ((x, w) :: ρ) rest = some o := by
  simp only [IR.Body.exec] at h
  cases he : IR.Expr.eval fs fuel ρ e with
  | none => simp [he] at h
  | some w => simp [he] at h; exact ⟨w, rfl, h⟩

theorem out_ite {c : IR.Expr} {a b : IR.Body} {ρ : Eval.Env} {o : Outcome}
    (h : IR.Body.exec fs fuel ρ (.ite c a b) = some o) :
    ∃ t, IR.Expr.eval fs fuel ρ c = some (.bool t) ∧
      IR.Body.exec fs fuel ρ (if t then a else b) = some o := by
  simp only [IR.Body.exec] at h
  cases hc : IR.Expr.eval fs fuel ρ c with
  | none => simp [hc] at h
  | some w =>
    cases w <;> simp [hc] at h
    rename_i t
    exact ⟨t, rfl, by cases t <;> simpa using h⟩

theorem out_letState {names : List String} {br rest : IR.Body} {ρ : Eval.Env} {o : Outcome}
    (h : IR.Body.exec fs fuel ρ (.letState names br rest) = some o) :
    ∃ inner ρ₁, IR.Body.exec fs fuel ρ br = some (.normal inner) ∧
      IR.bindState names inner ρ = some ρ₁ ∧ IR.Body.exec fs fuel ρ₁ rest = some o := by
  simp only [IR.Body.exec] at h
  cases hb : IR.Body.exec fs fuel ρ br with
  | none => simp [hb] at h
  | some r =>
    cases r with
    | ret v => simp [hb] at h
    | normal inner =>
      cases hs : IR.bindState names inner ρ with
      | none => simp [hb, hs] at h
      | some ρ₁ => simp [hb, hs] at h; exact ⟨inner, ρ₁, rfl, hs, h⟩

/-! ### Statement lists -/

def _root_.tolean.Go.Pure.Tail.isRet : Tail → Bool
  | .ret _ => true
  | .state _ => false

/-- The output body `body` means what the statements `ss` mean. A return gives
the same value. An end, which only a body for a branch has, gives
environments that agree. The interpreter's has new bindings in front, which
`env` does not have, and it changes only the names that `ss` may assign. -/
def StmtSim (env : Pure.Env) (tail : Tail) (ss : List Stmt) (body : IR.Body) : Prop :=
  ∀ (ρs ρo : Eval.Env), Agree ρs ρo → Scoped env ρs →
    (∀ v, IR.Body.exec fs fuel ρo body = some (.ret v) → Eval.exec p fuel ρs ss = some (.ret v)) ∧
    (∀ ρo', IR.Body.exec fs fuel ρo body = some (.normal ρo') →
      tail.isRet = false ∧ ∃ new mod, Eval.exec p fuel ρs ss = some (.normal (new ++ mod)) ∧
        Agree (new ++ mod) ρo' ∧ (∀ q ∈ new, env.has q.1 = false) ∧ Frame (changesList ss) mod ρs)

theorem agree_cons {ρs ρo : Eval.Env} (ha : Agree ρs ρo) (x : String) (w : Val) :
    Agree ((x, w) :: ρs) ((x, w) :: ρo) := fun n => by
  by_cases hn : n = x
  · subst hn; simp
  · rw [lookup_cons_ne _ _ hn, lookup_cons_ne _ _ hn]; exact ha n

theorem scoped_cons {env : Pure.Env} {ρ : Eval.Env} (hs : Scoped env ρ) (x : String) (ty : Ty)
    (w : Val) : Scoped (env ++ [Local.mk x ty]) ((x, w) :: ρ) := fun n => by
  rw [has_append, ← hs n]
  by_cases hn : n = x
  · subst hn; simp
  · rw [lookup_cons_ne _ _ hn]
    have : (x == n) = false := by simpa using Ne.symm hn
    simp [this]

theorem agree_set {ρs ρo : Eval.Env} {n : String} {w : Val} (ha : Agree ρs ρo)
    (hn : (ρs.lookup n).isSome) : Agree (ρs.set n w) ((n, w) :: ρo) := by
  intro x
  by_cases hx : x = n
  · subst hx; rw [Env.lookup_set_same _ _ _ hn, lookup_cons_eq]
  · rw [Env.lookup_set_ne _ _ _ _ (Ne.symm hx), lookup_cons_ne _ _ hx]
    exact ha x

/-- A statement that declares the local `x` with the value `w`, which is new
in `env`, means what the source means, when the rest does. -/
theorem push_sim {env : Pure.Env} {st : Stmt} {rest : List Stmt} {tail : Tail} {body rb : IR.Body}
    {x : String} {ty : Ty} (hfresh : env.has x = false)
    (hbody : ∀ (ρo : Eval.Env) (o : Outcome), IR.Body.exec fs fuel ρo body = some o → ∃ w,
      (∀ ρs, Agree ρs ρo → Scoped env ρs → Eval.execStmt p fuel ρs st = some (.normal ((x, w) :: ρs))) ∧
        IR.Body.exec fs fuel ((x, w) :: ρo) rb = some o)
    (hrest : StmtSim p fs fuel (env ++ [Local.mk x ty]) tail rest rb) :
    StmtSim p fs fuel env tail (st :: rest) body := by
  intro ρs ρo ha hs
  constructor
  · intro v hv
    obtain ⟨w, hw, hb⟩ := hbody ρo _ hv
    rw [exec_cons_normal p fuel (hw ρs ha hs)]
    exact (hrest _ _ (agree_cons ha x w) (scoped_cons hs x ty w)).1 v hb
  · intro ρo' hv
    obtain ⟨w, hw, hb⟩ := hbody ρo _ hv
    obtain ⟨htail, new, mod, hex, hag, hnew, hfr⟩ :=
      (hrest _ _ (agree_cons ha x w) (scoped_cons hs x ty w)).2 ρo' hb
    obtain ⟨ρ₁, ρ₂, rfl, h₁, h₂⟩ := Frame.split (a := [(x, w)]) (b := ρs) hfr
    refine ⟨htail, new ++ ρ₁, ρ₂, ?_, ?_, ?_, ?_⟩
    · rw [exec_cons_normal p fuel (hw ρs ha hs), List.append_assoc]; exact hex
    · rwa [List.append_assoc]
    · intro q hq
      rcases List.mem_append.mp hq with hq | hq
      · have := hnew q hq
        rw [has_append] at this
        simp only [Bool.or_eq_false_iff] at this
        exact this.1
      · obtain ⟨q', hq', hk⟩ := Frame.mem h₁ hq
        simp only [List.mem_singleton] at hq'
        subst hq'
        rw [hk]; exact hfresh
    · exact h₂.mono fun n hn => by simp [changesList, hn]

/-- A statement that gives the local `x` the value `w`, where `x` is in
scope, means what the source means, when the rest does. -/
theorem set_sim {env : Pure.Env} {st : Stmt} {rest : List Stmt} {tail : Tail} {body rb : IR.Body}
    {x : String} (hx : env.has x = true) (hch : x ∈ stmtChanges st)
    (hbody : ∀ (ρo : Eval.Env) (o : Outcome), IR.Body.exec fs fuel ρo body = some o → ∃ w,
      (∀ ρs, Agree ρs ρo → Scoped env ρs → Eval.execStmt p fuel ρs st = some (.normal (ρs.set x w))) ∧
        IR.Body.exec fs fuel ((x, w) :: ρo) rb = some o)
    (hrest : StmtSim p fs fuel env tail rest rb) :
    StmtSim p fs fuel env tail (st :: rest) body := by
  intro ρs ρo ha hs
  have hsome : (ρs.lookup x).isSome := by rw [hs x]; exact hx
  have hset : ∀ w : Val, Frame [x] (ρs.set x w) ρs := fun w => Frame.set (by simp) ρs
  have hs' : ∀ w : Val, Scoped env (ρs.set x w) := fun w n => ((hset w).isSome n).trans (hs n)
  constructor
  · intro v hv
    obtain ⟨w, hw, hb⟩ := hbody ρo _ hv
    rw [exec_cons_normal p fuel (hw ρs ha hs)]
    exact (hrest _ _ (agree_set ha hsome) (hs' w)).1 v hb
  · intro ρo' hv
    obtain ⟨w, hw, hb⟩ := hbody ρo _ hv
    obtain ⟨htail, new, mod, hex, hag, hnew, hfr⟩ := (hrest _ _ (agree_set ha hsome) (hs' w)).2 ρo' hb
    refine ⟨htail, new, mod, ?_, hag, hnew, ?_⟩
    · rw [exec_cons_normal p fuel (hw ρs ha hs)]; exact hex
    · exact (hfr.trans (hset w)).mono fun n hn => by
        simp only [List.mem_append, List.mem_singleton] at hn
        rcases hn with rfl | hn
        · simp [changesList, hch]
        · simp [changesList, hn]

/-! ### The translator on statements -/

theorem declare_ok {env env' : Pure.Env} {sp : Span} {x : String} {ty : Ty}
    (h : declare env sp x ty = .ok env') : env.has x = false ∧ env' = env ++ [Local.mk x ty] := by
  unfold declare at h
  split at h
  · exact absurd h reject_ne_ok
  · next hx =>
    split at h
    · exact absurd h reject_ne_ok
    · simp only [pure_ok] at h
      exact ⟨by simpa using hx, h.symm⟩

theorem zero_sound {ctx : Ctx} (hp : ctx.program = p) {te : Expr} {t : Ty}
    (ht : resolveType ctx te = some t) {ρ : Eval.Env} {w : Val}
    (hw : IR.Expr.eval fs fuel ρ (zeroCode t) = some w) : Eval.zeroOf p te = some w := by
  cases te with
  | ident sp name =>
    simp only [resolveType] at ht
    subst hp
    simp only [Eval.zeroOf]
    split at ht
    · simp at ht
    · next hn =>
      simp only [hn, Bool.false_eq_true, ↓reduceIte]
      split at ht <;> simp only [Option.some.injEq, reduceCtorEq] at ht <;> subst ht <;>
        simp only [zeroCode, IR.Expr.eval, Option.some.injEq] at hw <;> subst hw <;> rfl
  | _ => simp [resolveType] at ht

/-- `stmts_sound` and its case for `if`, by induction on the translator's
fuel. -/
theorem stmts_sound_aux {ctx : Ctx} (hp : ctx.program = p) (hc : CallsAgree p fs fuel) :
    ∀ n : Nat,
      (∀ env tail ss body, translateStmts ctx env tail n ss = .ok body →
        StmtSim p fs fuel env tail ss body) ∧
      (∀ env tail sp c t els rest body, translateIf ctx env tail n sp c t els rest = .ok body →
        StmtSim p fs fuel env tail (.ifStmt sp none c t els :: rest) body)
  | 0 => ⟨fun env tail ss body h => by simp [translateStmts] at h,
      fun env tail sp c t els rest body h => by simp [translateIf] at h⟩
  | n + 1 => by
    obtain ⟨ihs, ihi⟩ := stmts_sound_aux hp hc n
    refine ⟨fun env tail ss body h => ?_, fun env tail sp c t els rest body h => ?_⟩
    · cases ss with
      | nil =>
        cases tail with
        | ret r => simp [translateStmts] at h
        | state names =>
          simp only [translateStmts, pure_ok] at h
          subst h
          intro ρs ρo ha hs
          refine ⟨fun v hv => by simp [IR.Body.exec] at hv, fun ρo' hv => ?_⟩
          simp only [IR.Body.exec, Option.some.injEq, Outcome.normal.injEq] at hv
          subst hv
          exact ⟨rfl, [], ρs, exec_nil p fuel ρs, ha, by simp, Frame.refl _ ρs⟩
      | cons st rest =>
        rw [translateStmts.eq_def] at h
        simp only at h
        split at h
        -- `return e`
        · next sp e =>
          cases tail with
          | state names => simp [reject, throw, throwThe, MonadExceptOf.throw] at h
          | ret result =>
            cases rest with
            | cons _ _ => simp [reject, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
            | nil =>
              tm_simp at h
              obtain ⟨⟨ce, te⟩, hce, -, rfl⟩ := h
              intro ρs ρo ha hs
              refine ⟨fun v hv => ?_, fun ρo' hv => ?_⟩
              · obtain ⟨w, hw, hwv⟩ := out_value fs fuel hv
                cases hwv
                have he := expr_sound fs fuel p hp hc hce ha hs hw
                rw [exec_single, Eval.execStmt, he]; rfl
              · obtain ⟨w, -, hwv⟩ := out_value fs fuel hv
                cases hwv
        -- `x := e`, `x = e` and `x op= e`
        · next sp op sp' x e =>
          cases hk : AssignKind.ofString? op with
          | none => simp [hk, reject, throw, throwThe, MonadExceptOf.throw] at h
          | some kind =>
            simp only [hk, bind_ok] at h
            obtain ⟨⟨ce, te⟩, hce, h⟩ := h
            cases kind with
            | define =>
              simp only [bind_ok, pure_ok] at h
              obtain ⟨env', hdecl, rb, hrb, rfl⟩ := h
              obtain ⟨hfresh, rfl⟩ := declare_ok hdecl
              refine push_sim p fs fuel hfresh (fun ρo o hv => ?_) (ihs _ tail rest rb hrb)
              obtain ⟨w, hw, hb⟩ := out_let fs fuel hv
              refine ⟨w, fun ρs ha hs => ?_, hb⟩
              have he := expr_sound fs fuel p hp hc hce ha hs hw
              rw [Eval.execStmt]; simp [hk, he]
            | assign =>
              cases hl : env.lookup x with
              | none => simp [hl, reject, throw, throwThe, MonadExceptOf.throw] at h
              | some l =>
                simp only [hl] at h
                tm_simp at h
                obtain ⟨-, rb, hrb, rfl⟩ := h
                refine set_sim p fs fuel (env_has_of_lookup hl) (by simp [stmtChanges])
                  (fun ρo o hv => ?_) (ihs _ tail rest rb hrb)
                obtain ⟨w, hw, hb⟩ := out_let fs fuel hv
                refine ⟨w, fun ρs ha hs => ?_, hb⟩
                have he := expr_sound fs fuel p hp hc hce ha hs hw
                have hsome : (ρs.lookup x).isSome := by rw [hs x]; exact env_has_of_lookup hl
                obtain ⟨old, hold⟩ := Option.isSome_iff_exists.mp hsome
                rw [Eval.execStmt]; simp [hk, he, hold]
            | compound o =>
              cases hl : env.lookup x with
              | none => simp [hl, reject, throw, throwThe, MonadExceptOf.throw] at h
              | some l =>
                simp only [hl] at h
                tm_simp at h
                obtain ⟨⟨cb, tb⟩, hbin, -, rb, hrb, rfl⟩ := h
                refine set_sim p fs fuel (env_has_of_lookup hl) (by simp [stmtChanges])
                  (fun ρo o' hv => ?_) (ihs _ tail rest rb hrb)
                obtain ⟨w, hw, hb⟩ := out_let fs fuel hv
                refine ⟨w, fun ρs ha hs => ?_, hb⟩
                obtain ⟨va, vb, hva, hvb, hbw⟩ := translateBinary_out hbin hw
                simp only [IR.Expr.eval] at hva
                have he := expr_sound fs fuel p hp hc hce ha hs hvb
                rw [Eval.execStmt]; simp [hk, he, ha x, hva, hbw]
        -- `x++` and `x--`
        · next sp op sp' x =>
          cases ho : Eval.incDecOp? op with
          | none => simp [ho, reject, throw, throwThe, MonadExceptOf.throw] at h
          | some o =>
            cases hl : env.lookup x with
            | none => simp [ho, hl, reject, throw, throwThe, MonadExceptOf.throw] at h
            | some l =>
              simp only [ho, hl] at h
              tm_simp at h
              obtain ⟨⟨cb, tb⟩, hbin, -, rb, hrb, rfl⟩ := h
              refine set_sim p fs fuel (env_has_of_lookup hl) (by simp [stmtChanges])
                (fun ρo o' hv => ?_) (ihs _ tail rest rb hrb)
              obtain ⟨w, hw, hb⟩ := out_let fs fuel hv
              refine ⟨w, fun ρs ha hs => ?_, hb⟩
              obtain ⟨va, vb, hva, hvb, hbw⟩ := translateBinary_out hbin hw
              simp only [IR.Expr.eval, Option.some.injEq] at hva hvb
              subst hvb
              rw [Eval.execStmt]; simp [ho, ha x, hva, hbw]
        -- `var x T = e` and `var x T`
        · next sp sp' sp'' x te values =>
          cases ht : resolveType ctx te with
          | none => simp [ht, reject, throw, throwThe, MonadExceptOf.throw] at h
          | some ty =>
            simp only [ht] at h
            match values, h with
            | [], h =>
              tm_simp at h
              obtain ⟨env', hdecl, rb, hrb, rfl⟩ := h
              obtain ⟨hfresh, rfl⟩ := declare_ok hdecl
              refine push_sim p fs fuel hfresh (fun ρo o hv => ?_) (ihs _ tail rest rb hrb)
              obtain ⟨w, hw, hb⟩ := out_let fs fuel hv
              refine ⟨w, fun ρs ha hs => ?_, hb⟩
              have hz := zero_sound p fs fuel hp ht hw
              rw [Eval.execStmt]; simp [hz]
            | [e], h =>
              tm_simp at h
              obtain ⟨⟨c', t'⟩, hc', -, env', hdecl, rb, hrb, rfl⟩ := h
              obtain ⟨hfresh, rfl⟩ := declare_ok hdecl
              refine push_sim p fs fuel hfresh (fun ρo o hv => ?_) (ihs _ tail rest rb hrb)
              obtain ⟨w, hw, hb⟩ := out_let fs fuel hv
              refine ⟨w, fun ρs ha hs => ?_, hb⟩
              have he := expr_sound fs fuel p hp hc hc' ha hs hw
              rw [Eval.execStmt]; simp [he]
            | _ :: _ :: _, h => simp [reject, throw, throwThe, MonadExceptOf.throw] at h
        -- `if`
        · next sp c t els => exact ihi env tail sp c t els rest body h
        · exact absurd h reject_ne_ok
    · simp only [translateIf] at h
      rw [bind_ok] at h
      obtain ⟨⟨cond, ct⟩, hcond, h⟩ := h
      rw [ite_ok] at h
      simp only [pure_bind, bind_ok, reject_ne_ok, false_and, and_false, exists_false, or_false] at h
      obtain ⟨-, h⟩ := h
      split at h
      -- A branch returns: the rest joins the other branch.
      · cases tail with
        | state names => simp [reject, throw, throwThe, MonadExceptOf.throw] at h
        | ret result =>
          tm_simp at h
          obtain ⟨hnot, wt, hwt, wf, hwf, rfl⟩ := h
          have simT := ihs env (.ret result) (blockStatements t) wt hwt
          have simF := ihs env (.ret result) (elseStatements els ++ rest) wf hwf
          intro ρs ρo ha hs
          constructor
          · intro v hv
            obtain ⟨b, hb, hex⟩ := out_ite fs fuel hv
            have hcb := expr_sound fs fuel p hp hc hcond ha hs hb
            cases b
            · simp only [Bool.false_eq_true, ↓reduceIte] at hex
              have hr := (simF ρs ρo ha hs).1 v hex
              cases els with
              | none =>
                simp only [elseStatements, List.nil_append] at hr
                have hif : Eval.execStmt p fuel ρs (.ifStmt sp none c t none) = some (.normal ρs) :=
                  if_normal (new := []) p fuel hcb (by simp [branchOf, elseStatements, exec_nil])
                    (Frame.refl [] ρs)
                rw [exec_cons_normal p fuel hif]; exact hr
              | some f =>
                have hrest : rest = [] := by
                  simpa using hnot
                subst hrest
                simp only [List.append_nil] at hr
                exact exec_cons_ret p fuel (if_ret p fuel hcb (by simpa [branchOf] using hr))
            · simp only [↓reduceIte] at hex
              have hr := (simT ρs ρo ha hs).1 v hex
              exact exec_cons_ret p fuel (if_ret p fuel hcb (by simpa [branchOf] using hr))
          · intro ρo' hv
            obtain ⟨b, -, hex⟩ := out_ite fs fuel hv
            cases b
            · exact absurd ((simF ρs ρo ha hs).2 ρo' (by simpa using hex)).1 (by simp [Tail.isRet])
            · exact absurd ((simT ρs ρo ha hs).2 ρo' (by simpa using hex)).1 (by simp [Tail.isRet])
      -- No branch returns: the branches give the locals they change.
      · tm_simp at h
        obtain ⟨-, wt, hwt, wf, hwf, rb, hrb, rfl⟩ := h
        have simT := ihs env _ (blockStatements t) wt hwt
        have simF := ihs env _ (elseStatements els) wf hwf
        have simR := ihs env tail rest rb hrb
        intro ρs ρo ha hs
        have key : ∀ o, IR.Body.exec fs fuel ρo
            (.letState (changedNames (blockStatements t ++ elseStatements els) env) (.ite cond wt wf) rb) =
              some o →
            ∃ mod ρ₁, Eval.execStmt p fuel ρs (.ifStmt sp none c t els) = some (.normal mod) ∧
              Agree mod ρ₁ ∧ Scoped env mod ∧
              Frame (stmtChanges (.ifStmt sp none c t els)) mod ρs ∧
              IR.Body.exec fs fuel ρ₁ rb = some o := by
          intro o hv
          obtain ⟨inner, ρ₁, hbr, hbind, hrest⟩ := out_letState fs fuel hv
          obtain ⟨b, hb, hex⟩ := out_ite fs fuel hbr
          have hcb := expr_sound fs fuel p hp hc hcond ha hs hb
          have simB : StmtSim p fs fuel env
              (.state (changedNames (blockStatements t ++ elseStatements els) env))
              (branchOf b t els) (if b then wt else wf) := by
            cases b
            · simpa [branchOf] using simF
            · simpa [branchOf] using simT
          obtain ⟨-, new, mod, hexs, hag, hnew, hfr⟩ := (simB ρs ρo ha hs).2 inner hex
          have hchB : ∀ k, k ∈ changesList (branchOf b t els) →
              k ∈ changesList (blockStatements t ++ elseStatements els) := by
            intro k hk
            rw [changesList_append]
            cases b
            · exact List.mem_append_right _ (by simpa [branchOf] using hk)
            · exact List.mem_append_left _ (by simpa [branchOf] using hk)
          refine ⟨mod, ρ₁, if_normal p fuel hcb hexs hfr, ?_, ?_, ?_, hrest⟩
          · intro k
            rw [bindState_lookup hbind k]
            split
            · next hk =>
              have hkenv := (mem_changedNames.mp hk).1
              rw [← hag k, lookup_append_fresh mod (fun q hq heq => by
                have := hnew q hq
                rw [heq, hkenv] at this
                exact Bool.noConfusion this)]
            · next hk =>
              rw [← ha k]
              by_cases hkc : k ∈ changesList (branchOf b t els)
              · have hkenv : env.has k = false := by
                  cases h' : env.has k
                  · rfl
                  · exact absurd (mem_changedNames.mpr ⟨h', hchB k hkc⟩) hk
                have h1 := scoped_none hs hkenv
                have h2 := hfr.isSome k
                rw [h1] at h2 ⊢
                simpa using h2
              · exact hfr.lookup hkc
          · exact fun k => (hfr.isSome k).trans (hs k)
          · refine hfr.mono fun k hk => ?_
            simp only [stmtChanges, List.mem_append]
            cases b
            · right; simpa [branchOf, changesList_else] using hk
            · left; simpa [branchOf, changesList_block] using hk
        constructor
        · intro v hv
          obtain ⟨mod, ρ₁, hif, ha', hs', -, hrest⟩ := key _ hv
          rw [exec_cons_normal p fuel hif]
          exact (simR mod ρ₁ ha' hs').1 v hrest
        · intro ρo' hv
          obtain ⟨mod, ρ₁, hif, ha', hs', hfr, hrest⟩ := key _ hv
          obtain ⟨htail, new', mod', hex', hag', hnew', hfr'⟩ := (simR mod ρ₁ ha' hs').2 ρo' hrest
          refine ⟨htail, new', mod', by rw [exec_cons_normal p fuel hif]; exact hex', hag', hnew', ?_⟩
          simpa [changesList] using hfr'.trans hfr

/-- The body that the translator gives for a statement list means what the
statements mean. -/
theorem stmts_sound {ctx : Ctx} (hp : ctx.program = p) (hc : CallsAgree p fs fuel) {n : Nat}
    {env : Pure.Env} {tail : Tail} {ss : List Stmt} {body : IR.Body}
    (h : translateStmts ctx env tail n ss = .ok body) : StmtSim p fs fuel env tail ss body :=
  (stmts_sound_aux p fs fuel hp hc n).1 env tail ss body h

end tolean.Go.Proof
