import tolean.Go.Proof.Expr
import tolean.Go.Proof.Switch

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
      | .panic x => some (.panic x)
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

theorem exec_cons_panic {s : Stmt} {rest : List Stmt} {ρ : Eval.Env} {x : Val}
    (h : Eval.execStmt p fuel ρ s = some (.panic x)) :
    Eval.exec p fuel ρ (s :: rest) = some (.panic x) := by
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
      | .panic x => some (.panic x)
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

theorem block_panic (t : Stmt) {ρ : Eval.Env} {x : Val}
    (h : Eval.exec p fuel ρ (blockStatements t) = some (.panic x)) :
    Eval.execStmt p fuel ρ t = some (.panic x) := by
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
    (hc : Eval.eval p fuel ρ c = some (.ok (.bool b))) :
    Eval.execStmt p fuel ρ (.ifStmt sp none c t els) = (do
      let out ← if b then Eval.execStmt p fuel ρ t
        else match els with
          | some f => Eval.execStmt p fuel ρ f
          | none => some (.normal ρ)
      match out with
      | .ret v => some (.ret v)
      | .panic x => some (.panic x)
      | .normal ρ' => some (.normal (ρ'.drop (ρ'.length - ρ.length)))) := by
  rw [Eval.execStmt, hc]; rfl

/-- The statements of the branch that the test picks. -/
def branchOf (b : Bool) (t : Stmt) (els : Option Stmt) : List Stmt :=
  if b then blockStatements t else elseStatements els

theorem if_ret {sp : Span} {c : Expr} {t : Stmt} {els : Option Stmt} {ρ : Eval.Env} {b : Bool}
    {v : Val} (hc : Eval.eval p fuel ρ c = some (.ok (.bool b)))
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

theorem if_panic {sp : Span} {c : Expr} {t : Stmt} {els : Option Stmt} {ρ : Eval.Env} {b : Bool}
    {x : Val} (hc : Eval.eval p fuel ρ c = some (.ok (.bool b)))
    (hex : Eval.exec p fuel ρ (branchOf b t els) = some (.panic x)) :
    Eval.execStmt p fuel ρ (.ifStmt sp none c t els) = some (.panic x) := by
  rw [execStmt_if p fuel sp c t els ρ b hc]
  unfold branchOf at hex
  cases b
  · cases els with
    | none => simp [elseStatements, exec_nil] at hex
    | some f =>
      simp only [elseStatements, Bool.false_eq_true, ↓reduceIte] at hex ⊢
      simp [block_panic p fuel f hex]
  · simp only [↓reduceIte] at hex ⊢
    simp [block_panic p fuel t hex]

theorem if_normal {sp : Span} {c : Expr} {t : Stmt} {els : Option Stmt} {ρ new mod : Eval.Env}
    {b : Bool} {cs : List String} (hc : Eval.eval p fuel ρ c = some (.ok (.bool b)))
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

theorem out_throw {e : IR.Expr} {ρ : Eval.Env} {o : Outcome}
    (h : IR.Body.exec fs fuel ρ (.throw e) = some o) :
    ∃ v, IR.Expr.eval fs fuel ρ e = some v ∧ o = .panic v := by
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
    (∃ x, IR.Body.exec fs fuel ρ br = some (.panic x) ∧ o = .panic x) ∨
    ∃ inner ρ₁, IR.Body.exec fs fuel ρ br = some (.normal inner) ∧
      IR.bindState names inner ρ = some ρ₁ ∧ IR.Body.exec fs fuel ρ₁ rest = some o := by
  simp only [IR.Body.exec] at h
  cases hb : IR.Body.exec fs fuel ρ br with
  | none => simp [hb] at h
  | some r =>
    cases r with
    | ret v => simp [hb] at h
    | panic x => simp [hb] at h; exact .inl ⟨x, rfl, h.symm⟩
    | normal inner =>
      cases hs : IR.bindState names inner ρ with
      | none => simp [hb, hs] at h
      | some ρ₁ => simp [hb, hs] at h; exact .inr ⟨inner, ρ₁, rfl, hs, h⟩

theorem out_pure {a : IR.Expr} {ρ : Eval.Env} :
    IR.Expr.eval fs fuel ρ (IR.Expr.pure a) = IR.Expr.eval fs fuel ρ a := by
  simp only [IR.Expr.eval, IR.Expr.evalList]
  cases IR.Expr.eval fs fuel ρ a <;> rfl

/-- What `f a >>= fun x => rest` does: the call returns `w` and `rest` runs
with `x` bound to it, or the call panics and so does the body. -/
theorem out_bind {x : String} {ref : DeclRef} {args : List IR.Expr} {rest : IR.Body}
    {ρ : Eval.Env} {o : Outcome}
    (h : IR.Body.exec fs fuel ρ (.bind x ref args rest) = some o) :
    ∃ vs, IR.Expr.evalList fs fuel ρ args = some vs ∧
      ((∃ w, callR fs fuel ref vs = some (.ok w) ∧
          IR.Body.exec fs fuel ((x, w) :: ρ) rest = some o) ∨
        (∃ y, callR fs fuel ref vs = some (.error y) ∧ o = .panic y)) := by
  rw [IR.Body.exec] at h
  cases hvs : IR.Expr.evalList fs fuel ρ args with
  | none => simp [hvs] at h
  | some vs =>
    refine ⟨vs, rfl, ?_⟩
    cases fuel with
    | zero => simp [hvs] at h
    | succ fuel =>
      cases hl : fs.lookup ref with
      | none => simp [hvs, hl] at h
      | some x =>
        obtain ⟨ps, b⟩ := x
        by_cases hlen : ps.length = vs.length
        · cases hex : IR.Body.exec fs fuel (ps.zip vs).reverse b with
          | none => simp [hvs, hl, hlen, hex] at h
          | some r =>
            cases r with
            | normal _ => simp [hvs, hl, hlen, hex] at h
            | ret w =>
              simp only [hvs, hl, hlen, hex, Option.bind_eq_bind, Option.bind_some, bne_self_eq_false,
                Bool.false_eq_true, ↓reduceIte] at h
              exact .inl ⟨w, by simp [callR, hl, hlen, hex], by simpa using h⟩
            | panic y =>
              simp [hvs, hl, hlen, hex] at h
              exact .inr ⟨y, by simp [callR, hl, hlen, hex], h.symm⟩
        · simp [hvs, hl, hlen] at h

/-! ### Tests of divisors -/

theorem eqZero_eval {d : IR.Expr} {ρ : Eval.Env} {t : Bool}
    (h : IR.Expr.eval fs fuel ρ (.eq d (.int 0)) = some (.bool t)) :
    ∃ i, IR.Expr.eval fs fuel ρ d = some (.int i) ∧ (t = true ↔ i = 0) := by
  obtain ⟨x, y, r, hx, hy, he, hr⟩ := out_eq h
  simp only [IR.Expr.eval, Option.some.injEq] at hy
  subst hy
  cases hr
  cases x <;> simp [Eval.eqVal] at he
  subst he
  exact ⟨_, hx, by simp⟩

/-- Each value is an integer. -/
def Ints (vs : List Val) : Prop := ∀ d ∈ vs, ∃ i, d = .int i

theorem anyZero_eval {ρ : Eval.Env} :
    ∀ {ds : List IR.Expr} {t : Bool}, ds ≠ [] → IR.Expr.eval fs fuel ρ (anyZero ds) = some (.bool t) →
      ∃ vs, IR.Expr.evalList fs fuel ρ ds = some vs ∧ Ints vs ∧ (t = true ↔ Val.int 0 ∈ vs)
  | [], _, hne, _ => absurd rfl hne
  | [d], t, _, h => by
    simp only [anyZero, isZero, out_decide] at h
    obtain ⟨i, hi, ht⟩ := eqZero_eval fs fuel h
    refine ⟨[.int i], evalList_single hi, by simp [Ints], ?_⟩
    rw [ht]
    simp [eq_comm]
  | d :: d' :: rest, t, _, h => by
    simp only [anyZero] at h
    obtain ⟨x, y, hx, hy, ht⟩ := out_or h
    simp only [isZero, out_decide] at hx
    obtain ⟨i, hi, hxi⟩ := eqZero_eval fs fuel hx
    obtain ⟨vs, hvs, hint, hy'⟩ := anyZero_eval (ds := d' :: rest) (by simp) hy
    refine ⟨.int i :: vs, ?_, ?_, ?_⟩
    · simp [IR.Expr.evalList, hi, hvs]
    · intro d hd
      rcases List.mem_cons.mp hd with rfl | hd
      · exact ⟨i, rfl⟩
      · exact hint d hd
    · injection ht with ht
      subst ht
      rw [List.mem_cons, ← hy', Bool.or_eq_true, hxi]
      simp [eq_comm]

theorem zeroTest_eval {ρ : Eval.Env} {ds : List IR.Expr} {t : Bool} (hne : ds ≠ [])
    (h : IR.Expr.eval fs fuel ρ (zeroTest ds) = some (.bool t)) :
    ∃ vs, IR.Expr.evalList fs fuel ρ ds = some vs ∧ Ints vs ∧ (t = true ↔ Val.int 0 ∈ vs) := by
  match ds, hne, h with
  | [d], _, h =>
    simp only [zeroTest] at h
    obtain ⟨i, hi, ht⟩ := eqZero_eval fs fuel h
    refine ⟨[.int i], evalList_single hi, by simp [Ints], ?_⟩
    rw [ht]
    simp [eq_comm]
  | d :: d' :: rest, hne, h =>
    simp only [zeroTest] at h
    exact anyZero_eval fs fuel hne h

/-- The first check of integers that fails is a zero divisor. -/
theorem firstFault_ints : ∀ {vs : List Val}, Ints vs →
    firstFault vs = if Val.int 0 ∈ vs then some Eval.divideByZero else none
  | [], _ => by simp [firstFault]
  | d :: vs, h => by
    obtain ⟨i, rfl⟩ := h d (by simp)
    have ih := firstFault_ints (vs := vs) fun d hd => h d (by simp [hd])
    by_cases hi : i = 0
    · subst hi; simp [firstFault, fault]
    · have : Val.int i ≠ Val.int 0 := by simpa using hi
      simp [firstFault, fault, hi, ih, eq_comm, this]

/-- The test of one check: whether it fails, and the panic when it does. -/
theorem failTest_eval {ρ : Eval.Env} {k : IR.Expr} {t : Bool}
    (h : IR.Expr.eval fs fuel ρ (failTest k) = some (.bool t)) :
    ∃ w, IR.Expr.eval fs fuel ρ k = some w ∧ (t = false ↔ fault w = none) ∧
      ∀ x, IR.Expr.eval fs fuel ρ (failMessage k) = some x → t = true → fault w = some x := by
  unfold failTest at h
  unfold failMessage
  split at h
  · next hk =>
    simp only [hk, ↓reduceIte]
    obtain ⟨x, y, r, hx, hy, he, hr⟩ := out_ne h
    simp only [IR.Expr.eval, Option.some.injEq] at hy
    subst hy
    injection hr with hr
    subst hr
    cases x <;> simp [Eval.eqVal] at he
    next m =>
    subst he
    refine ⟨_, hx, ?_, fun x hx' ht => ?_⟩
    · by_cases hm : m = "" <;> simp [fault, hm]
    · rw [hx] at hx'
      cases hx'
      by_cases hm : m = "" <;> simp_all [fault]
  · next hk =>
    simp only [hk, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨i, hi, ht⟩ := eqZero_eval fs fuel h
    refine ⟨_, hi, ?_, fun x hx ht' => ?_⟩
    · by_cases h0 : i = 0 <;> cases t <;> simp_all [fault]
    · simp only [panicCode, IR.Expr.eval, Option.some.injEq] at hx
      subst hx
      have := ht.mp ht'
      simp [fault, this, Eval.divideByZero]

/-- What the chain of checks does: it throws the panic of the first check
that fails, after `c` has a value, or every check passes and it runs
`body`. -/
theorem checkChain_cases {ρ : Eval.Env} {c : IR.Expr} {body : IR.Body} {o : Outcome} :
    ∀ {ks : List IR.Expr}, IR.Body.exec fs fuel ρ (checkChain c ks body) = some o →
      (∃ x w, o = .panic x ∧ IR.Expr.eval fs fuel ρ c = some w ∧
        ∀ vs, IR.Expr.evalList fs fuel ρ ks = some vs → firstFault vs = some x) ∨
      (∃ vs, IR.Expr.evalList fs fuel ρ ks = some vs ∧ firstFault vs = none ∧
        IR.Body.exec fs fuel ρ body = some o)
  | [], h => .inr ⟨[], evalList_nil, rfl, h⟩
  | k :: ks, h => by
    simp only [checkChain] at h
    obtain ⟨t, ht, hex⟩ := out_ite fs fuel h
    obtain ⟨w, hw, hpass, hfail⟩ := failTest_eval fs fuel ht
    cases t
    · have hf : fault w = none := hpass.mp rfl
      simp only [Bool.false_eq_true, ↓reduceIte] at hex
      rcases checkChain_cases hex with ⟨x, wc, ho, hc, hall⟩ | ⟨vs, hvs, hnone, hb⟩
      · refine .inl ⟨x, wc, ho, hc, fun vs hvs => ?_⟩
        simp only [IR.Expr.evalList, hw, Option.pure_def, Option.bind_eq_bind, Option.bind_some] at hvs
        cases hks : IR.Expr.evalList fs fuel ρ ks with
        | none => simp [hks] at hvs
        | some us =>
          simp only [hks, Option.bind_some, Option.some.injEq] at hvs
          subst hvs
          simp [firstFault, hf, hall us hks]
      · refine .inr ⟨w :: vs, by simp [IR.Expr.evalList, hw, hvs], by simp [firstFault, hf, hnone], hb⟩
    · simp only [↓reduceIte] at hex
      obtain ⟨m, hm', rfl⟩ := out_throw fs fuel hex
      obtain ⟨wc, m0, hc, hm, happ⟩ := out_ext2 hm'
      simp only [IR.ExprExt.apply, Option.some.injEq] at happ
      subst happ
      have hf := hfail m0 hm rfl
      refine .inl ⟨m0, wc, rfl, hc, fun vs hvs => ?_⟩
      simp only [IR.Expr.evalList, hw, Option.pure_def, Option.bind_eq_bind, Option.bind_some] at hvs
      cases hks : IR.Expr.evalList fs fuel ρ ks with
      | none => simp [hks] at hvs
      | some us =>
        simp only [hks, Option.bind_some, Option.some.injEq] at hvs
        subst hvs
        simp [firstFault, hf]

/-- No check of `c` fails. -/
def NoFault (c : IR.Expr) (ρo : Eval.Env) : Prop :=
  ∀ ds, IR.Expr.evalList fs fuel ρo (divisors c) = some ds → firstFault ds = none

theorem outcome_ok {α : Type} {ds : List Val} (h : firstFault ds = none) (v : α) :
    outcome ds v = .ok v := by
  simp [outcome, h]

theorem outcome_fault {α : Type} {ds : List Val} {x : Val} (h : firstFault ds = some x) (v : α) :
    outcome ds v = .error x := by
  simp [outcome, h]

/-! ### Statement lists -/

def _root_.tolean.Go.Pure.Tail.isRet : Tail → Bool
  | .ret .. => true
  | .state _ => false

/-- The output body `body` means what the statements `ss` mean, from the
environments `ρs` and `ρo`. A return gives the same value, and a panic the
same value. An end, which only a body for a branch has, gives environments
that agree. The interpreter's has new bindings in front, which `env` does not
have, and it changes only the names that `ss` may assign. -/
def SimAt (env : Pure.Env) (tail : Tail) (ss : List Stmt) (body : IR.Body) (ρs ρo : Eval.Env) : Prop :=
  (∀ v, IR.Body.exec fs fuel ρo body = some (.ret v) → Eval.exec p fuel ρs ss = some (.ret v)) ∧
  (∀ ρo', IR.Body.exec fs fuel ρo body = some (.normal ρo') →
    tail.isRet = false ∧ ∃ new mod, Eval.exec p fuel ρs ss = some (.normal (new ++ mod)) ∧
      Agree (new ++ mod) ρo' ∧ (∀ q ∈ new, env.has q.1 = false) ∧ Frame (changesList ss) mod ρs) ∧
  (∀ x, IR.Body.exec fs fuel ρo body = some (.panic x) → Eval.exec p fuel ρs ss = some (.panic x))

/-- The output body `body` means what the statements `ss` mean, from all
environments that agree. -/
def StmtSim (env : Pure.Env) (tail : Tail) (ss : List Stmt) (body : IR.Body) : Prop :=
  ∀ (ρs ρo : Eval.Env), Agree ρs ρo → Scoped env ρs → SimAt p fs fuel env tail ss body ρs ρo

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
in `env`, means what the source means, when the rest does, from the output
environments where `P` holds. -/
theorem push_sim {P : Eval.Env → Prop} {env : Pure.Env} {st : Stmt} {rest : List Stmt} {tail : Tail}
    {body rb : IR.Body} {x : String} {ty : Ty} (hfresh : env.has x = false)
    (hbody : ∀ (ρo : Eval.Env) (o : Outcome), P ρo → IR.Body.exec fs fuel ρo body = some o → (∃ w,
      (∀ ρs, Agree ρs ρo → Scoped env ρs → Eval.execStmt p fuel ρs st = some (.normal ((x, w) :: ρs))) ∧
        IR.Body.exec fs fuel ((x, w) :: ρo) rb = some o) ∨
      ∃ y, o = .panic y ∧
        ∀ ρs, Agree ρs ρo → Scoped env ρs → Eval.execStmt p fuel ρs st = some (.panic y))
    (hrest : StmtSim p fs fuel (env ++ [Local.mk x ty]) tail rest rb) :
    ∀ ρs ρo, Agree ρs ρo → Scoped env ρs → P ρo → SimAt p fs fuel env tail (st :: rest) body ρs ρo := by
  intro ρs ρo ha hs hP
  refine ⟨fun v hv => ?_, fun ρo' hv => ?_, fun y hv => ?_⟩
  · obtain ⟨w, hw, hb⟩ | ⟨_, hy, -⟩ := hbody ρo _ hP hv
    rotate_left
    · cases hy
    rw [exec_cons_normal p fuel (hw ρs ha hs)]
    exact (hrest _ _ (agree_cons ha x w) (scoped_cons hs x ty w)).1 v hb
  · obtain ⟨w, hw, hb⟩ | ⟨_, hy, -⟩ := hbody ρo _ hP hv
    rotate_left
    · cases hy
    obtain ⟨htail, new, mod, hex, hag, hnew, hfr⟩ :=
      (hrest _ _ (agree_cons ha x w) (scoped_cons hs x ty w)).2.1 ρo' hb
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
  · obtain ⟨w, hw, hb⟩ | ⟨_, hy, hst⟩ := hbody ρo _ hP hv
    rotate_left
    · cases hy; exact exec_cons_panic p fuel (hst ρs ha hs)
    rw [exec_cons_normal p fuel (hw ρs ha hs)]
    exact (hrest _ _ (agree_cons ha x w) (scoped_cons hs x ty w)).2.2 y hb

/-- A statement that gives the local `x` the value `w`, where `x` is in
scope, means what the source means, when the rest does, from the output
environments where `P` holds. -/
theorem set_sim {P : Eval.Env → Prop} {env : Pure.Env} {st : Stmt} {rest : List Stmt} {tail : Tail}
    {body rb : IR.Body} {x : String} (hx : env.has x = true) (hch : x ∈ stmtChanges st)
    (hbody : ∀ (ρo : Eval.Env) (o : Outcome), P ρo → IR.Body.exec fs fuel ρo body = some o → (∃ w,
      (∀ ρs, Agree ρs ρo → Scoped env ρs → Eval.execStmt p fuel ρs st = some (.normal (ρs.set x w))) ∧
        IR.Body.exec fs fuel ((x, w) :: ρo) rb = some o) ∨
      ∃ y, o = .panic y ∧
        ∀ ρs, Agree ρs ρo → Scoped env ρs → Eval.execStmt p fuel ρs st = some (.panic y))
    (hrest : StmtSim p fs fuel env tail rest rb) :
    ∀ ρs ρo, Agree ρs ρo → Scoped env ρs → P ρo → SimAt p fs fuel env tail (st :: rest) body ρs ρo := by
  intro ρs ρo ha hs hP
  have hsome : (ρs.lookup x).isSome := by rw [hs x]; exact hx
  have hset : ∀ w : Val, Frame [x] (ρs.set x w) ρs := fun w => Frame.set (by simp) ρs
  have hs' : ∀ w : Val, Scoped env (ρs.set x w) := fun w n => ((hset w).isSome n).trans (hs n)
  refine ⟨fun v hv => ?_, fun ρo' hv => ?_, fun y hv => ?_⟩
  · obtain ⟨w, hw, hb⟩ | ⟨_, hy, -⟩ := hbody ρo _ hP hv
    rotate_left
    · cases hy
    rw [exec_cons_normal p fuel (hw ρs ha hs)]
    exact (hrest _ _ (agree_set ha hsome) (hs' w)).1 v hb
  · obtain ⟨w, hw, hb⟩ | ⟨_, hy, -⟩ := hbody ρo _ hP hv
    rotate_left
    · cases hy
    obtain ⟨htail, new, mod, hex, hag, hnew, hfr⟩ := (hrest _ _ (agree_set ha hsome) (hs' w)).2.1 ρo' hb
    refine ⟨htail, new, mod, ?_, hag, hnew, ?_⟩
    · rw [exec_cons_normal p fuel (hw ρs ha hs)]; exact hex
    · exact (hfr.trans (hset w)).mono fun n hn => by
        simp only [List.mem_append, List.mem_singleton] at hn
        rcases hn with rfl | hn
        · simp [changesList, hch]
        · simp [changesList, hn]
  · obtain ⟨w, hw, hb⟩ | ⟨_, hy, hst⟩ := hbody ρo _ hP hv
    rotate_left
    · cases hy; exact exec_cons_panic p fuel (hst ρs ha hs)
    rw [exec_cons_normal p fuel (hw ρs ha hs)]
    exact (hrest _ _ (agree_set ha hsome) (hs' w)).2.2 y hb

/-- What the output of a guarded statement does: it panics, as the source's
statement does, or no check fails and it runs `body`. -/
theorem guarded_cases {env : Pure.Env} {c : IR.Expr} {st : Stmt} {body : IR.Body}
    {ρs ρo : Eval.Env} (ha : Agree ρs ρo) (hs : Scoped env ρs)
    (hz : ∀ ρs ρo v, Agree ρs ρo → Scoped env ρs → IR.Expr.eval fs fuel ρo c = some v →
      ∃ ds, IR.Expr.evalList fs fuel ρo (divisors c) = some ds ∧
        (∀ x, firstFault ds = some x → Eval.execStmt p fuel ρs st = some (.panic x)))
    {o : Outcome} (h : IR.Body.exec fs fuel ρo (guarded c body) = some o) :
    (∃ x, o = .panic x ∧ Eval.execStmt p fuel ρs st = some (.panic x)) ∨
      (NoFault fs fuel c ρo ∧ IR.Body.exec fs fuel ρo body = some o) := by
  unfold guarded at h
  split at h
  · next hd =>
    refine .inr ⟨fun ds hds => ?_, h⟩
    rw [List.isEmpty_iff.mp hd, evalList_nil] at hds
    cases hds
    rfl
  · split at h
    · rcases checkChain_cases fs fuel h with ⟨x, w, rfl, hw, hall⟩ | ⟨vs, hvs, hnone, hb⟩
      · obtain ⟨ds, hds, hpanic⟩ := hz ρs ρo w ha hs hw
        exact .inl ⟨x, rfl, hpanic x (hall ds hds)⟩
      · refine .inr ⟨fun ds hds => ?_, hb⟩
        rw [hvs] at hds
        cases hds
        exact hnone
    · next hd _ =>
      have hne : divisors c ≠ [] := fun h' => hd (by simp [h'])
      obtain ⟨t, ht, hex⟩ := out_ite fs fuel h
      obtain ⟨vs, hvs, hint, htv⟩ := zeroTest_eval fs fuel hne ht
      have hff := firstFault_ints hint
      cases t
      · refine .inr ⟨fun ds hds => ?_, by simpa using hex⟩
        rw [hvs] at hds
        cases hds
        have hm : Val.int 0 ∉ vs := fun hm => absurd (htv.mpr hm) (by simp)
        simp [hff, hm]
      · left
        simp only [↓reduceIte] at hex
        obtain ⟨w, hw, hthrow⟩ := out_let fs fuel hex
        obtain ⟨m, hm, rfl⟩ := out_throw fs fuel hthrow
        simp only [panicCode, IR.Expr.eval, Option.some.injEq] at hm
        subst hm
        obtain ⟨ds, hds, hpanic⟩ := hz ρs ρo w ha hs hw
        rw [hvs] at hds
        cases hds
        refine ⟨_, rfl, hpanic _ ?_⟩
        simp [hff, htv.mp rfl, Eval.divideByZero]

/-- A statement whose checks the output tests means what the source means,
when the body after the test does from the environments where no check
fails. -/
theorem guarded_sim {env : Pure.Env} {tail : Tail} {c : IR.Expr} {st : Stmt} {rest : List Stmt}
    {body : IR.Body}
    (hz : ∀ ρs ρo v, Agree ρs ρo → Scoped env ρs → IR.Expr.eval fs fuel ρo c = some v →
      ∃ ds, IR.Expr.evalList fs fuel ρo (divisors c) = some ds ∧
        (∀ x, firstFault ds = some x → Eval.execStmt p fuel ρs st = some (.panic x)))
    (hb : ∀ ρs ρo, Agree ρs ρo → Scoped env ρs → NoFault fs fuel c ρo →
      SimAt p fs fuel env tail (st :: rest) body ρs ρo) :
    StmtSim p fs fuel env tail (st :: rest) (guarded c body) := by
  intro ρs ρo ha hs
  refine ⟨fun v hv => ?_, fun ρo' hv => ?_, fun y hv => ?_⟩
  · rcases guarded_cases p fs fuel ha hs hz hv with ⟨_, h, -⟩ | ⟨hn, hex⟩
    · cases h
    · exact (hb ρs ρo ha hs hn).1 v hex
  · rcases guarded_cases p fs fuel ha hs hz hv with ⟨_, h, -⟩ | ⟨hn, hex⟩
    · cases h
    · exact (hb ρs ρo ha hs hn).2.1 ρo' hex
  · rcases guarded_cases p fs fuel ha hs hz hv with ⟨x, h, hst⟩ | ⟨hn, hex⟩
    · cases h
      exact exec_cons_panic p fuel hst
    · exact (hb ρs ρo ha hs hn).2.2 y hex

/-- A statement that the interpreter runs as `b`, and that may assign what `b`
assigns, means what `b` means. -/
theorem sim_congr {env : Pure.Env} {tail : Tail} {a b : Stmt} {rest : List Stmt} {body : IR.Body}
    (h : ∀ ρ, Eval.execStmt p fuel ρ a = Eval.execStmt p fuel ρ b)
    (hch : ∀ k, k ∈ stmtChanges b → k ∈ stmtChanges a)
    (hs : StmtSim p fs fuel env tail (b :: rest) body) : StmtSim p fs fuel env tail (a :: rest) body := by
  intro ρs ρo ha hsc
  obtain ⟨h1, h2, h3⟩ := hs ρs ρo ha hsc
  rw [← exec_cons_congr p fuel h rest ρs] at h1 h2 h3
  refine ⟨h1, fun ρo' hv => ?_, h3⟩
  obtain ⟨ht, new, mod, hex, hag, hnew, hfr⟩ := h2 ρo' hv
  refine ⟨ht, new, mod, hex, hag, hnew, hfr.mono fun k hk => ?_⟩
  simp only [changesList, List.mem_append] at hk ⊢
  exact hk.imp_left (hch k)

/-- The changes of a switch's chain are those of its clauses. -/
theorem chain_changes {tag : Option Expr} {k : String} :
    ∀ (cs : List CaseClause) (dflt : Option (Span × List Stmt)) (d : Stmt),
      switchChain tag dflt cs = some d → k ∈ stmtChanges d →
        k ∈ changesClauses cs ∨ ∃ sp body, dflt = some (sp, body) ∧ k ∈ changesList body
  | [], none, d, h, _ => by simp [switchChain] at h
  | [], some (sp, body), d, h, hk => by
    simp only [switchChain, Option.some.injEq] at h
    subst h
    exact .inr ⟨sp, body, rfl, by simpa [stmtChanges] using hk⟩
  | .mk sp none body :: rest, dflt, d, h, hk => by
    simp only [switchChain] at h
    rcases chain_changes rest _ d h hk with hk | ⟨sp', body', he, hk⟩
    · exact .inl (by simp [changesClauses, hk])
    · simp only [Option.some.injEq, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact .inl (by simp [changesClauses, hk])
  | .mk sp (some es) body :: rest, dflt, d, h, hk => by
    simp only [switchChain] at h
    cases hc : caseCond sp tag es with
    | none =>
      simp only [hc] at h
      rcases chain_changes rest _ d h hk with hk | hk
      · exact .inl (by simp [changesClauses, hk])
      · exact .inr hk
    | some c =>
      simp only [hc, Option.some.injEq] at h
      subst h
      simp only [stmtChanges, changesOption, List.nil_append, List.mem_append] at hk
      rcases hk with hk | hk
      · exact .inl (by simp [changesClauses, hk])
      · cases hf : switchChain tag dflt rest with
        | none => simp [hf, changesOption] at hk
        | some f =>
          simp only [hf, changesOption] at hk
          rcases chain_changes rest _ f hf hk with hk | hk
          · exact .inl (by simp [changesClauses, hk])
          · exact .inr hk

/-- A block that does not return means what its statements mean, and then
what the rest means, with the locals that it changes. -/
theorem block_state_sim {env : Pure.Env} {tail : Tail} {sp : Span} {body rest : List Stmt}
    {inner rb : IR.Body}
    (simB : StmtSim p fs fuel env (.state (changedNames body env)) body inner)
    (simR : StmtSim p fs fuel env tail rest rb) :
    StmtSim p fs fuel env tail (.block sp body :: rest) (.letState (changedNames body env) inner rb) := by
  intro ρs ρo ha hs
  have key : ∀ o, IR.Body.exec fs fuel ρo (.letState (changedNames body env) inner rb) = some o →
      (∃ x, o = .panic x ∧ Eval.execStmt p fuel ρs (.block sp body) = some (.panic x)) ∨
      ∃ mod ρ₁, Eval.execStmt p fuel ρs (.block sp body) = some (.normal mod) ∧
        Agree mod ρ₁ ∧ Scoped env mod ∧ Frame (stmtChanges (.block sp body)) mod ρs ∧
        IR.Body.exec fs fuel ρ₁ rb = some o := by
    intro o hv
    rcases out_letState fs fuel hv with ⟨x, hbr, rfl⟩ | ⟨inner', ρ₁, hbr, hbind, hrest⟩
    · refine .inl ⟨x, rfl, ?_⟩
      rw [execStmt_block, (simB ρs ρo ha hs).2.2 x hbr]; rfl
    right
    obtain ⟨-, new, mod, hexs, hag, hnew, hfr⟩ := (simB ρs ρo ha hs).2.1 inner' hbr
    have hlen := hfr.length
    refine ⟨mod, ρ₁, by rw [execStmt_block, hexs]; simp [hlen], ?_, ?_, ?_, hrest⟩
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
        by_cases hkc : k ∈ changesList body
        · have hkenv : env.has k = false := by
            cases h' : env.has k
            · rfl
            · exact absurd (mem_changedNames.mpr ⟨h', hkc⟩) hk
          have h1 := scoped_none hs hkenv
          have h2 := hfr.isSome k
          rw [h1] at h2 ⊢
          simpa using h2
        · exact hfr.lookup hkc
    · exact fun k => (hfr.isSome k).trans (hs k)
    · simpa [stmtChanges] using hfr
  refine ⟨fun v hv => ?_, fun ρo' hv => ?_, fun y hv => ?_⟩
  · rcases key _ hv with ⟨x, hx, -⟩ | ⟨mod, ρ₁, hb, ha', hs', -, hrest⟩
    · cases hx
    rw [exec_cons_normal p fuel hb]
    exact (simR mod ρ₁ ha' hs').1 v hrest
  · rcases key _ hv with ⟨x, hx, -⟩ | ⟨mod, ρ₁, hb, ha', hs', hfr, hrest⟩
    · cases hx
    obtain ⟨htail, new', mod', hex', hag', hnew', hfr'⟩ := (simR mod ρ₁ ha' hs').2.1 ρo' hrest
    refine ⟨htail, new', mod', by rw [exec_cons_normal p fuel hb]; exact hex', hag', hnew', ?_⟩
    simpa [changesList] using hfr'.trans hfr
  · rcases key _ hv with ⟨x, hx, hb⟩ | ⟨mod, ρ₁, hb, ha', hs', -, hrest⟩
    · cases hx
      exact exec_cons_panic p fuel hb
    rw [exec_cons_normal p fuel hb]
    exact (simR mod ρ₁ ha' hs').2.2 y hrest

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

theorem zero_basic {u : String} {t : Ty} (ht : basicType u = some t) {ρ : Eval.Env} {w : Val}
    (hw : IR.Expr.eval fs fuel ρ (zeroCode t) = some w) : Eval.zeroOfBasic u = some w := by
  unfold basicType at ht
  split at ht <;> simp only [Option.some.injEq, reduceCtorEq] at ht <;> subst ht <;>
    simp only [zeroCode, IR.Expr.eval, Option.some.injEq] at hw <;> subst hw <;> rfl

theorem zero_sound {ctx : Ctx} (hp : ctx.program = p) {te : Expr} {t : Ty}
    (ht : resolveType ctx te = some t) {ρ : Eval.Env} {w : Val}
    (hw : IR.Expr.eval fs fuel ρ (zeroCode t) = some w) : Eval.zeroOf p te = some w := by
  cases te with
  | ident sp name =>
    subst hp
    simp only [resolveType] at ht
    simp only [Eval.zeroOf]
    cases hl : ctx.program.types.lookup name with
    | some u =>
      simp only [hl] at ht
      exact zero_basic (fs := fs) (fuel := fuel) ht hw
    | none =>
      simp only [hl] at ht
      split at ht
      · simp at ht
      · next hn =>
        simp only [hn, Bool.false_eq_true, ↓reduceIte]
        have := zero_basic (fs := fs) (fuel := fuel) ht hw
        unfold Eval.zeroOfBasic at this
        split at this <;> simp_all
  | _ => simp [resolveType] at ht

theorem guarded_zeroCode (t : Ty) (b : IR.Body) : guarded (zeroCode t) b = b := by
  cases t <;> simp [guarded, zeroCode, divisors]

/-- The source's expression has the value of its code when no divisor of the
code is zero. -/
theorem expr_ok {ctx : Ctx} (hp : ctx.program = p) (hc : CallsAgree p fs fuel) {n : Nat}
    {env : Pure.Env} {e : Expr} {c : IR.Expr} {t : Ty} (h : translateExpr ctx env n e = .ok (c, t))
    {ρs ρo : Eval.Env} {v : Val} (ha : Agree ρs ρo) (hs : Scoped env ρs)
    (hv : IR.Expr.eval fs fuel ρo c = some v) (hn : NoFault fs fuel c ρo) :
    Eval.eval p fuel ρs e = some (.ok v) := by
  obtain ⟨ds, hds, -, he⟩ := expr_sound fs fuel p hp hc h ha hs hv
  rw [he, outcome_ok (hn ds hds)]

/-- The source's expression panics when a check of its code fails. -/
theorem expr_zero {ctx : Ctx} (hp : ctx.program = p) (hc : CallsAgree p fs fuel) {n : Nat}
    {env : Pure.Env} {e : Expr} {c : IR.Expr} {t : Ty} (h : translateExpr ctx env n e = .ok (c, t))
    {ρs ρo : Eval.Env} {v : Val} (ha : Agree ρs ρo) (hs : Scoped env ρs)
    (hv : IR.Expr.eval fs fuel ρo c = some v) :
    ∃ ds, IR.Expr.evalList fs fuel ρo (divisors c) = some ds ∧
      (∀ x, firstFault ds = some x → Eval.eval p fuel ρs e = some (.error x)) := by
  obtain ⟨ds, hds, -, he⟩ := expr_sound fs fuel p hp hc h ha hs hv
  exact ⟨ds, hds, fun x hm => by rw [he, outcome_fault hm]⟩

theorem compound_strict {op : String} {o : BinOp} (hk : AssignKind.ofString? op = some (.compound o)) :
    o ≠ .land ∧ o ≠ .lor := by
  unfold AssignKind.ofString? at hk
  split at hk <;> simp only [Option.some.injEq, reduceCtorEq, AssignKind.compound.injEq] at hk <;>
    subst hk <;> decide

theorem incDec_strict {op : String} {o : BinOp} (ho : Eval.incDecOp? op = some o) :
    o ≠ .land ∧ o ≠ .lor ∧ o ≠ .quo ∧ o ≠ .rem := by
  unfold Eval.incDecOp? at ho
  split at ho <;> simp only [Option.some.injEq, reduceCtorEq] at ho <;> subst ho <;> decide

/-! ### Calls that can panic -/

theorem panicCallee_some {ctx : Ctx} {env : Pure.Env} {e : Expr} {f : String} {args : List Expr}
    {sig : FnSig} (h : panicCallee? ctx env e = some (f, args, sig)) :
    env.has f = false ∧ Eval.builtin ctx.program f = none ∧
      ∃ csp fsp, e = .call csp (.ident fsp f) args false := by
  unfold panicCallee? at h
  split at h
  · next csp fsp g args' =>
    split at h
    · simp at h
    · next hg =>
      split at h
      · split at h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, -⟩ := h
          simp only [Bool.or_eq_true, Option.isSome_iff_ne_none, not_or, ne_eq,
            Decidable.not_not] at hg
          exact ⟨by simpa using hg.1, hg.2, csp, fsp, rfl⟩
        · simp at h
      · simp at h
  · simp at h

/-- The statement forms that `bindCall?` finds, with the call `e`. -/
inductive BindShape : BindForm → Span → Expr → Stmt → Prop where
  | ret {sp e} : BindShape .ret sp e (.ret sp [e])
  | define {sp e xsp x} : BindShape (.define x) sp e (.assign sp ":=" [.ident xsp x] [e])
  | assign {sp e xsp x} : BindShape (.assign x) sp e (.assign sp "=" [.ident xsp x] [e])
  | var {sp e a b x te} :
    BindShape (.var x te) sp e (.decl sp (.mk a "var" [.value b [x] (some te) [e]]))

theorem bindCall_some {ctx : Ctx} {env : Pure.Env} {st : Stmt} {form : BindForm} {sp : Span}
    {f : String} {args : List Expr} {sig : FnSig}
    (h : bindCall? ctx env st = some (form, sp, f, args, sig)) :
    ∃ e, panicCallee? ctx env e = some (f, args, sig) ∧ BindShape form sp e st := by
  unfold bindCall? at h
  split at h
  all_goals first
    | (simp at h; done)
    | (obtain ⟨⟨f', args', sig'⟩, hc, he⟩ := Option.map_eq_some_iff.mp h
       simp only [Prod.mk.injEq] at he
       obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := he
       first
         | exact ⟨_, hc, .ret⟩
         | exact ⟨_, hc, .define⟩
         | exact ⟨_, hc, .assign⟩
         | exact ⟨_, hc, .var⟩)

/-- The source's call of a function that can panic: its arguments, then the
call. -/
theorem eval_panicCall {ctx : Ctx} {env : Pure.Env} {e : Expr} {f : String} {args : List Expr}
    {sig : FnSig} (hp : ctx.program = p) (h : panicCallee? ctx env e = some (f, args, sig))
    {ρs : Eval.Env} (hs : Scoped env ρs) :
    Eval.eval p fuel ρs e = (Eval.evalList p fuel ρs args).andThen (callS p fuel f) := by
  obtain ⟨hf, hb, csp, fsp, rfl⟩ := panicCallee_some h
  rw [hp] at hb
  simp [eval_call p fuel ρs csp fsp f args hb, scoped_none hs hf]

/-- The arguments of a call of a function that can panic: the source's
evaluate to the code's values, or panic when a divisor is zero. -/
theorem panicArgs {ctx : Ctx} (hp : ctx.program = p) (hc : CallsAgree p fs fuel)
    {env : Pure.Env} {e : Expr} {f : String} {args : List Expr} {sig : FnSig}
    {codes : List (IR.Expr × Ty)} (hcall : panicCallee? ctx env e = some (f, args, sig))
    (hargs : translateArgs ctx env exprFuel args = .ok codes) {ρs ρo : Eval.Env} {vs : List Val}
    (ha : Agree ρs ρo) (hs : Scoped env ρs)
    (hvs : IR.Expr.evalList fs fuel ρo (codes.map (·.1)) = some vs) :
    ∃ ds, IR.Expr.evalList fs fuel ρo (divisors (.call ⟨"", f⟩ (codes.map (·.1)))) = some ds ∧
      Eval.eval p fuel ρs e = tolean.Core.Res.andThen (some (outcome ds vs)) (callS p fuel f) := by
  obtain ⟨ds, hds, -, hev⟩ := (expr_sound_aux fs fuel p hp hc exprFuel).2 env args codes hargs
    ρs ρo vs ha hs hvs
  exact ⟨ds, by simpa [divisors] using hds, by rw [eval_panicCall p fuel hp hcall hs, hev]⟩

/-- The source's call panics when a check of an argument's code fails. -/
theorem call_zero {ctx : Ctx} (hp : ctx.program = p) (hc : CallsAgree p fs fuel)
    {env : Pure.Env} {e : Expr} {f : String} {args : List Expr} {sig : FnSig}
    {codes : List (IR.Expr × Ty)} (hcall : panicCallee? ctx env e = some (f, args, sig))
    (hargs : translateArgs ctx env exprFuel args = .ok codes) {ρs ρo : Eval.Env} {v : Val}
    (ha : Agree ρs ρo) (hs : Scoped env ρs)
    (hv : IR.Expr.eval fs fuel ρo (.ext .args (codes.map (·.1))) = some v) :
    ∃ ds, IR.Expr.evalList fs fuel ρo (divisors (.ext .args (codes.map (·.1)))) = some ds ∧
      (∀ x, firstFault ds = some x → Eval.eval p fuel ρs e = some (.error x)) := by
  simp only [IR.Expr.eval] at hv
  cases hvs : IR.Expr.evalList fs fuel ρo (codes.map (·.1)) with
  | none => simp [hvs] at hv
  | some vs =>
    obtain ⟨ds, hds, hev⟩ := panicArgs p fs fuel hp hc hcall hargs ha hs hvs
    exact ⟨ds, by simpa [divisors] using hds, fun x hm => by rw [hev, outcome_fault hm]; rfl⟩

/-- `f a >>= fun x => rest`, when no divisor of the arguments is zero: the
source's call returns the value that `rest` runs with, or panics as the
output does. -/
theorem call_bind {ctx : Ctx} (hp : ctx.program = p) (hc : CallsAgree p fs fuel)
    {env : Pure.Env} {e : Expr} {f : String} {args : List Expr} {sig : FnSig}
    {codes : List (IR.Expr × Ty)} (hcall : panicCallee? ctx env e = some (f, args, sig))
    (hargs : translateArgs ctx env exprFuel args = .ok codes) {ρo : Eval.Env}
    (hn : NoFault fs fuel (.ext .args (codes.map (·.1))) ρo) {x : String} {rb : IR.Body}
    {o : Outcome} (hv : IR.Body.exec fs fuel ρo (.bind x ⟨"", f⟩ (codes.map (·.1)) rb) = some o) :
    (∃ w, (∀ ρs, Agree ρs ρo → Scoped env ρs → Eval.eval p fuel ρs e = some (.ok w)) ∧
        IR.Body.exec fs fuel ((x, w) :: ρo) rb = some o) ∨
      (∃ y, o = .panic y ∧
        ∀ ρs, Agree ρs ρo → Scoped env ρs → Eval.eval p fuel ρs e = some (.error y)) := by
  obtain ⟨vs, hvs, hr⟩ := out_bind fs fuel hv
  have hev : ∀ ρs, Agree ρs ρo → Scoped env ρs → Eval.eval p fuel ρs e = callS p fuel f vs := by
    intro ρs ha hs
    obtain ⟨ds, hds, hev⟩ := panicArgs p fs fuel hp hc hcall hargs ha hs hvs
    rw [hev, outcome_ok (hn ds (by simpa [divisors] using hds))]; rfl
  rcases hr with ⟨w, hw, hb⟩ | ⟨y, hy, rfl⟩
  · exact .inl ⟨w, fun ρs ha hs => by rw [hev ρs ha hs]; exact hc f vs _ hw, hb⟩
  · exact .inr ⟨y, rfl, fun ρs ha hs => by rw [hev ρs ha hs]; exact hc f vs _ hy⟩

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
        | ret r m => simp [translateStmts] at h
        | state names =>
          simp only [translateStmts, pure_ok] at h
          subst h
          intro ρs ρo ha hs
          refine ⟨fun v hv => by simp [IR.Body.exec] at hv, fun ρo' hv => ?_,
            fun y hv => by simp [IR.Body.exec] at hv⟩
          simp only [IR.Body.exec, Option.some.injEq, Outcome.normal.injEq] at hv
          subst hv
          exact ⟨rfl, [], ρs, exec_nil p fuel ρs, ha, by simp, Frame.refl _ ρs⟩
      | cons st rest =>
        rw [translateStmts.eq_def] at h
        simp only at h
        split at h
        -- A call of a function that can panic, bound with `>>=`.
        · next form sp f args sig hbind =>
          obtain ⟨e, hcall, hshape⟩ := bindCall_some hbind
          rw [bind_ok] at h
          obtain ⟨codes, hargs, h⟩ := h
          have hz : ∀ (st : Stmt), (∀ ρs x, Eval.eval p fuel ρs e = some (.error x) →
              Eval.execStmt p fuel ρs st = some (.panic x)) →
              ∀ ρs ρo v, Agree ρs ρo → Scoped env ρs →
                IR.Expr.eval fs fuel ρo (.ext .args (codes.map (·.1))) = some v →
                ∃ ds, IR.Expr.evalList fs fuel ρo (divisors (.ext .args (codes.map (·.1)))) =
                  some ds ∧ (∀ x, firstFault ds = some x → Eval.execStmt p fuel ρs st =
                    some (.panic x)) := by
            intro st hst ρs ρo v ha hs hv
            obtain ⟨ds, hds, hzero⟩ := call_zero p fs fuel hp hc hcall hargs ha hs hv
            exact ⟨ds, hds, fun x hm => hst ρs x (hzero x hm)⟩
          cases hshape with
          | ret =>
            cases tail with
            | state names => tm_simp at h
            | ret result monadic =>
              cases rest with
              | cons _ _ => split at h <;> simp [reject, throw, throwThe, MonadExceptOf.throw, pure, Except.pure] at h
              | nil =>
                tm_simp at h
                obtain ⟨-, -, rfl⟩ := h
                refine guarded_sim p fs fuel
                  (hz _ fun ρs _ he => by rw [Eval.execStmt, he]; rfl) (fun ρs ρo ha hs hn => ?_)
                have hval : ∀ w o, IR.Body.exec fs fuel ((resultName, w) :: ρo)
                    (.value (if monadic then IR.Expr.pure (.var resultName) else .var resultName)) =
                      some o → o = .ret w := by
                  intro w o hv
                  obtain ⟨u, hu, rfl⟩ := out_value fs fuel hv
                  cases monadic <;> simp [out_pure, IR.Expr.eval] at hu <;> rw [hu]
                refine ⟨fun v hv => ?_, fun ρo' hv => ?_, fun y hv => ?_⟩
                · rcases call_bind p fs fuel hp hc hcall hargs hn hv with ⟨w, he, hb⟩ | ⟨y, hy, -⟩
                  · cases hval w _ hb
                    rw [exec_single, Eval.execStmt, he ρs ha hs]; rfl
                  · cases hy
                · rcases call_bind p fs fuel hp hc hcall hargs hn hv with ⟨w, -, hb⟩ | ⟨y, hy, -⟩
                  · cases hval w _ hb
                  · cases hy
                · rcases call_bind p fs fuel hp hc hcall hargs hn hv with ⟨w, -, hb⟩ | ⟨y', hy, he⟩
                  · cases hval w _ hb
                  · cases hy
                    rw [exec_single, Eval.execStmt, he ρs ha hs]; rfl
          | define =>
            tm_simp at h
            obtain ⟨-, env', hdecl, rb, hrb, rfl⟩ := h
            obtain ⟨hfresh, rfl⟩ := declare_ok hdecl
            refine guarded_sim p fs fuel
              (hz _ fun ρs _ he => by rw [Eval.execStmt]; simp [AssignKind.ofString?, he])
              (push_sim p fs fuel hfresh (fun ρo o hn hv => ?_) (ihs _ tail rest rb hrb))
            rcases call_bind p fs fuel hp hc hcall hargs hn hv with ⟨w, he, hb⟩ | ⟨y, hy, he⟩
            · exact .inl ⟨w, fun ρs ha hs => by
                rw [Eval.execStmt]; simp [AssignKind.ofString?, he ρs ha hs], hb⟩
            · exact .inr ⟨y, hy, fun ρs ha hs => by
                rw [Eval.execStmt]; simp [AssignKind.ofString?, he ρs ha hs]⟩
          | @assign _ _ _ x =>
            cases hl : env.lookup x with
            | none => simp only [hl] at h; tm_simp at h
            | some l =>
              simp only [hl] at h
              tm_simp at h
              obtain ⟨-, -, rb, hrb, rfl⟩ := h
              have hold : ∀ ρs, Scoped env ρs → ∃ old, ρs.lookup x = some old := fun ρs hs =>
                Option.isSome_iff_exists.mp (by rw [hs x]; exact env_has_of_lookup hl)
              refine guarded_sim p fs fuel
                (hz _ fun ρs _ he => by rw [Eval.execStmt]; simp [AssignKind.ofString?, he])
                (set_sim p fs fuel (env_has_of_lookup hl) (by simp [stmtChanges])
                  (fun ρo o hn hv => ?_) (ihs _ tail rest rb hrb))
              rcases call_bind p fs fuel hp hc hcall hargs hn hv with ⟨w, he, hb⟩ | ⟨y, hy, he⟩
              · refine .inl ⟨w, fun ρs ha hs => ?_, hb⟩
                obtain ⟨old, hold⟩ := hold ρs hs
                rw [Eval.execStmt]; simp [AssignKind.ofString?, he ρs ha hs, hold]
              · exact .inr ⟨y, hy, fun ρs ha hs => by
                  rw [Eval.execStmt]; simp [AssignKind.ofString?, he ρs ha hs]⟩
          | @var _ _ _ _ x te =>
            cases ht : resolveType ctx te with
            | none => simp only [ht] at h; tm_simp at h
            | some ty =>
              simp only [ht] at h
              tm_simp at h
              obtain ⟨-, -, env', hdecl, rb, hrb, rfl⟩ := h
              obtain ⟨hfresh, rfl⟩ := declare_ok hdecl
              refine guarded_sim p fs fuel
                (hz _ fun ρs _ he => by rw [Eval.execStmt]; simp [he])
                (push_sim p fs fuel hfresh (fun ρo o hn hv => ?_) (ihs _ tail rest rb hrb))
              rcases call_bind p fs fuel hp hc hcall hargs hn hv with ⟨w, he, hb⟩ | ⟨y, hy, he⟩
              · exact .inl ⟨w, fun ρs ha hs => by rw [Eval.execStmt]; simp [he ρs ha hs], hb⟩
              · exact .inr ⟨y, hy, fun ρs ha hs => by rw [Eval.execStmt]; simp [he ρs ha hs]⟩
        · next hbind =>
          split at h
          -- `return e`
          · next sp e =>
            cases tail with
            | state names => simp [reject, throw, throwThe, MonadExceptOf.throw] at h
            | ret result monadic =>
              cases rest with
              | cons _ _ => simp [reject, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
              | nil =>
                tm_simp at h
                obtain ⟨⟨ce, te⟩, hce, -, rfl⟩ := h
                refine guarded_sim p fs fuel (fun ρs ρo v ha hs hv => ?_) (fun ρs ρo ha hs hn => ?_)
                · obtain ⟨ds, hds, hz⟩ := expr_zero p fs fuel hp hc hce ha hs hv
                  exact ⟨ds, hds, fun x hm => by rw [Eval.execStmt, hz x hm]; rfl⟩
                have hval : ∀ o, IR.Body.exec fs fuel ρo
                    (.value (if monadic then IR.Expr.pure ce else ce)) = some o →
                    ∃ w, IR.Expr.eval fs fuel ρo ce = some w ∧ o = .ret w := by
                  intro o hv
                  obtain ⟨w, hw, hwv⟩ := out_value fs fuel hv
                  refine ⟨w, ?_, hwv⟩
                  cases monadic
                  · simpa using hw
                  · simpa [out_pure] using hw
                refine ⟨fun v hv => ?_, fun ρo' hv => ?_, fun y hv => ?_⟩
                · obtain ⟨w, hw, hwv⟩ := hval _ hv
                  cases hwv
                  have he := expr_ok p fs fuel hp hc hce ha hs hw hn
                  rw [exec_single, Eval.execStmt, he]; rfl
                · obtain ⟨w, -, hwv⟩ := hval _ hv
                  cases hwv
                · obtain ⟨w, -, hwv⟩ := hval _ hv
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
                refine guarded_sim p fs fuel (fun ρs ρo v ha hs hv => ?_)
                  (push_sim p fs fuel hfresh (fun ρo o hn hv => ?_) (ihs _ tail rest rb hrb))
                · obtain ⟨ds, hds, hz⟩ := expr_zero p fs fuel hp hc hce ha hs hv
                  exact ⟨ds, hds, fun x hm => by rw [Eval.execStmt]; simp [hk, hz x hm]⟩
                obtain ⟨w, hw, hb⟩ := out_let fs fuel hv
                refine .inl ⟨w, fun ρs ha hs => ?_, hb⟩
                have he := expr_ok p fs fuel hp hc hce ha hs hw hn
                rw [Eval.execStmt]; simp [hk, he]
              | assign =>
                cases hl : env.lookup x with
                | none => simp [hl, reject, throw, throwThe, MonadExceptOf.throw] at h
                | some l =>
                  simp only [hl] at h
                  tm_simp at h
                  obtain ⟨-, rb, hrb, rfl⟩ := h
                  refine guarded_sim p fs fuel (fun ρs ρo v ha hs hv => ?_)
                    (set_sim p fs fuel (env_has_of_lookup hl) (by simp [stmtChanges])
                      (fun ρo o hn hv => ?_) (ihs _ tail rest rb hrb))
                  · obtain ⟨ds, hds, hz⟩ := expr_zero p fs fuel hp hc hce ha hs hv
                    exact ⟨ds, hds, fun x hm => by rw [Eval.execStmt]; simp [hk, hz x hm]⟩
                  obtain ⟨w, hw, hb⟩ := out_let fs fuel hv
                  refine .inl ⟨w, fun ρs ha hs => ?_, hb⟩
                  have he := expr_ok p fs fuel hp hc hce ha hs hw hn
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
                  obtain ⟨hl', hr'⟩ := compound_strict hk
                  -- The source's `x op= e` gives what the code `cb` gives, or
                  -- the panic.
                  have key : ∀ ρs ρo w, Agree ρs ρo → Scoped env ρs →
                      IR.Expr.eval fs fuel ρo cb = some w → ∃ ds old,
                        IR.Expr.evalList fs fuel ρo (divisors cb) = some ds ∧ ρs.lookup x = some old ∧
                        ((Eval.eval p fuel ρs e).andThen fun v => Eval.operate o old v) =
                          some (outcome ds w) := by
                    intro ρs ρo w ha hs hw
                    obtain ⟨va, vb, hva, hvb, hout⟩ := translateBinary_out hbin hw
                    simp only [IR.Expr.eval] at hva
                    obtain ⟨db, hdb, hib, he⟩ := expr_sound fs fuel p hp hc hce ha hs hvb
                    obtain ⟨ds, hds, -, hres⟩ :=
                      hout [] db (by simp [divisors, IR.Expr.evalList]) checkVals_nil hdb hib
                    refine ⟨ds, va, hds, by rw [ha x]; exact hva, ?_⟩
                    rw [binaryRes_strict hl' hr', outcome_nil, tolean.Core.Res.andThen_ok, ← he] at hres
                    exact hres
                  refine guarded_sim p fs fuel (fun ρs ρo v ha hs hv => ?_)
                    (set_sim p fs fuel (env_has_of_lookup hl) (by simp [stmtChanges])
                      (fun ρo o' hn hv => ?_) (ihs _ tail rest rb hrb))
                  · obtain ⟨ds, old, hds, hold, hres⟩ := key ρs ρo v ha hs hv
                    refine ⟨ds, hds, fun x hm => ?_⟩
                    rw [outcome_fault hm] at hres
                    rw [Eval.execStmt]; simp [hk, hold, hres]
                  obtain ⟨w, hw, hb⟩ := out_let fs fuel hv
                  refine .inl ⟨w, fun ρs ha hs => ?_, hb⟩
                  obtain ⟨ds, old, hds, hold, hres⟩ := key ρs ρo w ha hs hw
                  rw [outcome_ok (hn ds hds)] at hres
                  rw [Eval.execStmt]; simp [hk, hold, hres]
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
                obtain ⟨hl', hr', hq', hm'⟩ := incDec_strict ho
                intro ρs ρo ha hs
                refine set_sim (P := fun _ => True) p fs fuel (env_has_of_lookup hl)
                  (by simp [stmtChanges]) (fun ρo o' _ hv => ?_) (ihs _ tail rest rb hrb) ρs ρo ha hs
                  trivial
                obtain ⟨w, hw, hb⟩ := out_let fs fuel hv
                refine .inl ⟨w, fun ρs ha hs => ?_, hb⟩
                obtain ⟨va, vb, hva, hvb, hout⟩ := translateBinary_out hbin hw
                simp only [IR.Expr.eval, Option.some.injEq] at hva hvb
                subst hvb
                obtain ⟨ds, -, -, hres⟩ := hout [] [] (by simp [divisors, IR.Expr.evalList]) checkVals_nil
                  (by simp [divisors, IR.Expr.evalList]) checkVals_nil
                rw [binaryRes_strict hl' hr', outcome_nil, outcome_nil, tolean.Core.Res.andThen_ok,
                  tolean.Core.Res.andThen_ok, operate_binary hq' hm'] at hres
                cases hbw : Eval.binary o va (.int 1) with
                | none => rw [hbw] at hres; simp at hres
                | some u =>
                  rw [hbw] at hres
                  simp only [tolean.Core.Res.lift_some, Option.some.injEq] at hres
                  have := outcome_eq_ok hres.symm
                  subst this
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
                rw [guarded_zeroCode]
                intro ρs ρo ha hs
                refine push_sim (P := fun _ => True) p fs fuel hfresh (fun ρo o _ hv => ?_)
                  (ihs _ tail rest rb hrb) ρs ρo ha hs trivial
                obtain ⟨w, hw, hb⟩ := out_let fs fuel hv
                refine .inl ⟨w, fun ρs ha hs => ?_, hb⟩
                have hz := zero_sound p fs fuel hp ht hw
                rw [Eval.execStmt]; simp [hz]
              | [e], h =>
                tm_simp at h
                obtain ⟨⟨c', t'⟩, hc', -, env', hdecl, rb, hrb, rfl⟩ := h
                obtain ⟨hfresh, rfl⟩ := declare_ok hdecl
                refine guarded_sim p fs fuel (fun ρs ρo v ha hs hv => ?_)
                  (push_sim p fs fuel hfresh (fun ρo o hn hv => ?_) (ihs _ tail rest rb hrb))
                · obtain ⟨ds, hds, hz⟩ := expr_zero p fs fuel hp hc hc' ha hs hv
                  exact ⟨ds, hds, fun x hm => by rw [Eval.execStmt]; simp [hz x hm]⟩
                obtain ⟨w, hw, hb⟩ := out_let fs fuel hv
                refine .inl ⟨w, fun ρs ha hs => ?_, hb⟩
                have he := expr_ok p fs fuel hp hc hc' ha hs hw hn
                rw [Eval.execStmt]; simp [he]
              | _ :: _ :: _, h => simp [reject, throw, throwThe, MonadExceptOf.throw] at h
          -- `if`
          · next sp c t els => exact ihi env tail sp c t els rest body h
          -- `if s; c { … }`, as the block `{ s; if c { … } }`
          · next sp s c t els =>
            refine sim_congr p fs fuel (fun ρ => execStmt_ifInit p fuel sp s c t els ρ)
              (fun k hk => ?_) (ihs env tail _ body h)
            simp only [stmtChanges, changesList, changesOption, List.nil_append, List.append_nil,
              List.mem_append] at hk ⊢
            rcases hk with hk | hk | hk <;> simp [hk]
          -- `switch`, as a chain of `if` statements
          · next sp init tag bsp clauses =>
            by_cases hbad : (tag.isSome && !hasCase clauses) = true
            · simp [hbad, reject, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
            have hcase : tag.isSome = true → hasCase clauses = true := by
              intro hs; simpa [hs] using hbad
            simp only [hbad, Bool.false_eq_true, ↓reduceIte, pure_bind] at h
            cases hd : switchChain tag none clauses with
            | none => simp [hd, reject, throw, throwThe, MonadExceptOf.throw] at h
            | some d =>
              simp only [hd] at h
              have hsw := execStmt_switch_chain p fuel (sp := sp) (bsp := bsp) hcase hd
              have hch := fun (k : String) (hk : k ∈ stmtChanges d) => chain_changes clauses none d hd hk
              cases init with
              | none =>
                refine sim_congr p fs fuel hsw (fun k hk => ?_) (ihs env tail _ body h)
                rcases hch k hk with hk | ⟨_, _, he, _⟩
                · simpa [stmtChanges, changesOption] using hk
                · cases he
              | some s =>
                refine sim_congr p fs fuel (fun ρ => ?_) (fun k hk => ?_) (ihs env tail _ body h)
                · rw [execStmt_switchInit, block_eq, block_eq, exec_cons_eq, exec_cons_eq]
                  congr 2
                  funext o
                  cases o with
                  | ret v => rfl
                  | panic x => rfl
                  | normal ρ₁ => exact exec_cons_congr p fuel hsw [] ρ₁
                · simp only [stmtChanges, changesList, changesOption, List.append_nil,
                    List.mem_append] at hk ⊢
                  rcases hk with hk | hk
                  · exact .inl hk
                  · rcases hch k hk with hk | ⟨_, _, he, _⟩
                    · exact .inr hk
                    · cases he
          -- a block
          · next sp bbody =>
            split at h
            · cases tail with
              | state names => simp [reject, throw, throwThe, MonadExceptOf.throw] at h
              | ret result monadic =>
                cases rest with
                | cons _ _ => simp [reject, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
                | nil =>
                  tm_simp at h
                  have sim := ihs env (.ret result monadic) bbody body h
                  intro ρs ρo ha hs
                  refine ⟨fun v hv => ?_, fun ρo' hv => ?_, fun x hv => ?_⟩
                  · exact exec_cons_ret p fuel (block_ret p fuel (.block sp bbody)
                      (by simpa [blockStatements] using (sim ρs ρo ha hs).1 v hv))
                  · exact absurd ((sim ρs ρo ha hs).2.1 ρo' hv).1 (by simp [Tail.isRet])
                  · exact exec_cons_panic p fuel (block_panic p fuel (.block sp bbody)
                      (by simpa [blockStatements] using (sim ρs ρo ha hs).2.2 x hv))
            · tm_simp at h
              obtain ⟨-, inner, hinner, rb, hrb, rfl⟩ := h
              exact block_state_sim p fs fuel (ihs env _ bbody inner hinner) (ihs env tail rest rb hrb)
          · exact absurd h reject_ne_ok
    · simp only [translateIf] at h
      rw [bind_ok] at h
      obtain ⟨⟨cond, ct⟩, hcond, h⟩ := h
      rw [ite_ok] at h
      simp only [pure_bind, bind_ok, reject_ne_ok, false_and, and_false, exists_false, or_false] at h
      obtain ⟨-, h⟩ := h
      have hz : ∀ ρs ρo v, Agree ρs ρo → Scoped env ρs → IR.Expr.eval fs fuel ρo cond = some v →
          ∃ ds, IR.Expr.evalList fs fuel ρo (divisors cond) = some ds ∧
            (∀ x, firstFault ds = some x → Eval.execStmt p fuel ρs (.ifStmt sp none c t els) =
              some (.panic x)) := by
        intro ρs ρo v ha hs hv
        obtain ⟨ds, hds, hz⟩ := expr_zero p fs fuel hp hc hcond ha hs hv
        exact ⟨ds, hds, fun x hm => by rw [Eval.execStmt, hz x hm]; rfl⟩
      split at h
      -- A branch returns: the rest joins the other branch.
      · cases tail with
        | state names => simp [reject, throw, throwThe, MonadExceptOf.throw] at h
        | ret result monadic =>
          tm_simp at h
          obtain ⟨hnot, wt, hwt, wf, hwf, rfl⟩ := h
          have simT := ihs env (.ret result monadic) (blockStatements t) wt hwt
          have simF := ihs env (.ret result monadic) (elseStatements els ++ rest) wf hwf
          refine guarded_sim p fs fuel hz (fun ρs ρo ha hs hn => ?_)
          -- The statements after the if, when the test is false.
          have hfalse : ∀ {o : Outcome}, Eval.eval p fuel ρs c = some (.ok (.bool false)) →
              Eval.exec p fuel ρs (elseStatements els ++ rest) = some o → (∀ ρ', o ≠ .normal ρ') →
              Eval.exec p fuel ρs (.ifStmt sp none c t els :: rest) = some o := by
            intro o hcb hr hno
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
              cases o with
              | normal ρ' => exact absurd rfl (hno ρ')
              | ret v => exact exec_cons_ret p fuel (if_ret p fuel hcb (by simpa [branchOf] using hr))
              | panic x =>
                exact exec_cons_panic p fuel (if_panic p fuel hcb (by simpa [branchOf] using hr))
          refine ⟨fun v hv => ?_, fun ρo' hv => ?_, fun y hv => ?_⟩
          · obtain ⟨b, hb, hex⟩ := out_ite fs fuel hv
            have hcb := expr_ok p fs fuel hp hc hcond ha hs hb hn
            cases b
            · simp only [Bool.false_eq_true, ↓reduceIte] at hex
              exact hfalse hcb ((simF ρs ρo ha hs).1 v hex) (fun _ h => by cases h)
            · simp only [↓reduceIte] at hex
              have hr := (simT ρs ρo ha hs).1 v hex
              exact exec_cons_ret p fuel (if_ret p fuel hcb (by simpa [branchOf] using hr))
          · obtain ⟨b, -, hex⟩ := out_ite fs fuel hv
            cases b
            · exact absurd ((simF ρs ρo ha hs).2.1 ρo' (by simpa using hex)).1 (by simp [Tail.isRet])
            · exact absurd ((simT ρs ρo ha hs).2.1 ρo' (by simpa using hex)).1 (by simp [Tail.isRet])
          · obtain ⟨b, hb, hex⟩ := out_ite fs fuel hv
            have hcb := expr_ok p fs fuel hp hc hcond ha hs hb hn
            cases b
            · simp only [Bool.false_eq_true, ↓reduceIte] at hex
              exact hfalse hcb ((simF ρs ρo ha hs).2.2 y hex) (fun _ h => by cases h)
            · simp only [↓reduceIte] at hex
              have hr := (simT ρs ρo ha hs).2.2 y hex
              exact exec_cons_panic p fuel (if_panic p fuel hcb (by simpa [branchOf] using hr))
      -- No branch returns: the branches give the locals they change.
      · tm_simp at h
        obtain ⟨-, wt, hwt, wf, hwf, rb, hrb, rfl⟩ := h
        have simT := ihs env _ (blockStatements t) wt hwt
        have simF := ihs env _ (elseStatements els) wf hwf
        have simR := ihs env tail rest rb hrb
        refine guarded_sim p fs fuel hz (fun ρs ρo ha hs hn => ?_)
        have key : ∀ o, IR.Body.exec fs fuel ρo
            (.letState (changedNames (blockStatements t ++ elseStatements els) env) (.ite cond wt wf) rb) =
              some o →
            (∃ x, o = .panic x ∧
              Eval.execStmt p fuel ρs (.ifStmt sp none c t els) = some (.panic x)) ∨
            ∃ mod ρ₁, Eval.execStmt p fuel ρs (.ifStmt sp none c t els) = some (.normal mod) ∧
              Agree mod ρ₁ ∧ Scoped env mod ∧
              Frame (stmtChanges (.ifStmt sp none c t els)) mod ρs ∧
              IR.Body.exec fs fuel ρ₁ rb = some o := by
          intro o hv
          have simB : ∀ b, StmtSim p fs fuel env
              (.state (changedNames (blockStatements t ++ elseStatements els) env))
              (branchOf b t els) (if b then wt else wf) := by
            intro b
            cases b
            · simpa [branchOf] using simF
            · simpa [branchOf] using simT
          rcases out_letState fs fuel hv with ⟨x, hbr, rfl⟩ | ⟨inner, ρ₁, hbr, hbind, hrest⟩
          · left
            obtain ⟨b, hb, hex⟩ := out_ite fs fuel hbr
            have hcb := expr_ok p fs fuel hp hc hcond ha hs hb hn
            exact ⟨x, rfl, if_panic p fuel hcb ((simB b ρs ρo ha hs).2.2 x hex)⟩
          right
          obtain ⟨b, hb, hex⟩ := out_ite fs fuel hbr
          have hcb := expr_ok p fs fuel hp hc hcond ha hs hb hn
          obtain ⟨-, new, mod, hexs, hag, hnew, hfr⟩ := (simB b ρs ρo ha hs).2.1 inner hex
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
            simp only [stmtChanges, changesOption, List.nil_append, List.mem_append]
            cases b
            · right; simpa [branchOf, changesList_else] using hk
            · left; simpa [branchOf, changesList_block] using hk
        refine ⟨fun v hv => ?_, fun ρo' hv => ?_, fun y hv => ?_⟩
        · rcases key _ hv with ⟨x, h, -⟩ | ⟨mod, ρ₁, hif, ha', hs', -, hrest⟩
          · cases h
          rw [exec_cons_normal p fuel hif]
          exact (simR mod ρ₁ ha' hs').1 v hrest
        · rcases key _ hv with ⟨x, h, -⟩ | ⟨mod, ρ₁, hif, ha', hs', hfr, hrest⟩
          · cases h
          obtain ⟨htail, new', mod', hex', hag', hnew', hfr'⟩ := (simR mod ρ₁ ha' hs').2.1 ρo' hrest
          refine ⟨htail, new', mod', by rw [exec_cons_normal p fuel hif]; exact hex', hag', hnew', ?_⟩
          simpa [changesList] using hfr'.trans hfr
        · rcases key _ hv with ⟨x, h, hif⟩ | ⟨mod, ρ₁, hif, ha', hs', -, hrest⟩
          · cases h
            exact exec_cons_panic p fuel hif
          rw [exec_cons_normal p fuel hif]
          exact (simR mod ρ₁ ha' hs').2.2 y hrest

/-- The body that the translator gives for a statement list means what the
statements mean. -/
theorem stmts_sound {ctx : Ctx} (hp : ctx.program = p) (hc : CallsAgree p fs fuel) {n : Nat}
    {env : Pure.Env} {tail : Tail} {ss : List Stmt} {body : IR.Body}
    (h : translateStmts ctx env tail n ss = .ok body) : StmtSim p fs fuel env tail ss body :=
  (stmts_sound_aux p fs fuel hp hc n).1 env tail ss body h

end tolean.Go.Proof
