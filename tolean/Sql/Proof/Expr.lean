import tolean.Sql.Translate.Plan

/-!
The translation of an expression means what the expression means.

`expr_sound` states it for `trExpr`. When the translator gives code for an
expression, and the IR's evaluator gives a value for that code, the
interpreter gives the same value for the expression. The two environments
must bind the same aliases to the same tables, with the same rows.

`Refines x y` says that every value of `x` is a value of `y`. Each operation
of the subset keeps it, and so do `AND` and `OR`, which can give a value even
when one side raises an error. An enum label is the one exception. The
translator writes a string literal as a label when the other side of `=` is
an enum, and the label is a different value from the string. `ExprOK` allows
that case, and `eqM_rel` shows that `=` gives the same answer either way.
-/
namespace tolean.Sql.Proof

open tolean tolean.Sql
open tolean.Sql.Eval
open tolean.Sql.Plan (TM St reject trExpr Scope Entry T)

variable {α β : Type}

theorem tm_bind_ok {x : TM α} {f : α → TM β} {st : St} {r : β × St} :
    (x >>= f) st = .ok r ↔ ∃ a st₁, x st = .ok (a, st₁) ∧ f a st₁ = .ok r := by
  show (x st >>= fun p => f p.1 p.2) = _ ↔ _
  cases h : x st with
  | error e => simp [bind, Except.bind]
  | ok p =>
    obtain ⟨a, s⟩ := p
    simp only [bind, Except.bind]
    exact ⟨fun h => ⟨a, s, rfl, h⟩, fun ⟨_, _, he, h⟩ => by cases he; exact h⟩

theorem tm_pure_ok {a : α} {st : St} {r : α × St} :
    (pure a : TM α) st = .ok r ↔ r = (a, st) := by
  simp [pure, StateT.pure, Except.pure, eq_comm]

theorem tm_reject_ne {m : String} {st : St} {r : α × St} : reject m st ≠ .ok r := by
  simp [reject, throw, throwThe, MonadExceptOf.throw, StateT.lift, bind, Except.bind]

/-- `x` refines `y`: every value of `x` is a value of `y`. -/
def Refines (x y : M α) : Prop := ∀ v, x = .ok v → y = .ok v

theorem Refines.refl (x : M α) : Refines x x := fun _ h => h

theorem Refines.bind {x y : M α} {f g : α → M β} (hx : Refines x y)
    (hf : ∀ a, Refines (f a) (g a)) : Refines (x >>= f) (y >>= g) := by
  intro v h
  cases hxa : x with
  | error e => simp [hxa, Bind.bind, Except.bind] at h
  | ok a =>
    simp only [hxa, Bind.bind, Except.bind] at h
    rw [hx a hxa]
    exact hf a v h

theorem Refines.map {x y : M α} {f : α → β} (hx : Refines x y) : Refines (f <$> x) (f <$> y) := by
  intro v h
  cases hxa : x with
  | error e => simp [hxa, Functor.map, Except.map] at h
  | ok a =>
    simp only [hxa, Functor.map, Except.map] at h
    rw [hx a hxa]
    exact h

theorem and3_mono {a a' b b' : M (Option Bool)} (ha : Refines a a') (hb : Refines b b') :
    Refines (and3 a b) (and3 a' b') := by
  intro v h
  rcases a with e | (_ | _ | _) <;> rcases b with e' | (_ | _ | _) <;>
    simp only [and3, reduceCtorEq, Except.ok.injEq] at h <;>
    (try (obtain rfl := ha _ rfl)) <;> (try (obtain rfl := hb _ rfl)) <;> subst h <;>
    (try (rcases a' with _ | (_ | _ | _))) <;> (try (rcases b' with _ | (_ | _ | _))) <;> rfl

theorem or3_mono {a a' b b' : M (Option Bool)} (ha : Refines a a') (hb : Refines b b') :
    Refines (or3 a b) (or3 a' b') := by
  intro v h
  rcases a with e | (_ | _ | _) <;> rcases b with e' | (_ | _ | _) <;>
    simp only [or3, reduceCtorEq, Except.ok.injEq] at h <;>
    (try (obtain rfl := ha _ rfl)) <;> (try (obtain rfl := hb _ rfl)) <;> subst h <;>
    (try (rcases a' with _ | (_ | _ | _))) <;> (try (rcases b' with _ | (_ | _ | _))) <;> rfl

variable {a a' b b' : M Val}

theorem andM_mono (ha : Refines a a') (hb : Refines b b') : Refines (andM a b) (andM a' b') :=
  Refines.map (and3_mono (ha.bind fun _ => .refl _) (hb.bind fun _ => .refl _))

theorem orM_mono (ha : Refines a a') (hb : Refines b b') : Refines (orM a b) (orM a' b') :=
  Refines.map (or3_mono (ha.bind fun _ => .refl _) (hb.bind fun _ => .refl _))

theorem notM_mono (ha : Refines a a') : Refines (notM a) (notM a') :=
  ha.bind fun _ => .refl _

theorem eqM_mono {ne : Bool} (ha : Refines a a') (hb : Refines b b') : Refines (eqM ne a b) (eqM ne a' b') :=
  ha.bind fun _ => hb.bind fun _ => .refl _

theorem cmpM_mono {op : CmpOp} (ha : Refines a a') (hb : Refines b b') : Refines (cmpM op a b) (cmpM op a' b') :=
  ha.bind fun _ => hb.bind fun _ => .refl _

theorem arithM_mono {op : ArithOp} (ha : Refines a a') (hb : Refines b b') :
    Refines (arithM op a b) (arithM op a' b') :=
  ha.bind fun _ => hb.bind fun _ => .refl _

theorem leastM_mono (ha : Refines a a') (hb : Refines b b') : Refines (leastM a b) (leastM a' b') :=
  ha.bind fun _ => hb.bind fun _ => .refl _

theorem negM_mono (ha : Refines a a') : Refines (negM a) (negM a') := ha.bind fun _ => .refl _

theorem isNullM_mono {n : Bool} (ha : Refines a a') : Refines (isNullM n a) (isNullM n a') :=
  ha.bind fun _ => .refl _

theorem coalesceM_mono (ha : Refines a a') (hb : Refines b b') :
    Refines (coalesceM a b) (coalesceM a' b') :=
  ha.bind fun v => by cases v <;> first | exact hb | exact .refl _

theorem coalesceM_null (a : M Val) : coalesceM a (pure .null) = a := by
  cases a with
  | error e => rfl
  | ok v => cases v <;> rfl

/-- A string compares with an enum label as the label does. -/
theorem eq3_enum_left {T l : String} {y : Val} {r : Option Bool} (h : eq3 (.enum T l) y = .ok r) :
    eq3 (.text l) y = .ok r := by
  cases y <;> simp only [eq3] at h ⊢ <;> first | exact h | (split at h <;> simp_all [stuck])

theorem eq3_enum_right {T l : String} {x : Val} {r : Option Bool} (h : eq3 x (.enum T l) = .ok r) :
    eq3 x (.text l) = .ok r := by
  cases x <;> simp only [eq3] at h ⊢ <;> first | exact h | (split at h <;> simp_all [stuck])

theorem check_ok {c : Bool} {m : String} {st st' : St} {u : Unit} :
    Plan.check c m st = .ok (u, st') ↔ c = true ∧ st' = st := by
  unfold Plan.check
  cases c
  · simp only [Bool.false_eq_true, ↓reduceIte, false_and, iff_false]; exact tm_reject_ne
  · simp only [↓reduceIte, tm_pure_ok, Prod.mk.injEq, true_and]

theorem need_ok {o : Option α} {m : String} {st st' : St} {a : α} :
    Plan.need o m st = .ok (a, st') ↔ o = some a ∧ st' = st := by
  unfold Plan.need
  cases o
  · simp only [reduceCtorEq, false_and, iff_false]; exact tm_reject_ne
  · simp only [tm_pure_ok, Prod.mk.injEq, Option.some.injEq]
    exact ⟨fun h => ⟨h.1.symm, h.2⟩, fun h => ⟨h.1.symm, h.2⟩⟩

/-- `x'` refines `x`, or it is an enum label whose source is the string
literal of `x`. -/
def ValRel (x' x : M Val) : Prop :=
  Refines x' x ∨ ∃ T l, x' = pure (.enum T l) ∧ x = pure (.text l)

theorem eqM_rel {ne : Bool} (ha : ValRel a a') (hb : ValRel b b') : Refines (eqM ne a b) (eqM ne a' b') := by
  intro v h
  simp only [eqM, bind, Except.bind] at h ⊢
  cases hav : a with
  | error e => simp [hav] at h
  | ok x =>
    cases hbv : b with
    | error e => simp [hav, hbv] at h
    | ok y =>
      simp only [hav, hbv] at h
      cases he : eq3 x y with
      | error e => simp [he] at h
      | ok r =>
        simp only [he] at h
        obtain ⟨x₀, hx₀, he₁⟩ : ∃ x₀, a' = .ok x₀ ∧ eq3 x₀ y = .ok r := by
          rcases ha with ha | ⟨T, l, rfl, rfl⟩
          · exact ⟨x, ha x hav, he⟩
          · cases hav; exact ⟨_, rfl, eq3_enum_left he⟩
        obtain ⟨y₀, hy₀, he₂⟩ : ∃ y₀, b' = .ok y₀ ∧ eq3 x₀ y₀ = .ok r := by
          rcases hb with hb | ⟨T, l, rfl, rfl⟩
          · exact ⟨y, hb y hbv, he₁⟩
          · cases hbv; exact ⟨_, rfl, eq3_enum_right he₁⟩
        simp only [hx₀, hy₀, he₂]
        exact h

section
variable (s : Schema) (i : Input) (Γ : Scope) (env : List Binding)

/-- The code `ie` of `e` means what `e` means, except an enum label, whose
source is a string literal. -/
def ExprOK (e : Expr) (ie : IR.Expr) (t : T) : Prop :=
  (∃ sp T l, ie = .enumLit T l ∧ e = .str sp l ∧ t.ty = .enum T) ∨
  (ie.isEnumLit = false ∧ Refines (ie.eval i (env.map Binding.row)) (Eval.eval s i env e))

variable {s i Γ env}

theorem ExprOK.rel {e : Expr} {ie : IR.Expr} {t : T} (h : ExprOK s i env e ie t) :
    ValRel (ie.eval i (env.map Binding.row)) (Eval.eval s i env e) := by
  rcases h with ⟨sp, T, l, rfl, rfl, _⟩ | ⟨_, h⟩
  · exact .inr ⟨T, l, rfl, rfl⟩
  · exact .inl h

/-- A translation whose type is not an enum is no label. -/
theorem ExprOK.refines {e : Expr} {ie : IR.Expr} {t : T} (h : ExprOK s i env e ie t)
    (ht : ∀ n, t.ty ≠ .enum n) : Refines (ie.eval i (env.map Binding.row)) (Eval.eval s i env e) := by
  rcases h with ⟨_, T, _, _, _, hty⟩ | ⟨_, h⟩
  · exact absurd hty (ht T)
  · exact h

theorem ExprOK.refines' {e : Expr} {ie : IR.Expr} {t : T} (h : ExprOK s i env e ie t)
    (hl : ie.isEnumLit = false) : Refines (ie.eval i (env.map Binding.row)) (Eval.eval s i env e) := by
  rcases h with ⟨_, _, _, rfl, _, _⟩ | ⟨_, h⟩
  · simp [IR.Expr.isEnumLit] at hl
  · exact h

/-- Take apart a translator step that gave a value. -/
macro "tm_simp" " at " h:ident : tactic =>
  `(tactic| simp only [tm_bind_ok, tm_pure_ok, need_ok, check_ok, Prod.mk.injEq] at $h:ident)

theorem castCode_ok {tgt : Target} {ie ie' : IR.Expr} {t t' : T} {st st' : St}
    (h : Plan.castCode tgt ie t st = .ok ((ie', t'), st')) :
    ie' = .cast tgt ie ∨ (∃ en nl, ie' = .enumText en nl ie ∧ tgt = .text) := by
  unfold Plan.castCode at h
  by_cases heq : t.ty = tgt.ty
  · rw [if_pos heq] at h
    cases tgt with
    | int w =>
      simp only at h
      tm_simp at h
      obtain ⟨_, _, _, ⟨rfl, _⟩, _⟩ := h
      exact .inl rfl
    | _ => simp only [tm_pure_ok, Prod.mk.injEq] at h; exact .inl h.1.1
  · rw [if_neg heq] at h
    revert h
    cases t.ty <;> cases tgt <;> simp only [tm_pure_ok, Prod.mk.injEq] <;>
      first | exact fun h => absurd h tm_reject_ne | exact fun h => .inr ⟨_, _, h.1.1, rfl⟩ |
        exact fun h => .inr ⟨_, _, h.1.1, trivial⟩

theorem binCode_ok {bop : BinOp} {ia ib ie : IR.Expr} {ta tb t : T} {st st' : St}
    (h : Plan.binCode bop ia ta ib tb st = .ok ((ie, t), st')) :
    (∃ aop, bop = .arith aop ∧ ie = .arith aop ia ib ∧ ta.ty = .int ∧ tb.ty = .int) ∨
    (bop = .eq ∧ ie = .eq false ia ib) ∨ (bop = .ne ∧ ie = .eq true ia ib) ∨
    (∃ cop, bop = .cmp cop ∧ ie = .cmp cop ia ib ∧ ta.ty = .int ∧ tb.ty = .int) := by
  unfold Plan.binCode at h
  split at h
  · tm_simp at h
    obtain ⟨_, _, ⟨hc, rfl⟩, ⟨rfl, _⟩, _⟩ := h
    simp only [decide_eq_true_eq] at hc
    exact .inl ⟨_, rfl, rfl, hc.1, hc.2.1⟩
  · tm_simp at h
    obtain ⟨_, _, ⟨_, rfl⟩, ⟨rfl, _⟩, _⟩ := h
    exact .inr (.inl ⟨rfl, rfl⟩)
  · tm_simp at h
    obtain ⟨_, _, ⟨_, rfl⟩, ⟨rfl, _⟩, _⟩ := h
    exact .inr (.inr (.inl ⟨rfl, rfl⟩))
  · tm_simp at h
    obtain ⟨_, _, ⟨hc, rfl⟩, ⟨rfl, _⟩, _⟩ := h
    simp only [decide_eq_true_eq] at hc
    exact .inr (.inr (.inr ⟨_, rfl, rfl, hc.1, hc.2⟩))
  · exact absurd h tm_reject_ne

theorem argType_ok {n : String} {hint : Option IR.Ty} {st st' : St} {ie : IR.Expr} {t : T}
    (h : (Plan.argType n hint >>= fun ty => pure (IR.Expr.arg n (decide (ty = .bool)), ({ ty, width := .w16 } : T))) st =
      .ok ((ie, t), st')) : ∃ b, ie = .arg n b := by
  tm_simp at h
  obtain ⟨_, _, _, h⟩ := h
  exact ⟨_, h.1.1⟩

theorem isNullM_rel {n : Bool} (ha : ValRel a a') : Refines (isNullM n a) (isNullM n a') := by
  rcases ha with ha | ⟨T, l, rfl, rfl⟩
  · exact isNullM_mono ha
  · exact .refl _

theorem expr_sound (hΓ : env.map Binding.shape = Γ.map Entry.shape) :
    ∀ (e : Expr) (hint : Option IR.Ty) (st st' : St) (ie : IR.Expr) (t : T),
    trExpr s Γ hint e st = .ok ((ie, t), st') → ExprOK s i env e ie t
  | .column sp qual n, hint, st, st', ie, t, h => by
    simp only [trExpr] at h
    tm_simp at h
    obtain ⟨⟨d, j⟩, _, ⟨hr, rfl⟩, en, _, ⟨he, rfl⟩, c, _, ⟨hc, rfl⟩, ct, _, ⟨hct, rfl⟩, ⟨rfl, rfl⟩, rfl⟩ := h
    refine .inr ⟨rfl, fun v hv => ?_⟩
    simp only [Eval.eval, hΓ, hr, Eval.column]
    simp only [IR.Expr.eval, List.getElem?_map] at hv
    cases hb : env[d]? with
    | none => simp [hb] at hv; cases hv
    | some b => simp only [hb, Option.map_some] at hv ⊢; exact hv
  | .int sp v, hint, st, st', ie, t, h => by
    simp only [trExpr] at h
    tm_simp at h
    obtain ⟨_, _, _, ⟨rfl, rfl⟩, rfl⟩ := h
    exact .inr ⟨rfl, fun v hv => by simpa [IR.Expr.eval, Eval.eval] using hv⟩
  | .bool sp b, hint, st, st', ie, t, h => by
    simp only [trExpr] at h
    tm_simp at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    exact .inr ⟨rfl, fun v hv => by simpa [IR.Expr.eval, Eval.eval] using hv⟩
  | .str sp v, hint, st, st', ie, t, h => by
    simp only [trExpr, Plan.strLit] at h
    split at h
    · tm_simp at h
      obtain ⟨_, _, _, ⟨rfl, rfl⟩, rfl⟩ := h
      exact .inl ⟨sp, _, v, rfl, rfl, rfl⟩
    · tm_simp at h
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
      exact .inr ⟨rfl, fun v hv => by simpa [IR.Expr.eval, Eval.eval] using hv⟩
  | .null sp, hint, st, st', ie, t, h => by
    simp only [trExpr] at h; exact absurd h tm_reject_ne
  | .arg sp n nl, hint, st, st', ie, t, h => by
    simp only [trExpr] at h
    rw [tm_bind_ok] at h
    obtain ⟨_, _, _, h⟩ := h
    obtain ⟨_, rfl⟩ := argType_ok h
    exact .inr ⟨rfl, fun v hv => by simpa [IR.Expr.eval, Eval.eval] using hv⟩
  | .cast sp inner tn, hint, st, st', ie, t, h => by
    simp only [trExpr] at h
    tm_simp at h
    obtain ⟨tgt, _, ⟨htgt, rfl⟩, _, _, _, ⟨ie₀, t₀⟩, _, h₀, _, _, ⟨hl, rfl⟩, h⟩ := h
    have ih := expr_sound hΓ inner _ _ _ _ _ h₀
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at hl
    have hr := ih.refines' hl
    refine .inr ⟨?_, ?_⟩
    · rcases castCode_ok h with rfl | ⟨_, _, rfl, _⟩ <;> rfl
    · rcases castCode_ok h with rfl | ⟨_, _, rfl, rfl⟩
      · simp only [IR.Expr.eval, Eval.eval, htgt]
        exact hr.bind fun _ => .refl _
      · simp only [IR.Expr.eval, Eval.eval, htgt]
        exact hr.bind fun _ => .refl _
  | .binary sp op a b, hint, st, st', ie, t, h => by
    simp only [trExpr] at h
    cases hop : BinOp.ofString op with
    | none => simp only [hop] at h; exact absurd h tm_reject_ne
    | some bop =>
      cases bop with
      | and =>
        simp only [hop] at h
        tm_simp at h
        obtain ⟨⟨ia, ta⟩, _, ha, ⟨ib, tb⟩, _, hb, _, _, ⟨hc, rfl⟩, ⟨rfl, rfl⟩, rfl⟩ := h
        simp only [decide_eq_true_eq] at hc
        have iha := (expr_sound hΓ a _ _ _ _ _ ha).refines (by intro n; rw [hc.1]; simp)
        have ihb := (expr_sound hΓ b _ _ _ _ _ hb).refines (by intro n; rw [hc.2]; simp)
        refine .inr ⟨rfl, ?_⟩
        simp only [IR.Expr.eval, Eval.eval, hop, Eval.binary]
        exact andM_mono iha ihb
      | or =>
        simp only [hop] at h
        tm_simp at h
        obtain ⟨⟨ia, ta⟩, _, ha, ⟨ib, tb⟩, _, hb, _, _, ⟨hc, rfl⟩, ⟨rfl, rfl⟩, rfl⟩ := h
        simp only [decide_eq_true_eq] at hc
        have iha := (expr_sound hΓ a _ _ _ _ _ ha).refines (by intro n; rw [hc.1]; simp)
        have ihb := (expr_sound hΓ b _ _ _ _ _ hb).refines (by intro n; rw [hc.2]; simp)
        refine .inr ⟨rfl, ?_⟩
        simp only [IR.Expr.eval, Eval.eval, hop, Eval.binary]
        exact orM_mono iha ihb
      | _ =>
        simp only [hop] at h
        tm_simp at h
        obtain ⟨_, _, _, ⟨ia, ta⟩, _, ha, ⟨ib, tb⟩, _, hb, _, _, ⟨_, rfl⟩, h⟩ := h
        have iha := expr_sound hΓ a _ _ _ _ _ ha
        have ihb := expr_sound hΓ b _ _ _ _ _ hb
        rcases binCode_ok h with ⟨aop, hbop, rfl, hta, htb⟩ | ⟨hbop, rfl⟩ | ⟨hbop, rfl⟩ |
            ⟨cop, hbop, rfl, hta, htb⟩
        · cases hbop <;> refine .inr ⟨rfl, ?_⟩ <;>
            simp only [IR.Expr.eval, Eval.eval, hop, Eval.binary] <;>
            exact arithM_mono (iha.refines (by intro n; rw [hta]; simp))
              (ihb.refines (by intro n; rw [htb]; simp))
        · cases hbop <;> refine .inr ⟨rfl, ?_⟩ <;>
            simp only [IR.Expr.eval, Eval.eval, hop, Eval.binary] <;>
            exact eqM_rel iha.rel ihb.rel
        · cases hbop <;> refine .inr ⟨rfl, ?_⟩ <;>
            simp only [IR.Expr.eval, Eval.eval, hop, Eval.binary] <;>
            exact eqM_rel iha.rel ihb.rel
        · cases hbop <;> refine .inr ⟨rfl, ?_⟩ <;>
            simp only [IR.Expr.eval, Eval.eval, hop, Eval.binary] <;>
            exact cmpM_mono (iha.refines (by intro n; rw [hta]; simp))
              (ihb.refines (by intro n; rw [htb]; simp))
  | .unary sp op a, hint, st, st', ie, t, h => by
    simp only [trExpr] at h
    by_cases hn : op = "not"
    · rw [if_pos hn] at h
      tm_simp at h
      obtain ⟨⟨ia, ta⟩, _, ha, _, _, ⟨hc, rfl⟩, ⟨rfl, rfl⟩, rfl⟩ := h
      simp only [decide_eq_true_eq] at hc
      have iha := (expr_sound hΓ a _ _ _ _ _ ha).refines (by intro n; rw [hc]; simp)
      refine .inr ⟨rfl, ?_⟩
      simp only [IR.Expr.eval, Eval.eval, Eval.unary, if_pos hn]
      exact notM_mono iha
    · by_cases hm : op = "-"
      · rw [if_neg hn, if_pos hm] at h
        tm_simp at h
        obtain ⟨⟨ia, ta⟩, _, ha, _, _, ⟨hc, rfl⟩, ⟨rfl, rfl⟩, rfl⟩ := h
        simp only [decide_eq_true_eq] at hc
        have iha := (expr_sound hΓ a _ _ _ _ _ ha).refines (by intro n; rw [hc.1]; simp)
        refine .inr ⟨rfl, ?_⟩
        simp only [IR.Expr.eval, Eval.eval, Eval.unary, if_neg hn, if_pos hm]
        exact negM_mono iha
      · rw [if_neg hn, if_neg hm] at h
        exact absurd h tm_reject_ne
  | .isNull sp inner negated, hint, st, st', ie, t, h => by
    simp only [trExpr] at h
    tm_simp at h
    obtain ⟨⟨ie₀, t₀⟩, _, h₀, _, _, ⟨_, rfl⟩, ⟨rfl, rfl⟩, rfl⟩ := h
    refine .inr ⟨rfl, ?_⟩
    exact isNullM_rel (expr_sound hΓ inner _ _ _ _ _ h₀).rel
  | .call sp f [], hint, st, st', ie, t, h => by
    rw [trExpr.eq_def] at h
    cases hf : Fn.ofString f with
    | none => simp only [hf] at h; exact absurd h tm_reject_ne
    | some fn =>
      cases fn with
      | now =>
        simp only [hf] at h
        tm_simp at h
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
        refine .inr ⟨rfl, fun v hv => ?_⟩
        simpa [IR.Expr.eval, Eval.eval, Eval.evalCall, hf] using hv
      | _ => simp only [hf] at h; exact absurd h tm_reject_ne
  | .call sp f [a], hint, st, st', ie, t, h => by
    rw [trExpr.eq_def] at h
    cases hf : Fn.ofString f with
    | none => simp only [hf] at h; exact absurd h tm_reject_ne
    | some fn => cases fn <;> (simp only [hf] at h; exact absurd h tm_reject_ne)
  | .call sp f [a, b], hint, st, st', ie, t, h => by
    rw [trExpr.eq_def] at h
    cases hf : Fn.ofString f with
    | none => simp only [hf] at h; exact absurd h tm_reject_ne
    | some fn =>
      cases fn with
      | now => simp only [hf] at h; exact absurd h tm_reject_ne
      | least =>
        simp only [hf] at h
        tm_simp at h
        obtain ⟨⟨ia, ta⟩, _, ha, ⟨ib, tb⟩, _, hb, _, _, ⟨hc, rfl⟩, ⟨rfl, rfl⟩, rfl⟩ := h
        simp only [decide_eq_true_eq] at hc
        have iha := (expr_sound hΓ a _ _ _ _ _ ha).refines (by intro n; rw [hc.1]; simp)
        have ihb := (expr_sound hΓ b _ _ _ _ _ hb).refines (by intro n; rw [hc.2.1]; simp)
        refine .inr ⟨rfl, ?_⟩
        simp only [IR.Expr.eval, Eval.eval, Eval.evalCall, hf]
        simpa using leastM_mono iha ihb
      | coalesce =>
        simp only [hf] at h
        tm_simp at h
        obtain ⟨⟨ia, ta⟩, _, ha, ⟨ib, tb⟩, _, hb, _, _, ⟨hl, rfl⟩, _, _, ⟨_, rfl⟩, ⟨rfl, rfl⟩, rfl⟩ := h
        simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hl
        have iha := (expr_sound hΓ a _ _ _ _ _ ha).refines' hl.1
        have ihb := (expr_sound hΓ b _ _ _ _ _ hb).refines' hl.2
        refine .inr ⟨rfl, ?_⟩
        simp only [IR.Expr.eval, Eval.eval, Eval.evalCall, hf]
        simpa [coalesceM_null] using coalesceM_mono iha ihb
  | .call sp f (a :: b :: c :: rest), hint, st, st', ie, t, h => by
    rw [trExpr.eq_def] at h
    cases hf : Fn.ofString f with
    | none => simp only [hf] at h; exact absurd h tm_reject_ne
    | some fn => cases fn <;> (simp only [hf] at h; exact absurd h tm_reject_ne)
  | .typedLit .., hint, st, st', ie, t, h => by
    simp only [trExpr] at h; exact absurd h tm_reject_ne
  | .exists .., hint, st, st', ie, t, h => by
    simp only [trExpr] at h; exact absurd h tm_reject_ne
  | .subquery .., hint, st, st', ie, t, h => by
    simp only [trExpr] at h; exact absurd h tm_reject_ne

end

end tolean.Sql.Proof
