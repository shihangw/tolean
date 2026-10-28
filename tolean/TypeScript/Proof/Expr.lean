import tolean.TypeScript.Translate
import tolean.TypeScript.Output.Eval

/-!
The translation of an expression means what the expression means.

`expr_sound` states it for the expression functions of the translator: when
the translator gives code for an expression, and the code evaluates to a
value in the output's evaluator, the interpreter gives the same value for the
expression. The two environments must agree on every name, and a name outside
the translator's scope must be unbound, so that `NaN` and `Number` are the
globals.

A call runs the body of a function, which is a statement, so this file takes
the agreement of calls as a hypothesis, `CallsAgree`. The proof for
statements gives it.
-/
namespace tolean.TypeScript.Proof

open tolean.TypeScript tolean.TypeScript.Syntax tolean.TypeScript.Translate
open tolean.TypeScript.Eval (Val Outcome)

variable {N : Type} [JSNumber N]

/-! ### The translator's monad -/

section Monad

variable {α β : Type}

@[simp] theorem bind_ok {x : TM α} {f : α → TM β} {s s' : Ctx} {b : β} :
    (x >>= f) s = .ok b s' ↔ ∃ a s₁, x s = .ok a s₁ ∧ f a s₁ = .ok b s' := by
  simp only [bind, EStateM.bind]
  cases h : x s with
  | ok a s₁ =>
    simp only [EStateM.Result.ok.injEq]
    constructor
    · intro h'; exact ⟨a, s₁, ⟨rfl, rfl⟩, h'⟩
    · rintro ⟨a', s₂, ⟨rfl, rfl⟩, h'⟩; exact h'
  | error e s₁ => simp

@[simp] theorem map_ok {x : TM α} {f : α → β} {s s' : Ctx} {b : β} :
    (f <$> x) s = .ok b s' ↔ ∃ a, x s = .ok a s' ∧ f a = b := by
  show (x >>= fun a => pure (f a)) s = .ok b s' ↔ _
  rw [bind_ok]
  simp only [pure, EStateM.pure, EStateM.Result.ok.injEq]
  constructor
  · rintro ⟨a, s₁, h, rfl, rfl⟩; exact ⟨a, h, rfl⟩
  · rintro ⟨a, h, rfl⟩; exact ⟨a, s', h, rfl, rfl⟩

@[simp] theorem ite_state {c : Prop} [Decidable c] {x y : TM α} {s : Ctx} :
    (if c then x else y) s = if c then x s else y s := by
  split <;> rfl

@[simp] theorem pure_ok {a b : α} {s s' : Ctx} : (pure a : TM α) s = .ok b s' ↔ a = b ∧ s = s' := by
  simp [pure, EStateM.pure]

@[simp] theorem get_ok {s s' c : Ctx} : (get : TM Ctx) s = .ok c s' ↔ c = s ∧ s' = s := by
  simp [get, getThe, MonadStateOf.get, EStateM.get]
  constructor <;> rintro ⟨rfl, rfl⟩ <;> exact ⟨rfl, rfl⟩

@[simp] theorem reject_ne_ok (sp : Span) (r : String) (s s' : Ctx) (a : α) :
    (reject (A := α) sp r) s ≠ .ok a s' := by
  simp [reject, get, getThe, MonadStateOf.get, EStateM.get, throw, throwThe, MonadExceptOf.throw,
    EStateM.throw, bind, EStateM.bind]

@[simp] theorem orReject_ok (o : Option α) (sp : Span) (r : String) (s s' : Ctx) (a : α) :
    (orReject o sp r) s = .ok a s' ↔ o = some a ∧ s = s' := by
  cases o <;> simp [orReject]

@[simp] theorem tooDeep_ne_ok (s s' : Ctx) (a : α) : (tooDeep (A := α)) s ≠ .ok a s' := by
  simp [tooDeep, get, getThe, MonadStateOf.get, EStateM.get, throw, throwThe, MonadExceptOf.throw,
    EStateM.throw, bind, EStateM.bind]

end Monad

/-! ### Environments and calls -/

/-- The interpreter's environment and the output's give every name the same
value. -/
def Agree (ρs ρo : Eval.Env N) : Prop := ∀ n, ρs.lookup n = ρo.lookup n

/-- The interpreter's environment binds exactly the names that the translator
has in scope. So a name out of scope, such as `NaN`, is the global. -/
def Scoped (env : Translate.Env) (ρ : Eval.Env N) : Prop :=
  ∀ n, (ρ.lookup n).isSome = env.has n

omit [JSNumber N] in
theorem Scoped.none {env : Translate.Env} {ρ : Eval.Env N} (h : Scoped env ρ) {n : String}
    (hn : env.has n = false) : ρ.lookup n = none := by
  have := h n; rw [hn] at this; simpa using this

omit [JSNumber N] in
theorem Scoped.some {env : Translate.Env} {ρ : Eval.Env N} (h : Scoped env ρ) {n : String}
    (hn : env.has n = true) : (ρ.lookup n).isSome := by
  rw [h n]; exact hn

/-- A call of the function `name` of the program, as the interpreter runs it. -/
def callS (m : Module) (fuel : Nat) (name : String) (vs : List (Val N)) : Option (Val N) :=
  match fuel with
  | 0 => none
  | fuel + 1 => do
    let (params, body) ← (Eval.functions m).lookup name
    if params.length != vs.length then none
    match ← Eval.execStmt m fuel (params.zip vs).reverse body with
    | .ret v => some v
    | .normal _ => none

/-- A call of the function `name` of the output, as its evaluator runs it. -/
def callO (fs : List (String × List String × Output.Body)) (fuel : Nat) (name : String)
    (vs : List (Val N)) : Option (Val N) :=
  match fuel with
  | 0 => none
  | fuel + 1 => do
    let (params, body) ← fs.lookup name
    if params.length != vs.length then none
    match ← Output.Body.exec fs fuel (params.zip vs).reverse body with
    | .ret v => some v
    | .normal _ => none

/-- Every call that gives a value in the output gives it in the interpreter. -/
def CallsAgree (m : Module) (fs : List (String × List String × Output.Body)) (fuel : Nat) : Prop :=
  ∀ name vs v, callO (N := N) fs fuel name vs = some v → callS m fuel name vs = some v

/-! ### The statement -/

variable (m : Module) (fs : List (String × List String × Output.Body)) (fuel : Nat)

/-- The output code `out` means what the expression `e` means. -/
def Sim (env : Translate.Env) (e : Expr) (out : Output.Expr) : Prop :=
  ∀ (ρs ρo : Eval.Env N) v, Agree ρs ρo → Scoped env ρs →
    Output.Expr.eval fs fuel ρo out = some v → Eval.eval m fuel ρs e = some v

/-- The output codes `outs` mean what the expressions `es` mean. -/
def SimList (env : Translate.Env) (es : List Expr) (outs : List Output.Expr) : Prop :=
  ∀ (ρs ρo : Eval.Env N) vs, Agree ρs ρo → Scoped env ρs →
    Output.Expr.evalList fs fuel ρo outs = some vs → Eval.evalList m fuel ρs es = some vs

theorem isInfinity_eq_true {e : Expr} (h : e.isInfinity = true) : ∃ s, e = .ident s "Infinity" := by
  unfold Expr.isInfinity at h
  split at h
  · next s => exact ⟨s, rfl⟩
  · simp at h

/-- The value of `-e`, from the value of `e`. -/
def negVal : Val N → Option (Val N)
  | .int i => some (.int (-i))
  | .num n => some (.num (JSNumber.neg n))
  | _ => none

/-- The interpreter negates the value of the operand, unless the operand is
the global `Infinity`, which it reads as `negInf`. -/
theorem eval_neg (sp : Span) (arg : Expr) (ρ : Eval.Env N) (v : Val N)
    (h : Eval.eval m fuel ρ arg = some v)
    (hInf : ∀ s, arg = .ident s "Infinity" → (ρ.lookup "Infinity").isSome) :
    Eval.eval m fuel ρ (.unary sp .neg arg) = negVal v := by
  cases arg with
  | ident s name =>
    by_cases hn : name = "Infinity"
    · subst hn
      obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp (hInf s rfl)
      simp only [Eval.eval, hw] at h ⊢
      obtain rfl : w = v := by simpa using h
      cases w <;> simp [negVal]
    · rw [Eval.eval]
      all_goals first
        | (intro _ hc; cases hc; exact hn rfl)
        | (rw [h]; cases v <;> simp [negVal])
  | _ =>
    rw [Eval.eval]
    all_goals first
      | (intro _ hc; cases hc)
      | (rw [h]; cases v <;> simp [negVal])

/-! ### What the output's evaluator says, one form at a time -/

section Inversion

variable {ρ : Eval.Env N} {v : Val N}

theorem out_not {p : Output.Expr} (h : Output.Expr.eval fs fuel ρ (.not p) = some v) :
    ∃ b, Output.Expr.eval fs fuel ρ p = some (.bool b) ∧ v = .bool !b := by
  simp only [Output.Expr.eval] at h
  cases hx : Output.Expr.eval fs fuel ρ p with
  | none => simp [hx] at h
  | some w => cases w <;> simp_all

theorem out_propNot {p : Output.Expr} (h : Output.Expr.eval fs fuel ρ (.propNot p) = some v) :
    ∃ b, Output.Expr.eval fs fuel ρ p = some (.bool b) ∧ v = .bool !b := by
  simp only [Output.Expr.eval] at h
  cases hx : Output.Expr.eval fs fuel ρ p with
  | none => simp [hx] at h
  | some w => cases w <;> simp_all

theorem out_neg {a : Output.Expr} (h : Output.Expr.eval fs fuel ρ (.neg a) = some v) :
    ∃ i, Output.Expr.eval fs fuel ρ a = some (.int i) ∧ v = .int (-i) := by
  simp only [Output.Expr.eval] at h
  cases hx : Output.Expr.eval fs fuel ρ a with
  | none => simp [hx] at h
  | some w => cases w <;> simp_all

theorem out_numberNeg {a : Output.Expr} (h : Output.Expr.eval fs fuel ρ (.numberNeg a) = some v) :
    ∃ n, Output.Expr.eval fs fuel ρ a = some (.num n) ∧ v = .num (JSNumber.neg n) := by
  simp only [Output.Expr.eval] at h
  cases hx : Output.Expr.eval fs fuel ρ a with
  | none => simp [hx] at h
  | some w => cases w <;> simp_all

theorem out_ite {c a b : Output.Expr} (h : Output.Expr.eval fs fuel ρ (.ite c a b) = some v) :
    ∃ t, Output.Expr.eval fs fuel ρ c = some (.bool t) ∧
      (if t then Output.Expr.eval fs fuel ρ a else Output.Expr.eval fs fuel ρ b) = some v := by
  simp only [Output.Expr.eval] at h
  cases hx : Output.Expr.eval fs fuel ρ c with
  | none => simp [hx] at h
  | some w => cases w <;> simp_all

theorem out_numberTest {t : Output.NumberTest} {a : Output.Expr}
    (h : Output.Expr.eval fs fuel ρ (.numberTest t a) = some v) :
    ∃ n, Output.Expr.eval fs fuel ρ a = some (.num n) ∧ v = .bool (t.apply n) := by
  simp only [Output.Expr.eval] at h
  cases hx : Output.Expr.eval fs fuel ρ a with
  | none => simp [hx] at h
  | some w => cases w <;> simp_all

theorem out_intOp {op : Output.IntOp} {a b : Output.Expr}
    (h : Output.Expr.eval fs fuel ρ (.intOp op a b) = some v) :
    ∃ x y, Output.Expr.eval fs fuel ρ a = some (.int x) ∧ Output.Expr.eval fs fuel ρ b = some (.int y) ∧
      v = .int (op.apply x y) := by
  simp only [Output.Expr.eval] at h
  cases hx : Output.Expr.eval fs fuel ρ a with
  | none => simp [hx] at h
  | some w =>
    cases hy : Output.Expr.eval fs fuel ρ b with
    | none => cases w <;> simp_all
    | some u => cases w <;> cases u <;> simp_all

theorem out_order {op : Output.Order} {a b : Output.Expr}
    (h : Output.Expr.eval fs fuel ρ (.order op a b) = some v) :
    ∃ x y, Output.Expr.eval fs fuel ρ a = some (.int x) ∧ Output.Expr.eval fs fuel ρ b = some (.int y) ∧
      v = .bool (op.apply x y) := by
  simp only [Output.Expr.eval] at h
  cases hx : Output.Expr.eval fs fuel ρ a with
  | none => simp [hx] at h
  | some w =>
    cases hy : Output.Expr.eval fs fuel ρ b with
    | none => cases w <;> simp_all
    | some u => cases w <;> cases u <;> simp_all

theorem out_division {op : Output.Division} {a b : Output.Expr}
    (h : Output.Expr.eval fs fuel ρ (.division op a b) = some v) :
    ∃ x y, Output.Expr.eval fs fuel ρ a = some (.int x) ∧ Output.Expr.eval fs fuel ρ b = some (.int y) ∧
      v = .int (op.apply x y) := by
  simp only [Output.Expr.eval] at h
  cases hx : Output.Expr.eval fs fuel ρ a with
  | none => simp [hx] at h
  | some w =>
    cases hy : Output.Expr.eval fs fuel ρ b with
    | none => cases w <;> simp_all
    | some u => cases w <;> cases u <;> simp_all

theorem out_numberOp {op : Output.NumberOp} {a b : Output.Expr}
    (h : Output.Expr.eval fs fuel ρ (.numberOp op a b) = some v) :
    ∃ x y, Output.Expr.eval fs fuel ρ a = some (.num x) ∧ Output.Expr.eval fs fuel ρ b = some (.num y) ∧
      v = op.apply x y := by
  simp only [Output.Expr.eval] at h
  cases hx : Output.Expr.eval fs fuel ρ a with
  | none => simp [hx] at h
  | some w =>
    cases hy : Output.Expr.eval fs fuel ρ b with
    | none => cases w <;> simp_all
    | some u => cases w <;> cases u <;> simp_all

theorem out_numberNe {a b : Output.Expr}
    (h : Output.Expr.eval fs fuel ρ (.numberNe a b) = some v) :
    ∃ x y, Output.Expr.eval fs fuel ρ a = some (.num x) ∧ Output.Expr.eval fs fuel ρ b = some (.num y) ∧
      v = .bool !(JSNumber.eq x y) := by
  simp only [Output.Expr.eval] at h
  cases hx : Output.Expr.eval fs fuel ρ a with
  | none => simp [hx] at h
  | some w =>
    cases hy : Output.Expr.eval fs fuel ρ b with
    | none => cases w <;> simp_all
    | some u => cases w <;> cases u <;> simp_all

theorem out_eq {a b : Output.Expr} (h : Output.Expr.eval fs fuel ρ (.eq a b) = some v) :
    ∃ x y t, Output.Expr.eval fs fuel ρ a = some x ∧ Output.Expr.eval fs fuel ρ b = some y ∧
      Output.eqVal x y = some t ∧ v = .bool t := by
  simp only [Output.Expr.eval] at h
  cases hx : Output.Expr.eval fs fuel ρ a with
  | none => simp [hx] at h
  | some w =>
    cases hy : Output.Expr.eval fs fuel ρ b with
    | none => simp [hx, hy] at h
    | some u =>
      cases ht : Output.eqVal w u with
      | none => simp [hx, hy, ht] at h
      | some t => simp [hx, hy, ht] at h; exact ⟨w, u, t, rfl, rfl, ht, h.symm⟩

theorem out_ne {a b : Output.Expr} (h : Output.Expr.eval fs fuel ρ (.ne a b) = some v) :
    ∃ x y t, Output.Expr.eval fs fuel ρ a = some x ∧ Output.Expr.eval fs fuel ρ b = some y ∧
      Output.eqVal x y = some t ∧ v = .bool !t := by
  simp only [Output.Expr.eval] at h
  cases hx : Output.Expr.eval fs fuel ρ a with
  | none => simp [hx] at h
  | some w =>
    cases hy : Output.Expr.eval fs fuel ρ b with
    | none => simp [hx, hy] at h
    | some u =>
      cases ht : Output.eqVal w u with
      | none => simp [hx, hy, ht] at h
      | some t => simp [hx, hy, ht] at h; exact ⟨w, u, t, rfl, rfl, ht, h.symm⟩

theorem out_and {a b : Output.Expr}
    (h : Output.Expr.eval fs fuel ρ (.and a b) = some v ∨ Output.Expr.eval fs fuel ρ (.propAnd a b) = some v) :
    ∃ x y, Output.Expr.eval fs fuel ρ a = some (.bool x) ∧ Output.Expr.eval fs fuel ρ b = some (.bool y) ∧
      v = .bool (x && y) := by
  rcases h with h | h <;>
  · simp only [Output.Expr.eval] at h
    cases hx : Output.Expr.eval fs fuel ρ a with
    | none => simp [hx] at h
    | some w =>
      cases hy : Output.Expr.eval fs fuel ρ b with
      | none => cases w <;> simp_all
      | some u => cases w <;> cases u <;> simp_all

theorem out_or {a b : Output.Expr}
    (h : Output.Expr.eval fs fuel ρ (.or a b) = some v ∨ Output.Expr.eval fs fuel ρ (.propOr a b) = some v) :
    ∃ x y, Output.Expr.eval fs fuel ρ a = some (.bool x) ∧ Output.Expr.eval fs fuel ρ b = some (.bool y) ∧
      v = .bool (x || y) := by
  rcases h with h | h <;>
  · simp only [Output.Expr.eval] at h
    cases hx : Output.Expr.eval fs fuel ρ a with
    | none => simp [hx] at h
    | some w =>
      cases hy : Output.Expr.eval fs fuel ρ b with
      | none => cases w <;> simp_all
      | some u => cases w <;> cases u <;> simp_all

/-- Whether a value is `null`. -/
def isNullVal : Val N → Bool
  | .null => true
  | _ => false

theorem out_isNone {a : Output.Expr} (h : Output.Expr.eval fs fuel ρ (.isNone a) = some v) :
    ∃ w, Output.Expr.eval fs fuel ρ a = some w ∧ v = .bool (isNullVal w) := by
  simp only [Output.Expr.eval] at h
  cases hx : Output.Expr.eval fs fuel ρ a with
  | none => simp [hx] at h
  | some w => cases w <;> simp_all [isNullVal]

theorem out_isSome {a : Output.Expr} (h : Output.Expr.eval fs fuel ρ (.isSome a) = some v) :
    ∃ w, Output.Expr.eval fs fuel ρ a = some w ∧ v = .bool !(isNullVal w) := by
  simp only [Output.Expr.eval] at h
  cases hx : Output.Expr.eval fs fuel ρ a with
  | none => simp [hx] at h
  | some w => cases w <;> simp_all [isNullVal]

end Inversion

/-- The output fields `outs` mean what the properties `ps` mean. -/
def SimFields (env : Translate.Env) (ps : List Property) (outs : List (String × Output.Expr)) : Prop :=
  ∀ (ρs ρo : Eval.Env N) fvs, Agree ρs ρo → Scoped env ρs →
    Output.Expr.evalFields fs fuel ρo outs = some fvs → Eval.evalProps m fuel ρs ps = some fvs

/-- The output field `(key, o)` means what the property `p` means: the
interpreter gives `(key, w)` for `p` when `o` has the value `w`. -/
def PropSim (env : Translate.Env) (p : Property) (key : String) (o : Output.Expr) : Prop :=
  ∀ (ρs ρo : Eval.Env N) w, Agree ρs ρo → Scoped env ρs → Output.Expr.eval fs fuel ρo o = some w →
    ∀ rest, Eval.evalProps m fuel ρs (p :: rest) = (Eval.evalProps m fuel ρs rest).map ((key, w) :: ·)

/-- A fold that appends one field for each property, where each field means
what its property means, gives fields that mean what the properties mean. -/
theorem fold_sim {env : Translate.Env} {α : Type}
    {g : α × List (String × Output.Expr) → Property → TM (α × List (String × Output.Expr))}
    (hstep : ∀ a acc p ctx r ctx', g (a, acc) p ctx = .ok r ctx' →
      ∃ key o, r.2 = acc ++ [(key, o)] ∧ PropSim (N := N) m fs fuel env p key o) :
    ∀ (ps : List Property) (a : α) acc ctx r ctx', ps.foldlM g (a, acc) ctx = .ok r ctx' →
      ∃ new, r.2 = acc ++ new ∧ SimFields (N := N) m fs fuel env ps new := by
  intro ps
  induction ps with
  | nil =>
    intro a acc ctx r ctx' h
    simp [List.foldlM_nil] at h
    obtain ⟨rfl, -⟩ := h
    refine ⟨[], by simp, ?_⟩
    intro ρs ρo fvs _ _ hv
    simp [Output.Expr.evalFields] at hv
    subst hv; simp [Eval.evalProps]
  | cons p ps ih =>
    intro a acc ctx r ctx' h
    simp [List.foldlM_cons] at h
    obtain ⟨a₁, acc₁, s₁, h₁, h⟩ := h
    obtain ⟨key, o, hr₁, hp⟩ := hstep _ _ _ _ _ _ h₁
    simp only at hr₁
    subst hr₁
    obtain ⟨new, hnew, hsim⟩ := ih a₁ _ _ _ _ h
    refine ⟨(key, o) :: new, by simp [hnew], ?_⟩
    intro ρs ρo fvs ha hs hv
    simp only [Output.Expr.evalFields] at hv
    cases hx : Output.Expr.eval fs fuel ρo o with
    | none => simp [hx] at hv
    | some w =>
      cases hxs : Output.Expr.evalFields fs fuel ρo new with
      | none => simp [hx, hxs] at hv
      | some ws =>
        simp [hx, hxs] at hv
        subst hv
        rw [hp ρs ρo w ha hs hx ps, hsim ρs ρo ws ha hs hxs]
        rfl

theorem eval_value (c : Code) (ρ : Eval.Env N) :
    Output.Expr.eval fs fuel ρ c.value = Output.Expr.eval fs fuel ρ c.code := by
  unfold Code.value
  split <;> simp [Output.Expr.eval]

/-- When each element's translation means what the element means, the list of
their values means what the list of elements means. -/
theorem mapM_sim {env : Translate.Env} {f : Expr → TM Code}
    (hf : ∀ e ctx c ctx', f e ctx = .ok c ctx' → Sim (N := N) m fs fuel env e c.code) :
    ∀ (es : List Expr) (ctx : Ctx) (codes : List Code) (ctx' : Ctx),
      es.mapM f ctx = .ok codes ctx' → SimList (N := N) m fs fuel env es (codes.map (·.value)) := by
  intro es
  induction es with
  | nil =>
    intro ctx codes ctx' h
    simp [List.mapM_nil] at h
    obtain ⟨rfl, -⟩ := h
    intro ρs ρo vs _ _ hv
    simp [Output.Expr.evalList] at hv
    subst hv; simp [Eval.evalList]
  | cons e es ih =>
    intro ctx codes ctx' h
    simp [List.mapM_cons] at h
    obtain ⟨c, s₁, hc, cs, hcs, rfl⟩ := h
    intro ρs ρo vs ha hs hv
    simp only [List.map_cons, Output.Expr.evalList] at hv
    cases hx : Output.Expr.eval fs fuel ρo c.value with
    | none => simp [hx] at hv
    | some x =>
      cases hxs : Output.Expr.evalList fs fuel ρo (cs.map (·.value)) with
      | none => simp [hx, hxs] at hv
      | some xs =>
        simp [hx, hxs] at hv
        subst hv
        rw [eval_value] at hx
        have h1 := hf _ _ _ _ hc ρs ρo x ha hs hx
        have h2 := ih _ _ _ hcs ρs ρo xs ha hs hxs
        simp [Eval.evalList, h1, h2]

/-- When each argument's translation means what the argument means, the list
of their codes means what the list of arguments means. -/
theorem zip_sim {env : Translate.Env} {g : Expr × Ty → TM Output.Expr}
    (hg : ∀ x t ctx o ctx', g (x, t) ctx = .ok o ctx' → Sim (N := N) m fs fuel env x o) :
    ∀ (args : List Expr) (ps : List Ty) (ctx : Ctx) (vals : List Output.Expr) (ctx' : Ctx),
      args.length = ps.length → (args.zip ps).mapM g ctx = .ok vals ctx' →
      SimList (N := N) m fs fuel env args vals := by
  intro args
  induction args with
  | nil =>
    intro ps ctx vals ctx' _ h
    simp [List.mapM_nil] at h
    obtain ⟨rfl, -⟩ := h
    intro ρs ρo vs _ _ hv
    simp [Output.Expr.evalList] at hv
    subst hv; simp [Eval.evalList]
  | cons x xs ih =>
    intro ps ctx vals ctx' hlen h
    cases ps with
    | nil => simp at hlen
    | cons t ts =>
      simp [List.mapM_cons] at h
      obtain ⟨o, s₁, ho, os, hos, rfl⟩ := h
      intro ρs ρo vs ha hs hv
      simp only [Output.Expr.evalList] at hv
      cases hx : Output.Expr.eval fs fuel ρo o with
      | none => simp [hx] at hv
      | some w =>
        cases hxs : Output.Expr.evalList fs fuel ρo os with
        | none => simp [hx, hxs] at hv
        | some ws =>
          simp [hx, hxs] at hv
          subst hv
          have h1 := hg _ _ _ _ _ ho ρs ρo w ha hs hx
          have h2 := ih ts _ _ _ (by simpa using hlen) hos ρs ρo ws ha hs hxs
          simp [Eval.evalList, h1, h2]

theorem eval_call (sp sp' : Span) (name : String) (args : List Expr) (ρ : Eval.Env N) :
    Eval.eval m fuel ρ (.call sp (.ident sp' name) args) =
      (Eval.evalList m fuel ρ args).bind (callS m fuel name) := by
  rw [Eval.eval]
  cases Eval.evalList m fuel ρ args <;> cases fuel <;> rfl

theorem out_call (name : String) (args : List Output.Expr) (ρ : Eval.Env N) :
    Output.Expr.eval fs fuel ρ (.call name args) =
      (Output.Expr.evalList fs fuel ρ args).bind (callO fs fuel name) := by
  rw [Output.Expr.eval]
  cases Output.Expr.evalList fs fuel ρ args <;> cases fuel <;> rfl

/-- An operator that evaluates both operands: not `&&`, `||` or `??`. -/
def _root_.tolean.TypeScript.Syntax.BinOp.strict : BinOp → Bool
  | .and | .or | .coalesce => false
  | _ => true

theorem eval_binary (sp : Span) (op : BinOp) (l r : Expr) (ρ : Eval.Env N) (hop : op.strict = true) :
    Eval.eval m fuel ρ (.binary sp op l r) =
      (do Eval.binary op (← Eval.eval m fuel ρ l) (← Eval.eval m fuel ρ r)) := by
  cases op <;> simp [BinOp.strict] at hop <;> rw [Eval.eval] <;>
    first | rfl | (intro hc; cases hc)

theorem isNull_eq_true {e : Expr} (h : e.isNull = true) : ∃ s, e = .null s := by
  cases e <;> simp [Expr.isNull] at h ⊢

theorem eval_stripParens (e : Expr) (ρ : Eval.Env N) :
    Eval.eval m fuel ρ e.stripParens = Eval.eval m fuel ρ e := by
  induction e using Expr.stripParens.induct with
  | case1 sp inner ih => simp only [Expr.stripParens, ih]; simp only [Eval.eval]
  | case2 e he => cases e <;> simp_all [Expr.stripParens]

/-- Narrowing changes a type, not the names in scope. -/
theorem narrow_has (env : Translate.Env) (n : String) (t : Ty) (x : String) :
    (env.narrow n t).has x = env.has x := by
  simp only [Env.has, Env.lookup, Env.narrow, List.find?_map, Option.isSome_map]
  congr 2
  funext l
  simp only [Function.comp_apply]
  split <;> rfl

/-- A test that `nullTestOf` finds gives whether the local is `null`. -/
theorem nullTestOf_eval {env : Translate.Env} {l : Expr} {name : String} {isNullTest : Bool}
    {value : Ty} (h : nullTestOf env l = some (name, isNullTest, value)) {ρ : Eval.Env N}
    (hs : Scoped env ρ) :
    ∃ w, ρ.lookup name = some w ∧
      Eval.eval m fuel ρ l = some (.bool (if isNullTest then isNullVal w else !isNullVal w)) := by
  unfold nullTestOf at h
  rw [← eval_stripParens]
  generalize l.stripParens = e at h ⊢
  cases e with
  | binary sp op a b =>
    simp only at h
    split at h
    · simp at h
    · rename_i hop
      have hop' : op = .strictEq ∨ op = .strictNe := by
        revert hop; cases op <;> first | (intro; left; rfl) | (intro; right; rfl) | decide
      have hstrict : op.strict = true := by rcases hop' with rfl | rfl <;> rfl
      rw [eval_binary m fuel sp op a b ρ hstrict]
      split at h
      · rename_i s0 n0 hother
        split at h
        · rename_i n1 b1 t1 hloc
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          have hhas : env.has n0 = true := by simp [Env.has, hloc]
          obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp (hs.some hhas)
          have hid : Eval.eval m fuel ρ (.ident s0 n0) = some w := by simp [Eval.eval, hw]
          refine ⟨w, hw, ?_⟩
          split at hother
          · rename_i hb
            obtain ⟨sb, rfl⟩ := isNull_eq_true hb
            simp only [Option.some.injEq] at hother
            subst hother
            rw [hid]
            rcases hop' with rfl | rfl <;> cases w <;> simp +decide [Eval.eval, Eval.binary, Eval.strictEq, isNullVal]
          · split at hother
            · rename_i _ ha
              obtain ⟨sa, rfl⟩ := isNull_eq_true ha
              simp only [Option.some.injEq] at hother
              subst hother
              rw [hid]
              rcases hop' with rfl | rfl <;> cases w <;>
                simp +decide [Eval.eval, Eval.binary, Eval.strictEq, isNullVal]
            · simp at hother
        · simp at h
      · simp at h
  | _ => simp at h

/-- A nonzero bigint literal has the same nonzero value in every environment. -/
theorem nonzero_literal (e : Expr) (h : isNonzeroBigintLiteral e = true) :
    ∃ y : Int, y ≠ 0 ∧ ∀ ρ : Eval.Env N, Eval.eval m fuel ρ e = some (.int y) := by
  induction e using isNonzeroBigintLiteral.induct with
  | case1 sp inner ih =>
    simp only [isNonzeroBigintLiteral] at h
    obtain ⟨y, hy, he⟩ := ih h
    exact ⟨y, hy, fun ρ => by rw [Eval.eval]; exact he ρ⟩
  | case2 sp inner ih =>
    simp only [isNonzeroBigintLiteral] at h
    obtain ⟨y, hy, he⟩ := ih h
    refine ⟨-y, by omega, fun ρ => ?_⟩
    rw [eval_neg m fuel sp inner ρ _ (he ρ) (fun s hs => by subst hs; simp [isNonzeroBigintLiteral] at h)]
    rfl
  | case3 sp text =>
    simp only [isNonzeroBigintLiteral, bigintValue?] at h
    cases hb : Eval.bigintLiteral text with
    | none => simp [hb] at h
    | some n =>
      simp [hb] at h
      exact ⟨n, h, fun ρ => by simp [Eval.eval, hb]⟩
  | case4 e h1 h2 h3 => simp [isNonzeroBigintLiteral] at h

@[simp] theorem requireFeature_ok (sp : Span) (f : Feature) (s s' : Ctx) (u : Unit) :
    (requireFeature sp f) s = .ok u s' ↔ s.target.supports f = true ∧ s' = s := by
  simp only [requireFeature, bind_ok, get_ok]
  cases ht : s.target.supports f
  · simp [ht]
  · simp only [true_and]
    constructor
    · rintro ⟨a, s₁, ⟨rfl, rfl⟩, h⟩
      simp [ht] at h
      exact h.symm
    · rintro rfl
      exact ⟨s', s', ⟨rfl, rfl⟩, by simp [ht]⟩

/-- The operator step means what the interpreter's rule for the operator
means, when each operand's code means what the operand means. -/
theorem operator_sound {sp s : Span} {op : BinOp} {l r : Expr} {a b c : Code} {ctx ctx' : Ctx}
    {ρs ρo : Eval.Env N} {v : Val N}
    (h : translateOperator s op r a b ctx = .ok c ctx')
    (hl : ∀ w, Output.Expr.eval fs fuel ρo a.code = some w → Eval.eval m fuel ρs l = some w)
    (hr : ∀ w, Output.Expr.eval fs fuel ρo b.code = some w → Eval.eval m fuel ρs r = some w)
    (hv : Output.Expr.eval fs fuel ρo c.code = some v) :
    Eval.eval m fuel ρs (.binary sp op l r) = some v := by
  unfold translateOperator at h
  cases op
  all_goals simp only [ite_state] at h
  all_goals (repeat' split at h)
  all_goals (simp at h)
  all_goals first | obtain ⟨rfl, -⟩ := h | obtain ⟨⟨-, -⟩, rfl⟩ := h
  all_goals try (exfalso; contradiction)
  all_goals simp only at hv
  -- `&&` and `||` short-circuit, so the interpreter's rule is not `Eval.binary`.
  case and.isTrue.isTrue.isTrue | and.isTrue.isFalse.isTrue =>
    first
      | obtain ⟨x, y, hx, hy, rfl⟩ := out_and fs fuel (.inr hv)
      | obtain ⟨x, y, hx, hy, rfl⟩ := out_and fs fuel (.inl hv)
    try simp only [eval_value] at hx hy
    rw [Eval.eval, hl _ hx]
    cases x <;> simp [Val.truthy, hr _ hy]
  case or.isTrue.isTrue.isFalse | or.isTrue.isFalse.isFalse =>
    first
      | obtain ⟨x, y, hx, hy, rfl⟩ := out_or fs fuel (.inr hv)
      | obtain ⟨x, y, hx, hy, rfl⟩ := out_or fs fuel (.inl hv)
    try simp only [eval_value] at hx hy
    rw [Eval.eval, hl _ hx]
    cases x <;> simp [Val.truthy, hr _ hy]
  all_goals rw [eval_binary m fuel sp _ l r ρs rfl]
  all_goals first
    | (obtain ⟨x, y, hx, hy, rfl⟩ := out_numberOp fs fuel hv
       rw [eval_value] at hx hy
       first
         | (rw [hl _ hx, hr _ hy]; rfl)
         | (rw [hl _ hy, hr _ hx]; rfl))
    | (obtain ⟨x, y, hx, hy, rfl⟩ := out_numberNe fs fuel hv
       rw [eval_value] at hx hy
       rw [hl _ hx, hr _ hy]; rfl)
    | (obtain ⟨x, y, hx, hy, rfl⟩ := out_intOp fs fuel hv
       rw [eval_value] at hx hy
       rw [hl _ hx, hr _ hy]; rfl)
    | (obtain ⟨x, y, hx, hy, rfl⟩ := out_order fs fuel hv
       rw [eval_value] at hx hy
       rw [hl _ hx, hr _ hy]; rfl)
    | (obtain ⟨x, y, hx, hy, rfl⟩ := out_division fs fuel hv
       rw [eval_value] at hx hy
       have hnz : isNonzeroBigintLiteral r = true := by simp_all
       obtain ⟨y0, hy0, he⟩ := nonzero_literal m fuel (N := N) r hnz
       have hyr := hr _ hy
       rw [he ρs] at hyr
       obtain rfl : y0 = y := by simpa using hyr
       rw [hl _ hx, hr _ hy]
       simp [Eval.binary, hy0, Output.Division.apply])
    | (obtain ⟨x, y, t, hx, hy, ht, rfl⟩ := out_eq fs fuel hv
       rw [eval_value] at hx hy
       rw [hl _ hx, hr _ hy]
       cases x <;> cases y <;> simp_all [Output.eqVal, Eval.binary, Eval.strictEq])
    | (obtain ⟨x, y, t, hx, hy, ht, rfl⟩ := out_ne fs fuel hv
       rw [eval_value] at hx hy
       rw [hl _ hx, hr _ hy]
       cases x <;> cases y <;> simp_all [Output.eqVal, Eval.binary, Eval.strictEq])

theorem expr_sound (hc : CallsAgree (N := N) m fs fuel) (F : Nat) :
    (∀ env exp e ctx c ctx', translateExpr F env exp e ctx = .ok c ctx' →
      Sim (N := N) m fs fuel env e c.code) ∧
    (∀ env exp s es ctx r ctx', translateElements F env exp s es ctx = .ok r ctx' →
      SimList (N := N) m fs fuel env es r.1) ∧
    (∀ env exp s es ctx c ctx', translateArray F env exp s es ctx = .ok c ctx' →
      Sim (N := N) m fs fuel env (.array s es) c.code) ∧
    (∀ env s callee args ctx c ctx', translateCall F env s callee args ctx = .ok c ctx' →
      Sim (N := N) m fs fuel env (.call s callee args) c.code) ∧
    (∀ env exp s ps ctx c ctx', translateObject F env exp s ps ctx = .ok c ctx' →
      Sim (N := N) m fs fuel env (.object s ps) c.code) ∧
    (∀ env s op l r ctx c ctx', translateBinary F env s op l r ctx = .ok c ctx' →
      Sim (N := N) m fs fuel env (.binary s op l r) c.code) := by
  induction F with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;>
      simp_all [translateExpr, translateElements, translateArray, translateCall, translateObject,
        translateBinary]
  | succ F ih =>
    obtain ⟨ihE, ihL, ihA, ihC, ihO, ihB⟩ := ih
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro env exp e ctx c ctx' h
      cases e with
      | paren sp inner =>
        simp only [translateExpr] at h
        intro ρs ρo v ha hs hv
        rw [Eval.eval]
        exact ihE _ _ _ _ _ _ h ρs ρo v ha hs hv
      | bigint sp text =>
        simp only [translateExpr] at h
        simp at h
        obtain ⟨n, ⟨hv, -⟩, rfl⟩ := h
        intro ρs ρo v _ _ hv'
        simp [Output.Expr.eval] at hv'
        subst hv'
        simp [Eval.eval]; simpa [bigintValue?] using hv
      | number sp text =>
        simp only [translateExpr] at h
        simp at h
        obtain ⟨n, ⟨hv, -⟩, rfl⟩ := h
        intro ρs ρo v _ _ hv'
        simp [Output.Expr.eval] at hv'
        subst hv'
        simp [Eval.eval]; exact ⟨n, by simpa [safeIntegerValue?] using hv, rfl⟩
      | null sp =>
        simp [translateExpr] at h
        obtain ⟨rfl, -⟩ := h
        intro ρs ρo v _ _ hv'
        simp [Output.Expr.eval] at hv'
        subst hv'; simp [Eval.eval]
      | bool sp b =>
        simp [translateExpr] at h
        obtain ⟨rfl, -⟩ := h
        intro ρs ρo v _ _ hv'
        simp [Output.Expr.eval] at hv'
        subst hv'; simp [Eval.eval]
      | string sp str =>
        simp [translateExpr] at h
        obtain ⟨rfl, -⟩ := h
        intro ρs ρo v _ _ hv'
        simp [Output.Expr.eval] at hv'
        subst hv'; simp [Eval.eval]
      | ident sp name =>
        simp only [translateExpr] at h
        intro ρs ρo v ha hs hv'
        cases hl : env.lookup name with
        | none =>
          simp only [hl] at h
          cases hk : numberConstant? name with
          | none => simp [hk] at h
          | some k =>
            simp [hk] at h
            obtain ⟨rfl, -⟩ := h
            have hnone : ρs.lookup name = none := hs.none (by simp [Translate.Env.has, hl])
            simp [Output.Expr.eval] at hv'
            subst hv'
            unfold numberConstant? at hk
            split at hk
            · cases hk; simp only [Eval.eval, hnone]; simp [Output.NumberConstant.value]
            · cases hk; simp only [Eval.eval, hnone]; simp [Output.NumberConstant.value]
            · cases hk
        | some l =>
          simp only [hl] at h
          simp at h
          obtain ⟨_, _, ⟨rfl, rfl⟩, h⟩ := h
          have hc : c.code = .var name := by
            split at h
            · simp at h
            · simp at h; rw [← h.1]
          rw [hc] at hv'
          simp only [Output.Expr.eval] at hv'
          rw [← ha name] at hv'
          simp only [Eval.eval, hv']
      | member sp obj name =>
        simp only [translateExpr] at h
        simp at h
        obtain ⟨o, s₁, ho, _, _, ⟨rfl, rfl⟩, ty, ⟨-, rfl⟩, rfl⟩ := h
        intro ρs ρo v ha hs hv'
        simp only [Output.Expr.eval] at hv'
        cases hobj : Output.Expr.eval fs fuel ρo o.code with
        | none => simp [hobj] at hv'
        | some ov =>
          have := ihE _ _ _ _ _ _ ho ρs ρo ov ha hs hobj
          simp only [Eval.eval, this]
          simpa [hobj] using hv'
      | unary sp op arg =>
        simp only [translateExpr] at h
        intro ρs ρo v ha hs hv'
        cases op with
        | not =>
          simp +decide at h
          obtain ⟨a, s₁, hta, h⟩ := h
          split at h
          · simp at h
            obtain ⟨hcode, -⟩ := h
            rw [← hcode] at hv'
            have key : ∃ b, Output.Expr.eval fs fuel ρo a.code = some (.bool b) ∧ v = .bool !b := by
              by_cases hp : a.prop = true
              · simp only [hp, if_true] at hv'; exact out_propNot fs fuel hv'
              · simp only [hp] at hv'; exact out_not fs fuel hv'
            obtain ⟨b, hb, rfl⟩ := key
            have := ihE _ _ _ _ _ _ hta ρs ρo _ ha hs hb
            simp [Eval.eval, this, Val.truthy]
          · simp at h
        | neg =>
          simp +decide at h
          split at h
          · next hcond =>
            simp at h
            obtain ⟨hcode, -⟩ := h
            rw [← hcode] at hv'
            simp [Output.Expr.eval, Output.NumberConstant.value] at hv'
            subst hv'
            obtain ⟨hm, hhas⟩ := hcond
            have hnone := hs.none hhas
            obtain ⟨s', rfl⟩ := isInfinity_eq_true hm
            simp only [Eval.eval, hnone]
          · next hcond =>
            simp at h
            obtain ⟨a, s₁, hta, h⟩ := h
            have hInf : ∀ s', arg = .ident s' "Infinity" → (ρs.lookup "Infinity").isSome := by
              rintro s' rfl
              apply hs.some
              simpa [Expr.isInfinity] using hcond
            cases ht : a.type <;> simp [ht] at h
            · obtain ⟨hcode, -⟩ := h
              rw [← hcode] at hv'
              obtain ⟨i, hi, rfl⟩ := out_neg fs fuel hv'
              rw [eval_value] at hi
              have := ihE _ _ _ _ _ _ hta ρs ρo _ ha hs hi
              rw [eval_neg m fuel sp arg ρs _ this hInf]; rfl
            · obtain ⟨hcode, -⟩ := h
              rw [← hcode] at hv'
              obtain ⟨n, hn, rfl⟩ := out_numberNeg fs fuel hv'
              rw [eval_value] at hn
              have := ihE _ _ _ _ _ _ hta ρs ρo _ ha hs hn
              rw [eval_neg m fuel sp arg ρs _ this hInf]; rfl
        | _ => simp +decide at h
      | binary sp op l r =>
        simp only [translateExpr] at h
        exact ihB _ _ _ _ _ _ _ _ h
      | call sp callee args =>
        simp only [translateExpr] at h
        exact ihC _ _ _ _ _ _ _ h
      | object sp props =>
        simp only [translateExpr] at h
        exact ihO _ _ _ _ _ _ _ h
      | array sp elems =>
        simp only [translateExpr] at h
        exact ihA _ _ _ _ _ _ _ h
      | cond sp test ifTrue ifFalse =>
        simp only [translateExpr] at h
        simp at h
        obtain ⟨tc, s₁, htc, h⟩ := h
        split at h
        · simp at h
          obtain ⟨ta, s₂, hta, tb, s₃, htb, h⟩ := h
          obtain ⟨ty, ⟨-, -⟩, hcode⟩ := h
          intro ρs ρo v ha hs hv'
          rw [← hcode] at hv'
          obtain ⟨t, ht, hbr⟩ := out_ite fs fuel hv'
          have htest := ihE _ _ _ _ _ _ htc ρs ρo _ ha hs ht
          simp only [Eval.eval, htest, Option.bind_eq_bind, Option.bind_some, Val.truthy]
          cases t
          · simp only [eval_value] at hbr ⊢
            exact ihE _ _ _ _ _ _ htb ρs ρo _ ha hs hbr
          · simp only [if_true, eval_value] at hbr ⊢
            exact ihE _ _ _ _ _ _ hta ρs ρo _ ha hs hbr
        · simp at h
      | _ => simp [translateExpr] at h
    · intro env exp sp es ctx r ctx' h
      simp only [translateElements] at h
      simp at h
      obtain ⟨codes, s₁, hcodes, elem, s₂, -, -, hr⟩ := h
      rw [← hr]
      exact mapM_sim m fs fuel (fun e ctx c ctx' h => ihE _ _ _ _ _ _ h) es ctx codes s₁ hcodes
    · intro env exp sp es ctx c ctx' h
      simp only [translateArray] at h
      simp at h
      obtain ⟨values, elem, hel, hcode⟩ := h
      intro ρs ρo v ha hs hv
      rw [← hcode] at hv
      simp only [Output.Expr.eval] at hv
      cases hx : Output.Expr.evalList fs fuel ρo values with
      | none => simp [hx] at hv
      | some xs =>
        simp [hx] at hv
        subst hv
        have := ihL _ _ _ _ _ _ _ hel ρs ρo xs ha hs hx
        simp [Eval.eval, this]
    · intro env sp callee args ctx c ctx' h
      simp only [translateCall] at h
      cases callee <;> simp at h
      case ident sp' name =>
        obtain ⟨_, _, ⟨rfl, rfl⟩, h⟩ := h
        split at h
        · simp at h
        · simp at h
          obtain ⟨fn, s₁, ⟨-, rfl⟩, h⟩ := h
          split at h
          · simp at h
          · split at h
            · next hlen =>
              simp at h
              obtain ⟨vals, hvals, hcode⟩ := h
              intro ρs ρo v ha hs hv
              rw [← hcode] at hv
              simp only at hv
              rw [out_call] at hv
              cases hx : Output.Expr.evalList fs fuel ρo vals with
              | none => simp [hx] at hv
              | some vs =>
                simp [hx] at hv
                have hargs := zip_sim m fs fuel ?hg args fn.params _ vals _ hlen.symm hvals
                  ρs ρo vs ha hs hx
                · rw [eval_call, hargs]; exact hc _ _ _ hv
                case hg =>
                  intro x t c₀ o c₁ hgo
                  simp at hgo
                  obtain ⟨a, s₂, hta, hgo⟩ := hgo
                  split at hgo
                  · simp at hgo
                    obtain ⟨rfl, -⟩ := hgo
                    intro ρs' ρo' w ha' hs' hw
                    rw [eval_value] at hw
                    exact ihE _ _ _ _ _ _ hta ρs' ρo' w ha' hs' hw
                  · simp at hgo
            · simp at h
      case member sp' obj test =>
        cases obj
        case ident sp'' oname =>
          by_cases hn : oname = "Number"
          · subst hn
            simp at h
            cases hN : env.has "Number" <;> simp [hN] at h
            cases hT : numberTest? test <;> simp [hT] at h
            rename_i form
            match args, h with
            | [arg], h =>
              simp at h
              obtain ⟨a, s₁, hta, h⟩ := h
              split at h
              · simp at h
                obtain ⟨hcode, -⟩ := h
                intro ρs ρo v ha hs hv
                rw [← hcode] at hv
                obtain ⟨n, hn, rfl⟩ := out_numberTest fs fuel hv
                rw [eval_value] at hn
                have harg := ihE _ _ _ _ _ _ hta ρs ρo _ ha hs hn
                have hnone := hs.none hN
                unfold numberTest? at hT
                split at hT <;> cases hT <;>
                  simp [Eval.eval, hnone, harg, Output.NumberTest.apply]
              · simp at h
            | [], h => simp at h
            | _ :: _ :: _, h => simp at h
          · simp [hn] at h
        all_goals simp at h
    · intro env exp sp props ctx c ctx' h
      simp only [translateObject] at h
      simp at h
      obtain ⟨_, _, ⟨rfl, rfl⟩, h⟩ := h
      cases exp with
      | none => simp at h
      | some t =>
        cases t <;> simp at h
        rename_i structName
        obtain ⟨info, _, ⟨-, rfl⟩, seen, parts, s₂, hfold, h⟩ := h
        have hparts : c.code = .struct parts structName := by
          obtain ⟨_, _, -, h⟩ := h
          split at h
          · simp at h; rw [← h.1]
          · simp at h
        have key := fold_sim (N := N) (env := env) m fs fuel ?hstep props [] [] _ _ _ hfold
        · obtain ⟨new, hnew, hsim⟩ := key
          intro ρs ρo v ha hs hv
          rw [hparts] at hv
          simp only at hnew
          rw [hnew] at hv
          simp only [Output.Expr.eval, List.nil_append] at hv
          cases hx : Output.Expr.evalFields fs fuel ρo new with
          | none => simp [hx] at hv
          | some fvs =>
            simp [hx] at hv
            subst hv
            simp [Eval.eval, hsim ρs ρo fvs ha hs hx]
        case hstep =>
          intro a acc p c₀ r c₁ hg
          cases p with
          | shorthand ps name =>
            simp at hg
            obtain ⟨fieldType, _, ⟨-, rfl⟩, hg⟩ := hg
            split at hg
            · simp at hg
            · simp at hg
              obtain ⟨v, _, hv, hg⟩ := hg
              split at hg
              · simp at hg
                obtain ⟨rfl, -⟩ := hg
                refine ⟨name, v.value, rfl, ?_⟩
                intro ρs ρo w ha hs hw rest
                rw [eval_value] at hw
                have := ihE _ _ _ _ _ _ hv ρs ρo w ha hs hw
                simp [Eval.evalProps, this]
                cases Eval.evalProps m fuel ρs rest <;> rfl
              · simp at hg
          | keyValue ps key val =>
            cases key with
            | ident key =>
              simp at hg
              obtain ⟨fieldType, _, ⟨-, rfl⟩, hg⟩ := hg
              split at hg
              · simp at hg
              · simp at hg
                obtain ⟨v, _, hv, hg⟩ := hg
                split at hg
                · simp at hg
                  obtain ⟨rfl, -⟩ := hg
                  refine ⟨key, v.value, rfl, ?_⟩
                  intro ρs ρo w ha hs hw rest
                  rw [eval_value] at hw
                  have := ihE _ _ _ _ _ _ hv ρs ρo w ha hs hw
                  simp [Eval.evalProps, this]
                  cases Eval.evalProps m fuel ρs rest <;> rfl
                · simp at hg
            | _ => simp at hg
    · intro env sp op l r ctx c ctx' h
      unfold translateBinary at h
      simp only [ite_state] at h
      -- The general path: both operands, then the operator.
      have general : ∀ {s₀ : Ctx}, (translateExpr F env none l >>= fun a => do
            let b ← translateExpr F env none r
            translateOperator sp op r a b) s₀ = .ok c ctx' →
          Sim (N := N) m fs fuel env (.binary sp op l r) c.code := by
        intro s₀ h
        simp only [bind_ok] at h
        obtain ⟨a, s₁, ha, b, s₂, hb, ho⟩ := h
        intro ρs ρo v hag hs hv
        exact operator_sound m fs fuel ho (fun w hw => ihE _ _ _ _ _ _ ha ρs ρo w hag hs hw)
          (fun w hw => ihE _ _ _ _ _ _ hb ρs ρo w hag hs hw) hv
      split at h
      · -- `x === null` and `x !== null`.
        rename_i hnull
        have hop : op = .strictEq ∨ op = .strictNe := by
          revert hnull
          cases op <;> first | (intro; left; rfl) | (intro; right; rfl) | (intro h; simp +decide at h)
        have hside : l.isNull = true ∨ r.isNull = true := by
          simpa using ((Bool.and_eq_true _ _).mp hnull).2
        generalize hother : (if l.isNull = true then r else l) = other at h
        split at h
        · simp at h
        · simp only [pure_bind, bind_ok] at h
          obtain ⟨o, s₁, ho, h⟩ := h
          cases hty : o.type <;> simp [hty] at h
          obtain ⟨rfl, -⟩ := h
          subst hother
          intro ρs ρo v hag hs hv
          have key := fun w hw => ihE _ _ _ _ _ _ ho ρs ρo w hag hs hw
          rw [eval_binary m fuel sp op l r ρs (by rcases hop with rfl | rfl <;> rfl)]
          rcases hop with rfl | rfl <;> simp +decide only [ite_true, ite_false] at hv
          all_goals first
            | obtain ⟨w, hw, rfl⟩ := out_isNone fs fuel hv
            | obtain ⟨w, hw, rfl⟩ := out_isSome fs fuel hv
          all_goals
            have hw' := key w hw
            by_cases hl : l.isNull = true
            · obtain ⟨sl, rfl⟩ := isNull_eq_true hl
              simp [Expr.isNull] at hw'
              rw [hw']
              cases w <;> simp +decide [Eval.eval, Eval.binary, Eval.strictEq, isNullVal]
            · have hr : r.isNull = true := by simpa [hl] using hside
              obtain ⟨sr, rfl⟩ := isNull_eq_true hr
              simp [hl] at hw'
              rw [hw']
              cases w <;> simp +decide [Eval.eval, Eval.binary, Eval.strictEq, isNullVal]
      · cases hn : nullTestOf env l with
        | none =>
          simp only [hn, pure_bind] at h
          exact general h
        | some t =>
          obtain ⟨name, isNullTest, value⟩ := t
          simp only [hn, pure_bind] at h
          split at h
          · -- `x === null || e` and `x !== null && e`: `e` sees `x` narrowed.
            rename_i hcond
            simp only [bind_ok, ite_state] at h
            obtain ⟨ws, s₁, hws, h⟩ := h
            split at h
            · simp at h
              obtain ⟨rfl, -⟩ := h
              intro ρs ρo v hag hs hv
              obtain ⟨w, hw, hl⟩ := nullTestOf_eval m fuel hn hs
              have hso : ρo.lookup name = some w := by rw [← hag]; exact hw
              have hs' : Scoped (env.narrow name value) ρs := fun x => by rw [narrow_has]; exact hs x
              have hr := fun u hu => ihE _ _ _ _ _ _ hws ρs ρo u hag hs' hu
              have hcases : (op = .or ∧ isNullTest = true) ∨ (op = .and ∧ isNullTest = false) := by
                revert hcond; cases op <;> cases isNullTest <;> simp +decide
              rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rw [Eval.eval, hl] <;>
                cases w <;> simp +decide [Output.Expr.eval, hso, isNullVal, Val.truthy, eval_value] at hv ⊢
              all_goals first | exact hr v hv | (subst hv; rfl) | (subst hv; simp +decide)
            · simp at h
          · exact general h

end tolean.TypeScript.Proof
