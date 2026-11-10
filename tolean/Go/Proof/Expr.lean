import tolean.Go.Translate.Pure
import tolean.Go.IR.Eval

/-!
The translation of an expression means what the expression means.

`expr_sound` states it for `translateExpr`: when the translator gives code
for an expression, and the code evaluates to a value in the IR's evaluator,
the interpreter gives the same value for the expression. The two
environments must agree on every name, and the interpreter's must bind
exactly the names of the translator's scope, so that `true` is the
predeclared name and a call finds a function.

A call runs the body of a function, which is a statement, so this file takes
the agreement of calls as a hypothesis, `CallsAgree`. `Proof/Package.lean`
proves it.
-/
namespace tolean.Go.Proof

open tolean.Go tolean.Go.Syntax tolean.Go.Pure
open tolean.Go.Eval (Val Outcome BinOp)

/-! ### The translator's monad -/

section Monad

variable {ε α β : Type}

@[simp] theorem bind_ok {x : Except ε α} {f : α → Except ε β} {b : β} :
    (x >>= f) = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x <;> simp [bind, Except.bind]

@[simp] theorem pure_ok {a b : α} : (pure a : Except ε α) = .ok b ↔ a = b := by
  simp [pure, Except.pure]

@[simp] theorem throw_ne_ok {e : ε} {a : α} : (throw e : Except ε α) ≠ .ok a := by
  simp [throw, throwThe, MonadExceptOf.throw]

@[simp] theorem reject_ne_ok {sp : Span} {r : String} {a : α} : reject sp r ≠ .ok a := by
  simp [reject]

theorem ite_ok {c : Prop} [Decidable c] {x y : Except ε α} {b : α} :
    (if c then x else y) = .ok b ↔ (c ∧ x = .ok b) ∨ (¬c ∧ y = .ok b) := by
  split <;> simp_all

end Monad

/-- Take apart a translator step that gave a value: each bind gives a value,
and each test that would refuse passed. -/
macro "tm_simp" " at " h:ident : tactic =>
  `(tactic| simp only [bind_ok, ite_ok, pure_bind, pure_ok, reject_ne_ok, throw_ne_ok, false_and,
    and_false, or_false, false_or, exists_false, exists_const, and_true, true_and, not_false_eq_true,
    not_true_eq_false, eq_self_iff_true, List.isEmpty_nil, Bool.false_eq_true, ↓reduceIte] at $h:ident)


/-! ### Environments and calls -/

/-- The interpreter's environment and the output's give every name the same
value. -/
def Agree (ρs ρo : Eval.Env) : Prop := ∀ n, ρs.lookup n = ρo.lookup n

/-- The interpreter binds exactly the names of the translator's scope. -/
def Scoped (env : Pure.Env) (ρ : Eval.Env) : Prop := ∀ n, (ρ.lookup n).isSome = env.has n

theorem Agree.refl (ρ : Eval.Env) : Agree ρ ρ := fun _ => rfl

/-- The functions of the output, as the IR's evaluator finds them. -/
abbrev Funcs := List (DeclRef × List String × IR.Body)

/-- A call of the function `f` of the program, as the interpreter runs it. -/
def callS (p : Eval.Program) (fuel : Nat) (f : String) (vs : List Val) : Option Val :=
  match fuel with
  | 0 => none
  | fuel + 1 => do
    let (params, body) ← p.funcs.lookup f
    if params.length != vs.length then none
    match ← Eval.execStmt p fuel (params.zip vs).reverse body with
    | .ret v => some v
    | .normal _ => none

/-- A call of the function `ref` of the output, as the IR's evaluator runs
it. -/
def callO (fs : Funcs) (fuel : Nat) (ref : DeclRef) (vs : List Val) : Option Val :=
  match fuel with
  | 0 => none
  | fuel + 1 => do
    let (params, body) ← fs.lookup ref
    if params.length != vs.length then none
    match ← IR.Body.exec fs fuel (params.zip vs).reverse body with
    | .ret v => some v
    | .normal _ => none

/-- Each call of the output that gives a value is a call that gives the same
value in the interpreter. -/
def CallsAgree (p : Eval.Program) (fs : Funcs) (fuel : Nat) : Prop :=
  ∀ f vs v, callO fs fuel ⟨"", f⟩ vs = some v → callS p fuel f vs = some v

theorem eval_call (p : Eval.Program) (fuel : Nat) (ρ : Eval.Env) (sp sp' : Span) (f : String)
    (args : List Expr) :
    Eval.eval p fuel ρ (.call sp (.ident sp' f) args false) =
      if (ρ.lookup f).isSome then none else (Eval.evalList p fuel ρ args).bind (callS p fuel f) := by
  rw [Eval.eval]
  cases fuel <;> rfl

theorem out_call (fs : Funcs) (fuel : Nat) (ρ : Eval.Env) (ref : DeclRef) (args : List IR.Expr) :
    IR.Expr.eval fs fuel ρ (.call ref args) = (IR.Expr.evalList fs fuel ρ args).bind (callO fs fuel ref) := by
  rw [IR.Expr.eval]
  cases fuel <;> rfl

/-! ### The output's operations -/

variable {fs : Funcs} {fuel : Nat} {ρ : Eval.Env} {v : Val}

theorem out_wrap64 {a : IR.Expr} (h : IR.Expr.eval fs fuel ρ (.wrap64 a) = some v) :
    ∃ i, IR.Expr.eval fs fuel ρ a = some (.int i) ∧ v = .int (wrap64 i) := by
  simp only [IR.Expr.wrap64, IR.Expr.eval, IR.Expr.evalList] at h
  cases ha : IR.Expr.eval fs fuel ρ a with
  | none => simp [ha] at h
  | some w =>
    cases w <;> simp [ha, IR.ExprExt.apply] at h
    exact ⟨_, rfl, h.symm⟩

theorem out_append {a b : IR.Expr} (h : IR.Expr.eval fs fuel ρ (.append a b) = some v) :
    ∃ x y, IR.Expr.eval fs fuel ρ a = some (.str x) ∧ IR.Expr.eval fs fuel ρ b = some (.str y) ∧
      v = .str (x ++ y) := by
  simp only [IR.Expr.append, IR.Expr.eval, IR.Expr.evalList] at h
  cases ha : IR.Expr.eval fs fuel ρ a with
  | none => simp [ha] at h
  | some wa =>
    cases hb : IR.Expr.eval fs fuel ρ b with
    | none => simp [ha, hb] at h
    | some wb =>
      cases wa <;> cases wb <;> simp [ha, hb, IR.ExprExt.apply] at h
      exact ⟨_, _, rfl, rfl, h.symm⟩

theorem out_neg {a : IR.Expr} (h : IR.Expr.eval fs fuel ρ (.neg a) = some v) :
    ∃ i, IR.Expr.eval fs fuel ρ a = some (.int i) ∧ v = .int (-i) := by
  simp only [IR.Expr.eval] at h
  cases ha : IR.Expr.eval fs fuel ρ a with
  | none => simp [ha] at h
  | some w => cases w <;> simp [ha] at h; exact ⟨_, rfl, h.symm⟩

theorem out_not {a : IR.Expr} (h : IR.Expr.eval fs fuel ρ (.not a) = some v) :
    ∃ b, IR.Expr.eval fs fuel ρ a = some (.bool b) ∧ v = .bool !b := by
  simp only [IR.Expr.eval] at h
  cases ha : IR.Expr.eval fs fuel ρ a with
  | none => simp [ha] at h
  | some w => cases w <;> simp [ha] at h; exact ⟨_, rfl, h.symm⟩

theorem out_intOp {op : tolean.IR.IntOp} {a b : IR.Expr}
    (h : IR.Expr.eval fs fuel ρ (.intOp op a b) = some v) :
    ∃ x y, IR.Expr.eval fs fuel ρ a = some (.int x) ∧ IR.Expr.eval fs fuel ρ b = some (.int y) ∧
      v = .int (op.apply x y) := by
  simp only [IR.Expr.eval] at h
  cases ha : IR.Expr.eval fs fuel ρ a with
  | none => simp [ha] at h
  | some wa =>
    cases hb : IR.Expr.eval fs fuel ρ b with
    | none => cases wa <;> simp [ha, hb] at h
    | some wb => cases wa <;> cases wb <;> simp [ha, hb] at h; exact ⟨_, _, rfl, rfl, h.symm⟩

theorem out_order {op : tolean.IR.Order} {a b : IR.Expr}
    (h : IR.Expr.eval fs fuel ρ (.order op a b) = some v) :
    ∃ x y, IR.Expr.eval fs fuel ρ a = some (.int x) ∧ IR.Expr.eval fs fuel ρ b = some (.int y) ∧
      v = .bool (op.apply x y) := by
  simp only [IR.Expr.eval] at h
  cases ha : IR.Expr.eval fs fuel ρ a with
  | none => simp [ha] at h
  | some wa =>
    cases hb : IR.Expr.eval fs fuel ρ b with
    | none => cases wa <;> simp [ha, hb] at h
    | some wb => cases wa <;> cases wb <;> simp [ha, hb] at h; exact ⟨_, _, rfl, rfl, h.symm⟩

theorem out_eq {a b : IR.Expr} (h : IR.Expr.eval fs fuel ρ (.eq a b) = some v) :
    ∃ x y r, IR.Expr.eval fs fuel ρ a = some x ∧ IR.Expr.eval fs fuel ρ b = some y ∧
      Eval.eqVal x y = some r ∧ v = .bool r := by
  simp only [IR.Expr.eval] at h
  cases ha : IR.Expr.eval fs fuel ρ a with
  | none => simp [ha] at h
  | some wa =>
    cases hb : IR.Expr.eval fs fuel ρ b with
    | none => simp [ha, hb] at h
    | some wb =>
      cases he : Eval.eqVal wa wb with
      | none => simp [ha, hb, he] at h
      | some r => simp [ha, hb, he] at h; exact ⟨_, _, _, rfl, rfl, he, h.symm⟩

theorem out_ne {a b : IR.Expr} (h : IR.Expr.eval fs fuel ρ (.ne a b) = some v) :
    ∃ x y r, IR.Expr.eval fs fuel ρ a = some x ∧ IR.Expr.eval fs fuel ρ b = some y ∧
      Eval.eqVal x y = some r ∧ v = .bool !r := by
  simp only [IR.Expr.eval] at h
  cases ha : IR.Expr.eval fs fuel ρ a with
  | none => simp [ha] at h
  | some wa =>
    cases hb : IR.Expr.eval fs fuel ρ b with
    | none => simp [ha, hb] at h
    | some wb =>
      cases he : Eval.eqVal wa wb with
      | none => simp [ha, hb, he] at h
      | some r => simp [ha, hb, he] at h; exact ⟨_, _, _, rfl, rfl, he, h.symm⟩

theorem out_and {a b : IR.Expr} (h : IR.Expr.eval fs fuel ρ (.and a b) = some v) :
    ∃ x y, IR.Expr.eval fs fuel ρ a = some (.bool x) ∧ IR.Expr.eval fs fuel ρ b = some (.bool y) ∧
      v = .bool (x && y) := by
  simp only [IR.Expr.eval] at h
  cases ha : IR.Expr.eval fs fuel ρ a with
  | none => simp [ha] at h
  | some wa =>
    cases hb : IR.Expr.eval fs fuel ρ b with
    | none => cases wa <;> simp [ha, hb] at h
    | some wb => cases wa <;> cases wb <;> simp [ha, hb] at h; exact ⟨_, _, rfl, rfl, h.symm⟩

theorem out_or {a b : IR.Expr} (h : IR.Expr.eval fs fuel ρ (.or a b) = some v) :
    ∃ x y, IR.Expr.eval fs fuel ρ a = some (.bool x) ∧ IR.Expr.eval fs fuel ρ b = some (.bool y) ∧
      v = .bool (x || y) := by
  simp only [IR.Expr.eval] at h
  cases ha : IR.Expr.eval fs fuel ρ a with
  | none => simp [ha] at h
  | some wa =>
    cases hb : IR.Expr.eval fs fuel ρ b with
    | none => cases wa <;> simp [ha, hb] at h
    | some wb => cases wa <;> cases wb <;> simp [ha, hb] at h; exact ⟨_, _, rfl, rfl, h.symm⟩

theorem out_decide {a : IR.Expr} : IR.Expr.eval fs fuel ρ (.decide a) = IR.Expr.eval fs fuel ρ a := by
  simp [IR.Expr.eval]

/-! ### Operators -/

variable {sp : Span} {a b c : IR.Expr} {ta tb t : Ty}

theorem arith_out {op : tolean.IR.IntOp} (h : arith sp op a ta b tb = .ok (c, t))
    (hv : IR.Expr.eval fs fuel ρ c = some v) :
    ∃ x y, IR.Expr.eval fs fuel ρ a = some (.int x) ∧ IR.Expr.eval fs fuel ρ b = some (.int y) ∧
      v = .int (wrap64 (op.apply x y)) := by
  unfold arith at h
  split at h
  · split at h
    · simp only [pure_ok, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      obtain ⟨i, hi, rfl⟩ := out_wrap64 hv
      obtain ⟨x, y, hx, hy, hxy⟩ := out_intOp hi
      cases hxy
      exact ⟨x, y, hx, hy, rfl⟩
    · exact absurd h reject_ne_ok
  · exact absurd h reject_ne_ok

theorem compare_out {op : tolean.IR.Order} (h : Pure.compare sp op a ta b tb = .ok (c, t))
    (hv : IR.Expr.eval fs fuel ρ c = some v) :
    ∃ x y, IR.Expr.eval fs fuel ρ a = some (.int x) ∧ IR.Expr.eval fs fuel ρ b = some (.int y) ∧
      v = .bool (op.apply x y) := by
  unfold Pure.compare at h
  split at h
  · split at h
    · simp only [pure_ok, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      rw [out_decide] at hv
      exact out_order hv
    · exact absurd h reject_ne_ok
  · exact absurd h reject_ne_ok

/-- The code of a binary operator gives what the interpreter's `binary`
gives on the values of the operands. -/
theorem translateBinary_out {o : BinOp} (h : translateBinary sp o a ta b tb = .ok (c, t))
    (hv : IR.Expr.eval fs fuel ρ c = some v) :
    ∃ va vb, IR.Expr.eval fs fuel ρ a = some va ∧ IR.Expr.eval fs fuel ρ b = some vb ∧
      Eval.binary o va vb = some v := by
  cases o <;> simp only [translateBinary] at h
  case add =>
    split at h
    · simp only [pure_ok, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      obtain ⟨x, y, hx, hy, rfl⟩ := out_append hv
      exact ⟨_, _, hx, hy, rfl⟩
    · obtain ⟨x, y, hx, hy, rfl⟩ := arith_out h hv
      exact ⟨_, _, hx, hy, rfl⟩
  case sub | mul =>
    obtain ⟨x, y, hx, hy, rfl⟩ := arith_out h hv
    exact ⟨_, _, hx, hy, rfl⟩
  case lt | le | gt | ge =>
    obtain ⟨x, y, hx, hy, rfl⟩ := compare_out h hv
    refine ⟨_, _, hx, hy, ?_⟩
    simp [Eval.binary, tolean.IR.Order.apply]
  case eq =>
    split at h
    · simp only [pure_ok, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      rw [out_decide] at hv
      obtain ⟨x, y, r, hx, hy, he, rfl⟩ := out_eq hv
      exact ⟨_, _, hx, hy, by simp [Eval.binary, he]⟩
    · exact absurd h reject_ne_ok
  case ne =>
    split at h
    · simp only [pure_ok, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      rw [out_decide] at hv
      obtain ⟨x, y, r, hx, hy, he, rfl⟩ := out_ne hv
      exact ⟨_, _, hx, hy, by simp [Eval.binary, he]⟩
    · exact absurd h reject_ne_ok
  case land =>
    split at h
    · simp only [pure_ok, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      obtain ⟨x, y, hx, hy, rfl⟩ := out_and hv
      exact ⟨_, _, hx, hy, rfl⟩
    · exact absurd h reject_ne_ok
  case lor =>
    split at h
    · simp only [pure_ok, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      obtain ⟨x, y, hx, hy, rfl⟩ := out_or hv
      exact ⟨_, _, hx, hy, rfl⟩
    · exact absurd h reject_ne_ok

/-- The interpreter's `&&`, `||` and the other operators give what `binary`
gives, once both operands have a value: `&&` and `||` skip the right
operand only when the left one decides. -/
theorem eval_binary {p : Eval.Program} {ρ : Eval.Env} {sp : Span} {op : String} {o : BinOp}
    {l r : Expr} {va vb : Val} (ho : BinOp.ofString? op = some o)
    (hl : Eval.eval p fuel ρ l = some va) (hr : Eval.eval p fuel ρ r = some vb)
    (hb : Eval.binary o va vb = some v) :
    Eval.eval p fuel ρ (.binary sp op l r) = some v := by
  rw [Eval.eval, ho]
  cases o
  case land =>
    cases va <;> cases vb <;> simp [Eval.binary] at hb
    subst hb
    rename_i x y
    cases x <;> simp [hl, hr]
  case lor =>
    cases va <;> cases vb <;> simp [Eval.binary] at hb
    subst hb
    rename_i x y
    cases x <;> simp [hl, hr]
  all_goals simp [hl, hr, hb]

/-! ### Expressions -/

theorem scoped_none {env : Pure.Env} {ρ : Eval.Env} {n : String} (hs : Scoped env ρ)
    (h : env.has n = false) : ρ.lookup n = none := by
  have := hs n
  rw [h] at this
  simpa using this

theorem env_has_of_lookup {env : Pure.Env} {n : String} {l : Local} (h : env.lookup n = some l) :
    env.has n = true := by
  simp [Pure.Env.has, h]

theorem env_lookup_none {env : Pure.Env} {n : String} (h : env.lookup n = none) :
    env.has n = false := by
  simp [Pure.Env.has, h]

variable (p : Eval.Program) (fs) (fuel)

/-- `expr_sound` and its case for argument lists, by induction on the
translator's fuel. -/
theorem expr_sound_aux {ctx : Ctx} (hp : ctx.program = p) (hc : CallsAgree p fs fuel) :
    ∀ n : Nat,
      (∀ (env : Pure.Env) (e : Expr) (c : IR.Expr) (t : Ty), translateExpr ctx env n e = .ok (c, t) →
        ∀ ρs ρo v, Agree ρs ρo → Scoped env ρs → IR.Expr.eval fs fuel ρo c = some v →
          Eval.eval p fuel ρs e = some v) ∧
      (∀ (env : Pure.Env) (es : List Expr) (cs : List (IR.Expr × Ty)),
        translateArgs ctx env n es = .ok cs →
        ∀ ρs ρo vs, Agree ρs ρo → Scoped env ρs →
          IR.Expr.evalList fs fuel ρo (cs.map (·.1)) = some vs → Eval.evalList p fuel ρs es = some vs)
  | 0 => by
    refine ⟨fun env e c t h => by simp [translateExpr] at h, fun env es cs h => ?_⟩
    cases es with
    | nil =>
      simp only [translateArgs, pure_ok] at h
      subst h
      intro ρs ρo vs _ _ hv
      simp [IR.Expr.evalList] at hv
      subst hv
      simp [Eval.evalList]
    | cons e es => simp [translateArgs] at h
  | n + 1 => by
    obtain ⟨ihe, iha⟩ := expr_sound_aux hp hc n
    refine ⟨fun env e c t h => ?_, fun env es cs h => ?_⟩
    · intro ρs ρo v ha hs hv
      rw [translateExpr.eq_def] at h
      simp only at h
      split at h
      -- A name: a local, or `true` or `false`.
      · next sp name =>
        split at h
        · next l hl =>
          simp only [pure_ok, Prod.mk.injEq] at h
          obtain ⟨rfl, -⟩ := h
          simp only [IR.Expr.eval] at hv
          rw [Eval.eval, ha name, hv]
        · next hl =>
          split at h
          · next b hb =>
            simp only [pure_ok, Prod.mk.injEq] at h
            obtain ⟨rfl, -⟩ := h
            simp only [IR.Expr.eval, Option.some.injEq] at hv
            subst hv
            rw [Eval.eval, scoped_none hs (env_lookup_none hl), ← hp, hb]
          · exact absurd h reject_ne_ok
      -- An integer literal.
      · next sp raw =>
        split at h
        · next k hk =>
          split at h
          · simp only [pure_ok, Prod.mk.injEq] at h
            obtain ⟨rfl, -⟩ := h
            simp only [IR.Expr.eval, Option.some.injEq] at hv
            subst hv
            simp [Eval.eval, hk]
          · exact absurd h reject_ne_ok
        · exact absurd h reject_ne_ok
      -- A string literal.
      · next sp raw =>
        split at h
        · next s hs' =>
          simp only [pure_ok, Prod.mk.injEq] at h
          obtain ⟨rfl, -⟩ := h
          simp only [IR.Expr.eval, Option.some.injEq] at hv
          subst hv
          simp [Eval.eval, hs']
        · exact absurd h reject_ne_ok
      -- Parentheses.
      · next sp inner =>
        rw [Eval.eval]
        exact ihe env inner c t h ρs ρo v ha hs hv
      -- A unary operator.
      · next sp op arg =>
        rw [bind_ok] at h
        obtain ⟨⟨ca, tc⟩, hca, h⟩ := h
        split at h
        · split at h
          · simp only [pure_ok, Prod.mk.injEq] at h
            obtain ⟨rfl, -⟩ := h
            obtain ⟨i, hi, rfl⟩ := out_wrap64 hv
            obtain ⟨j, hj, hij⟩ := out_neg hi
            injection hij with hij
            subst hij
            have := ihe env arg ca tc hca ρs ρo _ ha hs hj
            simp [Eval.eval, this, Eval.unary]
          · exact absurd h reject_ne_ok
        · split at h
          · simp only [pure_ok, Prod.mk.injEq] at h
            obtain ⟨rfl, -⟩ := h
            obtain ⟨b, hb, rfl⟩ := out_not hv
            have := ihe env arg ca tc hca ρs ρo _ ha hs hb
            simp [Eval.eval, this, Eval.unary]
          · exact absurd h reject_ne_ok
        · exact absurd h reject_ne_ok
      -- A binary operator.
      · next sp op l r =>
        cases ho : BinOp.ofString? op with
        | none => simp [ho] at h
        | some o =>
          simp only [ho, bind_ok] at h
          obtain ⟨⟨a, ta⟩, hla, ⟨b, tb⟩, hrb, h⟩ := h
          obtain ⟨va, vb, hva, hvb, hbin⟩ := translateBinary_out h hv
          exact eval_binary ho (ihe env l a ta hla ρs ρo va ha hs hva)
            (ihe env r b tb hrb ρs ρo vb ha hs hvb) hbin
      -- A call of a translated function.
      · next sp sp' f args =>
        cases hf : env.has f with
        | true => simp [hf] at h
        | false =>
          cases hsig : ctx.known.find? (·.name == f) with
          | none => simp [hf, hsig] at h
          | some sig =>
            simp only [hf, hsig, Bool.false_eq_true, ↓reduceIte, bind_ok] at h
            obtain ⟨_, -, codes, hcodes, h⟩ := h
            cases hfit : argsFit codes sig.params
            · simp [hfit, reject, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
            simp only [hfit, ↓reduceIte, bind, Except.bind, pure, Except.pure, Except.ok.injEq,
              Prod.mk.injEq] at h
            obtain ⟨hc', -⟩ := h
            subst hc'
            rw [out_call] at hv
            cases hvs : IR.Expr.evalList fs fuel ρo (codes.map (·.1)) with
            | none => simp [hvs] at hv
            | some vs =>
              simp only [hvs, Option.bind_some] at hv
              have hargs := iha env args codes hcodes ρs ρo vs ha hs hvs
              rw [eval_call, scoped_none hs hf]
              simp [hargs, hc f vs v hv]
      · exact absurd h reject_ne_ok
    · cases es with
      | nil =>
        simp only [translateArgs, pure_ok] at h
        subst h
        intro ρs ρo vs _ _ hv
        simp [IR.Expr.evalList] at hv
        subst hv
        simp [Eval.evalList]
      | cons e es =>
        simp only [translateArgs] at h
        rw [bind_ok] at h
        obtain ⟨⟨c, t⟩, hc', h⟩ := h
        rw [bind_ok] at h
        obtain ⟨cs', hcs, h⟩ := h
        simp only [pure_ok] at h
        subst h
        intro ρs ρo vs ha hs hv
        simp only [List.map_cons, IR.Expr.evalList] at hv
        cases hw : IR.Expr.eval fs fuel ρo c with
        | none => simp [hw] at hv
        | some w =>
          cases hws : IR.Expr.evalList fs fuel ρo (cs'.map (·.1)) with
          | none => simp [hw, hws] at hv
          | some ws =>
            simp [hw, hws] at hv
            subst hv
            simp [Eval.evalList, ihe env e c t hc' ρs ρo w ha hs hw,
              iha env es cs' hcs ρs ρo ws ha hs hws]

/-- The code that the translator gives for an expression gives a value only
when the interpreter gives the same value for the expression. -/
theorem expr_sound {ctx : Ctx} (hp : ctx.program = p) (hc : CallsAgree p fs fuel) {n : Nat}
    {env : Pure.Env} {e : Expr} {c : IR.Expr} {t : Ty} (h : translateExpr ctx env n e = .ok (c, t))
    {ρs ρo : Eval.Env} {v : Val} (ha : Agree ρs ρo) (hs : Scoped env ρs)
    (hv : IR.Expr.eval fs fuel ρo c = some v) : Eval.eval p fuel ρs e = some v :=
  (expr_sound_aux fs fuel p hp hc n).1 env e c t h ρs ρo v ha hs hv

end tolean.Go.Proof
