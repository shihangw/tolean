import tolean.TypeScript.EStateM
import tolean.TypeScript.Translate
import tolean.TypeScript.IR.Eval
import tolean.TypeScript.Spec.Lemmas.Eval

/-!
The translation of an expression means what the expression means.

`expr_sound` states it for the expression functions of the translator: when
the translator gives code for an expression, and the code evaluates to a
value in the IR's evaluator, the interpreter gives the same value for the
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

-- `TM` is an `EStateM`, so the shared lemmas apply.
export EStateM (bind_ok map_ok ite_state pure_ok get_ok)
attribute [simp] EStateM.bind_ok EStateM.map_ok

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
    · split at h
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
    · split at h
      · simp at h
      · simp only [bind_ok] at h
        obtain ⟨r, s₁, hr, h⟩ := h
        obtain ⟨-, rfl⟩ := checkLocalName_ok hr
        simp only [ite_state] at h
        split at h
        · simp at h
        · simp only [pure_ok] at h
          exact ⟨by simpa using hn, h.1.symm, h.2.symm⟩

/-- The check of a call of a function that can throw changes nothing. -/
theorem checkThrowingCall_ok {sp : Span} {name : String} {fn : FnInfo} {top : Bool} {s s' : Ctx} {u : Unit}
    (h : checkThrowingCall sp name fn top s = .ok u s') : s' = s := by
  simp only [checkThrowingCall, ite_state] at h
  split at h
  · simp at h
  · simp only [pure_ok] at h; exact h.2.symm

end Monad

/-! ### Environments and calls -/

/-- The interpreter's environment and the output's give every name the same
value. -/
def Agree (ρs ρo : Eval.Env N) : Prop := ∀ n, ρs.lookup n = ρo.lookup n

theorem has_add (env : Translate.Env) (l : Local) (x : String) :
    (env.add l).has x = (env.has x || l.name == x) := by
  simp only [Env.has, Env.lookup, Env.add, List.find?_append]
  cases env.locals.find? (·.name == x) <;> simp [List.find?]
  split <;> simp_all

/-- Each function that a call may name is the one the interpreter calls: in
the file of `m`, a call of `f.name` runs `f`. And each string enum whose
members code may read is the one the interpreter reads: in the file of `m`,
the name `e.name` is the enum with the members `e.members`. -/
def Resolves (m : Eval.Scope) (env : Translate.Env) : Prop :=
  (∀ f ∈ env.functions, Eval.resolve m f.name = some f.ref) ∧
    ∀ e ∈ env.enums, Eval.resolveEnum m e.name = some e.members

/-- The functions and the string enums that code may name. A branch or a
loop body keeps them, and changes only the locals. -/
def globals (env : Translate.Env) : List FnInfo × List EnumValue × List LocalFn :=
  (env.functions, env.enums, env.localFns)

theorem Resolves.congr {m : Eval.Scope} {env env' : Translate.Env} (h : Resolves m env)
    (hg : globals env' = globals env) : Resolves m env' := by
  simp only [globals, Prod.mk.injEq] at hg
  replace hg := And.intro hg.1 hg.2.1
  exact ⟨fun f hf => h.1 f (hg.1 ▸ hf), fun e he => h.2 e (hg.2 ▸ he)⟩

/-- A scope with the same globals has the same local functions, which change
the same locals. -/
theorem fnChanges_congr {env env' : Translate.Env} (hg : globals env' = globals env) :
    env'.fnChanges = env.fnChanges := by
  simp only [globals, Prod.mk.injEq] at hg
  simp [Env.fnChanges, hg.2.2]

/-- The interpreter's environment binds exactly the names that the translator
has in scope, so a name out of scope, such as `NaN`, is the global. And the
functions that the translator knows are the ones that the interpreter calls. -/
def Scoped (m : Eval.Scope) (env : Translate.Env) (ρ : Eval.Env N) : Prop :=
  (∀ n, (ρ.lookup n).isSome = env.has n) ∧ Resolves m env

omit [JSNumber N] in
theorem Scoped.none {m : Eval.Scope} {env : Translate.Env} {ρ : Eval.Env N} (h : Scoped m env ρ)
    {n : String} (hn : env.has n = false) : ρ.lookup n = none := by
  have := h.1 n; rw [hn] at this; simpa using this

omit [JSNumber N] in
theorem Scoped.some {m : Eval.Scope} {env : Translate.Env} {ρ : Eval.Env N} (h : Scoped m env ρ)
    {n : String} (hn : env.has n = true) : (ρ.lookup n).isSome := by
  rw [h.1 n]; exact hn

/-- A call of the function `key` of the program, as the interpreter runs it:
what it returns or throws. -/
def callS (p : Eval.Program) (fuel : Nat) (key : DeclRef) (vs : List (Val N)) :
    Option (Except (Val N) (Val N)) :=
  match fuel with
  | 0 => none
  | fuel + 1 => do
    let (params, body) ← (Eval.functionsOf p).lookup key
    if !Stmt.ownsChanges params body then none
    match ← Eval.execStmt ⟨p, key.file⟩ fuel (← Eval.bindArgs params vs) body with
    | .ret r => some r
    | .normal _ | .brk _ | .cont _ => none

/-- A call of the function `key` of the output, as its evaluator runs it:
what it returns or throws. -/
def callO (fs : List (DeclRef × List String × IR.Body)) (fuel : Nat) (key : DeclRef)
    (vs : List (Val N)) : Option (Except (Val N) (Val N)) :=
  match fuel with
  | 0 => none
  | fuel + 1 => do
    let (params, body) ← fs.lookup key
    if params.length != vs.length then none
    match ← IR.Body.exec fs fuel (params.zip vs).reverse body with
    | .ret r => some r
    | .normal _ | .brk _ | .cont _ => none

/-- Every call that returns or throws in the output returns or throws the
same value in the interpreter. -/
def CallsAgree (p : Eval.Program) (fs : List (DeclRef × List String × IR.Body)) (fuel : Nat) :
    Prop :=
  ∀ key vs r, callO (N := N) fs fuel key vs = some r → callS p fuel key vs = some r

/-! ### The statement -/

variable (m : Eval.Scope) (fs : List (DeclRef × List String × IR.Body)) (fuel : Nat)

/-- The output code `out` means what the expression `e` means. -/
def Sim (env : Translate.Env) (e : Expr) (out : IR.Expr) : Prop :=
  ∀ (ρs ρo : Eval.Env N) v, Agree ρs ρo → Scoped m env ρs →
    IR.Expr.eval fs fuel ρo out = some v → Eval.eval m fuel ρs e = some v

/-- When the output code `out` of a call of `callee` on `args` is a call of a
function of the output, `callee` is a name, and the output's call returns or
throws what the source's call returns or throws. A statement that passes on
the error of a call needs this, because `Sim` is only about the value. -/
def CallSim (env : Translate.Env) (callee : Expr) (args : List Expr) (out : IR.Expr) : Prop :=
  ∀ ref outs, out = .call ref outs → ∃ sp name, callee = .ident sp name ∧
    ∀ (ρs ρo : Eval.Env N) r, Agree ρs ρo → Scoped m env ρs →
      IR.Expr.evalCall fs fuel ρo ref outs = some r → Eval.evalCall m fuel ρs name args = some r

/-- The output codes `outs` mean what the expressions `es` mean. -/
def SimList (env : Translate.Env) (es : List Expr) (outs : List IR.Expr) : Prop :=
  ∀ (ρs ρo : Eval.Env N) vs, Agree ρs ρo → Scoped m env ρs →
    IR.Expr.evalList fs fuel ρo outs = some vs → Eval.evalList m fuel ρs es = some vs

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

omit [JSNumber N] in
/-- A member's string, as the field of the enum's object. -/
theorem lookup_map_str {members : List (String × String)} {k v : String} (h : members.lookup k = some v) :
    (members.map fun (p : String × String) => (p.1, (Val.str p.2 : Val N))).lookup k = some (.str v) := by
  induction members with
  | nil => simp at h
  | cons p ps ih =>
    obtain ⟨a, b⟩ := p
    by_cases hk : k = a
    · subst hk; simp [List.lookup] at h ⊢; exact h
    · have hk' : (k == a) = false := by simpa using hk
      simp only [List.lookup, hk', List.map_cons] at h ⊢
      exact ih h

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

/-! ### What the IR's evaluator says, one form at a time -/

section Inversion

variable {ρ : Eval.Env N} {v : Val N}

theorem out_not {p : IR.Expr} (h : IR.Expr.eval fs fuel ρ (.not p) = some v) :
    ∃ b, IR.Expr.eval fs fuel ρ p = some (.bool b) ∧ v = .bool !b := by
  simp only [IR.Expr.eval] at h
  cases hx : IR.Expr.eval fs fuel ρ p with
  | none => simp [hx] at h
  | some w => cases w <;> simp_all

theorem out_propNot {p : IR.Expr} (h : IR.Expr.eval fs fuel ρ (.propNot p) = some v) :
    ∃ b, IR.Expr.eval fs fuel ρ p = some (.bool b) ∧ v = .bool !b := by
  simp only [IR.Expr.eval] at h
  cases hx : IR.Expr.eval fs fuel ρ p with
  | none => simp [hx] at h
  | some w => cases w <;> simp_all

theorem out_neg {a : IR.Expr} (h : IR.Expr.eval fs fuel ρ (.neg a) = some v) :
    ∃ i, IR.Expr.eval fs fuel ρ a = some (.int i) ∧ v = .int (-i) := by
  simp only [IR.Expr.eval] at h
  cases hx : IR.Expr.eval fs fuel ρ a with
  | none => simp [hx] at h
  | some w => cases w <;> simp_all

theorem out_numberNeg {a : IR.Expr} (h : IR.Expr.eval fs fuel ρ (.numberNeg a) = some v) :
    ∃ n, IR.Expr.eval fs fuel ρ a = some (.num n) ∧ v = .num (JSNumber.neg n) := by
  simp only [IR.Expr.eval, IR.Expr.evalList] at h
  cases hx : IR.Expr.eval fs fuel ρ a with
  | none => simp [hx, IR.ExprExt.apply] at h
  | some w => cases w <;> simp_all [IR.ExprExt.apply]

theorem out_ite {c a b : IR.Expr} (h : IR.Expr.eval fs fuel ρ (.ite c a b) = some v) :
    ∃ t, IR.Expr.eval fs fuel ρ c = some (.bool t) ∧
      (if t then IR.Expr.eval fs fuel ρ a else IR.Expr.eval fs fuel ρ b) = some v := by
  simp only [IR.Expr.eval] at h
  cases hx : IR.Expr.eval fs fuel ρ c with
  | none => simp [hx] at h
  | some w => cases w <;> simp_all

theorem out_numberTest {t : IR.NumberTest} {a : IR.Expr}
    (h : IR.Expr.eval fs fuel ρ (.numberTest t a) = some v) :
    ∃ n, IR.Expr.eval fs fuel ρ a = some (.num n) ∧ v = .bool (t.apply n) := by
  simp only [IR.Expr.eval, IR.Expr.evalList] at h
  cases hx : IR.Expr.eval fs fuel ρ a with
  | none => simp [hx, IR.ExprExt.apply] at h
  | some w => cases w <;> simp_all [IR.ExprExt.apply]

theorem out_numberFn {f : IR.NumberFn} {a : IR.Expr}
    (h : IR.Expr.eval fs fuel ρ (.ext (.numberFn f) [a]) = some v) :
    ∃ n, IR.Expr.eval fs fuel ρ a = some (.num n) ∧ v = .num (f.apply n) := by
  simp only [IR.Expr.eval, IR.Expr.evalList] at h
  cases hx : IR.Expr.eval fs fuel ρ a with
  | none => simp [hx, IR.ExprExt.apply] at h
  | some w => cases w <;> simp_all [IR.ExprExt.apply]

theorem out_numberFold {isMax : Bool} {args : List IR.Expr}
    (h : IR.Expr.eval fs fuel ρ (.ext (.numberFold isMax) args) = some v) :
    ∃ vs xs, IR.Expr.evalList fs fuel ρ args = some vs ∧ Eval.numbers? vs = some xs ∧
      v = .num (if isMax then JSNumber.maximum xs else JSNumber.minimum xs) := by
  simp only [IR.Expr.eval] at h
  cases hx : IR.Expr.evalList fs fuel ρ args with
  | none => simp [hx] at h
  | some vs =>
    cases hn : Eval.numbers? vs with
    | none => simp [hx, hn, IR.ExprExt.apply] at h
    | some xs =>
      simp [hx, hn, IR.ExprExt.apply] at h
      exact ⟨vs, xs, rfl, hn, h.symm⟩

theorem out_intOp {op : IR.IntOp} {a b : IR.Expr}
    (h : IR.Expr.eval fs fuel ρ (.intOp op a b) = some v) :
    ∃ x y, IR.Expr.eval fs fuel ρ a = some (.int x) ∧ IR.Expr.eval fs fuel ρ b = some (.int y) ∧
      v = .int (op.apply x y) := by
  simp only [IR.Expr.eval] at h
  cases hx : IR.Expr.eval fs fuel ρ a with
  | none => simp [hx] at h
  | some w =>
    cases hy : IR.Expr.eval fs fuel ρ b with
    | none => cases w <;> simp_all
    | some u => cases w <;> cases u <;> simp_all

theorem out_order {op : IR.Order} {a b : IR.Expr}
    (h : IR.Expr.eval fs fuel ρ (.order op a b) = some v) :
    ∃ x y, IR.Expr.eval fs fuel ρ a = some (.int x) ∧ IR.Expr.eval fs fuel ρ b = some (.int y) ∧
      v = .bool (op.apply x y) := by
  simp only [IR.Expr.eval] at h
  cases hx : IR.Expr.eval fs fuel ρ a with
  | none => simp [hx] at h
  | some w =>
    cases hy : IR.Expr.eval fs fuel ρ b with
    | none => cases w <;> simp_all
    | some u => cases w <;> cases u <;> simp_all

theorem out_division {op : IR.Division} {a b : IR.Expr}
    (h : IR.Expr.eval fs fuel ρ (.division op a b) = some v) :
    ∃ x y, IR.Expr.eval fs fuel ρ a = some (.int x) ∧ IR.Expr.eval fs fuel ρ b = some (.int y) ∧
      v = .int (op.apply x y) := by
  simp only [IR.Expr.eval] at h
  cases hx : IR.Expr.eval fs fuel ρ a with
  | none => simp [hx] at h
  | some w =>
    cases hy : IR.Expr.eval fs fuel ρ b with
    | none => cases w <;> simp_all
    | some u => cases w <;> cases u <;> simp_all

/-- `ExprExt.apply` on an operation of the number model, without the other
operations, so that a proof need not unfold them all. -/
theorem apply_numberOp (op : IR.NumberOp) (w u : Val N) :
    IR.ExprExt.apply (.numberOp op) [w, u] =
      match w, u with
      | .num a, .num b => some (op.apply a b)
      | _, _ => none := by
  cases w <;> cases u <;> rfl

theorem apply_numberNe (w u : Val N) :
    IR.ExprExt.apply .numberNe [w, u] =
      match w, u with
      | .num a, .num b => some (.bool !(JSNumber.eq a b))
      | _, _ => none := by
  cases w <;> cases u <;> rfl

theorem out_numberOp {op : IR.NumberOp} {a b : IR.Expr}
    (h : IR.Expr.eval fs fuel ρ (.numberOp op a b) = some v) :
    ∃ x y, IR.Expr.eval fs fuel ρ a = some (.num x) ∧ IR.Expr.eval fs fuel ρ b = some (.num y) ∧
      v = op.apply x y := by
  simp only [IR.Expr.eval, IR.Expr.evalList] at h
  cases hx : IR.Expr.eval fs fuel ρ a with
  | none => simp [hx] at h
  | some w =>
    cases hy : IR.Expr.eval fs fuel ρ b with
    | none => simp [hx, hy] at h
    | some u =>
      simp only [hx, hy, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at h
      rw [apply_numberOp] at h
      cases w <;> cases u <;> simp at h
      exact ⟨_, _, rfl, rfl, h.symm⟩

/-- `ExprExt.apply` on an order of strings, without the other operations. -/
theorem apply_stringOrder (le : Bool) (w u : Val N) :
    IR.ExprExt.apply (.stringOrder le) [w, u] =
      match w, u with
      | .str a, .str b => some (.bool (if le then a.le b else a.lt b))
      | _, _ => none := by
  cases w <;> cases u <;> rfl

theorem out_stringOrder {le : Bool} {a b : IR.Expr}
    (h : IR.Expr.eval fs fuel ρ (.ext (.stringOrder le) [a, b]) = some v) :
    ∃ x y, IR.Expr.eval fs fuel ρ a = some (.str x) ∧ IR.Expr.eval fs fuel ρ b = some (.str y) ∧
      v = .bool (if le then x.le y else x.lt y) := by
  simp only [IR.Expr.eval, IR.Expr.evalList] at h
  cases hx : IR.Expr.eval fs fuel ρ a with
  | none => simp [hx] at h
  | some w =>
    cases hy : IR.Expr.eval fs fuel ρ b with
    | none => simp [hx, hy] at h
    | some u =>
      simp only [hx, hy, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at h
      rw [apply_stringOrder] at h
      cases w <;> cases u <;> simp at h
      exact ⟨_, _, rfl, rfl, h.symm⟩

theorem out_stringAppend {left right : IR.StringPart} {a b : IR.Expr}
    (h : IR.Expr.eval fs fuel ρ (.ext (.stringAppend left right) [a, b]) = some v) :
    ∃ x y sx sy, IR.Expr.eval fs fuel ρ a = some x ∧ IR.Expr.eval fs fuel ρ b = some y ∧
      left.toStr x = some sx ∧ right.toStr y = some sy ∧ v = .str (sx ++ sy) := by
  simp only [IR.Expr.eval, IR.Expr.evalList] at h
  cases hx : IR.Expr.eval fs fuel ρ a with
  | none => simp [hx, IR.ExprExt.apply] at h
  | some w =>
    cases hy : IR.Expr.eval fs fuel ρ b with
    | none => simp_all [IR.ExprExt.apply]
    | some u =>
      cases h1 : left.toStr w <;> cases h2 : right.toStr u <;> simp_all [IR.ExprExt.apply]

theorem out_numberNe {a b : IR.Expr}
    (h : IR.Expr.eval fs fuel ρ (.numberNe a b) = some v) :
    ∃ x y, IR.Expr.eval fs fuel ρ a = some (.num x) ∧ IR.Expr.eval fs fuel ρ b = some (.num y) ∧
      v = .bool !(JSNumber.eq x y) := by
  simp only [IR.Expr.eval, IR.Expr.evalList] at h
  cases hx : IR.Expr.eval fs fuel ρ a with
  | none => simp [hx] at h
  | some w =>
    cases hy : IR.Expr.eval fs fuel ρ b with
    | none => simp [hx, hy] at h
    | some u =>
      simp only [hx, hy, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at h
      rw [apply_numberNe] at h
      cases w <;> cases u <;> simp at h
      exact ⟨_, _, rfl, rfl, h.symm⟩

theorem out_eq {a b : IR.Expr} (h : IR.Expr.eval fs fuel ρ (.eq a b) = some v) :
    ∃ x y t, IR.Expr.eval fs fuel ρ a = some x ∧ IR.Expr.eval fs fuel ρ b = some y ∧
      IR.eqVal x y = some t ∧ v = .bool t := by
  simp only [IR.Expr.eval] at h
  cases hx : IR.Expr.eval fs fuel ρ a with
  | none => simp [hx] at h
  | some w =>
    cases hy : IR.Expr.eval fs fuel ρ b with
    | none => simp [hx, hy] at h
    | some u =>
      cases ht : IR.eqVal w u with
      | none => simp [hx, hy, ht] at h
      | some t => simp [hx, hy, ht] at h; exact ⟨w, u, t, rfl, rfl, ht, h.symm⟩

theorem out_ne {a b : IR.Expr} (h : IR.Expr.eval fs fuel ρ (.ne a b) = some v) :
    ∃ x y t, IR.Expr.eval fs fuel ρ a = some x ∧ IR.Expr.eval fs fuel ρ b = some y ∧
      IR.eqVal x y = some t ∧ v = .bool !t := by
  simp only [IR.Expr.eval] at h
  cases hx : IR.Expr.eval fs fuel ρ a with
  | none => simp [hx] at h
  | some w =>
    cases hy : IR.Expr.eval fs fuel ρ b with
    | none => simp [hx, hy] at h
    | some u =>
      cases ht : IR.eqVal w u with
      | none => simp [hx, hy, ht] at h
      | some t => simp [hx, hy, ht] at h; exact ⟨w, u, t, rfl, rfl, ht, h.symm⟩

theorem out_and {a b : IR.Expr}
    (h : IR.Expr.eval fs fuel ρ (.and a b) = some v ∨ IR.Expr.eval fs fuel ρ (.propAnd a b) = some v) :
    ∃ x y, IR.Expr.eval fs fuel ρ a = some (.bool x) ∧ IR.Expr.eval fs fuel ρ b = some (.bool y) ∧
      v = .bool (x && y) := by
  rcases h with h | h <;>
  · simp only [IR.Expr.eval] at h
    cases hx : IR.Expr.eval fs fuel ρ a with
    | none => simp [hx] at h
    | some w =>
      cases hy : IR.Expr.eval fs fuel ρ b with
      | none => cases w <;> simp_all
      | some u => cases w <;> cases u <;> simp_all

theorem out_or {a b : IR.Expr}
    (h : IR.Expr.eval fs fuel ρ (.or a b) = some v ∨ IR.Expr.eval fs fuel ρ (.propOr a b) = some v) :
    ∃ x y, IR.Expr.eval fs fuel ρ a = some (.bool x) ∧ IR.Expr.eval fs fuel ρ b = some (.bool y) ∧
      v = .bool (x || y) := by
  rcases h with h | h <;>
  · simp only [IR.Expr.eval] at h
    cases hx : IR.Expr.eval fs fuel ρ a with
    | none => simp [hx] at h
    | some w =>
      cases hy : IR.Expr.eval fs fuel ρ b with
      | none => cases w <;> simp_all
      | some u => cases w <;> cases u <;> simp_all

/-- Whether a value is `null`. -/
def isNullVal : Val N → Bool
  | .null => true
  | _ => false

theorem out_isNone {a : IR.Expr} (h : IR.Expr.eval fs fuel ρ (.isNone a) = some v) :
    ∃ w, IR.Expr.eval fs fuel ρ a = some w ∧ w ≠ .undefined ∧ v = .bool (isNullVal w) := by
  simp only [IR.Expr.eval] at h
  cases hx : IR.Expr.eval fs fuel ρ a with
  | none => simp [hx] at h
  | some w => cases w <;> simp_all [isNullVal]

theorem out_isSome {a : IR.Expr} (h : IR.Expr.eval fs fuel ρ (.isSome a) = some v) :
    ∃ w, IR.Expr.eval fs fuel ρ a = some w ∧ w ≠ .undefined ∧ v = .bool !(isNullVal w) := by
  simp only [IR.Expr.eval] at h
  cases hx : IR.Expr.eval fs fuel ρ a with
  | none => simp [hx] at h
  | some w => cases w <;> simp_all [isNullVal]

theorem out_coalesce {a b : IR.Expr} {nullable : Bool}
    (h : IR.Expr.eval fs fuel ρ (.coalesce a b nullable) = some v) :
    ∃ w, IR.Expr.eval fs fuel ρ a = some w ∧
      (((w = .null ∨ w = .undefined) ∧ IR.Expr.eval fs fuel ρ b = some v) ∨
        (isNullVal w = false ∧ w ≠ .undefined ∧ v = w)) := by
  simp only [IR.Expr.eval] at h
  cases hx : IR.Expr.eval fs fuel ρ a with
  | none => simp [hx] at h
  | some w =>
    refine ⟨w, rfl, ?_⟩
    cases w <;> simp [hx] at h <;> first | (subst h; simp [isNullVal]) | simp [isNullVal, h]

/-- `ExprExt.apply` on an operation of `JSBigInt` on two bigints, without the
other operations. -/
theorem apply_bigintOp (op : IR.BigintOp) (w u : Val N) :
    IR.ExprExt.apply (.bigintOp op) [w, u] =
      match w, u with
      | .int a, .int b => some (.int (op.apply a b))
      | _, _ => none := by
  cases w <;> cases u <;> rfl

theorem out_bigintOp {op : IR.BigintOp} {a b : IR.Expr}
    (h : IR.Expr.eval fs fuel ρ (.ext (.bigintOp op) [a, b]) = some v) :
    ∃ x y, IR.Expr.eval fs fuel ρ a = some (.int x) ∧ IR.Expr.eval fs fuel ρ b = some (.int y) ∧
      v = .int (op.apply x y) := by
  simp only [IR.Expr.eval, IR.Expr.evalList] at h
  cases hx : IR.Expr.eval fs fuel ρ a with
  | none => simp [hx] at h
  | some w =>
    cases hy : IR.Expr.eval fs fuel ρ b with
    | none => simp [hx, hy] at h
    | some u =>
      simp only [hx, hy, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at h
      rw [apply_bigintOp] at h
      cases w <;> cases u <;> simp at h
      exact ⟨_, _, rfl, rfl, h.symm⟩

theorem out_bigintNot {a : IR.Expr} (h : IR.Expr.eval fs fuel ρ (.ext .bigintNot [a]) = some v) :
    ∃ i, IR.Expr.eval fs fuel ρ a = some (.int i) ∧ v = .int (JSBigInt.bitNot i) := by
  simp only [IR.Expr.eval, IR.Expr.evalList] at h
  cases hx : IR.Expr.eval fs fuel ρ a with
  | none => simp [hx, IR.ExprExt.apply] at h
  | some w => cases w <;> simp_all [IR.ExprExt.apply]

theorem out_bigintPow {k : Nat} {a : IR.Expr}
    (h : IR.Expr.eval fs fuel ρ (.ext (.bigintPow k) [a]) = some v) :
    ∃ i, IR.Expr.eval fs fuel ρ a = some (.int i) ∧ v = .int (i ^ k) := by
  simp only [IR.Expr.eval, IR.Expr.evalList] at h
  cases hx : IR.Expr.eval fs fuel ρ a with
  | none => simp [hx, IR.ExprExt.apply] at h
  | some w => cases w <;> simp_all [IR.ExprExt.apply]

end Inversion

/-- The output fields `outs` mean what the properties `ps` mean. -/
def SimFields (env : Translate.Env) (ps : List Property) (outs : List (String × IR.Expr)) : Prop :=
  ∀ (ρs ρo : Eval.Env N) fvs, Agree ρs ρo → Scoped m env ρs →
    IR.Expr.evalFields fs fuel ρo outs = some fvs → Eval.evalProps m fuel ρs ps = some fvs

/-- The output field `(key, o)` means what the property `p` means: the
interpreter gives `(key, w)` for `p` when `o` has the value `w`. -/
def PropSim (env : Translate.Env) (p : Property) (key : String) (o : IR.Expr) : Prop :=
  ∀ (ρs ρo : Eval.Env N) w, Agree ρs ρo → Scoped m env ρs → IR.Expr.eval fs fuel ρo o = some w →
    ∀ rest, Eval.evalProps m fuel ρs (p :: rest) = (Eval.evalProps m fuel ρs rest).map ((key, w) :: ·)

/-- A fold that appends one field for each property, where each field means
what its property means, gives fields that mean what the properties mean. -/
theorem fold_sim {env : Translate.Env} {α : Type}
    {g : α × List (String × IR.Expr) → Property → TM (α × List (String × IR.Expr))}
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
    simp [IR.Expr.evalFields] at hv
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
    simp only [IR.Expr.evalFields] at hv
    cases hx : IR.Expr.eval fs fuel ρo o with
    | none => simp [hx] at hv
    | some w =>
      cases hxs : IR.Expr.evalFields fs fuel ρo new with
      | none => simp [hx, hxs] at hv
      | some ws =>
        simp [hx, hxs] at hv
        subst hv
        rw [hp ρs ρo w ha hs hx ps, hsim ρs ρo ws ha hs hxs]
        rfl

theorem eval_value (c : Code) (ρ : Eval.Env N) :
    IR.Expr.eval fs fuel ρ c.value = IR.Expr.eval fs fuel ρ c.code := by
  unfold Code.value
  split <;> simp [IR.Expr.eval]

/-- An element that is not a spread holds its own value in an array literal. -/
theorem evalElems_cons {ρ : Eval.Env N} {e : Expr} {es : List Expr} (he : e.spreadArg? = none) :
    Eval.evalElems m fuel ρ (e :: es) =
      (do return (← Eval.eval m fuel ρ e) :: (← Eval.evalElems m fuel ρ es)) := by
  cases e <;> simp_all [Expr.spreadArg?, Eval.evalElems]

/-- A spread is not a value on its own. -/
theorem eval_spreadElem {ρ : Eval.Env N} {sp : Span} {e : Expr} :
    Eval.eval m fuel ρ (.spread sp e) = none := by
  rw [Eval.eval] <;> simp

/-- When each element of an array literal has a value, none is a spread, and
the literal holds those values. -/
theorem evalElems_of_evalList {ρ : Eval.Env N} :
    ∀ {es : List Expr} {vs : List (Val N)}, Eval.evalList m fuel ρ es = some vs →
      Eval.evalElems m fuel ρ es = some vs
  | [], vs, h => by simpa [Eval.evalList, Eval.evalElems] using h
  | e :: es, vs, h => by
    simp only [Eval.evalList] at h
    cases hx : Eval.eval m fuel ρ e with
    | none => simp [hx] at h
    | some x =>
      cases hxs : Eval.evalList m fuel ρ es with
      | none => simp [hx, hxs] at h
      | some xs =>
        simp only [hx, hxs, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          Option.some.injEq] at h
        subst h
        cases hs : e.spreadArg? with
        | some p =>
          obtain ⟨sp, a⟩ := p
          cases e <;> simp [Expr.spreadArg?] at hs
          obtain ⟨rfl, rfl⟩ := hs
          rw [eval_spreadElem] at hx
          cases hx
        | none =>
          rw [evalElems_cons m fuel hs, hx, evalElems_of_evalList hxs]
          rfl

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
    simp [IR.Expr.evalList] at hv
    subst hv; simp [Eval.evalList]
  | cons e es ih =>
    intro ctx codes ctx' h
    simp [List.mapM_cons] at h
    obtain ⟨c, s₁, hc, cs, hcs, rfl⟩ := h
    intro ρs ρo vs ha hs hv
    simp only [List.map_cons, IR.Expr.evalList] at hv
    cases hx : IR.Expr.eval fs fuel ρo c.value with
    | none => simp [hx] at hv
    | some x =>
      cases hxs : IR.Expr.evalList fs fuel ρo (cs.map (·.value)) with
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
theorem zip_sim {env : Translate.Env} {g : Expr × Ty → TM IR.Expr}
    (hg : ∀ x t ctx o ctx', g (x, t) ctx = .ok o ctx' → Sim (N := N) m fs fuel env x o) :
    ∀ (args : List Expr) (ps : List Ty) (ctx : Ctx) (vals : List IR.Expr) (ctx' : Ctx),
      args.length ≤ ps.length → (args.zip ps).mapM g ctx = .ok vals ctx' →
      SimList (N := N) m fs fuel env args vals := by
  intro args
  induction args with
  | nil =>
    intro ps ctx vals ctx' _ h
    simp [List.mapM_nil] at h
    obtain ⟨rfl, -⟩ := h
    intro ρs ρo vs _ _ hv
    simp [IR.Expr.evalList] at hv
    subst hv; simp [Eval.evalList]
  | cons x xs ih =>
    intro ps ctx vals ctx' hlen h
    cases ps with
    | nil => simp at hlen
    | cons t ts =>
      simp [List.mapM_cons] at h
      obtain ⟨o, s₁, ho, os, hos, rfl⟩ := h
      intro ρs ρo vs ha hs hv
      simp only [IR.Expr.evalList] at hv
      cases hx : IR.Expr.eval fs fuel ρo o with
      | none => simp [hx] at hv
      | some w =>
        cases hxs : IR.Expr.evalList fs fuel ρo os with
        | none => simp [hx, hxs] at hv
        | some ws =>
          simp [hx, hxs] at hv
          subst hv
          have h1 := hg _ _ _ _ _ ho ρs ρo w ha hs hx
          have h2 := ih ts _ _ _ (by simpa using hlen) hos ρs ρo ws ha hs hxs
          simp [Eval.evalList, h1, h2]

/-- The output's list of codes, then `none` for each optional parameter that
a call leaves out, evaluates to the values of the codes, then `undefined` for
each. -/
theorem evalList_append_undefined {α : Type} (ρ : Eval.Env N) (missing : List α) :
    ∀ vals : List IR.Expr, IR.Expr.evalList fs fuel ρ (vals ++ missing.map fun _ => IR.Expr.undefined) =
      (IR.Expr.evalList fs fuel ρ vals).map (· ++ List.replicate missing.length .undefined)
  | [] => by
    simp only [List.nil_append]
    induction missing with
    | nil => simp [IR.Expr.evalList]
    | cons _ xs ih =>
      simp [IR.Expr.evalList, IR.Expr.eval, IR.ExprExt.apply, ih, List.replicate_succ]
  | v :: vals => by
    simp only [List.cons_append, IR.Expr.evalList, evalList_append_undefined ρ missing vals]
    cases IR.Expr.eval fs fuel ρ v <;> cases IR.Expr.evalList fs fuel ρ vals <;> simp

/-- A call that gives a value when it passes `undefined` for its last
parameters gives the same value when it leaves them out. -/
theorem callS_append_undefined {p : Eval.Program} {fuel : Nat} {key : DeclRef} {vs : List (Val N)} {k : Nat}
    {v : Except (Val N) (Val N)} (h : callS p fuel key (vs ++ List.replicate k .undefined) = some v) :
    callS p fuel key vs = some v := by
  cases fuel with
  | zero => simp [callS] at h
  | succ fuel =>
    simp only [callS] at h ⊢
    cases hl : (Eval.functionsOf p).lookup key with
    | none => simp [hl] at h
    | some pb =>
      obtain ⟨params, body⟩ := pb
      cases hb : Eval.bindArgs params (vs ++ List.replicate k .undefined) with
      | none => simp [hl, hb] at h
      | some env =>
        simp only [hl, hb, Option.bind_eq_bind, Option.bind_some] at h
        simp only [Eval.bindArgs_append_undefined hb, Option.bind_eq_bind, Option.bind_some]
        exact h

/-- `zip_sim` for translations that give a `Code`, whose value the output
uses. -/
theorem zip_sim_value {env : Translate.Env} {g : Expr × Ty → TM Code}
    (hg : ∀ x t ctx o ctx', g (x, t) ctx = .ok o ctx' → Sim (N := N) m fs fuel env x o.value) :
    ∀ (args : List Expr) (ps : List Ty) (ctx : Ctx) (codes : List Code) (ctx' : Ctx),
      args.length ≤ ps.length → (args.zip ps).mapM g ctx = .ok codes ctx' →
      SimList (N := N) m fs fuel env args (codes.map Code.value) := by
  intro args
  induction args with
  | nil =>
    intro ps ctx codes ctx' _ h
    simp [List.mapM_nil] at h
    obtain ⟨rfl, -⟩ := h
    intro ρs ρo vs _ _ hv
    simp [IR.Expr.evalList] at hv
    subst hv; simp [Eval.evalList]
  | cons x xs ih =>
    intro ps ctx codes ctx' hlen h
    cases ps with
    | nil => simp at hlen
    | cons t ts =>
      simp [List.mapM_cons] at h
      obtain ⟨o, s₁, ho, os, hos, rfl⟩ := h
      intro ρs ρo vs ha hs hv
      simp only [List.map_cons, IR.Expr.evalList] at hv
      cases hx : IR.Expr.eval fs fuel ρo o.value with
      | none => simp [hx] at hv
      | some w =>
        cases hxs : IR.Expr.evalList fs fuel ρo (os.map Code.value) with
        | none => simp [hx, hxs] at hv
        | some ws =>
          simp [hx, hxs] at hv
          subst hv
          have h1 := hg _ _ _ _ _ ho ρs ρo w ha hs hx
          have h2 := ih ts _ _ _ (by simpa using hlen) hos ρs ρo ws ha hs hxs
          simp [Eval.evalList, h1, h2]

omit [JSNumber N] in
/-- A result that `Except.toOption` takes a value from is that value. -/
@[simp] theorem bind_toOption {o : Option (Except (Val N) (Val N))} {v : Val N} :
    o.bind Except.toOption = some v ↔ o = some (.ok v) := by
  cases o with
  | none => simp
  | some r => cases r <;> simp [Except.toOption]

theorem evalCall_eq (name : String) (args : List Expr) (ρ : Eval.Env N) (hn : name ≠ "Number")
    (hl : ρ.lookup name = none) :
    Eval.evalCall m fuel ρ name args =
      (Eval.evalList m fuel ρ args).bind fun vs => (Eval.resolve m name).bind fun key =>
        callS m.program fuel key vs := by
  have hn' : (name == "Number") = false := by simpa using hn
  rw [Eval.evalCall]
  cases Eval.evalList m fuel ρ args <;> cases fuel <;> cases Eval.resolve m name <;>
    simp only [hn', hl, Bool.false_and, Bool.false_eq_true, ↓reduceIte] <;> rfl

theorem eval_call (sp sp' : Span) (name : String) (args : List Expr) (ρ : Eval.Env N)
    (hn : name ≠ "Number") (hl : ρ.lookup name = none) :
    Eval.eval m fuel ρ (.call sp (.ident sp' name) args) =
      ((Eval.evalList m fuel ρ args).bind fun vs => (Eval.resolve m name).bind fun key =>
        callS m.program fuel key vs).bind Except.toOption := by
  rw [Eval.eval, ← evalCall_eq _ _ _ _ _ hn hl]; rfl

/-- An expression that gives a value gives it at the top of a declaration or
a `return` too. -/
theorem evalTop_ok {e : Expr} {ρ : Eval.Env N} {w : Val N} (h : Eval.eval m fuel ρ e = some w) :
    Eval.evalTop m fuel ρ e = some (.ok w) := by
  rw [Eval.evalTop.eq_def]
  split
  · rw [Eval.eval] at h
    simpa only [Option.bind_eq_bind, bind_toOption] using h
  · simp [h]

/-- A call at the top of a declaration or a `return` gives what the call
returns or throws. -/
theorem evalTop_call (cs sp : Span) (name : String) (args : List Expr) (ρ : Eval.Env N) :
    Eval.evalTop m fuel ρ (.call cs (.ident sp name) args) = Eval.evalCall m fuel ρ name args := by
  rw [Eval.evalTop]

/-- `pure e`, which a function that can throw returns, has the value of `e`. -/
theorem eval_pureIf {p : Prop} [Decidable p] (e : IR.Expr) (ρ : Eval.Env N) :
    IR.Expr.eval fs fuel ρ (if p then IR.Expr.pure e else e) = IR.Expr.eval fs fuel ρ e := by
  split
  · simp only [IR.Expr.eval, IR.Expr.evalList]
    cases IR.Expr.eval fs fuel ρ e <;> rfl
  · rfl

theorem eval_call_toOption (sp sp' : Span) (name : String) (args : List Expr) (ρ : Eval.Env N) :
    Eval.eval m fuel ρ (.call sp (.ident sp' name) args) =
      (Eval.evalCall m fuel ρ name args).bind Except.toOption := by
  rw [Eval.eval]; rfl

theorem out_call_toOption (key : DeclRef) (args : List IR.Expr) (ρ : Eval.Env N) :
    IR.Expr.eval fs fuel ρ (.call key args) = (IR.Expr.evalCall fs fuel ρ key args).bind Except.toOption := by
  rw [IR.Expr.eval]; rfl

theorem out_evalCall (key : DeclRef) (args : List IR.Expr) (ρ : Eval.Env N) :
    IR.Expr.evalCall fs fuel ρ key args = (IR.Expr.evalList fs fuel ρ args).bind (callO fs fuel key) := by
  rw [IR.Expr.evalCall]
  cases IR.Expr.evalList fs fuel ρ args <;> cases fuel <;> rfl

theorem out_call (key : DeclRef) (args : List IR.Expr) (ρ : Eval.Env N) :
    IR.Expr.eval fs fuel ρ (.call key args) =
      ((IR.Expr.evalList fs fuel ρ args).bind (callO fs fuel key)).bind Except.toOption := by
  rw [IR.Expr.eval, ← out_evalCall]; rfl

/-- An operator that evaluates both operands: not `&&`, `||` or `??`. -/
def _root_.tolean.TypeScript.Syntax.BinOp.strict : BinOp → Bool
  | .and | .or | .coalesce => false
  | _ => true

theorem eval_binary (sp : Span) (op : BinOp) (l r : Expr) (ρ : Eval.Env N) (hop : op.strict = true) :
    Eval.eval m fuel ρ (.binary sp op l r) =
      (do Eval.binary op (← Eval.eval m fuel ρ l) (← Eval.eval m fuel ρ r)) := by
  cases op <;> simp [BinOp.strict] at hop <;> rw [Eval.eval] <;>
    first | rfl | (intro hc; cases hc)

/-- An operator that tests a value against `null` evaluates both operands. -/
theorem nullOp_strict {op : BinOp} {b : Bool} (h : nullOp? op = some b) : op.strict = true := by
  cases op <;> simp [nullOp?] at h <;> rfl

/-- With `null` on one side, an operator that `nullOp?` names gives whether
the other value is `null`, or the negation. -/
theorem nullOp_binary {op : BinOp} {b : Bool} (h : nullOp? op = some b) (w : Val N) (hw : w ≠ .undefined) :
    Eval.binary op w .null = some (.bool (if b then isNullVal w else !isNullVal w)) ∧
      Eval.binary op .null w = some (.bool (if b then isNullVal w else !isNullVal w)) := by
  cases op <;> simp [nullOp?] at h <;> subst h <;> cases w <;>
    simp_all +decide [Eval.binary, Eval.strictEq, Eval.looseEq, isNullVal]

omit [JSNumber N] in
theorem isUndefinedName_eq {e : Expr} (h : e.isUndefinedName = true) : ∃ s, e = .ident s "undefined" := by
  unfold Expr.isUndefinedName at h
  split at h
  · exact ⟨_, rfl⟩
  · simp at h

/-- The global `undefined`, when no variable hides it. -/
theorem eval_undefined {ρ : Eval.Env N} (s : Span) (h : ρ.lookup "undefined" = none) :
    Eval.eval m fuel ρ (.ident s "undefined") = some .undefined := by
  simp [Eval.eval, h]

/-- `===` with `undefined` tells whether the value is `undefined`. -/
theorem strictEq_undefined (w : Val N) :
    Eval.strictEq w .undefined = some (w matches .undefined) ∧
      Eval.strictEq .undefined w = some (w matches .undefined) := by
  cases w <;> simp [Eval.strictEq]

theorem isNull_eq_true {e : Expr} (h : e.isNull = true) : ∃ s, e = .null s := by
  cases e <;> simp [Expr.isNull] at h ⊢

theorem eval_stripParens (e : Expr) (ρ : Eval.Env N) :
    Eval.eval m fuel ρ e.stripParens = Eval.eval m fuel ρ e := by
  induction e using Expr.stripParens.induct with
  | case1 sp inner ih => simp only [Expr.stripParens, ih]; simp only [Eval.eval]
  | case2 e he => cases e <;> simp_all [Expr.stripParens]

omit [JSNumber N] in
/-- A read of one more property at the end of a path. -/
theorem getPath_append (f : String) : ∀ (fields : List (String × Val N)) (fs : List String), fs ≠ [] →
    Eval.getPath fields (fs ++ [f]) =
      (Eval.getPath fields fs).bind fun v => match v with
        | .obj inner => Eval.getProp inner f
        | _ => none
  | _, [], h => absurd rfl h
  | fields, [g], _ => by
    simp only [List.cons_append, List.nil_append, Eval.getPath]
    cases Eval.getProp fields g with
    | none => simp
    | some w => cases w <;> simp
  | fields, g :: h :: t, _ => by
    simp only [List.cons_append, Eval.getPath]
    cases Eval.getProp fields g with
    | none => simp
    | some w =>
      cases w with
      | obj inner =>
        have := getPath_append f inner (h :: t) (by simp)
        simp only [List.cons_append] at this
        simp [this]
      | _ => simp

/-- An optional chain that reads `path` from `base`: a `?.` that meets `null`
or `undefined` skips the rest, and otherwise the chain reads the path. -/
theorem evalChain_optChain {ρ : Eval.Env N} : ∀ {e base : Expr} {path : List String},
    e.optChain? = some (base, path) → ∀ {v : Val N}, Eval.eval m fuel ρ base = some v →
    Eval.evalChain m fuel ρ e = (match v with
      | .null | .undefined => some none
      | .obj fields => (Eval.getPath fields path).map some
      | _ => none)
  | .optMember sp obj f, base, path, h, v, hb => by
    simp only [Expr.optChain?, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [Eval.evalChain]
    cases v <;> simp [hb, Eval.getPath]
  | .member sp o f, base, path, h, v, hb => by
    simp only [Expr.optChain?, Option.map_eq_some_iff] at h
    obtain ⟨⟨b, fs⟩, ho, heq⟩ := h
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    have hne : fs ≠ [] := by
      intro hfs; subst hfs
      cases o <;> simp [Expr.optChain?] at ho
    have ih := evalChain_optChain (e := o) ho hb
    rw [Eval.evalChain, ih]
    cases v with
    | obj fields =>
      simp only [getPath_append f fields fs hne]
      cases Eval.getPath fields fs with
      | none => simp
      | some w => cases w <;> simp
    | _ => simp
  | .ident .., _, _, h, _, _ | .number .., _, _, h, _, _ | .bigint .., _, _, h, _, _
  | .string .., _, _, h, _, _ | .bool .., _, _, h, _, _ | .null _, _, _, h, _, _ | .array .., _, _, h, _, _
  | .object .., _, _, h, _, _ | .paren .., _, _, h, _, _ | .index .., _, _, h, _, _ | .call .., _, _, h, _, _
  | .unary .., _, _, h, _, _ | .prefix .., _, _, h, _, _ | .postfix .., _, _, h, _, _
  | .binary .., _, _, h, _, _ | .cond .., _, _, h, _, _ | .assign .., _, _, h, _, _
  | .arrow .., _, _, h, _, _ => by simp [Expr.optChain?] at h

/-- A property read after an optional chain reads the chain's path, or gives
`undefined` where the `?.` meets `null` or `undefined`. -/
theorem eval_member_chain {ρ : Eval.Env N} {sp : Span} {obj base : Expr} {name : String} {path : List String}
    (hsp : obj.optSpine = true) (h : (Expr.member sp obj name).optChain? = some (base, path)) {v : Val N}
    (hb : Eval.eval m fuel ρ base = some v) :
    Eval.eval m fuel ρ (.member sp obj name) = (match v with
      | .null | .undefined => some .undefined
      | .obj fields => Eval.getPath fields path
      | _ => none) := by
  simp only [Expr.optChain?, Option.map_eq_some_iff] at h
  obtain ⟨⟨b, fs⟩, ho, heq⟩ := h
  simp only [Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl⟩ := heq
  have hne : fs ≠ [] := by
    intro hfs; subst hfs
    cases obj <;> simp [Expr.optChain?] at ho
  rw [Eval.eval, if_pos hsp, evalChain_optChain m fuel ho hb]
  cases v with
  | obj fields =>
    simp only [getPath_append name fields fs hne]
    cases Eval.getPath fields fs with
    | none => simp
    | some w => cases w <;> simp
  | _ => simp

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
    (hs : Scoped m env ρ) :
    ∃ w, ρ.lookup name = some w ∧ (w ≠ .undefined →
      Eval.eval m fuel ρ l = some (.bool (if isNullTest then isNullVal w else !isNullVal w))) := by
  unfold nullTestOf at h
  rw [← eval_stripParens]
  generalize l.stripParens = e at h ⊢
  cases e with
  | binary sp op a b =>
    simp only at h
    cases hop : nullOp? op with
    | none => simp [hop] at h
    | some isEq =>
      simp only [hop] at h
      rw [eval_binary m fuel sp op a b ρ (nullOp_strict hop)]
      have hb := nullOp_binary (N := N) hop
      split at h
      · rename_i s0 n0 hother
        split at h
        · rename_i n1 b1 t1 hloc
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          have hhas : env.has n0 = true := by simp [Env.has, hloc]
          obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp (hs.some hhas)
          have hid : Eval.eval m fuel ρ (.ident s0 n0) = some w := by simp [Eval.eval, hw]
          refine ⟨w, hw, fun hwu => ?_⟩
          split at hother
          · rename_i hbn
            obtain ⟨sb, rfl⟩ := isNull_eq_true hbn
            simp only [Option.some.injEq] at hother
            subst hother
            rw [hid]
            simp [Eval.eval, (hb w hwu).1]
          · split at hother
            · rename_i _ ha
              obtain ⟨sa, rfl⟩ := isNull_eq_true ha
              simp only [Option.some.injEq] at hother
              subst hother
              rw [hid]
              simp [Eval.eval, (hb w hwu).2]
            · simp at hother
        · simp at h
      · simp at h
  | _ => simp at h

/-- Whether a value is `undefined`. -/
def isUndefVal : Val N → Bool
  | .undefined => true
  | _ => false

/-- What a test that `undefinedTestOf` finds evaluates to: whether the local
is `undefined`, or the negation. `===` with `undefined` is defined for every
value, so this holds whatever the local holds. -/
theorem undefinedTestOf_eval {env : Translate.Env} {l : Expr} {name : String} {isEq : Bool}
    {value : Ty} (h : undefinedTestOf env l = some (name, isEq, value)) {ρ : Eval.Env N}
    (hs : Scoped m env ρ) :
    ∃ w, ρ.lookup name = some w ∧
      Eval.eval m fuel ρ l = some (.bool (if isEq then isUndefVal w else !isUndefVal w)) := by
  unfold undefinedTestOf at h
  split at h
  · simp at h
  rename_i hu
  have hund : ρ.lookup "undefined" = none := hs.none (by simpa using hu)
  have hund' : ∀ s, Eval.eval m fuel ρ (.ident s "undefined") = some .undefined := by
    intro s; simp [Eval.eval, hund]
  rw [← eval_stripParens]
  generalize l.stripParens = e at h ⊢
  cases e with
  | binary sp op a b =>
    simp only at h
    cases op <;> simp only at h <;> (try simp at h; done)
    all_goals
      rw [eval_binary m fuel sp _ a b ρ rfl]
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
          · rename_i hbn
            obtain ⟨sb, rfl⟩ := isUndefinedName_eq hbn
            simp only [Option.some.injEq] at hother
            subst hother
            rw [hid, hund']
            cases w <;> simp [Eval.binary, Eval.strictEq, isUndefVal]
          · split at hother
            · rename_i _ ha
              obtain ⟨sa, rfl⟩ := isUndefinedName_eq ha
              simp only [Option.some.injEq] at hother
              subst hother
              rw [hid, hund']
              cases w <;> simp [Eval.binary, Eval.strictEq, isUndefVal]
            · simp at hother
        · simp at h
      · simp at h
  | _ => simp at h

/-- The two sides that `tagSide` reads: a read of the tag of the local `n`,
as `n.kind` or `typeof n`, and the string `t`, in either order. The read
gives the tag that the IR's evaluator reads. -/
theorem tagSide_eval {l r : Expr} {n : String} {f : Option String} {t : String}
    (h : tagSide l r = some (n, f, t)) {ρ : Eval.Env N} {w : Val N} (hw : ρ.lookup n = some w)
    {k : JSString} (hk : IR.tagOf f w = some k) :
    (Eval.eval m fuel ρ l = some (.str k) ∧ Eval.eval m fuel ρ r = some (.str (.ofString t))) ∨
      (Eval.eval m fuel ρ l = some (.str (.ofString t)) ∧ Eval.eval m fuel ρ r = some (.str k)) := by
  have hfield : ∀ sp sp' field, f = some field →
      Eval.eval m fuel ρ (.member sp (.ident sp' n) field) = some (.str k) := by
    rintro sp sp' field rfl
    cases w with
    | obj fields =>
      simp only [IR.tagOf] at hk
      split at hk
      · rename_i k' hk'
        simp only [Option.some.injEq] at hk
        subst hk
        simp [Eval.eval, hw, Eval.getProp, hk', Expr.optSpine]
      · simp at hk
    | _ => simp [IR.tagOf] at hk
  have htype : ∀ sp sp', f = none →
      Eval.eval m fuel ρ (.unary sp .typeof (.ident sp' n)) = some (.str k) := by
    rintro sp sp' rfl
    simp only [IR.tagOf, Option.some.injEq] at hk
    subst hk
    simp [Eval.eval, hw]
  unfold tagSide at h
  split at h <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  all_goals obtain ⟨rfl, rfl, rfl⟩ := h
  · exact .inl ⟨hfield _ _ _ rfl, by simp [Eval.eval]⟩
  · exact .inr ⟨by simp [Eval.eval], hfield _ _ _ rfl⟩
  · exact .inl ⟨htype _ _ rfl, by simp [Eval.eval]⟩
  · exact .inr ⟨by simp [Eval.eval], htype _ _ rfl⟩

/-- A test that `tagTestOf` finds gives whether the local's tag is the one it
names, when the IR's evaluator reads a tag from the local. -/
theorem tagTestOf_eval {env : Translate.Env} {e : Expr} {t : TagTest}
    (h : tagTestOf env e = some t) {ρ : Eval.Env N} (hs : Scoped m env ρ) :
    ∃ w, ρ.lookup t.name = some w ∧ ∀ k, IR.tagOf t.field w = some k →
      Eval.eval m fuel ρ e =
        some (.bool (if t.isEq then k == .ofString t.tag else !(k == .ofString t.tag))) := by
  unfold tagTestOf at h
  rw [← eval_stripParens]
  generalize e.stripParens = e' at h ⊢
  cases e' with
  | binary sp op l r =>
    simp only [Option.bind_eq_bind] at h
    split at h
    · rename_i hop
      have hop' : op = .strictEq ∨ op = .strictNe := by
        revert hop; cases op <;> first | (intro; left; rfl) | (intro; right; rfl) | decide
      simp only [Option.pure_def, Option.bind_some, Option.bind_eq_some_iff] at h
      obtain ⟨⟨n, f, tg⟩, hside, loc, hloc, h⟩ := h
      split at h
      · rename_i ref tags hty
        try dsimp only at h hloc
        cases hu : List.find? (fun x => x.ref == ref) env.unions with
        | none => rw [hu] at h; simp at h
        | some u =>
        rw [hu] at h
        simp only [Option.bind_some] at h
        cases hm : List.lookup tg u.members with
        | none => rw [hm] at h; simp at h
        | some member =>
        rw [hm] at h
        simp only [Option.bind_some] at h
        split at h
        · simp only [Option.some.injEq] at h
          subst h
          have hhas : env.has n = true := by simp [Env.has, hloc]
          obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp (hs.some hhas)
          refine ⟨w, hw, ?_⟩
          intro k hk
          rw [eval_binary m fuel sp op l r ρ (by rcases hop' with rfl | rfl <;> rfl)]
          rcases tagSide_eval m fuel hside hw hk with ⟨hl, hr⟩ | ⟨hl, hr⟩ <;>
            rcases hop' with rfl | rfl <;>
            simp +decide [hl, hr, Eval.binary, Eval.strictEq]
          all_goals by_cases hkt : k = .ofString tg
          all_goals first
            | (simp_all; done)
            | simp [hkt, show ¬ JSString.ofString tg = k from fun e => hkt e.symm]
        · simp at h
      · simp at h
    · simp at h
  | _ => simp at h

/-- A value that becomes a member of a union of primitive types keeps its
value: the evaluator gives a member's constructor the value inside. -/
theorem eval_into (unions : List UnionInfo) (c : Code) (expected : Option Ty) (ρ : Eval.Env N) :
    IR.Expr.eval fs fuel ρ (c.into unions expected).code = IR.Expr.eval fs fuel ρ c.code := by
  unfold Code.into
  repeat' split
  all_goals simp [IR.Expr.eval, eval_value]

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

/-- A bigint literal is never negative. -/
theorem bigintLiteral_nonneg {text : String} {n : Int} (h : Eval.bigintLiteral text = some n) :
    0 ≤ n := by
  unfold Eval.bigintLiteral at h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨k, -, rfl⟩ := h
  exact Int.ofNat_le.mpr (Nat.zero_le k)

/-- A bigint literal that `bigintLiteralNat?` reads, in any parentheses,
evaluates to its value. -/
theorem bigintLiteralNat_eval (e : Expr) {k : Nat} (h : bigintLiteralNat? e = some k) :
    ∀ ρ : Eval.Env N, Eval.eval m fuel ρ e = some (.int k) := by
  induction e using bigintLiteralNat?.induct with
  | case1 sp inner ih =>
    simp only [bigintLiteralNat?] at h
    exact fun ρ => by rw [Eval.eval]; exact ih h ρ
  | case2 sp text =>
    simp only [bigintLiteralNat?, bigintValue?] at h
    cases hb : Eval.bigintLiteral text with
    | none => simp [hb] at h
    | some n =>
      simp only [hb, Option.map_some, Option.some.injEq] at h
      have := bigintLiteral_nonneg hb
      subst h
      intro ρ
      simp [Eval.eval, hb, Int.toNat_of_nonneg this]
  | case3 e h1 h2 => simp [bigintLiteralNat?] at h

/-- `a ** k` on bigints, with a literal `k`: the interpreter raises the value
of `a` to the power `k`, which is not negative. -/
theorem binary_exp_literal {l r : Expr} {ρ : Eval.Env N} {k : Nat} {x : Int}
    (hk : bigintLiteralNat? r = some k) (hl : Eval.eval m fuel ρ l = some (.int x)) :
    (do Eval.binary .exp (← Eval.eval m fuel ρ l) (← Eval.eval m fuel ρ r)) =
      some (Val.int (x ^ k)) := by
  rw [hl, bigintLiteralNat_eval m fuel r hk ρ]
  have hk0 : ¬ ((k : Int) < 0) := by omega
  simp [Eval.binary, hk0]

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

/-- The parts that `concatParts?` picks convert the operands as the
interpreter's rule for `+` does. -/
theorem concatParts?_binary {s t : Ty} {left right : IR.StringPart}
    (hp : concatParts? s t = some (left, right)) {x y : Val N} {sx sy : JSString}
    (hx : left.toStr x = some sx) (hy : right.toStr y = some sy) :
    Eval.binary .add x y = some (.str (sx ++ sy)) := by
  unfold concatParts? at hp
  split at hp <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hp <;>
    obtain ⟨rfl, rfl⟩ := hp <;>
    cases x <;> cases y <;> simp_all [IR.StringPart.toStr, Eval.binary]

omit [JSNumber N] in
/-- `concatOperands` joins the operands with the parts that `concatParts?`
picks. -/
theorem concatOperands_ok {s : Span} {a b c : Code} {ctx ctx' : Ctx}
    (h : concatOperands s a b ctx = .ok c ctx') :
    ∃ left right, concatParts? a.type b.type = some (left, right) ∧
      c = ⟨.ext (.stringAppend left right) [a.value, b.value], false, .string⟩ := by
  unfold concatOperands at h
  cases hp : concatParts? a.type b.type with
  | none => simp [hp] at h
  | some p =>
    obtain ⟨left, right⟩ := p
    simp only [hp, pure_ok] at h
    exact ⟨left, right, rfl, h.1.symm⟩

/-- `a + b` with a string operand means what the interpreter's rule for `+`
means, when each operand's code means what the operand means. -/
theorem concat_sound {sp s : Span} {l r : Expr} {a b c : Code} {ctx ctx' : Ctx}
    {ρs ρo : Eval.Env N} {v : Val N}
    (h : concatOperands s a b ctx = .ok c ctx')
    (hl : ∀ w, IR.Expr.eval fs fuel ρo a.code = some w → Eval.eval m fuel ρs l = some w)
    (hr : ∀ w, IR.Expr.eval fs fuel ρo b.code = some w → Eval.eval m fuel ρs r = some w)
    (hv : IR.Expr.eval fs fuel ρo c.code = some v) :
    Eval.eval m fuel ρs (.binary sp .add l r) = some v := by
  obtain ⟨left, right, hp, rfl⟩ := concatOperands_ok h
  obtain ⟨x, y, sx, sy, hx, hy, hsx, hsy, rfl⟩ := out_stringAppend fs fuel hv
  rw [eval_value] at hx hy
  rw [eval_binary m fuel sp _ l r ρs rfl, hl _ hx, hr _ hy]
  exact concatParts?_binary hp hsx hsy

-- The value type has many constructors, and `cases` on a value makes a goal
-- for each, so this proof takes more than the default heartbeats.
set_option maxHeartbeats 400000 in
/-- The operator step means what the interpreter's rule for the operator
means, when each operand's code means what the operand means. -/
theorem applyOperator_sound {sp s : Span} {op : BinOp} {l r : Expr} {a b c : Code} {ctx ctx' : Ctx}
    {ρs ρo : Eval.Env N} {v : Val N}
    (h : applyOperator s op r a b ctx = .ok c ctx')
    (hl : ∀ w, IR.Expr.eval fs fuel ρo a.code = some w → Eval.eval m fuel ρs l = some w)
    (hr : ∀ w, IR.Expr.eval fs fuel ρo b.code = some w → Eval.eval m fuel ρs r = some w)
    (hv : IR.Expr.eval fs fuel ρo c.code = some v) :
    Eval.eval m fuel ρs (.binary sp op l r) = some v := by
  unfold applyOperator at h
  cases op
  all_goals simp only [ite_state] at h
  all_goals (repeat' split at h)
  -- `+` with a string operand.
  case add.isTrue => exact concat_sound m fs fuel h hl hr hv
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
    | (obtain ⟨x, y, hx, hy, rfl⟩ := out_stringOrder fs fuel hv
       rw [eval_value] at hx hy
       first
         | (rw [hl _ hx, hr _ hy]; rfl)
         | (rw [hl _ hy, hr _ hx]; rfl))
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
       simp [Eval.binary, hy0, IR.Division.apply])
    | (obtain ⟨x, y, hx, hy, rfl⟩ := out_bigintOp fs fuel hv
       rw [eval_value] at hx hy
       rw [hl _ hx, hr _ hy]; rfl)
    | (obtain ⟨x, hx, rfl⟩ := out_bigintPow fs fuel hv
       rw [eval_value] at hx
       exact binary_exp_literal m fuel (by assumption) (hl _ hx))
    | (obtain ⟨x, y, t, hx, hy, ht, rfl⟩ := out_eq fs fuel hv
       rw [eval_value] at hx hy
       rw [hl _ hx, hr _ hy]
       cases x <;> cases y <;> simp_all [IR.eqVal, Eval.binary, Eval.strictEq])
    | (obtain ⟨x, y, t, hx, hy, ht, rfl⟩ := out_ne fs fuel hv
       rw [eval_value] at hx hy
       rw [hl _ hx, hr _ hy]
       cases x <;> cases y <;> simp_all [IR.eqVal, Eval.binary, Eval.strictEq])

/-! ### Methods of a string -/

/-- A method of a string that takes no callback, other than `at` and `slice`,
which have rules of their own: the interpreter evaluates the receiver, then
the arguments, and `stringMethod` gives the value. A call with one argument
reaches the rule of `get` and `has`, which passes a string on to
`stringMethod` too. -/
theorem eval_stringCall (sp sp' : Span) (recv : Expr) (method : String) (args : List Expr)
    (hr : recv.namesNumber = false) (harg : args.any (·.isArrow) = false) (hat : method ≠ "at")
    (hsl : method ≠ "slice") (ρ : Eval.Env N) {t : JSString}
    (hrecv : Eval.eval m fuel ρ recv = some (.str t)) :
    Eval.eval m fuel ρ (.call sp (.member sp' recv method) args) =
      (Eval.evalList m fuel ρ args).bind (Eval.stringMethod method t) := by
  have hr' : ∀ s, recv ≠ .ident s "Number" := by
    intro s h; subst h; simp [Expr.namesNumber] at hr
  have hrM : ∀ s, recv ≠ .ident s "Math" := by
    intro s h; subst h; simp [Expr.namesNumber] at hr
  have hrO : ∀ s, recv ≠ .ident s "Object" := by
    intro s h; subst h; simp [Expr.namesNumber] at hr
  have hrD : ∀ s, recv ≠ .ident s "Date" := by
    intro s h; subst h; simp [Expr.namesNumber] at hr
  rcases args with _ | ⟨a, _ | ⟨b, rest⟩⟩
  all_goals rw [Eval.eval]
  all_goals first
    | (rw [hrecv]
       first
         | rfl
         | (cases ha : Eval.eval m fuel ρ a <;> simp [Eval.evalList, ha]))
    | exact hr'
    | exact hrM
    | exact hrO
    | exact hrD
    | (intro _ h _; exact hrD _ h)
    | (intros; contradiction)
    | (intros; subst_vars; exact absurd rfl (hr' _))
    | (intros; subst_vars; exact absurd rfl (hrM _))
    | (intros; subst_vars; exact absurd rfl (hrO _))
    | (intros; subst_vars; exact absurd rfl (hrD _))
    | (clear hrecv; intros; simp_all [Expr.isArrow]; done)
    | (intros; subst_vars; exact absurd rfl hat)
    | (intros; subst_vars; exact absurd rfl hsl)

/-- A method that `stringMethod` gives a value for is not `at` or `slice`. -/
theorem stringMethod_not_at {method : String} {t : JSString} {vs : List (Val N)} {v : Val N}
    (h : Eval.stringMethod method t vs = some v) : method ≠ "at" ∧ method ≠ "slice" := by
  constructor <;> (intro he; subst he; simp [Eval.stringMethod] at h)

/-- The method that `stringMethod?` picks gives the value that the
interpreter's `stringMethod` gives. -/
theorem stringMethod_of {method : String} {sm : IR.StringMethod} (hm : stringMethod? method = some sm)
    (t : JSString) (vs : List (Val N)) : Eval.stringMethod method t vs = sm.apply t vs := by
  unfold stringMethod? at hm
  repeat' split at hm
  all_goals first
    | (cases hm
       rename_i hmm
       simp only [beq_iff_eq] at hmm
       subst hmm
       simp [Eval.stringMethod, IR.StringMethod.apply])
    | simp at hm

/-- The code of `stringCall` evaluates the receiver to a string and the
arguments, and its value is the one that `stringMethod` gives them. -/
theorem stringCall_sound {s : Span} {method : String} {str : Code} {args : List Code}
    {ctx ctx' : Ctx} {c : Code} (h : stringCall s method str args ctx = .ok c ctx')
    {ρ : Eval.Env N} {v : Val N} (hv : IR.Expr.eval fs fuel ρ c.code = some v) :
    ∃ t vs, IR.Expr.eval fs fuel ρ str.value = some (.str t) ∧
      IR.Expr.evalList fs fuel ρ (args.map Code.value) = some vs ∧
      Eval.stringMethod method t vs = some v := by
  unfold stringCall at h
  split at h
  · cases hm : stringMethod? method with
    | none => simp [hm] at h
    | some sm =>
      simp only [hm] at h
      split at h
      · split at h
        · simp only [bind_ok, pure_ok] at h
          obtain ⟨_, _, -, rfl, -⟩ := h
          simp only [IR.Expr.eval, IR.Expr.evalList] at hv
          cases hx : IR.Expr.eval fs fuel ρ str.value with
          | none => simp [hx] at hv
          | some w =>
            cases hy : IR.Expr.evalList fs fuel ρ (args.map Code.value) with
            | none => simp [hx, hy] at hv
            | some vs =>
              simp only [hx, hy, Option.bind_eq_bind, Option.bind_some] at hv
              cases w <;> simp [IR.ExprExt.apply] at hv
              rename_i t
              exact ⟨t, vs, rfl, rfl, by rw [stringMethod_of hm]; exact hv⟩
        · simp at h
      · simp at h
  · simp at h

/-- A string that becomes the constructor of a literal union has the same
value: the evaluator gives a constructor its string. -/
theorem enumOperand_code (known : List EnumInfo) (c : Code) (t : Ty) (ρ : Eval.Env N) :
    IR.Expr.eval fs fuel ρ (enumOperand known c t).code = IR.Expr.eval fs fuel ρ c.code := by
  unfold enumOperand
  split
  · rename_i m ref hc
    split
    · simp [hc, IR.Expr.eval]
    · rfl
  · rfl

/-- The operator step means what the interpreter's rule for the operator
means, when each operand's code means what the operand means. -/
theorem operator_sound {sp s : Span} {op : BinOp} {l r : Expr} {a b c : Code} {ctx ctx' : Ctx}
    {ρs ρo : Eval.Env N} {v : Val N}
    (h : translateOperator s op r a b ctx = .ok c ctx')
    (hl : ∀ w, IR.Expr.eval fs fuel ρo a.code = some w → Eval.eval m fuel ρs l = some w)
    (hr : ∀ w, IR.Expr.eval fs fuel ρo b.code = some w → Eval.eval m fuel ρs r = some w)
    (hv : IR.Expr.eval fs fuel ρo c.code = some v) :
    Eval.eval m fuel ρs (.binary sp op l r) = some v := by
  unfold translateOperator at h
  simp only [bind_ok, get_ok] at h
  obtain ⟨_, _, ⟨rfl, rfl⟩, h⟩ := h
  exact applyOperator_sound m fs fuel h
    (fun w hw => hl w (by rwa [enumOperand_code] at hw))
    (fun w hw => hr w (by rwa [enumOperand_code] at hw)) hv

-- The value type has many constructors, and `cases` on a value makes a goal
-- for each, so this proof takes more than the default heartbeats.
set_option maxHeartbeats 400000 in
/-- `translateBinary` is sound, when `translateExpr` is with one unit of fuel less. -/
theorem translateBinary_sound {F : Nat}
    (ihE : ∀ env exp e ctx c ctx', translateExpr F env exp e ctx = .ok c ctx' →
      Sim (N := N) m fs fuel env e c.code) :
    ∀ env sp op l r ctx c ctx', translateBinary (F + 1) env sp op l r ctx = .ok c ctx' →
      Sim (N := N) m fs fuel env (.binary sp op l r) c.code := by
  intro env sp op l r ctx c ctx' h
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
  · -- `a ?? b`: the value of `a`, unless it is `null`.
    rename_i hco
    obtain rfl : op = .coalesce := by cases op <;> first | rfl | exact absurd hco (by decide)
    simp only [bind_ok] at h
    obtain ⟨a, s₁, ha, h⟩ := h
    cases hty : a.type with
    | nullable value | optional value =>
      simp only [hty, bind_ok] at h
      obtain ⟨b, s₂, hb, h⟩ := h
      have hcode : ∃ nb, c.code = .coalesce a.value b.value nb := by
        repeat' split at h
        all_goals simp at h
        all_goals first | exact ⟨_, (congrArg Code.code h.1).symm⟩ | simp_all
      obtain ⟨nb, hcode⟩ := hcode
      intro ρs ρo v hag hs hv
      rw [hcode] at hv
      obtain ⟨w, hw, hcase⟩ := out_coalesce fs fuel hv
      rw [eval_value] at hw
      rw [Eval.eval, ihE _ _ _ _ _ _ ha ρs ρo w hag hs hw]
      rcases hcase with ⟨hnu, hbv⟩ | ⟨hn, hu, hvw⟩
      · rw [eval_value] at hbv
        rcases hnu with rfl | rfl <;> exact ihE _ _ _ _ _ _ hb ρs ρo v hag hs hbv
      · rw [hvw]
        cases w <;> simp_all [isNullVal]
    | _ => simp [hty] at h
  split at h
  · -- `x === undefined` and `x !== undefined`, on an optional value.
    rename_i hund
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hund
    obtain ⟨⟨hside, hnu⟩, hop⟩ := hund
    replace hop : op = .strictEq ∨ op = .strictNe := by
      revert hop; cases op <;> simp +decide
    simp only [pure_bind, bind_ok] at h
    obtain ⟨o, s₁, ho, h⟩ := h
    cases hty : o.type <;> simp [hty] at h
    obtain ⟨rfl, -⟩ := h
    intro ρs ρo v hag hs hv
    have hstrict : op.strict = true := by rcases hop with rfl | rfl <;> rfl
    rw [eval_binary m fuel sp op l r ρs hstrict]
    have hlook : ρs.lookup "undefined" = none := hs.none hnu
    obtain ⟨w, hw, rfl⟩ : ∃ w, IR.Expr.eval fs fuel ρo o.code = some w ∧
        v = .bool (if op = .strictEq then (w matches .undefined) else !(w matches .undefined)) := by
      have he : (BinOp.strictEq == BinOp.strictEq) = true := rfl
      have hn : (BinOp.strictNe == BinOp.strictEq) = false := rfl
      cases hx : IR.Expr.eval fs fuel ρo o.code with
      | none =>
        rcases hop with rfl | rfl <;> simp [he, hn, IR.Expr.eval, IR.Expr.evalList, hx] at hv
      | some w =>
        refine ⟨w, rfl, ?_⟩
        rcases hop with rfl | rfl <;>
          simp [he, hn, IR.Expr.eval, IR.Expr.evalList, hx, IR.ExprExt.apply] at hv <;> (subst hv; cases w <;> rfl)
    have hw' := ihE _ _ _ _ _ _ ho ρs ρo w hag hs hw
    have hu := strictEq_undefined (N := N) w
    by_cases hl : l.isUndefinedName = true
    · obtain ⟨sl, rfl⟩ := isUndefinedName_eq hl
      simp only [hl, ↓reduceIte] at hw'
      rcases hop with rfl | rfl <;> simp [eval_undefined m fuel sl hlook, hw', Eval.binary, hu.2]
    · have hr : r.isUndefinedName = true := by simpa [hl] using hside
      obtain ⟨sr, rfl⟩ := isUndefinedName_eq hr
      simp only [hl, Bool.false_eq_true, ↓reduceIte] at hw'
      rcases hop with rfl | rfl <;> simp [eval_undefined m fuel sr hlook, hw', Eval.binary, hu.1]
  split at h
  · -- `x === null` and `x !== null`, or `==` and `!=`.
    rename_i hnull
    obtain ⟨isEq, hop⟩ := Option.isSome_iff_exists.mp ((Bool.and_eq_true _ _).mp hnull).1
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
      rw [eval_binary m fuel sp op l r ρs (nullOp_strict hop)]
      have hb := nullOp_binary (N := N) hop
      obtain ⟨w, hw, hu, rfl⟩ : ∃ w, IR.Expr.eval fs fuel ρo o.code = some w ∧ w ≠ .undefined ∧
          v = .bool (if isEq then isNullVal w else !isNullVal w) := by
        rw [hop] at hv
        cases isEq <;> simp at hv
        · obtain ⟨w, hw, hu, rfl⟩ := out_isSome fs fuel hv
          exact ⟨w, hw, hu, by simp⟩
        · obtain ⟨w, hw, hu, rfl⟩ := out_isNone fs fuel hv
          exact ⟨w, hw, hu, by simp⟩
      have hw' := key w hw
      by_cases hl : l.isNull = true
      · obtain ⟨sl, rfl⟩ := isNull_eq_true hl
        simp [Expr.isNull] at hw'
        simp [hw', Eval.eval, (hb w hu).2]
      · have hr : r.isNull = true := by simpa [hl] using hside
        obtain ⟨sr, rfl⟩ := isNull_eq_true hr
        simp [hl] at hw'
        simp [hw', Eval.eval, (hb w hu).1]
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
          by_cases hu : w = .undefined
          · subst hu; simp [IR.Expr.eval, hso] at hv
          replace hl := hl hu
          have hs' : Scoped m (env.narrow name value) ρs :=
            ⟨fun x => by rw [narrow_has]; exact hs.1 x, hs.2⟩
          have hr := fun u hu => ihE _ _ _ _ _ _ hws ρs ρo u hag hs' hu
          have hcases : (op = .or ∧ isNullTest = true) ∨ (op = .and ∧ isNullTest = false) := by
            revert hcond; cases op <;> cases isNullTest <;> simp +decide
          rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rw [Eval.eval, hl] <;>
            cases w <;> simp +decide [IR.Expr.eval, hso, isNullVal, Val.truthy, eval_value] at hv ⊢
          all_goals first | exact hr v hv | (subst hv; rfl) | (subst hv; simp +decide)
        · simp at h
      · exact general h

/-! ### Array methods with a callback -/

/-- The value of an array method with a callback, from the value of the array. -/
def methodVal (method : IR.ListMethod) (ρ : Eval.Env N) (name : String) (body : Expr)
    (items : List (Val N)) : Option (Val N) :=
  match method with
  | .map => do return .list (← Eval.evalMap m fuel ρ name body items)
  | .filter => do return .list (← Eval.evalFilter m fuel ρ name body items)
  | .any => do return .bool (← Eval.evalFind m fuel ρ name body true items).isSome
  | .all => do return .bool (← Eval.evalFind m fuel ρ name body false items).isNone
  | .find => do return (← Eval.evalFind m fuel ρ name body true items).getD .undefined
  | .mapIdx index => do return .list (← Eval.evalMapIdx m fuel ρ name index body 0 items)
  | .findIndex => do
    return .num (JSNumber.ofSafeInt (((← Eval.evalFindIdx m fuel ρ name body 0 items).map Int.ofNat).getD (-1)))
  | .findLast => do return (← Eval.evalFind m fuel ρ name body true items.reverse).getD .undefined
  | .sortWith other => do return .list (← Eval.sortValues (Eval.evalCompare m fuel ρ name other body) items)

theorem eval_arrayMethod (sp sp' sa : Span) (par : Bool) (recv : Expr) (name : String) (p : Param)
    (body : Expr) (method : IR.ListMethod) (hm : listMethod? name = some method)
    (hr : recv.namesNumber = false) (ρ : Eval.Env N) :
    Eval.eval m fuel ρ (.call sp (.member sp' recv name) [.arrow sa par [p] body]) =
      (Eval.eval m fuel ρ recv).bind fun
        | .list items => methodVal m fuel method ρ p.name body items
        | _ => none := by
  have key : ∀ items : List (Val N),
      (if name = "map" then (Eval.evalMap m fuel ρ p.name body items).bind (fun r => some (Val.list r))
      else if name = "filter" then (Eval.evalFilter m fuel ρ p.name body items).bind (fun r => some (Val.list r))
      else if name = "some" then (Eval.evalFind m fuel ρ p.name body true items).bind (fun r => some (Val.bool r.isSome))
      else if name = "every" then (Eval.evalFind m fuel ρ p.name body false items).bind (fun r => some (Val.bool r.isNone))
      else if name = "find" then (Eval.evalFind m fuel ρ p.name body true items).bind (fun r => some (r.getD .undefined))
      else if name = "findIndex" then (Eval.evalFindIdx m fuel ρ p.name body 0 items).bind
        (fun r => some (Val.num (JSNumber.ofSafeInt ((r.map Int.ofNat).getD (-1)))))
      else if name = "findLast" then
        (Eval.evalFind m fuel ρ p.name body true items.reverse).bind (fun r => some (r.getD .undefined))
      else none) = methodVal m fuel method ρ p.name body items := by
    intro items
    unfold listMethod? at hm
    by_cases h1 : name = "map" <;> simp [h1] at hm ⊢
    · subst hm; rfl
    by_cases h2 : name = "filter" <;> simp [h2] at hm ⊢
    · subst hm; rfl
    by_cases h3 : name = "some" <;> simp [h3] at hm ⊢
    · subst hm; rfl
    by_cases h4 : name = "every" <;> simp [h4] at hm ⊢
    · subst hm; rfl
    by_cases h5 : name = "find" <;> simp [h5] at hm ⊢
    · subst hm; rfl
    by_cases h6 : name = "findIndex" <;> simp [h6] at hm ⊢
    · subst hm; rfl
    by_cases h7 : name = "findLast" <;> simp [h7] at hm ⊢
    subst hm; rfl
  have hr' : ∀ s, recv ≠ .ident s "Number" := by
    intro s h; subst h; simp [Expr.namesNumber] at hr
  have hrM : ∀ s, recv ≠ .ident s "Math" := by
    intro s h; subst h; simp [Expr.namesNumber] at hr
  have hrO : ∀ s, recv ≠ .ident s "Object" := by
    intro s h; subst h; simp [Expr.namesNumber] at hr
  have hrD : ∀ s, recv ≠ .ident s "Date" := by
    intro s h; subst h; simp [Expr.namesNumber] at hr
  generalize hR : Eval.eval m fuel ρ recv = r
  rw [Eval.eval]
  · rw [hR]
    cases r with
    | none => rfl
    | some v =>
      cases v <;> simp only [Option.bind_some, Option.bind_eq_bind]
      all_goals first | rfl | (rw [← key]; simp)
  all_goals first | exact hr' | exact hrM | exact hrO | exact hrD | (intro _ h _; exact hrD _ h)

/-- `xs.map((x, i) => e)`, from the value of the array. -/
theorem eval_mapIdx (sp sp' sa : Span) (par : Bool) (recv : Expr) (p q : Param) (body : Expr)
    (hr : recv.namesNumber = false) (hpq : p.name ≠ q.name) (ρ : Eval.Env N) :
    Eval.eval m fuel ρ (.call sp (.member sp' recv "map") [.arrow sa par [p, q] body]) =
      (Eval.eval m fuel ρ recv).bind fun
        | .list items => methodVal m fuel (.mapIdx q.name) ρ p.name body items
        | _ => none := by
  have hr' : ∀ s, recv ≠ .ident s "Number" := by
    intro s h; subst h; simp [Expr.namesNumber] at hr
  have hrM : ∀ s, recv ≠ .ident s "Math" := by
    intro s h; subst h; simp [Expr.namesNumber] at hr
  have hrO : ∀ s, recv ≠ .ident s "Object" := by
    intro s h; subst h; simp [Expr.namesNumber] at hr
  have hrD : ∀ s, recv ≠ .ident s "Date" := by
    intro s h; subst h; simp [Expr.namesNumber] at hr
  generalize hR : Eval.eval m fuel ρ recv = r
  rw [Eval.eval]
  · simp only [beq_iff_eq, hpq, ↓reduceIte, hR]
    cases r with
    | none => rfl
    | some v => cases v <;> simp [methodVal]
  all_goals first | exact hr' | exact hrM | exact hrO | exact hrD | (intro _ h _; exact hrD _ h) | decide

/-- The value of a `List` function with a callback in the output, from the
value of the list. -/
def outMethodVal (method : IR.ListMethod) (ρ : Eval.Env N) (name : String) (body : IR.Expr)
    (items : List (Val N)) : Option (Val N) :=
  match method with
  | .map => do return .list (← IR.Expr.evalMap fs fuel ρ name body items)
  | .filter => do return .list (← IR.Expr.evalFilter fs fuel ρ name body items)
  | .any => do return .bool (← IR.Expr.evalFind fs fuel ρ name body true items).isSome
  | .all => do return .bool (← IR.Expr.evalFind fs fuel ρ name body false items).isNone
  | .find => do return (← IR.Expr.evalFind fs fuel ρ name body true items).getD .undefined
  | .mapIdx index => do return .list (← IR.Expr.evalMapIdx fs fuel ρ name index body 0 items)
  | .findIndex => do
    return .num (JSNumber.ofSafeInt (((← IR.Expr.evalFindIdx fs fuel ρ name body 0 items).map Int.ofNat).getD (-1)))
  | .findLast => do return (← IR.Expr.evalFind fs fuel ρ name body true items.reverse).getD .undefined
  | .sortWith other => do return .list (← Eval.sortValues (IR.Expr.evalCompare fs fuel ρ name other body) items)

theorem out_listMethod {method : IR.ListMethod} {items : IR.Expr} {name : String} {t : IR.Ty}
    {body : IR.Expr} {ρ : Eval.Env N} {v : Val N}
    {info : IR.CallbackInfo IR.TyExt}
    (h : IR.Expr.eval fs fuel ρ (.listMethod method items name t body info) = some v) :
    ∃ xs, IR.Expr.eval fs fuel ρ items = some (.list xs) ∧
      outMethodVal fs fuel method ρ name body xs = some v := by
  simp only [IR.Expr.eval] at h
  cases hx : IR.Expr.eval fs fuel ρ items with
  | none => simp [hx] at h
  | some u =>
    cases u <;> simp [hx] at h
    rename_i xs
    refine ⟨xs, rfl, ?_⟩
    cases method <;> exact h

/-- The body of a callback means what the interpreter gives it, for every value
of the parameter `x`. -/
def BodySim (ρs ρo : Eval.Env N) (x : String) (body : Expr) (code : IR.Expr) : Prop :=
  ∀ w v, IR.Expr.eval fs fuel ((x, w) :: ρo) code = some v →
    Eval.eval m fuel ((x, w) :: ρs) body = some v

theorem evalMap_sim {ρs ρo : Eval.Env N} {x : String} {body : Expr} {code : IR.Expr}
    (hb : BodySim m fs fuel ρs ρo x body code) :
    ∀ xs vs, IR.Expr.evalMap fs fuel ρo x code xs = some vs → Eval.evalMap m fuel ρs x body xs = some vs
  | [], vs, h => by simp [IR.Expr.evalMap] at h; subst h; simp [Eval.evalMap]
  | w :: xs, vs, h => by
    simp only [IR.Expr.evalMap] at h
    cases hw : IR.Expr.eval fs fuel ((x, w) :: ρo) code with
    | none => simp [hw] at h
    | some u =>
      cases hr : IR.Expr.evalMap fs fuel ρo x code xs with
      | none => simp [hw, hr] at h
      | some us =>
        simp [hw, hr] at h
        subst h
        simp [Eval.evalMap, hb w u hw, evalMap_sim hb xs us hr]

theorem evalFilter_sim {ρs ρo : Eval.Env N} {x : String} {body : Expr} {code : IR.Expr}
    (hb : BodySim m fs fuel ρs ρo x body code) :
    ∀ xs vs, IR.Expr.evalFilter fs fuel ρo x code xs = some vs →
      Eval.evalFilter m fuel ρs x body xs = some vs
  | [], vs, h => by simp [IR.Expr.evalFilter] at h; subst h; simp [Eval.evalFilter]
  | w :: xs, vs, h => by
    simp only [IR.Expr.evalFilter] at h
    cases hw : IR.Expr.eval fs fuel ((x, w) :: ρo) code with
    | none => simp [hw] at h
    | some u =>
      cases u <;> simp [hw] at h
      rename_i keep
      cases hr : IR.Expr.evalFilter fs fuel ρo x code xs with
      | none => simp [hr] at h
      | some us =>
        simp [hr] at h
        subst h
        simp [Eval.evalFilter, hb w _ hw, evalFilter_sim hb xs us hr, Val.truthy]

theorem evalFind_sim {ρs ρo : Eval.Env N} {x : String} {body : Expr} {code : IR.Expr} {want : Bool}
    (hb : BodySim m fs fuel ρs ρo x body code) :
    ∀ xs r, IR.Expr.evalFind fs fuel ρo x code want xs = some r →
      Eval.evalFind m fuel ρs x body want xs = some r
  | [], r, h => by simp [IR.Expr.evalFind] at h; subst h; simp [Eval.evalFind]
  | w :: xs, r, h => by
    simp only [IR.Expr.evalFind] at h
    cases hw : IR.Expr.eval fs fuel ((x, w) :: ρo) code with
    | none => simp [hw] at h
    | some u =>
      cases u <;> simp [hw] at h
      rename_i b
      simp only [Eval.evalFind, hb w _ hw, Option.bind_eq_bind, Option.bind_some, Val.truthy]
      by_cases hbw : b = want
      · simp [hbw] at h ⊢; exact h
      · simp [hbw] at h ⊢; exact evalFind_sim hb xs r h

theorem evalFindIdx_sim {ρs ρo : Eval.Env N} {x : String} {body : Expr} {code : IR.Expr}
    (hb : BodySim m fs fuel ρs ρo x body code) :
    ∀ xs start r, IR.Expr.evalFindIdx fs fuel ρo x code start xs = some r →
      Eval.evalFindIdx m fuel ρs x body start xs = some r
  | [], _, r, h => by simp [IR.Expr.evalFindIdx] at h; subst h; simp [Eval.evalFindIdx]
  | w :: xs, start, r, h => by
    simp only [IR.Expr.evalFindIdx] at h
    cases hw : IR.Expr.eval fs fuel ((x, w) :: ρo) code with
    | none => simp [hw] at h
    | some u =>
      cases u <;> simp [hw] at h
      rename_i b
      simp only [Eval.evalFindIdx, hb w _ hw, Option.bind_eq_bind, Option.bind_some, Val.truthy]
      cases b
      · simp at h ⊢; exact evalFindIdx_sim hb xs (start + 1) r h
      · simp at h ⊢; exact h

theorem methodVal_sim {ρs ρo : Eval.Env N} {x : String} {body : Expr} {code : IR.Expr}
    (hb : BodySim m fs fuel ρs ρo x body code) (method : IR.ListMethod) (hm : ∀ i, method ≠ .mapIdx i)
    (hso : ∀ o, method ≠ .sortWith o) (xs : List (Val N)) (v : Val N)
    (h : outMethodVal fs fuel method ρo x code xs = some v) :
    methodVal m fuel method ρs x body xs = some v := by
  cases method <;> simp only [outMethodVal, methodVal] at h ⊢
  · cases hr : IR.Expr.evalMap fs fuel ρo x code xs <;> simp [hr] at h
    simp [evalMap_sim m fs fuel hb xs _ hr, h]
  · cases hr : IR.Expr.evalFilter fs fuel ρo x code xs <;> simp [hr] at h
    simp [evalFilter_sim m fs fuel hb xs _ hr, h]
  all_goals
    first
    | (cases hr : IR.Expr.evalFind fs fuel ρo x code true xs <;> simp [hr] at h
       simp [evalFind_sim m fs fuel hb xs _ hr, h])
    | (cases hr : IR.Expr.evalFind fs fuel ρo x code false xs <;> simp [hr] at h
       simp [evalFind_sim m fs fuel hb xs _ hr, h])
    | (cases hr : IR.Expr.evalFind fs fuel ρo x code true xs.reverse <;> simp [hr] at h
       simp [evalFind_sim m fs fuel hb xs.reverse _ hr, h])
    | (cases hr : IR.Expr.evalFindIdx fs fuel ρo x code 0 xs <;> simp [hr] at h
       simp [evalFindIdx_sim m fs fuel hb xs 0 _ hr, h])
    | exact absurd rfl (hm _)
    | exact absurd rfl (hso _)

omit [JSNumber N] in
theorem agree_cons {ρs ρo : Eval.Env N} (ha : Agree ρs ρo) (x : String) (w : Val N) :
    Agree ((x, w) :: ρs) ((x, w) :: ρo) := fun n => by
  simp only [List.lookup]; split
  · rfl
  · exact ha n

omit [JSNumber N] in
theorem scoped_cons {env : Translate.Env} {ρs : Eval.Env N} (hs : Scoped m env ρs) (x : String)
    (b : Binding) (t : Ty) (w : Val N) :
    Scoped m (env.add { name := x, binding := b, type := t }) ((x, w) :: ρs) :=
  ⟨fun n => by
    rw [has_add, ← hs.1 n]
    simp only [List.lookup]
    by_cases hn : n = x
    · subst hn; simp
    · have h1 : (n == x) = false := by simpa using hn
      have h2 : (x == n) = false := by simpa using Ne.symm hn
      simp [h1, h2], hs.2⟩

theorem bodySim_of {env : Translate.Env} {ρs ρo : Eval.Env N} {x : String} {b : Binding} {t : Ty}
    {body : Expr} {code : IR.Expr} (hsim : Sim (N := N) m fs fuel (env.add { name := x, binding := b, type := t }) body code)
    (ha : Agree ρs ρo) (hs : Scoped m env ρs) : BodySim m fs fuel ρs ρo x body code :=
  fun w v hv => hsim _ _ v (agree_cons ha x w) (scoped_cons m hs x b t w) hv

/-- The body of a callback of `map` that reads the index means what the
interpreter gives it, for every value of the element `x` and the index `i`. -/
def BodySimIdx (ρs ρo : Eval.Env N) (x i : String) (body : Expr) (code : IR.Expr) : Prop :=
  ∀ w k v, IR.Expr.eval fs fuel ((x, w) :: (i, .num k) :: ρo) code = some v →
    Eval.eval m fuel ((x, w) :: (i, .num k) :: ρs) body = some v

theorem bodySimIdx_of {env : Translate.Env} {ρs ρo : Eval.Env N} {x i : String} {elem : Ty}
    {body : Expr} {code : IR.Expr}
    (hsim : Sim (N := N) m fs fuel ((env.add { name := i, binding := .param, type := .number }).add
      { name := x, binding := .param, type := elem }) body code)
    (ha : Agree ρs ρo) (hs : Scoped m env ρs) : BodySimIdx m fs fuel ρs ρo x i body code := by
  intro w k v hv
  exact hsim _ _ v (agree_cons (agree_cons ha i _) x w)
    (scoped_cons m (scoped_cons m hs i .param .number _) x .param elem w) hv

theorem evalMapIdx_sim {ρs ρo : Eval.Env N} {x i : String} {body : Expr} {code : IR.Expr}
    (hb : BodySimIdx m fs fuel ρs ρo x i body code) :
    ∀ xs start vs, IR.Expr.evalMapIdx fs fuel ρo x i code start xs = some vs →
      Eval.evalMapIdx m fuel ρs x i body start xs = some vs
  | [], _, vs, h => by simp [IR.Expr.evalMapIdx] at h; subst h; simp [Eval.evalMapIdx]
  | w :: xs, start, vs, h => by
    simp only [IR.Expr.evalMapIdx] at h
    cases hw : IR.Expr.eval fs fuel ((x, w) :: (i, .num (JSNumber.ofSafeInt start)) :: ρo) code with
    | none => simp [hw] at h
    | some u =>
      cases hr : IR.Expr.evalMapIdx fs fuel ρo x i code (start + 1) xs with
      | none => simp [hw, hr] at h
      | some us =>
        simp [hw, hr] at h
        subst h
        simp [Eval.evalMapIdx, hb w _ u hw, evalMapIdx_sim hb xs (start + 1) us hr]

omit [JSNumber N] in
theorem indexedCallbackOf_some {method : IR.ListMethod} {args : List Expr} {p q : Param} {body : Expr}
    (h : indexedCallbackOf method args = some (p, q, body)) :
    method = .map ∧ ∃ sa par, args = [.arrow sa par [p, q] body] := by
  unfold indexedCallbackOf at h
  split at h
  · cases h; exact ⟨rfl, _, _, rfl⟩
  · cases h

omit [JSNumber N] in
theorem listMethod?_ne_mapIdx {name : String} {method : IR.ListMethod} (h : listMethod? name = some method)
    (i : String) : method ≠ .mapIdx i := by
  unfold listMethod? at h
  intro hm; subst hm
  repeat' split at h
  all_goals simp at h

omit [JSNumber N] in
theorem listMethod?_ne_sortWith {name : String} {method : IR.ListMethod} (h : listMethod? name = some method)
    (o : String) : method ≠ .sortWith o := by
  unfold listMethod? at h
  intro hm; subst hm
  repeat' split at h
  all_goals simp at h

omit [JSNumber N] in
theorem listMethod?_map {name : String} (h : listMethod? name = some .map) : name = "map" := by
  unfold listMethod? at h
  repeat' split at h
  all_goals first | (simp at h; done) | simp_all

omit [JSNumber N] in
theorem callbackOf_some {args : List Expr} {p : Param} {body : Expr}
    (h : callbackOf args = some (p, body)) : ∃ sa par, args = [.arrow sa par [p] body] := by
  unfold callbackOf at h
  split at h
  · cases h; exact ⟨_, _, rfl⟩
  · cases h

theorem translateArrayMethod_sound {F : Nat}
    (ihE : ∀ env exp e ctx c ctx', translateExpr F env exp e ctx = .ok c ctx' →
      Sim (N := N) m fs fuel env e c.code)
    {env : Translate.Env} {exp : Option Ty} {s : Span} {recv : Expr} {method : IR.ListMethod}
    {args : List Expr} {ctx ctx' : Ctx} {c : Code}
    (h : translateArrayMethod (F + 1) env exp s recv method args ctx = .ok c ctx')
    {sp : Span} {name : String} (hname : listMethod? name = some method) :
    Sim (N := N) m fs fuel env (.call s (.member sp recv name) args) c.code := by
  cases hidx : indexedCallbackOf method args with
  | some t =>
    obtain ⟨p, q, body⟩ := t
    obtain ⟨rfl, sa, par, rfl⟩ := indexedCallbackOf_some hidx
    have hn : name = "map" := listMethod?_map hname
    subst hn
    simp only [translateArrayMethod, hidx, ite_state] at h
    split at h
    · simp at h
    rename_i hr
    simp only [pure_bind, bind_ok, orReject_ok] at h
    obtain ⟨xs, s₂, hxs, elem, s₃, ⟨helem, rfl⟩, -, s₄, -, -, s₅, -, withIndex, s₆, hd1, inner, s₇, hd2,
      b, s₈, hb, type, s₉, -, h⟩ := h
    simp only [pure_ok] at h
    obtain ⟨rfl, -⟩ := h
    obtain ⟨-, rfl, -⟩ := declare_ok hd1
    obtain ⟨hpn, rfl, -⟩ := declare_ok hd2
    have hpq : p.name ≠ q.name := by
      intro he; rw [has_add] at hpn; simp [he] at hpn
    intro ρs ρo v ha hs hv
    obtain ⟨items, hitems, hval⟩ := out_listMethod fs fuel hv
    rw [eval_value] at hitems
    have hrecv := ihE _ _ _ _ _ _ hxs ρs ρo _ ha hs hitems
    have hbody : Sim (N := N) m fs fuel _ body b.value := fun ρs ρo w ha hs hw =>
      ihE _ _ _ _ _ _ hb ρs ρo w ha hs (by rwa [eval_value] at hw)
    rw [eval_mapIdx m fuel _ _ _ _ _ _ _ _ (by simpa using hr) hpq, hrecv]
    simp only [outMethodVal] at hval
    simp only [Option.bind_some, methodVal]
    cases hr2 : IR.Expr.evalMapIdx fs fuel ρo p.name q.name b.value 0 items <;> simp [hr2] at hval
    simp [evalMapIdx_sim m fs fuel (bodySimIdx_of m fs fuel hbody ha hs) items 0 _ hr2, hval]
  | none =>
    simp only [translateArrayMethod, hidx, pure_bind, bind_ok, orReject_ok] at h
    obtain ⟨⟨p, body⟩, s₁, ⟨hcb, rfl⟩, h⟩ := h
    obtain ⟨sa, par, rfl⟩ := callbackOf_some hcb
    simp only [ite_state] at h
    split at h
    · simp at h
    rename_i hr
    simp only [bind_ok, orReject_ok] at h
    obtain ⟨xs, s₂, hxs, elem, s₃, ⟨helem, rfl⟩, -, s₄, -, inner, s₅, hdecl, b, s₆, hb, type, s₇, -, h⟩ := h
    simp only [pure_ok] at h
    obtain ⟨rfl, -⟩ := h
    obtain ⟨-, rfl, -⟩ := declare_ok hdecl
    intro ρs ρo v ha hs hv
    obtain ⟨items, hitems, hval⟩ := out_listMethod fs fuel hv
    rw [eval_value] at hitems
    have hrecv := ihE _ _ _ _ _ _ hxs ρs ρo _ ha hs hitems
    have hbody : Sim (N := N) m fs fuel _ body b.value := fun ρs ρo w ha hs hw =>
      ihE _ _ _ _ _ _ hb ρs ρo w ha hs (by rwa [eval_value] at hw)
    rw [eval_arrayMethod m fuel _ _ _ _ _ _ _ _ _ hname (by simpa using hr), hrecv]
    exact methodVal_sim m fs fuel (bodySim_of m fs fuel hbody ha hs) method (listMethod?_ne_mapIdx hname)
      (listMethod?_ne_sortWith hname)
      items v hval

/-! ### `reduce` -/

/-- The body of the callback of `reduce` means what the interpreter gives it,
for every value so far `a` and every element `x`. -/
def BodySim2 (ρs ρo : Eval.Env N) (a x : String) (body : Expr) (code : IR.Expr) : Prop :=
  ∀ u w v, IR.Expr.eval fs fuel ((x, w) :: (a, u) :: ρo) code = some v →
    Eval.eval m fuel ((x, w) :: (a, u) :: ρs) body = some v

theorem bodySim2_of {env : Translate.Env} {ρs ρo : Eval.Env N} {a x : String} {ta tx : Ty}
    {body : Expr} {code : IR.Expr}
    (hsim : Sim (N := N) m fs fuel ((env.add { name := a, binding := .param, type := ta }).add
      { name := x, binding := .param, type := tx }) body code)
    (ha : Agree ρs ρo) (hs : Scoped m env ρs) : BodySim2 m fs fuel ρs ρo a x body code := by
  intro u w v hv
  exact hsim _ _ v (agree_cons (agree_cons ha a _) x w)
    (scoped_cons m (scoped_cons m hs a .param ta _) x .param tx w) hv

theorem evalReduce_sim {ρs ρo : Eval.Env N} {a x : String} {body : Expr} {code : IR.Expr}
    (hb : BodySim2 m fs fuel ρs ρo a x body code) :
    ∀ xs u r, IR.Expr.evalReduce fs fuel ρo a x code u xs = some r →
      Eval.evalReduce m fuel ρs a x body u xs = some r
  | [], u, r, h => by simp [IR.Expr.evalReduce] at h; subst h; simp [Eval.evalReduce]
  | w :: xs, u, r, h => by
    simp only [IR.Expr.evalReduce] at h
    cases hw : IR.Expr.eval fs fuel ((x, w) :: (a, u) :: ρo) code with
    | none => simp [hw] at h
    | some u' =>
      simp only [hw, Option.bind_eq_bind, Option.bind_some] at h
      simp only [Eval.evalReduce, hb u w u' hw, Option.bind_eq_bind, Option.bind_some]
      exact evalReduce_sim hb xs u' r h

omit [JSNumber N] in
theorem reducerOf_some {args : List Expr} {a p : Param} {body init : Expr}
    (h : reducerOf args = some (a, p, body, init)) : ∃ sa par, args = [.arrow sa par [a, p] body, init] := by
  unfold reducerOf at h
  split at h
  · cases h; exact ⟨_, _, rfl⟩
  · cases h

/-- `xs.reduce((a, x) => e, init)`: the interpreter evaluates the array, then
the initial value, then the callback on each element. -/
theorem eval_reduce (sp sp' sa : Span) (par : Bool) (recv : Expr) (a p : Param) (body init : Expr)
    (hap : a.name ≠ p.name) (hr : recv.namesNumber = false) (ρ : Eval.Env N) :
    Eval.eval m fuel ρ (.call sp (.member sp' recv "reduce") [.arrow sa par [a, p] body, init]) =
      (Eval.eval m fuel ρ recv).bind fun
        | .list items => (Eval.eval m fuel ρ init).bind fun v =>
            Eval.evalReduce m fuel ρ a.name p.name body v items
        | _ => none := by
  have hrM : ∀ s, recv ≠ .ident s "Math" := by
    intro s h; subst h; simp [Expr.namesNumber] at hr
  have hrO : ∀ s, recv ≠ .ident s "Object" := by
    intro s h; subst h; simp [Expr.namesNumber] at hr
  have hrD : ∀ s, recv ≠ .ident s "Date" := by
    intro s h; subst h; simp [Expr.namesNumber] at hr
  rw [Eval.eval]
  · simp only [beq_iff_eq, hap, if_false]
    generalize Eval.eval m fuel ρ recv = r
    cases r with
    | none => rfl
    | some w => cases w <;> simp [Option.bind_eq_bind]
  · exact hrM

theorem translateReduce_sound {F : Nat}
    (ihE : ∀ env exp e ctx c ctx', translateExpr F env exp e ctx = .ok c ctx' →
      Sim (N := N) m fs fuel env e c.code)
    {env : Translate.Env} {exp : Option Ty} {s : Span} {recv : Expr} {args : List Expr}
    {ctx ctx' : Ctx} {c : Code}
    (h : translateReduce (F + 1) env exp s recv args ctx = .ok c ctx') {sp : Span} :
    Sim (N := N) m fs fuel env (.call s (.member sp recv "reduce") args) c.code := by
  simp only [translateReduce, bind_ok, orReject_ok] at h
  obtain ⟨⟨a, p, body, init⟩, s₁, ⟨hcb, rfl⟩, h⟩ := h
  obtain ⟨sa, par, rfl⟩ := reducerOf_some hcb
  simp only [ite_state] at h
  split at h
  · simp only [bind_ok, reject_ne_ok, false_and, exists_false] at h
  rename_i hnn
  simp only [pure_bind, bind_ok, orReject_ok] at h
  obtain ⟨xs, s₂, hxs, elem, s₃, ⟨-, rfl⟩, i, s₄, hi, h⟩ := h
  simp only [ite_state] at h
  split at h
  · simp only [bind_ok, reject_ne_ok, false_and, exists_false] at h
  simp only [bind_ok] at h
  obtain ⟨-, s₅, -, -, s₆, -, withAcc, s₇, hdA, inner, s₈, hdP, b, s₉, hb, h⟩ := h
  simp only [ite_state] at h
  split at h
  · simp only [pure_ok] at h
    obtain ⟨rfl, -⟩ := h
    obtain ⟨-, rfl, -⟩ := declare_ok hdA
    obtain ⟨hnp, rfl, -⟩ := declare_ok hdP
    -- The two parameters have different names, as the spec needs.
    have hap : a.name ≠ p.name := by
      intro he; rw [has_add] at hnp; simp [he] at hnp
    intro ρs ρo v ha hs hv
    simp only [IR.Expr.eval] at hv
    cases hx : IR.Expr.eval fs fuel ρo xs.value with
    | none => simp [hx] at hv
    | some w =>
      cases w with
      | list items =>
        cases hinit : IR.Expr.eval fs fuel ρo i.value with
        | none => simp [hx, hinit] at hv
        | some u =>
          simp only [hx, hinit, Option.bind_eq_bind, Option.bind_some] at hv
          rw [eval_value] at hx hinit
          have hrecv := ihE _ _ _ _ _ _ hxs ρs ρo _ ha hs hx
          have hini := ihE _ _ _ _ _ _ hi ρs ρo _ ha hs hinit
          have hbody : Sim (N := N) m fs fuel _ body b.value := fun ρs ρo w ha hs hw =>
            ihE _ _ _ _ _ _ hb ρs ρo w ha hs (by rwa [eval_value] at hw)
          rw [eval_reduce m fuel _ _ _ _ _ _ _ _ _ hap (by simpa using hnn), hrecv]
          simp only [Option.bind_some, hini]
          exact evalReduce_sim m fs fuel (bodySim2_of m fs fuel hbody ha hs) items u v hv
      | _ => simp [hx] at hv
  · simp only [bind_ok, reject_ne_ok, false_and, exists_false] at h


/-! ### Sorting -/

/-- The comparator of the output gives a sign only where the interpreter's
gives the same one, for every pair of elements. -/
theorem evalCompare_sim {ρs ρo : Eval.Env N} {a x : String} {body : Expr} {code : IR.Expr}
    (hb : BodySim2 m fs fuel ρs ρo a x body code) (w u : Val N) (o : Ordering)
    (h : IR.Expr.evalCompare fs fuel ρo x a code w u = some o) :
    Eval.evalCompare m fuel ρs x a body w u = some o := by
  -- The comparator's own branch, for any two values.
  have last : ∀ w u : Val N,
      (do let .num v ← IR.Expr.eval fs fuel ((x, w) :: (a, u) :: ρo) code | none
          JSNumber.compareSign v) = some o →
      (do let .num v ← Eval.eval m fuel ((x, w) :: (a, u) :: ρs) body | none
          JSNumber.compareSign v) = some o := by
    intro w u h
    cases hv : IR.Expr.eval fs fuel ((x, w) :: (a, u) :: ρo) code with
    | none => rw [hv] at h; cases h
    | some v => rw [hv] at h; rw [hb u w v hv]; exact h
  unfold IR.Expr.evalCompare at h
  unfold Eval.evalCompare
  cases w <;> cases u <;> simp only at h ⊢ <;> first | exact h | exact last _ _ h

omit [JSNumber N] in
/-- `List.all` reads its test only on the elements. -/
theorem all_congr_mem {α : Type} {l : List α} {p q : α → Bool} (h : ∀ a ∈ l, p a = q a) :
    l.all p = l.all q := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.all_cons, h x List.mem_cons_self, ih (fun a ha => h a (List.mem_cons_of_mem _ ha))]

omit [JSNumber N] in
/-- `consistentOn` reads the comparator only on the elements. -/
theorem consistentOn_congr {α : Type} {c₁ c₂ : α → α → Option Ordering} {items : List α}
    (h : ∀ x ∈ items, ∀ y ∈ items, c₁ x y = c₂ x y) : Eval.consistentOn c₁ items = Eval.consistentOn c₂ items := by
  unfold Eval.consistentOn
  refine all_congr_mem fun a ha => all_congr_mem fun b hb => ?_
  have hin : (items.all fun c => !(c₁ a b != some .gt && c₁ b c != some .gt) || c₁ a c != some .gt) =
      (items.all fun c => !(c₂ a b != some .gt && c₂ b c != some .gt) || c₂ a c != some .gt) :=
    all_congr_mem fun c hc => by rw [h a ha b hb, h b hb c hc, h a ha c hc]
  rw [hin, h a ha b hb, h b hb a ha]

omit [JSNumber N] in
/-- A sort gives a value only where the interpreter's sort gives the same
one, when each sign of the first comparator on the elements is a sign of the
second. -/
theorem sortValues_sim {α : Type} {c₁ c₂ : α → α → Option Ordering} {items ys : List α}
    (hc : ∀ x ∈ items, ∀ y ∈ items, ∀ o, c₁ x y = some o → c₂ x y = some o)
    (h : Eval.sortValues c₁ items = some ys) : Eval.sortValues c₂ items = some ys := by
  unfold Eval.sortValues at h ⊢
  split at h
  · rename_i hcons
    cases h
    -- A consistent comparator gives a sign for every pair, so the two agree
    -- on the elements.
    have hsome : ∀ x ∈ items, ∀ y ∈ items, (c₁ x y).isSome = true := by
      intro x hx y hy
      unfold Eval.consistentOn at hcons
      rw [List.all_eq_true] at hcons
      have := hcons x hx
      rw [List.all_eq_true] at this
      have := this y hy
      simp only [Bool.and_eq_true] at this
      exact this.1.1
    have heq : ∀ x ∈ items, ∀ y ∈ items, c₁ x y = c₂ x y := by
      intro x hx y hy
      have hs := hsome x hx y hy
      cases h1 : c₁ x y with
      | none => rw [h1] at hs; cases hs
      | some o => exact (hc x hx y hy o h1).symm
    rw [← consistentOn_congr heq, if_pos hcons]
    have hm := List.map_mergeSort (f := id) (l := items) (r := fun a b => c₁ a b != some .gt)
      (s := fun a b => c₂ a b != some .gt) (fun a ha b hb => by
        show (c₁ a b != some .gt) = (c₂ a b != some .gt)
        rw [heq a ha b hb])
    simp only [List.map_id] at hm
    rw [hm]
  · cases h

/-- `xs.toSorted((a, b) => e)` and `[...xs].sort((a, b) => e)`, from the value of
the array. -/
theorem eval_sort (sp sp' sa : Span) (par : Bool) (recv : Expr) (method : String) (p q : Param)
    (body : Expr) (hm : method = "toSorted" ∨ (method = "sort" ∧ recv.isArrayLiteral = true))
    (hr : recv.namesNumber = false) (hpq : p.name ≠ q.name) (ρ : Eval.Env N) :
    Eval.eval m fuel ρ (.call sp (.member sp' recv method) [.arrow sa par [p, q] body]) =
      (Eval.eval m fuel ρ recv).bind fun
        | .list items => methodVal m fuel (.sortWith q.name) ρ p.name body items
        | _ => none := by
  have hr' : ∀ s, recv ≠ .ident s "Number" := by
    intro s h; subst h; simp [Expr.namesNumber] at hr
  have hrM : ∀ s, recv ≠ .ident s "Math" := by
    intro s h; subst h; simp [Expr.namesNumber] at hr
  have hrD : ∀ s, recv ≠ .ident s "Date" := by
    intro s h; subst h; simp [Expr.namesNumber] at hr
  rcases hm with rfl | ⟨rfl, hlit⟩
  all_goals
    generalize hR : Eval.eval m fuel ρ recv = r
    rw [Eval.eval]
    · simp only [beq_iff_eq, hpq, ↓reduceIte, hR]
      cases r with
      | none => simp
      | some v => cases v <;> simp_all [methodVal]
    all_goals first | exact hr' | exact hrM | (intro _ h _; exact hrD _ h) | decide

omit [JSNumber N] in
theorem sortOf_some {callee recv : Expr} {method : String} (h : sortOf callee = some (recv, method)) :
    ∃ sp, callee = .member sp recv method ∧ (method = "toSorted" ∨ method = "sort") := by
  unfold sortOf at h
  split at h <;> simp at h
  all_goals obtain ⟨rfl, rfl⟩ := h
  all_goals exact ⟨_, rfl, by simp⟩

theorem translateSort_sound {F : Nat}
    (ihE : ∀ env exp e ctx c ctx', translateExpr F env exp e ctx = .ok c ctx' →
      Sim (N := N) m fs fuel env e c.code)
    {env : Translate.Env} {s : Span} {recv : Expr} {method : String} {args : List Expr}
    {ctx ctx' : Ctx} {c : Code}
    (h : translateSort (F + 1) env s recv method args ctx = .ok c ctx')
    (hmethod : method = "toSorted" ∨ method = "sort") {sp : Span} :
    Sim (N := N) m fs fuel env (.call s (.member sp recv method) args) c.code := by
  simp only [translateSort] at h
  split at h
  rotate_left
  · simp at h
  rename_i sa par p q body
  simp only [ite_state] at h
  split at h
  · simp at h
  rename_i hsortlit
  simp only [pure_bind, bind_ok, requireFeature_ok, ite_state] at h
  obtain ⟨-, s₁, -, h⟩ := h
  split at h
  · simp only [bind_ok, reject_ne_ok, false_and, exists_false] at h
  rename_i hr
  simp only [bind_ok, orReject_ok, ite_state] at h
  obtain ⟨xs, s₂, hxs, elem, s₃, ⟨-, rfl⟩, h⟩ := h
  split at h
  · simp only [bind_ok, reject_ne_ok, false_and, exists_false] at h
  simp only [bind_ok] at h
  obtain ⟨-, s₄, -, -, s₅, -, withQ, s₆, hdQ, inner, s₇, hdP, b, s₈, hb, h⟩ := h
  simp only [ite_state] at h
  split at h
  rotate_left
  · simp only [bind_ok, reject_ne_ok, false_and, exists_false] at h
  simp only [bind_ok, orReject_ok, pure_ok] at h
  obtain ⟨-, s₉, -, -, s₁₀, -, rfl, -⟩ := h
  obtain ⟨-, rfl, -⟩ := declare_ok hdQ
  obtain ⟨hnp, rfl, -⟩ := declare_ok hdP
  have hpq : p.name ≠ q.name := by
    intro he; rw [has_add] at hnp; simp [he] at hnp
  have hm : method = "toSorted" ∨ (method = "sort" ∧ recv.isArrayLiteral = true) := by
    rcases hmethod with rfl | rfl
    · exact Or.inl rfl
    · refine Or.inr ⟨rfl, ?_⟩
      simpa using hsortlit
  intro ρs ρo v ha hs hv
  obtain ⟨items, hitems, hval⟩ := out_listMethod fs fuel hv
  rw [eval_value] at hitems
  have hrecv := ihE _ _ _ _ _ _ hxs ρs ρo _ ha hs hitems
  have hbody : Sim (N := N) m fs fuel _ body b.value := fun ρs ρo w ha hs hw =>
    ihE _ _ _ _ _ _ hb ρs ρo w ha hs (by rwa [eval_value] at hw)
  have hb2 := bodySim2_of m fs fuel hbody ha hs
  rw [eval_sort m fuel _ _ _ _ _ _ _ _ _ hm (by simpa using hr) hpq, hrecv]
  simp only [outMethodVal] at hval
  simp only [Option.bind_some, methodVal]
  cases hys : Eval.sortValues (IR.Expr.evalCompare fs fuel ρo p.name q.name b.value) items with
  | none => rw [hys] at hval; cases hval
  | some ys =>
    rw [hys] at hval
    rw [sortValues_sim (fun x _ y _ o hxy => evalCompare_sim m fs fuel hb2 x y o hxy) hys]
    exact hval

/-! ### Arrays: length and indexes -/

omit [JSNumber N] in
theorem indexLiteral_ok {sp : Span} {text : String} {xs c : Code} {elem : Ty} {ctx ctx' : Ctx}
    (h : indexLiteral sp text xs elem ctx = .ok c ctx') :
    ∃ k, Eval.numberLiteral text = some k ∧ 0 ≤ k ∧
      c.code = .ascribe (.ext (.indexLit k.toNat) [xs.value]) (Ty.optional elem).lean := by
  simp only [indexLiteral, bind_ok, orReject_ok, ite_state] at h
  obtain ⟨k, s₁, ⟨hk, rfl⟩, h⟩ := h
  split at h
  · rename_i hpos
    simp only [pure_bind, pure_ok] at h
    exact ⟨k, hk, by simpa using hpos, by rw [← h.1]⟩
  · simp at h

omit [JSNumber N] in
theorem indexNumber_ok {sp : Span} {xs i c : Code} {elem : Ty} {ctx ctx' : Ctx}
    (h : indexNumber sp xs i elem ctx = .ok c ctx') :
    c.code = .ext .indexNumber [xs.value, i.value] := by
  simp only [indexNumber, ite_state] at h
  split at h
  · simp only [pure_bind, pure_ok] at h; rw [← h.1]
  · simp at h

/-- `xs[i]` on an array: a number literal is the integer it names, and any
other number is its integer when it is a safe integer. -/
theorem eval_index_list {ρ : Eval.Env N} {sp : Span} {obj key : Expr} {items : List (Val N)}
    (h : Eval.eval m fuel ρ obj = some (.list items)) :
    Eval.eval m fuel ρ (.index sp obj key) =
      match Eval.numberText? key with
      | some text => (Eval.numberLiteral text).map fun k => Eval.elementAt items (some k)
      | none => (Eval.eval m fuel ρ key).bind fun
        | .num n => some (Eval.elementAt items (JSNumber.toSafeInt n))
        | _ => none := by
  simp only [Eval.eval, h, Option.bind_eq_bind, Option.bind_some]
  cases hk : Eval.numberText? key with
  | some text =>
    simp only
    generalize Eval.numberLiteral text = o
    cases o <;> rfl
  | none =>
    simp only
    cases Eval.eval m fuel ρ key with
    | none => simp
    | some w => cases w <;> simp

/-- `xs.length` on an array. -/
theorem eval_length {ρ : Eval.Env N} {sp : Span} {obj : Expr} {items : List (Val N)}
    (hsp : obj.optSpine = false) (h : Eval.eval m fuel ρ obj = some (.list items)) :
    Eval.eval m fuel ρ (.member sp obj "length") = some (.num (JSNumber.ofSafeInt items.length)) := by
  simp [Eval.eval, hsp, h]

theorem length_sound {env : Translate.Env} {sp : Span} {obj : Expr} {o : IR.Expr}
    (hsp : obj.optSpine = false) (hobj : Sim (N := N) m fs fuel env obj o) :
    Sim (N := N) m fs fuel env (.member sp obj "length") (.ext .length [o]) := by
  intro ρs ρo v ha hs hv
  simp only [IR.Expr.eval, IR.Expr.evalList] at hv
  cases hx : IR.Expr.eval fs fuel ρo o with
  | none => simp [hx] at hv
  | some w =>
    simp only [hx, Option.bind_eq_bind, Option.bind_some, pure_bind] at hv
    cases w
    case list items =>
      simp only [IR.ExprExt.apply, Option.some.injEq] at hv
      rw [eval_length m fuel hsp (hobj ρs ρo _ ha hs hx), hv]
    all_goals simp [IR.ExprExt.apply] at hv

theorem translateArrayIndex_sound {F : Nat}
    (ihE : ∀ env exp e ctx c ctx', translateExpr F env exp e ctx = .ok c ctx' →
      Sim (N := N) m fs fuel env e c.code)
    {env : Translate.Env} {s : Span} {o : Code} {elem : Ty} {key : Expr} {ctx ctx' : Ctx} {c : Code}
    (h : translateArrayIndex (F + 1) env s o elem key ctx = .ok c ctx')
    {sp : Span} {obj : Expr} (hobj : Sim (N := N) m fs fuel env obj o.value) :
    Sim (N := N) m fs fuel env (.index sp obj key) c.code := by
  simp only [translateArrayIndex, ite_state] at h
  split at h
  · simp at h
  simp only [pure_bind] at h
  split at h
  · -- A number literal, which is the integer it names.
    rename_i sp' text
    obtain ⟨k, hk, hpos, hc⟩ := indexLiteral_ok h
    intro ρs ρo v ha hs hv
    rw [hc] at hv
    simp only [IR.Expr.eval, IR.Expr.evalList] at hv
    cases hx : IR.Expr.eval fs fuel ρo o.value with
    | none => simp [hx] at hv
    | some w =>
      cases w
      case list items =>
        simp only [hx, Option.bind_eq_bind, Option.bind_some, pure_bind, IR.ExprExt.apply,
          Option.some.injEq, Int.toNat_of_nonneg hpos] at hv
        rw [eval_index_list m fuel (hobj ρs ρo _ ha hs hx)]
        simp [Eval.numberText?, hk, hv]
      all_goals simp [hx, IR.ExprExt.apply] at hv
  · -- Any other number: its integer, when it is a safe integer.
    rename_i hnot
    simp only [bind_ok] at h
    obtain ⟨i, s₂, hi, h⟩ := h
    have hc := indexNumber_ok h
    have hnt : Eval.numberText? key = none := by
      cases key <;> simp [Eval.numberText?] at hnot ⊢
    intro ρs ρo v ha hs hv
    rw [hc] at hv
    simp only [IR.Expr.eval, IR.Expr.evalList, eval_value] at hv
    cases hx : IR.Expr.eval fs fuel ρo o.code with
    | none => simp [hx] at hv
    | some w =>
      cases hkey : IR.Expr.eval fs fuel ρo i.code with
      | none => simp [hx, hkey] at hv
      | some kv =>
        simp only [hx, hkey, Option.bind_eq_bind, Option.bind_some, pure_bind] at hv
        cases w
        case list items =>
          cases kv
          case num n =>
            simp only [IR.ExprExt.apply, Option.some.injEq] at hv
            rw [eval_index_list m fuel (hobj ρs ρo _ ha hs (by rw [eval_value]; exact hx)), hnt,
              ihE _ _ _ _ _ _ hi ρs ρo _ ha hs hkey]
            simp [hv]
          all_goals simp [IR.ExprExt.apply] at hv
        all_goals simp [IR.ExprExt.apply] at hv

/-! ### Array methods without a callback -/

/-- A method of an array that takes no callback: the interpreter evaluates the
array, then the arguments, and `arrayMethod` gives the value. -/
theorem eval_arrayCall (sp sp' : Span) (recv : Expr) (method : String) (args : List Expr)
    (hr : recv.namesNumber = false) (harg : args.any (·.isArrow) = false) (hat : method ≠ "at")
    (hsl : method ≠ "slice") (ρ : Eval.Env N) {items : List (Val N)} (hrecv : Eval.eval m fuel ρ recv = some (.list items)) :
    Eval.eval m fuel ρ (.call sp (.member sp' recv method) args) =
      (Eval.evalList m fuel ρ args).bind (Eval.arrayMethod method items) := by
  have hr' : ∀ s, recv ≠ .ident s "Number" := by
    intro s h; subst h; simp [Expr.namesNumber] at hr
  have hrM : ∀ s, recv ≠ .ident s "Math" := by
    intro s h; subst h; simp [Expr.namesNumber] at hr
  have hrO : ∀ s, recv ≠ .ident s "Object" := by
    intro s h; subst h; simp [Expr.namesNumber] at hr
  have hrD : ∀ s, recv ≠ .ident s "Date" := by
    intro s h; subst h; simp [Expr.namesNumber] at hr
  -- One argument goes to the rule of `get` and `has`, which passes an array
  -- on to `arrayMethod`; any other number to the rule of #94.
  rcases args with _ | ⟨a, _ | ⟨b, rest⟩⟩
  all_goals rw [Eval.eval]
  all_goals first
    | (rw [hrecv]
       first
         | rfl
         | (cases ha : Eval.eval m fuel ρ a <;> simp [Eval.evalList, ha]))
    | exact hr'
    | exact hrM
    | exact hrO
    | exact hrD
    | (intro _ h _; exact hrD _ h)
    | (intros; contradiction)
    | (intros; subst_vars; exact absurd rfl (hr' _))
    | (intros; subst_vars; exact absurd rfl (hrM _))
    | (intros; subst_vars; exact absurd rfl (hrO _))
    | (intros; subst_vars; exact absurd rfl (hrD _))
    | (clear hrecv; intros; simp_all [Expr.isArrow]; done)
    | (intros; subst_vars; exact absurd rfl hat)
    | (intros; subst_vars; exact absurd rfl hsl)

omit [JSNumber N] in
/-- The integers of the arguments of `slice`, when each is a literal. -/
theorem sliceArgs_eq {args : List Expr} {bounds : List Int} {start : Int} {stop : Option Int}
    (hk : args.mapM Eval.intLiteral? = some bounds) (hb : sliceBounds bounds = some (start, stop)) :
    (args = [] ∧ start = 0 ∧ stop = none) ∨
      (∃ a, args = [a] ∧ Eval.intLiteral? a = some start ∧ stop = none) ∨
      (∃ a b e, args = [a, b] ∧ Eval.intLiteral? a = some start ∧ Eval.intLiteral? b = some e ∧
        stop = some e) := by
  rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · simp at hk; subst hk; simp [sliceBounds] at hb; exact Or.inl ⟨rfl, hb.1.symm, hb.2.symm⟩
  · cases ha : Eval.intLiteral? a <;> simp [ha] at hk
    subst hk; simp [sliceBounds] at hb
    exact Or.inr (Or.inl ⟨a, rfl, by rw [ha, hb.1], hb.2.symm⟩)
  · cases ha : Eval.intLiteral? a <;> cases hb' : Eval.intLiteral? b <;> simp [ha, hb'] at hk
    subst hk; simp [sliceBounds] at hb
    exact Or.inr (Or.inr ⟨a, b, _, rfl, by rw [ha, hb.1], hb', hb.2.symm⟩)
  · cases ha : Eval.intLiteral? a <;> cases hb' : Eval.intLiteral? b <;>
      cases hc : Eval.intLiteral? c <;> simp [ha, hb', hc] at hk
    cases hr : rest.mapM Eval.intLiteral? <;> simp [hr] at hk
    subst hk; simp [sliceBounds] at hb

/-- A literal argument is the integer it names. -/
theorem evalInt_lit {ρ : Eval.Env N} {e : Expr} {k : Int} (h : Eval.intLiteral? e = some k) :
    Eval.evalInt m fuel ρ e = some k := by
  unfold Eval.evalInt; simp [h]

/-- `xs.slice(start, end)` with integer literals: the interpreter evaluates
the array, and `sliceList` gives the elements. -/
theorem eval_slice (sp sp' : Span) (recv : Expr) (args : List Expr) {bounds : List Int} {start : Int}
    {stop : Option Int} (hk : args.mapM Eval.intLiteral? = some bounds)
    (hb : sliceBounds bounds = some (start, stop)) (hr : recv.namesNumber = false) (ρ : Eval.Env N) :
    Eval.eval m fuel ρ (.call sp (.member sp' recv "slice") args) =
      (Eval.eval m fuel ρ recv).bind fun
        | .list items => some (.list (Eval.sliceList items start stop))
        | _ => none := by
  have hcases := sliceArgs_eq hk hb
  rw [Eval.eval]
  · generalize Eval.eval m fuel ρ recv = r
    cases r with
    | none => rfl
    | some w =>
      cases w <;> simp only [Option.bind_eq_bind, Option.bind_some]
      case list items =>
        rcases hcases with ⟨rfl, rfl, rfl⟩ | ⟨a, rfl, ha, rfl⟩ | ⟨a, b, e, rfl, ha, hb', rfl⟩
        · rfl
        · simp [evalInt_lit m fuel ha]
        · simp [evalInt_lit m fuel ha, evalInt_lit m fuel hb']
  all_goals intros; simp_all [Expr.namesNumber]
  all_goals rcases hcases with ⟨h, -⟩ | ⟨a, h, ha, -⟩ | ⟨a, b, e, h, ha, -⟩ <;> simp_all [Eval.intLiteral?]


/-- `xs.at(k)` with an integer literal: the interpreter evaluates the array,
and `atVal` gives the element. -/
theorem eval_at (sp sp' : Span) (recv arg : Expr) (k : Int) (hk : Eval.intLiteral? arg = some k)
    (hr : recv.namesNumber = false) (ρ : Eval.Env N) :
    Eval.eval m fuel ρ (.call sp (.member sp' recv "at") [arg]) =
      (Eval.eval m fuel ρ recv).bind fun
        | .list items => some (Eval.atVal items k)
        | _ => none := by
  rw [Eval.eval]
  all_goals first
    | (generalize Eval.eval m fuel ρ recv = r
       cases r with
       | none => rfl
       | some w => cases w <;> simp [Option.bind_eq_bind, hk])
    | (intros; simp_all [Expr.namesNumber, Eval.intLiteral?])

omit [JSNumber N] in
/-- `includes` becomes one of its two operations. -/
theorem includesOp_some {elem : Ty} {op : IR.ExprExt} (h : includesOp? elem = some op) :
    op = .includes ∨ op = .includesNumber := by
  unfold includesOp? at h
  split at h
  · cases h; exact Or.inr rfl
  · split at h
    · cases h; exact Or.inl rfl
    · cases h

/-- The code of `arrayCall` evaluates the array and the arguments, and its
value is the one that `arrayMethod` gives them. -/
theorem arrayCall_sound {s : Span} {method : String} {elem : Ty} {xs : Code} {args : List Code}
    {ctx ctx' : Ctx} {c : Code} (h : arrayCall s method elem xs args ctx = .ok c ctx')
    {ρ : Eval.Env N} {v : Val N} (hv : IR.Expr.eval fs fuel ρ c.code = some v) :
    ∃ items vs, IR.Expr.eval fs fuel ρ xs.value = some (.list items) ∧
      IR.Expr.evalList fs fuel ρ (args.map Code.value) = some vs ∧
      Eval.arrayMethod method items vs = some v := by
  simp only [arrayCall, ite_state] at h
  split at h
  · rename_i hm
    have hm' : method = "includes" := by simpa using hm
    subst hm'
    match args, h with
    | [x], h =>
      simp only [ite_state] at h
      split at h
      · simp only [pure_bind, bind_ok, requireFeature_ok, orReject_ok, pure_ok] at h
        obtain ⟨-, s₁, ⟨-, rfl⟩, op, s₂, ⟨hop, rfl⟩, rfl, -⟩ := h
        simp only [IR.Expr.eval, IR.Expr.evalList] at hv
        cases hx : IR.Expr.eval fs fuel ρ xs.value with
        | none => simp [hx] at hv
        | some w =>
          cases hy : IR.Expr.eval fs fuel ρ x.value with
          | none => simp [hx, hy] at hv
          | some u =>
            simp only [hx, hy, Option.bind_eq_bind, Option.bind_some] at hv
            cases w
            case list items =>
              refine ⟨items, [u], rfl, by simp [IR.Expr.evalList, hy], ?_⟩
              rcases includesOp_some hop with rfl | rfl <;>
                simpa [IR.ExprExt.apply, Eval.arrayMethod] using hv
            all_goals rcases includesOp_some hop with rfl | rfl <;> simp [IR.ExprExt.apply] at hv
      · simp at h
    | [], h => simp at h
    | _ :: _ :: _, h => simp at h
  · simp at h

theorem out_dateOfNumber {a : IR.Expr} {ρ : Eval.Env N} {v : Val N}
    (h : IR.Expr.eval fs fuel ρ (.ext .dateOfNumber [a]) = some v) :
    ∃ t, IR.Expr.eval fs fuel ρ a = some (.num t) ∧ v = .date (JSDate.timeClip t) := by
  simp only [IR.Expr.eval, IR.Expr.evalList] at h
  cases hx : IR.Expr.eval fs fuel ρ a with
  | none => simp [hx, IR.ExprExt.apply] at h
  | some w => cases w <;> simp_all [IR.ExprExt.apply]

theorem out_dateMethod {name : String} {a : IR.Expr} {ρ : Eval.Env N} {v : Val N}
    (h : IR.Expr.eval fs fuel ρ (.ext (.dateMethod name) [a]) = some v) :
    ∃ t, IR.Expr.eval fs fuel ρ a = some (.date t) ∧ Eval.dateMethod name t [] = some v := by
  simp only [IR.Expr.eval, IR.Expr.evalList] at h
  cases hx : IR.Expr.eval fs fuel ρ a with
  | none => simp [hx, IR.ExprExt.apply] at h
  | some w => cases w <;> simp_all [IR.ExprExt.apply]

theorem out_dateUtc {args : List IR.Expr} {ρ : Eval.Env N} {v : Val N}
    (h : IR.Expr.eval fs fuel ρ (.ext .dateUtc args) = some v) :
    ∃ vs xs, IR.Expr.evalList fs fuel ρ args = some vs ∧ Eval.numbers? vs = some xs ∧
      v = .num (JSDate.utc xs) := by
  simp only [IR.Expr.eval] at h
  cases hx : IR.Expr.evalList fs fuel ρ args with
  | none => simp [hx] at h
  | some vs =>
    cases hn : Eval.numbers? vs with
    | none => simp [hx, hn, IR.ExprExt.apply] at h
    | some xs =>
      simp [hx, hn, IR.ExprExt.apply] at h
      exact ⟨vs, xs, rfl, hn, h.symm⟩

/-- The interpreter's rule for `Date.UTC(args)`, where no variable hides
`Date`: the time value of the date that the numbers give. -/
theorem eval_dateUtc (sp sp' sp'' : Span) (args : List Expr) (ρ : Eval.Env N)
    (hnone : ρ.lookup "Date" = none) :
    Eval.eval m fuel ρ (.call sp (.member sp' (.ident sp'' "Date") "UTC") args) =
      (Eval.evalList m fuel ρ args).bind fun vs => (Eval.numbers? vs).map (.num ∘ JSDate.utc) := by
  rw [Eval.eval]
  · simp only [hnone, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
    cases Eval.evalList m fuel ρ args <;> simp
    rename_i vs
    cases Eval.numbers? vs <;> rfl
  all_goals simp

/-- `translateDateUtc` means what the interpreter's rule for `Date.UTC` means,
when `tr` means what each argument means. Its code is no call. -/
theorem translateDateUtc_sound {tr : Expr → TM Code} {env : Translate.Env}
    (htr : ∀ e ctx c ctx', tr e ctx = .ok c ctx' → Sim (N := N) m fs fuel env e c.code)
    (hD : env.has "Date" = false) {sp sp' sp'' : Span} {args : List Expr}
    {ctx ctx' : Ctx} {c : Code} (h : translateDateUtc tr sp args ctx = .ok c ctx') :
    Sim (N := N) m fs fuel env (.call sp (.member sp' (.ident sp'' "Date") "UTC") args) c.code ∧
      ∀ ref outs, c.code ≠ .call ref outs := by
  unfold translateDateUtc at h
  simp at h
  split at h
  · simp at h
    obtain ⟨codes, s₁, hcodes, -, hcode⟩ := h
    have hargs := mapM_sim m fs fuel htr args ctx codes s₁ hcodes
    refine ⟨fun ρs ρo v ha hs hv => ?_, by rw [← hcode]; intro ref outs hc; cases hc⟩
    rw [← hcode] at hv
    obtain ⟨vs, xs, hvs, hxs, rfl⟩ := out_dateUtc fs fuel hv
    rw [eval_dateUtc m fuel _ _ _ _ _ (hs.none hD), hargs ρs ρo vs ha hs hvs]
    simp [hxs]
  · simp at h

/-- A method of a date that takes no arguments: the interpreter evaluates the
receiver, and `dateMethod` gives the value. -/
theorem eval_dateCall (sp sp' : Span) (recv : Expr) (method : String)
    (hr : recv.namesNumber = false) (hsl : method ≠ "slice") (ρ : Eval.Env N) {t : Option Int}
    (hrecv : Eval.eval m fuel ρ recv = some (.date t)) :
    Eval.eval m fuel ρ (.call sp (.member sp' recv method) []) = Eval.dateMethod method t [] := by
  have hrM : ∀ s, recv ≠ .ident s "Math" := by
    intro s h; subst h; simp [Expr.namesNumber] at hr
  have hrD : ∀ s, recv ≠ .ident s "Date" := by
    intro s h; subst h; simp [Expr.namesNumber] at hr
  rw [Eval.eval]
  · rw [hrecv]; simp [Eval.evalList]
  all_goals first
    | exact hrM | exact hsl
    | (intro _ h _; exact hrD _ h)
    | (intros; subst_vars; exact absurd rfl (hrD _))
    | simp

omit [JSNumber N] in
/-- What `translateDateCall` accepts: a method that is not `at` or `slice`,
with no arguments. -/
theorem translateDateCall_ok {s : Span} {method : String} {d c : Code} {args : List Expr}
    {ctx ctx' : Ctx} (h : translateDateCall s method d args ctx = .ok c ctx') :
    method ≠ "at" ∧ method ≠ "slice" ∧ args = [] ∧
      c = ⟨.ext (.dateMethod method) [d.value], false, .number⟩ := by
  unfold translateDateCall at h
  split at h
  · rename_i hm
    split at h
    · rename_i hempty
      simp at h
      refine ⟨?_, ?_, by simpa using hempty, h.1.symm⟩ <;>
        (intro he; subst he; simp [JSDate.methodName?] at hm)
    · simp at h
  · simp at h

-- The value type has many constructors, and `cases` on a value makes a goal
-- for each, so this proof takes more than the default heartbeats.
set_option maxHeartbeats 400000 in
theorem translateArrayCall_sound {F : Nat}
    (ihE : ∀ env exp e ctx c ctx', translateExpr F env exp e ctx = .ok c ctx' →
      Sim (N := N) m fs fuel env e c.code)
    {env : Translate.Env} {s : Span} {recv : Expr} {method : String}
    {args : List Expr} {ctx ctx' : Ctx} {c : Code}
    (h : translateArrayCall (F + 1) env s recv method args ctx = .ok c ctx')
    {sp : Span} (hr : recv.namesNumber = false) :
    Sim (N := N) m fs fuel env (.call s (.member sp recv method) args) c.code := by
  simp only [translateArrayCall, ite_state] at h
  split at h
  · simp only [bind_ok, reject_ne_ok, false_and, exists_false] at h
  rename_i harg
  simp only [pure_bind, bind_ok] at h
  obtain ⟨xs, s₁, hxs, h⟩ := h
  simp only [ite_state] at h
  split at h
  · -- A method of a string: the value that `stringMethod` gives.
    simp only [bind_ok] at h
    obtain ⟨codes, s₂, hcodes, h⟩ := h
    intro ρs ρo v ha hs hv
    obtain ⟨t, vs, ht, hvs, hval⟩ := stringCall_sound fs fuel h hv
    rw [eval_value] at ht
    have hrecv := ihE _ _ _ _ _ _ hxs ρs ρo _ ha hs ht
    have hargs := mapM_sim m fs fuel (fun e ctx c ctx' he => ihE _ _ _ _ _ _ he) args _ codes _ hcodes
      ρs ρo vs ha hs hvs
    obtain ⟨hat, hsl⟩ := stringMethod_not_at hval
    rw [eval_stringCall m fuel _ _ _ _ _ hr (by simpa using harg) hat hsl _ hrecv]
    simp [hargs, hval]
  split at h
  · -- A method of a date, which takes no arguments.
    obtain ⟨-, hsl, rfl, rfl⟩ := translateDateCall_ok h
    intro ρs ρo v ha hs hv
    obtain ⟨t, ht, hval⟩ := out_dateMethod fs fuel hv
    rw [eval_value] at ht
    rw [eval_dateCall m fuel _ _ _ _ hr hsl _ (ihE _ _ _ _ _ _ hxs ρs ρo _ ha hs ht), hval]
  simp only [bind_ok, orReject_ok] at h
  obtain ⟨elem, s₂, ⟨-, rfl⟩, h⟩ := h
  simp only [ite_state] at h
  split at h
  · -- `xs.at(k)`: the element that `atVal` gives.
    rename_i hat
    have hat' : method = "at" := by simpa using hat
    subst hat'
    rcases args with _ | ⟨arg, _ | ⟨_, _⟩⟩
    · simp at h
    · simp only [bind_ok, orReject_ok, requireFeature_ok, ite_state] at h
      obtain ⟨k, s₃, ⟨hk, rfl⟩, -, s₄, ⟨-, rfl⟩, h⟩ := h
      by_cases hm : elem.isMaybe = true
      · simp [hm] at h
      simp only [hm, Bool.false_eq_true, if_false, pure_ok] at h
      obtain ⟨rfl, -⟩ := h
      intro ρs ρo v ha hs hv
      simp only [IR.Expr.eval, IR.Expr.evalList] at hv
      cases hx : IR.Expr.eval fs fuel ρo xs.value with
      | none => simp [hx] at hv
      | some w =>
        simp only [hx, Option.bind_eq_bind, Option.bind_some] at hv
        cases w with
        | list items =>
          simp [IR.ExprExt.apply] at hv
          rw [eval_value] at hx
          have hrecv := ihE _ _ _ _ _ _ hxs ρs ρo _ ha hs hx
          rw [eval_at m fuel _ _ _ _ _ hk hr, hrecv]
          simp [hv]
        | _ => simp [IR.ExprExt.apply] at hv
    · simp at h
  rename_i hat
  split at h
  · -- `xs.slice(start, end)`: the elements that `sliceList` gives.
    rename_i hsl
    have hsl' : method = "slice" := by simpa using hsl
    subst hsl'
    simp only [bind_ok, orReject_ok, ite_state] at h
    obtain ⟨bounds, s₃, ⟨hk, rfl⟩, ⟨start, stop⟩, s₄, ⟨hb, rfl⟩, h⟩ := h
    split at h
    · simp at h
    simp only [pure_ok] at h
    obtain ⟨rfl, -⟩ := h
    intro ρs ρo v ha hs hv
    simp only [IR.Expr.eval, IR.Expr.evalList] at hv
    cases hx : IR.Expr.eval fs fuel ρo xs.value with
    | none => simp [hx] at hv
    | some w =>
      simp only [hx, Option.bind_eq_bind, Option.bind_some] at hv
      cases w with
      | list items =>
        simp [IR.ExprExt.apply] at hv
        rw [eval_value] at hx
        have hrecv := ihE _ _ _ _ _ _ hxs ρs ρo _ ha hs hx
        rw [eval_slice m fuel _ _ _ _ hk hb hr, hrecv]
        simp [hv]
      | _ => simp [IR.ExprExt.apply] at hv
  rename_i hsl
  simp only [bind_ok] at h
  obtain ⟨codes, s₃, hcodes, h⟩ := h
  intro ρs ρo v ha hs hv
  obtain ⟨items, vs, hitems, hvs, hval⟩ := arrayCall_sound fs fuel h hv
  rw [eval_value] at hitems
  have hrecv := ihE _ _ _ _ _ _ hxs ρs ρo _ ha hs hitems
  have hargs := mapM_sim m fs fuel (fun e ctx c ctx' he => ihE _ _ _ _ _ _ he) args _ codes _ hcodes
    ρs ρo vs ha hs hvs
  rw [eval_arrayCall m fuel _ _ _ _ _ hr (by simpa using harg) (by simpa using hat) (by simpa using hsl) _ hrecv]
  simp [hargs, hval]

/-! ### Object spread -/

/-- `{ ...e, props }`: the interpreter evaluates `e`, then the properties after
it, and sets each of them in the object of `e`. -/
theorem eval_spread (s sp : Span) (e : Expr) (ps : List Property) (ρ : Eval.Env N) :
    Eval.eval m fuel ρ (.object s (.spread sp e :: ps)) =
      (Eval.eval m fuel ρ e).bind fun
        | .obj obj => (Eval.evalProps m fuel ρ ps).bind fun rest =>
            some (.obj (rest.foldl (fun acc (k, v) => Eval.setProp acc k v) obj))
        | _ => none := by
  rw [Eval.eval]
  generalize Eval.eval m fuel ρ e = r
  cases r with
  | none => rfl
  | some w => cases w <;> simp [Option.bind_eq_bind]

omit [JSNumber N] in
theorem spreadOf_some {props : List Property} {base : Expr} {rest : List Property}
    (h : spreadOf props = some (base, rest)) : ∃ sp, props = .spread sp base :: rest := by
  unfold spreadOf at h
  split at h
  · cases h; exact ⟨_, rfl⟩
  · cases h

omit [JSNumber N] in
theorem spreadFieldType_ok {name : String} {fields : List (String × Ty)} {seen : List String} {sp : Span}
    {key : String} {t : Ty} {ctx ctx' : Ctx} (h : spreadFieldType name fields seen sp key ctx = .ok t ctx') :
    ctx' = ctx := by
  simp only [spreadFieldType, bind_ok, orReject_ok, ite_state] at h
  obtain ⟨t', s₁, ⟨-, rfl⟩, h⟩ := h
  split at h
  · simp at h
  simp only [pure_bind, ite_state] at h
  split at h
  · simp at h
  simp only [pure_ok] at h
  exact h.2.symm

theorem translateSpread_sound {F : Nat}
    (ihE : ∀ env exp e ctx c ctx', translateExpr F env exp e ctx = .ok c ctx' →
      Sim (N := N) m fs fuel env e c.code)
    {env : Translate.Env} {s : Span} {base : Expr} {rest : List Property} {ctx ctx' : Ctx} {c : Code}
    (h : translateSpread (F + 1) env s base rest ctx = .ok c ctx') {sp : Span} :
    Sim (N := N) m fs fuel env (.object s (.spread sp base :: rest)) c.code := by
  simp only [translateSpread, bind_ok] at h
  obtain ⟨b, s₁, hb, h⟩ := h
  cases hst : b.type.structRef? with
  | none => simp [hst] at h
  | some ra =>
    obtain ⟨ref, args⟩ := ra
    simp only [hst, bind_ok, get_ok, orReject_ok] at h
    obtain ⟨_, _, ⟨rfl, rfl⟩, info, s₂, ⟨-, rfl⟩, ⟨seen, parts⟩, s₃, hfold, h⟩ := h
    simp only [pure_ok] at h
    obtain ⟨rfl, -⟩ := h
    have key := fold_sim (N := N) (env := env) m fs fuel ?hstep rest [] [] _ _ _ hfold
    · obtain ⟨new, hnew, hsim⟩ := key
      simp only [List.nil_append] at hnew
      subst hnew
      intro ρs ρo v ha hs hv
      simp only [IR.Expr.eval] at hv
      cases hx : IR.Expr.eval fs fuel ρo b.value with
      | none => simp [hx] at hv
      | some w =>
        cases w with
        | obj obj =>
          cases hfs : IR.Expr.evalFields fs fuel ρo parts with
          | none => simp [hx, hfs] at hv
          | some us =>
            simp only [hx, hfs, Option.bind_eq_bind, Option.bind_some] at hv
            rw [eval_value] at hx
            rw [eval_spread, ihE _ _ _ _ _ _ hb ρs ρo _ ha hs hx]
            simp only [hsim ρs ρo us ha hs hfs, Option.bind_some]
            simpa using hv
        | _ => simp [hx] at hv
    case hstep =>
      intro a acc p c₀ r c₁ hg
      cases p with
      | shorthand ps name =>
        simp only [bind_ok, pure_bind] at hg
        obtain ⟨fieldType, _, hft, v, _, hv, hg⟩ := hg
        obtain rfl := spreadFieldType_ok hft
        simp only [ite_state] at hg
        split at hg
        · simp only [pure_ok] at hg
          obtain ⟨rfl, -⟩ := hg
          refine ⟨name, v.value, rfl, ?_⟩
          intro ρs ρo w ha hs hw rest
          rw [eval_value] at hw
          have := ihE _ _ _ _ _ _ hv ρs ρo w ha hs hw
          simp [Eval.evalProps, this]
          cases Eval.evalProps m fuel ρs rest <;> rfl
        · simp at hg
      | spread ps v => simp at hg
      | keyValue ps key val =>
        cases key with
        | ident key =>
          by_cases hk : key = "__proto__"
          · subst hk; simp at hg
          simp only [hk, beq_iff_eq, if_false, bind_ok, pure_bind] at hg
          obtain ⟨fieldType, _, hft, v, _, hv, hg⟩ := hg
          obtain rfl := spreadFieldType_ok hft
          simp only [ite_state] at hg
          split at hg
          · simp only [pure_ok] at hg
            obtain ⟨rfl, -⟩ := hg
            refine ⟨key, v.value, rfl, ?_⟩
            intro ρs ρo w ha hs hw rest
            rw [eval_value] at hw
            have := ihE _ _ _ _ _ _ hv ρs ρo w ha hs hw
            simp [Eval.evalProps, this, hk]
            cases Eval.evalProps m fuel ρs rest <;> rfl
          · simp at hg
        | _ => simp at hg

omit [JSNumber N] in
/-- `firstFitting` gives a result of one of its two parsers, from the state it
starts from. -/
theorem firstFitting_ok {A : Type} {x y : TM A} {fits : A → Bool} {s s' : Ctx} {a : A}
    (h : firstFitting x y fits s = .ok a s') : x s = .ok a s' ∨ y s = .ok a s' := by
  simp only [firstFitting] at h
  split at h
  · rename_i b s₁ hx
    split at h
    · obtain ⟨rfl, rfl⟩ : b = a ∧ s₁ = s' := by simpa using h
      exact .inl hx
    · exact .inr h
  · exact .inr h

omit [JSNumber N] in
/-- Fixing the type of an `undefined` argument does not change its value. -/
theorem fixArgs_value (ps : List Ty) (cs : List Code) :
    (fixArgs ps cs).map Code.value = cs.map Code.value := by
  simp only [fixArgs, List.map_map]
  congr 1
  funext c
  simp only [Function.comp]
  split <;> rfl

/-- The type that `optArgs` writes on an argument does not change its value. -/
theorem evalList_optArgs (sol : List (String × Ty)) (ρ : Eval.Env N) :
    ∀ (cs : List Code) (ps : List Ty),
      IR.Expr.evalList fs fuel ρ (optArgs sol cs ps) = IR.Expr.evalList fs fuel ρ (cs.map Code.value)
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | c :: cs, p :: ps => by
    simp only [optArgs, List.map_cons, IR.Expr.evalList, evalList_optArgs sol ρ cs ps]
    split <;> (try split) <;> simp [IR.Expr.eval]

/-! ### Maps -/

/-- An owned map, read as its local, means what the name means. -/
theorem ownedMap_sim {env : Translate.Env} {e : Expr} {c : Code} (h : ownedMap? env e = some c) :
    Sim (N := N) m fs fuel env e c.code := by
  intro ρs ρo v ha _ hv
  cases e with
  | ident sp name =>
    simp only [ownedMap?] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      simp only [IR.Expr.eval] at hv
      rw [← ha name] at hv
      simp only [Eval.eval, hv]
    · simp at h
  | _ => simp [ownedMap?] at h

/-- The receiver of `size`, `get` or `has` means what the expression means. -/
theorem translateRecv_sim {env : Translate.Env} {e : Expr} {tr : Expr → TM Code} {ctx ctx' : Ctx}
    {c : Code} (htr : ∀ ctx c ctx', tr e ctx = .ok c ctx' → Sim (N := N) m fs fuel env e c.code)
    (h : translateRecv tr env e ctx = .ok c ctx') : Sim (N := N) m fs fuel env e c.code := by
  cases hc : ownedMap? env e with
  | some c' =>
    simp only [translateRecv, hc, pure_ok] at h
    obtain ⟨rfl, -⟩ := h
    exact ownedMap_sim m fs fuel hc
  | none =>
    simp only [translateRecv, hc] at h
    exact htr _ _ _ h

/-- The value of `m.get(k)` or `m.has(k)`, from the entries of the map and the
key. -/
def mapMethodVal (name : String) : Val N → Val N → Option (Val N)
  | .map entries, k =>
    (Eval.mapFind entries k).bind fun found =>
      if name = "get" then some (found.getD .undefined)
      else if name = "has" then some (.bool found.isSome) else none
  | .set elems, x => (Eval.setHas elems x).bind fun found => if name = "has" then some (.bool found) else none
  | _, _ => none

theorem eval_mapMethod (sp sp' : Span) (recv key : Expr) (name : String) (hr : recv.namesNumber = false)
    (hk : ∀ sa par ps b, key ≠ .arrow sa par ps b) (hat : name ≠ "at") (hsl : name ≠ "slice")
    (ρ : Eval.Env N) :
    Eval.eval m fuel ρ (.call sp (.member sp' recv name) [key]) =
      (Eval.eval m fuel ρ recv).bind fun r =>
        match r with
        | .map _ | .set _ => (Eval.eval m fuel ρ key).bind (mapMethodVal name r)
        | .list items => (Eval.eval m fuel ρ key).bind fun k => Eval.arrayMethod name items [k]
        | .str s => (Eval.eval m fuel ρ key).bind fun k => Eval.stringMethod name s [k]
        | _ => none := by
  have hr' : ∀ s, recv ≠ .ident s "Number" := by
    intro s h; subst h; simp [Expr.namesNumber] at hr
  have hrM : ∀ s, recv ≠ .ident s "Math" := by
    intro s h; subst h; simp [Expr.namesNumber] at hr
  have hrO : ∀ s, recv ≠ .ident s "Object" := by
    intro s h; subst h; simp [Expr.namesNumber] at hr
  have hrD : ∀ s, recv ≠ .ident s "Date" := by
    intro s h; subst h; simp [Expr.namesNumber] at hr
  generalize hR : Eval.eval m fuel ρ recv = r
  rw [Eval.eval]
  all_goals first
    | (rw [hR]
       cases r with
       | none => rfl
       | some v =>
         cases v <;> simp only [Option.bind_some, Option.bind_eq_bind]
         all_goals first
           | rfl
           | (cases Eval.eval m fuel ρ key <;> simp [mapMethodVal]))
    | exact hr'
    | exact hrM
    | exact hrO
    | exact hrD
    | (intro _ h _; exact hrD _ h)
    | (intro sa par p b h; exact hk _ _ _ _ h)
    | (intro sa par p q b h; exact hk _ _ _ _ h)
    | (intro h; exact hat h)
    | (intro h; exact hsl h)

/-- What `.ext op args` gives in the output, from the values of its
arguments. -/
theorem out_ext {op : IR.ExprExt} {args : List IR.Expr} {ρ : Eval.Env N} {v : Val N}
    (h : IR.Expr.eval fs fuel ρ (.ext op args) = some v) :
    ∃ vs, IR.Expr.evalList fs fuel ρ args = some vs ∧ IR.ExprExt.apply op vs = some v := by
  simp only [IR.Expr.eval] at h
  cases hl : IR.Expr.evalList fs fuel ρ args with
  | none => simp [hl] at h
  | some vs => simp [hl] at h; exact ⟨vs, rfl, h⟩

/-- `.ext op [r, k]` means `recv.name(key)`, when `r` means `recv`, `k` means
`key`, and `op` gives what the interpreter's method gives. -/
theorem collection_call_sim {env : Translate.Env} {s sp : Span} {recv key : Expr} {name : String}
    {op : IR.ExprExt} {r k : IR.Expr} (hr : recv.namesNumber = false)
    (hk : ∀ sa par ps b, key ≠ .arrow sa par ps b) (hat : name ≠ "at") (hsl : name ≠ "slice")
    (hrecv : Sim (N := N) m fs fuel env recv r) (hkey : Sim (N := N) m fs fuel env key k)
    (happly : ∀ vr vk w : Val N, IR.ExprExt.apply op [vr, vk] = some w → mapMethodVal name vr vk = some w) :
    Sim (N := N) m fs fuel env (.call s (.member sp recv name) [key]) (.ext op [r, k]) := by
  intro ρs ρo w ha hs hw
  obtain ⟨vs, hvs, happ⟩ := out_ext fs fuel hw
  simp only [IR.Expr.evalList] at hvs
  cases hx : IR.Expr.eval fs fuel ρo r with
  | none => simp [hx] at hvs
  | some vr =>
    cases hy : IR.Expr.eval fs fuel ρo k with
    | none => simp [hx, hy] at hvs
    | some vk =>
      simp [hx, hy] at hvs
      subst hvs
      have hv := happly _ _ _ happ
      rw [eval_mapMethod m fuel _ _ _ _ _ hr hk hat hsl, hrecv ρs ρo _ ha hs hx]
      cases vr <;> simp only [Option.bind_some] <;>
        first
        | (rw [hkey ρs ρo _ ha hs hy]; exact hv)
        | (simp [mapMethodVal] at hv)

theorem mapMethodOf_some {sp : Span} {recv recv' : Expr} {name : String} {op : IR.ExprExt}
    (h : mapMethodOf (.member sp recv name) = some (recv', op)) :
    recv' = recv ∧ ((name = "get" ∧ op = .mapGet) ∨ (name = "has" ∧ op = .mapHas)) := by
  simp only [mapMethodOf] at h
  split at h <;> simp_all

theorem translateMapMethod_sound {F : Nat}
    (ihE : ∀ env exp e ctx c ctx', translateExpr F env exp e ctx = .ok c ctx' →
      Sim (N := N) m fs fuel env e c.code)
    {env : Translate.Env} {s : Span} {recv : Expr} {op : IR.ExprExt}
    {args : List Expr} {ctx ctx' : Ctx} {c : Code}
    (h : translateMapMethod (F + 1) env s recv op args ctx = .ok c ctx')
    {sp : Span} {name : String} (hname : mapMethodOf (.member sp recv name) = some (recv, op)) :
    Sim (N := N) m fs fuel env (.call s (.member sp recv name) args) c.code := by
  obtain ⟨-, hop⟩ := mapMethodOf_some hname
  simp only [translateMapMethod, ite_state] at h
  split at h
  · simp at h
  rename_i hr
  rcases args with _ | ⟨key, _ | ⟨_, _⟩⟩ <;> simp only at h <;> try (simp at h; done)
  try simp only [pure_bind, ite_state] at h
  split at h
  · simp at h
  rename_i hka
  simp only [Bool.false_eq_true, ↓reduceIte, bind_ok] at h
  obtain ⟨o, s₁, ho, h⟩ := h
  have hrecv := translateRecv_sim m fs fuel (fun _ _ _ hx => ihE _ _ _ _ _ _ hx) ho
  have hrv : Sim (N := N) m fs fuel env recv o.value := fun ρs ρo w ha hs hw =>
    hrecv ρs ρo w ha hs (by rwa [eval_value] at hw)
  have hr' : recv.namesNumber = false := by simpa using hr
  have hk : ∀ sa par ps b, key ≠ .arrow sa par ps b := fun sa par ps b he => hka _ _ _ _ he
  -- `has` is the method when `op` is `.mapHas`, and `get` otherwise.
  have hasName : (op == .mapHas) = true → name = "has" := fun hhas => by
    rcases hop with ⟨-, rfl⟩ | ⟨h1, -⟩
    · exact absurd hhas (by decide)
    · exact h1
  have getName : ¬(op == .mapHas) = true → name = "get" := fun hhas => by
    rcases hop with ⟨h1, -⟩ | ⟨-, rfl⟩
    · exact h1
    · exact absurd (by decide) hhas
  cases hot : o.type
  all_goals try (simp [hot] at h; done)
  next k v =>
    simp only [hot, bind_ok] at h
    obtain ⟨kc, s₂, hkc, h⟩ := h
    have hkv : Sim (N := N) m fs fuel env key kc.value := fun ρs ρo w ha hs hw =>
      ihE _ _ _ _ _ _ hkc ρs ρo w ha hs (by rwa [eval_value] at hw)
    try simp only [ite_state] at h
    split at h
    rotate_left
    · simp at h
    try simp only [pure_bind, ite_state] at h
    split at h
    · rename_i hhas
      simp at h
      obtain ⟨rfl, -⟩ := h
      obtain rfl := hasName hhas
      refine collection_call_sim m fs fuel hr' hk (by decide) (by decide) hrv hkv fun vr vk w happ => ?_
      cases vr <;> simp [IR.ExprExt.apply] at happ
      obtain ⟨found, hf, rfl⟩ := happ
      simp [mapMethodVal, hf]
    · rename_i hhas
      split at h
      · simp at h
      simp at h
      obtain ⟨rfl, -⟩ := h
      obtain rfl := getName hhas
      refine collection_call_sim m fs fuel hr' hk (by decide) (by decide) hrv hkv fun vr vk w happ => ?_
      cases vr <;> simp [IR.ExprExt.apply] at happ
      obtain ⟨found, hf, rfl⟩ := happ
      simp [mapMethodVal, hf]
  next t =>
    simp only [hot, ite_state] at h
    split at h
    rotate_left
    · simp at h
    rename_i hhas
    simp only [bind_ok] at h
    obtain ⟨xc, s₂, hxc, h⟩ := h
    have hxv : Sim (N := N) m fs fuel env key xc.value := fun ρs ρo w ha hs hw =>
      ihE _ _ _ _ _ _ hxc ρs ρo w ha hs (by rwa [eval_value] at hw)
    try simp only [ite_state] at h
    split at h
    rotate_left
    · simp at h
    simp at h
    obtain ⟨rfl, -⟩ := h
    obtain rfl := hasName hhas
    refine collection_call_sim m fs fuel hr' hk (by decide) (by decide) hrv hxv fun vr vk w happ => ?_
    cases vr <;> (try simp only [IR.ExprExt.apply] at happ) <;> try (simp at happ; done)
    rename_i elems
    simp only [mapMethodVal]
    cases hf : Eval.setHas elems vk <;> simp [hf] at happ ⊢ <;> exact happ

/-- A read of a field, of a member of a string enum, or of the `size` of a map. -/
theorem translateMember_sound {F : Nat}
    (ihE : ∀ env exp e ctx c ctx', translateExpr F env exp e ctx = .ok c ctx' →
      Sim (N := N) m fs fuel env e c.code)
    {env : Translate.Env} {exp : Option Ty} {sp : Span} {obj : Expr} {name : String} {ctx ctx' : Ctx}
    {c : Code} (h : translateExprCore (F + 1) env exp (.member sp obj name) ctx = .ok c ctx') :
    Sim (N := N) m fs fuel env (.member sp obj name) c.code := by
  simp only [translateExprCore] at h
  cases he : enumOf? env obj with
  | some e =>
    -- `T.A`: the string of the member, which the interpreter reads from
    -- the object of the enum.
    simp only [he, bind_ok, orReject_ok, pure_ok] at h
    obtain ⟨value, s₁, ⟨hval, rfl⟩, rfl, -⟩ := h
    intro ρs ρo v _ hs hv'
    simp only [IR.Expr.eval, Option.some.injEq] at hv'
    subst hv'
    obtain ⟨sp', n, rfl⟩ : ∃ sp' n, obj = .ident sp' n := by
      cases obj <;> simp [enumOf?] at he; exact ⟨_, _, rfl⟩
    simp only [enumOf?, Bool.or_eq_true] at he
    split at he
    · simp at he
    rename_i hng
    simp only [not_or, Bool.not_eq_true] at hng
    have hname : e.name = n := by simpa using List.find?_some he
    have hres := hs.2.2 e (List.mem_of_find?_eq_some he)
    rw [hname] at hres
    have hnone : ρs.lookup n = none := hs.none hng.1
    have hg : n ≠ "NaN" ∧ n ≠ "Infinity" ∧ n ≠ "undefined" := by
      have := hng.2
      refine ⟨?_, ?_, ?_⟩ <;> intro h <;> subst h <;> simp [isGlobalName, isNumberName] at this
    simp only [Eval.eval, Expr.optSpine, Bool.false_eq_true, ↓reduceIte, hnone, hres, hg.1, hg.2.1,
      hg.2.2, Option.map_some, Eval.enumObject, Eval.getProp, beq_iff_eq, Option.bind_eq_bind,
      Option.bind_some]
    rw [lookup_map_str hval]
  | none =>
  simp only [he] at h
  split at h
  · rename_i hsp
    cases hc : (Expr.member sp obj name).optChain? with
    | none => simp [hc] at h
    | some bp =>
      obtain ⟨base, path⟩ := bp
      simp only [hc, bind_ok] at h
      obtain ⟨o, s₁, ho, ⟨bind, ty⟩, s₂, -, h⟩ := h
      simp only [pure_ok] at h
      obtain ⟨rfl, -⟩ := h
      intro ρs ρo v ha hs hv'
      simp only [IR.Expr.eval, IR.Expr.evalList] at hv'
      cases hobj : IR.Expr.eval fs fuel ρo o.code with
      | none => simp [hobj] at hv'
      | some ov =>
        have := ihE _ _ _ _ _ _ ho ρs ρo ov ha hs hobj
        simp only [hobj] at hv'
        rw [eval_member_chain m fuel hsp hc this]
        cases ov <;> simp only [IR.ExprExt.apply] at hv' <;> first | exact hv' | simp at hv'
  rename_i hsp
  simp only [pure_bind, bind_ok] at h
  obtain ⟨o, s₁, ho, h⟩ := h
  have hrecv := translateRecv_sim m fs fuel (fun _ _ _ hx => ihE _ _ _ _ _ _ hx) ho
  simp only [ite_state] at h
  split at h
  · -- `xs.length`: the spec gives the length of the array.
    rename_i hlen
    simp at h
    obtain ⟨rfl, -⟩ := h
    have hn : name = "length" := by simp at hlen; exact hlen.2
    subst hn
    exact length_sound m fs fuel (by simpa using hsp) fun ρs ρo w ha hs hw =>
      hrecv ρs ρo w ha hs (by rwa [eval_value] at hw)
  cases hot : o.type
  case map k v =>
    -- `m.size`, the number of entries.
    simp only [hot, ite_state] at h
    split at h
    · rename_i hsize
      obtain rfl : name = "size" := by simpa using hsize
      simp only [pure_ok] at h
      obtain ⟨rfl, -⟩ := h
      intro ρs ρo w ha hs hw
      obtain ⟨vs, hvs, happ⟩ := out_ext fs fuel hw
      simp only [IR.Expr.evalList] at hvs
      cases hx : IR.Expr.eval fs fuel ρo o.value with
      | none => simp [hx] at hvs
      | some vo =>
        simp [hx] at hvs
        subst hvs
        rw [eval_value] at hx
        have hobj := hrecv ρs ρo _ ha hs hx
        cases vo <;> (try simp only [IR.ExprExt.apply] at happ) <;> try (simp at happ; done)
        rename_i entries
        simp only [Option.some.injEq] at happ
        subst happ
        simp [Eval.eval, hsp, hobj]
    · simp at h
  case string =>
    -- `s.length`, the number of code units.
    simp only [hot, ite_state] at h
    split at h
    · rename_i hlen
      obtain rfl : name = "length" := by simpa using hlen
      simp only [pure_ok] at h
      obtain ⟨rfl, -⟩ := h
      intro ρs ρo w ha hs hw
      obtain ⟨vs, hvs, happ⟩ := out_ext fs fuel hw
      simp only [IR.Expr.evalList] at hvs
      cases hx : IR.Expr.eval fs fuel ρo o.value with
      | none => simp [hx] at hvs
      | some vo =>
        simp [hx] at hvs
        subst hvs
        rw [eval_value] at hx
        have hobj := hrecv ρs ρo _ ha hs hx
        cases vo <;> (try simp only [IR.ExprExt.apply] at happ) <;> try (simp at happ; done)
        rename_i str
        simp only [Option.some.injEq] at happ
        subst happ
        simp [Eval.eval, hsp, hobj]
    · simp at h
  case set t =>
    -- `s.size`, the number of elements.
    simp only [hot, ite_state] at h
    split at h
    · rename_i hsize
      obtain rfl : name = "size" := by simpa using hsize
      simp only [pure_ok] at h
      obtain ⟨rfl, -⟩ := h
      intro ρs ρo w ha hs hw
      obtain ⟨vs, hvs, happ⟩ := out_ext fs fuel hw
      simp only [IR.Expr.evalList] at hvs
      cases hx : IR.Expr.eval fs fuel ρo o.value with
      | none => simp [hx] at hvs
      | some vo =>
        simp [hx] at hvs
        subst hvs
        rw [eval_value] at hx
        have hobj := hrecv ρs ρo _ ha hs hx
        cases vo <;> (try simp only [IR.ExprExt.apply] at happ) <;> try (simp at happ; done)
        rename_i elems
        simp only [Option.some.injEq] at happ
        subst happ
        simp [Eval.eval, hsp, hobj]
    · simp at h
  all_goals try (simp [hot] at h; done)
  all_goals
    simp only [hot] at h
    simp at h
    obtain ⟨_, _, ⟨rfl, rfl⟩, ty, ⟨-, rfl⟩, rfl⟩ := h
    intro ρs ρo v ha hs hv'
    simp only [IR.Expr.eval] at hv'
    cases hobj : IR.Expr.eval fs fuel ρo o.code with
    | none => simp [hobj] at hv'
    | some ov =>
      have := hrecv ρs ρo ov ha hs hobj
      simp only [Eval.eval, hsp, Bool.false_eq_true, ↓reduceIte, this]
      simp only [hobj, Option.bind_eq_bind, Option.bind_some] at hv'
      cases ov <;> simp_all

/-- What the output's loop runs over is what the interpreter's loop visits. -/
theorem loopOver_sim {env : Translate.Env} {iterable : Expr} {items : Code} {elem : Ty}
    {li : IR.Expr} (hsim : Sim (N := N) m fs fuel env iterable items.code)
    (hlo : loopOver items = some (elem, li)) {ρs ρo : Eval.Env N} {vs : List (Val N)}
    (ha : Agree ρs ρo) (hs : Scoped m env ρs) (hi : IR.Expr.eval fs fuel ρo li = some (.list vs)) :
    ∃ v, Eval.eval m fuel ρs iterable = some v ∧ Eval.iterValues v = some vs := by
  unfold loopOver at hlo
  split at hlo <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hlo
  · obtain ⟨-, rfl⟩ := hlo
    exact ⟨_, hsim ρs ρo _ ha hs hi, rfl⟩
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
      refine ⟨w, hsim ρs ρo _ ha hs hx, ?_⟩
      cases w <;> simp [IR.ExprExt.apply] at happ
      subst happ
      rfl

/-! ### Array spread -/

/-- What a piece of an array literal stands for: an element that is not a
spread, which its code means, or a spread `...x`, whose list is what a loop
over `x` visits. -/
def PartSim (env : Translate.Env) (e : Expr) : ElemPart → Prop
  | .one c => e.spreadArg? = none ∧ Sim (N := N) m fs fuel env e c.code
  | .many t li => ∃ sp x items, e = .spread sp x ∧ Sim (N := N) m fs fuel env x items.code ∧
      loopOver items = some (t, li)

theorem spreadArg?_some {e x : Expr} {sp : Span} (h : e.spreadArg? = some (sp, x)) :
    e = .spread sp x := by
  cases e <;> simp [Expr.spreadArg?] at h
  obtain ⟨rfl, rfl⟩ := h
  rfl

theorem translateElem_sim {env : Translate.Env} {tr : Option Ty → Expr → TM Code}
    (htr : ∀ exp e ctx c ctx', tr exp e ctx = .ok c ctx' → Sim (N := N) m fs fuel env e c.code)
    {exp : Option Ty} {e : Expr} {ctx ctx' : Ctx} {p : ElemPart}
    (h : translateElem tr exp e ctx = .ok p ctx') : PartSim (N := N) m fs fuel env e p := by
  unfold translateElem at h
  cases hs : e.spreadArg? with
  | some q =>
    obtain ⟨sp, x⟩ := q
    rw [hs] at h
    simp only [bind_ok, orReject_ok, pure_ok] at h
    obtain ⟨items, s₁, hi, ⟨t, li⟩, s₂, ⟨hlo, -⟩, rfl, -⟩ := h
    exact ⟨sp, x, items, spreadArg?_some hs, htr _ _ _ _ _ hi, hlo⟩
  | none =>
    rw [hs] at h
    simp only [bind_ok, pure_ok] at h
    obtain ⟨c, s₁, hc, rfl, -⟩ := h
    exact ⟨hs, htr _ _ _ _ _ hc⟩

/-- The lists that the output joins hold, one after another, what the array
literal holds. -/
theorem mapM_parts_sim {env : Translate.Env} {f : Expr → TM ElemPart}
    (hf : ∀ e ctx p ctx', f e ctx = .ok p ctx' → PartSim (N := N) m fs fuel env e p) (t : IR.Ty) :
    ∀ (es : List Expr) (ctx : Ctx) (ps : List ElemPart) (ctx' : Ctx),
      es.mapM f ctx = .ok ps ctx' →
      ∀ (ρs ρo : Eval.Env N) ws lss, Agree ρs ρo → Scoped m env ρs →
        IR.Expr.evalList fs fuel ρo (partLists t ps) = some ws → ws.mapM IR.listItems? = some lss →
        Eval.evalElems m fuel ρs es = some lss.flatten := by
  intro es
  induction es with
  | nil =>
    intro ctx ps ctx' h ρs ρo ws lss _ _ hws hl
    simp [List.mapM_nil] at h
    obtain ⟨rfl, -⟩ := h
    simp [partLists, IR.Expr.evalList] at hws
    subst hws
    simp at hl
    subst hl
    simp [Eval.evalElems]
  | cons e es ih =>
    intro ctx ps ctx' h ρs ρo ws lss ha hs hws hl
    simp [List.mapM_cons] at h
    obtain ⟨p, s₁, hp, ps', hps, rfl⟩ := h
    have hpart := hf _ _ _ _ hp
    cases p with
    | many t' li =>
      obtain ⟨sp, x, items, rfl, hsim, hlo⟩ := hpart
      simp only [partLists, IR.Expr.evalList] at hws
      cases hw : IR.Expr.eval fs fuel ρo li with
      | none => simp [hw] at hws
      | some w =>
        cases hws' : IR.Expr.evalList fs fuel ρo (partLists t ps') with
        | none => simp [hw, hws'] at hws
        | some ws' =>
          simp [hw, hws'] at hws
          subst hws
          cases w with
          | list l =>
            cases hl' : ws'.mapM IR.listItems? with
            | none => simp [List.mapM_cons, IR.listItems?, hl'] at hl
            | some lss' =>
              simp [List.mapM_cons, IR.listItems?, hl'] at hl
              subst hl
              obtain ⟨v, hv, hiter⟩ := loopOver_sim m fs fuel hsim hlo ha hs hw
              have := ih _ _ _ hps ρs ρo ws' lss' ha hs hws' hl'
              simp [Eval.evalElems, hv, hiter, this]
          | _ => simp [List.mapM_cons, IR.listItems?] at hl
    | one c =>
      obtain ⟨hsp, hsim⟩ := hpart
      simp only [partLists] at hws
      split at hws
      · next xs ty rest heq =>
        simp only [IR.Expr.evalList, IR.Expr.eval] at hws
        cases hv0 : IR.Expr.eval fs fuel ρo c.value with
        | none => simp [hv0] at hws
        | some v0 =>
          cases hxs : IR.Expr.evalList fs fuel ρo xs with
          | none => simp [hv0, hxs] at hws
          | some vxs =>
            cases hrest : IR.Expr.evalList fs fuel ρo rest with
            | none => simp [hv0, hxs, hrest] at hws
            | some ws' =>
              simp [hv0, hxs, hrest] at hws
              subst hws
              cases hl' : ws'.mapM IR.listItems? with
              | none => simp [List.mapM_cons, IR.listItems?, hl'] at hl
              | some lss' =>
                simp [List.mapM_cons, IR.listItems?, hl'] at hl
                subst hl
                have hev : IR.Expr.evalList fs fuel ρo (partLists t ps') = some (.list vxs :: ws') := by
                  simp [heq, IR.Expr.evalList, IR.Expr.eval, hxs, hrest]
                have hm : (Val.list vxs :: ws').mapM IR.listItems? = some (vxs :: lss') := by
                  simp [List.mapM_cons, IR.listItems?, hl']
                have := ih _ _ _ hps ρs ρo _ _ ha hs hev hm
                rw [eval_value] at hv0
                rw [evalElems_cons m fuel hsp, hsim ρs ρo _ ha hs hv0, this]
                simp
      · simp only [IR.Expr.evalList, IR.Expr.eval] at hws
        cases hv0 : IR.Expr.eval fs fuel ρo c.value with
        | none => simp [hv0] at hws
        | some v0 =>
          cases hws' : IR.Expr.evalList fs fuel ρo (partLists t ps') with
          | none => simp [hv0, hws'] at hws
          | some ws' =>
            simp [hv0, hws'] at hws
            subst hws
            cases hl' : ws'.mapM IR.listItems? with
            | none => simp [List.mapM_cons, IR.listItems?, hl'] at hl
            | some lss' =>
              simp [List.mapM_cons, IR.listItems?, hl'] at hl
              subst hl
              have := ih _ _ _ hps ρs ρo _ _ ha hs hws' hl'
              rw [eval_value] at hv0
              rw [evalElems_cons m fuel hsp, hsim ρs ρo _ ha hs hv0, this]
              simp

/-- An array literal with a spread means the lists that the output joins. -/
theorem translateSpreadArray_sound {env : Translate.Env} {tr : Option Ty → Expr → TM Code}
    (htr : ∀ exp e ctx c ctx', tr exp e ctx = .ok c ctx' → Sim (N := N) m fs fuel env e c.code)
    {exp : Option Ty} {s : Span} {elems : List Expr} {ctx ctx' : Ctx} {c : Code}
    (h : translateSpreadArray tr exp s elems ctx = .ok c ctx') :
    Sim (N := N) m fs fuel env (.array s elems) c.code := by
  simp only [translateSpreadArray, bind_ok, pure_ok] at h
  obtain ⟨parts, s₁, hparts, elem, s₂, -, u, s₃, -, rfl, -⟩ := h
  intro ρs ρo v ha hs hv
  obtain ⟨ws, hws, happ⟩ := out_ext fs fuel hv
  simp only [IR.ExprExt.apply] at happ
  cases hm : ws.mapM IR.listItems? with
  | none => simp [hm] at happ
  | some lss =>
    simp [hm] at happ
    subst happ
    have := mapM_parts_sim m fs fuel (fun _ _ _ _ hp => translateElem_sim m fs fuel htr hp) elem.lean
      elems ctx parts s₁ hparts ρs ρo ws lss ha hs hws hm
    simp [Eval.eval, this]

/-- `new Date(t)` means what the interpreter's rule for it means: the date
whose time value is TimeClip of `t`. -/
theorem translateNewDate_sound {tr : Option Ty → Expr → TM Code} {env : Translate.Env}
    (htr : ∀ exp e ctx c ctx', tr exp e ctx = .ok c ctx' → Sim (N := N) m fs fuel env e c.code)
    {sp : Span} {typeArgs : List TypeExpr} {args : List Expr} {ctx ctx' : Ctx} {c : Code}
    (h : translateNewDate tr env sp args ctx = .ok c ctx') :
    Sim (N := N) m fs fuel env (.new sp "Date" typeArgs args) c.code := by
  match args, h with
  | [arg], h =>
    unfold translateNewDate at h
    split at h
    · simp only [bind_ok, reject_ne_ok, false_and, exists_false] at h
    rename_i hhas
    simp only [pure_bind, bind_ok] at h
    obtain ⟨t, s₁, ht, h⟩ := h
    split at h
    · simp at h
      obtain ⟨rfl, -⟩ := h
      intro ρs ρo v ha hs hv
      obtain ⟨x, hx, rfl⟩ := out_dateOfNumber fs fuel hv
      rw [eval_value] at hx
      have harg := htr _ _ _ _ _ ht ρs ρo _ ha hs hx
      simp [Eval.eval, hs.none (by simpa using hhas), harg]
    · simp at h
  | [], h =>
    unfold translateNewDate at h
    split at h <;> simp only [bind_ok, pure_bind, reject_ne_ok, false_and, exists_false] at h
  | _ :: _ :: _, h =>
    unfold translateNewDate at h
    split at h <;> simp only [bind_ok, pure_bind, reject_ne_ok, false_and, exists_false] at h

/-- `new Map()` and `new Set()`, and `new Map(items)` and `new Set(items)`,
which set or add each value that `items` visits. -/
theorem translateNew_sound {tr : Option Ty → Expr → TM Code} {env : Translate.Env}
    (htr : ∀ exp e ctx c ctx', tr exp e ctx = .ok c ctx' → Sim (N := N) m fs fuel env e c.code)
    {exp : Option Ty} {sp : Span} {callee : String} {typeArgs : List TypeExpr} {args : List Expr}
    {ctx ctx' : Ctx} {c : Code}
    (h : translateNew tr env exp sp callee typeArgs args ctx = .ok c ctx') :
    Sim (N := N) m fs fuel env (.new sp callee typeArgs args) c.code := by
  unfold translateNew at h
  split at h
  · rename_i hc
    obtain rfl : callee = "Date" := by simpa using hc
    split at h
    · exact translateNewDate_sound m fs fuel htr h
    · simp at h
  simp only [ite_state] at h
  split at h
  rotate_left
  · simp at h
  rename_i hcallee
  simp only [pure_bind, ite_state] at h
  split at h
  · simp at h
  rename_i hhas
  try simp only [pure_bind] at h
  have hnone : ∀ ρs : Eval.Env N, Scoped m env ρs → ρs.lookup callee = none :=
    fun ρs hs => hs.none (by simpa using hhas)
  have hc : callee = "Map" ∨ callee = "Set" := by simpa using hcallee
  rcases hc with rfl | rfl
  · simp only [show ("Map" == "Map") = true from rfl, ↓reduceIte] at h
    rcases args with _ | ⟨arg, _ | ⟨_, _⟩⟩
    · simp only [bind_ok] at h
      obtain ⟨type, s₁, -, h⟩ := h
      simp only [pure_ok] at h
      obtain ⟨rfl, -⟩ := h
      intro ρs ρo v _ hs hv
      simp [IR.Expr.eval, IR.Expr.evalList, IR.ExprExt.apply] at hv
      subst hv
      simp [Eval.eval, hnone ρs hs]
    · simp only [bind_ok, orReject_ok] at h
      obtain ⟨declared, s₁, -, items, s₂, hitems, ⟨elem, li⟩, s₃, ⟨hlo, rfl⟩, type, s₄, -, h⟩ := h
      simp only [pure_ok] at h
      obtain ⟨rfl, -⟩ := h
      have hsim := translateRecv_sim m fs fuel (fun _ _ _ hx => htr _ _ _ _ _ hx) hitems
      intro ρs ρo v ha hs hv
      simp only [IR.Expr.eval] at hv
      cases hli : IR.Expr.eval fs fuel ρo li with
      | none => simp [IR.Expr.evalList, hli] at hv
      | some u =>
        simp [IR.Expr.evalList, hli] at hv
        cases u <;> simp [IR.ExprExt.apply] at hv
        rename_i vs
        obtain ⟨es, hes, rfl⟩ := hv
        obtain ⟨va, hva, hit⟩ := loopOver_sim m fs fuel hsim hlo ha hs hli
        simp [Eval.eval, hnone ρs hs, hva, hit, hes]
    · simp at h
  · simp only [show ("Set" == "Map") = false from rfl, ↓reduceIte, Bool.false_eq_true] at h
    rcases args with _ | ⟨arg, _ | ⟨_, _⟩⟩
    · simp only [bind_ok] at h
      obtain ⟨type, s₁, -, h⟩ := h
      simp only [pure_ok] at h
      obtain ⟨rfl, -⟩ := h
      intro ρs ρo v _ hs hv
      simp [IR.Expr.eval, IR.Expr.evalList, IR.ExprExt.apply] at hv
      subst hv
      simp [Eval.eval, hnone ρs hs]
    · simp only [bind_ok, orReject_ok] at h
      obtain ⟨declared, s₁, -, items, s₂, hitems, ⟨elem, li⟩, s₃, ⟨hlo, rfl⟩, type, s₄, -, h⟩ := h
      simp only [pure_ok] at h
      obtain ⟨rfl, -⟩ := h
      have hsim := translateRecv_sim m fs fuel (fun _ _ _ hx => htr _ _ _ _ _ hx) hitems
      intro ρs ρo v ha hs hv
      simp only [IR.Expr.eval] at hv
      cases hli : IR.Expr.eval fs fuel ρo li with
      | none => simp [IR.Expr.evalList, hli] at hv
      | some u =>
        simp [IR.Expr.evalList, hli] at hv
        cases u <;> simp [IR.ExprExt.apply] at hv
        rename_i vs
        obtain ⟨es, hes, rfl⟩ := hv
        obtain ⟨va, hva, hit⟩ := loopOver_sim m fs fuel hsim hlo ha hs hli
        simp [Eval.eval, hnone ρs hs, hva, hit, hes]
    · simp at h

theorem out_numberSameValue {a b : IR.Expr} {ρ : Eval.Env N} {v : Val N}
    (h : IR.Expr.eval fs fuel ρ (.ext .numberSameValue [a, b]) = some v) :
    ∃ x y, IR.Expr.eval fs fuel ρ a = some (.num x) ∧ IR.Expr.eval fs fuel ρ b = some (.num y) ∧
      v = .bool (JSNumber.sameValue x y) := by
  simp only [IR.Expr.eval, IR.Expr.evalList] at h
  cases hx : IR.Expr.eval fs fuel ρ a with
  | none => simp [hx] at h
  | some w =>
    cases hy : IR.Expr.eval fs fuel ρ b with
    | none => simp [hx, hy] at h
    | some u =>
      simp only [hx, hy, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at h
      cases w <;> cases u <;> simp [IR.ExprExt.apply] at h
      exact ⟨_, _, rfl, rfl, h.symm⟩

theorem out_numberOfInt {a : IR.Expr} {ρ : Eval.Env N} {v : Val N}
    (h : IR.Expr.eval fs fuel ρ (.ext .numberOfInt [a]) = some v) :
    ∃ i, IR.Expr.eval fs fuel ρ a = some (.int i) ∧ v = .num (JSNumber.ofInt i) := by
  simp only [IR.Expr.eval, IR.Expr.evalList] at h
  cases hx : IR.Expr.eval fs fuel ρ a with
  | none => simp [hx, IR.ExprExt.apply] at h
  | some w => cases w <;> simp_all [IR.ExprExt.apply]

/-- The interpreter's rule for `Object.is(a, b)`, where no variable hides
`Object`: SameValue of the values of the arguments. -/
theorem eval_objectIs (sp sp' sp'' : Span) (x y : Expr) (ρ : Eval.Env N)
    (hnone : ρ.lookup "Object" = none) :
    Eval.eval m fuel ρ (.call sp (.member sp' (.ident sp'' "Object") "is") [x, y]) =
      (Eval.eval m fuel ρ x).bind fun p => (Eval.eval m fuel ρ y).bind fun q =>
        (Eval.sameValue p q).map .bool := by
  rw [Eval.eval]
  · simp only [hnone, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
    cases Eval.eval m fuel ρ x <;> cases Eval.eval m fuel ρ y <;> simp
    rename_i p q
    cases Eval.sameValue p q <;> rfl
  all_goals simp

/-- Two values that the output compares with `=` are the same by SameValue
when they are equal. -/
theorem sameValue_of_eqVal {p q : Val N} {t : Bool} (h : IR.eqVal p q = some t) :
    Eval.sameValue p q = some t := by
  unfold IR.eqVal at h
  split at h <;> simp_all [Eval.sameValue, Eval.strictEq]

/-- `translateObjectIs` means what the interpreter's rule for `Object.is`
means, when `tr` means what each argument means. Its code is no call. -/
theorem translateObjectIs_sound {tr : Expr → TM Code} {env : Translate.Env}
    (htr : ∀ e ctx c ctx', tr e ctx = .ok c ctx' → Sim (N := N) m fs fuel env e c.code)
    (hO : env.has "Object" = false) {sp sp' sp'' : Span} {args : List Expr}
    {ctx ctx' : Ctx} {c : Code} (h : translateObjectIs tr sp args ctx = .ok c ctx') :
    Sim (N := N) m fs fuel env (.call sp (.member sp' (.ident sp'' "Object") "is") args) c.code ∧
      ∀ ref outs, c.code ≠ .call ref outs := by
  unfold translateObjectIs at h
  match args, h with
  | [x, y], h =>
    simp at h
    obtain ⟨a, s₁, hta, b, s₂, htb, h⟩ := h
    split at h
    · simp at h
      obtain ⟨rfl, -⟩ := h
      refine ⟨fun ρs ρo v ha hs hv => ?_, by intro ref outs hc; cases hc⟩
      obtain ⟨p, q, hp, hq, rfl⟩ := out_numberSameValue fs fuel hv
      rw [eval_value] at hp hq
      rw [eval_objectIs m fuel _ _ _ _ _ _ (hs.none hO), htr _ _ _ _ hta ρs ρo _ ha hs hp,
        htr _ _ _ _ htb ρs ρo _ ha hs hq]
      simp [Eval.sameValue]
    · split at h
      · simp at h
        obtain ⟨rfl, -⟩ := h
        refine ⟨fun ρs ρo v ha hs hv => ?_, by intro ref outs hc; cases hc⟩
        obtain ⟨p, q, t, hp, hq, ht, rfl⟩ := out_eq fs fuel hv
        rw [eval_value] at hp hq
        rw [eval_objectIs m fuel _ _ _ _ _ _ (hs.none hO), htr _ _ _ _ hta ρs ρo _ ha hs hp,
          htr _ _ _ _ htb ρs ρo _ ha hs hq]
        simp [sameValue_of_eqVal ht]
      · simp at h
  | [], h => simp at h
  | [_], h => simp at h
  | _ :: _ :: _ :: _, h => simp at h

/-- `translateNumberCall` means what the interpreter's rule for `Number(b)`
means, when `tr` means what the argument means. Its code is no call. -/
theorem translateNumberCall_sound {tr : Expr → TM Code} {env : Translate.Env}
    (htr : ∀ e ctx c ctx', tr e ctx = .ok c ctx' → Sim (N := N) m fs fuel env e c.code)
    (hN : env.has "Number" = false) {sp sp' : Span} {args : List Expr}
    {ctx ctx' : Ctx} {c : Code} (h : translateNumberCall tr sp args ctx = .ok c ctx') :
    Sim (N := N) m fs fuel env (.call sp (.ident sp' "Number") args) c.code ∧
      ∀ ref outs, c.code ≠ .call ref outs := by
  unfold translateNumberCall at h
  match args, h with
  | [x], h =>
    simp at h
    obtain ⟨a, s₁, hta, h⟩ := h
    split at h
    · simp at h
      obtain ⟨rfl, -⟩ := h
      refine ⟨fun ρs ρo v ha hs hv => ?_, by intro ref outs hc; cases hc⟩
      obtain ⟨i, hi, rfl⟩ := out_numberOfInt fs fuel hv
      rw [eval_value] at hi
      have harg := htr _ _ _ _ hta ρs ρo _ ha hs hi
      rw [eval_call_toOption, Eval.evalCall]
      simp [Eval.evalList, harg, hs.none hN, Eval.numberOf, Except.toOption]
    · simp at h
  | [], h => simp at h
  | _ :: _ :: _, h => simp at h

/-- The interpreter's rule for `Math.f(args)`, where no variable hides `Math`:
the function of `mathCall` on the values of the arguments. -/
theorem eval_math (sp sp' sp'' : Span) (f : String) (args : List Expr) (ρ : Eval.Env N)
    (hnone : ρ.lookup "Math" = none) :
    Eval.eval m fuel ρ (.call sp (.member sp' (.ident sp'' "Math") f) args) =
      (Eval.evalList m fuel ρ args).bind (Eval.mathCall f) := by
  rw [Eval.eval]
  · simp [hnone]
  all_goals simp

/-- `translateMathCall` means what the interpreter's rule for `Math.f(args)`
means, when `tr` means what each argument means, and its code is an
operation of the number model. -/
theorem translateMathCall_sound {tr : Expr → TM Code} {env : Translate.Env}
    (htr : ∀ e ctx c ctx', tr e ctx = .ok c ctx' → Sim (N := N) m fs fuel env e c.code)
    (hM : env.has "Math" = false) {sp sp' sp'' : Span} {f : String} {args : List Expr}
    {ctx ctx' : Ctx} {c : Code} (h : translateMathCall tr sp f args ctx = .ok c ctx') :
    Sim (N := N) m fs fuel env (.call sp (.member sp' (.ident sp'' "Math") f) args) c.code ∧
      ∃ op outs, c.code = .ext op outs := by
  unfold translateMathCall at h
  cases hfn : numberFn? f with
  | some fn =>
    simp only [hfn] at h
    match args, h with
    | [arg], h =>
      simp at h
      obtain ⟨a, s₁, hta, h⟩ := h
      split at h
      · simp at h
        obtain ⟨hcode, -⟩ := h
        refine ⟨fun ρs ρo v ha hs hv => ?_, _, _, by rw [← hcode]⟩
        rw [← hcode] at hv
        obtain ⟨n, hn, rfl⟩ := out_numberFn fs fuel hv
        rw [eval_value] at hn
        have harg := htr _ _ _ _ hta ρs ρo _ ha hs hn
        rw [eval_math m fuel _ _ _ _ _ _ (hs.none hM)]
        unfold numberFn? at hfn
        split at hfn <;> cases hfn <;>
          simp [Eval.evalList, harg, Eval.mathCall, IR.NumberFn.apply]
      · simp at h
    | [], h => simp at h
    | _ :: _ :: _, h => simp at h
  | none =>
    simp only [hfn] at h
    simp at h
    split at h
    · rename_i hf
      simp at h
      obtain ⟨codes, s₁, hcodes, -, hcode⟩ := h
      have hargs := mapM_sim m fs fuel htr args ctx codes s₁ hcodes
      refine ⟨fun ρs ρo v ha hs hv => ?_, _, _, by rw [← hcode]⟩
      rw [← hcode] at hv
      obtain ⟨vs, xs, hvs, hxs, rfl⟩ := out_numberFold fs fuel hv
      rw [eval_math m fuel _ _ _ _ _ _ (hs.none hM), hargs ρs ρo vs ha hs hvs]
      rcases hf with rfl | rfl <;> simp [Eval.mathCall, hxs]
    · simp at h

/-- A call of a function of the program: the output's call means what the
source's call means, and it returns or throws what the source's call returns
or throws (`CallSim`). -/
theorem translateCall_sound {F : Nat} (hc : CallsAgree (N := N) m.program fs fuel)
    (ihE : ∀ env exp e ctx c ctx', translateExpr F env exp e ctx = .ok c ctx' →
      Sim (N := N) m fs fuel env e c.code) :
    ∀ env sp callee args top ctx c ctx', translateCall (F + 1) env sp callee args top ctx = .ok c ctx' →
      Sim (N := N) m fs fuel env (.call sp callee args) c.code ∧
        CallSim (N := N) m fs fuel env callee args c.code := by
  intro env sp callee args top ctx c ctx' h
  simp only [translateCall] at h
  cases callee <;> simp at h
  case ident sp' name =>
    by_cases hN : name = "Number"
    · subst hN
      simp at h
      cases hNb : env.has "Number" <;> simp [hNb] at h
      obtain ⟨hsim, hnc⟩ :=
        translateNumberCall_sound m fs fuel (fun e ctx c ctx' h => ihE _ _ _ _ _ _ h) hNb h
      exact ⟨hsim, fun ref outs' hout => absurd hout (hnc ref outs')⟩
    simp [hN] at h
    split at h
    · simp at h
    · simp at h
      obtain ⟨fn, s₁, ⟨hfind, rfl⟩, h⟩ := h
      split at h
      · simp at h
      · rename_i hlocal
        have hlocal' : env.has name = false := by simpa using hlocal
        try simp only [bind_ok] at h
        obtain ⟨_, s₂, hck, h⟩ := h
        obtain rfl := checkThrowingCall_ok hck
        split at h
        · next hlen =>
          have hle : args.length ≤ fn.params.length := by
            first | exact hlen.1 | (simp at hlen; exact hlen.1)
          -- The arguments, then the checks of their types, which do not
          -- change what the call means.
          simp only [bind_ok] at h
          -- Fixing the type of an `undefined` argument keeps its value.
          obtain ⟨first, s₂, hcodes, _, s₃, -, _, s₄, -, h⟩ := h
          obtain ⟨codes, hcodes', hcode⟩ : ∃ codes : List Code, codes.map Code.value = first.map Code.value ∧
              c.code = .call fn.ref (optArgs (Ty.unifyList [] fn.params (codes.map (·.type))) codes fn.params ++
                List.drop args.length (fn.params.map fun _ => IR.Expr.undefined)) := by
            obtain ⟨_, -, rfl⟩ := map_ok.mp h
            exact ⟨_, fixArgs_value _ _, rfl⟩
          -- What the call returns or throws, from which its value follows.
          have hcall : ∀ (ρs ρo : Eval.Env N) r, Agree ρs ρo → Scoped m env ρs →
              IR.Expr.evalCall fs fuel ρo fn.ref (optArgs (Ty.unifyList [] fn.params (codes.map (·.type)))
                codes fn.params ++ List.drop args.length (fn.params.map fun _ => IR.Expr.undefined)) = some r →
              Eval.evalCall m fuel ρs name args = some r := by
            intro ρs ρo r ha hs hr
            rw [out_evalCall, ← List.map_drop, evalList_append_undefined, evalList_optArgs, hcodes'] at hr
            cases hx : IR.Expr.evalList fs fuel ρo (first.map Code.value) with
            | none => simp [hx] at hr
            | some vs =>
              simp only [hx] at hr
              have hargs := zip_sim_value m fs fuel ?hg args fn.params _ first _ hle hcodes
                ρs ρo vs ha hs hx
              · have hname : fn.name = name := by simpa using List.find?_some hfind
                have hres := hs.2.1 fn (List.mem_of_find?_eq_some hfind)
                rw [hname] at hres
                rw [evalCall_eq (hn := hN) (hl := hs.none hlocal'), hargs]
                simp only [Option.bind_some, hres, callS_append_undefined (hc _ _ _ hr)]
              case hg =>
                intro x t c₀ o c₁ hgo
                intro ρs' ρo' w ha' hs' hw
                rw [eval_value] at hw
                exact ihE _ _ _ _ _ _ hgo ρs' ρo' w ha' hs' hw
          refine ⟨fun ρs ρo v ha hs hv => ?_, fun ref outs hout => ⟨sp', name, rfl, ?_⟩⟩
          · rw [hcode, out_call_toOption, bind_toOption] at hv
            rw [eval_call_toOption, hcall ρs ρo _ ha hs hv]
            rfl
          · rw [hcode] at hout
            injection hout with h1 h2
            subst h1 h2
            exact hcall
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
            refine ⟨fun ρs ρo v ha hs hv => ?_, fun ref outs hout => by rw [← hcode] at hout; cases hout⟩
            rw [← hcode] at hv
            obtain ⟨n, hn, rfl⟩ := out_numberTest fs fuel hv
            rw [eval_value] at hn
            have harg := ihE _ _ _ _ _ _ hta ρs ρo _ ha hs hn
            have hnone := hs.none hN
            unfold numberTest? at hT
            split at hT <;> cases hT <;>
              simp [Eval.eval, hnone, harg, IR.NumberTest.apply]
          · simp at h
        | [], h => simp at h
        | _ :: _ :: _, h => simp at h
      · by_cases hM : oname = "Math"
        · subst hM
          simp [hn] at h
          cases hMa : env.has "Math" <;> simp [hMa] at h
          obtain ⟨hsim, op, outs, hcode⟩ :=
            translateMathCall_sound m fs fuel (fun e ctx c ctx' h => ihE _ _ _ _ _ _ h) hMa h
          exact ⟨hsim, fun ref outs' hout => by rw [hcode] at hout; cases hout⟩
        · by_cases hO : oname = "Object"
          · subst hO
            by_cases hi : test = "is"
            · subst hi
              simp at h
              cases hOb : env.has "Object" <;> simp [hOb] at h
              obtain ⟨hsim, hnc⟩ :=
                translateObjectIs_sound m fs fuel (fun e ctx c ctx' h => ihE _ _ _ _ _ _ h) hOb h
              exact ⟨hsim, fun ref outs' hout => absurd hout (hnc ref outs')⟩
            · simp [hi] at h
          · by_cases hDt : oname = "Date"
            · subst hDt
              by_cases hu : test = "UTC"
              · subst hu
                simp at h
                cases hDb : env.has "Date" <;> simp [hDb] at h
                obtain ⟨hsim, hnc⟩ :=
                  translateDateUtc_sound m fs fuel (fun e ctx c ctx' h => ihE _ _ _ _ _ _ h) hDb h
                exact ⟨hsim, fun ref outs' hout => absurd hout (hnc ref outs')⟩
              · simp [hu] at h
            · simp [hn, hM, hO, hDt] at h
    all_goals simp at h

/-- An object literal of an interface, or of a member of a tagged union. -/
theorem translateObject_sound {F : Nat}
    (ihE : ∀ env exp e ctx c ctx', translateExpr F env exp e ctx = .ok c ctx' →
      Sim (N := N) m fs fuel env e c.code)
    (ihO : ∀ env exp s ps ctx c ctx', translateObject F env exp s ps ctx = .ok c ctx' →
      Sim (N := N) m fs fuel env (.object s ps) c.code)
    {env : Translate.Env} {exp : Option Ty} {sp : Span} {props : List Property} {ctx ctx' : Ctx}
    {c : Code} (h : translateObject (F + 1) env exp sp props ctx = .ok c ctx') :
    Sim (N := N) m fs fuel env (.object sp props) c.code := by
  simp only [translateObject] at h
  simp at h
  obtain ⟨_, _, ⟨rfl, rfl⟩, h⟩ := h
  cases exp with
  | none => simp at h
  | some t =>
    cases t
    case tagged uref tags =>
      -- A member of a tagged union: the structure of the member, which the
      -- evaluator gives as it is.
      simp only [bind_ok, orReject_ok, ite_state] at h
      obtain ⟨union, _, ⟨-, rfl⟩, field, _, ⟨-, rfl⟩, tag, _, ⟨-, rfl⟩, h⟩ := h
      split at h
      · simp only [bind_ok, orReject_ok] at h
        obtain ⟨member, _, ⟨-, rfl⟩, h⟩ := h
        simp only [map_ok] at h
        obtain ⟨inner, hinner, rfl⟩ := h
        intro ρs ρo v ha hs hv
        simp only [IR.Expr.eval] at hv
        exact ihO _ _ _ _ _ _ _ hinner ρs ρo v ha hs hv
      · simp at h
    all_goals try simp at h
    rename_i structName structArgs
    obtain ⟨info, _, ⟨-, rfl⟩, seen, parts, s₂, hfold, h⟩ := h
    have hparts : c.code = .struct parts structName (Ty.leanList structArgs) := by
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
      simp only [IR.Expr.eval, List.nil_append] at hv
      cases hx : IR.Expr.evalFields fs fuel ρo new with
      | none => simp [hx] at hv
      | some fvs =>
        simp [hx] at hv
        subst hv
        -- The properties have values, so the first is not a spread, which
        -- `evalProps` does not read.
        have hev := hsim ρs ρo fvs ha hs hx
        rcases props with _ | ⟨p, ps⟩
        · simp [Eval.eval, hev]
        · cases p with
          | spread _ _ => simp [Eval.evalProps] at hev
          | _ => simp [Eval.eval, hev]
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
      | spread ps v => simp at hg
      | keyValue ps key val =>
        cases key with
        | ident key =>
          by_cases hk : key = "__proto__"
          · subst hk; simp at hg
          simp [hk] at hg
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
              simp [Eval.evalProps, this, hk]
              cases Eval.evalProps m fuel ρs rest <;> rfl
            · simp at hg
        | _ => simp at hg

/-- What a read of a `Record` gives: the property of an object that a string
names. It splits each value on its own, so a new kind of value adds one case,
not one for each other kind. -/
theorem apply_recordGet {r : DeclRef} {keys : List String} {ov kv v : Val N}
    (h : IR.ExprExt.apply (.recordGet r keys) [ov, kv] = some v) :
    ∃ fields k, ov = .obj fields ∧ kv = .str k ∧ Eval.getKey fields k = some v := by
  cases ov <;> simp [IR.ExprExt.apply] at h
  cases kv <;> simp at h
  exact ⟨_, _, rfl, rfl, h⟩

theorem expr_sound (hc : CallsAgree (N := N) m.program fs fuel) (F : Nat) :
    (∀ env exp e ctx c ctx', translateExpr F env exp e ctx = .ok c ctx' →
      Sim (N := N) m fs fuel env e c.code) ∧
    (∀ env exp s es ctx r ctx', translateElements F env exp s es ctx = .ok r ctx' →
      SimList (N := N) m fs fuel env es r.1) ∧
    (∀ env exp s es ctx c ctx', translateArray F env exp s es ctx = .ok c ctx' →
      Sim (N := N) m fs fuel env (.array s es) c.code) ∧
    (∀ env s callee args top ctx c ctx', translateCall F env s callee args top ctx = .ok c ctx' →
      Sim (N := N) m fs fuel env (.call s callee args) c.code ∧
        CallSim (N := N) m fs fuel env callee args c.code) ∧
    (∀ env exp s ps ctx c ctx', translateObject F env exp s ps ctx = .ok c ctx' →
      Sim (N := N) m fs fuel env (.object s ps) c.code) ∧
    (∀ env s op l r ctx c ctx', translateBinary F env s op l r ctx = .ok c ctx' →
      Sim (N := N) m fs fuel env (.binary s op l r) c.code) ∧
    (∀ env exp s recv method args ctx c ctx', translateArrayMethod F env exp s recv method args ctx = .ok c ctx' →
      ∀ sp name, listMethod? name = some method →
        Sim (N := N) m fs fuel env (.call s (.member sp recv name) args) c.code) ∧
    (∀ env exp s recv args ctx c ctx', translateReduce F env exp s recv args ctx = .ok c ctx' →
      ∀ sp, Sim (N := N) m fs fuel env (.call s (.member sp recv "reduce") args) c.code) ∧
    (∀ env s recv method args ctx c ctx', translateSort F env s recv method args ctx = .ok c ctx' →
      method = "toSorted" ∨ method = "sort" →
      ∀ sp, Sim (N := N) m fs fuel env (.call s (.member sp recv method) args) c.code) ∧
    (∀ env s recv op args ctx c ctx', translateMapMethod F env s recv op args ctx = .ok c ctx' →
      ∀ sp name, mapMethodOf (.member sp recv name) = some (recv, op) →
        Sim (N := N) m fs fuel env (.call s (.member sp recv name) args) c.code) ∧
    (∀ env s recv method args ctx c ctx', translateArrayCall F env s recv method args ctx = .ok c ctx' →
      ∀ sp, recv.namesNumber = false →
        Sim (N := N) m fs fuel env (.call s (.member sp recv method) args) c.code) ∧
    (∀ env s o elem key ctx c ctx', translateArrayIndex F env s o elem key ctx = .ok c ctx' →
      ∀ sp obj, Sim (N := N) m fs fuel env obj o.value →
        Sim (N := N) m fs fuel env (.index sp obj key) c.code) ∧
    (∀ env s base rest ctx c ctx', translateSpread F env s base rest ctx = .ok c ctx' →
      ∀ sp, Sim (N := N) m fs fuel env (.object s (.spread sp base :: rest)) c.code) ∧
    (∀ env exp e ctx c ctx', translateExprCore F env exp e ctx = .ok c ctx' →
      Sim (N := N) m fs fuel env e c.code) := by
  induction F with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;>
      simp_all [translateExpr, translateElements, translateArray, translateCall, translateObject,
        translateBinary, translateArrayMethod, translateReduce, translateSort, translateMapMethod, translateArrayCall, translateArrayIndex, translateSpread,
        translateExprCore]
  | succ F ih =>
    obtain ⟨ihE, ihL, ihA, ihC, ihO, ihB, ihM, ihR, ihT, ihMM, ihK, ihI, ihS, ihX⟩ := ih
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    -- The core first, then the step that makes a value a member of a union.
    rotate_right
    · intro env exp e ctx c ctx' h
      cases e with
      | paren sp inner =>
        simp only [translateExprCore] at h
        intro ρs ρo v ha hs hv
        rw [Eval.eval]
        exact ihX _ _ _ _ _ _ h ρs ρo v ha hs hv
      | asConst sp inner =>
        simp only [translateExprCore] at h
        intro ρs ρo v ha hs hv
        rw [Eval.eval]
        exact ihX _ _ _ _ _ _ h ρs ρo v ha hs hv
      | satisfies sp inner type =>
        simp only [translateExprCore, bind_ok] at h
        obtain ⟨t, s₁, -, c', s₂, hc', h⟩ := h
        simp only [ite_state] at h
        split at h
        · obtain ⟨rfl, -⟩ := h
          intro ρs ρo v ha hs hv
          rw [Eval.eval]
          rcases firstFitting_ok hc' with hx | hy
          · exact ihX _ _ _ _ _ _ hx ρs ρo v ha hs hv
          · exact ihX _ _ _ _ _ _ hy ρs ρo v ha hs hv
        · simp at h
      | bigint sp text =>
        simp only [translateExprCore] at h
        simp at h
        obtain ⟨n, ⟨hv, -⟩, rfl⟩ := h
        intro ρs ρo v _ _ hv'
        simp [IR.Expr.eval] at hv'
        subst hv'
        simp [Eval.eval]; simpa [bigintValue?] using hv
      | number sp text =>
        simp only [translateExprCore] at h
        simp at h
        obtain ⟨n, ⟨hv, -⟩, rfl⟩ := h
        intro ρs ρo v _ _ hv'
        simp [IR.Expr.eval, IR.Expr.evalList, IR.ExprExt.apply] at hv'
        subst hv'
        simp [Eval.eval]; exact ⟨n, by simpa [safeIntegerValue?] using hv, rfl⟩
      | null sp =>
        simp [translateExprCore] at h
        obtain ⟨rfl, -⟩ := h
        intro ρs ρo v _ _ hv'
        simp [IR.Expr.eval] at hv'
        subst hv'; simp [Eval.eval]
      | bool sp b =>
        simp [translateExprCore] at h
        obtain ⟨rfl, -⟩ := h
        intro ρs ρo v _ _ hv'
        simp [IR.Expr.eval] at hv'
        subst hv'; simp [Eval.eval]
      | string sp str =>
        -- A string, or the constructor of a literal union for it: either is
        -- the string.
        have hcode : ∀ ρ : Eval.Env N, IR.Expr.eval fs fuel ρ c.code = some (.str str) := by
          intro ρ
          simp only [translateExprCore] at h
          split at h
          all_goals simp only [bind_ok, get_ok, orReject_ok, ite_state, pure_ok] at h
          all_goals first
            | (obtain ⟨rfl, -⟩ := h; simp [IR.Expr.eval])
            | (obtain ⟨_, _, ⟨rfl, rfl⟩, _, _, ⟨-, rfl⟩, h⟩ := h
               split at h
               · simp at h
               simp only [pure_bind] at h
               split at h
               · simp at h
                 obtain ⟨rfl, -⟩ := h
                 simp [IR.Expr.eval]
               · simp at h)
            | (split at h
               · obtain ⟨rfl, -⟩ := h
                 simp [IR.Expr.eval]
               · simp at h)
        intro ρs ρo v _ _ hv'
        rw [hcode] at hv'
        simp at hv'
        subst hv'; simp [Eval.eval]
      | ident sp name =>
        simp only [translateExprCore] at h
        intro ρs ρo v ha hs hv'
        cases hl : env.lookup name with
        | none =>
          simp only [hl] at h
          have hnone : ρs.lookup name = none := hs.none (by simp [Translate.Env.has, hl])
          split at h
          · -- `undefined`, where an optional value is expected.
            rename_i hu
            have hu' : name = "undefined" := by simpa using hu
            subst hu'
            split at h
            · simp only [pure_ok] at h
              obtain ⟨rfl, -⟩ := h
              simp [IR.Expr.eval, IR.Expr.evalList, IR.ExprExt.apply] at hv'
              subst hv'
              simp [Eval.eval, hnone]
            · simp at h
          cases hk : numberConstant? name with
          | none => simp [hk] at h
          | some k =>
            simp [hk] at h
            obtain ⟨rfl, -⟩ := h
            simp [IR.Expr.eval, IR.Expr.evalList, IR.ExprExt.apply] at hv'
            subst hv'
            unfold numberConstant? at hk
            split at hk
            · cases hk; simp only [Eval.eval, hnone]; simp [IR.NumberConstant.value]
            · cases hk; simp only [Eval.eval, hnone]; simp [IR.NumberConstant.value]
            · cases hk
        | some l =>
          simp only [hl] at h
          -- A local function may only be called.
          split at h
          · simp at h
          simp at h
          obtain ⟨_, _, ⟨rfl, rfl⟩, h⟩ := h
          have hc : c.code = .var name := by
            split at h
            · simp at h
            · simp at h
              obtain ⟨_, _, ⟨rfl, rfl⟩, h⟩ := h
              split at h
              · simp at h
              · simp at h; rw [← h.1]
          rw [hc] at hv'
          simp only [IR.Expr.eval] at hv'
          rw [← ha name] at hv'
          simp only [Eval.eval, hv']
      | member sp obj name => exact translateMember_sound m fs fuel ihE h
      | optMember sp obj name =>
        simp only [translateExprCore, bind_ok] at h
        obtain ⟨o, s₁, ho, ⟨bind, ty⟩, s₂, -, h⟩ := h
        simp only [pure_ok] at h
        obtain ⟨rfl, -⟩ := h
        intro ρs ρo v ha hs hv'
        simp only [IR.Expr.eval, IR.Expr.evalList] at hv'
        cases hobj : IR.Expr.eval fs fuel ρo o.code with
        | none => simp [hobj] at hv'
        | some ov =>
          have := ihE _ _ _ _ _ _ ho ρs ρo ov ha hs hobj
          simp only [hobj] at hv'
          simp only [Eval.eval, this, Option.bind_eq_bind, Option.bind_some]
          cases ov <;> simp only [IR.ExprExt.apply] at hv' <;> first | exact hv' | simp at hv'
      | index sp obj key =>
        simp only [translateExprCore, bind_ok] at h
        obtain ⟨o, s₁, ho, h⟩ := h
        cases hot : o.type.tupleElems? with
        | some tys =>
          -- `t[i]`: the element `i` of the tuple, which the array has at `i`.
          simp only [hot] at h
          cases key
          case number sp' text =>
            simp only [bind_ok, orReject_ok] at h
            obtain ⟨i, s₂, ⟨hi, rfl⟩, h⟩ := h
            cases hti : tys[i.toNat]? with
            | none => simp [hti] at h
            | some ty =>
              simp only [hti] at h
              split at h
              · next hpos =>
                simp at h
                obtain ⟨rfl, -⟩ := h
                intro ρs ρo v ha hs hv
                simp only [IR.Expr.eval] at hv
                cases hx : IR.Expr.eval fs fuel ρo o.code with
                | none => simp [hx] at hv
                | some w =>
                  cases w
                  case list items =>
                    simp [hx] at hv
                    have hobj := ihE _ _ _ _ _ _ ho ρs ρo _ ha hs hx
                    have hlit : Eval.numberLiteral text = some i := hi
                    simp only [Eval.eval, hobj, Eval.numberText?, hlit, Option.bind_eq_bind, Option.bind_some,
                      Eval.elementAt] at hpos ⊢
                    simp [hpos, hv]
                  all_goals simp [hx] at hv
              · simp at h
          all_goals simp at h
        | none =>
        simp only [hot] at h
        cases hel : o.type.element? with
        | some elem =>
          -- `xs[i]` on an array: the element at the index, as the spec reads it.
          simp only [hel] at h
          exact ihI _ _ _ _ _ _ _ _ h sp obj fun ρs ρo w ha hs hw =>
            ihE _ _ _ _ _ _ ho ρs ρo w ha hs (by rwa [eval_value] at hw)
        | none =>
        -- `r[k]` on a `Record<K, V>`: the evaluator reads the property that
        -- the string names, as the spec does.
        simp only [hel] at h
        simp at h
        obtain ⟨_, _, ⟨rfl, rfl⟩, keyRef, keys, ty, _, ⟨-, rfl⟩, k, s₃, hk, h⟩ := h
        split at h
        · simp only [pure_ok] at h
          obtain ⟨rfl, -⟩ := h
          intro ρs ρo v ha hs hv'
          simp only [IR.Expr.eval, IR.Expr.evalList, eval_value] at hv'
          cases hobj : IR.Expr.eval fs fuel ρo o.code with
          | none => simp [hobj] at hv'
          | some ov =>
            cases hkey : IR.Expr.eval fs fuel ρo k.code with
            | none => simp [hobj, hkey] at hv'
            | some kv =>
              have h1 := ihE _ _ _ _ _ _ ho ρs ρo ov ha hs hobj
              have h2 := ihE _ _ _ _ _ _ hk ρs ρo kv ha hs hkey
              simp only [hobj, hkey, Option.bind_eq_bind, Option.bind_some, pure_bind] at hv'
              simp only [Eval.eval, h1, h2, Option.bind_eq_bind, Option.bind_some]
              obtain ⟨fields, k, rfl, rfl, hget⟩ := apply_recordGet hv'
              simp_all
        · simp at h
      | unary sp op arg =>
        simp only [translateExprCore] at h
        intro ρs ρo v ha hs hv'
        cases op with
        | not =>
          simp +decide at h
          obtain ⟨a, s₁, hta, h⟩ := h
          split at h
          · simp at h
            obtain ⟨hcode, -⟩ := h
            rw [← hcode] at hv'
            have key : ∃ b, IR.Expr.eval fs fuel ρo a.code = some (.bool b) ∧ v = .bool !b := by
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
            simp [IR.Expr.eval, IR.Expr.evalList, IR.ExprExt.apply, IR.NumberConstant.value] at hv'
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
        | bitNot =>
          simp +decide at h
          obtain ⟨a, s₁, hta, h⟩ := h
          split at h
          · simp at h
            obtain ⟨rfl, -⟩ := h
            obtain ⟨n, hn, rfl⟩ := out_numberFn fs fuel hv'
            rw [eval_value] at hn
            have := ihE _ _ _ _ _ _ hta ρs ρo _ ha hs hn
            simp [Eval.eval, this, IR.NumberFn.apply]
          split at h
          · simp at h
            obtain ⟨⟨-, -⟩, rfl⟩ := h
            obtain ⟨i, hi, rfl⟩ := out_bigintNot fs fuel hv'
            rw [eval_value] at hi
            have := ihE _ _ _ _ _ _ hta ρs ρo _ ha hs hi
            simp [Eval.eval, this]
          · simp at h
        | _ => simp +decide at h
      | binary sp op l r =>
        simp only [translateExprCore] at h
        exact ihB _ _ _ _ _ _ _ _ h
      | call sp callee args =>
        simp only [translateExprCore] at h
        cases hred : reduceOf callee with
        | some recv =>
          simp only [hred] at h
          unfold reduceOf at hred
          split at hred
          · rename_i sp' recv'
            cases hred
            exact ihR _ _ _ _ _ _ _ _ h sp'
          · simp at hred
        | none =>
        simp only [hred] at h
        cases hso : sortOf callee with
        | some rm =>
          obtain ⟨recv, method⟩ := rm
          simp only [hso] at h
          obtain ⟨sp', rfl, hmethod⟩ := sortOf_some hso
          exact ihT _ _ _ _ _ _ _ _ h hmethod sp'
        | none =>
        simp only [hso] at h
        cases hm : arrayMethodOf callee with
        | some rm =>
          obtain ⟨recv, method⟩ := rm
          simp only [hm] at h
          unfold arrayMethodOf at hm
          split at hm
          · rename_i sp' recv' name
            cases hl : listMethod? name with
            | none => simp [hl] at hm
            | some lm =>
              simp [hl] at hm
              obtain ⟨rfl, rfl⟩ := hm
              exact ihM _ _ _ _ _ _ _ _ _ h sp' name hl
          · simp at hm
        | none =>
          simp only [hm] at h
          cases hmm : mapMethodOf callee with
          | some ro =>
            obtain ⟨recv, op⟩ := ro
            simp only [hmm] at h
            obtain ⟨sp', name, rfl⟩ : ∃ sp' name, callee = .member sp' recv name := by
              cases callee <;> simp [mapMethodOf] at hmm
              rename_i sp' o name
              obtain ⟨rfl, -⟩ := (mapMethodOf_some hmm)
              exact ⟨_, _, rfl⟩
            exact ihMM _ _ _ _ _ _ _ _ h sp' name hmm
          | none =>
            simp only [hmm] at h
            cases hk : arrayCallOf callee with
            | some rk =>
              obtain ⟨recv, method⟩ := rk
              simp only [hk] at h
              unfold arrayCallOf at hk
              split at hk
              · rename_i sp' recv' name
                split at hk
                · simp at hk
                · rename_i hn
                  simp only [Option.some.injEq, Prod.mk.injEq] at hk
                  obtain ⟨rfl, rfl⟩ := hk
                  exact ihK _ _ _ _ _ _ _ _ h sp' (by simpa using hn)
              · simp at hk
            | none =>
              simp only [hk] at h
              exact (ihC _ _ _ _ _ _ _ _ h).1
      | object sp props =>
        simp only [translateExprCore] at h
        cases hsp : spreadOf props with
        | some br =>
          obtain ⟨base, rest⟩ := br
          simp only [hsp] at h
          obtain ⟨sp', rfl⟩ := spreadOf_some hsp
          exact ihS _ _ _ _ _ _ _ h sp'
        | none =>
          simp only [hsp] at h
          exact ihO _ _ _ _ _ _ _ h
      | array sp elems =>
        simp only [translateExprCore] at h
        cases hexp : exp with
        | none => rw [hexp] at h; exact ihA _ _ _ _ _ _ _ h
        | some t =>
          rw [hexp] at h
          cases t
          case tuple tys =>
            -- A tuple: the list of its elements, as the array literal is.
            simp only at h
            split at h
            · next hlen =>
              simp only [bind_ok, pure_ok] at h
              obtain ⟨_, _, ⟨-, rfl⟩, codes, s₁, hcodes, hcode, -⟩ := h
              intro ρs ρo v ha hs hv
              rw [← hcode] at hv
              simp only [IR.Expr.eval] at hv
              cases hx : IR.Expr.evalList fs fuel ρo (codes.map Code.value) with
              | none => simp [hx] at hv
              | some vs =>
                simp [hx] at hv
                subst hv
                have hel := zip_sim_value m fs fuel ?hg elems tys _ codes _ (Nat.le_of_eq (by simpa using hlen)) hcodes
                  ρs ρo vs ha hs hx
                · simp [Eval.eval, evalElems_of_evalList m fuel hel]
                case hg =>
                  intro x t c₀ o c₁ hgo
                  simp only [bind_ok] at hgo
                  obtain ⟨a, s₂, hta, hgo⟩ := hgo
                  split at hgo
                  · simp at hgo
                    obtain ⟨rfl, -⟩ := hgo
                    intro ρs' ρo' w ha' hs' hw
                    rw [eval_value] at hw
                    exact ihE _ _ _ _ _ _ hta ρs' ρo' w ha' hs' hw
                  · simp at hgo
            · simp at h
          all_goals exact ihA _ _ _ _ _ _ _ h
      | cond sp test ifTrue ifFalse =>
        simp only [translateExprCore] at h
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
      | new sp callee typeArgs args =>
        simp only [translateExprCore] at h
        exact translateNew_sound m fs fuel (fun _ _ _ _ _ hx => ihE _ _ _ _ _ _ hx) h
      | _ => simp [translateExprCore] at h
    · intro env exp e ctx c ctx' h
      simp only [translateExpr, bind_ok, pure_ok] at h
      obtain ⟨c₀, s₁, h₀, rfl, -⟩ := h
      intro ρs ρo v ha hs hv
      rw [eval_into] at hv
      exact ihX _ _ _ _ _ _ h₀ ρs ρo v ha hs hv
    · intro env exp sp es ctx r ctx' h
      simp only [translateElements] at h
      simp at h
      obtain ⟨codes, s₁, hcodes, elem, s₂, -, -, hr⟩ := h
      rw [← hr]
      exact mapM_sim m fs fuel (fun e ctx c ctx' h => ihE _ _ _ _ _ _ h) es ctx codes s₁ hcodes
    · intro env exp sp es ctx c ctx' h
      simp only [translateArray, ite_state] at h
      split at h
      · exact translateSpreadArray_sound m fs fuel (fun _ _ _ _ _ hx => ihE _ _ _ _ _ _ hx) h
      simp at h
      obtain ⟨values, elem, hel, hcode⟩ := h
      intro ρs ρo v ha hs hv
      rw [← hcode] at hv
      simp only [IR.Expr.eval] at hv
      cases hx : IR.Expr.evalList fs fuel ρo values with
      | none => simp [hx] at hv
      | some xs =>
        simp [hx] at hv
        subst hv
        have := ihL _ _ _ _ _ _ _ hel ρs ρo xs ha hs hx
        simp [Eval.eval, evalElems_of_evalList m fuel this]
    · exact translateCall_sound m fs fuel hc ihE
    · intro env exp sp props ctx c ctx' h
      exact translateObject_sound m fs fuel ihE ihO h
    · exact translateBinary_sound m fs fuel ihE
    · intro env exp s recv method args ctx c ctx' h sp name hname
      exact translateArrayMethod_sound m fs fuel ihE h hname
    · intro env exp s recv args ctx c ctx' h sp
      exact translateReduce_sound m fs fuel ihE h
    · intro env s recv method args ctx c ctx' h hmethod sp
      exact translateSort_sound m fs fuel ihE h hmethod
    · intro env s recv op args ctx c ctx' h sp name hname
      exact translateMapMethod_sound m fs fuel ihE h hname
    · intro env s recv method args ctx c ctx' h sp hr
      exact translateArrayCall_sound m fs fuel ihE h hr
    · intro env s o elem key ctx c ctx' h sp obj hobj
      exact translateArrayIndex_sound m fs fuel ihE h hobj
    · intro env s base rest ctx c ctx' h sp
      exact translateSpread_sound m fs fuel ihE h

end tolean.TypeScript.Proof
