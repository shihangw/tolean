import tolean.Go.Translate.Pure
import tolean.Go.IR.Eval

/-!
The translation of an expression means what the expression means.

`expr_sound` states it for `translateExpr`: when the translator gives code
for an expression, and the code evaluates to a value in the IR's evaluator,
the interpreter gives the same value for the expression, unless a divisor of
the code is zero. Then the interpreter panics. The code divides without a
panic, as Lean does, and the statement that holds the expression tests the
divisors first (`Pure.guarded`). The two
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
open tolean.Core (Res)

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
def callS (p : Eval.Program) (fuel : Nat) (f : String) (vs : List Val) : Res Val Val :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match p.funcs.lookup f with
    | none => none
    | some (params, body) =>
      if params.length != vs.length then none
      else match Eval.execStmt p fuel (params.zip vs).reverse body with
        | some (.ret v) => .ok v
        | some (.panic x) => .fail x
        | _ => none

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
    | _ => none

/-- A call of the function `ref` of the output, as `Body.bind` runs it: `.ok`
of the value it returns, or `.error` of its panic. -/
def callR (fs : Funcs) (fuel : Nat) (ref : DeclRef) (vs : List Val) : Option (Except Val Val) :=
  match fuel with
  | 0 => none
  | fuel + 1 => do
    let (params, body) ← fs.lookup ref
    if params.length != vs.length then none
    match ← IR.Body.exec fs fuel (params.zip vs).reverse body with
    | .ret v => some (.ok v)
    | .panic x => some (.error x)
    | .normal _ => none

/-- Each call of the output that returns a value or panics is a call that
returns the same value or panics the same way in the interpreter. -/
def CallsAgree (p : Eval.Program) (fs : Funcs) (fuel : Nat) : Prop :=
  ∀ f vs r, callR fs fuel ⟨"", f⟩ vs = some r → callS p fuel f vs = some r

theorem callR_of_callO {fs : Funcs} {fuel : Nat} {ref : DeclRef} {vs : List Val} {v : Val}
    (h : callO fs fuel ref vs = some v) : callR fs fuel ref vs = some (.ok v) := by
  cases fuel with
  | zero => simp [callO] at h
  | succ fuel =>
    simp only [callO] at h
    simp only [callR]
    cases hl : fs.lookup ref with
    | none => simp [hl] at h
    | some x =>
      obtain ⟨ps, b⟩ := x
      by_cases hlen : ps.length = vs.length
      · cases hex : IR.Body.exec fs fuel (ps.zip vs).reverse b with
        | none => simp [hl, hlen, hex] at h
        | some o => cases o <;> simp [hl, hlen, hex] at h ⊢; exact h
      · simp [hl, hlen] at h

theorem eval_call (p : Eval.Program) (fuel : Nat) (ρ : Eval.Env) (sp sp' : Span) (f : String)
    (args : List Expr) :
    Eval.eval p fuel ρ (.call sp (.ident sp' f) args false) =
      if (ρ.lookup f).isSome then none
      else (Eval.evalList p fuel ρ args).andThen (callS p fuel f) := by
  rw [Eval.eval]
  split
  · rfl
  · congr 1

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

theorem out_division {op : tolean.IR.Division} {a b : IR.Expr}
    (h : IR.Expr.eval fs fuel ρ (.division op a b) = some v) :
    ∃ x y, IR.Expr.eval fs fuel ρ a = some (.int x) ∧ IR.Expr.eval fs fuel ρ b = some (.int y) ∧
      v = .int (op.apply x y) := by
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

/-! ### Divisors -/

/-- Each value is an integer, as each divisor of translated code is. -/
def AllInt (ds : List Val) : Prop := ∀ d ∈ ds, ∃ i, d = .int i

/-- What the interpreter gives for an expression whose code has the value
`v`, when the divisors of the code have the values `ds`: a panic when one of
them is zero, and `v` otherwise. -/
def outcome {α : Type} (ds : List Val) (v : α) : Except Val α :=
  if Val.int 0 ∈ ds then .error Eval.divideByZero else .ok v

theorem allInt_nil : AllInt [] := by simp [AllInt]

theorem allInt_append {a b : List Val} (ha : AllInt a) (hb : AllInt b) : AllInt (a ++ b) := by
  intro d hd
  rcases List.mem_append.mp hd with hd | hd
  · exact ha d hd
  · exact hb d hd

theorem allInt_int (i : Int) : AllInt [.int i] := by simp [AllInt]

theorem outcome_nil {α : Type} (v : α) : outcome [] v = .ok v := by simp [outcome]

theorem andThen_outcome {α β : Type} (ds : List Val) (a : α) (f : α → Res Val β) :
    Res.andThen (some (outcome ds a)) f =
      if Val.int 0 ∈ ds then some (.error Eval.divideByZero) else f a := by
  unfold outcome
  split <;> rfl

theorem outcome_some {α : Type} (ds : List Val) (v : α) :
    (if Val.int 0 ∈ ds then some (.error Eval.divideByZero) else some (.ok v)) =
      some (outcome ds v) := by
  unfold outcome
  split <;> rfl

theorem evalList_append {ρ : Eval.Env} :
    ∀ {a b : List IR.Expr} {da db : List Val}, IR.Expr.evalList fs fuel ρ a = some da →
      IR.Expr.evalList fs fuel ρ b = some db → IR.Expr.evalList fs fuel ρ (a ++ b) = some (da ++ db)
  | [], b, da, db, ha, hb => by
    simp only [IR.Expr.evalList, Option.some.injEq] at ha
    subst ha
    simpa using hb
  | e :: es, b, da, db, ha, hb => by
    simp only [IR.Expr.evalList] at ha
    cases he : IR.Expr.eval fs fuel ρ e with
    | none => simp [he] at ha
    | some w =>
      cases hes : IR.Expr.evalList fs fuel ρ es with
      | none => simp [he, hes] at ha
      | some ws =>
        simp only [he, hes, Option.pure_def, Option.bind_eq_bind, Option.bind_some,
          Option.some.injEq] at ha
        subst ha
        simp [IR.Expr.evalList, he, evalList_append hes hb]

theorem evalList_single {ρ : Eval.Env} {d : IR.Expr} {w : Val}
    (h : IR.Expr.eval fs fuel ρ d = some w) : IR.Expr.evalList fs fuel ρ [d] = some [w] := by
  simp [IR.Expr.evalList, h]

theorem evalList_nil {ρ : Eval.Env} : IR.Expr.evalList fs fuel ρ [] = some [] := by
  simp [IR.Expr.evalList]

/-- The divisor that the output tests, when it is not a literal other than
zero. -/
theorem tested_eval {ρ : Eval.Env} {b : IR.Expr} {y : Int}
    (hy : IR.Expr.eval fs fuel ρ b = some (.int y)) :
    ∃ ks, IR.Expr.evalList fs fuel ρ (tested b) = some ks ∧ AllInt ks ∧ (Val.int 0 ∈ ks ↔ y = 0) := by
  unfold tested
  split
  · next n =>
    simp only [IR.Expr.eval, Option.some.injEq, Val.int.injEq] at hy
    subst hy
    split
    · next h0 => exact ⟨[.int n], evalList_single (by simp [IR.Expr.eval]), allInt_int n, by simp [h0]⟩
    · next h0 => exact ⟨[], evalList_nil, allInt_nil, by simp [h0]⟩
  · exact ⟨[.int y], evalList_single hy, allInt_int y, by simp [eq_comm]⟩

/-- The divisors of the code of a binary operator, from those of its
operands. -/
theorem divisors_pair (ds : List Val) {ρ : Eval.Env} {a b : IR.Expr} {da db : List Val}
    (ha : IR.Expr.evalList fs fuel ρ (divisors a) = some da) (hia : AllInt da)
    (hb : IR.Expr.evalList fs fuel ρ (divisors b) = some db) (hib : AllInt db)
    (hds : ds = da ++ db) :
    IR.Expr.evalList fs fuel ρ (divisors a ++ divisors b) = some ds ∧ AllInt ds := by
  subst hds
  exact ⟨evalList_append ha hb, allInt_append hia hib⟩

/-! ### Operators -/

/-- What the interpreter gives for `l op r`, from what it gives for `l` and
`r`. `&&` and `||` look at `r` only when `l` does not decide. -/
def binaryRes (o : BinOp) (x y : Res Val Val) : Res Val Val :=
  match o with
  | .land =>
    x.andThen fun
      | .bool true => y.andThen fun
        | .bool b => .ok (.bool b)
        | _ => none
      | .bool false => .ok (.bool false)
      | _ => none
  | .lor =>
    x.andThen fun
      | .bool true => .ok (.bool true)
      | .bool false => y.andThen fun
        | .bool b => .ok (.bool b)
        | _ => none
      | _ => none
  | o => x.andThen fun a => y.andThen fun b => Eval.operate o a b

theorem eval_binary {p : Eval.Program} {ρ : Eval.Env} {sp : Span} {op : String} {o : BinOp}
    {l r : Expr} (ho : BinOp.ofString? op = some o) :
    Eval.eval p fuel ρ (.binary sp op l r) =
      binaryRes o (Eval.eval p fuel ρ l) (Eval.eval p fuel ρ r) := by
  rw [Eval.eval, ho]
  cases o <;> rfl

/-- Every operator but `&&` and `||` evaluates both operands, then applies
`operate`. -/
theorem binaryRes_strict {o : BinOp} (hl : o ≠ .land) (hr : o ≠ .lor) (x y : Res Val Val) :
    binaryRes o x y = x.andThen fun a => y.andThen fun b => Eval.operate o a b := by
  cases o <;> first | rfl | exact absurd rfl hl | exact absurd rfl hr

theorem operate_binary {o : BinOp} (hq : o ≠ .quo) (hr : o ≠ .rem) (a b : Val) :
    Eval.operate o a b = Res.lift (Eval.binary o a b) := by
  cases o <;> first | exact absurd rfl hq | exact absurd rfl hr | (cases a <;> cases b <;> rfl)

variable {sp : Span} {a b c : IR.Expr} {ta tb t : Ty}

/-- The conclusion of `translateBinary_out`: once the operands' divisors have
values, so do the result's, and the interpreter's `binaryRes` gives what the
result's code gives, or the panic. -/
def BinaryOut (fs : Funcs) (fuel : Nat) (ρ : Eval.Env) (o : BinOp) (a b c : IR.Expr)
    (va vb v : Val) : Prop :=
  ∀ da db, IR.Expr.evalList fs fuel ρ (divisors a) = some da → AllInt da →
    IR.Expr.evalList fs fuel ρ (divisors b) = some db → AllInt db →
    ∃ ds, IR.Expr.evalList fs fuel ρ (divisors c) = some ds ∧ AllInt ds ∧
      binaryRes o (some (outcome da va)) (some (outcome db vb)) = some (outcome ds v)

/-- A strict operator whose code divides by nothing new and whose value is
what `binary` gives. -/
theorem binaryOut_plain {o : BinOp} (hl : o ≠ .land) (hr : o ≠ .lor) (hq : o ≠ .quo)
    (hm : o ≠ .rem) {va vb : Val} (hbin : Eval.binary o va vb = some v)
    (hdiv : divisors c = divisors a ++ divisors b) :
    BinaryOut fs fuel ρ o a b c va vb v := by
  intro da db ha hia hb hib
  refine ⟨da ++ db, by rw [hdiv]; exact evalList_append ha hb, allInt_append hia hib, ?_⟩
  rw [binaryRes_strict hl hr, andThen_outcome]
  simp only [andThen_outcome, operate_binary hq hm, hbin, Res.lift_some]
  unfold outcome
  by_cases h1 : Val.int 0 ∈ da <;> by_cases h2 : Val.int 0 ∈ db <;> simp [h1, h2]

theorem arith_out {op : tolean.IR.IntOp} (h : arith sp op a ta b tb = .ok (c, t))
    (hv : IR.Expr.eval fs fuel ρ c = some v) :
    ∃ x y, IR.Expr.eval fs fuel ρ a = some (.int x) ∧ IR.Expr.eval fs fuel ρ b = some (.int y) ∧
      v = .int (wrap64 (op.apply x y)) ∧ divisors c = divisors a ++ divisors b := by
  unfold arith at h
  split at h
  · split at h
    · simp only [pure_ok, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      obtain ⟨i, hi, rfl⟩ := out_wrap64 hv
      obtain ⟨x, y, hx, hy, hxy⟩ := out_intOp hi
      cases hxy
      exact ⟨x, y, hx, hy, rfl, by simp [divisors, divisors.divisorsList]⟩
    · exact absurd h reject_ne_ok
  · exact absurd h reject_ne_ok

theorem compare_out {op : tolean.IR.Order} (h : Pure.compare sp op a ta b tb = .ok (c, t))
    (hv : IR.Expr.eval fs fuel ρ c = some v) :
    ∃ x y, IR.Expr.eval fs fuel ρ a = some (.int x) ∧ IR.Expr.eval fs fuel ρ b = some (.int y) ∧
      v = .bool (op.apply x y) ∧ divisors c = divisors a ++ divisors b := by
  unfold Pure.compare at h
  split at h
  · split at h
    · simp only [pure_ok, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      rw [out_decide] at hv
      obtain ⟨x, y, hx, hy, rfl⟩ := out_order hv
      exact ⟨x, y, hx, hy, rfl, by simp [divisors]⟩
    · exact absurd h reject_ne_ok
  · exact absurd h reject_ne_ok

/-- `a / b` and `a % b`: the code divides by `b` too, and the interpreter
panics when `b` is zero. -/
theorem divide_out {op : tolean.IR.Division} {o : BinOp}
    (ho : o = (match op with | .tdiv => .quo | .tmod => .rem))
    (h : divide sp op a ta b tb = .ok (c, t)) (hv : IR.Expr.eval fs fuel ρ c = some v) :
    ∃ va vb, IR.Expr.eval fs fuel ρ a = some va ∧ IR.Expr.eval fs fuel ρ b = some vb ∧
      BinaryOut fs fuel ρ o a b c va vb v := by
  unfold divide at h
  split at h
  · split at h
    · exact absurd h reject_ne_ok
    · split at h
      · exact absurd h reject_ne_ok
      · cases op with
        | tdiv =>
          simp only [pure_ok, Prod.mk.injEq] at h
          obtain ⟨rfl, -⟩ := h
          obtain ⟨i, hi, rfl⟩ := out_wrap64 hv
          obtain ⟨x, y, hx, hy, hxy⟩ := out_division hi
          cases hxy
          subst ho
          refine ⟨_, _, hx, hy, fun da db ha hia hb hib => ?_⟩
          obtain ⟨ks, hks, hik, hiff⟩ := tested_eval hy
          refine ⟨da ++ db ++ ks ++ [], ?_, ?_, ?_⟩
          · simp only [divisors, divisors.divisorsList]
            exact evalList_append (evalList_append (evalList_append ha hb) hks) evalList_nil
          · exact allInt_append (allInt_append (allInt_append hia hib) hik) allInt_nil
          · simp only [binaryRes, andThen_outcome, Eval.operate]
            unfold outcome
            by_cases h3 : y = 0
            · have h3' := hiff.mpr h3
              by_cases h1 : Val.int 0 ∈ da <;> by_cases h2 : Val.int 0 ∈ db <;>
                simp [h1, h2, h3, h3']
            · have h3' : Val.int 0 ∉ ks := fun h => h3 (hiff.mp h)
              by_cases h1 : Val.int 0 ∈ da <;> by_cases h2 : Val.int 0 ∈ db <;>
                simp [h1, h2, h3, h3', tolean.IR.Division.apply]
        | tmod =>
          simp only [pure_ok, Prod.mk.injEq] at h
          obtain ⟨rfl, -⟩ := h
          obtain ⟨x, y, hx, hy, rfl⟩ := out_division hv
          subst ho
          refine ⟨_, _, hx, hy, fun da db ha hia hb hib => ?_⟩
          obtain ⟨ks, hks, hik, hiff⟩ := tested_eval hy
          refine ⟨da ++ db ++ ks, ?_, ?_, ?_⟩
          · simp only [divisors]
            exact evalList_append (evalList_append ha hb) hks
          · exact allInt_append (allInt_append hia hib) hik
          · simp only [binaryRes, andThen_outcome, Eval.operate]
            unfold outcome
            by_cases h3 : y = 0
            · have h3' := hiff.mpr h3
              by_cases h1 : Val.int 0 ∈ da <;> by_cases h2 : Val.int 0 ∈ db <;>
                simp [h1, h2, h3, h3']
            · have h3' : Val.int 0 ∉ ks := fun h => h3 (hiff.mp h)
              by_cases h1 : Val.int 0 ∈ da <;> by_cases h2 : Val.int 0 ∈ db <;>
                simp [h1, h2, h3, h3', tolean.IR.Division.apply]
  · exact absurd h reject_ne_ok

/-- The code of a binary operator gives what the interpreter gives on the
values of the operands, or the interpreter panics on a zero divisor. -/
theorem translateBinary_out {o : BinOp} (h : translateBinary sp o a ta b tb = .ok (c, t))
    (hv : IR.Expr.eval fs fuel ρ c = some v) :
    ∃ va vb, IR.Expr.eval fs fuel ρ a = some va ∧ IR.Expr.eval fs fuel ρ b = some vb ∧
      BinaryOut fs fuel ρ o a b c va vb v := by
  cases o <;> simp only [translateBinary] at h
  case add =>
    split at h
    · simp only [pure_ok, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      obtain ⟨x, y, hx, hy, rfl⟩ := out_append hv
      exact ⟨_, _, hx, hy, binaryOut_plain (by decide) (by decide) (by decide) (by decide)
        rfl (by simp [divisors, divisors.divisorsList])⟩
    · obtain ⟨x, y, hx, hy, rfl, hd⟩ := arith_out h hv
      exact ⟨_, _, hx, hy, binaryOut_plain (by decide) (by decide) (by decide) (by decide)
        rfl hd⟩
  case sub | mul =>
    obtain ⟨x, y, hx, hy, rfl, hd⟩ := arith_out h hv
    exact ⟨_, _, hx, hy, binaryOut_plain (by decide) (by decide) (by decide) (by decide)
      rfl hd⟩
  case quo => exact divide_out rfl h hv
  case rem => exact divide_out rfl h hv
  case lt | le | gt | ge =>
    obtain ⟨x, y, hx, hy, rfl, hd⟩ := compare_out h hv
    exact ⟨_, _, hx, hy, binaryOut_plain (by decide) (by decide) (by decide) (by decide)
      (by simp [Eval.binary, tolean.IR.Order.apply]) hd⟩
  case eq =>
    split at h
    · simp only [pure_ok, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      rw [out_decide] at hv
      obtain ⟨x, y, r, hx, hy, he, rfl⟩ := out_eq hv
      exact ⟨_, _, hx, hy, binaryOut_plain (by decide) (by decide) (by decide) (by decide)
        (by simp [Eval.binary, he]) (by simp [divisors])⟩
    · exact absurd h reject_ne_ok
  case ne =>
    split at h
    · simp only [pure_ok, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      rw [out_decide] at hv
      obtain ⟨x, y, r, hx, hy, he, rfl⟩ := out_ne hv
      exact ⟨_, _, hx, hy, binaryOut_plain (by decide) (by decide) (by decide) (by decide)
        (by simp [Eval.binary, he]) (by simp [divisors])⟩
    · exact absurd h reject_ne_ok
  case land =>
    split at h
    · exact absurd h reject_ne_ok
    · next hb =>
      split at h
      · simp only [pure_ok, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        obtain ⟨x, y, hx, hy, rfl⟩ := out_and hv
        refine ⟨_, _, hx, hy, fun da db ha hia hb' hib => ?_⟩
        have hnil : divisors b = [] := by simpa using hb
        rw [hnil, evalList_nil] at hb'
        cases hb'
        refine ⟨da ++ [], by simpa [divisors, hnil] using ha, allInt_append hia allInt_nil, ?_⟩
        simp only [binaryRes, andThen_outcome, outcome_nil, List.append_nil]
        unfold outcome
        by_cases h1 : Val.int 0 ∈ da <;> cases x <;> simp [h1]
      · exact absurd h reject_ne_ok
  case lor =>
    split at h
    · exact absurd h reject_ne_ok
    · next hb =>
      split at h
      · simp only [pure_ok, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        obtain ⟨x, y, hx, hy, rfl⟩ := out_or hv
        refine ⟨_, _, hx, hy, fun da db ha hia hb' hib => ?_⟩
        have hnil : divisors b = [] := by simpa using hb
        rw [hnil, evalList_nil] at hb'
        cases hb'
        refine ⟨da ++ [], by simpa [divisors, hnil] using ha, allInt_append hia allInt_nil, ?_⟩
        simp only [binaryRes, andThen_outcome, outcome_nil, List.append_nil]
        unfold outcome
        by_cases h1 : Val.int 0 ∈ da <;> cases x <;> simp [h1]
      · exact absurd h reject_ne_ok

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

/-- An expression whose code divides by nothing. -/
theorem plain_out {ρ : Eval.Env} {c : IR.Expr} (hd : divisors c = []) :
    IR.Expr.evalList fs fuel ρ (divisors c) = some [] ∧ AllInt [] :=
  ⟨by rw [hd]; exact evalList_nil, allInt_nil⟩

variable (p : Eval.Program) (fs) (fuel)

/-- `expr_sound` and its case for argument lists, by induction on the
translator's fuel. -/
theorem expr_sound_aux {ctx : Ctx} (hp : ctx.program = p) (hc : CallsAgree p fs fuel) :
    ∀ n : Nat,
      (∀ (env : Pure.Env) (e : Expr) (c : IR.Expr) (t : Ty), translateExpr ctx env n e = .ok (c, t) →
        ∀ ρs ρo v, Agree ρs ρo → Scoped env ρs → IR.Expr.eval fs fuel ρo c = some v →
          ∃ ds, IR.Expr.evalList fs fuel ρo (divisors c) = some ds ∧ AllInt ds ∧
            Eval.eval p fuel ρs e = some (outcome ds v)) ∧
      (∀ (env : Pure.Env) (es : List Expr) (cs : List (IR.Expr × Ty)),
        translateArgs ctx env n es = .ok cs →
        ∀ ρs ρo vs, Agree ρs ρo → Scoped env ρs →
          IR.Expr.evalList fs fuel ρo (cs.map (·.1)) = some vs →
          ∃ ds, IR.Expr.evalList fs fuel ρo (divisors.divisorsList (cs.map (·.1))) = some ds ∧
            AllInt ds ∧ Eval.evalList p fuel ρs es = some (outcome ds vs))
  | 0 => by
    refine ⟨fun env e c t h => by simp [translateExpr] at h, fun env es cs h => ?_⟩
    cases es with
    | nil =>
      simp only [translateArgs, pure_ok] at h
      subst h
      intro ρs ρo vs _ _ hv
      simp [IR.Expr.evalList] at hv
      subst hv
      exact ⟨[], by simp [divisors.divisorsList, IR.Expr.evalList], allInt_nil,
        by simp [Eval.evalList, outcome_nil]⟩
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
          refine ⟨[], by simp [divisors, IR.Expr.evalList], allInt_nil, ?_⟩
          rw [Eval.eval, ha name, hv, outcome_nil]
        · next hl =>
          split at h
          · next b hb =>
            simp only [pure_ok, Prod.mk.injEq] at h
            obtain ⟨rfl, -⟩ := h
            simp only [IR.Expr.eval, Option.some.injEq] at hv
            subst hv
            refine ⟨[], by simp [divisors, IR.Expr.evalList], allInt_nil, ?_⟩
            rw [Eval.eval, scoped_none hs (env_lookup_none hl), ← hp, hb, outcome_nil]
            rfl
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
            refine ⟨[], by simp [divisors, IR.Expr.evalList], allInt_nil, ?_⟩
            simp [Eval.eval, hk, outcome_nil]
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
          refine ⟨[], by simp [divisors, IR.Expr.evalList], allInt_nil, ?_⟩
          simp [Eval.eval, hs', outcome_nil]
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
            obtain ⟨ds, hds, hint, he⟩ := ihe env arg ca tc hca ρs ρo _ ha hs hj
            refine ⟨ds ++ [], by simpa [divisors, divisors.divisorsList] using hds,
              allInt_append hint allInt_nil, ?_⟩
            rw [Eval.eval, he, andThen_outcome, List.append_nil, ← outcome_some]
            rfl
          · exact absurd h reject_ne_ok
        · split at h
          · simp only [pure_ok, Prod.mk.injEq] at h
            obtain ⟨rfl, -⟩ := h
            obtain ⟨b, hb, rfl⟩ := out_not hv
            obtain ⟨ds, hds, hint, he⟩ := ihe env arg ca tc hca ρs ρo _ ha hs hb
            refine ⟨ds, by simpa [divisors] using hds, hint, ?_⟩
            rw [Eval.eval, he, andThen_outcome, ← outcome_some]
            rfl
          · exact absurd h reject_ne_ok
        · exact absurd h reject_ne_ok
      -- A binary operator.
      · next sp op l r =>
        cases ho : BinOp.ofString? op with
        | none => simp [ho] at h
        | some o =>
          simp only [ho, bind_ok] at h
          obtain ⟨⟨a, ta⟩, hla, ⟨b, tb⟩, hrb, h⟩ := h
          obtain ⟨va, vb, hva, hvb, hout⟩ := translateBinary_out h hv
          obtain ⟨da, hda, hia, hl⟩ := ihe env l a ta hla ρs ρo va ha hs hva
          obtain ⟨db, hdb, hib, hr⟩ := ihe env r b tb hrb ρs ρo vb ha hs hvb
          obtain ⟨ds, hds, hint, hres⟩ := hout da db hda hia hdb hib
          refine ⟨ds, hds, hint, ?_⟩
          rw [eval_binary ho, hl, hr, hres]
      -- A call of a translated function.
      · next sp sp' f args =>
        cases hf : env.has f with
        | true => simp [hf] at h
        | false =>
          cases hsig : ctx.known.find? (·.name == f) with
          | none => simp [hf, hsig] at h
          | some sig =>
            simp only [hf, hsig, Bool.false_eq_true, ↓reduceIte, bind_ok] at h
            obtain ⟨_, -, h⟩ := h
            cases hpanic : sig.panics
            · simp only [hpanic, Bool.false_eq_true, ↓reduceIte, pure_bind, bind_ok] at h
              obtain ⟨codes, hcodes, h⟩ := h
              cases hfit : argsFit codes sig.params
              · simp [hfit, reject, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
              simp only [hfit, ↓reduceIte, pure, Except.pure, Except.ok.injEq,
                Prod.mk.injEq] at h
              obtain ⟨hc', -⟩ := h
              subst hc'
              rw [out_call] at hv
              cases hvs : IR.Expr.evalList fs fuel ρo (codes.map (·.1)) with
              | none => simp [hvs] at hv
              | some vs =>
                simp only [hvs, Option.bind_some] at hv
                obtain ⟨ds, hds, hint, hargs⟩ := iha env args codes hcodes ρs ρo vs ha hs hvs
                refine ⟨ds, by simpa [divisors] using hds, hint, ?_⟩
                rw [eval_call, scoped_none hs hf, hargs]
                simp only [andThen_outcome, hc f vs _ (callR_of_callO hv)]
                exact outcome_some ds v
            · simp [hpanic, reject, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
      · exact absurd h reject_ne_ok
    · cases es with
      | nil =>
        simp only [translateArgs, pure_ok] at h
        subst h
        intro ρs ρo vs _ _ hv
        simp [IR.Expr.evalList] at hv
        subst hv
        exact ⟨[], by simp [divisors.divisorsList, IR.Expr.evalList], allInt_nil,
          by simp [Eval.evalList, outcome_nil]⟩
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
            obtain ⟨d1, hd1, hi1, he1⟩ := ihe env e c t hc' ρs ρo w ha hs hw
            obtain ⟨d2, hd2, hi2, he2⟩ := iha env es cs' hcs ρs ρo ws ha hs hws
            refine ⟨d1 ++ d2, ?_, allInt_append hi1 hi2, ?_⟩
            · simp only [List.map_cons, divisors.divisorsList]
              exact evalList_append hd1 hd2
            · rw [Eval.evalList, he1, andThen_outcome]
              unfold outcome
              by_cases h1 : Val.int 0 ∈ d1 <;> by_cases h2 : Val.int 0 ∈ d2 <;>
                simp [h1, h2, he2, outcome]

/-- The code that the translator gives for an expression gives a value only
when the interpreter gives the same value for the expression, or panics
because a divisor of the code is zero. -/
theorem expr_sound {ctx : Ctx} (hp : ctx.program = p) (hc : CallsAgree p fs fuel) {n : Nat}
    {env : Pure.Env} {e : Expr} {c : IR.Expr} {t : Ty} (h : translateExpr ctx env n e = .ok (c, t))
    {ρs ρo : Eval.Env} {v : Val} (ha : Agree ρs ρo) (hs : Scoped env ρs)
    (hv : IR.Expr.eval fs fuel ρo c = some v) :
    ∃ ds, IR.Expr.evalList fs fuel ρo (divisors c) = some ds ∧ AllInt ds ∧
      Eval.eval p fuel ρs e = some (outcome ds v) :=
  (expr_sound_aux fs fuel p hp hc n).1 env e c t h ρs ρo v ha hs hv

end tolean.Go.Proof
