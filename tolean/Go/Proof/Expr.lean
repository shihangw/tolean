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
    (args : List Expr) (hb : Eval.builtin p f = none) :
    Eval.eval p fuel ρ (.call sp (.ident sp' f) args false) =
      if (ρ.lookup f).isSome then none
      else (Eval.evalList p fuel ρ args).andThen (callS p fuel f) := by
  rw [Eval.eval]
  split
  · rfl
  · rw [hb, Eval.callFunc]
    congr 1

theorem eval_builtin (p : Eval.Program) (fuel : Nat) (ρ : Eval.Env) (sp sp' : Span) (f : String)
    (a : Expr) {b : Eval.Builtin} (hb : Eval.builtin p f = some b) (hl : ρ.lookup f = none) :
    Eval.eval p fuel ρ (.call sp (.ident sp' f) [a] false) =
      (Eval.eval p fuel ρ a).andThen fun x => Res.lift (Eval.applyBuiltin b x) := by
  rw [Eval.eval, hl, hb]
  rfl

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

/-- An operation of two arguments. -/
theorem out_ext2 {op : IR.ExprExt} {a b : IR.Expr} (h : IR.Expr.eval fs fuel ρ (.ext op [a, b]) = some v) :
    ∃ x y, IR.Expr.eval fs fuel ρ a = some x ∧ IR.Expr.eval fs fuel ρ b = some y ∧
      op.apply [x, y] = some v := by
  simp only [IR.Expr.eval, IR.Expr.evalList] at h
  cases ha : IR.Expr.eval fs fuel ρ a with
  | none => simp [ha] at h
  | some wa =>
    cases hb : IR.Expr.eval fs fuel ρ b with
    | none => simp [ha, hb] at h
    | some wb => simp [ha, hb] at h; exact ⟨_, _, rfl, rfl, h⟩

/-- An operation of one argument. -/
theorem out_ext1 {op : IR.ExprExt} {a : IR.Expr} (h : IR.Expr.eval fs fuel ρ (.ext op [a]) = some v) :
    ∃ x, IR.Expr.eval fs fuel ρ a = some x ∧ op.apply [x] = some v := by
  simp only [IR.Expr.eval, IR.Expr.evalList] at h
  cases ha : IR.Expr.eval fs fuel ρ a with
  | none => simp [ha] at h
  | some wa => simp [ha] at h; exact ⟨_, rfl, h⟩

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

/-- Each value is an integer, as the value of a divisor is, or a string, as
the value of the test of an index is. -/
def CheckVals (ds : List Val) : Prop := ∀ d ∈ ds, (∃ i, d = .int i) ∨ ∃ m, d = .str m

/-- The panic that a check with the value `d` causes: a divisor panics when it
is zero, and the test of an index when its message is not empty. -/
def fault : Val → Option Val
  | .int i => if i = 0 then some Eval.divideByZero else none
  | .str m => if m = "" then none else some (.str m)
  | .bool _ => none

/-- The panic of the first check of `ds` that fails. -/
def firstFault : List Val → Option Val
  | [] => none
  | d :: ds => (fault d).or (firstFault ds)

/-- What the interpreter gives for an expression whose code has the value
`v`, when the checks of the code have the values `ds`: the panic of the first
check that fails, and `v` when none does. -/
def outcome {α : Type} (ds : List Val) (v : α) : Except Val α :=
  match firstFault ds with
  | some x => .error x
  | none => .ok v

theorem checkVals_nil : CheckVals [] := by simp [CheckVals]

theorem checkVals_append {a b : List Val} (ha : CheckVals a) (hb : CheckVals b) : CheckVals (a ++ b) := by
  intro d hd
  rcases List.mem_append.mp hd with hd | hd
  · exact ha d hd
  · exact hb d hd

theorem checkVals_int (i : Int) : CheckVals [.int i] := by simp [CheckVals]

theorem checkVals_str (m : String) : CheckVals [.str m] := by simp [CheckVals]

theorem firstFault_append : ∀ (a b : List Val), firstFault (a ++ b) = (firstFault a).or (firstFault b)
  | [], b => by simp [firstFault]
  | d :: a, b => by
    simp only [List.cons_append, firstFault, firstFault_append a b, Option.or_assoc]

theorem outcome_nil {α : Type} (v : α) : outcome [] v = .ok v := by simp [outcome, firstFault]

theorem andThen_outcome {α β : Type} (ds : List Val) (a : α) (f : α → Res Val β) :
    Res.andThen (some (outcome ds a)) f =
      match firstFault ds with
      | some x => some (.error x)
      | none => f a := by
  unfold outcome
  split <;> rfl

theorem outcome_some {α : Type} (ds : List Val) (v : α) :
    (match firstFault ds with
      | some x => some (.error x)
      | none => some (.ok v)) = some (outcome ds v) := by
  unfold outcome
  split <;> rfl

/-- Two steps, each with its checks, are one step with the checks of both. -/
theorem outcome_bind {α β : Type} (da db : List Val) (a : α) (f : α → β) :
    Res.andThen (some (outcome da a)) (fun x => some (outcome db (f x))) =
      some (outcome (da ++ db) (f a)) := by
  unfold outcome
  rw [firstFault_append]
  cases firstFault da <;> cases firstFault db <;> rfl

/-- A step with its checks, then a step that gives a value with its own. -/
theorem outcome_then {α β : Type} {da db : List Val} {a : α} {w : β} {g : α → Res Val β}
    (hg : g a = some (outcome db w)) :
    Res.andThen (some (outcome da a)) g = some (outcome (da ++ db) w) := by
  unfold outcome at *
  rw [firstFault_append]
  cases firstFault da with
  | some x => rfl
  | none => simpa using hg

theorem outcome_map {α β : Type} (d : List Val) (a : α) (f : α → β) :
    Res.andThen (some (outcome d a)) (fun x => Res.ok (f x)) = some (outcome d (f a)) := by
  unfold outcome
  cases firstFault d <;> rfl

/-- `s[i]` gives the byte at `i`, unless the test of the index fails. -/
theorem index_outcome (s : String) (i : Int) :
    Eval.indexString (.str s) (.int i) = some (outcome [.str (indexFault s i)] (.int (byteAt s i))) := by
  have hlen : byteLen s = ((Eval.strBytes s).length : Int) := rfl
  unfold Eval.indexString outcome indexFault
  by_cases hb : 0 ≤ i ∧ i.toNat < (Eval.strBytes s).length
  · have hb' : 0 ≤ i ∧ i < byteLen s := by rw [hlen]; omega
    simp only [hb, hb', firstFault, fault, Option.or_none]
    have h2 : i.toNat < s.toByteArray.toList.length := hb.2
    simp [byteAt, bytes, Eval.strBytes, List.getElem?_eq_getElem h2]
  · have hb' : ¬ (0 ≤ i ∧ i < byteLen s) := by rw [hlen]; omega
    simp only [hb, hb', dite_false, if_false, firstFault, fault, Option.or_none, indexMessage_ne]
    rfl

theorem outcome_eq_ok {α : Type} {ds : List Val} {v u : α} (h : outcome ds v = .ok u) : v = u := by
  unfold outcome at h
  split at h
  · cases h
  · injection h

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
    ∃ ks, IR.Expr.evalList fs fuel ρ (tested b) = some ks ∧ CheckVals ks ∧
      firstFault ks = if y = 0 then some Eval.divideByZero else none := by
  unfold tested
  split
  · next n =>
    simp only [IR.Expr.eval, Option.some.injEq, Val.int.injEq] at hy
    subst hy
    split
    · next h0 => exact ⟨[.int n], evalList_single (by simp [IR.Expr.eval]), checkVals_int n,
        by simp [h0, firstFault, fault]⟩
    · exact ⟨[], evalList_nil, checkVals_nil, by simp [*, firstFault]⟩
  · exact ⟨[.int y], evalList_single hy, checkVals_int y, by
      by_cases h0 : y = 0 <;> simp [h0, firstFault, fault]⟩

/-- The divisors of the code of a binary operator, from those of its
operands. -/
theorem divisors_pair (ds : List Val) {ρ : Eval.Env} {a b : IR.Expr} {da db : List Val}
    (ha : IR.Expr.evalList fs fuel ρ (divisors a) = some da) (hia : CheckVals da)
    (hb : IR.Expr.evalList fs fuel ρ (divisors b) = some db) (hib : CheckVals db)
    (hds : ds = da ++ db) :
    IR.Expr.evalList fs fuel ρ (divisors a ++ divisors b) = some ds ∧ CheckVals ds := by
  subst hds
  exact ⟨evalList_append ha hb, checkVals_append hia hib⟩

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
  ∀ da db, IR.Expr.evalList fs fuel ρ (divisors a) = some da → CheckVals da →
    IR.Expr.evalList fs fuel ρ (divisors b) = some db → CheckVals db →
    ∃ ds, IR.Expr.evalList fs fuel ρ (divisors c) = some ds ∧ CheckVals ds ∧
      binaryRes o (some (outcome da va)) (some (outcome db vb)) = some (outcome ds v)

/-- A strict operator whose code divides by nothing new and whose value is
what `binary` gives. -/
theorem binaryOut_plain {o : BinOp} (hl : o ≠ .land) (hr : o ≠ .lor) (hq : o ≠ .quo)
    (hm : o ≠ .rem) {va vb : Val} (hbin : Eval.binary o va vb = some v)
    (hdiv : divisors c = divisors a ++ divisors b) :
    BinaryOut fs fuel ρ o a b c va vb v := by
  intro da db ha hia hb hib
  refine ⟨da ++ db, by rw [hdiv]; exact evalList_append ha hb, checkVals_append hia hib, ?_⟩
  rw [binaryRes_strict hl hr]
  simp only [operate_binary hq hm]
  unfold outcome
  rw [firstFault_append]
  cases firstFault da <;> cases firstFault db <;> simp [hbin]

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

/-- The operator of the interpreter for an order. -/
def orderOp : tolean.IR.Order → BinOp
  | .lt => .lt
  | .le => .le
  | .gt => .gt
  | .ge => .ge

theorem compare_out {op : tolean.IR.Order} (h : Pure.compare sp op a ta b tb = .ok (c, t))
    (hv : IR.Expr.eval fs fuel ρ c = some v) :
    ∃ x y, IR.Expr.eval fs fuel ρ a = some x ∧ IR.Expr.eval fs fuel ρ b = some y ∧
      Eval.binary (orderOp op) x y = some v ∧ divisors c = divisors a ++ divisors b := by
  unfold Pure.compare at h
  split at h
  · simp only [pure_ok, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    obtain ⟨x, y, hx, hy, happ⟩ := out_ext2 hv
    refine ⟨x, y, hx, hy, ?_, by cases op <;> simp [strOrder, divisors, divisors.divisorsList]⟩
    cases op <;> cases x <;> cases y <;>
      simp_all [strOrder, IR.ExprExt.apply, orderOp, Eval.binary, strLt, strLe, strGt, strGe,
        Eval.strBytes, bytes]
  · split at h
    · split at h
      · simp only [pure_ok, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        rw [out_decide] at hv
        obtain ⟨x, y, hx, hy, rfl⟩ := out_order hv
        exact ⟨_, _, hx, hy, by cases op <;> simp [orderOp, Eval.binary, tolean.IR.Order.apply],
          by simp [divisors]⟩
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
          · exact checkVals_append (checkVals_append (checkVals_append hia hib) hik) checkVals_nil
          · simp only [binaryRes, Eval.operate]
            unfold outcome
            simp only [firstFault_append, hiff, firstFault, Option.or_none]
            cases firstFault da <;> cases firstFault db <;> by_cases h3 : y = 0 <;>
              simp [h3, tolean.IR.Division.apply]
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
          · exact checkVals_append (checkVals_append hia hib) hik
          · simp only [binaryRes, Eval.operate]
            unfold outcome
            simp only [firstFault_append, hiff]
            cases firstFault da <;> cases firstFault db <;> by_cases h3 : y = 0 <;>
              simp [h3, tolean.IR.Division.apply]
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
    obtain ⟨x, y, hx, hy, hbin, hd⟩ := compare_out h hv
    exact ⟨_, _, hx, hy, binaryOut_plain (by decide) (by decide) (by decide) (by decide)
      hbin hd⟩
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
        refine ⟨da ++ [], by simpa [divisors, hnil] using ha, checkVals_append hia checkVals_nil, ?_⟩
        simp only [binaryRes, andThen_outcome, outcome_nil, List.append_nil]
        unfold outcome
        cases firstFault da <;> cases x <;> simp
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
        refine ⟨da ++ [], by simpa [divisors, hnil] using ha, checkVals_append hia checkVals_nil, ?_⟩
        simp only [binaryRes, andThen_outcome, outcome_nil, List.append_nil]
        unfold outcome
        cases firstFault da <;> cases x <;> simp
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
    IR.Expr.evalList fs fuel ρ (divisors c) = some [] ∧ CheckVals [] :=
  ⟨by rw [hd]; exact evalList_nil, checkVals_nil⟩

variable (p : Eval.Program) (fs) (fuel)

/-- `expr_sound` and its case for argument lists, by induction on the
translator's fuel. -/
theorem expr_sound_aux {ctx : Ctx} (hp : ctx.program = p) (hc : CallsAgree p fs fuel) :
    ∀ n : Nat,
      (∀ (env : Pure.Env) (e : Expr) (c : IR.Expr) (t : Ty), translateExpr ctx env n e = .ok (c, t) →
        ∀ ρs ρo v, Agree ρs ρo → Scoped env ρs → IR.Expr.eval fs fuel ρo c = some v →
          ∃ ds, IR.Expr.evalList fs fuel ρo (divisors c) = some ds ∧ CheckVals ds ∧
            Eval.eval p fuel ρs e = some (outcome ds v)) ∧
      (∀ (env : Pure.Env) (es : List Expr) (cs : List (IR.Expr × Ty)),
        translateArgs ctx env n es = .ok cs →
        ∀ ρs ρo vs, Agree ρs ρo → Scoped env ρs →
          IR.Expr.evalList fs fuel ρo (cs.map (·.1)) = some vs →
          ∃ ds, IR.Expr.evalList fs fuel ρo (divisors.divisorsList (cs.map (·.1))) = some ds ∧
            CheckVals ds ∧ Eval.evalList p fuel ρs es = some (outcome ds vs))
  | 0 => by
    refine ⟨fun env e c t h => by simp [translateExpr] at h, fun env es cs h => ?_⟩
    cases es with
    | nil =>
      simp only [translateArgs, pure_ok] at h
      subst h
      intro ρs ρo vs _ _ hv
      simp [IR.Expr.evalList] at hv
      subst hv
      exact ⟨[], by simp [divisors.divisorsList, IR.Expr.evalList], checkVals_nil,
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
          refine ⟨[], by simp [divisors, IR.Expr.evalList], checkVals_nil, ?_⟩
          rw [Eval.eval, ha name, hv, outcome_nil]
        · next hl =>
          split at h
          -- A constant of the package.
          · next te w hw =>
            split at h
            · simp only [pure_ok, Prod.mk.injEq] at h
              obtain ⟨rfl, -⟩ := h
              have hv' : v = w := by
                cases w <;> simp [valueCode, IR.Expr.eval] at hv <;> exact hv.symm
              subst hv'
              refine ⟨[], by cases v <;> simp [valueCode, divisors, IR.Expr.evalList], checkVals_nil, ?_⟩
              rw [Eval.eval, scoped_none hs (env_lookup_none hl), ← hp]
              simp [Eval.global, hw, outcome_nil, Res.lift]
            · exact absurd h reject_ne_ok
          -- `true` or `false`.
          · next hc =>
            split at h
            · next b hb =>
              simp only [pure_ok, Prod.mk.injEq] at h
              obtain ⟨rfl, -⟩ := h
              simp only [IR.Expr.eval, Option.some.injEq] at hv
              subst hv
              refine ⟨[], by simp [divisors, IR.Expr.evalList], checkVals_nil, ?_⟩
              rw [Eval.eval, scoped_none hs (env_lookup_none hl), ← hp]
              simp [Eval.global, hc, hb, outcome_nil, Res.lift]
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
            refine ⟨[], by simp [divisors, IR.Expr.evalList], checkVals_nil, ?_⟩
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
          refine ⟨[], by simp [divisors, IR.Expr.evalList], checkVals_nil, ?_⟩
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
              checkVals_append hint checkVals_nil, ?_⟩
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
      -- An index of a string.
      · next sp str idx =>
        simp only [bind_ok] at h
        obtain ⟨⟨cs, ts⟩, hcs, ⟨ci, ti⟩, hci, h⟩ := h
        by_cases hts : ts = .string
        · by_cases hti : ti.isNum = true
          · simp only [hts, hti, ↓reduceIte, pure_bind, pure_ok,
              Prod.mk.injEq] at h
            obtain ⟨rfl, -⟩ := h
            obtain ⟨x, y, hx, hy, happ⟩ := out_ext2 hv
            obtain ⟨da, hda, hia, hs1⟩ := ihe env str cs ts hcs ρs ρo x ha hs hx
            obtain ⟨db, hdb, hib, hs2⟩ := ihe env idx ci ti hci ρs ρo y ha hs hy
            cases x <;> cases y <;> simp [IR.ExprExt.apply] at happ
            next text k =>
            subst happ
            have hfault : IR.Expr.eval fs fuel ρo (.ext .indexFault [cs, ci]) =
                some (.str (indexFault text k)) := by
              simp [IR.Expr.eval, IR.Expr.evalList, hx, hy, IR.ExprExt.apply]
            refine ⟨da ++ (db ++ [.str (indexFault text k)]), ?_, ?_, ?_⟩
            · have hd : divisors (.ext .byteAt [cs, ci]) =
                  divisors cs ++ (divisors ci ++ [.ext .indexFault [cs, ci]]) := by
                simp [divisors, divisors.divisorsList]
              rw [hd]
              exact evalList_append hda (evalList_append hdb (evalList_single hfault))
            · exact checkVals_append hia (checkVals_append hib (checkVals_str _))
            · rw [Eval.eval, hs1, hs2]
              exact outcome_then (outcome_then (index_outcome text k))
          · simp [hts, hti, reject, throw, throwThe, MonadExceptOf.throw, bind,
              Except.bind, pure, Except.pure] at h
        · simp [hts, reject, throw, throwThe, MonadExceptOf.throw, bind,
            Except.bind] at h
      -- A call of `len`, a conversion, or a translated function.
      · next sp sp' f args =>
        cases hf : env.has f with
        | true => simp [hf] at h
        | false =>
        have hl : ρs.lookup f = none := scoped_none hs hf
        cases hbi : Eval.builtin ctx.program f with
        | some bi =>
          rw [hp] at hbi
          match args, h with
          | [arg], h =>
            have hev := eval_builtin p fuel ρs sp sp' f arg hbi hl
            simp only [hf, hp, hbi, Bool.false_eq_true, ↓reduceIte, bind_ok, pure_bind] at h
            obtain ⟨⟨ca, tc⟩, hca, h⟩ := h
            cases bi with
            | len =>
              by_cases htc : tc = .string
              · simp only [htc, ↓reduceIte, pure_ok, Prod.mk.injEq] at h
                obtain ⟨rfl, -⟩ := h
                obtain ⟨x, hx, happ⟩ := out_ext1 hv
                obtain ⟨ds, hds, hint, he⟩ := ihe env arg ca tc hca ρs ρo x ha hs hx
                cases x <;> simp [IR.ExprExt.apply] at happ
                subst happ
                refine ⟨ds ++ [], by simpa [divisors, divisors.divisorsList] using hds,
                  checkVals_append hint checkVals_nil, ?_⟩
                rw [hev, he]
                exact outcome_then (by simp [Eval.applyBuiltin, outcome_nil]; rfl)
              · simp [htc] at h
            | toInt | toInt64 =>
              by_cases htc : tc.isNum = true
              · simp only [htc, ↓reduceIte, pure_ok, Prod.mk.injEq] at h
                obtain ⟨rfl, -⟩ := h
                obtain ⟨ds, hds, hint, he⟩ := ihe env arg ca tc hca ρs ρo v ha hs hv
                refine ⟨ds ++ [], by simpa using hds, checkVals_append hint checkVals_nil, ?_⟩
                rw [hev, he]
                exact outcome_then (by simp [Eval.applyBuiltin, outcome_nil])
              · simp [htc] at h
            | convert u =>
              -- A conversion to a type of the package over `int`, `int64`
              -- or `bool` keeps the value.
              have hu : u ≠ "string" → Eval.applyBuiltin (.convert u) v = some v := by
                intro hu; simp [Eval.applyBuiltin, hu]
              have hok : ∀ t', (match basicType u with
                  | some .int => if tc.isNum then pure (ca, Ty.int) else reject sp "the subset converts only integers to an integer type"
                  | some .int64 => if tc.isNum then pure (ca, Ty.int64) else reject sp "the subset converts only integers to an integer type"
                  | some .bool => if tc = .bool then pure (ca, Ty.bool) else reject sp "the subset converts only a bool to a bool type"
                  | _ => reject sp s!"the subset leaves out conversions to '{f}'" : TM (IR.Expr × Ty)) = .ok (c, t') →
                  c = ca ∧ u ≠ "string" := by
                intro t' h'
                cases hb : basicType u with
                | none => simp [hb] at h'
                | some bt =>
                  have hs : u ≠ "string" := by
                    rintro rfl; simp [basicType] at hb; subst hb; simp [basicType, reject, throw, throwThe, MonadExceptOf.throw] at h'
                  cases bt <;> simp [hb] at h' <;> (try split at h') <;>
                    simp_all [pure_ok]
              obtain ⟨rfl, hus⟩ := hok t h
              obtain ⟨ds, hds, hint, he⟩ := ihe env arg c tc hca ρs ρo v ha hs hv
              refine ⟨ds ++ [], by simpa using hds, checkVals_append hint checkVals_nil, ?_⟩
              rw [hev, he]
              exact outcome_then (by simp [hu hus, outcome_nil])
          | [], h => simp [hf, hp, hbi] at h
          | _ :: _ :: _, h => simp [hf, hp, hbi] at h
        | none =>
          cases hsig : ctx.known.find? (·.name == f) with
          | none => simp [hf, hbi, hsig] at h
          | some sig =>
            simp only [hf, hbi, hsig, Bool.false_eq_true, ↓reduceIte, bind_ok] at h
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
                rw [hp] at hbi
                rw [eval_call p fuel ρs sp sp' f args hbi, hl, hargs]
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
        exact ⟨[], by simp [divisors.divisorsList, IR.Expr.evalList], checkVals_nil,
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
            refine ⟨d1 ++ d2, ?_, checkVals_append hi1 hi2, ?_⟩
            · simp only [List.map_cons, divisors.divisorsList]
              exact evalList_append hd1 hd2
            · rw [Eval.evalList, he1]
              exact outcome_then (by rw [he2]; exact outcome_map d2 ws (w :: ·))

/-- The code that the translator gives for an expression gives a value only
when the interpreter gives the same value for the expression, or panics
because a divisor of the code is zero. -/
theorem expr_sound {ctx : Ctx} (hp : ctx.program = p) (hc : CallsAgree p fs fuel) {n : Nat}
    {env : Pure.Env} {e : Expr} {c : IR.Expr} {t : Ty} (h : translateExpr ctx env n e = .ok (c, t))
    {ρs ρo : Eval.Env} {v : Val} (ha : Agree ρs ρo) (hs : Scoped env ρs)
    (hv : IR.Expr.eval fs fuel ρo c = some v) :
    ∃ ds, IR.Expr.evalList fs fuel ρo (divisors c) = some ds ∧ CheckVals ds ∧
      Eval.eval p fuel ρs e = some (outcome ds v) :=
  (expr_sound_aux fs fuel p hp hc n).1 env e c t h ρs ρo v ha hs hv

end tolean.Go.Proof
