import Lean
import tolean.TypeScript.Proof.Module
import tolean.TypeScript.Spec.Lemmas.Number
import tolean.TypeScript.IR.Equality
import tolean.TypeScript.Map
import Lean.Elab.Tactic.Basic
import Lean.Meta.AppBuilder
import Lean.Meta.Tactic.Assert

/-!
The printer link for one file.

`translate_sound` is about the Tolean IR, so it trusts the printer: that the
printed Lean computes what `IR/Eval.lean` gives for the IR. A certificate
closes that gap for its file. It holds the IR as a Lean term, and the kernel
checks with `translatesTo` that the translator gives that IR for the parsed
program. Then one theorem for each function states that the printed
definition computes what the evaluator gives for the IR, and
`decls_sound` carries it to the interpreter. So the file is proved with no
trust in the translator or in the printer.
-/
namespace tolean.TypeScript.Proof

open tolean.TypeScript tolean.TypeScript.Syntax tolean.TypeScript.Translate
open tolean.TypeScript.Eval (Val)

variable {N : Type} [JSNumber N]

/-- The translator gives `decls` for `m`, from the state `start`. The kernel
can decide this, and a certificate does. -/
def translatesTo (m : Module) (start : Ctx) (decls : List IR.Decl) : Bool :=
  match translateDecls m start with
  | .ok d _ => decide (d = decls)
  | .error _ _ => false

theorem translatesTo_ok {m : Module} {start : Ctx} {decls : List IR.Decl}
    (h : translatesTo m start decls = true) : ∃ finish, translateDecls m start = .ok decls finish := by
  unfold translatesTo at h
  split at h
  · next d finish hd =>
    rw [decide_eq_true_iff] at h
    exact ⟨finish, h ▸ hd⟩
  · simp at h

/-- The translator is sound for one file that imports nothing. When it gives
`decls` for `m`, from a state with the file's name, no functions and no enums, a call
of the output gives a value only when the interpreter gives the same value
for the same call of `m`. -/
theorem decls_sound {file : String} {m : Module} {decls : List IR.Decl} {start : Ctx}
    (hfile : start.file = file) (hfns : (start.functions, start.enums, start.enumValues) = ([], [], []))
    (hifaces : start.interfaces = [])
    (h : translatesTo m start decls = true) (name : String) (args : List (Val N)) (fuel : Nat) (v : Val N)
    (hv : IR.runIn (IR.functionsOf [(file, decls)]) ⟨file, name⟩ args fuel = some v) :
    Eval.runIn [(file, m)] ⟨file, name⟩ args fuel = some v := by
  obtain ⟨finish, hrun⟩ := translatesTo_ok h
  exact program_sound (.snoc false "N" .nil hfile hfns hifaces hrun) (by simp) _ args fuel v hv

/-- A fold of the output and `List.foldl` agree when one run of the body and
one step of the fold agree. A certificate proves a lemma for each loop from
this one. -/
theorem runFold_foldl {α σ : Type} (fs : List (DeclRef × List String × IR.Body)) (fuel : Nat)
    (names : List String) (element : String) (body : IR.Body) (encX : α → Val N)
    (upd : σ → Eval.Env N → Eval.Env N) (dec : Eval.Env N → σ) (step : Eval.Env N → σ → α → σ)
    (I : Eval.Env N → Prop)
    (hbody : ∀ ρ s x, I ρ → ∃ inner,
      IR.Body.exec fs fuel ((element, encX x) :: upd s ρ) body = some (.normal inner) ∧
        IR.bindState names inner (upd s ρ) = some (upd (step ρ s x) ρ))
    (hdec : ∀ ρ, I ρ → upd (dec ρ) ρ = ρ) (xs : List α) (ρ : Eval.Env N) (hI : I ρ) :
    IR.Body.runFold fs fuel names element body ρ (xs.map encX) =
      some (.normal (upd (xs.foldl (step ρ) (dec ρ)) ρ)) := by
  have key : ∀ (xs : List α) (s : σ), IR.Body.runFold fs fuel names element body (upd s ρ) (xs.map encX) =
      some (.normal (upd (xs.foldl (step ρ) s) ρ)) := by
    intro xs
    induction xs with
    | nil => intro s; simp [IR.Body.runFold]
    | cons x xs ih =>
      intro s
      obtain ⟨inner, hex, hb⟩ := hbody ρ s x hI
      simp only [List.map_cons, IR.Body.runFold, hex, hb, Option.bind_eq_bind, Option.bind_some,
        List.foldl_cons]
      exact ih (step ρ s x)
  have := key xs (dec ρ)
  rwa [hdec ρ hI] at this

/-- How one step of `forIn` ends, as the evaluator gives it: a `done` is a
`break`. -/
def stepOutcome {σ : Type} : ForInStep σ → Eval.Env N → Eval.Outcome N
  | .done _, ρ => .brk ρ
  | .yield _, ρ => .normal ρ

/-- A fold of the output whose body can `break`, and `forIn`, agree when one
run of the body and one step of `forIn` agree. A certificate proves a lemma
for each such loop from this one. -/
theorem runFold_forIn {α σ : Type} (fs : List (DeclRef × List String × IR.Body)) (fuel : Nat)
    (names : List String) (element : String) (body : IR.Body) (encX : α → Val N)
    (upd : σ → Eval.Env N → Eval.Env N) (dec : Eval.Env N → σ)
    (step : Eval.Env N → α → σ → ForInStep σ) (I : Eval.Env N → Prop)
    (hbody : ∀ ρ s x, I ρ → ∃ inner,
      IR.Body.exec fs fuel ((element, encX x) :: upd s ρ) body = some (stepOutcome (step ρ x s) inner) ∧
        IR.bindState names inner (upd s ρ) = some (upd (step ρ x s).value ρ))
    (hdec : ∀ ρ, I ρ → upd (dec ρ) ρ = ρ) (xs : List α) (ρ : Eval.Env N) (hI : I ρ) :
    IR.Body.runFold fs fuel names element body ρ (xs.map encX) =
      some (.normal (upd (Id.run (forIn xs (dec ρ) (step ρ))) ρ)) := by
  have key : ∀ (xs : List α) (s : σ), IR.Body.runFold fs fuel names element body (upd s ρ) (xs.map encX) =
      some (.normal (upd (Id.run (forIn xs s (step ρ))) ρ)) := by
    intro xs
    induction xs with
    | nil => intro s; simp [IR.Body.runFold]
    | cons x xs ih =>
      intro s
      obtain ⟨inner, hex, hb⟩ := hbody ρ s x hI
      cases hst : step ρ x s with
      | done s' =>
        rw [hst] at hex hb
        simp only [List.map_cons, IR.Body.runFold, hex, stepOutcome, hb, ForInStep.value,
          Option.bind_eq_bind, Option.bind_some, List.forIn_cons, hst]
        rfl
      | yield s' =>
        rw [hst] at hex hb
        simp only [List.map_cons, IR.Body.runFold, hex, stepOutcome, hb, ForInStep.value,
          Option.bind_eq_bind, Option.bind_some, List.forIn_cons, hst]
        exact ih s'
  have := key xs (dec ρ)
  rwa [hdec ρ hI] at this
/-- A callback of the output and a Lean function agree on the elements of a
list when they agree on each element. A certificate proves a lemma for each
call of `map` from this one. -/
theorem evalMap_map {α β : Type} (fs : List (DeclRef × List String × IR.Body)) (fuel : Nat)
    (ρ : Eval.Env N) (param : String) (body : IR.Expr) (encX : α → Val N) (encY : β → Val N)
    (f : α → β) (hb : ∀ x, IR.Expr.eval fs fuel ((param, encX x) :: ρ) body = some (encY (f x))) :
    ∀ xs : List α, IR.Expr.evalMap fs fuel ρ param body (xs.map encX) = some ((xs.map f).map encY)
  | [] => by simp [IR.Expr.evalMap]
  | x :: xs => by simp [IR.Expr.evalMap, hb x, evalMap_map fs fuel ρ param body encX encY f hb xs]

/-- The same for `List.mapIdx`, whose function also takes the index, where the
first element is at `start`. -/
theorem evalMapIdx_from {α β : Type} (fs : List (DeclRef × List String × IR.Body)) (fuel : Nat)
    (ρ : Eval.Env N) (param index : String) (body : IR.Expr) (encX : α → Val N) (encY : β → Val N)
    (f : Nat → α → β)
    (hb : ∀ (n : Nat) x, IR.Expr.eval fs fuel ((param, encX x) :: (index, .num (JSNumber.ofSafeInt n)) :: ρ) body =
      some (encY (f n x))) :
    ∀ (xs : List α) (start : Nat), IR.Expr.evalMapIdx fs fuel ρ param index body start (xs.map encX) =
      some ((xs.mapIdx fun k => f (start + k)).map encY)
  | [], _ => by simp [IR.Expr.evalMapIdx]
  | x :: xs, start => by
    have key : (fun k => f (start + 1 + k)) = fun k => f (start + (k + 1)) := by
      funext k; congr 1; omega
    simp [IR.Expr.evalMapIdx, hb start x, evalMapIdx_from fs fuel ρ param index body encX encY f hb xs,
      List.mapIdx_cons, key]

/-- A callback of `map` that reads the index and a Lean function agree on the
elements of a list when they agree on each element at each index. -/
theorem evalMapIdx_mapIdx {α β : Type} (fs : List (DeclRef × List String × IR.Body)) (fuel : Nat)
    (ρ : Eval.Env N) (param index : String) (body : IR.Expr) (encX : α → Val N) (encY : β → Val N)
    (f : Nat → α → β)
    (hb : ∀ (n : Nat) x, IR.Expr.eval fs fuel ((param, encX x) :: (index, .num (JSNumber.ofSafeInt n)) :: ρ) body =
      some (encY (f n x)))
    (xs : List α) :
    IR.Expr.evalMapIdx fs fuel ρ param index body 0 (xs.map encX) = some ((xs.mapIdx f).map encY) := by
  simpa using evalMapIdx_from fs fuel ρ param index body encX encY f hb xs 0

/-- The position of the first element for which `body` is true, as
`List.findIdx?` finds it, where the first element is at `start`. -/
theorem evalFindIdx_from {α : Type} (fs : List (DeclRef × List String × IR.Body)) (fuel : Nat)
    (ρ : Eval.Env N) (param : String) (body : IR.Expr) (encX : α → Val N) (p : α → Bool)
    (hb : ∀ x, IR.Expr.eval fs fuel ((param, encX x) :: ρ) body = some (.bool (p x))) :
    ∀ (xs : List α) (start : Nat), IR.Expr.evalFindIdx fs fuel ρ param body start (xs.map encX) =
      some ((xs.findIdx? p).map (· + start))
  | [], _ => by simp [IR.Expr.evalFindIdx]
  | x :: xs, start => by
    simp only [List.map_cons, IR.Expr.evalFindIdx, hb x, Option.bind_eq_bind, Option.bind_some,
      List.findIdx?_cons]
    cases p x
    · simp only [Bool.false_eq_true, if_false, evalFindIdx_from fs fuel ρ param body encX p hb xs (start + 1),
        Option.map_map]
      have key : (fun k => k + (start + 1)) = ((fun k => k + start) ∘ fun i => i + 1) := by
        funext k; simp only [Function.comp_apply]; omega
      simp [key]
    · simp

/-- The same from the first element: `findIndex` is `List.findIdx?`. -/
theorem evalFindIdx_findIdx {α : Type} (fs : List (DeclRef × List String × IR.Body)) (fuel : Nat)
    (ρ : Eval.Env N) (param : String) (body : IR.Expr) (encX : α → Val N) (p : α → Bool)
    (hb : ∀ x, IR.Expr.eval fs fuel ((param, encX x) :: ρ) body = some (.bool (p x))) (xs : List α) :
    IR.Expr.evalFindIdx fs fuel ρ param body 0 (xs.map encX) = some (xs.findIdx? p) := by
  simpa using evalFindIdx_from fs fuel ρ param body encX p hb xs 0

/-- A callback of `reduce` and a Lean function agree on a list when they agree
on each value so far and each element. A certificate proves a lemma for each
call of `reduce` from this one. -/
theorem evalReduce_foldl {α β : Type} (fs : List (DeclRef × List String × IR.Body)) (fuel : Nat)
    (ρ : Eval.Env N) (acc param : String) (body : IR.Expr) (encA : β → Val N) (encX : α → Val N)
    (f : β → α → β)
    (hb : ∀ a x, IR.Expr.eval fs fuel ((param, encX x) :: (acc, encA a) :: ρ) body = some (encA (f a x))) :
    ∀ (xs : List α) (a : β), IR.Expr.evalReduce fs fuel ρ acc param body (encA a) (xs.map encX) =
      some (encA (xs.foldl f a))
  | [], _ => by simp [IR.Expr.evalReduce]
  | x :: xs, a => by
    simp [IR.Expr.evalReduce, hb a x, evalReduce_foldl fs fuel ρ acc param body encA encX f hb xs]

/-- The same, for any initial value `v` that encodes what `dec` reads back from
it. A certificate states its lemma for a callback of `reduce` this way: the
proof that links a function unfolds the encoding of the initial value, such
as `encList Val.int init` to `Val.list (List.map Val.int init)`, so the lemma
must match the unfolded value too. -/
theorem evalReduce_foldl_val {α β : Type} (fs : List (DeclRef × List String × IR.Body)) (fuel : Nat)
    (ρ : Eval.Env N) (acc param : String) (body : IR.Expr) (encA : β → Val N) (encX : α → Val N)
    (f : β → α → β) (dec : Option (Val N) → β)
    (hb : ∀ a x, IR.Expr.eval fs fuel ((param, encX x) :: (acc, encA a) :: ρ) body = some (encA (f a x)))
    (xs : List α) (v : Val N) (hv : encA (dec (some v)) = v) :
    IR.Expr.evalReduce fs fuel ρ acc param body v (xs.map encX) =
      some (encA (xs.foldl f (dec (some v)))) := by
  have := evalReduce_foldl fs fuel ρ acc param body encA encX f hb xs (dec (some v))
  rwa [hv] at this

/-- The same for `filter`. -/
theorem evalFilter_filter {α : Type} (fs : List (DeclRef × List String × IR.Body)) (fuel : Nat)
    (ρ : Eval.Env N) (param : String) (body : IR.Expr) (encX : α → Val N) (p : α → Bool)
    (hb : ∀ x, IR.Expr.eval fs fuel ((param, encX x) :: ρ) body = some (.bool (p x))) :
    ∀ xs : List α, IR.Expr.evalFilter fs fuel ρ param body (xs.map encX) = some ((xs.filter p).map encX)
  | [] => by simp [IR.Expr.evalFilter]
  | x :: xs => by
    simp only [List.map_cons, IR.Expr.evalFilter, hb x, evalFilter_filter fs fuel ρ param body encX p hb xs,
      Option.bind_eq_bind, Option.bind_some, List.filter_cons]
    cases p x <;> simp

/-- The first element for which `body` is `want`, as `List.find?` finds it. -/
theorem evalFind_find {α : Type} (fs : List (DeclRef × List String × IR.Body)) (fuel : Nat)
    (ρ : Eval.Env N) (param : String) (body : IR.Expr) (encX : α → Val N) (p : α → Bool) (want : Bool)
    (hb : ∀ x, IR.Expr.eval fs fuel ((param, encX x) :: ρ) body = some (.bool (p x))) :
    ∀ xs : List α, IR.Expr.evalFind fs fuel ρ param body want (xs.map encX) =
      some ((xs.find? fun x => p x == want).map encX)
  | [] => by simp [IR.Expr.evalFind]
  | x :: xs => by
    simp only [List.map_cons, IR.Expr.evalFind, hb x, Option.bind_eq_bind, Option.bind_some, List.find?_cons]
    cases p x == want
    · simp [evalFind_find fs fuel ρ param body encX p want hb xs]
    · simp

/-- The same for `find` and `some`, which stop at the first element that passes. -/
theorem evalFind_true {α : Type} (fs : List (DeclRef × List String × IR.Body)) (fuel : Nat)
    (ρ : Eval.Env N) (param : String) (body : IR.Expr) (encX : α → Val N) (p : α → Bool)
    (hb : ∀ x, IR.Expr.eval fs fuel ((param, encX x) :: ρ) body = some (.bool (p x))) (xs : List α) :
    IR.Expr.evalFind fs fuel ρ param body true (xs.map encX) = some ((xs.find? p).map encX) := by
  simpa using evalFind_find fs fuel ρ param body encX p true hb xs

/-- The same for `every`, which stops at the first element that fails. -/
theorem evalFind_false {α : Type} (fs : List (DeclRef × List String × IR.Body)) (fuel : Nat)
    (ρ : Eval.Env N) (param : String) (body : IR.Expr) (encX : α → Val N) (p : α → Bool)
    (hb : ∀ x, IR.Expr.eval fs fuel ((param, encX x) :: ρ) body = some (.bool (p x))) (xs : List α) :
    IR.Expr.evalFind fs fuel ρ param body false (xs.map encX) =
      some ((xs.find? fun x => !p x).map encX) := by
  simpa using evalFind_find fs fuel ρ param body encX p false hb xs

/-- `some` is `List.any`. -/
@[simp] theorem find?_isSome {α : Type} (p : α → Bool) (xs : List α) :
    (xs.find? p).isSome = xs.any p := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases h : p x <;> simp_all

/-- `every` is `List.all`. -/
@[simp] theorem find?_not_isNone {α : Type} (p : α → Bool) (xs : List α) :
    (xs.find? fun x => !p x).isNone = xs.all p := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases h : p x <;> simp_all

omit [JSNumber N] in
/-- `find` gives `undefined` when no element passes, as an optional value does. -/
@[simp] theorem getD_map_undefined {α : Type} (enc : α → Val N) (o : Option α) :
    (o.map enc).getD .undefined = Eval.encUndef enc o := by
  cases o <;> rfl

/-- How one step of `forIn` ends in a loop that a `return` can end, where
`getRet` reads the value to return from the state: with one, a `done` is a
`return`, and without one it is a `break`. -/
def retOutcome {R τ : Type} (encR : R → Val N) (getRet : τ → Option R) :
    ForInStep τ → Eval.Env N → Eval.Outcome N
  | .done t, ρ => match getRet t with
    | some r => .ret (.ok (encR r))
    | none => .brk ρ
  | .yield _, ρ => .normal ρ

/-- What a loop that a `return` can end gives for its final state `t`: the
value to return, or the locals at its end. -/
def retResult {R σ τ : Type} (encR : R → Val N) (getRet : τ → Option R) (getS : τ → σ)
    (upd : σ → Eval.Env N → Eval.Env N) (ρ : Eval.Env N) (t : τ) : Eval.Outcome N :=
  match getRet t with
  | some r => .ret (.ok (encR r))
  | none => .normal (upd (getS t) ρ)

/-- A fold of the output whose body can `return`, and `forIn`, agree when one
run of the body and one step of `forIn` agree. The state of `forIn` holds
the value to return, which `getRet` reads, and the locals, which `getS`
reads; `init` starts it with no value. A certificate proves a lemma for each
such loop from this one. -/
theorem runFold_forInRet {α σ τ R : Type} (fs : List (DeclRef × List String × IR.Body)) (fuel : Nat)
    (names : List String) (element : String) (body : IR.Body) (encX : α → Val N) (encR : R → Val N)
    (getRet : τ → Option R) (getS : τ → σ) (init : σ → τ)
    (upd : σ → Eval.Env N → Eval.Env N) (dec : Eval.Env N → σ)
    (step : Eval.Env N → α → τ → ForInStep τ) (I : Eval.Env N → Prop)
    (hinit : ∀ s, getRet (init s) = none ∧ getS (init s) = s)
    (hbody : ∀ ρ s x, I ρ → ∃ inner,
      IR.Body.exec fs fuel ((element, encX x) :: upd s ρ) body =
        some (retOutcome encR getRet (step ρ x (init s)) inner) ∧
      (getRet (step ρ x (init s)).value = none →
        IR.bindState names inner (upd s ρ) = some (upd (getS (step ρ x (init s)).value) ρ)) ∧
      ∀ t, step ρ x (init s) = .yield t → t = init (getS t) ∧ getRet t = none)
    (hdec : ∀ ρ, I ρ → upd (dec ρ) ρ = ρ) (xs : List α) (ρ : Eval.Env N) (hI : I ρ) :
    IR.Body.runFold fs fuel names element body ρ (xs.map encX) =
      some (retResult encR getRet getS upd ρ (Id.run (forIn xs (init (dec ρ)) (step ρ)))) := by
  have key : ∀ (xs : List α) (s : σ), IR.Body.runFold fs fuel names element body (upd s ρ) (xs.map encX) =
      some (retResult encR getRet getS upd ρ (Id.run (forIn xs (init s) (step ρ)))) := by
    intro xs
    induction xs with
    | nil => intro s; simp [IR.Body.runFold, retResult, (hinit s).1, (hinit s).2]
    | cons x xs ih =>
      intro s
      obtain ⟨inner, hex, hb, hy⟩ := hbody ρ s x hI
      cases hst : step ρ x (init s) with
      | done t =>
        rw [hst] at hex hb
        cases hr : getRet t with
        | some r =>
          simp only [List.map_cons, IR.Body.runFold, hex, retOutcome, hr, Option.bind_eq_bind,
            Option.bind_some, List.forIn_cons, hst]
          simp [retResult, hr]
        | none =>
          simp only [ForInStep.value] at hb
          simp only [List.map_cons, IR.Body.runFold, hex, retOutcome, hr, hb hr, Option.bind_eq_bind,
            Option.bind_some, List.forIn_cons, hst]
          simp [retResult, hr]
      | yield t =>
        obtain ⟨ht, hr⟩ := hy t hst
        rw [hst] at hex hb
        simp only [ForInStep.value] at hb
        have hstep : Id.run (forIn (x :: xs) (init s) (step ρ)) = Id.run (forIn xs t (step ρ)) := by
          simp [List.forIn_cons, hst]
        rw [hstep]
        simp only [List.map_cons, IR.Body.runFold, hex, retOutcome, hb hr, Option.bind_eq_bind,
          Option.bind_some]
        have := ih (getS t)
        rwa [← ht] at this
  have := key xs (dec ρ)
  rwa [hdec ρ hI] at this

/-- `includes` on the encoded elements of a list, when SameValueZero of `v`
and each element is a test `p` of the element. -/
theorem includesVal_map {α : Type} (enc : α → Val N) (v : Val N) (p : α → Bool)
    (h : ∀ y, Eval.sameValueZero v (enc y) = some (p y)) :
    ∀ xs : List α, Eval.includesVal v (xs.map enc) = some (xs.any p)
  | [] => by simp [Eval.includesVal]
  | y :: ys => by
    simp only [List.map_cons, Eval.includesVal, h y, Option.bind_eq_bind, Option.bind_some, List.any_cons]
    cases p y
    · simp [includesVal_map enc v p h ys]
    · simp

/-- `includes` of `v` is membership of `x`, when `v` is the same as the
encoding of an element exactly when the element is `x`. A certificate states
it for each constructor of a literal union. -/
theorem includesVal_enc {α : Type} [DecidableEq α] (enc : α → Val N) (v : Val N) (x : α)
    (h : ∀ y, Eval.sameValueZero v (enc y) = some (decide (y = x))) (xs : List α) :
    Eval.includesVal v (xs.map enc) = some (decide (x ∈ xs)) := by
  rw [includesVal_map enc v _ h]
  induction xs with
  | nil => simp
  | cons y ys ih => by_cases hy : y = x <;> simp_all [eq_comm]

@[simp] theorem includesVal_int (x : Int) (xs : List Int) :
    Eval.includesVal (N := N) (.int x) (xs.map .int) = some (decide (x ∈ xs)) :=
  includesVal_enc _ _ _ (fun y => by simp [Eval.sameValueZero, Eval.strictEq, eq_comm]) xs

@[simp] theorem includesVal_bool (x : Bool) (xs : List Bool) :
    Eval.includesVal (N := N) (.bool x) (xs.map .bool) = some (decide (x ∈ xs)) :=
  includesVal_enc _ _ _ (fun y => by simp [Eval.sameValueZero, Eval.strictEq, eq_comm]) xs

@[simp] theorem includesVal_str (x : JSString) (xs : List JSString) :
    Eval.includesVal (N := N) (.str x) (xs.map .str) = some (decide (x ∈ xs)) :=
  includesVal_enc _ _ _ (fun y => by simp [Eval.sameValueZero, Eval.strictEq, eq_comm]) xs

@[simp] theorem includesVal_num (x : N) (xs : List N) :
    Eval.includesVal (.num x) (xs.map .num) = some (xs.any (JSNumber.sameValueZero x)) :=
  includesVal_map _ _ _ (fun _ => rfl) xs

omit [JSNumber N] in
/-- The element of an encoded list at an integer index. -/
@[simp] theorem elementAt_map_some {α : Type} (enc : α → Val N) (xs : List α) (k : Int) :
    Eval.elementAt (xs.map enc) (some k) = Eval.encUndef enc (if 0 ≤ k then xs[k.toNat]? else none) := by
  by_cases hk : 0 ≤ k
  · simp only [Eval.elementAt, hk, if_true, List.getElem?_map]
    cases xs[k.toNat]? <;> rfl
  · simp [Eval.elementAt, hk]

omit [JSNumber N] in
/-- The element of a list literal at an integer index, one step at a time, as
a pattern on a literal reads it. -/
@[simp] theorem elementAt_cons (x : Val N) (xs : List (Val N)) (k : Int) :
    Eval.elementAt (x :: xs) (some k) =
      if k = 0 then x else if 0 < k then Eval.elementAt xs (some (k - 1)) else .undefined := by
  simp only [Eval.elementAt]
  by_cases h0 : k = 0
  · subst h0; simp
  · by_cases hp : 0 < k
    · have h1 : 0 ≤ k - 1 := by omega
      have h2 : k.toNat = (k - 1).toNat + 1 := by omega
      rw [if_pos (Int.le_of_lt hp), if_neg h0, if_pos hp, if_pos h1, h2, List.getElem?_cons_succ]
    · have h3 : ¬ 0 ≤ k := by omega
      simp [h0, hp, h3]

/-- `xs[i]` with a number `i`, on an encoded list. -/
@[simp] theorem elementAt_map_toSafeInt {α : Type} (enc : α → Val N) (xs : List α) (i : N) :
    Eval.elementAt (xs.map enc) (JSNumber.toSafeInt i) = Eval.encUndef enc (JSNumber.elementAt? xs i) := by
  unfold JSNumber.elementAt?
  cases JSNumber.toSafeInt i with
  | none => rfl
  | some k => exact elementAt_map_some enc xs k

omit [JSNumber N] in
/-- `xs.at(k)` on an encoded list: a negative `k` counts from the end, which
is an index of the reversed list. -/
@[simp] theorem atVal_map {α : Type} (enc : α → Val N) (xs : List α) (k : Int) :
    Eval.atVal (xs.map enc) k =
      Eval.encUndef enc (if 0 ≤ k then xs[k.toNat]? else xs.reverse[(-k - 1).toNat]?) := by
  unfold Eval.atVal
  by_cases hk : 0 ≤ k
  · simp only [hk, if_true, elementAt_map_some]
  · simp only [hk, if_false, elementAt_map_some, List.length_map]
    congr 1
    by_cases hl : 0 ≤ (xs.length : Int) + k
    · have hlt : (-k - 1).toNat < xs.length := by omega
      rw [if_pos hl, List.getElem?_reverse hlt]
      congr 1
      omega
    · rw [if_neg hl, eq_comm, List.getElem?_eq_none]
      simp only [List.length_reverse]
      omega

/-- `slice` on an encoded list is `slice` on the list, encoded. It comes before
the lemmas for each kind of bound, so that the list keeps the shape
`List.map enc xs` that the lemmas of callbacks match. -/
@[simp high] theorem sliceList_map {α β : Type} (f : α → β) (xs : List α) (start : Int) (stop : Option Int) :
    Eval.sliceList (xs.map f) start stop = (Eval.sliceList xs start stop).map f := by
  simp [Eval.sliceList, List.map_take, List.map_drop]

/-- An element of a reversed list, with no side condition. -/
theorem getElem?_rev {α : Type} (l : List α) (i : Nat) :
    l.reverse[i]? = if i < l.length then l[l.length - 1 - i]? else none := by
  split
  · exact List.getElem?_reverse ‹_›
  · rw [List.getElem?_eq_none]; simp; omega

/-- The elements of two slices agree at every index. -/
macro "slice_tac" : tactic => `(tactic| (
  apply List.ext_getElem?
  intro i
  simp only [Eval.sliceList, Eval.relIndex, List.getElem?_take, List.getElem?_drop, getElem?_rev,
    List.length_take, List.length_drop, List.length_reverse]
  repeat' split
  all_goals first
    | rfl
    | omega
    | (congr 1; omega)
    | (rw [List.getElem?_eq_none (by omega)])
    | (rw [eq_comm, List.getElem?_eq_none (by omega)])
    | (rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)])))

/-- `slice` with bounds that are not negative. -/
@[simp] theorem sliceList_nonneg {α : Type} (xs : List α) (k e : Int) (hk : 0 ≤ k) (he : 0 ≤ e) :
    Eval.sliceList xs k (some e) = (xs.take e.toNat).drop k.toNat := by
  slice_tac

/-- `slice` with a start that is not negative and no end. -/
@[simp] theorem sliceList_from {α : Type} (xs : List α) (k : Int) (hk : 0 ≤ k) :
    Eval.sliceList xs k none = xs.drop k.toNat := by
  slice_tac

/-- `slice` with a negative start and no end: the last elements. -/
@[simp] theorem sliceList_last {α : Type} (xs : List α) (k : Int) (hk : k < 0) :
    Eval.sliceList xs k none = (xs.reverse.take (-k).toNat).reverse := by
  slice_tac

/-- `slice` with a start that is not negative and a negative end. -/
@[simp] theorem sliceList_dropLast {α : Type} (xs : List α) (k e : Int) (hk : 0 ≤ k) (he : e < 0) :
    Eval.sliceList xs k (some e) = ((xs.reverse.drop (-e).toNat).reverse).drop k.toNat := by
  slice_tac

/-- `slice` with a negative start and an end that is not negative: the start
counts back from the length. -/
@[simp] theorem sliceList_mixed {α : Type} (xs : List α) (k e : Int) (hk : k < 0) (he : 0 ≤ e) :
    Eval.sliceList xs k (some e) = (xs.take e.toNat).drop (xs.length - (-k).toNat) := by
  slice_tac

/-- `slice` with two negative bounds. -/
@[simp] theorem sliceList_neg {α : Type} (xs : List α) (k e : Int) (hk : k < 0) (he : e < 0) :
    Eval.sliceList xs k (some e) = ((xs.reverse.take (-k).toNat).drop (-e).toNat).reverse := by
  slice_tac

/-! ### Certificates: sorts -/

/-- A comparator is consistent for every list when its signs are those of a
lawful comparison: one that `Std.TransCmp` says is a total preorder. -/
theorem consistentOn_of_transCmp {α : Type} {cmp : α → α → Option Ordering} (o : α → α → Ordering)
    [Std.TransCmp o] (h : ∀ a b, cmp a b = some (o a b)) (xs : List α) :
    Eval.consistentOn cmp xs = true := by
  unfold Eval.consistentOn
  simp only [List.all_eq_true]
  intro a _ b _
  simp only [h, Option.isSome_some, Option.map_some, beq_iff_eq, Option.some.injEq, Bool.true_and,
    Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true']
  refine ⟨Std.OrientedCmp.eq_swap, fun c _ => ?_⟩
  by_cases hab : o a b = .gt
  · simp [hab]
  by_cases hbc : o b c = .gt
  · simp [hbc]
  right
  have hle : ∀ x : Ordering, x ≠ .gt → x.isLE = true := by decide
  have := Std.TransCmp.isLE_trans (hle _ hab) (hle _ hbc)
  cases hac : o a c <;> simp_all

/-- A sort of encoded values and `JSNumber.sortWith` agree, when the body of
the comparator gives the number `cmp x y`, when no encoded value is
`undefined`, and when the comparator is consistent for every list. A
certificate proves a lemma for each sort from this one. -/
theorem sortValues_sortWith {α : Type} (fs : List (DeclRef × List String × IR.Body)) (fuel : Nat)
    (ρ : Eval.Env N) (param other : String) (body : IR.Expr) (encX : α → Val N) (cmp : α → α → N)
    (hb : ∀ x y, IR.Expr.eval fs fuel ((param, encX x) :: (other, encX y) :: ρ) body = some (.num (cmp x y)))
    (hu : ∀ x, encX x ≠ .undefined)
    (hc : ∀ xs : List α, Eval.consistentOn (fun x y => JSNumber.compareSign (cmp x y)) xs = true)
    (xs : List α) :
    Eval.sortValues (IR.Expr.evalCompare fs fuel ρ param other body) (xs.map encX) =
      some ((JSNumber.sortWith cmp xs).map encX) := by
  have he : ∀ x y, IR.Expr.evalCompare fs fuel ρ param other body (encX x) (encX y) =
      JSNumber.compareSign (cmp x y) := by
    intro x y
    have hx := hu x
    have hy := hu y
    unfold IR.Expr.evalCompare
    split
    · contradiction
    · contradiction
    · contradiction
    · rw [hb x y]; rfl
  have hcons : Eval.consistentOn (IR.Expr.evalCompare fs fuel ρ param other body) (xs.map encX) = true := by
    have := hc xs
    unfold Eval.consistentOn at this ⊢
    simpa [List.all_map, he] using this
  unfold Eval.sortValues JSNumber.sortWith
  rw [if_pos hcons, List.map_mergeSort (s := fun a b => IR.Expr.evalCompare fs fuel ρ param other body a b != some .gt)
    (fun a _ b _ => by simp only [he])]

theorem int_compare_of_lt {a b : Int} (h : a < b) : compare a b = .lt := Int.compare_eq_lt.mpr h
theorem int_compare_of_gt {a b : Int} (h : b < a) : compare a b = .gt := Int.compare_eq_gt.mpr h
theorem int_compare_of_eq {a b : Int} (h1 : ¬a < b) (h2 : ¬b < a) : compare a b = .eq :=
  Int.compare_eq_eq.mpr (by omega)

/-- `JSNumber.sliceInt` on an encoded list, which the output calls for a slice
with a bound that is not a literal. -/
@[simp high] theorem sliceInt_map {α β : Type} (f : α → β) (xs : List α) (a : Int) (b : Option Int) :
    JSNumber.sliceInt (xs.map f) a b = (JSNumber.sliceInt xs a b).map f := by
  simp [JSNumber.sliceInt, List.map_take, List.map_drop]

/-- `xs.at(i)` with a number `i`, on an encoded list: `JSNumber.atIndex?`,
which the output calls. It comes before `atVal_map`, which would write the
index out. -/
@[simp high] theorem atVal_map_toIndexInt {α : Type} (enc : α → Val N) (xs : List α) (i : N) :
    Eval.atVal (xs.map enc) (JSNumber.toIndexInt i) = Eval.encUndef enc (JSNumber.atIndex? xs i) := by
  rw [atVal_map]
  rfl

end tolean.TypeScript.Proof

/-- The proof that the sign of a comparator of keys is a lexicographic
comparison of the keys, for every two elements: split on each test of the
comparator, and compare the keys in each branch. -/
syntax "sort_tac" : tactic
macro_rules
  | `(tactic| sort_tac) =>
    `(tactic| (
      intro a b
      try simp only []
      repeat' split
      all_goals simp_all [tolean.TypeScript.compareSign_one, tolean.TypeScript.compareSign_zero,
        tolean.TypeScript.compareSign_neg_one, tolean.TypeScript.compareSign_neg_zero, compareLex, compareOn, Ordering.then,
        tolean.TypeScript.JSString.compare_of_lt, tolean.TypeScript.JSString.compare_of_gt,
        tolean.TypeScript.JSString.compare_of_eq, tolean.TypeScript.Proof.int_compare_of_lt,
        tolean.TypeScript.Proof.int_compare_of_gt, tolean.TypeScript.Proof.int_compare_of_eq]))

namespace tolean.TypeScript.IR

open Lean Elab Tactic Meta in
/-- Split on the value of a `List.find? p xs` in the goal, the value of a
call of `find`. The evaluator reads that value only through a `match`, which
`split` cannot take apart until it knows whether the value is `some`. -/
elab "split_find" : tactic => withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  let some e := target.find? fun e => e.isAppOfArity ``List.find? 3 && !e.hasLooseBVars
    | throwError "split_find: no List.find? in the goal"
  let stx ← Term.exprToSyntax e
  evalTactic (← `(tactic| cases _ : $stx))

open Lean Elab Tactic Meta in
/-- Split on an element that the goal reads from a list, such as `xs[0]?` or
`JSNumber.elementAt? xs i` or `JSNumber.atIndex? xs i`, where the evaluator
encodes it with `encUndef`.
The value is `undefined` when there is no element, so the evaluator and the
printed definition read it only through a `match`, as for `find`. -/
elab "split_undef" : tactic => withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  let some e := target.find? fun e =>
      e.isAppOf ``tolean.TypeScript.Eval.encUndef && e.getAppNumArgs > 0 &&
        (e.appArg!.isAppOf ``GetElem?.getElem? || e.appArg!.isAppOf ``tolean.TypeScript.JSNumber.elementAt? ||
          e.appArg!.isAppOf ``tolean.TypeScript.JSNumber.atIndex?) &&
        !e.hasLooseBVars
    | throwError "split_undef: no element of a list in the goal"
  let stx ← Term.exprToSyntax e.appArg!
  evalTactic (← `(tactic| cases _ : $stx))

/-- The proof of a link theorem: unfold the IR's evaluator on the IR and the
printed definitions, then split on each branch. `defs` names the IR, the
encoders, the printed definitions and the loop lemmas. -/
syntax "link_tac" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
-- `simp` would fold the printed `if c then true else b` into `decide c || b`,
-- which `split` cannot take apart, so those four lemmas stay out.
macro_rules
  | `(tactic| link_tac [$defs,*]) =>
    `(tactic| (
      simp [runIn, callIn, Except.toOption, functionsOf, functions, Body.exec, Body.runFold, Expr.eval,
        Expr.evalCall, Expr.evalList,
        Expr.evalFields, Expr.evalMap, Expr.evalMapIdx, Expr.evalFilter, Expr.evalFind, Expr.evalFindIdx, Expr.evalReduce,
        bindState, eqVal, ← List.map_reverse,
        -- `includes` on an array literal compares with `===` once the list
        -- has reduced, so strict equality on primitives must reduce too.
        Eval.includesVal, Eval.sameValueZero, Eval.strictEq, Eval.setProp,
        tolean.IR.IntOp.apply, tolean.IR.Order.apply,
        tolean.IR.Division.apply, ExprExt.apply, listItems?, StringPart.toStr, StringMethod.apply, Eval.oneString, Eval.noArgs, NumberOp.apply, NumberConstant.value,
        NumberTest.apply, tagOf, Eval.Val.typeOf, Eval.Env.set, Eval.getProp, Eval.getKey_ofString, Eval.getPath,
        Eval.objectPrototypeNames, List.lookup, DeclRef.beq_def, -List.map_map, -List.map_tail, ← List.map_drop, ← List.map_take, ← List.map_reverse, ← List.map_append,
        -- A map or set read, such as the initial value of a `reduce`, must
        -- reach a value before a fold lemma can rewrite the call that uses it.
        -- So must the map or set that the read looks in, when `new Map(items)`
        -- or `new Set(items)` makes it.
        Eval.mapFind, Eval.setHas, Eval.mapOfItems, Eval.setOfItems, Eval.mapSet, Eval.setAdd,
        Eval.sameKey, Eval.storedKey,
        -- The output's side of such a read, in the model of `Map.lean`. On a
        -- key with decidable equality it reduces without these, but not on a
        -- `number` key, which stays abstract.
        JSMap.has, JSMap.get?, JSMap.ofList, JSMap.set, JSMap.empty,
        JSSet.has, JSSet.ofList, JSSet.add, JSSet.empty,
        JSKey.same_ofDecidableEq, JSKey.stored_ofDecidableEq, JSKey.same_ofJSNumber, JSKey.stored_ofJSNumber,
        -Bool.if_true_left, -Bool.if_false_right, -Bool.if_false_left, -Bool.if_true_right, $defs,*]
      all_goals repeat' (split_find <;> simp [-List.map_map, -List.map_tail, ← List.map_drop, ← List.map_take, ← List.map_reverse, ← List.map_append, $defs,*])
      all_goals repeat' (split_undef <;> simp [-List.map_map, -List.map_tail, ← List.map_drop, ← List.map_take, ← List.map_reverse, ← List.map_append, $defs,*])
      all_goals repeat' (split <;> (try simp_all [bindState, eqVal, tolean.IR.IntOp.apply,
        tolean.IR.Order.apply, tolean.IR.Division.apply, ExprExt.apply, listItems?, StringPart.toStr, StringMethod.apply, Eval.oneString, Eval.noArgs, NumberOp.apply,
        NumberTest.apply, tagOf, Eval.Val.typeOf, Eval.Env.set, Eval.getProp, Eval.getKey_ofString, Eval.getPath,
        Eval.objectPrototypeNames, List.lookup, DeclRef.beq_def, -List.map_map, -List.map_tail, ← List.map_drop, ← List.map_take, ← List.map_reverse, ← List.map_append,
        -Bool.if_true_left, -Bool.if_false_right, -Bool.if_false_left, -Bool.if_true_right, $defs,*]))
      all_goals (try simp_all [bindState, eqVal, Eval.Env.set, Eval.getProp, Eval.getKey_ofString, Eval.getPath, Eval.objectPrototypeNames, List.lookup, DeclRef.beq_def, -List.map_map, -List.map_tail, ← List.map_drop, ← List.map_take, ← List.map_reverse, ← List.map_append, $defs,*])
      -- The steps above keep `List.map enc (xs ++ ys)` whole, so that a fold
      -- lemma can rewrite a loop over an array with a spread. Where an
      -- encoded literal stands beside it, the two sides agree once the map
      -- splits again.
      all_goals (try simp [List.map_append])
      -- Two `match`es that differ only in their auxiliary functions, as a
      -- loop lemma's step and the printed definition can, agree by `rfl`.
      all_goals (try rfl)))

open Lean Meta Elab Tactic in
/-- For two hypotheses `h₁ : a = b` and `h₂ : a' = b'`, where `a` and `a'`
apply the same function and agree by unfolding, add `b = b'`. A loop lemma's
step and the printed definition's step are such a pair when they hold a
`match`, because each `match` has its own auxiliary function. After a split
on the result of each loop, this lets `simp_all` see that the two results
are the same. -/
elab "link_eqs" : tactic => withMainContext do
  let hyps ← getLocalHyps
  let mut facts : Array Lean.Expr := #[]
  -- One fact for each pair: both directions would make `simp_all` loop.
  for i in [0:hyps.size] do
    for j in [i + 1:hyps.size] do
      let h₁ := hyps[i]!
      let h₂ := hyps[j]!
      let some (_, a, _) := (← instantiateMVars (← inferType h₁)).eq? | continue
      let some (_, a', _) := (← instantiateMVars (← inferType h₂)).eq? | continue
      if a == a' || !a.getAppFn.isConst || a.getAppFn != a'.getAppFn then continue
      if ← withNewMCtxDepth (isDefEq a a') then
        facts := facts.push (← mkEqTrans (← mkEqSymm h₁) h₂)
  let mut g ← getMainGoal
  for p in facts do
    let (_, g') ← (← g.assert `link_eq (← inferType p) p).intro1P
    g := g'
  replaceMainGoal [g]

end tolean.TypeScript.IR
