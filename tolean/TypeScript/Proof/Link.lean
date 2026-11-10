import Lean
import tolean.TypeScript.Proof.Module
import tolean.TypeScript.IR.Equality
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

end tolean.TypeScript.Proof

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
        tolean.IR.IntOp.apply, tolean.IR.Order.apply,
        tolean.IR.Division.apply, ExprExt.apply, StringPart.toStr, StringMethod.apply, Eval.oneString, NumberOp.apply, NumberConstant.value,
        NumberTest.apply, tagOf, Eval.Val.typeOf, Eval.Env.set, Eval.getProp, Eval.getKey_ofString, Eval.getPath,
        Eval.objectPrototypeNames, List.lookup, DeclRef.beq_def, -List.map_map,
        -Bool.if_true_left, -Bool.if_false_right, -Bool.if_false_left, -Bool.if_true_right, $defs,*]
      all_goals repeat' (split_find <;> simp [-List.map_map, ← List.map_reverse, $defs,*])
      all_goals repeat' (split <;> (try simp_all [bindState, eqVal, tolean.IR.IntOp.apply,
        tolean.IR.Order.apply, tolean.IR.Division.apply, ExprExt.apply, StringPart.toStr, StringMethod.apply, Eval.oneString, NumberOp.apply,
        NumberTest.apply, tagOf, Eval.Val.typeOf, Eval.Env.set, Eval.getProp, Eval.getKey_ofString, Eval.getPath,
        Eval.objectPrototypeNames, List.lookup, DeclRef.beq_def, -List.map_map,
        -Bool.if_true_left, -Bool.if_false_right, -Bool.if_false_left, -Bool.if_true_right, $defs,*]))
      all_goals (try simp_all [bindState, eqVal, Eval.Env.set, Eval.getProp, Eval.getKey_ofString, Eval.getPath, Eval.objectPrototypeNames, List.lookup, DeclRef.beq_def, -List.map_map, $defs,*])
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
