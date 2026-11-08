import Lean
import tolean.TypeScript.Proof.Module
import tolean.TypeScript.IR.Equality

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
`decls` for `m`, from a state with the file's name and no functions, a call
of the output gives a value only when the interpreter gives the same value
for the same call of `m`. -/
theorem decls_sound {file : String} {m : Module} {decls : List IR.Decl} {start : Ctx}
    (hfile : start.file = file) (hfns : start.functions = []) (hifaces : start.interfaces = [])
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
      some (upd (xs.foldl (step ρ) (dec ρ)) ρ) := by
  have key : ∀ (xs : List α) (s : σ), IR.Body.runFold fs fuel names element body (upd s ρ) (xs.map encX) =
      some (upd (xs.foldl (step ρ) s) ρ) := by
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
      some (upd (Id.run (forIn xs (dec ρ) (step ρ))) ρ) := by
  have key : ∀ (xs : List α) (s : σ), IR.Body.runFold fs fuel names element body (upd s ρ) (xs.map encX) =
      some (upd (Id.run (forIn xs s (step ρ))) ρ) := by
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
      simp [runIn, functionsOf, functions, Body.exec, Body.runFold, Expr.eval, Expr.evalList,
        Expr.evalFields, Expr.evalMap, Expr.evalFilter, Expr.evalFind, bindState, eqVal,
        tolean.IR.IntOp.apply, tolean.IR.Order.apply,
        tolean.IR.Division.apply, ExprExt.apply, NumberOp.apply, NumberConstant.value,
        NumberTest.apply, tagOf, Eval.Val.typeOf, Eval.Env.set, Eval.getProp, Eval.getKey,
        Eval.objectPrototypeNames, List.lookup, DeclRef.beq_def, -List.map_map,
        -Bool.if_true_left, -Bool.if_false_right, -Bool.if_false_left, -Bool.if_true_right, $defs,*]
      all_goals repeat' (split_find <;> simp [-List.map_map, $defs,*])
      all_goals repeat' (split <;> (try simp_all [bindState, eqVal, tolean.IR.IntOp.apply,
        tolean.IR.Order.apply, tolean.IR.Division.apply, ExprExt.apply, NumberOp.apply,
        NumberTest.apply, tagOf, Eval.Val.typeOf, Eval.Env.set, Eval.getProp, Eval.getKey,
        Eval.objectPrototypeNames, List.lookup, DeclRef.beq_def, -List.map_map,
        -Bool.if_true_left, -Bool.if_false_right, -Bool.if_false_left, -Bool.if_true_right, $defs,*]))
      all_goals (try simp_all [bindState, eqVal, Eval.Env.set, Eval.getProp, Eval.getKey, Eval.objectPrototypeNames, List.lookup, DeclRef.beq_def, -List.map_map, $defs,*])
      -- Two `match`es that differ only in their auxiliary functions, as a
      -- loop lemma's step and the printed definition can, agree by `rfl`.
      all_goals (try rfl)))

end tolean.TypeScript.IR
