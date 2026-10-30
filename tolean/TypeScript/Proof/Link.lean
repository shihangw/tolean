import tolean.TypeScript.Proof.Module
import tolean.TypeScript.Output.Equality

/-!
The printer link for one file.

`translate_sound` is about the output tree, so it trusts the printer: that the
printed Lean computes what `Output/Eval.lean` gives for the tree. A
certificate closes that gap for its file. It holds the tree as a Lean term,
and the kernel checks with `translatesTo` that the translator gives that tree
for the parsed program. Then one theorem for each function states that the
printed definition computes what the evaluator gives for the tree, and
`decls_sound` carries it to the interpreter. So the file is proved with no
trust in the translator or in the printer.
-/
namespace tolean.TypeScript.Proof

open tolean.TypeScript tolean.TypeScript.Syntax tolean.TypeScript.Translate
open tolean.TypeScript.Eval (Val)

variable {N : Type} [JSNumber N]

/-- The translator gives `decls` for `m`, from the state `start`. The kernel
can decide this, and a certificate does. -/
def translatesTo (m : Module) (start : Ctx) (decls : List Output.Decl) : Bool :=
  match translateDecls m start with
  | .ok d _ => decide (d = decls)
  | .error _ _ => false

theorem translatesTo_ok {m : Module} {start : Ctx} {decls : List Output.Decl}
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
theorem decls_sound {file : String} {m : Module} {decls : List Output.Decl} {start : Ctx}
    (hfile : start.file = file) (hfns : start.functions = []) (hifaces : start.interfaces = [])
    (h : translatesTo m start decls = true) (name : String) (args : List (Val N)) (fuel : Nat) (v : Val N)
    (hv : Output.runIn (Output.functionsOf [(file, decls)]) ⟨file, name⟩ args fuel = some v) :
    Eval.runIn [(file, m)] ⟨file, name⟩ args fuel = some v := by
  obtain ⟨finish, hrun⟩ := translatesTo_ok h
  exact program_sound (.snoc false "N" .nil hfile hfns hifaces hrun) (by simp) _ args fuel v hv

/-- A fold of the output and `List.foldl` agree when one run of the body and
one step of the fold agree. A certificate proves a lemma for each loop from
this one. -/
theorem runFold_foldl {α σ : Type} (fs : List (DeclRef × List String × Output.Body)) (fuel : Nat)
    (names : List String) (element : String) (body : Output.Body) (encX : α → Val N)
    (upd : σ → Eval.Env N → Eval.Env N) (dec : Eval.Env N → σ) (step : Eval.Env N → σ → α → σ)
    (I : Eval.Env N → Prop)
    (hbody : ∀ ρ s x, I ρ → ∃ inner,
      Output.Body.exec fs fuel ((element, encX x) :: upd s ρ) body = some (.normal inner) ∧
        Output.bindState names inner (upd s ρ) = some (upd (step ρ s x) ρ))
    (hdec : ∀ ρ, I ρ → upd (dec ρ) ρ = ρ) (xs : List α) (ρ : Eval.Env N) (hI : I ρ) :
    Output.Body.runFold fs fuel names element body ρ (xs.map encX) =
      some (upd (xs.foldl (step ρ) (dec ρ)) ρ) := by
  have key : ∀ (xs : List α) (s : σ), Output.Body.runFold fs fuel names element body (upd s ρ) (xs.map encX) =
      some (upd (xs.foldl (step ρ) s) ρ) := by
    intro xs
    induction xs with
    | nil => intro s; simp [Output.Body.runFold]
    | cons x xs ih =>
      intro s
      obtain ⟨inner, hex, hb⟩ := hbody ρ s x hI
      simp only [List.map_cons, Output.Body.runFold, hex, hb, Option.bind_eq_bind, Option.bind_some,
        List.foldl_cons]
      exact ih (step ρ s x)
  have := key xs (dec ρ)
  rwa [hdec ρ hI] at this

end tolean.TypeScript.Proof

namespace tolean.TypeScript.Output

/-- The proof of a link theorem: unfold the output's evaluator on the tree and
the printed definitions, then split on each branch. `defs` names the tree, the
encoders, the printed definitions and the loop lemmas. -/
syntax "link_tac" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
-- `simp` would fold the printed `if c then true else b` into `decide c || b`,
-- which `split` cannot take apart, so those four lemmas stay out.
macro_rules
  | `(tactic| link_tac [$defs,*]) =>
    `(tactic| (
      simp [runIn, functionsOf, functions, Body.exec, Body.runFold, Expr.eval, Expr.evalList,
        Expr.evalFields, bindState, eqVal, IntOp.apply, Order.apply, Division.apply, NumberOp.apply,
        NumberConstant.value, NumberTest.apply, Eval.Env.set, List.lookup, DeclRef.beq_def,
        -Bool.if_true_left, -Bool.if_false_right, -Bool.if_false_left, -Bool.if_true_right, $defs,*]
      all_goals repeat' (split <;> (try simp_all [bindState, eqVal, IntOp.apply, Order.apply,
        Division.apply, NumberOp.apply, NumberTest.apply, Eval.Env.set, List.lookup, DeclRef.beq_def,
        -Bool.if_true_left, -Bool.if_false_right, -Bool.if_false_left, -Bool.if_true_right, $defs,*]))
      all_goals (try simp_all [bindState, eqVal, Eval.Env.set, List.lookup, DeclRef.beq_def, $defs,*])))

end tolean.TypeScript.Output
