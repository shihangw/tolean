import tolean.TypeScript.Proof.Module

/-!
A check that the translator's theorems keep their meaning. CI builds this
file with the rest of the library, so the build fails when it does not hold.

`--wfail` already fails on a `sorry`, but an `axiom` gives no warning, and a
weaker statement still builds. So `#guard_msgs` pins the axioms that each
theorem depends on to Lean's three standard ones, and each `example` restates
a theorem with the statement that the docs describe. A change that adds an
axiom, or that changes a statement, has to change this file too, where a
reviewer sees it.
-/
namespace tolean.TypeScript.Proof

open tolean.TypeScript tolean.TypeScript.Syntax tolean.TypeScript.Translate
open tolean.TypeScript.Eval (Val)

/-- info: 'tolean.TypeScript.Proof.program_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms program_sound

/-- info: 'tolean.TypeScript.Proof.translate_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms translate_sound

/-- When the translator translates every file of a program, in an order where
each file comes after the files it imports from, a call of a function of the
output gives a value only when the interpreter gives the same value for the
same call of the program. -/
example {N : Type} [JSNumber N] {p : Eval.Program} {outs : List (String × List Output.Decl)}
    {ifaces : List (String × Interface)} (h : ProgramTranslation p outs ifaces)
    (hnd : (p.map (·.1)).Nodup) (key : DeclRef) (args : List (Val N)) (fuel : Nat) (v : Val N)
    (hv : Output.runIn (Output.functionsOf outs) key args fuel = some v) :
    Eval.runIn p key args fuel = some v :=
  program_sound h hnd key args fuel v hv

/-- The same, for one file that `translateTree` parses and translates. -/
example {N : Type} [JSNumber N] {file source : String} {target : Edition} {m : Module}
    {names : Output.Names} {decls : List Output.Decl}
    (h : translateTree file source target = .ok (m, names, decls))
    (name : String) (args : List (Val N)) (fuel : Nat) (v : Val N)
    (hv : Output.runIn (Output.functionsOf [(file, decls)]) ⟨file, name⟩ args fuel = some v) :
    Eval.runIn [(file, m)] ⟨file, name⟩ args fuel = some v :=
  translate_sound h name args fuel v hv

end tolean.TypeScript.Proof
