# Project proofs use a fixed axiom policy

Tolean should accept project proofs of obligations whose statements it
generates. The project supplies a theorem in a separate Lean module, not a
replacement statement or a tactic string. The checker requires the theorem's
type to be exactly the named statement. It accepts only `propext`,
`Classical.choice` and `Quot.sound`, including dependencies of dependencies.
The project cannot add axioms to this list. In particular, a proof that uses
Lean's `sorryAx` must fail.

The first slice adds an `obligations` field to the project chain manifest.
Each entry names `spec`, `proof` and `module`. `chain check` imports the
module and checks the theorem with the fixed policy. Existing claims retain
their explicit axiom lists because claims describe project trust choices.
An obligation instead promises a proof within Tolean's policy.

The next slice generates statements for additional comparators on bigint
elements. Each statement binds the number model and the lexical scope, then
requires `Eval.Consistent` for the translated comparator. This means that the
comparator must be consistent on every finite input list. Its name contains
the source location, so a project cannot substitute another statement through
its manifest.

The certificate first tries the existing sort tactic against the constant
ordering. It then uses the supplied theorem if that attempt fails. Without a
supplied theorem, the generator currently attempts automatic proofs only for
a literal-zero comparator. Other shapes require a manifest entry. The sort
link theorem passes the resulting consistency proof to
`sortValues_sortWith`, so the function certificate still follows through
`program_sound`.

Generated output records each required statement. The chain checker reads
these records independently of the project's supplied proof list. It checks
either the supplied theorem or the certificate's consistency theorem, under
the same fixed axiom policy. A missing manifest entry cannot remove a
generated requirement.

Additional comparator shapes on other element types remain refused in this
slice. Obligations that capture generic types also remain refused. These
restrictions do not change the existing support for known key comparisons.
The mechanism does not yet serve `@decreases`, which remains refused here.

Literal nonzero comparators remain refused because their consistency
obligation cannot hold, even on a singleton array. A consistent comparator
must compare each element with itself as equal. Interpreter seed 359337175
exposed this case: main refused the program, but the comparator extension
initially accepted it while the interpreter correctly gave no value.
