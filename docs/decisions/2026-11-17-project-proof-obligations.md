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

This slice does not generate comparator obligations or consume their proofs
in certificates. The translator currently rejects arbitrary comparators in
`translateSort` before the certifier sees them. The certifier independently
requires `keyComparator?` so that it can construct its consistency proof.
Removing either guard alone would not connect an external proof to
`program_sound`. Both guards remain in place.

The manifest checker is useful independently, but its entries do not prove
that a statement came from Tolean. The later certificate integration must
derive the required statements from the generated output and check that each
required obligation has a proof. It must not treat a project-written list as
the list of required obligations. It must also pass those proofs to the
certificate theorem. Until then, arbitrary comparators and `@decreases`
obligations remain refused.
