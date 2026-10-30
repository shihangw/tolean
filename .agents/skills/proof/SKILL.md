---
name: proof
description: Prove Lean theorems about tolean's parser and other `ParseM` (EStateM) code. Use when writing or fixing a proof that steps through a parser do-block, a loop, or fuel, such as the round trip in `tolean/TypeScript/Syntax/RoundTrip*.lean`.
---

# Proofs about the parser

Steps, in order. Each ends when its check passes.

1. **Pick the technique files** for the work (below). Read every one whose condition matches before writing the first lemma.
2. **Develop in a scratch file** that imports the module you extend: `nix develop --command bash -c 'lake env lean <scratch>.lean'`. It checks one file in seconds. Done when the file prints no error and no `sorry`.
3. **Merge** the scratch content into the module and run `lake build <module>`. Done when it builds clean.
4. **List the theorems** in `tolean/TypeScript/Spec/Coverage.lean`. Build `tolean.TypeScript.Spec.Coverage`; its error names every unlisted theorem. Add each to the group for its module. A lemma nothing uses gets deleted, not listed. A `simp` lemma is in use when deleting it breaks the build, even where no proof names it. Done when the index builds.
5. **Check the axioms** of each main theorem with `#print axioms`. Done when it lists only `propext`, `Classical.choice` and `Quot.sound`.
6. **Run `lake build --wfail`** on the whole project. Warnings are errors, so an unused variable, an unused `simp` argument or a `simpa` linter hint fails it. Remove what the linter names; keep linters on for the whole file. Done when it completes.
7. **A parser edit** (such as naming a loop step) must not change what the parser reads: run the equivalence check in [loops-and-fuel.md](loops-and-fuel.md), then `node check.ts`, `./checkCertify.sh` and `node checkTranslate.ts` in `tests/typescript`.

## Technique files

- [do-blocks.md](do-blocks.md): read for every proof that runs a parser function. Rewriting a do-block step by step, guards, `if` and `match` in do-notation.
- [simp-and-decide.md](simp-and-decide.md): read when `simp`, `rw` or `decide` misbehaves, or before a proof about lengths, `BEq` or string tests.
- [loops-and-fuel.md](loops-and-fuel.md): read when the code calls `Parse.iterate`, takes fuel, or calls `budget`.
- [round-trip.md](round-trip.md): read when extending the round trip (printer, `Touching`, `Laid`, `ReadsW`, `Ends`, `afterOK`) or the proof that parser output is well formed (`Ready`, `WordsOK`). Also states what the round trip covers.
- [lean-gotchas.md](lean-gotchas.md): read when a Lean error is about syntax, a name, hygiene or termination rather than the math.
