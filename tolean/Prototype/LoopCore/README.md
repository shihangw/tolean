# Shared loop core experiment

This is a partial prototype, not a replacement translator. The C and C++ models
share a proved loop lowering. The existing TypeScript interpreters are proved
equal to instances of the core. Go has a range interpreter and executable checks,
but **does not yet have a proved loop translator or a counted-loop instance**.
The requested four-language validation is therefore not complete.

## What the theorem says

`Core.execLoop_eq_runFold` has the following statement. The variables `ρ`, `r`,
and `v` are arbitrary types.

```lean
(source target : ρ → Option (Outcome ρ r))
(bind : v → ρ → Option ρ)
(leave : ρ → ρ → Option ρ)
(step : ∀ s, target s = (source s).map Outcome.lower)
(env : ρ) (items : List v) :
execLoop source bind leave env items = runFold target bind leave env items
```

`Outcome.lower` changes `cont s` to `normal s` and preserves the other outcomes.
Thus the hypothesis covers failure, normal completion, continue, break, and
return. Both loops can fail when binding an element or leaving its scope. A
return can carry a different type from the elements. TypeScript uses this
distinction for its `Except` return carrier.

`Core.lowerLoop_sound` connects this induction to an actual `IR.Body.fold`.
It assumes that the translated body satisfies the one-step hypothesis and that
the items expression evaluates to the input list. It concludes that `evalIR`
of the lowered loop equals the source loop followed by the translated rest.
A return bypasses the rest. The small evaluator rejects unsupported IR forms.
Its expression evaluator, value projections, binding, and state projection are
parameters. It imports no source-language module.

The simulation hypothesis currently uses the **same state representation and
pointwise equality**, not an arbitrary relation between different source and
target environments. C's body theorem proves that hypothesis by induction.
This restriction matters for Go: the real source evaluator updates bindings,
whereas its IR evaluator prepends shadowing bindings. A useful next theorem
would lift a relation through both partial binders and both scope projections.
The current Go bridge leaves body agreement as a hypothesis. It does not
silently assert that agreement for the existing Go translator.

## Language evidence

Counts include comments and blank lines in the named Lean modules. They exclude
the existing modules that the prototype imports. Shared core: **113 lines**.
The C and C++ examples and printer adapter add 86 lines together.

| Language | Head forms | New language lines | Reused core | Parameters and verdict |
| --- | --- | ---: | --- | --- |
| C | Captured integer start and bound, increment by one | 162 | `execLoop`, `lowerLoop`, `lowerLoop_sound`, `evalIR` | Functional environment, integer and array values, projection of changed names. Proved for the mathematical AST model. |
| C++ | By-value and const-reference vector ranges; C counted head | 70 | Same loop runner, lowering, evaluator, and theorem; C body proof | Immutable vectors and value-only observations. Reuse is small, but aliasing is not modeled. |
| Go | Real AST range with blank index and declared value | 63, plus 37 example lines | `execLoop`; conditional `execLoop_eq_runFold` bridge | Existing scalar values, environment, and interpreter; separate immutable slice parameters. No lowering proof, counted head, or Go golden output yet. |
| TypeScript | Existing for-of and counted semantics | 69 | Exact equalities with `execLoop` and `runFold` | Partial binder, length-based scope exit, partial `bindState`, `Except` return, rejection of IR continue. The existing semantics really are instances. |

The TypeScript counted equality reuses `Proof.execCounted_eq`, which relates
`execCounted` to a successful `JSNumber.countFrom`. The existing
`Proof.loopHead_sim` and `HeadSim` connect accepted counted syntax to the items
expression. `Proof.translateLoop_sound` remains the existing translator's loop
soundness theorem. The corpus files
`tests/typescript/corpus/translate/accept/loopReturn.ts` and `countedFor.ts`
exercise the return and counted forms covered by these existing general
theorems. This prototype does not add file-specific certificates or rerun that
corpus suite.

## What the source models omit

C's statements are continuation-shaped Lean data, and their tiny expression
language is embedded directly in the shared IR. There is no C expression
translation proof separate from its shared denotation. The head denotes a list
by definition; `head_sound` proves the items expression gives that list, not a
separate operational C counter machine. The C golden functions specialize the
length parameter to four. Indexing fails in the interpreter outside the array,
whereas the printer extension uses `List.getD`. The printed functions therefore
agree only on in-bounds accesses; no general printer correctness theorem is
claimed.

The checked head interfaces reject writes to the induction variable. C++
also rejects writes to its vector or element binder, even for by-value loops.
Bounds are captured integers, so the body cannot change what a bound reads.
The C head check keeps the start and bound within signed 32-bit integers, which
also bounds the last counter update. Other arithmetic uses mathematical `Int`.
Agreement with real C and C++ additionally requires that every arithmetic
result fits signed `int`; this precondition is not proved or enforced by the
translator. There is no claim about overflowing programs.

The raw lowering functions remain available for stating theorems about the
model. The checked wrappers only enforce the stated head restrictions. They
are not type checkers, full mutation analyses, or certificates for arbitrary
IR expressions. There are no nested source loops, pointers, observable reference
identity, mutable arrays, dynamic captured-bound expressions, or parser.
No theorem relates the Go extension to the complete Go language specification.

## Checks and design verdict

Run from the worktree root:

```sh
nix develop --command bash tests/prototype/loopcore/run.sh
nix develop --command lake build --wfail \
  tolean.Prototype.LoopCore.Examples \
  tolean.Prototype.LoopCore.GoExamples \
  tolean.Prototype.LoopCore.TypeScript
nix develop --command lake env lean tests/prototype/loopcore/Axioms.lean
```

The script checks six goldens against the real `Body.lines` output, compiles
them, and checks their results with `by decide`. The C and C++ AST checks also
use `by decide`. Go's source interpreter checks use `#guard`, not `native_decide`.
Native C outputs are 10, 2, and 5; C++ outputs are 10, 3, and 13; Go outputs are
10, 3, and 5. All nine match their Lean checks. Golden files compile with unused
parameter warnings because they share a uniform test signature. The new library
modules pass `--wfail`. The axiom audit lists only `propext`, `Quot.sound`, and,
for some imported semantics, `Classical.choice`.

One generic runner works for both functional and association-list environments.
The fold evaluator need not choose one language's value type, and separating
return values from elements was necessary for TypeScript. The induction still
needs a more general simulation relation before it can absorb existing
source-to-IR proofs with different stores.

The current shared printer's optional-return state handles the early exits and
two sequenced loops in the examples. A dedicated `LoopResult` carrier, proposed
in PR #292, appears compatible with this control separation, but that PR is not
imported and its representation has not been tested here. This experiment
supports sharing the loop mechanism; it does not yet establish that all four
front ends can share the complete soundness proof.
