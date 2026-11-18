# Counted-loop certificates require a safe bound

**Status:** accepted · **Date:** 2026-11-16

A certificate for a function with a counted `for` loop requires one
precondition for each loop. The precondition says that `JSNumber.countUp?`
on the loop's bound returns a value. It is stated over the function's
parameters, as a hypothesis in the certificate theorem.

The hypothesis preserves nullish branches that narrow a parameter used by
the bound. For example, a nullable numeric bound requires the condition only
in its `some` branch. Each enclosing loop also carries its child loops'
safety conditions in its invariant, with narrowing relative to that loop's
scope. This lets the certifier prove the enclosing lemma before it proves
the function theorem.

The interpreter gives no value when that list does not exist, because the
counter would pass `Number.MAX_SAFE_INTEGER`. A certificate cannot claim an
output for that input. The precondition matches this behavior without proving
the converse of `program_sound`, which would require a second proof of the
translator.

The certifier accepts a bound only when it reads function parameters. A
literal bound still gets a precondition, because the theorem holds for an
abstract number model and its safe-integer laws do not reduce the list by
computation. A `const` local and other non-parameter names remain refused.
Inlining a chain of local definitions is later work.

The evaluator and the translated loop use the same list when the precondition
holds. `JSNumber.countUp?_eq_of_isSome` rewrites the interpreter's result to
the list that `JSNumber.countUp` provides. The existing loop proof then
establishes the certificate without changing its proof or weakening its
claim.
