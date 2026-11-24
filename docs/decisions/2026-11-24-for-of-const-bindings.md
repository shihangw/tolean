# Check `for … of` const assignments at the loop body

**Status:** accepted · **Date:** 2026-11-24

The interpreter and translator use one source-level predicate to reject
assignments to a `for (const … of …)` binding. The interpreter gives no value
for such a loop, and the translator refuses to emit code for it. JavaScript
throws a `TypeError` when the body assigns the binding.

## Why this model

The interpreter environment stores values but not whether a binding is
mutable. Adding binding kinds would change the environment relation used by
`program_sound` and require its statement proofs to preserve those kinds.
That machinery would model `const` more generally, but the translator already
refuses assignments to ordinary `const` locals.

Instead, `Stmt.constLoopAssignedIn` checks whether the body assigns any
binding name. It uses the AST's exhaustive assignment scan, so it covers
simple assignments, compound assignments, and increments. The same predicate
guards the interpreter and both forms of translated loop binding, including
array patterns.

The assignment scan is conservative about nested functions and shadowed
names. It may refuse a body where a syntactic assignment cannot reach the
loop binding. This restriction keeps the interpreter and translator aligned
without adding binding identity to the environment.

`for … of` lexical bindings and `PutValue` are specified in ES2015, so the
check adds no edition gate. See `tolean/TypeScript/Edition.lean`.
