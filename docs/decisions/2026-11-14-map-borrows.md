# Pass changed maps back to the caller

**Status:** accepted design, implementation pending · **Date:** 2026-11-14

A function that changes a caller's map should return the new map, and the
caller should bind that result in place of its old map. We choose this
borrow translation rather than a state monad. This record settles the design
question in step 8 of the [pure TypeScript plan](../plans/pure-typescript.md).
It does not enable map parameters that change.

## The result carries the maps

The translator must determine which `Map` parameters a function changes.
A function that changes one map and returns nothing returns that map in
Lean. A function that changes several maps returns a tuple in parameter
order. If the function also returns a value, the tuple contains that value
first, followed by the changed maps. The caller binds each changed map
again and uses the ordinary result where the source uses it.

A `ReadonlyMap` parameter stays a plain input. A mutable `Map` parameter
that the function only reads does too. The annotation alone must not make
a call change the caller's bindings.

This keeps the maps that a function changes visible in its type. A state
monad would obscure that information and require state-monad lemmas in
proofs about otherwise plain functions. The [effects plan](../plans/effects.md)
reserves the monad for global state.

## Only an exclusive caller may lend a map

Copying a map in and back out is faithful only if no other reference can
observe it during the call. The caller must own each changed map. A second
local name, a field that holds the map, a captured reference, or another
argument that holds the same map must make the call fail translation.
In particular, passing one map to two changed parameters is not two
independent borrows.

The callee must not let the borrowed map escape through a stored reference
or its ordinary result. Forwarding a borrow to another function needs the
same checks and must pass the final map back through every call.

## The spec must return the state too

The current interpreter binds arguments as values. `Stmt.ownsChanges`
refuses every function that changes a parameter, and `evalCall` returns
only the ordinary result. Removing that guard would lose the change at the
call, so it would not implement a borrow.

The call rule must copy each borrowed map into the callee's parameter
binding and copy its final value back into the caller's argument binding.
Both normal completion and an explicit return must preserve that final
state. The current statement result for a return has no environment.
Exceptional completion needs the same care: JavaScript retains changes
made before a throw, even when a caller catches the error.

The IR evaluator and the interpreter must agree on these results before
the translator accepts a borrow. The proof of `program_sound` must cover
the new call rule, and tests must compare the caller's observations with
Node. Both translators must print the same tuple and rebinding code.

## Current boundary

Step 8 remains unfinished. The interpreter has no result that carries both
a returned value and final parameter bindings, and calls in expressions
have no path to update the caller's environment. Local-function writeback
does not fill this gap: it handles captured locals on normal completion,
not returned values with changed parameters.

Until that machinery and its soundness proof exist, all changed map
parameters stay refused, including an exclusive borrow of a single map.
Readonly inputs and maps created and changed within one function retain
their existing translation. This decision introduces no new accepted
construct and makes no new claim about `program_sound`.
