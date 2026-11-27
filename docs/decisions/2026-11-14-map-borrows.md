# Pass changed maps back to the caller

**Status:** accepted design, partly implemented · **Date:** 2026-11-14

A function that changes a caller's map should return the new map, and the
caller should bind that result in place of its old map. We choose this
borrow translation rather than a state monad. This record settles the design
question in step 8 of the [pure TypeScript plan](../plans/pure-typescript.md).
The first implementation and three later extensions now cover the
[straight-line case](../typescript/README.md#map-borrows) described below.

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

The original interpreter bound arguments as values. `Stmt.ownsChanges`
refused every function that changed a parameter, and `evalCall` returned
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

## Boundary when decided

When this decision was made, every changed map parameter was refused,
including an exclusive borrow of one map. The decision chose the result
shape without changing that boundary.

## Current implementation

A void function may now change one or more Map parameters through straight-line
set, delete and forwarding calls with atomic arguments. It may end with a
bare return. A forwarded borrow must go to an earlier borrowing function
in the same file. At the outer call, the caller owns the map and passes it
exactly once in a top-level call statement.
When a function changes several maps, every mutable Map parameter must
change. The function returns a tuple of the final maps in parameter order,
and the caller binds each name again. The translator refuses a call that
passes one map for two changed parameters. The interpreter gives that call
no result either. Other arguments must not keep
that map, and the ownership check still counts collections that those
arguments let escape.

The source interpreter copies the final map back, and the IR evaluator
uses the same state result. The proof of `program_sound` covers this call
rule. Corpus tests check the generated code, and interpreter tests compare
the caller's observations with Node. Readonly inputs retain their existing
translation.

A borrowing function may also return an ordinary value through one final
`return e;` after its updates. The spec runs the body with that return
turned into an assignment to a fresh variable, so the call completes
normally and the final maps are copied back as before. The Lean function
returns a tuple of the value and the final maps, and the caller binds the
value to the `const` or `let` that the call initializes. Only such a
declaration may make the call.

Step 8 remains open. Early returns, branches, loops, throws and imported
borrowing functions remain refused. Borrowing functions receive no per-file certificate yet. A wider
result must preserve the final parameter bindings on every supported
completion path; the statement proof must also relate newly declared
source and output variables before a returned value can be copied out.

Reject fixtures in `tests/typescript/corpus/translate/reject/mapBorrow*.ts`
and `tests/typescript/corpus/translate/projects/reject/importedMapBorrow`
record this boundary. Each of them fails translation today. Several of the
refusals still use a general message, such as the one for a `void` return
type, because the translator accepts no borrow shape that they would match.
