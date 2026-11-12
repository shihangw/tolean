# A local function is lifted out, and each call passes the state

**Status:** accepted · **Date:** 2026-11-12

Tolean translates a function declaration at the top of another function's
body into a Lean function of its own. The lifted function takes the locals
that its body names, then its own parameters. When it returns nothing, it
returns the `let` locals that it changes, and each call binds them again.
`tests/typescript/corpus/translate/accept/localFunctions.ts` shows the
output.

## What the interpreter does

JS gives a local function a closure, so its body reads and writes the
variables of the function around it. The interpreter in
`tolean/TypeScript/Spec/Eval.lean` models that only for the cases that
Tolean accepts. A declaration binds the name to a closure value, which holds
the parameters and the body. A call runs the body in an environment of the
arguments and the caller's variables that the body names (`captures`). Then
it writes the values of those variables back into the caller's environment
(`writeBack`).

This works because the closure never escapes. Tolean refuses every use of
the name except a call, so a call always runs while the variables that the
closure saw are still in scope, under the same names. A closure that was
returned or stored would need a store that outlives the call, and the
interpreter has none.

## The output translates the body again at each call

The proof needs to know what the lifted function means at each call. At the
declaration, the translator has a scope with the function's parameters and
the captured locals. At a call, it translates the body again in the same
scope, and it checks that the text is the text of the lifted function. So
the proof of the call gets the translation of the body as a fact, and the
induction over the translator's fuel covers it.

The IR's meaning of a call also checks that the name holds the closure that
the declaration bound. The printed Lean code does not contain that check,
because Lean names the function directly. The proof uses it to show that the
interpreter calls the same body.

## Fuel

The interpreter and the IR spend one unit of fuel on a call, so the body runs
with less fuel than the statement that calls it. `stmts_sound` therefore
holds for every fuel at which calls agree at that fuel and below, and
`calls_agree` proves that agreement by strong induction on the fuel.

## An arrow function in a `const` has the same tree

`const g = (x: T): R => { … }` in the body of a function is a local function
too. The parser gives it the tree of `function g(x: T): R { … }`, a
`Stmt.funDecl`, so the interpreter, the translator and their proofs need
nothing new. The two differ in JavaScript only before the statement: a
declaration is hoisted to the top of its block, and a `const` is in its
temporal dead zone there. The interpreter binds the name where the statement
stands, and Tolean refuses a call before it, so they mean the same wherever
Tolean accepts them.

The parser looks for the arrow form before it reads a declaration of a
variable. It reads `const g = (`, the parameters, a return type if there is
one, `=>` and then a `{`. If any of them is missing, it goes back to where
it started and reads a declaration. `parseArrow` refuses the `{` that the
check looks for, so the check never finds one where a declaration reads. The
round-trip proof in `Syntax/RoundTripStmt.lean` (`localArrowHead_decl`) uses
that fact, so the proof of a declaration needs only one more step.

## Left for later

A local function that returns a value and also changes a variable of the
function around it is step 14 of `docs/plans/pure-typescript.md`, with calls
between local functions and certificates for them. The interpreter keeps no
variables with a `return`, so such a function needs a new path in it.
