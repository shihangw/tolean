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
scope, and it checks that the IR equals the IR of the lifted function. So
the proof of the call gets the translation of the body as a fact, and the
induction over the translator's fuel covers it.

The check uses decidable equality on the IR rather than comparing its debug
text. The Lean kernel can run that equality when a certificate checks the
translation. It cannot run the formatter that produces the debug text.

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

## Certificates

A certificate writes the closure's syntax tree as a Lean term, and its link
proof unfolds the lifted definition at each call. A loop that calls a local
function has an invariant for the closure bound to that name. The closure
has no data encoder: the invariant states its exact parameters and body.
The loop's printed step captures only data, because the printed call names
the lifted function directly.

Each local call spends one unit of fuel. A loop lemma therefore reserves
that unit in addition to the depth of calls to functions of the module.
The certifier also visits loops inside a lifted body, so a local function
can contain a loop as well as be called by one.

## A final return can read the captured state

The interpreter now retains the environment of a final return. The first
translation accepts a final return that names a changed captured variable.
Before it executes the body, the interpreter checks whether it changes
captured variables and ends with a value return. It selects the
state-preserving executor for that form and the ordinary executor otherwise.
It never recovers state by replaying the body. The call-contract proof
relates this dispatch to the same results, including refusal and normal
termination.
The lifted function returns the state tuple, and the caller reads that
variable from the tuple as the call's value. This avoids returning the same
value twice.

The proof simulates the statements before the return with `StmtSim`. That
relation preserves values of names that were in scope before the body.
The final identifier therefore has the same value in the interpreter and
the IR. The proof also relates the state that the call writes back.

## Left for later

A compound final return expression, a final return of a new local variable,
implicit transitive captures, and longer sibling call chains remain in
step 14. An earlier return in a state-writing local stays refused.

## Calls of earlier siblings

A local can call an earlier sibling that calls no other local function.
The caller must name the sibling's captured variables itself, so both
interpreters already pass those variables into the body. The change analysis
uses the actual local function environment and includes state written by
the sibling.

The IR keeps a captured closure as an ordinary argument and checks its
parameters and body at each call. The printer marks that argument's type
as erased, writes `Unit`, and passes `()`. The generated call names the
lifted definition directly, so it does not read the erased argument.
Certificates check this erasure by relating the IR to the printed body.
The printer emits nested callees before the local that calls them.

A caller that returns a value while changing captured state must write
some captured variable directly. The interpreter's expression-call guard
does not yet count state changes made only through sibling calls.
