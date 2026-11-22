# One shared loop core for every language

**Status:** accepted · **Date:** 2026-11-22

Every supported `for` loop runs its body once per value of a list, in
order, until the body breaks or returns. A loop has a head and a body.
The head decides which values to visit. The core threads state and handles
`break`, `continue` and early return. It also handles sequencing, nesting
and certificates. Those parts should be the same in every language.

This decision covers `for` loops. It specifies the full design before
extraction, but does not introduce a neutral statement language. Separate
records will cover `switch` and `if`.

## What already exists

TypeScript already separates the head from the body. In
`tolean/TypeScript/Translate.lean`, `LoopHead` has `forOf` and `counted`
constructors. `loopHead` returns an element name, its type and an
`items : IR.Expr`. `translateLoop` builds one `IR.Body.fold` for both heads.
It computes changed locals and flags for breaks and returns before it
translates the body.

In `tolean/TypeScript/Spec/Eval.lean`, `execLoop` consumes a list and
handles `normal`, `cont`, `brk` and `ret`. It drops each iteration's local
bindings while preserving changes to outer variables. `execCounted`
instead tests the bound and increments the counter, with a limit that
rejects unsafe JavaScript counts. The proof connects these two views.
`HeadSim` in `tolean/TypeScript/Proof/LoopHead.lean` says that, for agreeing
and well-scoped environments, the source statement equals `execLoop` over
the list to which the output's items evaluate. `loopHead_sim` proves this
for both heads. `translateLoop_sound` in
`tolean/TypeScript/Proof/Stmt.lean` then proves the body and fold once.
Pattern binders have additional translation and proof code today.

The fold evaluator is still in `tolean/TypeScript/IR/Eval.lean`, not in a
shared `tolean/IR/Eval.lean`. Its `Body.runFold` keeps the changed locals,
stops on a break and propagates a return. Source `continue` has already
been lowered to normal completion of the translated body.
`runFold_foldl` in `tolean/TypeScript/Proof/Link.lean` connects that evaluator
to the printed fold.

[PR #292](https://github.com/shihangw/tolean/pull/292) adds
`bodyExec_fold_compose` in that link module and the per-loop certificate
step with `loop_prepare` and `split_loop_result`. It also puts `LoopResult`
in `tolean/Runtime/LoopResult.lean`, under `tolean.Runtime`. The carrier
distinguishes a returned value from completed loop state. These changes
are implemented on that PR, but are not on main at the time of this record.
They complete the direction of the
[composable-loop certificate record](2026-11-21-composable-loop-certificates.md),
whose checkpoint on main still describes the earlier blocked prototype.

Go does not yet have proved loops. `tolean/Go/Translate/Pure.lean` refuses
loop statements, and `Outcome` in `tolean/Go/Spec/Eval.lean` has only
`normal` and `ret`. The older string translator in
`tolean/Go/Translate.lean` translates slice ranges into recursive functions.
Its `Mode.loop` uses `.inl` for completed state and `.inr` for a function
return. A `continue` calls the recursive function on the remaining list.
That translation is not the proved path.

## Layers and ownership

The following module locations describe the intended split. Shared
evaluation and proof modules do not exist at these locations yet.

| Layer | Owner and location | Contract |
|---|---|---|
| a. Loop head | Each language's translator | Produce binder names, an element type and an items expression, subject to the head's side conditions. Multiple names can bind fields of one list element. |
| b. Loop interpreter | Shared evaluation module under `tolean/`; called by each language's source interpreter | One generic `execLoop` takes the body-execution function, environment operations and element binding operation. A shared `Outcome` has `normal`, `ret`, `brk` and `cont`. Go gains the last two cases. |
| c. Head simulation | Shared statement under `tolean/Proof/`; proofs under each language's `Proof/` | Generalize `HeadSim`: the source loop statement equals shared `execLoop` over the list that the output's items evaluate to, under the required environment and evaluation hypotheses. Prove it once for each head form. |
| d. Lowering | Shared translation module under `tolean/`; existing printer in `tolean/IR.lean` | Build `Body.fold` from changed locals, the element binder, translated body, items, rest and `LoopInfo`. Keep the printer's choice of `foldl`, `forIn` and, after #292, `LoopResult`. |
| e. Fold soundness | Shared IR evaluator and proof modules under `tolean/` | Generalize `runFold` and `translateLoop_sound`. A language supplies body-statement soundness and its `HeadSim`, with the environment laws required by the generic evaluator. |
| f. Certificates | Shared certificate and link modules under `tolean/`; carrier in `tolean/Runtime/LoopResult.lean` | Keep a lemma per loop and #292's per-loop composition step. Prepare the current environment, apply `bodyExec_fold_compose` and the loop lemma, then use `split_loop_result` to distinguish completion from return. |

The generic interpreter must preserve scope as well as bind the element.
Its environment interface needs an operation that leaves the iteration's
scope while retaining updates to outer locals. The return payload must
also be a parameter: TypeScript carries an `Except`, while Go's current
pure interpreter returns a value. Binding failure and failed body
evaluation must remain explicit rather than becoming normal completion.

The translator-side work moves too, not just the printer. The shared
lowering owns the policy for changed locals and break and return flags.
Each language still supplies the facts about assignments and jumps in its
own syntax. Nested loops must not make a break of the inner loop look like
a break of the outer one. Language-specific name resolution and scope
checks stay at the boundary.

## Heads and refusals

The table distinguishes TypeScript's current heads from proposed Go, C
and C++ heads. It does not claim that these languages already accept them on a proved
path.

| Language and head | Items list | Side conditions | What stays refused |
|---|---|---|---|
| TypeScript `for (const x of xs)` | Array elements, set values, map entries or string iteration values, in source order | The body cannot change the iterable. Pattern binders bind parts of an element. | Mutable iteration that could change the values visited |
| TypeScript `for (let i = a; i < b; i++)` | `JSNumber.countUp a b` | Today `a` is an integer literal. The counter and everything the bound reads stay unchanged by the body. Evaluation requires a safe count. | Other tests and updates, except the already accepted equivalent updates `++i` and `i += 1` |
| Go `for _, x := range xs` over a slice or array | Elements in index order | The body cannot change the iterable, including through an alias. | Range over a map, channel or function iterator |
| Go `for i := range xs` or `for i, x := range xs` over a slice or array | Indices, or index-value pairs | Length and index values must fit the modeled Go `int`. The same no-mutation rule applies. | Unordered map iteration and other range forms not listed here |
| Go `for i := a; i < b; i++` | Consecutive values from `a`, excluding `b` | Start, counter and bound have the same modeled integer type. The body cannot assign the counter or change what the bound reads. | Other update forms or tests |
| C `for (int i = a; i < b; i++)` | Consecutive values from `a`, excluding `b` | Start and bound fit the counter's signed type. Require a bound of that same type and an unchanged counter and bound. | Mixed-type bounds, other update forms and pointer-walking loops |
| C traversal of an array with known length | Indices, with element reads in index order | Prove the index range is within the array and fits the counter type. The body cannot change the iterable. | Unknown lengths and traversal through unchecked pointers |
| C++ `for (const auto& x : xs)` or `for (auto x : xs)` over `std::vector`, `std::array` or built-in arrays | Elements in order, as for TypeScript's `for...of` | Element reads and copies must have modeled value semantics. The body cannot change the iterable or invalidate its iterators. | Writes through `auto&`, user-defined ranges and unmodeled copy or lifetime effects |
| C++ `for (int i = a; i < b; ++i)` | Integers from `a`, excluding `b` | Require the signed bound to have the counter's type, as in C. The counter and what the bound reads stay unchanged by the body. | Mixed-type bounds and other update forms |
| C++ `for (size_t i = 0; i < v.size(); ++i)` | Unsigned integers from zero, excluding `v.size()` | The bound has the counter's type. The body cannot change `v.size()`, assign the counter or change the iterated container. | Bounds of a different type and bodies that invalidate iterators |

The strict bound makes the Go increment safe despite Go's wrapping
integer semantics. An iteration starts only when `i < b`. Since `b` fits
the same type, `i` is at most that type's maximum minus one. Thus `i + 1`
is representable, even on the last iteration before the test fails.
If `a >= b`, the list is empty. The same argument avoids C's undefined
signed overflow, but C must refuse a bound of a different type rather
than silently rely on its usual arithmetic conversions.

C++ adds head mappings and refusals, not new shared layers. Signed
overflow is undefined as in C. Unsigned arithmetic wraps, but the same
strict-bound argument prevents wrapping when the bound has the counter's
type. In particular, a fixed `v.size()` permits a finite list of indices.

C++ initially refuses a body that writes through `auto& x`. That
in-place element mutation may later become a map over the list. Explicit
iterator loops with `begin`, `end`, `!= end` and `++it` also stay refused
until a later change recognizes the idiom. Ranges with user-defined
`begin` or `end`, or overloaded operators, need separate models.
`unordered_map` and `unordered_set` do not supply the required specified
order. Structured bindings over maps wait until maps are modeled.
Bodies that invalidate iterators, such as `push_back` or `erase` on the
iterated container, stay refused. So do loops whose bodies can throw
across destructors with effects.

Labeled `break` and `continue`, and `goto`, remain outside this design.
An accepted head never permits the body to assign its counter or change
what its bound reads. A later design may cover Go `for cond {}` as a
while loop, but it is not a finite-list head in this implementation.

## Evaluator dependency

Layers b and e depend on step 6 of the
[shared-core plan](../plans/shared-core.md): the IR evaluator must become
generic over both value type and environment. Moving the TypeScript
evaluator unchanged would merely impose TypeScript's values and scope
representation on Go.

We can design heads, the shared `HeadSim` statement, lowering and
certificates now: layers a, c at the statement level, d and f. Concrete
proofs must wait for the evaluator interfaces they use. This record
defines their boundary without claiming the generic evaluator is done.

## Order of work

Each step ends green. After the runtime move's import and qualified-name
changes in #292, extraction must leave TypeScript output unchanged and
must not change its certificate counts.

1. Move `LoopResult` to `tolean.Runtime`. This is done in #292, pending
   its arrival on main.
2. Introduce shared `Outcome` and generic `execLoop` as part of the
   evaluator work in shared-core step 6. Make TypeScript's `execLoop` an
   instance. Preserve the statements of its existing proofs.
3. Add Go's proved range loop and counted `for` on these shared pieces.
   Go is the first second user and tests whether the parameters suffice.
4. Once Go uses the pieces, lift `translateLoop`'s lowering and
   `translateLoop_sound` into the shared modules.
5. Let later C and C++ front ends reuse layers a through f, with their
   own heads and simulations.

The shared-core plan still extracts a part when a second language uses
it. Steps 2 and 3 are one Go-driven effort, with green intermediate
commits, not a generalization for hypothetical users. Go determines the
environment and value requirements before extraction, and its loops
validate them before we move lowering and fold soundness. Designing the
whole boundary now does not require moving all its code now.

## Alternatives considered

Sharing only `LoopResult` and a few lemmas would leave every language
with its own lowering and fold proof. C would repeat the work again.
The common list interpretation lets us share the larger proof without
sharing source syntax.

Making while loops or recursion the single primitive would lose the
`foldl` and `forIn` output that users and proofs already rely on. It would
also require termination measures for loops whose finite items list
already explains why they terminate.

A neutral statement language for all control flow would be too large a
step. TypeScript's statement proof currently has 5,883 lines. Loops have
an existing head boundary that lets us move one part without redesigning
every statement. Switches and conditionals can follow in later records.

## Open questions

- Which environment operations should the generic evaluator require?
  TypeScript's `Env N` is a list with scope drop. Go's `Env` is also a
  list today, but its values and scope operations are separate.
- How should shared certificates express the `countUp?` hypothesis from
  step 15 of the [pure TypeScript plan](../plans/pure-typescript.md) and
  the [counted-loop record](2026-11-16-counted-loop-certificates.md)?
  What are its Go and C analogues when type bounds establish increment
  safety but evaluation still has other preconditions?
- How should while and do-while loops with `@decreases` relate to this
  finite-list core?
- Should Go's recursive-function string translation for loops be deleted
  as the proved loops arrive, or kept until step 5 of the shared-core
  plan removes the rest of that translator?
