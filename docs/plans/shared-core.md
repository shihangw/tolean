# Plan: a shared Tolean IR and shared monad pieces

**Status:** in progress · **Date:** 2026-10-29

TypeScript has the parts that let Lean prove a translator. It builds the
[Tolean IR](../decisions/2026-10-30-tolean-ir.md), which is the Lean code
that the translator writes as Lean data, in a shared core with a TypeScript
extension. It also has an evaluator for the IR, an interpreter for the
source, `program_sound` and certificates. Go has the same parts for its pure
functions only, and the [Go proofs plan](go-proofs.md) lists the rest. SQL
has them for its `SELECT` queries, with an IR of its own, and the
[SQL proofs plan](sql-proofs.md) lists the rest. The rest of both
translators builds strings with `partial def`, so Lean cannot reason about
it. When TypeScript
gains effects, its output stops being plain functions and becomes code in a
monad. This plan says which of these parts the languages share and which stay
with one language. The goal is that `program_sound` and certificates carry
over to effectful TypeScript and then to Go, without each language building
them again.

The [effects plan](effects.md) decides what a library call may do, through
tags such as `observe` and `fails`, and how proofs assume it. This plan is
about the layer underneath: how the IR, its evaluator and the proofs
represent those effects.

## What every language shares

Every language translates into the same target, which is Lean. So the parts
that describe Lean code do not depend on the source language.

| Part | What it is | Today |
|---|---|---|
| Pure core of the IR | Integers, booleans, strings, `Option`, `if`, `let`, structures, lists and `List.foldl`. Each language adds its own constructs at one extension point per layer, such as JavaScript numbers for TypeScript. | `tolean/IR.lean`, with the TypeScript extension in `tolean/TypeScript/IR.lean` |
| Its printer | One IR, printed in one way, so there is one printer to trust or certify. The [printing plan](printing.md) hands its layout to Lean. | Part of `tolean/IR.lean`, which asks each language how to print what it adds |
| Its evaluator | The meaning of the IR. It becomes generic over the value type and environment, so that Go can use `int64` and SQL can use its own values and three-valued logic. | `tolean/TypeScript/IR/Eval.lean`, over the TypeScript interpreter's `Val N`, and `tolean/Go/IR/Eval.lean`, over Go's values |
| Loop core | Every supported `for` runs its body over a list in order. Languages supply heads and their simulations; the core shares state threading, control flow, lowering, fold soundness and certificates. See the [loop-core decision](../decisions/2026-11-22-shared-loop-core.md). | TypeScript's `LoopHead`, `execLoop` and `translateLoop_sound`; shared `Body.fold` and printer in `tolean/IR.lean`. [PR #292](https://github.com/shihangw/tolean/pull/292) adds runtime `LoopResult` and per-loop certificate composition. Go's proved path lowers a leading counted `for` to `Body.fold`. |
| Proof plumbing | `Env` and its lemmas, fuel, the encode and decode pattern, `link_tac`, `runFold_foldl`, a lemma of the shape of `decls_sound`, and kernel-decidable equality on the IR | `Env` is in `tolean/TypeScript/Spec/Eval.lean`, and the rest is under `tolean/TypeScript/Proof/` |
| Certificate generator | The layout of a certificate, and `chars!` | `tolean/TypeScript/Certify.lean` and `Certify/`, with `chars!` in `Syntax/Parser.lean` |
| Lexer side of the round trip | `lexChars_render`, `Laid` and `NoBreak` are about tokens and lines, not about TypeScript | `tolean/TypeScript/Syntax/` |

## Shared monad pieces

Code with effects needs a monad, and the effects of the three languages
reduce to a few pieces.

| Effect | TypeScript | Go | PostgreSQL | Piece |
|---|---|---|---|---|
| Mutable state | Object and array mutation, and `let` captured by a closure | Variables behind pointers, and struct fields | The database | State over an abstract store |
| Failure | `throw` and `try` | `panic`. An `error` is an ordinary value. | Constraint violations and SQL errors | Exceptions |
| Calls to the outside | I/O, `fetch`, `Date.now` and `Math.random` | Interface calls, which are steps in `StateM` today | None, because the query is the effect | External calls: the outside world answers each call |
| Asynchrony and concurrency | `async`, `await` and the event loop | Goroutines and channels | READ COMMITTED transactions | Not shared |

The piece for external calls matters most. It lets a theorem hold for every
answer that the outside world gives, which is how Go's interface calls
already work.

Each piece gets its lemmas once: bind, run and the frame rules. Then
`link_tac` and the lemma of the shape of `decls_sound` work for any monad
built from the pieces. The repository already shares lemmas this way for its
own monads. `tolean/Core/EStateM.lean` holds the `EStateM` lemmas that
the translator's, parser's and lexer's monads use, and it grows.

The generated code uses Lean's own monads for the pieces: `StateT`, `ExceptT`
and `EStateM`, over `Id`. It does not use a monad of Tolean's own. `Std.Do`
gives Hoare triples and the tactic `mvcgen` for exactly these monads, so a
person who proves a claim about effectful code gets Lean's program logic with
no work from Tolean. A monad of our own would need those instances first.
Lean 4.30 calls `mvcgen` experimental, so until it is stable, proofs use
`simp` with the lemmas of the pieces.

Where the [effects plan](effects.md) asks for it, the generated code is
generic over the monad, with class constraints such as
`[Monad m] [Observe m]`. Each language's interpreter fixes one stack of the
standard monads. `program_sound` and the certificates are stated for that
stack, and a claim proved for every monad that meets the constraints holds
for that stack too.

## What stays with one language

- **The source interpreter.** JS, Go and PostgreSQL give the same syntax
  different meanings. `+` on JS numbers, on Go's wrapping `int64` and on a SQL
  `NULL` all differ. Each interpreter is the specification of its language.
- **The layout of the store.** TypeScript objects can alias, so TypeScript
  needs a real heap once the subset allows mutation through an alias. Go has
  pointers. SQL has tables.
- **The concurrency model.** The event loop, Go's scheduler and READ
  COMMITTED differ too much to share. PostgreSQL already has its own proved
  model. The [async plan](async.md) gives TypeScript its model.

## What Aeneas shows

[Aeneas](https://github.com/AeneasVerif/aeneas) writes every Rust function as
Lean code in a `Result` monad, with `ok`, `fail` for a panic or an overflow,
and `div` for a loop that does not end. That monad is the kind of piece that
this plan shares. Effectful TypeScript needs about the same piece for `throw`
and for loops that may not end, and Go needs it for `panic`.

Aeneas avoids a heap because Rust's borrow checker rules out aliasing, so a
mutation becomes a pure update of a value. TypeScript has no borrow checker.
Today the subset gives the same property, because only locals that a function
owns can change. Once the subset allows shared mutable objects, the
TypeScript store must be a heap, which Aeneas never needs to model.

## Steps

Each step ends with all checks green, and with no change to the output of
code that has no effects. The numbers stay as they were when the plan was
written, so that other documents can name a step.

2. Add the typing relation `WellTyped` on the IR, with its two theorems: the
   translator gives well-typed IR, and well-typed IR gives a value of its
   type. Section 3 of the [decision record on the IR](../decisions/2026-10-30-tolean-ir.md)
   explains why.
3. Give TypeScript state. Add it to the IR, to its evaluator and to the
   interpreter, and extend `program_sound` and certificates to cover it.
   Exceptions are done: `Outcome.ret` holds an `Except`, the IR has
   `Body.throw` and `Body.bind`, and `program_sound_call` covers a call that
   throws. Certificates do not cover a function that can throw yet. Go uses
   the same `Body.throw` for a panic: its interpreter and IR evaluator have a
   panic outcome, and `translate_sound` covers integer `/` and `%`, whose
   division by zero panics, the index of a string, which panics out of
   range, and a call of a function that can panic, which the Go IR runs
   with `Body.bind`. A Go function with several results returns the shared
   IR's `tuple`, and `a, b := f()` takes it apart with `letTuple`, as
   TypeScript's object destructuring does. State is not done, and Go does not need
   it yet: the Go code that the proved path accepts reads only parameters and
   locals, which the environment holds. Package-level constants need no state either,
   because the interpreter holds their values in the program. Go will need
   state for package-level variables and for slices, which a callee can
   change; build the state piece with the first of these, so that Go is its
   second user.
4. The `EStateM` lemmas are in the shared module `tolean/Core/EStateM.lean`,
   and `tolean/Core/Except.lean` holds `Core.Res`, the result of a
   computation that can fail or throw, with its bind lemmas. The lemmas for
   the state piece are not added yet.
5. Move the rest of the Go translator onto the Tolean IR and the Go
   interpreter, as the [Go proofs plan](go-proofs.md) lists, and delete its
   string translation.
6. Take the rest of the shared parts out of the TypeScript code, now that Go
   uses them too: the evaluator with the value type and environment as
   parameters, and the proof plumbing. The generic evaluator must include the
   shared loop runner before Go loop lowering can use it. Use Go as its second
   user before lowering and fold soundness move out of TypeScript; taking these
   parts out before a second language uses them would fit them to TypeScript
   alone.
6a. Connect Go loop lowering to the shared evaluator. A counted `for` loop
    with literal bounds, as the first statement of a function, is done:
    `Go.Spec.Eval.execStmt` runs it with `Core.Loop.execLoop`,
    `Go.IR.Body.exec` runs `fold` with `Core.Loop.runFold`, and `top_sound`
    proves the lowering. `range` is not: `Go.Spec.Eval.execStmt` refuses it,
    and `Go.Translate.transRange` writes Lean text without a proof.
    `tolean/Experimental/LoopCore` contains small C and C++ models and examples
    that exercise the core's shape only; they are not supported source
    languages or production translators.
7. Add the piece for external calls, and move Go's interface calls onto it.
8. Do the same for SQL. Its `SELECT` queries already build an IR of their
   own, with an interpreter and a proof, and the
   [SQL proofs plan](sql-proofs.md) lists the rest. That IR becomes the SQL
   extension of the shared IR once the shared IR has errors.
9. Build the [shared loop core](../decisions/2026-11-22-shared-loop-core.md).
   Each language maps its `for` heads to an items list and proves that
   simulation. Share the interpreter, lowering, fold soundness and
   certificates. Layers b and e of the record depend on step 6's generic
   evaluator; heads, the simulation statement, lowering and certificates
   can be designed now. Start with #292's runtime carrier, then develop
   shared `Outcome` and `execLoop` with Go as the second user. Add proved
   Go ranges and counted loops before extracting lowering and fold
   soundness. C and C++ later supply their own heads and refusals.
   This follows the second-user rule in step 6, rather than extracting
   an interface fitted only to TypeScript. Each stage ends green and
   preserves TypeScript output and certificate counts after #292's
   runtime import changes. This step concerns `for`. Go's `switch` and its
   `if` with an init statement need no shared piece, because the translator
   writes them with the IR's `ite` and `letState`, as the
   [decision record](../decisions/2026-11-26-go-switch-as-if-chain.md)
   explains.

## Open questions

- A stack of monad transformers can make `simp` slow, because it unfolds
  every layer. Do proofs about a stack of the standard monads stay fast
  enough until `mvcgen` is stable?
- Should the IR have a fixed set of effect nodes in its core, or should each
  language add its effects at the extension point, as it adds its values?
- How should loops that may not end appear in the IR? The printed Lean can
  use `partial_fixpoint`, which gives a result like the `div` of Aeneas, as
  the [decision record on the IR](../decisions/2026-10-30-tolean-ir.md) says. The
  evaluator could keep fuel, or give the same kind of result.
