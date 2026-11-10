# Plan: a shared Tolean IR and shared monad pieces

**Status:** in progress, see [Progress](#progress) · **Date:** 2026-10-29

Today only TypeScript has the parts that let Lean prove a translator. It
builds the [Tolean IR](../decisions/2026-10-30-tolean-ir.md), which is the Lean
code that the translator writes as Lean data. It also has an evaluator for
the IR, an interpreter for the source,
`program_sound` and certificates. The Go and SQL translators build strings,
and they use `partial def`, so Lean cannot reason about them. When TypeScript
gains effects, its output stops being plain functions and becomes code in a
monad. This plan says which of these parts the languages share and which stay
with one language. The goal is that `program_sound` and certificates carry
over to effectful TypeScript and then to Go, without each language building
them again.

The [effects plan](effects.md) decides what a library call may do, through
tags such as `observe` and `fails`, and how proofs assume it. This plan is
about the layer underneath: how the IR, its evaluator and the proofs
represent those effects.

## Progress

Each row is a step of the plan that is built, with the pull request that
built it.

| Step | What is built | Pull request |
|---|---|---|
| 1 | The shared core of the IR, its printer and its equality are in `tolean/IR.lean` and `tolean/IR/`. The core includes inductive types whose constructors take no arguments, which TypeScript uses for literal unions and SQL could use for its enums. TypeScript adds JavaScript numbers and `null` in `tolean/TypeScript/IR.lean`. Every corpus file translates to the same text as before. | [#50](https://github.com/shihangw/tolean/pull/50) |

## What every language shares

Every language translates into the same target, which is Lean. So the parts
that describe Lean code do not depend on the source language.

| Part | What it is | Today |
|---|---|---|
| Pure core of the IR | Integers, booleans, strings, `Option`, `if`, `let`, structures, lists and `List.foldl`. Each language adds its own constructs at one extension point per layer, such as JavaScript numbers for TypeScript. | `tolean/IR.lean`, with the TypeScript extension in `tolean/TypeScript/IR.lean` |
| Its printer | One IR, printed in one way, so there is one printer to trust or certify. The [printing plan](printing.md) hands its layout to Lean. | Part of `tolean/IR.lean`, which asks each language how to print what it adds |
| Its evaluator | The meaning of the IR. It becomes generic over the value type, so that Go can use `int64` and SQL can use its own values and three-valued logic. | `tolean/TypeScript/IR/Eval.lean`, over the TypeScript interpreter's `Val N` |
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
own monads. `tolean/TypeScript/EStateM.lean` holds the `EStateM` lemmas that
the translator's, parser's and lexer's monads use. That file moves to a shared
place and grows.

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
code that has no effects.

1. Split the Tolean IR into a shared core in `tolean/IR/` and a TypeScript
   extension for JavaScript numbers and `null`. The printer and the
   evaluator get a hook for each language's constructs. The output of every
   corpus file stays the same, byte for byte.
2. Add the typing relation `WellTyped` on the IR, with its two theorems: the
   translator gives well-typed IR, and well-typed IR gives a value of its
   type. Section 3 of the [decision record on the IR](../decisions/2026-10-30-tolean-ir.md)
   explains why.
3. Give TypeScript state and exceptions. Add them to the IR, to its
   evaluator and to the interpreter, and extend `program_sound` and
   certificates to cover them. These two pieces are what most code needs
   first.
4. Move the `EStateM` lemmas to a shared module, and add the lemmas for the
   state and exception pieces next to them.
5. Make the Go translator total, and have it build the Tolean IR, with a Go
   extension for `int64` wrapping. Give Go an interpreter for its subset.
6. Take the rest of the shared parts out of the TypeScript code, now that Go
   uses them too: the evaluator with the value type as a parameter, and the
   proof plumbing. Taking them out before a second language uses them would
   fit them to TypeScript alone.
7. Add the piece for external calls, and move Go's interface calls onto it.
8. Do the same for SQL. Its `SELECT` queries already build an IR of their
   own, with an interpreter and a proof, and the
   [SQL proofs plan](sql-proofs.md) lists the rest. That IR becomes the SQL
   extension of the shared IR once the shared IR has errors.

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
