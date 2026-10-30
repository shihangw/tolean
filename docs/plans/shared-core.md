# Plan: a shared output core and shared monad pieces

**Status:** planned, not built · **Date:** 2026-10-29

Today only TypeScript has the parts that let Lean prove a translator. It has
an output tree, an evaluator for that tree, an interpreter for the source,
`program_sound` and certificates. The Go and SQL translators build strings,
and they use `partial def`, so Lean cannot reason about them. When TypeScript
gains effects, its output stops being plain functions and becomes code in a
monad. This plan says which of these parts the languages share and which stay
with one language. The goal is that `program_sound` and certificates carry
over to effectful TypeScript and then to Go, without each language building
them again.

The [effects plan](effects.md) decides what a library call may do, through
tags such as `observe` and `fails`, and how proofs assume it. This plan is
about the layer underneath: how the output tree, its evaluator and the proofs
represent those effects.

## What every language shares

Every language translates into the same target, which is Lean. So the parts
that describe Lean code do not depend on the source language.

| Part | What it is | Today |
|---|---|---|
| Pure core of the output tree | Integers, booleans, strings, `if`, `let`, structures, lists and `List.foldl` | `tolean/TypeScript/Output.lean`, for TypeScript only |
| Its printer | One tree, printed in one way, so there is one printer to trust or certify | Part of `Output.lean` |
| Its evaluator | The meaning of the tree. It becomes generic over the value type, so that Go can use `int64` and SQL can use its own values and three-valued logic. | `Output/Eval.lean`, over the TypeScript interpreter's `Val N` |
| Proof plumbing | `Env` and its lemmas, fuel, the encode and decode pattern, `link_tac`, `runFold_foldl`, a lemma of the shape of `decls_sound`, and kernel-decidable equality on trees | `Env` is in `tolean/TypeScript/Spec/Eval.lean`, and the rest is under `tolean/TypeScript/Proof/` |
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

A stack of monad transformers makes proofs slow, because `simp` has to unfold
every layer. So the generated code of each language uses one concrete monad,
defined as one structure, and not a stack. The lemmas are stated about the
pieces, and each concrete monad gets them with a single unfolding.

## What stays with one language

- **The source interpreter.** JS, Go and PostgreSQL give the same syntax
  different meanings. `+` on JS numbers, on Go's wrapping `int64` and on a SQL
  `NULL` all differ. Each interpreter is the specification of its language.
- **The layout of the store.** TypeScript objects can alias, so TypeScript
  needs a real heap once the subset allows mutation through an alias. Go has
  pointers. SQL has tables.
- **The concurrency model.** The event loop, Go's scheduler and READ
  COMMITTED differ too much to share. PostgreSQL already has its own proved
  model.

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

1. Give TypeScript state and exceptions. Add them to the output tree, to its
   evaluator and to the interpreter, and extend `program_sound` and
   certificates to cover them. These two pieces are what most code needs
   first.
2. Move the `EStateM` lemmas to a shared module, and add the lemmas for the
   state and exception pieces next to them.
3. Make the Go translator total, and have it build an output tree on the
   same pieces. Give Go an interpreter for its subset.
4. Take the shared parts out of the TypeScript code, now that Go uses them
   too: the pure core of the output tree, its printer, its evaluator with the
   value type as a parameter, and the proof plumbing. Taking them out before
   a second language uses them would fit them to TypeScript alone.
5. Add the piece for external calls, and move Go's interface calls onto it.
6. Do the same for SQL.

## Open questions

- The effects plan writes class constraints such as `[Monad m] [Observe m]`,
  so generated code is generic over the monad. This plan uses one concrete
  monad per language, because proofs about it are faster. One answer is that
  the classes stay the interface, the pieces give the instances, and a
  certificate is about the concrete instance. Does that keep the proofs fast
  enough?
- Should the output tree have a fixed set of effect nodes, or one point where
  each language adds its own?
- How should loops that may not end appear in the output: with fuel, as they
  do now, or with a `div` result as in Aeneas?
