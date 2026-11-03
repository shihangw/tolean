# The Tolean IR

**Status:** accepted, except printing through `Lean.Syntax`, which is to try · **Date:** 2026-10-30

The Tolean intermediate representation, or Tolean IR, is the form a program
takes after Tolean translates it and before it becomes Lean text. It is a
small language of Lean code, written as Lean data: types, expressions,
bodies and declarations. Three parts of Tolean use it. The translator builds
it, the printer writes it as Lean text, and an evaluator gives it a meaning.

```
source ──parser──▶ syntax tree ──translator──▶ Tolean IR ──printer──▶ Lean text
                        │                          │
                  interpreter                  evaluator
                        └────── program_sound ─────┘
```

Because the IR has a meaning of its own, a theorem can relate it to the
source. `program_sound` states that for every program that the translator
accepts, the IR computes only what the interpreter computes for the source.
A certificate then proves, for one file, that the printed Lean computes what
the IR computes.

Today only TypeScript has an IR, in `tolean/TypeScript/IR.lean`. This record
explains three choices about it.

## 1. The IR is our own type, not `Lean.Expr`

Lean already has a type for its terms, `Lean.Expr`, so the translator could
build those instead of a type of its own. We chose not to, for four reasons.

**`Lean.Expr` has no meaning that a theorem can use.** `program_sound` needs
a function, written in Lean, that says what each IR term computes. Lean
cannot define such a function for its own terms in general. A term's meaning
depends on the constants of an environment, and a logic cannot define the
meaning of all of its own terms inside itself. With our own type, the
evaluator in `IR/Eval.lean` is an ordinary total function, and the proofs
unfold it.

**`Lean.Expr` is the form after elaboration.** It has de Bruijn indices,
universe levels, implicit arguments and instances that elaboration has
already filled in. To build it, the translator would have to do the
elaborator's work itself, such as finding each type class instance. The
Tolean IR stays at the level of the code that a person reads, and Lean's
elaborator does that work when it compiles the printed text.

**`Lean.Expr` can say anything.** A proof about the translator has a case for
each form that the IR has. The Tolean IR has only the forms that the
translator writes, so the proofs stay as small as the translation.

**The kernel runs our own type directly.** A certificate makes the kernel
run the translator and compare its IR with the one that the certificate
holds. That needs an equality that the kernel can decide, which
`IR/Equality.lean` proves for the IR. It needs nothing from Lean's
environment.

## 2. Shared primitives, with constructs for each language

Most of the IR is not about TypeScript. Integers, booleans, strings,
`Option`, `List`, structures, `let`, `if`, a match on `Option`, a fold over a
list and function declarations are the same for Go. What belongs to one
language is small. For TypeScript, it is JavaScript numbers: the number type
`N`, its operators, its constants such as `NaN`, and `null`.

So the IR becomes a shared core with one extension point for each layer,
and each language adds its own constructs there. The core also reuses Lean's
own types for values, such as `Int`, `String`, `List` and `Option`, as the
IR does now. The first step of the [shared core plan](../plans/shared-core.md)
moves the core to `tolean/IR/` and makes JavaScript numbers the first
extension. Go's translator then builds the same IR, with its own extension
for `int64`.

## 3. Printing through `Lean.Syntax`: to try

Our printer, in `IR.lean`, writes Lean text by hand. Lean's own parser and
formatter could write it instead: the printer would build a `Lean.Syntax`
tree, and Lean's formatter would write the text. This is worth trying,
because code that Lean supports officially, and that every Lean user runs,
deserves more trust than a printer of our own. Text that Lean's formatter
writes from a syntax tree is text that Lean's parser reads back as that tree.

It would not remove the printer link. The link is about meaning: the printed
Lean must compute what the IR computes. A certificate proves that for its
file, whichever printer wrote the text. So the change makes printing bugs
rarer, but a file without a certificate still trusts the link.

These questions decide whether it works:

- **The environment.** Lean's formatter reads the parser tables of an
  environment, so the printer would run in `CoreM` with Lean's core
  imported. Today the printer is a pure function.
- **The WebAssembly build.** The playground runs the translator in the
  browser. The formatter needs Lean's environment there too, and that may be
  too large to load.
- **Readability.** Lean's formatter chooses its own line breaks. The output
  must stay as easy to read as it is now, and the golden files of the corpus
  would all change once.

A first step is to print each corpus file both ways behind a flag, and check
that every certificate still passes and that the WebAssembly build still
runs.
