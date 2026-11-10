# Plan: prove the Go translator

**Status:** in progress · **Date:** 2026-11-09

The TypeScript translator is proved for every program it accepts. The Go
translator is proved only for pure functions: those that take and return
`int`, `int64`, `bool` and `string` values, and whose bodies declare and
assign locals, test with `if` and return. The [Go guide](../go/README.md)
describes that part. Everything else still goes through the older string
translation in `tolean/Go/Translate.lean`, which Lean cannot reason about,
because it builds text with `partial def`.

This plan moves the rest of the Go subset onto the proved path, one
construct at a time, until the string translation can be deleted. It is
step 5 of the [shared core plan](shared-core.md), and it uses the state and
exception pieces that step 3 of that plan adds to the IR.

## The rules for every addition

Each construct keeps the rules that TypeScript's do.

1. **The Go specification defines the behavior.** The interpreter in
   `tolean/Go/Spec/Eval.lean` follows the section that defines the
   construct, and a comment names it. Behavior that depends on the platform
   or the scheduler stays refused.
2. **The translation sees every change to state.** A value that two names
   can reach, such as the target of a pointer or the backing array of a
   slice, changes only where the translation can see the change.
3. **The proof covers it.** Each construct extends `Pure.lean`, the IR and
   its evaluator, and the interpreter, so that `translate_sound` holds for
   programs that use it.

## What to add

A construct leaves these tables when the proved path translates it, and the
Go guide documents it from then on.

### Values and types

| Go | Lean | Refused |
|---|---|---|
| A package-level `const` or `var` that a pure function reads | A `def` | A `var` that some function assigns |
| A named type, such as `type Side string` | `abbrev` | Methods on a named type of a basic type, until methods are added |
| A struct, its composite literals and its fields | A structure, and `{ s with f := e }` for an assignment to a field | Embedded fields, and a struct that a pointer can reach |
| A function with several results, and `a, b := f()` | A tuple | Named results |
| `error`, `errors.New` and `fmt.Errorf` with a leading `%w` | `Option GoError`, as today | Other uses of `fmt` |

### Operators

| Go | Lean | Refused |
|---|---|---|
| `/` and `%` on integers | `Int.tdiv` and `Int.tmod` in `Except`, because a division by zero panics, and `MinInt64 / -1` wraps | Constant expressions, as now |
| `<` and the other orders on strings | The order of UTF-8 bytes | |
| `len(s)` on a string | The number of UTF-8 bytes | Indexing a string, until the interpreter models bytes |

### Statements and loops

| Go | Lean | Refused |
|---|---|---|
| `switch` with a tag, and without one | A chain of `if` | `fallthrough`, which the parser refuses |
| `for i := a; i < b; i++` | A fold whose state records that the loop stopped | Other counted loops |
| `for _, x := range xs` over a slice, with `break`, `continue` and `return` | `List.foldl`, or `forIn`, as for TypeScript's `for … of` | A loop that changes the slice it ranges over |
| An `if` with an init statement, such as `if v := f(); v > 0` | A `let` before the `if` | |

### Slices

| Go | Lean | Refused |
|---|---|---|
| `[]T{…}`, `len`, `append` and `xs[i]` | `List T`, with `xs[i]?` in `Except` for an index out of range | A slice that the function shares and also changes, since two slices can share a backing array |
| `make([]T, 0, n)` | `[]` | `make` with a nonzero length |

### Methods and effects

| Go | Lean | Refused |
|---|---|---|
| A method on a value receiver | A function that takes the receiver first | Pointer receivers |
| A call of a method on an interface parameter, such as a store | A step in `StateM State`, as today, built from the shared piece for external calls | Interfaces that the package implements itself |
| Code that only feeds observability, such as tracing | Nothing: the translator erases it, as today, and a proof shows that the erased statements change no other value | |

### Checks

| Check | What it does |
|---|---|
| The interpreter against Go | Run random pure programs with `go run` and with the interpreter, and compare the results, as `tests/typescript/interpreter.test.ts` does with Node |
| Certificates | Prove the printer link for one file, as TypeScript's certificates do |

## Open questions

- The interpreter assumes that `int` is 64 bits wide, as it is on every
  64-bit platform. Should the translator refuse `int` and accept only
  `int64`, so that a claim holds on 32-bit platforms too?
- A Go string is a sequence of bytes, and the interpreter models it as a
  Lean `String`, which is a sequence of Unicode characters. The two agree for
  the operations of the subset on valid UTF-8. Indexing a string would need
  the bytes. Should strings become lists of bytes, as TypeScript's became
  lists of UTF-16 code units?
- Recursion: the proved path refuses a function that calls itself, because
  Lean would need a proof that the recursion ends. TypeScript's plan has the
  same open question.
