# Plan: prove the Go translator

**Status:** in progress · **Date:** 2026-11-09

The TypeScript translator is proved for every program it accepts. The Go
translator is proved only for pure functions: those that take and return
`int`, `int64`, `bool` and `string` values, and whose bodies declare and
assign locals, read the package's literal constants, use types declared over a basic type, test with `if` and
`switch`, and return. The [Go guide](../go/README.md)
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
| A package-level `var` that a pure function reads, and a `const` built with `iota`, another constant or an operator | A `def` | A `var` that some function assigns |
| A conversion to a named type over `string`, and a named type over another named type or over a composite type | `abbrev` | Methods on a named type of a basic type, until methods are added |
| A struct, its composite literals and its fields | A structure, and `{ s with f := e }` for an assignment to a field | Embedded fields, and a struct that a pointer can reach |
| A function with several results, and `a, b := f()` | A tuple | Named results |
| `error`, `errors.New` and `fmt.Errorf` with a leading `%w` | `Option GoError`, as today | Other uses of `fmt` |

### Statements and loops

| Go | Lean | Refused |
|---|---|---|
| `for i := a; i < b; i++` | A same-type integer list, lowered through the [shared loop core](../decisions/2026-11-22-shared-loop-core.md) to `Body.fold`. The bound must not refer to the counter and must stay unchanged by the header update and the body. | Other updates or tests, mixed-type bounds, and bodies that assign the counter or change what the bound reads |
| `for _, x := range xs` over a slice or array, with `break`, `continue` and `return` | Elements in order through the shared loop core, printed as `List.foldl` or `forIn`, with the shared return carrier where needed | A body that changes the iterable, including through an alias; range over a map, channel or function iterator |
| `for i := range xs` or `for i, x := range xs` over a slice or array | Indices or index-value pairs through the same shared loop core | Lengths outside the modeled `int` range and the same mutation restrictions |
| An `if` with an init statement, or a `switch`, that returns on some path and has statements after it, such as `if v := f(); v > 0 { return v }; return 0` | The `let` of the init statement in front of the code after the `if` | Nothing yet. The translator refuses this form, because the code after the statement would run where the init statement's name is still bound. The [decision record](../decisions/2026-11-26-go-switch-as-if-chain.md) explains why. |

Go supplies each loop head and its `HeadSim`, not a second fold proof.
The shared interpreter requires `brk` and `cont` cases in Go's `Outcome`.
Its evaluator and soundness layers depend on step 6 of the
[shared-core plan](shared-core.md); step 9 there records the loop work.
Labeled jumps and `goto` remain refused. The loop-core decision does not
change the separate work on `switch` and `if`.

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
| Certificates | Prove the printer link for one file, as TypeScript's certificates do |

## Open questions

- The interpreter assumes that `int` is 64 bits wide, as it is on every
  64-bit platform. Should the translator refuse `int` and accept only
  `int64`, so that a claim holds on 32-bit platforms too?
- Recursion: the proved path refuses a function that calls itself, because
  Lean would need a proof that the recursion ends. TypeScript's plan has the
  same open question.
