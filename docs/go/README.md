# Go

Tolean translates Go code that has effects. A function that calls methods on
an interface, such as a database store, becomes a function in a state monad,
so a proof can plug in a model of what the interface does. The
[README](../../README.md) describes the parts that all languages share.

[This graph](verification.svg) shows the verification chain for Go. It
marks which links are proved, tested against a reference, or trusted.

## The translator

### Parsing

`tolean/Go/Syntax/` puts on every node the span that `go/ast` gives it, and it
inserts semicolons at line breaks as the Go specification requires. It reads:

- **Declarations:** `package`, imports, `const`, `var` and `type` (including
  aliases), each alone or grouped; functions and methods.
- **Types:** names and qualified names, pointers, arrays, slices, maps, structs
  (with embedded fields and tags), interfaces (with embedded interfaces),
  function types and `...` parameters.
- **Statements:** blocks, `:=`, `=` and the compound assignments, `++` and
  `--`, declarations, `return`, `break` and `continue`, `if` with an init
  statement and `else`, the three forms of `for`, `range` with `:=`, `=` or
  no variables, `switch` with an init statement and a tag, type switches and
  `defer`.
- **Expressions:** names; integer (decimal, hex, octal, binary, with
  separators), floating-point, rune, string and raw string literals; composite
  literals, including those whose element type is left out; selectors,
  indexing, two-index slicing, calls with `...`, unary and binary operators,
  type assertions and function literals. Like `go/parser`, it does not read `T{` as a
composite literal in the header of `if`, `for` or `switch` when `T` is a plain
type name, unless the literal is in parentheses.

The parser refuses generics, channels, `go`, `goto`, `select`, labels,
`fallthrough`, three-index slices, `[...]T` arrays, imaginary literals and
non-ASCII names. It reads type switches, type assertions, function literals
and `defer` even though the translator refuses them, so that a file can be
read when the translator needs only some of its declarations.

`tests/go/check` checks the parser against `go/parser`.
`tests/go/goast` prints the tree from `go/parser` in the same S-expression
form, with columns counted in code points, and it refuses the node kinds that
the Lean parser does not read:

- For `corpus/parse/accept/*.go`, both parsers must accept the file, and the
  two trees must be equal, spans included.
- For `corpus/parse/reject/*.go`, the Lean parser must refuse the file. The
  first line gives the line, the column and part of the message to expect.
- Any Go file named on the command line is checked like an accepted file.

### Translation

`tolean/Go/Translate.lean` translates one Go package at a time. It starts
from the functions named with `--root` and keeps only the declarations they
reach, so a file can hold code that Tolean does not support:

```sh
tolean translate-go --root Post --erase-type Log --erase-package time \
  Ledger.lean Ledger ledger.go
```

The generated code imports `tolean/Go/Spec/Basic.lean`, the trusted model of
Go values. Review it with care.

- A function that calls a method on an interface parameter, such as a store,
  becomes a function in `StateM State`. The interface becomes a structure that
  holds the methods the code calls, so a proof can plug in a model of the
  store.
- A `range` loop over a slice becomes its own recursive function. `continue`
  is the recursive call, `break` returns the locals that the loop changes, and
  `return` leaves the function with its result.
- `int` and `int64` arithmetic wraps as Go's does, through `Go.wrap64`. A
  proof shows that the values stay in range and then reasons over `Int`.
- An `error` is `Option GoError`. Tolean models how an error was made
  (`errors.New`, or `fmt.Errorf` with a leading `%w`) and drops the rest of
  the message.
- Code that only feeds observability is erased. A statement is erased when it
  reads a value of a type named by `--erase-type` or calls a package named by
  `--erase-package`. Tolean refuses to erase a statement unless it only
  assigns through the erased value, so that erasing it cannot change any
  other value.

`tests/go/check` also translates each package in `corpus/translate/*/` with
the options in its `args` file. The result must equal the committed `.lean`
file in the same directory, and Lean must compile it. The corpus package
`ledger` posts a double-entry journal entry, and `fees` computes the fee on
a transfer with pure functions.

### What is proved

A pure function takes and returns `int`, `int64`, `bool` and `string`
values and calls only other pure functions. Its body may declare locals with
`:=` or `var`, assign them with `=`, `+=`, `-=`, `*=`, `++` and `--`, test
with `if` and `else`, and return. The translator writes each pure function
through `tolean/Go/Translate/Pure.lean`, which proves that translation, and
it writes everything else as before.

`Pure.lean` is a total function, so Lean can reason about it. It does not
write text. It builds the [Tolean IR](../decisions/2026-10-30-tolean-ir.md),
the Lean code it writes as Lean data. `tolean/Go/IR.lean` adds what only Go
needs to the shared IR: `Go.wrap64` and `++` on strings.
`tolean/Go/IR/Eval.lean` gives the IR a meaning.

`tolean/Go/Spec/Eval.lean` is an interpreter for the pure subset. It runs
the syntax tree that the parser returns and follows the Go specification.
The theorem `translate_sound` in `tolean/Go/Proof/Package.lean` states that
when a function of the IR gives a value for a call, the interpreter gives
the same value for the same call of the source's function. It holds for
every package, every input and every amount of fuel. The proof follows the
one for TypeScript, in three files: `Proof/Expr.lean` for expressions,
`Proof/Stmt.lean` for statements and `Proof/Package.lean` for calls.

The translator types each expression as Go does. An integer literal is an
untyped constant that takes the type of the other operand. The translator
refuses an operator on two constants, because Go computes such an operator
exactly at compile time. In Go, `9223372036854775807 + 1 > 0` is true, but
the wrapping arithmetic of the output would make it false.

Three links of the chain are still trusted for a pure function. The parser
is tested against `go/parser`. The printer writes the IR as Lean text, and
the corpus tests it. The interpreter states what Go means, and no test
compares it with the Go runtime yet.
