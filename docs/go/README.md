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
`:=` or `var`, assign them with `=`, `+=`, `-=`, `*=`, `/=`, `%=`, `++`
and `--`, test with `if`, `else` and `switch`, and return. The translator writes each pure
function through `tolean/Go/Translate/Pure.lean`, which proves that
translation, and it writes everything else as before.

An `if` may have an init statement, as in `if d := x - y; d > 0 { … }`. A
`switch` may have a tag or none, an init statement, several values in one
case, and a `default` clause anywhere in its body. The translator writes a
switch as the chain of `if` statements that Go's rules give it: the first
case value that equals the tag picks its clause, and `default` runs when
none does. A plain block `{ … }` is accepted too. `Proof/Switch.lean` proves
that the interpreter gives each of these statements the meaning of the
statements that the translator writes for it.

Some forms of these statements stay on the string translation. An `if` with
an init statement, a `switch` or a block that returns on some path must be
the last statement of its list, so `if v := f(); v > 0 { return v }` cannot
be followed by more code. A switch with a tag needs at least one case value,
because only a case test evaluates the tag. A case with several values
becomes a `||` of tests, so a value after the first may not divide, and
neither may the tag of such a switch. `break` inside a switch is refused. The [decision record](../decisions/2026-11-26-go-switch-as-if-chain.md)
gives the reasons.

Integer `/` and `%` become `Int.tdiv` and `Int.tmod`, which round toward
zero as Go does. `/` wraps through `Go.wrap64`, so `MinInt64 / -1` is
`MinInt64`, as in Go. Go panics when the divisor is zero, and Lean's
division gives zero instead, so a statement that divides first tests each
divisor that is not a nonzero literal. When one of them is zero, the function
throws Go's message, `runtime error: integer divide by zero`. A function that
can panic returns `Except String T` and `pure` of its value; a function whose
divisors are all nonzero literals still returns `T`:

```lean
def Quo (a : Int) (b : Int) : (Except String Int) :=
  if b = (0 : Int) then
    let _ := (Go.wrap64 (Int.tdiv a b))
    throw ("runtime error: integer divide by zero")
  else
    (pure (Go.wrap64 (Int.tdiv a b)))
```

The translator refuses a division by the constant zero, which Go refuses
too, and a division in the right operand of `&&` or `||`, which Go might not
evaluate. It also refuses a call of a function that can panic, from a pure
function or from the rest of the package, until calls in `Except` are
added. The corpus package `divide` shows the output.

The proved path also accepts a counted loop as the first statement of a
function: `for i := a; i < b; i++ { body }`. Both bounds must be nonnegative
integer literals below `2^63`, and the loop may take at most 256 iterations.
The counter must have a fresh, unreserved name. The body may update parameters,
declare iteration-local variables, and use the existing non-returning `if`
forms. For example, `func Sum(total int) int` may start with
`for i := 0; i < 10; i++ { total += i }` and then return `total`.
Arithmetic in the body still wraps.

The bounds become a list of integers, and the shared `IR.Body.fold` threads
the changed locals. `LoopFrame.loop_refines` uses
`Core.Loop.execLoop_refines` to connect the source loop with that fold.
`top_sound` connects the leading loop and its continuation to the existing
package theorem. A panic in the body ends the loop, as a return does.
The interpreter records the Go specification's “For statements with for
clause” rule next to its counted-loop case.

This first proved form refuses early return, `break`, `continue`, nested loops,
and loops after another statement. It also refuses computed bounds, other
comparison or update operators, counter mutation, and more than 256
iterations. The limit keeps the literal list emitted by this lowering within
Lean's compilation recursion depth.
The other restrictions keep the loop within the existing state-only body
translation and the leading-loop proof. Slice ranges remain outside the proved
path because its value model has no slices. The older string translator's
range support is unchanged and is not covered by this theorem.

`Pure.lean` is a total function, so Lean can reason about it. It does not
write text. It builds the [Tolean IR](../decisions/2026-10-30-tolean-ir.md),
the Lean code it writes as Lean data. `tolean/Go/IR.lean` adds what only Go
needs to the shared IR: `Go.wrap64`, `++` on strings, and `pure` for the
value of a function that can panic. The shared IR gives `Int.tdiv`,
`Int.tmod` and `throw`.
`tolean/Go/IR/Eval.lean` gives the IR a meaning.

`tolean/Go/Spec/Eval.lean` is an interpreter for the pure subset. It runs
the syntax tree that the parser returns and follows the Go specification.
The interpreter has an outcome for a panic next to the one for a return. The
theorem `translate_sound` in `tolean/Go/Proof/Package.lean` states that when
a function of the IR returns a value for a call, or throws, the interpreter
returns the same value for the same call of the source's function, or panics
with the same message. It holds for
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
the corpus tests it. The interpreter states what Go means, and a test
compares it with the Go runtime on random programs.

That test is `tests/go/differential`. It writes random functions of the
proved subset, calls each one with random arguments, and requires four
results to agree: the value that `go run` prints, the interpreter's value,
the value of the IR that `Pure.lean` builds, and the value of the Lean code
that `tolean translate-go` prints. It also requires that `Pure.lean`
accepts every generated function, so a generator that leaves the subset
fails loudly instead of testing less. The test checks a sample, so it is
evidence for the interpreter and the printer, not a proof. It assumes that
`int` is 64 bits wide, as the interpreter does, so it runs on a 64-bit
platform. When the subset grows, the generator should grow with it. Run it
from `tests/go` after `lake build`:

```sh
go run ./differential
```

`TOLEAN_SEED` repeats a run, `TOLEAN_PROGRAMS` sets the number of random
programs, and `TOLEAN_KEEP=1` keeps the generated files.
