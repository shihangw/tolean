# Go named types on the proved path

**Status:** accepted · **Date:** 2026-11-26

The proved path now reads a type that a package declares over a predeclared
type, such as `type Celsius int`, `type Open bool`, `type Name string` or the
alias `type Count = int64`, and conversions to such a type. This record says
how the interpreter, the translator and the proof treat them.

## The decision

- **The interpreter.** `Eval.Program` holds each such type with the name of
  its underlying type. The zero value of the type is that of its underlying
  type ("The zero value"). A call of the type's name is a conversion
  ("Conversions"). It keeps the value, because every value of the subset has
  the same representation in a type and in its underlying type. The
  interpreter has no rule for an integer converted to a string type, which
  gives a code point, so it gives no result there.
- **The translator.** A named type is its underlying type. The output types a
  parameter `c Celsius` as `Int` and writes `Celsius(x)` as `x`. The string
  translation still writes `abbrev Celsius := Int` for the rest of the file.
- **Type checking stays with Go.** The translator does not keep `Celsius`
  apart from `int`. It would accept `c + x` for a `Celsius` `c` and an `int`
  `x`, which `go build` refuses. The proof needs no such check, because the
  interpreter has no types: the output computes what the interpreter does for
  every program, typed or not. The CLI's input is a package that compiles,
  and the differential test compiles each program with `go run`.
- **Conversions to a string type stay off the proved path.** Go allows
  `Name(65)` and gives `"A"`. The proof has no type invariant on values that
  would show an operand of type `string` is a string, so the translator
  refuses every conversion to a type over `string`. Locals, parameters and
  constants of such a type are fine, because they need no conversion.
- **Other conversions.** The subset converts an integer to a type over `int`
  or `int64`, as it already did for `int(x)` and `int64(x)`, and a bool to a
  type over `bool`.
- **Left out:** a type over another type of the package, as in
  `type Temp Celsius`, which needs the chain of underlying types; a type over
  a composite type, which waits for structs; and methods.
