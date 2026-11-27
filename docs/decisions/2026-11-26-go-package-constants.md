# Go package-level constants on the proved path

**Status:** accepted · **Date:** 2026-11-26

A pure Go function may now read a constant that its package declares at the
top level. This record says which constants the proved path accepts, how the
output writes them, and why package-level `var` declarations stay on the
string translation.

## The decision

- The interpreter in `tolean/Go/Spec/Eval.lean` gives `Program` a list of
  constants. A constant joins the list when its spec declares one name with
  one value, and the value is an integer or string literal, an integer
  literal after `-`, or `true` or `false`. The Go specification defines these
  in "Constants" and "Constant declarations". A name in an expression is a
  local first, then a constant of the package, then a predeclared name, as
  "Declarations and scope" says.
- Any other constant leaves the subset: a spec without a value, which repeats
  the one before it with `iota`; a constant built from another constant or an
  operator; and a rune or floating-point constant. A function that reads one
  stays on the string translation.
- The translator gives a constant without a type the type that its literal
  has: an untyped integer, a `string` or a `bool`. A typed constant has its
  declared type, which must be `int`, `int64`, `bool` or `string`. An integer
  constant must fit in `int64`.
- The output writes the constant's value where the function reads it. The
  string translation still writes a `def` for each constant that the roots
  reach, so a reader sees the name next to the value.

## Why the value and not a reference to the `def`

The IR has no expression that names a top-level value, and its evaluator
looks a name up in the locals only. A reference would need a new IR node,
an evaluator case and a printer case, for a value that the output can write
as a literal. The value also keeps the existing division rules: the output
tests no divisor that is a nonzero literal, and the translator refuses a
constant zero divisor, which Go refuses too.

## Why constants need no state

A constant cannot change, so the interpreter can hold its value in the
program, next to the functions. Shared-core step 3 asks Go to build the
state piece with its first package-level variable. This record does not add
it, because a constant does not need it. A package-level `var` does: another
function, or an `init` function, can assign it before the pure function
runs, and the proved path would have to follow every such assignment. So
`var` stays on the string translation until the state piece exists.

## Untyped constants stay exact

Go computes with untyped constants exactly, and the output computes with
wrapping 64-bit integers. The translator already refuses an operator on two
untyped constants, and a constant of the package is untyped in the same way
as a literal, so `A + B` with two untyped constants is refused too. A typed
constant expression that overflows does not compile in Go, so it cannot
disagree with the output.
