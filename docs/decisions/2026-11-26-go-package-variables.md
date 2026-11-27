# Go package-level variables that nothing changes

**Status:** accepted · **Date:** 2026-11-26

The proved path now reads a package-level `var` when no code can change it.
It does not yet support a variable that some function assigns. This record
says why the two cases differ, and why the state piece of shared-core step 3
is still not built.

## The decision

- A package-level variable joins the interpreter's values when it declares
  one unexported name, its initial value is a literal of the kind that a
  [constant](2026-11-26-go-package-constants.md) may have or it has a type
  and no value, and nothing in the package writes it. A write is an
  assignment, `++` or `--`, a `range` with `=`, or `&`, anywhere in a
  function, method, `init` function, function literal or initial value.
- The check in `tolean/Go/Spec/Eval.lean` reads syntax only. It counts a
  local of the same name too, which only refuses more.
- Such a variable keeps its initial value for the whole run, because Go
  initializes a variable with a literal value before any `init` function
  runs ("Package initialization"). So the interpreter reads it as it reads a
  constant, and the proof of constants covers it unchanged.
- An exported variable stays out, because another package can assign it.
- The string translation writes a `def` for `var x T` with no value, at the
  zero value of `T`. It refused such a variable before.

## Why the state piece waits

A variable that a function assigns needs state: the interpreter, the IR
evaluator and the output would thread the package's variables through every
call. Two questions block a design that the proof can follow. First, Go
leaves part of the order of evaluation unspecified: in `x + f()`, where `f`
assigns `x`, Go does not say whether `x` is read before or after the call.
The translator would have to refuse every such read, and the interpreter
would need a rule that says which reads are determined. Second, the
functions that the string translation writes can assign a variable too,
and a proved function that reads it would depend on code that has no proof.
Then the claim would hold only for programs where every writer is proved.

Both questions concern every user of the state piece, and TypeScript's
mutable objects raise the second one as well. So the piece belongs in a
change of its own, with its decision record, rather than in this one.
