# Go structs on the proved path

**Status:** accepted · **Date:** 2026-11-26

A pure Go function may now build a struct with a composite literal, read its
fields and assign one field of a local struct. This record says which forms
the proved path accepts, how the output writes them, and why the other forms
stay on the string translation.

## The decision

- The interpreter in `tolean/Go/Spec/Eval.lean` gives `Program` the struct
  types that the package declares, with each field's name and type, and adds
  a struct value: its fields in declaration order. The Go specification
  defines these in "Struct types", "Composite literals" and "Selectors".
- A struct type joins the subset when it has no embedded field, its field
  names are distinct, and every field has one of the types `int`, `int64`,
  `bool` or `string`. A function that uses any other struct stays on the
  string translation.
- A literal joins the subset in three forms: `S{}`, which gives each field
  its zero value; `S{a, b}`, which gives every field in order; and
  `S{X: a, Y: b}`, which names every field once, in declaration order. Go
  evaluates the elements left to right, so the output does too, and a
  division by zero in an element panics before the struct exists.
- `x.f` reads a field of any expression of a struct type. `x.f = e` sets one
  field, when `x` is a local. The interpreter evaluates `e`, then replaces
  the field in `x`, as "Assignment statements" says.
- The output uses the shared IR's `struct`, `field` and `structUpdate`
  nodes, which the TypeScript path already prints: a `structure` with a
  default for each field, `{ X := a, Y := b }` for a literal, `p.X` for a
  read, and `{ p with X := e }` for an assignment. Go adds no IR node.

## Why some forms are refused

- `var p S` without a value: the interpreter gives the zero struct, and the
  translator would need a zero code for each struct type. `S{}` writes the
  same value and is accepted, so the refusal costs one rewrite.
- A keyed literal with some fields missing or out of order: Go fills the
  missing fields with zero values and still evaluates the elements in the
  order written. Accepting it would make the proof follow two orders. The
  forms above cover the common uses, and the rest can come later.
- `==` and `!=` on structs: the output would need a decidable equality on
  every generated structure. The proved path refuses the comparison until a
  program needs it.
- A field whose type is a struct, a named type or anything else outside the
  four basic types, and embedded fields: each needs its own rules for zero
  values and selectors.
- A field assignment through anything but a local, such as `f().x = 1`,
  which Go refuses anyway, or `a.b.c = 1`, which needs nested updates.

## Proof

`translate_sound` covers every case. `Proof/Expr.lean` proves that a
selector reads the field the interpreter reads, and that a literal's code
gives the struct that the interpreter builds, with the divisors of its
elements in order. `Proof/Stmt.lean` proves the field assignment with the
same steps as `x = e`. The differential generator writes a struct type for
some programs, with literals of all three forms, field reads and field
writes, and the corpus package `structs` shows the output.
