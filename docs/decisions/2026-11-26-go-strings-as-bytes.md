# Go strings as bytes

**Status:** accepted · **Date:** 2026-11-26

A Go string is a sequence of bytes. `len(s)` counts its bytes, `s[i]` reads
one byte, and `<` compares two strings byte by byte (Go specification,
"String types", "Index expressions" and "Comparison operators"). The Go
interpreter keeps a string as a Lean `String`, which is a sequence of
Unicode characters. This record settles the open question of the
[Go proofs plan](../plans/go-proofs.md): should strings become lists of
bytes, as TypeScript's became lists of UTF-16 code units?

## The decision

- The interpreter keeps a Lean `String`, and it reads the bytes of a string
  through `String.toUTF8`. Every string that the proved subset can make is
  valid UTF-8: a literal, a parameter, and the concatenation of two such
  strings. A Lean `String` holds exactly the valid UTF-8 byte sequences, so
  it loses nothing that the subset can reach.
- `len(s)` gives the number of bytes. The output writes `Go.byteLen s`.
- `s[i]` gives the byte at index `i`, as an integer from 0 to 255. The
  output writes `Go.byteAt s i`. When `i` is negative or not below
  `len(s)`, Go panics, and the interpreter panics with Go's message, such as
  `runtime error: index out of range [5] with length 3`. A negative index
  gives `runtime error: index out of range [-1]`, without the length.
- The output tests each index before the statement, as it tests divisors
  (see the [record on panics](2026-11-26-go-panics.md)). `Go.indexFault s i`
  gives the message, or the empty string when the index is in range. The
  checks of a statement stay in Go's order of evaluation, and the output
  tests them one at a time, because the first check that fails decides the
  message. A statement that only divides keeps its one test of all the
  divisors, so its output does not change.
- When a check fails, the output throws `Go.after c m`. It evaluates the
  statement's expression `c`, as the interpreter does before it reaches the
  check, and it throws the message `m`.
- The orders `<`, `<=`, `>` and `>=` on strings compare the UTF-8 bytes. The
  output writes `Go.strLt a b` and the others. On valid UTF-8, this order is
  the order of code points, but the definition states the bytes, as Go does.
- `+` on strings stays `++`, and `==` and `!=` stay as they are.
- A byte has its own type in the translator. The subset converts it with
  `int(s[i])` or `int64(s[i])` and refuses any other use of it.

## What is refused

- **Slices of strings, `s[i:j]`.** A slice can cut a UTF-8 sequence in two,
  as `"é"[1:]` does, and no Lean `String` holds the result. Supporting it
  would need a byte list for every string, and every string function of the
  output would change.
- **`range` over a string, and conversions to and from `[]rune`.** They
  decode UTF-8, and Go replaces each invalid byte with U+FFFD. They are only
  useful together with slices, which the subset refuses.
- **Byte arithmetic and rune literals.** A `byte` wraps at 8 bits, and a
  rune literal such as `'a'` is an untyped constant whose type depends on
  its use. The subset converts a byte to `int` before any arithmetic.
- **An index in the right operand of `&&` or `||`.** Go might not evaluate
  it, so a failed check would not mean a panic. Divisions are refused there
  for the same reason.

## Alternatives

- **Strings as lists of bytes everywhere.** The interpreter could model a
  string as `List UInt8`, as TypeScript models a string as UTF-16 code
  units. It would admit slices, but the output would need byte lists too,
  and the printed Lean would lose `String` and its literals for every
  function, including those that only concatenate.
- **A string of runes.** Lean's `String` operations count characters, not
  bytes. Using `String.length` for `len(s)` would be wrong for any string
  with a character outside ASCII.
