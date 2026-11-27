/-!
The model of Go values that code generated from Go imports. Proofs assume
only what this file states, so review it with care.

- `int` and `int64` are `Int`, and every arithmetic result passes through
  `wrap64`, which wraps it into the 64-bit range as Go does.
- `error` is `Option GoError`: `none` is `nil`. Tolean models only how an error
  was made (a sentinel from `errors.New`, or `fmt.Errorf` with a leading `%w`)
  and drops the message text of `fmt.Errorf`.
- `context.Context` carries nothing: translated code only passes it along, so
  no theorem can depend on what it holds.
-/
namespace tolean.Go

/-- Go's `int64` wraps around on overflow. -/
def wrap64 (x : Int) : Int := (x + 2 ^ 63) % 2 ^ 64 - 2 ^ 63

theorem wrap64_of_range {x : Int} (lo : -2 ^ 63 ≤ x) (hi : x < 2 ^ 63) : wrap64 x = x := by
  unfold wrap64
  rw [Int.emod_eq_of_lt (by omega) (by omega)]
  omega

/-! ### Strings as bytes

A Go string is a sequence of bytes. The translation keeps a Go string as a
Lean `String`, whose bytes are its UTF-8 encoding, and every string that the
proved subset can make is valid UTF-8. The functions below read those bytes,
as Go's `len`, indexing and orders do. -/

/-- The bytes of a string: its UTF-8 encoding. -/
def bytes (s : String) : List UInt8 := s.toUTF8.toList

/-- `len(s)`: the number of bytes of `s`. -/
def byteLen (s : String) : Int := (bytes s).length

/-- `s[i]`: the byte at index `i`, as an integer. An index out of range gives
`0`, and the translation tests the index first (`indexFault`). -/
def byteAt (s : String) (i : Int) : Int := ((bytes s).getD i.toNat 0).toNat

/-- `a < b` on strings: the lexicographic order of their bytes. -/
def strLt (a b : String) : Bool := decide (bytes a < bytes b)

/-- `a <= b` on strings. -/
def strLe (a b : String) : Bool := decide (bytes a ≤ bytes b)

/-- `a > b` on strings. -/
def strGt (a b : String) : Bool := decide (bytes a > bytes b)

/-- `a >= b` on strings. -/
def strGe (a b : String) : Bool := decide (bytes a ≥ bytes b)

/-- The message of the panic of an index `i` out of the range of a string of
`n` bytes. Go writes a negative index without the length. -/
def indexMessage (i n : Int) : String :=
  "runtime error: index out of range [" ++
    (if i < 0 then s!"{i}]" else s!"{i}] with length {n}")

/-- The message of the panic that `s[i]` causes, or `""` when `i` is in
range. -/
def indexFault (s : String) (i : Int) : String :=
  if 0 ≤ i ∧ i < byteLen s then "" else indexMessage i (byteLen s)

theorem indexMessage_ne (i n : Int) : indexMessage i n ≠ "" := by
  intro h
  have h' := congrArg String.length h
  have : "runtime error: index out of range [".length = 35 := by decide
  simp only [indexMessage, String.length_append, String.length_empty] at h'
  omega

/-- The values `a`, `a + 1`, and so on, below `b`: the values that the counter
of `for i := a; i < b; i++` takes. The list is empty when `b ≤ a`. -/
def upTo (a b : Int) : List Int := (List.range (b - a).toNat).map fun (k : Nat) => a + k

/-- The value `m`. The output of a failed check writes `Go.after c m` so that
it evaluates `c`, the expression that Go was evaluating, before it panics with
`m`. -/
def after {α β : Sort _} (_ : α) (m : β) : β := m

/-- How an error value was made. -/
inductive GoError where
  /-- `errors.New(text)`. -/
  | sentinel (text : String)
  /-- `fmt.Errorf("%w…", inner, …)`; the rest of the message is not modeled. -/
  | wrapped (inner : Option GoError)
deriving Repr, Inhabited

/-- Go's `error`; `none` is `nil`. -/
abbrev error := Option GoError

/-- `fmt.Errorf` whose format starts with `%w` and whose first argument is
`inner`. -/
def errorf (inner : error) : error := some (.wrapped inner)

/-- Go's `context.Context`. -/
structure Context where
deriving Inhabited

end tolean.Go
