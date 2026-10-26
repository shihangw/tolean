/-!
The model of Go values that code generated from Go imports. Proofs assume
only what this file states, so review it with care.

- `int` and `int64` are `Int`, and every arithmetic result passes through
  `wrap64`, which wraps it into the 64-bit range as Go does.
- `error` is `Option GoError`: `none` is `nil`. tolean models only how an error
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
