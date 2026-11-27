/-!
The exception piece of the shared core. Go's interpreter is its first user.

A run of an interpreter can end in three ways. It gives a value. It fails with
an error that the program raises, such as a Go panic or a TypeScript `throw`.
Or it gets stuck, because the program leaves the subset or the fuel runs out.
`Res ε α` holds the three: `none` is stuck, `some (.error e)` failed with `e`,
and `some (.ok a)` gave `a`.

`Res.andThen` runs one step after another. A stuck step or an error ends the
run, as `>>=` of `ExceptT ε Option` does. The Go interpreter uses `andThen` rather than `do`
notation over `ExceptT`, so that a proof can rewrite each step with the
`simp` lemmas below.
-/
namespace tolean.Core

/-- A run that is stuck (`none`), fails with an error, or gives a value. -/
abbrev Res (ε α : Type) := Option (Except ε α)

namespace Res

variable {ε α β : Type}

/-- The run gives `a`. -/
@[reducible] def ok (a : α) : Res ε α := some (.ok a)

/-- The run fails with `e`. -/
@[reducible] def fail (e : ε) : Res ε α := some (.error e)

/-- A step that cannot fail, only get stuck. -/
def lift : Option α → Res ε α
  | none => none
  | some a => some (.ok a)

/-- Run `x`, then `f` on its value. A stuck `x` gets stuck, and an `x` that
fails fails with the same error. -/
def andThen (x : Res ε α) (f : α → Res ε β) : Res ε β :=
  match x with
  | none => none
  | some (.error e) => some (.error e)
  | some (.ok a) => f a

@[simp] theorem andThen_ok (a : α) (f : α → Res ε β) : andThen (some (.ok a)) f = f a := rfl

@[simp] theorem andThen_error (e : ε) (f : α → Res ε β) :
    andThen (some (.error e)) f = some (.error e) := rfl

@[simp] theorem andThen_none (f : α → Res ε β) : andThen none f = none := rfl

@[simp] theorem lift_some (a : α) : (lift (some a) : Res ε α) = some (.ok a) := rfl

@[simp] theorem lift_none : (lift none : Res ε α) = none := rfl

theorem andThen_eq_ok {x : Res ε α} {f : α → Res ε β} {b : β} :
    andThen x f = some (.ok b) ↔ ∃ a, x = some (.ok a) ∧ f a = some (.ok b) := by
  rcases x with _ | _ | a <;> simp [andThen]

theorem andThen_eq_error {x : Res ε α} {f : α → Res ε β} {e : ε} :
    andThen x f = some (.error e) ↔
      x = some (.error e) ∨ ∃ a, x = some (.ok a) ∧ f a = some (.error e) := by
  rcases x with _ | _ | a <;> simp [andThen]

theorem lift_eq_ok {x : Option α} {a : α} : (lift x : Res ε α) = some (.ok a) ↔ x = some a := by
  cases x <;> simp [lift]

end Res

end tolean.Core
