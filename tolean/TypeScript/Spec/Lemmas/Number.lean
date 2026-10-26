/-
Facts about JS numbers proved from the laws in `tolean.TypeScript.Spec.Number`.

They assume nothing beyond those laws, so they need no audit. Any project that
requires `tolean` can import them, and `simp` uses the ones marked `@[simp]`.
-/
import tolean.TypeScript.Spec.Number

namespace tolean.TypeScript
open JSNumber

variable {N : Type} [JSNumber N]

section SafeIntegers
variable [SafeIntLaws N]

/-- A safe integer is `===` to itself. -/
@[simp] theorem eq_refl_of_safe {a : N} {i : Int} (h : toSafeInt a = some i) :
    eq a a = true := by
  simp [SafeIntLaws.eq h h]

/-- A safe integer is `<=` itself. -/
@[simp] theorem le_refl_of_safe {a : N} {i : Int} (h : toSafeInt a = some i) :
    le a a = true := by
  simp [SafeIntLaws.le h h]

/-- No safe integer is `<` itself. -/
@[simp] theorem lt_irrefl_of_safe {a : N} {i : Int} (h : toSafeInt a = some i) :
    lt a a = false := by
  simp [SafeIntLaws.lt h h]

end SafeIntegers

section SpecialValues
variable [SpecialValueLaws N]

/-- `x === x` exactly when `x` is not `NaN`, so `x !== x` is a NaN test. -/
theorem eq_self_eq_not_isNaN {a : N} : eq a a = !isNaN a := by
  cases h : isNaN a
  · simp [SpecialValueLaws.eq_refl h]
  · simp [SpecialValueLaws.nan_eq h]

/-- `Infinity === Infinity`. -/
@[simp] theorem eq_posInf_posInf : eq (posInf (N := N)) posInf = true :=
  SpecialValueLaws.eq_refl SpecialValueLaws.isNaN_posInf

/-- `-Infinity === -Infinity`. -/
@[simp] theorem eq_negInf_negInf : eq (negInf (N := N)) negInf = true :=
  SpecialValueLaws.eq_refl SpecialValueLaws.isNaN_negInf

/-- A safe integer is not `NaN`. -/
@[simp] theorem isNaN_eq_false_of_safe {a : N} {i : Int} (h : toSafeInt a = some i) :
    isNaN a = false :=
  SpecialValueLaws.isFinite_not_nan (SpecialValueLaws.safe_finite h)

end SpecialValues

end tolean.TypeScript
