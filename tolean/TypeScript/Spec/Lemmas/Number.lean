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

/-- The sign of `1`, as a sort reads the value of a comparator. -/
theorem compareSign_one : compareSign (ofSafeInt (N := N) 1) = some .gt := by
  have h := SafeIntLaws.ofSafeInt (N := N) (i := 1) (by unfold InRange maxSafe; omega)
  have h0 := SafeIntLaws.ofSafeInt (N := N) (i := 0) (by unfold InRange maxSafe; omega)
  simp [compareSign, SafeIntLaws.lt h h0, SafeIntLaws.lt h0 h]

/-- The sign of `0`. -/
theorem compareSign_zero : compareSign (ofSafeInt (N := N) 0) = some .eq := by
  have h0 := SafeIntLaws.ofSafeInt (N := N) (i := 0) (by unfold InRange maxSafe; omega)
  simp [compareSign, SafeIntLaws.lt h0 h0, SafeIntLaws.eq h0 h0]

/-- The sign of `-0`, which a comparator may give in place of `0`. -/
theorem compareSign_neg_zero : compareSign (neg (ofSafeInt (N := N) 0)) = some .eq := by
  have h0 := SafeIntLaws.ofSafeInt (N := N) (i := 0) (by unfold InRange maxSafe; omega)
  have hn := SafeIntLaws.neg h0
  simp only [Int.neg_zero] at hn
  simp [compareSign, SafeIntLaws.lt hn h0, SafeIntLaws.lt h0 hn, SafeIntLaws.eq hn h0]

/-- The sign of `-1`, which the translation writes as the negation of `1`. -/
theorem compareSign_neg_one : compareSign (neg (ofSafeInt (N := N) 1)) = some .lt := by
  have h := SafeIntLaws.ofSafeInt (N := N) (i := 1) (by unfold InRange maxSafe; omega)
  have h0 := SafeIntLaws.ofSafeInt (N := N) (i := 0) (by unfold InRange maxSafe; omega)
  simp [compareSign, SafeIntLaws.lt (SafeIntLaws.neg h) h0]

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
