import tolean.Audit
import sensor.RaiseSpec

namespace Proof
open sensor.Raise

theorem raise_stays_under_max : Spec.raise_stays_under_max := by
  intro g step h
  unfold raise
  split
  · exact Int.le_refl _
  · show g.level + step ≤ g.max; omega

end Proof

#audit_claims Spec Proof
