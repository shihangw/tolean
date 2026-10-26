import sensor.Raise

namespace Spec
open sensor.Raise

/-- `raise` never lifts the level above the maximum. -/
def raise_stays_under_max : Prop :=
  ∀ (g : Gauge) (step : Int), g.level ≤ g.max → (raise g step).level ≤ (raise g step).max

end Spec
