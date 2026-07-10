import Percolation.Critical.BoxRadiusProperties

/-! Application and adversarial endpoint tests for Grimmett, Theorem 6.14. -/

namespace Chapter6Review

open Percolation Filter Set Topology
open scoped unitInterval

/-- The continuity statement includes the one-sided topology at density one. -/
example (d : ℕ) (hd : 2 ≤ d) :
    ContinuousOn (boxRadiusDecayRate d) {p : I | 0 < (p : ℝ)} := by
  exact boxRadiusDecayRate_continuousOn d (by omega)

/-- The rate diverges, rather than taking a totalized real value, at the zero-density endpoint. -/
example (d : ℕ) (hd : 2 ≤ d) :
    Tendsto (clampedBoxRadiusDecayRate d) (𝓝[>] (0 : ℝ)) atTop := by
  exact boxRadiusDecayRate_tendsto_top_at_zero d (by omega)

/-- The critical value is zero without assuming critical percolation is absent. -/
example (d : ℕ) (hd : 2 ≤ d) :
    boxRadiusDecayRate d (cubicCriticalProbabilityUnit d hd) = 0 := by
  exact boxRadiusDecayRate_critical_eq_zero d hd

/-- At density one the rate is zero; this catches accidental use of the logarithmic ratio
formula (6.40), whose denominator vanishes at this endpoint. -/
example (d : ℕ) (hd : 2 ≤ d) :
    boxRadiusDecayRate d (1 : I) = 0 := by
  apply boxRadiusDecayRate_eq_zero_of_critical_lt d (by omega)
  simpa using (cubicCriticalProbability_pos_lt_one hd).2

/-- A reversed subcritical monotonicity inequality contradicts the proved strict decrease. -/
example (d : ℕ) (hd : 2 ≤ d) {a b : I}
    (ha : 0 < (a : ℝ) ∧ (a : ℝ) < cubicCriticalProbability d)
    (hb : 0 < (b : ℝ) ∧ (b : ℝ) < cubicCriticalProbability d)
    (hab : a < b) :
    ¬ boxRadiusDecayRate d a ≤ boxRadiusDecayRate d b := by
  exact not_le_of_gt (boxRadiusDecayRate_strictAntiOn_subcritical d hd ha hb hab)

end Chapter6Review
