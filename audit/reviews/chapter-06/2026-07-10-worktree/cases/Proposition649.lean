import Percolation.Critical.TwoPoint

/-! Application, endpoint, and refutation tests for Grimmett, Proposition 6.49. -/

namespace Chapter6Review

open Percolation Filter Set Topology
open scoped ENNReal unitInterval

/-- The exact geometric two-point bound only assumes positive density and finite susceptibility. -/
example (d : ℕ) (hd : 2 ≤ d) (p : I) (hp : 0 < (p : ℝ))
    (hchi : susceptibility d p < ⊤) (x : Cubic d) :
    twoPointConnectivity d p cubicOrigin x ≤
      (1 - ((susceptibility d p).toReal)⁻¹) ^ cubicL1Dist cubicOrigin x := by
  exact twoPointConnectivity_le_one_sub_susceptibility_inv_pow (by omega) hp hchi x

/-- The ENNReal codomain gives the mathematically correct critical endpoint. -/
example (d : ℕ) (hd : 2 ≤ d) :
    correlationLength d (cubicCriticalProbabilityUnit d hd) = ⊤ := by
  exact correlationLength_critical_eq_top d hd

/-- Below criticality the comparison has no hidden finiteness or coercion premise. -/
example (d : ℕ) (hd : 2 ≤ d) (p : I) (hp : 0 < (p : ℝ))
    (hpc : (p : ℝ) < cubicCriticalProbability d) :
    correlationLength d p ≤ susceptibility d p := by
  exact correlationLength_le_susceptibility hd hp hpc

/-- The final critical-divergence consequence is a one-sided statement in the unit interval. -/
example (d : ℕ) (hd : 2 ≤ d) :
    Tendsto (susceptibility d)
      (𝓝[<] (cubicCriticalProbabilityUnit d hd)) (𝓝 ⊤) := by
  exact susceptibility_tendsto_top_at_critical d hd

/-- A finite critical correlation length would contradict the endpoint theorem. -/
example (d : ℕ) (hd : 2 ≤ d) :
    ¬ correlationLength d (cubicCriticalProbabilityUnit d hd) < ⊤ := by
  simp

end Chapter6Review
