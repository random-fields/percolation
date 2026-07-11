import Percolation.Critical.TwoPoint

/-! Source-facing application tests for the correlation-length conclusions after Proposition 6.49. -/

namespace Chapter6RepairReview

open Percolation Filter Set
open scoped unitInterval Topology

example (d : ℕ) (hd : 2 ≤ d) :
    ContinuousOn (correlationLength d)
      {p : I | 0 < (p : ℝ) ∧ (p : ℝ) < cubicCriticalProbability d} := by
  exact correlationLength_continuousOn_subcritical d hd

example (d : ℕ) (hd : 2 ≤ d) :
    StrictMonoOn (correlationLength d)
      {p : I | 0 < (p : ℝ) ∧ (p : ℝ) < cubicCriticalProbability d} := by
  exact correlationLength_strictMonoOn_subcritical d hd

example (d : ℕ) (hd : 2 ≤ d) :
    Tendsto (clampedCorrelationLength d) (nhdsWithin 0 (Ioi 0)) (𝓝 0) := by
  exact correlationLength_tendsto_zero_at_zero d (Nat.zero_lt_of_lt hd)

example (d : ℕ) (hd : 2 ≤ d) :
    correlationLength d (cubicCriticalProbabilityUnit d hd) = ⊤ := by
  exact correlationLength_critical_eq_top d hd

end Chapter6RepairReview
