import Percolation.TheoremsForExperiment

namespace Review.TheoremsForExperiment

open Percolation
open scoped unitInterval

/-- Grimmett, Theorem 3.7. -/
theorem grimmett_theorem_3_7 :
    triangularCriticalProbability < cubicCriticalProbability 2 := by
  sorry

/-- Grimmett, Theorem 11.70 and equation 11.71. -/
theorem grimmett_theorem_11_70 (p : I) (l : ℕ) (hl : 1 ≤ l) (tau : ℝ)
    (htau : rswSquareCrossingProbability p l = tau) :
    grimmettRSWLowerBound tau ≤ rswAnnulusOpenCircuitProbability p l := by
  sorry

/-- Duminil-Copin, Proposition 2.14. -/
theorem duminilCopin_proposition_2_14 (n : ℕ) (hn : 1 ≤ n) :
    (1 / 128 : ℝ) ≤ duminilCopinVerticalCrossingProbability squareHalfDensity n := by
  sorry

end Review.TheoremsForExperiment
