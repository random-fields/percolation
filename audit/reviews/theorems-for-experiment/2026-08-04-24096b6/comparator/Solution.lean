import Percolation.TheoremsForExperiment

namespace Review.TheoremsForExperiment

open Percolation
open scoped unitInterval

theorem grimmett_theorem_3_7 :
    triangularCriticalProbability < cubicCriticalProbability 2 :=
  Percolation.grimmett_theorem_3_7

theorem grimmett_theorem_11_70 (p : I) (l : ℕ) (hl : 1 ≤ l) (tau : ℝ)
    (htau : rswSquareCrossingProbability p l = tau) :
    grimmettRSWLowerBound tau ≤ rswAnnulusOpenCircuitProbability p l :=
  Percolation.grimmett_theorem_11_70 p l hl tau htau

theorem duminilCopin_proposition_2_14 (n : ℕ) (hn : 1 ≤ n) :
    (1 / 128 : ℝ) ≤ duminilCopinVerticalCrossingProbability squareHalfDensity n :=
  Percolation.duminilCopin_proposition_2_14 n hn

end Review.TheoremsForExperiment
