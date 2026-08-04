import Percolation.TheoremsForExperiment

namespace PercolationReviewCases

open scoped unitInterval

-- Grimmett, Theorem 3.7: the public declaration has the literal source conclusion.
example :
    Percolation.triangularCriticalProbability < Percolation.cubicCriticalProbability 2 := by
  exact Percolation.grimmett_theorem_3_7

-- Grimmett, Theorem 11.70: the public declaration accepts the source equality hypothesis.
example (p : I) (l : Nat) (hl : 1 <= l) (tau : Real)
    (htau : Percolation.rswSquareCrossingProbability p l = tau) :
    Percolation.grimmettRSWLowerBound tau <=
      Percolation.rswAnnulusOpenCircuitProbability p l := by
  exact Percolation.grimmett_theorem_11_70 p l hl tau htau

-- Duminil-Copin, Proposition 2.14: positive integral scales are directly recoverable.
example (n : Nat) (hn : 1 <= n) :
    (1 / 128 : Real) <=
      Percolation.duminilCopinVerticalCrossingProbability Percolation.squareHalfDensity n := by
  exact Percolation.duminilCopin_proposition_2_14 n hn

end PercolationReviewCases
