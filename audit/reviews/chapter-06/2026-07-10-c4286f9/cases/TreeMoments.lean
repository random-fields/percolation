import Percolation.Critical.ClusterExponential

/-! Source-facing application and small-cardinality tests for (6.93)--(6.97). -/

namespace Chapter6FrozenReview

open Percolation
open scoped ENNReal unitInterval BigOperators

/-- The general tree-graph inequality is usable at arbitrary density and keeps endpoint-safe
`ENNReal` sums. -/
example (d n : ℕ) (p : I) (x : Fin (n + 3) → Cubic d) :
    bernoulliBondMeasure d p (orderedMultiPointConnectionEvent d n x) ≤
      ∑' s : CubicConnectivitySkeleton (n + 3),
        ∑' psi : s.Vertex → Cubic d, skeletonConnectivityWeight p s psi x := by
  exact multiPointConnectivity_le_skeleton_sum d n p x

/-- The source moment exponent and number of skeleton edges remain visible in the public type. -/
example (d k : ℕ) (p : I) :
    clusterSizeMomentENNReal d p (k + 2) ≤
      (connectivitySkeletonCount (k + 3) : ℝ≥0∞) *
        susceptibility d p ^ (2 * k + 3) := by
  exact clusterSizeMoment_le d k p

/-- Equation (6.97) now has the literal random-variable expectation on the left. -/
example (d : ℕ) (p : I) (t : ℝ≥0∞)
    (ht : 2 * (t * susceptibility d p ^ 2) < 1) :
    clusterSizeExponentialMoment d p t ≤
      susceptibility d p * ENNReal.ofReal
        (1 / (1 - 2 * (t * susceptibility d p ^ 2).toReal) ^ (1 / 2 : ℝ)) := by
  exact clusterSizeExponentialMoment_le d p t ht

/-- The canonical counting code and concrete decoder have the same source cardinality. -/
example : connectivitySkeletonCount 5 = Fintype.card (CubicConnectivitySkeleton 5) := by
  exact (cubicConnectivitySkeleton_card_eq 5 (by omega)).symm

/-- Independent finite computations cross-check the concrete recursive decoder. -/
example : Fintype.card (CubicConnectivitySkeleton 3) = 1 := by decide
example : Fintype.card (CubicConnectivitySkeleton 4) = 3 := by decide
example : Fintype.card (CubicConnectivitySkeleton 5) = 15 := by decide

end Chapter6FrozenReview
