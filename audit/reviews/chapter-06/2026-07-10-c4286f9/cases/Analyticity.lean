import Percolation.Critical.ClusterAnalyticity

/-! Application, restriction, and endpoint tests for Grimmett, Theorem 6.108. -/

namespace Chapter6FrozenReview

open Percolation Set
open scoped unitInterval

/-- Both physical functions are represented by real-analytic animal series throughout
`[0,p_c)`. -/
example (d : ℕ) (hd : 2 ≤ d) :
    AnalyticOnNhd ℝ (concreteClusterDensitySeries d)
        (Ico (0 : ℝ) (cubicCriticalProbability d)) ∧
      AnalyticOnNhd ℝ (concreteSusceptibilitySeries d)
        (Ico (0 : ℝ) (cubicCriticalProbability d)) := by
  exact clusterDensity_and_susceptibility_analytic_belowCritical d hd

/-- The zero endpoint is supported by an honest complex neighborhood. -/
example (d : ℕ) (hd : 2 ≤ d) :
    AnalyticAt ℂ (complexClusterDensitySeries d) 0 ∧
      AnalyticAt ℂ (complexSusceptibilitySeries d) 0 := by
  exact ⟨complexClusterDensitySeries_analyticAt_zero (Nat.zero_lt_of_lt hd),
    complexSusceptibilitySeries_analyticAt_zero (Nat.zero_lt_of_lt hd)⟩

/-- Restricting the complex density series recovers the already audited real animal series. -/
example (d : ℕ) (hd : 2 ≤ d) (p : ℝ) :
    complexClusterDensitySeries d (p : ℂ) = concreteClusterDensitySeries d p := by
  exact complexClusterDensitySeries_ofReal (Nat.zero_lt_of_lt hd) p

/-- On a physical subcritical density, the susceptibility series has the intended probabilistic
normalization rather than the cluster-density `1/n` normalization. -/
example (d : ℕ) (hd : 2 ≤ d) (p : I)
    (hp : (p : ℝ) < cubicCriticalProbability d) :
    concreteSusceptibilitySeries d p = (susceptibility d p).toReal := by
  exact concreteSusceptibilitySeries_eq_susceptibility_toReal_of_lt_critical d p hp

/-- The density identification is independently inherited from the exact animal decomposition. -/
example (d : ℕ) (hd : 2 ≤ d) (p : I) :
    concreteClusterDensitySeries d p = openClustersPerVertex d p := by
  exact concreteClusterDensitySeries_eq_openClustersPerVertex (Nat.zero_lt_of_lt hd) p

end Chapter6FrozenReview

