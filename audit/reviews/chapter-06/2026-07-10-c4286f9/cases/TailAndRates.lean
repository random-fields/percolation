import Percolation.Critical.ClusterSizeRate

/-! Application and endpoint tests for Theorems 6.75, 6.78 and Lemma 6.102. -/

namespace Chapter6FrozenReview

open Percolation Filter
open scoped unitInterval

/-- Corrected source-facing exponential decay is eventual; the theorem exposes its threshold. -/
example (d : ℕ) (hd : 2 ≤ d) (p : I) (hp0 : 0 < (p : ℝ))
    (hp : (p : ℝ) < cubicCriticalProbability d) :
    ∃ lambda : ℝ, 0 < lambda ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      clusterSizeAtLeast d p n ≤ Real.exp (-lambda * n) := by
  exact clusterSizeAtLeast_exponential_decay_of_lt_critical d hd p hp0 hp

/-- The exact (6.77) bound is available once the printed source threshold is supplied. -/
example (d : ℕ) (hd : 0 < d) (p : I) (hp : 0 < (p : ℝ))
    (hchi : susceptibility d p < ⊤) (n : ℕ)
    (hn : (susceptibility d p).toReal ^ 2 < n) :
    clusterSizeAtLeast d p n ≤
      2 * Real.exp (-(1 / 2 : ℝ) * n / (susceptibility d p).toReal ^ 2) := by
  exact clusterSizeAtLeast_le_two_exp_neg hd hp hchi n hn

/-- Lemma 6.102 retains both positive-size premises and the exact joining-edge factor. -/
example (d m n : ℕ) (p : I) (hd : 0 < d) (hm : 0 < m) (hn : 0 < n)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    (p : ℝ) * (1 - (p : ℝ))⁻¹ ^ 2 *
        (finiteClusterSizeProbability d p m / m) *
        (finiteClusterSizeProbability d p n / n) ≤
      finiteClusterSizeProbability d p (m + n) / (m + n) := by
  exact CubicBondAnimal.finiteClusterSizeProbability_normalized_supermultiplicative
    d m n p hd hm hn hp0 hp1

/-- The exact-size rate limit has no hidden subcritical premise. -/
example (d : ℕ) (p : I) (hd : 0 < d) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    Tendsto (fun n : ℕ => -Real.log (finiteClusterSizeProbability d p n) / n)
      atTop (nhds (clusterSizeDecayRate d p)) := by
  exact clusterSizeProbability_logRate_tendsto d p hd hp0 hp1

/-- Below criticality the rate is positive and no larger than the box-radius rate. -/
example (d : ℕ) (hd : 2 ≤ d) (p : I) (hp0 : 0 < (p : ℝ))
    (hp : (p : ℝ) < cubicCriticalProbability d) :
    0 < clusterSizeDecayRate d p ∧
      clusterSizeDecayRate d p ≤ boxRadiusDecayRate d p := by
  exact ⟨clusterSizeDecayRate_pos_of_lt_critical d hd p hp0 hp,
    clusterSizeDecayRate_le_boxRadiusDecayRate d hd p hp0 hp⟩

end Chapter6FrozenReview

