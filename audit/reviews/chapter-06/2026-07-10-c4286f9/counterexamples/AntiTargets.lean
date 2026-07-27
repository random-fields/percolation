import Percolation.Critical.ClusterAnalyticity

/-! Compiling refutations of tempting but false strengthenings. -/

namespace Chapter6FrozenReview

open Percolation Set
open scoped ENNReal unitInterval

/-- A strict exponential upper bound at cluster size one is impossible: the origin cluster
always has at least one vertex. -/
example (d : ℕ) (p : I) : clusterSizeAtLeast d p 1 = 1 := by
  unfold clusterSizeAtLeast
  rw [show clusterSizeAtLeastEvent d 1 = Set.univ by
    ext omega
    simp only [clusterSizeAtLeastEvent, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    rw [clusterSizeENNReal_eq_encard]
    have hmem : cubicOrigin ∈ cubicOpenCluster d omega := by
      exact ⟨SimpleGraph.Walk.nil, by intro e he; simp at he⟩
    have hcard : (1 : ℕ∞) ≤ (cubicOpenCluster d omega).encard :=
      Set.one_le_encard_iff_nonempty.mpr ⟨cubicOrigin, hmem⟩
    exact_mod_cast hcard]
  exact MeasureTheory.probReal_univ

example (d : ℕ) (p : I) :
    ¬ ∃ lambda : ℝ, 0 < lambda ∧
      clusterSizeAtLeast d p 1 ≤ Real.exp (-lambda * (1 : ℕ)) := by
  intro h
  obtain ⟨lambda, hlambda, hle⟩ := h
  have hone : clusterSizeAtLeast d p 1 = 1 := by
    unfold clusterSizeAtLeast
    rw [show clusterSizeAtLeastEvent d 1 = Set.univ by
      ext omega
      simp only [clusterSizeAtLeastEvent, Set.mem_setOf_eq, Set.mem_univ, iff_true]
      rw [clusterSizeENNReal_eq_encard]
      have hmem : cubicOrigin ∈ cubicOpenCluster d omega := by
        exact ⟨SimpleGraph.Walk.nil, by intro e he; simp at he⟩
      have hcard : (1 : ℕ∞) ≤ (cubicOpenCluster d omega).encard :=
        Set.one_le_encard_iff_nonempty.mpr ⟨cubicOrigin, hmem⟩
      exact_mod_cast hcard]
    exact MeasureTheory.probReal_univ
  rw [hone] at hle
  have hexp : Real.exp (-lambda) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  norm_num only [Nat.cast_one, mul_one] at hle
  exact (not_lt_of_ge hle) hexp

/-- The printed lower expression in Proposition 6.47 cannot be totalized at the origin without
changing its meaning: its positive-dimensional polynomial denominator is zero. -/
example (d : ℕ) (hd : 2 ≤ d) :
    (cubicL1Dist cubicOrigin (cubicOrigin : Cubic d) : ℝ) ^ (4 * d * (d - 1)) = 0 := by
  rw [cubicL1Dist_self]
  have hd0 : d ≠ 0 := by omega
  have hdsub : d - 1 ≠ 0 := by omega
  have hexp : 4 * d * (d - 1) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hd0) hdsub
  norm_num [hexp]

/-- `AnalyticOnNhd` at zero is stronger than one-sided physical differentiability and therefore
guards against silently replacing Theorem 6.108 by a merely `C^1` endpoint result. -/
example (d : ℕ) (hd : 2 ≤ d) :
    AnalyticAt ℝ (concreteSusceptibilitySeries d) 0 := by
  exact concreteSusceptibilitySeries_analyticOnNhd_belowCritical d hd 0
    ⟨le_rfl, cubicCriticalProbability_pos_lt_one hd |>.1⟩

end Chapter6FrozenReview
