import Percolation.Critical.FiniteSlabTLowerBound
import Percolation.Critical.StaticAnnularPeeling
import Percolation.Critical.StaticSecondCluster
import Percolation.Critical.StaticLogInset

/-!
# Static renormalization from a supercritical quarter slab

This file composes the concrete finite-volume proof of Lemma 7.78 with the already formalized
peeling and density arguments.  The remaining upstream input is exactly the strict quarter-slab
critical comparison supplied by Grimmett--Marstrand Theorem 7.2.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval

theorem cubicCriticalProbability_le_regionCriticalProbability
    (d : ℕ) (A : Set (Cubic d)) :
    cubicCriticalProbability d ≤ regionCriticalProbability d A := by
  rw [← regionCriticalProbability_univ d]
  exact regionCriticalProbability_anti (Set.subset_univ A)

theorem exists_twoArmSeparation_probability_le_exp_of_quarterSlabCritical_lt
    {d L : ℕ} (hd : 3 ≤ d) (p : I) (hp1 : (p : ℝ) < 1)
    (hcrit : regionCriticalProbability d (cubicQuarterSlab d L) < (p : ℝ)) :
    ∃ xi : ℝ, 0 < xi ∧ ∀ n N : ℕ, n < N → ∀ x y : Cubic d,
      (bernoulliBondMeasure d p).real (twoArmSeparationEvent d n N x y) ≤
        Real.exp (-xi * ((N - n : ℕ) : ℝ)) := by
  obtain ⟨delta, hdelta0, hdelta1, hslab⟩ :=
    exists_unit_uniformFiniteSlabConnectionLowerBound_of_critical_lt d hd L p hcrit
  have hp0 : 0 < (p : ℝ) :=
    (regionCriticalProbability_nonneg d (cubicQuarterSlab d L)).trans_lt hcrit
  exact exists_twoArmSeparation_probability_le_exp_of_uniformFiniteSlab
    (by omega) p hp0 hp1 hdelta0 hdelta1 hslab

theorem exists_secondMacroscopicCluster_probability_le_exp_of_quarterSlabCritical_lt
    {d L : ℕ} (hd : 3 ≤ d) (p : I)
    (hcrit : regionCriticalProbability d (cubicQuarterSlab d L) < (p : ℝ)) :
    ∃ mu : ℝ, 0 < mu ∧ ∀ m n : ℕ, 1 ≤ m → 1 ≤ n →
      (bernoulliBondMeasure d p).real
          (secondMacroscopicClusterEvent d m n cubicOrigin) ≤
        d * (2 * n + 1 : ℝ) ^ (2 * d) * Real.exp (-mu * m) := by
  obtain ⟨delta, hdelta0, hdelta1, hslab⟩ :=
    exists_unit_uniformFiniteSlabConnectionLowerBound_of_critical_lt d hd L p hcrit
  have hp0 : 0 < (p : ℝ) :=
    (regionCriticalProbability_nonneg d (cubicQuarterSlab d L)).trans_lt hcrit
  exact exists_secondMacroscopicCluster_probability_le_exp_of_uniformFiniteSlab
    (by omega) p hp0 hdelta0 hdelta1 hslab

theorem epsilonDenseCrossingCluster_probability_tendsto_one_of_quarterSlabCritical_lt
    {d L : ℕ} (hd : 3 ≤ d) (p : I) (hp1 : (p : ℝ) < 1)
    (hcrit : regionCriticalProbability d (cubicQuarterSlab d L) < (p : ℝ))
    {epsilon : ℝ} (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon < 1) :
    Filter.Tendsto
      (fun n ↦ (bernoulliBondMeasure d p).real
        (epsilonDenseCrossingClusterEvent d p epsilon n cubicOrigin))
      Filter.atTop (nhds 1) := by
  obtain ⟨delta, hdelta0, hdelta1, hslab⟩ :=
    exists_unit_uniformFiniteSlabConnectionLowerBound_of_critical_lt d hd L p hcrit
  have hp0 : 0 < (p : ℝ) :=
    (regionCriticalProbability_nonneg d (cubicQuarterSlab d L)).trans_lt hcrit
  have hpc : cubicCriticalProbability d < (p : ℝ) :=
    (cubicCriticalProbability_le_regionCriticalProbability d
      (cubicQuarterSlab d L)).trans_lt hcrit
  exact epsilonDenseCrossingCluster_probability_tendsto_one_of_uniformFiniteSlab
    (by omega) p hp0 hp1 (theta_pos_of_criticalProbability_lt hpc)
      hdelta0 hdelta1 hslab hepsilon0 hepsilon1

theorem epsilonGoodBox_probability_tendsto_one_of_quarterSlabCritical_lt
    {d L : ℕ} (hd : 3 ≤ d) (p : I) (hp1 : (p : ℝ) < 1)
    (hcrit : regionCriticalProbability d (cubicQuarterSlab d L) < (p : ℝ))
    {epsilon : ℝ} (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon < 1) :
    Filter.Tendsto
      (fun n ↦ (bernoulliBondMeasure d p).real
        (epsilonGoodBoxEvent d p epsilon cubicOrigin n))
      Filter.atTop (nhds 1) := by
  obtain ⟨delta, hdelta0, hdelta1, hslab⟩ :=
    exists_unit_uniformFiniteSlabConnectionLowerBound_of_critical_lt d hd L p hcrit
  have hp0 : 0 < (p : ℝ) :=
    (regionCriticalProbability_nonneg d (cubicQuarterSlab d L)).trans_lt hcrit
  have hpc : cubicCriticalProbability d < (p : ℝ) :=
    (cubicCriticalProbability_le_regionCriticalProbability d
      (cubicQuarterSlab d L)).trans_lt hcrit
  exact epsilonGoodBox_probability_tendsto_one_of_uniformFiniteSlab
    (by omega) p hp0 hp1 (theta_pos_of_criticalProbability_lt hpc)
      hdelta0 hdelta1 hslab hepsilon0 hepsilon1

end Percolation
