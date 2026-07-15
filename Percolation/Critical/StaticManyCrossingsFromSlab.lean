import Percolation.Critical.StaticManyCrossings
import Percolation.Critical.StaticRenormalizationFromSlab

/-!
# Many disjoint crossings from a supercritical finite slab

This file discharges the LSS marginal hypothesis in the aligned form of Theorem 7.68.  The sole
remaining percolation input is the strict finite-quarter-slab comparison supplied by Theorem 7.2.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval

/-- A fixed site density strictly between the concrete Peierls threshold and one. -/
noncomputable def staticCrossingSiteDensity : I :=
  ⟨(siteSquareCrossingPeierlsThreshold + 1) / 2, by
    rcases siteSquareCrossingPeierlsThreshold_mem_Ioo with ⟨hzero, hone⟩
    constructor <;> linarith⟩

theorem siteSquareCrossingPeierlsThreshold_lt_staticCrossingSiteDensity :
    siteSquareCrossingPeierlsThreshold < (staticCrossingSiteDensity : ℝ) := by
  rcases siteSquareCrossingPeierlsThreshold_mem_Ioo with ⟨_hzero, hone⟩
  simp only [staticCrossingSiteDensity]
  linarith

theorem staticCrossingSiteDensity_lt_one :
    (staticCrossingSiteDensity : ℝ) < 1 := by
  rcases siteSquareCrossingPeierlsThreshold_mem_Ioo with ⟨_hzero, hone⟩
  simp only [staticCrossingSiteDensity]
  linarith

/-- Theorem 7.61, in the finite-quarter-slab form currently available, eventually supplies the
one-site marginal required by LSS at the fixed high-density site parameter. -/
theorem exists_staticManyCrossings_goodBlockScale_of_quarterSlabCritical_lt
    {d L : ℕ} (hd : 3 ≤ d) (p : I) (hp1 : (p : ℝ) < 1)
    (hcrit : regionCriticalProbability d (cubicQuarterSlab d L) < (p : ℝ)) :
    ∃ N : ℕ, 1 ≤ N ∧
      (lssMarginalThresholdUnit
          (3 ^ d * (3 * d + 1) ^ d) staticCrossingSiteDensity
            staticCrossingSiteDensity_lt_one : ℝ) ≤
        (epsilonGoodBlockLaw d p (1 / 2 : ℝ) N).real
          {η : Set (Cubic d) | cubicOrigin ∈ η} := by
  let δ : ℝ := lssMarginalThresholdUnit
    (3 ^ d * (3 * d + 1) ^ d) staticCrossingSiteDensity
      staticCrossingSiteDensity_lt_one
  have hδ1 : δ < 1 := by
    exact lssMarginalThreshold_lt_one
      (3 ^ d * (3 * d + 1) ^ d) staticCrossingSiteDensity.2.1
        staticCrossingSiteDensity_lt_one
  have htendsto := epsilonGoodBox_probability_tendsto_one_of_quarterSlabCritical_lt
    hd p hp1 hcrit (epsilon := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  have heventually : ∀ᶠ N : ℕ in Filter.atTop,
      1 ≤ N ∧ δ ≤
        (bernoulliBondMeasure d p).real
          (epsilonGoodBoxEvent d p (1 / 2 : ℝ) cubicOrigin N) := by
    filter_upwards [Filter.eventually_ge_atTop 1,
      htendsto.eventually_const_le hδ1] with N hN hmarginal
    exact ⟨hN, hmarginal⟩
  obtain ⟨N, hN, hmarginal⟩ := heventually.exists
  refine ⟨N, hN, ?_⟩
  rw [epsilonGoodBlockLaw_real_mem]
  have hcenter : epsilonGoodBlockCenter N (cubicOrigin : Cubic d) = cubicOrigin := by
    funext i
    simp [epsilonGoodBlockCenter, cubicScale, cubicOrigin]
  rw [hcenter]
  exact hmarginal

/-- The aligned source-facing conclusion of Theorem 7.68, with the good-block scale chosen
automatically from the finite-quarter-slab comparison. -/
theorem exists_maxEdgeDisjointCrossings_probability_ge_aligned_of_quarterSlabCritical_lt
    {d L : ℕ} (hd : 3 ≤ d) (p₁ p₂ : I)
    (hp₁0 : 0 < (p₁ : ℝ)) (hp₁1 : (p₁ : ℝ) < 1)
    (h12 : (p₁ : ℝ) < p₂)
    (hcrit : regionCriticalProbability d (cubicQuarterSlab d L) < (p₁ : ℝ)) :
    ∃ N : ℕ, 1 ≤ N ∧
      ∀ K : ℕ, staticManyCrossingsBlockThreshold d N p₁ p₂ ≤ K →
        1 - Real.exp (-staticManyCrossingsExponentialRate d N *
            ((N * (K + 1) : ℕ) : ℝ) ^ (d - 1)) ≤
          (bernoulliBondMeasure d p₂).real
            {ω | staticManyCrossingsDensity d N p₁ p₂ *
                ((N * (K + 1) : ℕ) : ℝ) ^ (d - 1) ≤
              (maxEdgeDisjointLeftRightCrossings d (N * (K + 1))
                (Fin.castLE (by omega) 0) ω : ℝ)} := by
  obtain ⟨N, hN, hmarginal⟩ :=
    exists_staticManyCrossings_goodBlockScale_of_quarterSlabCritical_lt
      hd p₁ hp₁1 hcrit
  refine ⟨N, hN, fun K hK ↦ ?_⟩
  exact maxEdgeDisjointCrossings_probability_ge_aligned
    hd p₁ p₂ staticCrossingSiteDensity (1 / 2 : ℝ) N K hN hp₁0 h12 hK
      staticCrossingSiteDensity_lt_one
      siteSquareCrossingPeierlsThreshold_lt_staticCrossingSiteDensity hmarginal

end Percolation
