import Percolation.Critical.InfiniteClusterUniqueness

/-!
# Supercritical finite-cluster size estimates

This file begins the size-distribution argument in Grimmett Section 8.6 with the exact density
estimate of Lemma 8.68.
-/

namespace Percolation

open MeasureTheory
open scoped unitInterval

theorem infiniteClusterVertexDensity_nonneg (d : ℕ) (s : Finset (Cubic d))
    (omega : EdgeConfiguration d) : 0 ≤ infiniteClusterVertexDensity d s omega := by
  rw [infiniteClusterVertexDensity_eq_card_div]
  positivity

theorem infiniteClusterVertexDensity_le_one (d : ℕ) {s : Finset (Cubic d)}
    (hs : s.Nonempty) (omega : EdgeConfiguration d) :
    infiniteClusterVertexDensity d s omega ≤ 1 := by
  rw [infiniteClusterVertexDensity_eq_card_div, div_le_one]
  · exact_mod_cast Finset.card_le_card fun x hx ↦
      (mem_infiniteClusterVerticesIn.mp hx).1
  · exact_mod_cast Finset.card_pos.mpr hs

theorem integrable_infiniteClusterVertexDensity (d : ℕ) {s : Finset (Cubic d)}
    (hs : s.Nonempty) (p : I) :
    Integrable (infiniteClusterVertexDensity d s) (bernoulliBondMeasure d p) := by
  apply integrable_of_bounded_measurable (measurable_infiniteClusterVertexDensity d s)
  intro omega
  rw [abs_of_nonneg (infiniteClusterVertexDensity_nonneg d s omega)]
  exact infiniteClusterVertexDensity_le_one d hs omega

theorem integral_infiniteClusterVertexDensity (d : ℕ) {s : Finset (Cubic d)}
    (hs : s.Nonempty) (p : I) :
    ∫ omega, infiniteClusterVertexDensity d s omega ∂bernoulliBondMeasure d p = theta d p := by
  have hfun : infiniteClusterVertexDensity d s = fun omega ↦
      (∑ x ∈ s, translatedCylinderIndicator (infiniteClusterVertexEvent d cubicOrigin) x omega) /
        (s.card : ℝ) := by
    funext omega
    exact infiniteClusterVertexDensity_eq_translatedAverage d s omega
  rw [hfun]
  exact (integral_translatedCylinderAverage_of_measurable
    (measurableSet_infiniteClusterVertexEvent d cubicOrigin) p s hs).trans
      (bernoulliBondMeasure_real_infiniteClusterVertexEvent_origin d p)

/-- Grimmett Lemma 8.68: with probability at least `θ(p)/2`, at least half the expected
infinite-cluster density of a finite set is present. -/
theorem infiniteClusterVertexCount_ge_half_probability_ge (d : ℕ) (p : I) (m : ℕ) :
    theta d p / 2 ≤
      (bernoulliBondMeasure d p).real
        {omega | theta d p * ((cubicMetricBox d cubicOrigin m).card : ℝ) / 2 ≤
          ((infiniteClusterVerticesIn d (cubicMetricBox d cubicOrigin m) omega).card : ℝ)} := by
  let s := cubicMetricBox d cubicOrigin m
  let A := denseInfiniteClusterVertexEvent d p (1 / 2 : ℝ) m
  have hs : s.Nonempty :=
    ⟨cubicOrigin, mem_cubicMetricBox_iff_lInfDist_le.mpr (by simp)⟩
  have hAmeas : MeasurableSet A := measurableSet_denseInfiniteClusterVertexEvent d p (1 / 2) m
  have hpoint : ∀ omega, infiniteClusterVertexDensity d s omega ≤
      eventIndicator A omega + theta d p / 2 := by
    intro omega
    by_cases homega : omega ∈ A
    · rw [eventIndicator, Set.indicator_of_mem homega]
      have hle := infiniteClusterVertexDensity_le_one d hs omega
      have htheta : 0 ≤ theta d p := measureReal_nonneg
      linarith
    · rw [eventIndicator, Set.indicator_of_notMem homega]
      have hlt : infiniteClusterVertexDensity d s omega < theta d p / 2 := by
        change ¬(1 - (1 / 2 : ℝ)) * theta d p ≤
          infiniteClusterVertexDensity d s omega at homega
        rw [not_le] at homega
        norm_num at homega
        simpa [div_eq_mul_inv, mul_comm] using homega
      norm_num
      exact hlt.le
  have hmono : theta d p ≤ (bernoulliBondMeasure d p).real A + theta d p / 2 := by
    have hAint : Integrable (eventIndicator A) (bernoulliBondMeasure d p) :=
      (memLp_eventIndicator hAmeas).integrable one_le_two
    have hconst : Integrable (fun _omega : EdgeConfiguration d ↦ theta d p / 2)
        (bernoulliBondMeasure d p) := integrable_const _
    have hsum : Integrable (fun omega : EdgeConfiguration d ↦
        eventIndicator A omega + theta d p / 2) (bernoulliBondMeasure d p) := by
      simpa only [Pi.add_apply] using hAint.add hconst
    calc
      theta d p = ∫ omega, infiniteClusterVertexDensity d s omega
          ∂bernoulliBondMeasure d p := (integral_infiniteClusterVertexDensity d hs p).symm
      _ ≤ ∫ omega, eventIndicator A omega + theta d p / 2
          ∂bernoulliBondMeasure d p := by
        exact integral_mono (integrable_infiniteClusterVertexDensity d hs p)
          hsum hpoint
      _ = (bernoulliBondMeasure d p).real A + theta d p / 2 := by
        rw [integral_add hAint hconst, integral_eventIndicator hAmeas]
        simp
  have hhalf : theta d p / 2 ≤ (bernoulliBondMeasure d p).real A := by linarith
  have hset : {omega | theta d p * ((cubicMetricBox d cubicOrigin m).card : ℝ) / 2 ≤
      ((infiniteClusterVerticesIn d (cubicMetricBox d cubicOrigin m) omega).card : ℝ)} = A := by
    ext omega
    rw [Set.mem_setOf_eq, mem_denseInfiniteClusterVertexEvent_iff_card]
    norm_num
    ring_nf
  rw [hset]
  exact hhalf

end Percolation
