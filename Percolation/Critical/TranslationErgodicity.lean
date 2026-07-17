import Percolation.Critical.InfiniteClusterDensity

/-!
# Ergodicity of cubic translations

This file derives the zero--one law for measurable events invariant under every lattice
translation.  The proof uses the finite-cylinder approximation and finite-range covariance
estimates already developed for box-density laws; it does not assume an abstract ergodic
theorem.
-/

namespace Percolation

open Filter MeasureTheory ProbabilityTheory
open scoped symmDiff unitInterval

/-- A bond event is invariant under every translation from the origin. -/
def IsInvariantUnderCubicTranslations {d : ℕ}
    (A : Set (EdgeConfiguration d)) : Prop :=
  ∀ x : Cubic d, translatedCylinderEvent x A = A

/-- A weak law for the spatial average of translates of an arbitrary measurable bond event.
This is the generic form of the finite-cylinder argument used for infinite-cluster density. -/
theorem translatedEventAverage_measureReal_tendsto_zero
    {d : ℕ} (hd : 1 ≤ d) (p : I) {A : Set (EdgeConfiguration d)}
    (hA : MeasurableSet A) {ε : ℝ} (hε : 0 < ε) :
    Tendsto
      (fun n ↦ (bernoulliBondMeasure d p).real
        {ω | ε ≤
          |(∑ x ∈ cubicMetricBox d cubicOrigin n,
              translatedCylinderIndicator A x ω) /
                ((cubicMetricBox d cubicOrigin n).card : ℝ) -
            (bernoulliBondMeasure d p).real A|})
      atTop (nhds 0) := by
  apply Metric.tendsto_atTop.2
  intro η hη
  let μ := bernoulliBondMeasure d p
  have htolerance : 0 < min (ε / 4) (η * ε / 8) := by positivity
  obtain ⟨E, C, hC, happrox⟩ :=
    exists_dependsOn_measureReal_symmDiff_lt μ hA htolerance
  have happroxε : μ.real (A ∆ C) < ε / 4 :=
    happrox.trans_le (min_le_left _ _)
  have happroxη : μ.real (A ∆ C) < η * ε / 8 :=
    happrox.trans_le (min_le_right _ _)
  let D : ℝ := (((2 * (2 * cubicEdgeSetRadius E) + 1) ^ d : ℕ) : ℝ)
  have hden : Tendsto
      (fun n : ℕ ↦ ((cubicMetricBox d cubicOrigin n).card : ℝ)) atTop atTop := by
    apply Filter.tendsto_atTop_mono
      (f := fun n : ℕ ↦ (n : ℝ))
      (g := fun n : ℕ ↦ ((cubicMetricBox d cubicOrigin n).card : ℝ))
    · intro n
      rw [cubicMetricBox_card]
      exact_mod_cast (show n ≤ (2 * n + 1) ^ d from
        (show n ≤ 2 * n + 1 by omega).trans
          (le_self_pow (show 1 ≤ 2 * n + 1 by omega)
            (Nat.ne_of_gt (Nat.zero_lt_one.trans_le hd))))
    · exact tendsto_natCast_atTop_atTop
  have hvariance : Tendsto
      (fun n : ℕ ↦
        (D / ((cubicMetricBox d cubicOrigin n).card : ℝ)) / (ε / 2) ^ 2)
      atTop (nhds 0) := by
    simpa using (hden.const_div_atTop D).div_const ((ε / 2) ^ 2)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hvariance (η / 2) (by positivity)
  refine ⟨N, fun n hn ↦ ?_⟩
  have hs : (cubicMetricBox d cubicOrigin n).Nonempty := by
    exact ⟨cubicOrigin, mem_cubicMetricBox_iff_lInfDist_le.mpr (by simp)⟩
  let a : EdgeConfiguration d → ℝ := fun ω ↦
    (∑ x ∈ cubicMetricBox d cubicOrigin n,
      translatedCylinderIndicator A x ω) /
        ((cubicMetricBox d cubicOrigin n).card : ℝ)
  let c : EdgeConfiguration d → ℝ := fun ω ↦
    (∑ x ∈ cubicMetricBox d cubicOrigin n,
      translatedCylinderIndicator C x ω) /
        ((cubicMetricBox d cubicOrigin n).card : ℝ)
  let m : EdgeConfiguration d → ℝ := fun ω ↦
    (∑ x ∈ cubicMetricBox d cubicOrigin n,
      |translatedCylinderIndicator A x ω - translatedCylinderIndicator C x ω|) /
        ((cubicMetricBox d cubicOrigin n).card : ℝ)
  have hcenter : |μ.real C - μ.real A| ≤ μ.real (A ∆ C) := by
    simpa [abs_sub_comm, symmDiff_comm] using
      (abs_measureReal_sub_le_measureReal_symmDiff (μ := μ)
        hC.measurableSet.nullMeasurableSet hA.nullMeasurableSet)
  have hsubset :
      {ω | ε ≤ |a ω - μ.real A|} ⊆
        {ω | ε / 4 ≤ m ω} ∪ {ω | ε / 2 ≤ |c ω - μ.real C|} := by
    intro ω hω
    by_contra hnot
    rw [Set.mem_union, not_or] at hnot
    have hm : m ω < ε / 4 := not_le.mp hnot.1
    have hc : |c ω - μ.real C| < ε / 2 := not_le.mp hnot.2
    have hac : |a ω - c ω| ≤ m ω := by
      exact abs_finset_average_sub_average_le_average_abs_sub hs
        (fun x ↦ translatedCylinderIndicator A x ω)
        (fun x ↦ translatedCylinderIndicator C x ω)
    have hca : |μ.real C - μ.real A| < ε / 4 :=
      hcenter.trans_lt happroxε
    have htri : |a ω - μ.real A| ≤
        |a ω - c ω| + |c ω - μ.real C| + |μ.real C - μ.real A| := by
      calc
        |a ω - μ.real A| ≤ |a ω - c ω| + |c ω - μ.real A| :=
          abs_sub_le (a ω) (c ω) (μ.real A)
        _ ≤ |a ω - c ω| +
            (|c ω - μ.real C| + |μ.real C - μ.real A|) :=
          add_le_add le_rfl (abs_sub_le (c ω) (μ.real C) (μ.real A))
        _ = |a ω - c ω| + |c ω - μ.real C| +
            |μ.real C - μ.real A| := by ring
    exact (not_lt_of_ge hω) (lt_of_le_of_lt htri (by linarith))
  have hbound :
      μ.real {ω | ε ≤ |a ω - μ.real A|} ≤
        μ.real (A ∆ C) / (ε / 4) +
          (D / ((cubicMetricBox d cubicOrigin n).card : ℝ)) / (ε / 2) ^ 2 := by
    calc
      μ.real {ω | ε ≤ |a ω - μ.real A|} ≤
          μ.real ({ω | ε / 4 ≤ m ω} ∪
            {ω | ε / 2 ≤ |c ω - μ.real C|}) := measureReal_mono hsubset
      _ ≤ μ.real {ω | ε / 4 ≤ m ω} +
          μ.real {ω | ε / 2 ≤ |c ω - μ.real C|} := measureReal_union_le _ _
      _ ≤ μ.real (A ∆ C) / (ε / 4) +
          (D / ((cubicMetricBox d cubicOrigin n).card : ℝ)) / (ε / 2) ^ 2 := by
        apply add_le_add
        · exact bernoulliBondMeasure_real_translatedIndicator_discrepancy_le
            hA hC.measurableSet p _ hs (by positivity)
        · simpa [D] using
            bernoulliBondMeasure_real_translatedCylinderAverage_deviation_le
              hC p _ hs (by positivity : 0 < ε / 2)
  have hfirst : μ.real (A ∆ C) / (ε / 4) < η / 2 := by
    apply (div_lt_iff₀ (by positivity : 0 < ε / 4)).2
    nlinarith
  have hsecond :
      (D / ((cubicMetricBox d cubicOrigin n).card : ℝ)) / (ε / 2) ^ 2 < η / 2 := by
    have hnonneg : 0 ≤
        (D / ((cubicMetricBox d cubicOrigin n).card : ℝ)) / (ε / 2) ^ 2 := by
      dsimp [D]
      positivity
    have hn' := hN n hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg] at hn'
    exact hn'
  rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg]
  change μ.real {ω | ε ≤ |a ω - μ.real A|} < η
  exact hbound.trans_lt (by linarith)

/-- Bernoulli bond measure is ergodic under the full group of cubic translations. -/
theorem bernoulliBondMeasure_real_eq_zero_or_one_of_translationInvariant
    {d : ℕ} (hd : 1 ≤ d) (p : I) {A : Set (EdgeConfiguration d)}
    (hA : MeasurableSet A) (hinv : IsInvariantUnderCubicTranslations A) :
    (bernoulliBondMeasure d p).real A = 0 ∨
      (bernoulliBondMeasure d p).real A = 1 := by
  let q := (bernoulliBondMeasure d p).real A
  have hq0 : 0 ≤ q := measureReal_nonneg
  have hq1 : q ≤ 1 := measureReal_le_one
  by_cases hqz : q = 0
  · exact Or.inl hqz
  right
  by_contra hqone
  have hqpos : 0 < q := lt_of_le_of_ne hq0 (Ne.symm hqz)
  have hqlt : q < 1 := lt_of_le_of_ne hq1 hqone
  let ε : ℝ := q * (1 - q) / 2
  have hε : 0 < ε := by dsimp [ε]; positivity
  have ht := translatedEventAverage_measureReal_tendsto_zero hd p hA hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 ht (1 / 2) (by norm_num)
  have hdev (n : ℕ) :
      {ω | ε ≤
        |(∑ x ∈ cubicMetricBox d cubicOrigin n,
            translatedCylinderIndicator A x ω) /
              ((cubicMetricBox d cubicOrigin n).card : ℝ) - q|} = Set.univ := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    have hs : (cubicMetricBox d cubicOrigin n).Nonempty :=
      ⟨cubicOrigin, mem_cubicMetricBox_iff_lInfDist_le.mpr (by simp)⟩
    have hsum :
        (∑ x ∈ cubicMetricBox d cubicOrigin n,
            translatedCylinderIndicator A x ω) /
              ((cubicMetricBox d cubicOrigin n).card : ℝ) = eventIndicator A ω := by
      apply (div_eq_iff (show ((cubicMetricBox d cubicOrigin n).card : ℝ) ≠ 0 by
        exact_mod_cast (Finset.card_pos.mpr hs).ne')).2
      rw [Finset.sum_congr rfl (fun x _hx ↦ by
        rw [translatedCylinderIndicator, hinv x]), Finset.sum_const, nsmul_eq_mul]
      ring
    rw [hsum]
    by_cases hω : ω ∈ A
    · rw [eventIndicator, Set.indicator_of_mem hω,
        abs_of_nonneg (sub_nonneg.mpr hq1)]
      dsimp [ε]
      nlinarith [mul_nonneg hq0 (sub_nonneg.mpr hq1)]
    · rw [eventIndicator, Set.indicator_of_notMem hω, zero_sub, abs_neg,
        abs_of_nonneg hq0]
      dsimp [ε]
      nlinarith [mul_nonneg hq0 (sub_nonneg.mpr hq1)]
  have hsmall := hN N le_rfl
  rw [hdev] at hsmall
  have huniv : (bernoulliBondMeasure d p).real Set.univ = 1 := by
    simp [Measure.real]
  rw [huniv] at hsmall
  norm_num [Real.dist_eq] at hsmall

end Percolation
