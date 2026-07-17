import Percolation.Critical.InfiniteClusterDensity
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-!
# An almost-sure box law from summable finite-cylinder approximations

This file upgrades the finite-range variance estimate for translated cylinder fields to an
almost-sure law for a measurable event which admits a summably accurate sequence of finite
cylinder approximations.  The result is tailored to the replacement for the multiparameter
ergodic theorem in Grimmett's Theorem 8.99: exponentially accurate radius truncations have
summable approximation error, while their slowly growing supports retain a summable variance
bound in dimensions at least two.
-/

namespace Percolation

open Filter MeasureTheory ProbabilityTheory
open scoped symmDiff unitInterval

/-- Average of the translated indicators of an event over a nonempty finite vertex set. -/
noncomputable def translatedEventAverage {d : ℕ}
    (A : Set (EdgeConfiguration d)) (s : Finset (Cubic d))
    (omega : EdgeConfiguration d) : ℝ :=
  (∑ x ∈ s, translatedCylinderIndicator A x omega) / (s.card : ℝ)

/-- Quantitative deviation estimate for a general measurable event, obtained by replacing it
with a finite cylinder.  This is the abstract form of the estimate previously used for the
infinite-cluster vertex field. -/
theorem bernoulliBondMeasure_real_translatedEventAverage_deviation_le_of_approx
    {d : ℕ} (p : I) {A C : Set (EdgeConfiguration d)}
    (hA : MeasurableSet A) {E : Finset (CubicEdge d)} (hC : DependsOn E C)
    (s : Finset (Cubic d)) (hs : s.Nonempty)
    {ε : ℝ} (hε : 0 < ε)
    (happrox : (bernoulliBondMeasure d p).real (A ∆ C) < ε / 4) :
    (bernoulliBondMeasure d p).real
        {omega | ε ≤
          |translatedEventAverage A s omega -
            (bernoulliBondMeasure d p).real A|} ≤
      (bernoulliBondMeasure d p).real (A ∆ C) / (ε / 4) +
        (((((2 * (2 * cubicEdgeSetRadius E) + 1) ^ d : ℕ) : ℝ) / s.card) /
          (ε / 2) ^ 2) := by
  let a : EdgeConfiguration d → ℝ := fun omega ↦ translatedEventAverage A s omega
  let c : EdgeConfiguration d → ℝ := fun omega ↦ translatedEventAverage C s omega
  let m : EdgeConfiguration d → ℝ := fun omega ↦
    (∑ x ∈ s,
      |translatedCylinderIndicator A x omega - translatedCylinderIndicator C x omega|) /
        (s.card : ℝ)
  let μ := bernoulliBondMeasure d p
  have hεfour : 0 < ε / 4 := by positivity
  have hεtwo : 0 < ε / 2 := by positivity
  have hcenter : |μ.real C - μ.real A| ≤ μ.real (A ∆ C) := by
    simpa [abs_sub_comm, symmDiff_comm] using
      (abs_measureReal_sub_le_measureReal_symmDiff (μ := μ)
        hC.measurableSet.nullMeasurableSet hA.nullMeasurableSet)
  have hsubset :
      {omega | ε ≤ |a omega - μ.real A|} ⊆
        {omega | ε / 4 ≤ m omega} ∪
          {omega | ε / 2 ≤ |c omega - μ.real C|} := by
    intro omega homega
    by_contra hnot
    rw [Set.mem_union, not_or] at hnot
    have hm : m omega < ε / 4 := not_le.mp hnot.1
    have hc : |c omega - μ.real C| < ε / 2 := not_le.mp hnot.2
    have hac : |a omega - c omega| ≤ m omega := by
      exact abs_finset_average_sub_average_le_average_abs_sub hs
        (fun x ↦ translatedCylinderIndicator A x omega)
        (fun x ↦ translatedCylinderIndicator C x omega)
    have hca : |μ.real C - μ.real A| < ε / 4 :=
      hcenter.trans_lt (by simpa [μ] using happrox)
    have htri : |a omega - μ.real A| ≤
        |a omega - c omega| + |c omega - μ.real C| +
          |μ.real C - μ.real A| := by
      calc
        |a omega - μ.real A| ≤
            |a omega - c omega| + |c omega - μ.real A| :=
          abs_sub_le (a omega) (c omega) (μ.real A)
        _ ≤ |a omega - c omega| +
            (|c omega - μ.real C| + |μ.real C - μ.real A|) :=
          add_le_add le_rfl (abs_sub_le (c omega) (μ.real C) (μ.real A))
        _ = |a omega - c omega| + |c omega - μ.real C| +
            |μ.real C - μ.real A| := by ring
    exact (not_lt_of_ge homega) (lt_of_le_of_lt htri (by linarith))
  calc
    μ.real {omega | ε ≤ |translatedEventAverage A s omega - μ.real A|} =
        μ.real {omega | ε ≤ |a omega - μ.real A|} := rfl
    _ ≤ μ.real ({omega | ε / 4 ≤ m omega} ∪
          {omega | ε / 2 ≤ |c omega - μ.real C|}) :=
      measureReal_mono hsubset
    _ ≤ μ.real {omega | ε / 4 ≤ m omega} +
          μ.real {omega | ε / 2 ≤ |c omega - μ.real C|} :=
      measureReal_union_le _ _
    _ ≤ μ.real (A ∆ C) / (ε / 4) +
        (((((2 * (2 * cubicEdgeSetRadius E) + 1) ^ d : ℕ) : ℝ) / s.card) /
          (ε / 2) ^ 2) := by
      apply add_le_add
      · exact bernoulliBondMeasure_real_translatedIndicator_discrepancy_le
          hA hC.measurableSet p s hs hεfour
      · simpa [c, translatedEventAverage] using
          (bernoulliBondMeasure_real_translatedCylinderAverage_deviation_le
            hC p s hs hεtwo)

/-- A summably accurate family of finite-cylinder approximations, with summable finite-range
variance costs, gives the almost-sure translated box law.  This is a direct Borel--Cantelli
replacement for the multiparameter pointwise ergodic theorem in the applications below. -/
theorem translatedEventAverage_tendsto_ae_of_summable_cylinderApprox
    {d : ℕ} (p : I) {A : Set (EdgeConfiguration d)} (hA : MeasurableSet A)
    (E : ℕ → Finset (CubicEdge d)) (C : ℕ → Set (EdgeConfiguration d))
    (hC : ∀ n, DependsOn (E n) (C n))
    (s : ℕ → Finset (Cubic d)) (hs : ∀ n, (s n).Nonempty)
    (happrox : Summable fun n ↦
      (bernoulliBondMeasure d p).real (A ∆ C n))
    (hrange : Summable fun n ↦
      ((((2 * (2 * cubicEdgeSetRadius (E n)) + 1) ^ d : ℕ) : ℝ) /
        (s n).card)) :
    ∀ᵐ omega ∂bernoulliBondMeasure d p,
      Tendsto (fun n ↦ translatedEventAverage A (s n) omega) atTop
        (nhds ((bernoulliBondMeasure d p).real A)) := by
  let μ := bernoulliBondMeasure d p
  let err : ℕ → ℝ := fun n ↦ μ.real (A ∆ C n)
  let rangeCost : ℕ → ℝ := fun n ↦
    ((((2 * (2 * cubicEdgeSetRadius (E n)) + 1) ^ d : ℕ) : ℝ) /
      (s n).card)
  have herr : Summable err := by simpa [err, μ] using happrox
  have hrange' : Summable rangeCost := by simpa [rangeCost] using hrange
  have herrZero : Tendsto err atTop (nhds 0) := herr.tendsto_atTop_zero
  have hforEach : ∀ k : ℕ, ∀ᵐ omega ∂μ,
      ∀ᶠ n in atTop,
        |translatedEventAverage A (s n) omega - μ.real A| <
          1 / ((k + 1 : ℕ) : ℝ) := by
    intro k
    let ε : ℝ := 1 / ((k + 1 : ℕ) : ℝ)
    have hε : 0 < ε := by positivity
    have hsmall : ∀ᶠ n in atTop, err n < ε / 4 := by
      obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 herrZero (ε / 4) (by positivity)
      refine eventually_atTop.2 ⟨N, fun n hn ↦ ?_⟩
      have hdist := hN n hn
      rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg] at hdist
      exact hdist
    let major : ℕ → ℝ := fun n ↦ err n / (ε / 4) + rangeCost n / (ε / 2) ^ 2
    have hmajor : Summable major := by
      exact (herr.div_const (ε / 4)).add (hrange'.div_const ((ε / 2) ^ 2))
    let bad : ℕ → Set (EdgeConfiguration d) := fun n ↦
      {omega | ε ≤ |translatedEventAverage A (s n) omega - μ.real A|}
    have hbadBound : ∀ᶠ n in atTop, μ.real (bad n) ≤ major n := by
      filter_upwards [hsmall] with n hn
      exact bernoulliBondMeasure_real_translatedEventAverage_deviation_le_of_approx
        p hA (hC n) (s n) (hs n) hε (by simpa [err, μ] using hn)
    have hbadSummable : Summable fun n ↦ μ.real (bad n) := by
      apply hmajor.of_norm_bounded_eventually_nat
      filter_upwards [hbadBound] with n hn
      rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
      exact hn
    have hbadENNReal : (∑' n, μ (bad n)) ≠ ⊤ := by
      have heq : (fun n ↦ μ (bad n)) = fun n ↦ ENNReal.ofReal (μ.real (bad n)) := by
        funext n
        exact (ENNReal.ofReal_toReal (measure_ne_top μ (bad n))).symm
      rw [heq]
      exact hbadSummable.tsum_ofReal_ne_top
    have hae := ae_eventually_notMem hbadENNReal
    filter_upwards [hae] with omega homega
    filter_upwards [homega] with n hn
    exact not_le.mp (by simpa [bad, ε] using hn)
  have hall : ∀ᵐ omega ∂μ, ∀ k : ℕ,
      ∀ᶠ n in atTop,
        |translatedEventAverage A (s n) omega - μ.real A| <
          1 / ((k + 1 : ℕ) : ℝ) :=
    ae_all_iff.mpr hforEach
  filter_upwards [hall] with omega homega
  apply Metric.tendsto_atTop.2
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  have hk' : 1 / ((k + 1 : ℕ) : ℝ) < ε := by
    simpa only [Nat.cast_add, Nat.cast_one] using hk
  obtain ⟨N, hN⟩ := eventually_atTop.1 (homega k)
  refine ⟨N, fun n hn ↦ ?_⟩
  rw [Real.dist_eq]
  exact (hN n hn).trans hk'

end Percolation
