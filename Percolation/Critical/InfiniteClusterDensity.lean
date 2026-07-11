import Percolation.Critical.FiniteCylinderField

/-!
# Density of vertices in infinite open clusters

The supercritical block argument in Grimmett Chapter 7 needs a weak law for the proportion of
vertices in a large box which lie in infinite open clusters.  We prove it directly, without a
multiparameter pointwise ergodic theorem: approximate the origin event by a finite cylinder,
translate that cylinder, use finite-range covariance, and control the approximation error in
`L¹`.
-/

namespace Percolation

open Filter MeasureTheory ProbabilityTheory
open scoped symmDiff unitInterval

/-- Event that a specified cubic-lattice vertex lies in an infinite open cluster. -/
def infiniteClusterVertexEvent (d : ℕ) (x : Cubic d) : Set (EdgeConfiguration d) :=
  {ω | hasInfiniteOpenClusterFrom d ω x}

theorem measurableSet_infiniteClusterVertexEvent (d : ℕ) (x : Cubic d) :
    MeasurableSet (infiniteClusterVertexEvent d x) :=
  measurableSet_hasInfiniteOpenClusterFrom d x

/-- The event at `x` is the translate of the event at the origin. -/
theorem translatedCylinderEvent_infiniteClusterOrigin (d : ℕ) (x : Cubic d) :
    translatedCylinderEvent x (infiniteClusterVertexEvent d cubicOrigin) =
      infiniteClusterVertexEvent d x := by
  ext ω
  change hasInfiniteOpenClusterFrom d
      (cubicTranslationConfigurationPullback cubicOrigin x ω) cubicOrigin ↔
    hasInfiniteOpenClusterFrom d ω x
  simpa using
    (cubicTranslationConfigurationPullback_hasInfiniteOpenClusterFrom_iff
      ω cubicOrigin x cubicOrigin)

/-- Proportion of vertices of a nonempty finite set which lie in infinite open clusters.
The totalized empty-set value is zero and is not used by the convergence theorem. -/
noncomputable def infiniteClusterVertexDensity (d : ℕ) (s : Finset (Cubic d))
    (ω : EdgeConfiguration d) : ℝ :=
  (∑ x ∈ s, eventIndicator (infiniteClusterVertexEvent d x) ω) / (s.card : ℝ)

theorem infiniteClusterVertexDensity_eq_translatedAverage (d : ℕ)
    (s : Finset (Cubic d)) (ω : EdgeConfiguration d) :
    infiniteClusterVertexDensity d s ω =
      (∑ x ∈ s,
        translatedCylinderIndicator (infiniteClusterVertexEvent d cubicOrigin) x ω) /
          (s.card : ℝ) := by
  unfold infiniteClusterVertexDensity translatedCylinderIndicator
  simp_rw [translatedCylinderEvent_infiniteClusterOrigin]

theorem bernoulliBondMeasure_real_infiniteClusterVertexEvent_origin (d : ℕ) (p : I) :
    (bernoulliBondMeasure d p).real
        (infiniteClusterVertexEvent d cubicOrigin) = theta d p := by
  rfl

/-- Absolute difference of two event indicators is the indicator of their symmetric
difference. -/
theorem abs_eventIndicator_sub_eventIndicator {Ω : Type*} (A B : Set Ω) (ω : Ω) :
    |eventIndicator A ω - eventIndicator B ω| = eventIndicator (A ∆ B) ω := by
  by_cases hA : ω ∈ A <;> by_cases hB : ω ∈ B <;>
    simp [eventIndicator, hA, hB, Set.mem_symmDiff]

theorem translatedCylinderEvent_symmDiff {d : ℕ} (x : Cubic d)
    (A B : Set (EdgeConfiguration d)) :
    translatedCylinderEvent x (A ∆ B) =
      translatedCylinderEvent x A ∆ translatedCylinderEvent x B := by
  rfl

/-- The average absolute pointwise error between two translated event fields has expectation
equal to the symmetric-difference probability of the origin events. -/
theorem integral_translatedSymmDiffAverage {d : ℕ}
    {A C : Set (EdgeConfiguration d)} (hA : MeasurableSet A) (hC : MeasurableSet C)
    (p : I) (s : Finset (Cubic d)) (hs : s.Nonempty) :
    ∫ ω, (∑ x ∈ s,
        |translatedCylinderIndicator A x ω - translatedCylinderIndicator C x ω|) /
          (s.card : ℝ) ∂bernoulliBondMeasure d p =
      (bernoulliBondMeasure d p).real (A ∆ C) := by
  have hAC : MeasurableSet (A ∆ C) := hA.symmDiff hC
  have hfun : (fun ω ↦ (∑ x ∈ s,
      |translatedCylinderIndicator A x ω - translatedCylinderIndicator C x ω|) /
        (s.card : ℝ)) =
      fun ω ↦ (∑ x ∈ s, translatedCylinderIndicator (A ∆ C) x ω) /
        (s.card : ℝ) := by
    funext ω
    congr 1
    apply Finset.sum_congr rfl
    intro x hx
    rw [translatedCylinderIndicator, translatedCylinderIndicator,
      abs_eventIndicator_sub_eventIndicator]
    simp only [translatedCylinderIndicator]
    rw [translatedCylinderEvent_symmDiff]
  rw [hfun]
  exact integral_translatedCylinderAverage_of_measurable hAC p s hs

/-- Triangle inequality for two finite empirical averages. -/
theorem abs_finset_average_sub_average_le_average_abs_sub
    {ι : Type*} {s : Finset ι} (hs : s.Nonempty) (f g : ι → ℝ) :
    |(∑ x ∈ s, f x) / (s.card : ℝ) - (∑ x ∈ s, g x) / (s.card : ℝ)| ≤
      (∑ x ∈ s, |f x - g x|) / (s.card : ℝ) := by
  have hcard : (0 : ℝ) < s.card := by
    exact_mod_cast Finset.card_pos.mpr hs
  rw [div_sub_div_same, ← Finset.sum_sub_distrib, abs_div, abs_of_pos hcard]
  exact div_le_div_of_nonneg_right
    (Finset.abs_sum_le_sum_abs (fun x ↦ f x - g x) s) hcard.le

/-- Markov bound for the empirical discrepancy between translates of two events. -/
theorem bernoulliBondMeasure_real_translatedIndicator_discrepancy_le {d : ℕ}
    {A C : Set (EdgeConfiguration d)} (hA : MeasurableSet A) (hC : MeasurableSet C)
    (p : I) (s : Finset (Cubic d)) (hs : s.Nonempty)
    {ε : ℝ} (hε : 0 < ε) :
    (bernoulliBondMeasure d p).real
        {ω | ε ≤ (∑ x ∈ s,
          |translatedCylinderIndicator A x ω - translatedCylinderIndicator C x ω|) /
            (s.card : ℝ)} ≤
      (bernoulliBondMeasure d p).real (A ∆ C) / ε := by
  let f : EdgeConfiguration d → ℝ := fun ω ↦
    (∑ x ∈ s,
      |translatedCylinderIndicator A x ω - translatedCylinderIndicator C x ω|) /
        (s.card : ℝ)
  have hnonneg : 0 ≤ᵐ[bernoulliBondMeasure d p] f := by
    filter_upwards [] with ω
    exact div_nonneg (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _) (Nat.cast_nonneg _)
  have hint : Integrable f (bernoulliBondMeasure d p) := by
    have hAint (x : Cubic d) :
        Integrable (translatedCylinderIndicator A x) (bernoulliBondMeasure d p) :=
      (memLp_translatedCylinderIndicator_of_measurable hA p x).integrable one_le_two
    have hCint (x : Cubic d) :
        Integrable (translatedCylinderIndicator C x) (bernoulliBondMeasure d p) :=
      (memLp_translatedCylinderIndicator_of_measurable hC p x).integrable one_le_two
    dsimp [f]
    exact (integrable_finsetSum s fun x _ ↦ (hAint x).sub (hCint x) |>.abs).div_const _
  have hmarkov := mul_meas_ge_le_integral_of_nonneg hnonneg hint ε
  have hintegral : ∫ ω, f ω ∂bernoulliBondMeasure d p =
      (bernoulliBondMeasure d p).real (A ∆ C) := by
    exact integral_translatedSymmDiffAverage hA hC p s hs
  rw [hintegral] at hmarkov
  apply (le_div_iff₀ hε).2
  change (bernoulliBondMeasure d p).real {ω | ε ≤ f ω} * ε ≤
    (bernoulliBondMeasure d p).real (A ∆ C)
  rw [mul_comm]
  exact hmarkov

/-- Quantitative density estimate obtained from any finite-cylinder approximation of the
origin infinite-cluster event. -/
theorem bernoulliBondMeasure_real_infiniteClusterVertexDensity_deviation_le_of_approx
    {d : ℕ} (p : I) {E : Finset (CubicEdge d)} {C : Set (EdgeConfiguration d)}
    (hC : DependsOn E C) (s : Finset (Cubic d)) (hs : s.Nonempty)
    {ε : ℝ} (hε : 0 < ε)
    (happrox : (bernoulliBondMeasure d p).real
      (infiniteClusterVertexEvent d cubicOrigin ∆ C) < ε / 4) :
    (bernoulliBondMeasure d p).real
        {ω | ε ≤ |infiniteClusterVertexDensity d s ω - theta d p|} ≤
      (bernoulliBondMeasure d p).real
          (infiniteClusterVertexEvent d cubicOrigin ∆ C) / (ε / 4) +
        (((((2 * (2 * cubicEdgeSetRadius E) + 1) ^ d : ℕ) : ℝ) / s.card) /
          (ε / 2) ^ 2) := by
  let A : Set (EdgeConfiguration d) := infiniteClusterVertexEvent d cubicOrigin
  let a : EdgeConfiguration d → ℝ := fun ω ↦
    (∑ x ∈ s, translatedCylinderIndicator A x ω) / (s.card : ℝ)
  let c : EdgeConfiguration d → ℝ := fun ω ↦
    (∑ x ∈ s, translatedCylinderIndicator C x ω) / (s.card : ℝ)
  let m : EdgeConfiguration d → ℝ := fun ω ↦
    (∑ x ∈ s,
      |translatedCylinderIndicator A x ω - translatedCylinderIndicator C x ω|) /
        (s.card : ℝ)
  let μ := bernoulliBondMeasure d p
  have hAm : MeasurableSet A := measurableSet_infiniteClusterVertexEvent d cubicOrigin
  have hε4 : 0 < ε / 4 := by positivity
  have hε2 : 0 < ε / 2 := by positivity
  have hcenter : |μ.real C - μ.real A| ≤ μ.real (A ∆ C) := by
    simpa [abs_sub_comm, symmDiff_comm] using
      (abs_measureReal_sub_le_measureReal_symmDiff (μ := μ)
        hC.measurableSet.nullMeasurableSet hAm.nullMeasurableSet)
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
      hcenter.trans_lt (by simpa [μ, A] using happrox)
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
    have : |a ω - μ.real A| < ε := by linarith
    exact (not_lt_of_ge hω) this
  calc
    μ.real {ω | ε ≤ |infiniteClusterVertexDensity d s ω - theta d p|}
        = μ.real {ω | ε ≤ |a ω - μ.real A|} := by
          apply congrArg μ.real
          ext ω
          change (ε ≤ |infiniteClusterVertexDensity d s ω - theta d p|) ↔
            (ε ≤ |a ω - μ.real A|)
          rw [infiniteClusterVertexDensity_eq_translatedAverage]
          rfl
    _ ≤ μ.real ({ω | ε / 4 ≤ m ω} ∪
          {ω | ε / 2 ≤ |c ω - μ.real C|}) := measureReal_mono hsubset
    _ ≤ μ.real {ω | ε / 4 ≤ m ω} +
          μ.real {ω | ε / 2 ≤ |c ω - μ.real C|} := measureReal_union_le _ _
    _ ≤ μ.real (A ∆ C) / (ε / 4) +
          (((((2 * (2 * cubicEdgeSetRadius E) + 1) ^ d : ℕ) : ℝ) / s.card) /
            (ε / 2) ^ 2) := by
      apply add_le_add
      · exact bernoulliBondMeasure_real_translatedIndicator_discrepancy_le
          hAm hC.measurableSet p s hs hε4
      · exact bernoulliBondMeasure_real_translatedCylinderAverage_deviation_le
          hC p s hs hε2
    _ = μ.real (infiniteClusterVertexEvent d cubicOrigin ∆ C) / (ε / 4) +
          (((((2 * (2 * cubicEdgeSetRadius E) + 1) ^ d : ℕ) : ℝ) / s.card) /
            (ε / 2) ^ 2) := rfl

/-- The proportion of vertices in `B(n)` which lie in infinite open clusters converges in
probability to `θ(p)`.  This is the box-density law needed in the proof of Lemma 7.97. -/
theorem infiniteClusterVertexDensity_measureReal_tendsto_zero
    {d : ℕ} (hd : 1 ≤ d) (p : I) {ε : ℝ} (hε : 0 < ε) :
    Tendsto
      (fun n ↦ (bernoulliBondMeasure d p).real
        {ω | ε ≤
          |infiniteClusterVertexDensity d (cubicMetricBox d cubicOrigin n) ω -
            theta d p|})
      atTop (nhds 0) := by
  apply Metric.tendsto_atTop.2
  intro η hη
  let μ := bernoulliBondMeasure d p
  let A : Set (EdgeConfiguration d) := infiniteClusterVertexEvent d cubicOrigin
  have hAm : MeasurableSet A := measurableSet_infiniteClusterVertexEvent d cubicOrigin
  have htolerance : 0 < min (ε / 4) (η * ε / 8) := by positivity
  obtain ⟨E, C, hC, happrox⟩ :=
    exists_dependsOn_measureReal_symmDiff_lt μ hAm htolerance
  have happroxε : μ.real (A ∆ C) < ε / 4 :=
    happrox.trans_le (min_le_left _ _)
  have happroxη : μ.real (A ∆ C) < η * ε / 8 :=
    happrox.trans_le (min_le_right _ _)
  let D : ℝ := (((2 * (2 * cubicEdgeSetRadius E) + 1) ^ d : ℕ) : ℝ)
  have hden : Tendsto
      (fun n : ℕ ↦ ((cubicMetricBox d cubicOrigin n).card : ℝ)) atTop atTop := by
    apply Filter.tendsto_atTop_mono
      (f := fun n : ℕ ↦ (n : ℝ)) (g := fun n : ℕ ↦
        ((cubicMetricBox d cubicOrigin n).card : ℝ))
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
  have hbound :=
    bernoulliBondMeasure_real_infiniteClusterVertexDensity_deviation_le_of_approx
      p hC (cubicMetricBox d cubicOrigin n) hs hε (by simpa [μ, A] using happroxε)
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
  calc
    μ.real
        {ω | ε ≤
          |infiniteClusterVertexDensity d (cubicMetricBox d cubicOrigin n) ω - theta d p|}
        ≤ μ.real (A ∆ C) / (ε / 4) +
          (D / ((cubicMetricBox d cubicOrigin n).card : ℝ)) / (ε / 2) ^ 2 := by
            simpa [μ, A, D] using hbound
    _ < η := by linarith

end Percolation
