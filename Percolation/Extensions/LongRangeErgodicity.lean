import Percolation.Extensions.LongRange
import Percolation.Critical.FiniteCylinderField

/-!
# Translation averages for long-range product measures

The cut argument for Grimmett's criterion (12.1) needs only a weak spatial law of large
numbers.  This file proves it directly by finite-cylinder approximation.  The proof remains
valid for the infinite-range edge set because each approximating cylinder has finite support,
and sufficiently separated translations of that support are independent.
-/

namespace Percolation

open Filter MeasureTheory ProbabilityTheory
open scoped unitInterval symmDiff

/-- Indicator field obtained by translating a long-range event. -/
noncomputable def longRangeTranslatedIndicator
    (A : Set LongRangeConfiguration) (a : ℤ) : LongRangeConfiguration → ℝ :=
  eventIndicator (longRangeTranslatedEvent a A)

theorem measurable_longRangeTranslatedIndicator {A : Set LongRangeConfiguration}
    (hA : MeasurableSet A) (a : ℤ) :
    Measurable (longRangeTranslatedIndicator A a) :=
  measurable_eventIndicator (measurableSet_longRangeTranslatedEvent hA a)

theorem memLp_longRangeTranslatedIndicator {A : Set LongRangeConfiguration}
    (hA : MeasurableSet A) (p : LongRangeProfile) (a : ℤ) :
    MemLp (longRangeTranslatedIndicator A a) 2 (longRangeMeasure p) :=
  memLp_eventIndicator (measurableSet_longRangeTranslatedEvent hA a)

theorem integral_longRangeTranslatedIndicator {A : Set LongRangeConfiguration}
    (hA : MeasurableSet A) (p : LongRangeProfile) (a : ℤ) :
    ∫ ω, longRangeTranslatedIndicator A a ω ∂longRangeMeasure p =
      (longRangeMeasure p).real A := by
  rw [longRangeTranslatedIndicator,
    integral_eventIndicator (measurableSet_longRangeTranslatedEvent hA a),
    longRangeMeasure_real_translatedEvent p hA a]

theorem covariance_longRangeTranslatedIndicator_le_one
    {A : Set LongRangeConfiguration} (hA : MeasurableSet A)
    (p : LongRangeProfile) (a b : ℤ) :
    cov[longRangeTranslatedIndicator A a, longRangeTranslatedIndicator A b;
      longRangeMeasure p] ≤ 1 :=
  covariance_eventIndicator_le_one
    (measurableSet_longRangeTranslatedEvent hA a)
    (measurableSet_longRangeTranslatedEvent hA b)

theorem covariance_longRangeTranslatedIndicator_eq_zero_of_far
    {E : Finset (Sym2 ℤ)} {A : Set LongRangeConfiguration}
    (hA : DependsOn E A) (p : LongRangeProfile) {a b : ℤ}
    (hab : 2 * longRangeEdgeSetRadius E < (a - b).natAbs) :
    cov[longRangeTranslatedIndicator A a, longRangeTranslatedIndicator A b;
      longRangeMeasure p] = 0 := by
  let S := E.map (longRangeEdgeTranslateEmbedding a)
  let T := E.map (longRangeEdgeTranslateEmbedding b)
  have hST : Disjoint S T := by
    exact disjoint_longRangeTranslatedEdgeSets_of_far E hab
  have hIndep : IndepSet (longRangeTranslatedEvent a A)
      (longRangeTranslatedEvent b A) (longRangeMeasure p) := by
    simpa only [longRangeMeasure] using
      inhomogeneousSetBernoulli_indepSet_of_dependsOn
        (longRangeEdgeDensity p) hST
        (dependsOn_longRangeTranslatedEvent hA a)
        (dependsOn_longRangeTranslatedEvent hA b)
  have ham := measurableSet_longRangeTranslatedEvent hA.measurableSet a
  have hbm := measurableSet_longRangeTranslatedEvent hA.measurableSet b
  rw [longRangeTranslatedIndicator, longRangeTranslatedIndicator,
    covariance_eventIndicator ham hbm]
  have hprod := hIndep.measure_inter_eq_mul
  have hprodReal :
      (longRangeMeasure p).real
          (longRangeTranslatedEvent a A ∩ longRangeTranslatedEvent b A) =
        (longRangeMeasure p).real (longRangeTranslatedEvent a A) *
          (longRangeMeasure p).real (longRangeTranslatedEvent b A) := by
    simpa [Measure.real, ENNReal.toReal_mul] using congrArg ENNReal.toReal hprod
  rw [hprodReal, sub_self]

theorem longRangeTranslationNeighborhood_card (a : ℤ) (D : ℕ) :
    (Finset.Icc (a - D) (a + D)).card = 2 * D + 1 := by
  rw [Int.card_Icc]
  omega

theorem natAbs_sub_gt_of_not_mem_translationNeighborhood
    {a b : ℤ} {D : ℕ} (h : b ∉ Finset.Icc (a - D) (a + D)) :
    D < (a - b).natAbs := by
  simp only [Finset.mem_Icc, not_and_or, not_le] at h
  rcases h with h | h
  · have hab : (D : ℤ) < a - b := by omega
    have hle : a - b ≤ ((a - b).natAbs : ℤ) := Int.le_natAbs
    have hcast : (D : ℤ) < (a - b).natAbs := hab.trans_le hle
    exact_mod_cast hcast
  · have hba : (D : ℤ) < b - a := by omega
    have habs : (a - b).natAbs = (b - a).natAbs := by
      rw [show a - b = -(b - a) by ring, Int.natAbs_neg]
    rw [habs]
    have hle : b - a ≤ ((b - a).natAbs : ℤ) := Int.le_natAbs
    have hcast : (D : ℤ) < (b - a).natAbs := hba.trans_le hle
    exact_mod_cast hcast

/-- Variance of a translated finite-cylinder average. -/
theorem variance_longRangeTranslatedCylinderAverage_le
    {E : Finset (Sym2 ℤ)} {A : Set LongRangeConfiguration}
    (hA : DependsOn E A) (p : LongRangeProfile)
    (s : Finset ℤ) (hs : s.Nonempty) :
    Var[fun ω ↦ (∑ a ∈ s, longRangeTranslatedIndicator A a ω) / (s.card : ℝ);
      longRangeMeasure p] ≤
      ((4 * longRangeEdgeSetRadius E + 1 : ℕ) : ℝ) / s.card := by
  let D := 2 * longRangeEdgeSetRadius E
  let N : ℤ → Finset ℤ := fun a ↦ Finset.Icc (a - D) (a + D)
  exact variance_finset_average_le_of_finite_covariance_neighborhood
    (longRangeMeasure p) s hs (longRangeTranslatedIndicator A)
    (fun a _ha ↦ memLp_longRangeTranslatedIndicator hA.measurableSet p a)
    N (4 * longRangeEdgeSetRadius E + 1)
    (fun a _ha ↦ by
      dsimp [N, D]
      have hc := longRangeTranslationNeighborhood_card a
        (2 * longRangeEdgeSetRadius E)
      exact hc.le.trans (by omega))
    (fun a _ha b _hb hbN ↦ by
      apply covariance_longRangeTranslatedIndicator_eq_zero_of_far hA p
      exact natAbs_sub_gt_of_not_mem_translationNeighborhood hbN)
    (fun a _ha b _hb ↦
      covariance_longRangeTranslatedIndicator_le_one hA.measurableSet p a b)

theorem integral_longRangeTranslatedAverage
    {A : Set LongRangeConfiguration} (hA : MeasurableSet A)
    (p : LongRangeProfile) (s : Finset ℤ) (hs : s.Nonempty) :
    ∫ ω, (∑ a ∈ s, longRangeTranslatedIndicator A a ω) / (s.card : ℝ)
        ∂longRangeMeasure p =
      (longRangeMeasure p).real A := by
  rw [integral_div, integral_finsetSum s (fun a _ha ↦
    (memLp_longRangeTranslatedIndicator hA p a).integrable one_le_two)]
  simp_rw [integral_longRangeTranslatedIndicator hA p]
  rw [Finset.sum_const, nsmul_eq_mul]
  field_simp [show (s.card : ℝ) ≠ 0 by
    exact_mod_cast (Finset.card_pos.mpr hs).ne']

/-- Explicit Chebyshev estimate for a finite-cylinder translation average. -/
theorem longRangeMeasure_real_translatedCylinderAverage_deviation_le
    {E : Finset (Sym2 ℤ)} {A : Set LongRangeConfiguration}
    (hA : DependsOn E A) (p : LongRangeProfile)
    (s : Finset ℤ) (hs : s.Nonempty) {ε : ℝ} (hε : 0 < ε) :
    (longRangeMeasure p).real
        {ω | ε ≤ |(∑ a ∈ s, longRangeTranslatedIndicator A a ω) /
            (s.card : ℝ) - (longRangeMeasure p).real A|} ≤
      ((((4 * longRangeEdgeSetRadius E + 1 : ℕ) : ℝ) / s.card) / ε ^ 2) := by
  have h := measure_average_deviation_le_of_finite_covariance_neighborhood
    (longRangeMeasure p) s hs (longRangeTranslatedIndicator A)
    (fun a _ha ↦ memLp_longRangeTranslatedIndicator hA.measurableSet p a)
    (fun a ↦ Finset.Icc
      (a - 2 * longRangeEdgeSetRadius E) (a + 2 * longRangeEdgeSetRadius E))
    (4 * longRangeEdgeSetRadius E + 1)
    (fun a _ha ↦ by
      have hc := longRangeTranslationNeighborhood_card a
        (2 * longRangeEdgeSetRadius E)
      exact hc.le.trans (by omega))
    (fun a _ha b _hb hbN ↦ by
      apply covariance_longRangeTranslatedIndicator_eq_zero_of_far hA p
      exact natAbs_sub_gt_of_not_mem_translationNeighborhood hbN)
    (fun a _ha b _hb ↦
      covariance_longRangeTranslatedIndicator_le_one hA.measurableSet p a b)
    hε
  rw [integral_longRangeTranslatedAverage hA.measurableSet p s hs] at h
  have hnonneg : 0 ≤
      ((((4 * longRangeEdgeSetRadius E + 1 : ℕ) : ℝ) / s.card) / ε ^ 2) := by
    positivity
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  simpa only [Measure.real, ENNReal.toReal_ofReal hnonneg] using hreal

theorem longRangeTranslatedEvent_symmDiff (a : ℤ)
    (A B : Set LongRangeConfiguration) :
    longRangeTranslatedEvent a (A ∆ B) =
      longRangeTranslatedEvent a A ∆ longRangeTranslatedEvent a B := by
  rfl

theorem abs_longRangeEventIndicator_sub_eventIndicator
    (A B : Set LongRangeConfiguration) (ω : LongRangeConfiguration) :
    |eventIndicator A ω - eventIndicator B ω| = eventIndicator (A ∆ B) ω := by
  by_cases hA : ω ∈ A <;> by_cases hB : ω ∈ B <;>
    simp [eventIndicator, hA, hB, Set.mem_symmDiff]

theorem abs_longRange_finset_average_sub_average_le_average_abs_sub
    {s : Finset ℤ} (hs : s.Nonempty) (f g : ℤ → ℝ) :
    |(∑ x ∈ s, f x) / (s.card : ℝ) - (∑ x ∈ s, g x) / (s.card : ℝ)| ≤
      (∑ x ∈ s, |f x - g x|) / (s.card : ℝ) := by
  have hcard : (0 : ℝ) < s.card := by
    exact_mod_cast Finset.card_pos.mpr hs
  rw [div_sub_div_same, ← Finset.sum_sub_distrib, abs_div, abs_of_pos hcard]
  exact div_le_div_of_nonneg_right
    (Finset.abs_sum_le_sum_abs (fun x ↦ f x - g x) s) hcard.le

theorem integral_longRangeTranslatedSymmDiffAverage
    {A C : Set LongRangeConfiguration} (hA : MeasurableSet A) (hC : MeasurableSet C)
    (p : LongRangeProfile) (s : Finset ℤ) (hs : s.Nonempty) :
    ∫ ω, (∑ a ∈ s,
        |longRangeTranslatedIndicator A a ω - longRangeTranslatedIndicator C a ω|) /
          (s.card : ℝ) ∂longRangeMeasure p =
      (longRangeMeasure p).real (A ∆ C) := by
  have hAC : MeasurableSet (A ∆ C) := hA.symmDiff hC
  have hfun : (fun ω ↦ (∑ a ∈ s,
      |longRangeTranslatedIndicator A a ω - longRangeTranslatedIndicator C a ω|) /
        (s.card : ℝ)) =
      fun ω ↦ (∑ a ∈ s, longRangeTranslatedIndicator (A ∆ C) a ω) /
        (s.card : ℝ) := by
    funext ω
    congr 1
    apply Finset.sum_congr rfl
    intro a _ha
    rw [longRangeTranslatedIndicator, longRangeTranslatedIndicator,
      abs_longRangeEventIndicator_sub_eventIndicator]
    simp only [longRangeTranslatedIndicator]
    rw [longRangeTranslatedEvent_symmDiff]
  rw [hfun]
  exact integral_longRangeTranslatedAverage hAC p s hs

theorem longRangeMeasure_real_translatedIndicator_discrepancy_le
    {A C : Set LongRangeConfiguration} (hA : MeasurableSet A) (hC : MeasurableSet C)
    (p : LongRangeProfile) (s : Finset ℤ) (hs : s.Nonempty)
    {ε : ℝ} (hε : 0 < ε) :
    (longRangeMeasure p).real
        {ω | ε ≤ (∑ a ∈ s,
          |longRangeTranslatedIndicator A a ω - longRangeTranslatedIndicator C a ω|) /
            (s.card : ℝ)} ≤
      (longRangeMeasure p).real (A ∆ C) / ε := by
  let f : LongRangeConfiguration → ℝ := fun ω ↦
    (∑ a ∈ s,
      |longRangeTranslatedIndicator A a ω - longRangeTranslatedIndicator C a ω|) /
        (s.card : ℝ)
  have hnonneg : 0 ≤ᵐ[longRangeMeasure p] f := by
    filter_upwards [] with ω
    exact div_nonneg (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _) (Nat.cast_nonneg _)
  have hint : Integrable f (longRangeMeasure p) := by
    have hAint (a : ℤ) :
        Integrable (longRangeTranslatedIndicator A a) (longRangeMeasure p) :=
      (memLp_longRangeTranslatedIndicator hA p a).integrable one_le_two
    have hCint (a : ℤ) :
        Integrable (longRangeTranslatedIndicator C a) (longRangeMeasure p) :=
      (memLp_longRangeTranslatedIndicator hC p a).integrable one_le_two
    dsimp [f]
    exact (integrable_finsetSum s fun a _ ↦ (hAint a).sub (hCint a) |>.abs).div_const _
  have hmarkov := mul_meas_ge_le_integral_of_nonneg hnonneg hint ε
  have hintegral : ∫ ω, f ω ∂longRangeMeasure p =
      (longRangeMeasure p).real (A ∆ C) :=
    integral_longRangeTranslatedSymmDiffAverage hA hC p s hs
  rw [hintegral] at hmarkov
  apply (le_div_iff₀ hε).2
  change (longRangeMeasure p).real {ω | ε ≤ f ω} * ε ≤
    (longRangeMeasure p).real (A ∆ C)
  rw [mul_comm]
  exact hmarkov

/-- Integer interval used for the one-dimensional translation average. -/
noncomputable def longRangeTranslationInterval (m : ℤ) (n : ℕ) : Finset ℤ :=
  Finset.Icc m (m + n)

@[simp]
theorem longRangeTranslationInterval_card (m : ℤ) (n : ℕ) :
    (longRangeTranslationInterval m n).card = n + 1 := by
  rw [longRangeTranslationInterval, Int.card_Icc]
  have h : m + (n : ℤ) + 1 - m = ((n + 1 : ℕ) : ℤ) := by omega
  rw [h, Int.toNat_natCast]

theorem longRangeTranslationInterval_nonempty (m : ℤ) (n : ℕ) :
    (longRangeTranslationInterval m n).Nonempty := by
  exact ⟨m, by simp [longRangeTranslationInterval]⟩

/-- Weak law for averages of translates of an arbitrary measurable long-range event. -/
theorem longRangeTranslatedEventAverage_measureReal_tendsto_zero
    (p : LongRangeProfile) {A : Set LongRangeConfiguration}
    (hA : MeasurableSet A) (m : ℤ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto
      (fun n ↦ (longRangeMeasure p).real
        {ω | ε ≤
          |(∑ a ∈ longRangeTranslationInterval m n,
              longRangeTranslatedIndicator A a ω) /
                ((longRangeTranslationInterval m n).card : ℝ) -
            (longRangeMeasure p).real A|})
      atTop (nhds 0) := by
  apply Metric.tendsto_atTop.2
  intro η hη
  let μ := longRangeMeasure p
  have htolerance : 0 < min (ε / 4) (η * ε / 8) := by positivity
  obtain ⟨E, C, hC, happrox⟩ :=
    exists_dependsOn_measureReal_symmDiff_lt μ hA htolerance
  have happroxε : μ.real (A ∆ C) < ε / 4 :=
    happrox.trans_le (min_le_left _ _)
  have happroxη : μ.real (A ∆ C) < η * ε / 8 :=
    happrox.trans_le (min_le_right _ _)
  let D : ℝ := (4 * longRangeEdgeSetRadius E + 1 : ℕ)
  have hden : Tendsto
      (fun n : ℕ ↦ ((longRangeTranslationInterval m n).card : ℝ)) atTop atTop := by
    have hcast : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop
    have h := hcast.comp (tendsto_add_atTop_nat (1 : ℕ))
    convert h using 1
    funext n
    simp [Function.comp_apply]
  have hvariance : Tendsto
      (fun n : ℕ ↦
        (D / ((longRangeTranslationInterval m n).card : ℝ)) / (ε / 2) ^ 2)
      atTop (nhds 0) := by
    simpa using (hden.const_div_atTop D).div_const ((ε / 2) ^ 2)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hvariance (η / 2) (by positivity)
  refine ⟨N, fun n hn ↦ ?_⟩
  let s := longRangeTranslationInterval m n
  have hs : s.Nonempty := longRangeTranslationInterval_nonempty m n
  let a : LongRangeConfiguration → ℝ := fun ω ↦
    (∑ x ∈ s, longRangeTranslatedIndicator A x ω) / (s.card : ℝ)
  let c : LongRangeConfiguration → ℝ := fun ω ↦
    (∑ x ∈ s, longRangeTranslatedIndicator C x ω) / (s.card : ℝ)
  let r : LongRangeConfiguration → ℝ := fun ω ↦
    (∑ x ∈ s,
      |longRangeTranslatedIndicator A x ω - longRangeTranslatedIndicator C x ω|) /
        (s.card : ℝ)
  have hcenter : |μ.real C - μ.real A| ≤ μ.real (A ∆ C) := by
    simpa [abs_sub_comm, symmDiff_comm] using
      (abs_measureReal_sub_le_measureReal_symmDiff (μ := μ)
        hC.measurableSet.nullMeasurableSet hA.nullMeasurableSet)
  have hsubset :
      {ω | ε ≤ |a ω - μ.real A|} ⊆
        {ω | ε / 4 ≤ r ω} ∪ {ω | ε / 2 ≤ |c ω - μ.real C|} := by
    intro ω hω
    by_contra hnot
    rw [Set.mem_union, not_or] at hnot
    have hr : r ω < ε / 4 := not_le.mp hnot.1
    have hc : |c ω - μ.real C| < ε / 2 := not_le.mp hnot.2
    have hac : |a ω - c ω| ≤ r ω := by
      exact abs_longRange_finset_average_sub_average_le_average_abs_sub hs
        (fun x ↦ longRangeTranslatedIndicator A x ω)
        (fun x ↦ longRangeTranslatedIndicator C x ω)
    have hca : |μ.real C - μ.real A| < ε / 4 := hcenter.trans_lt happroxε
    have htri : |a ω - μ.real A| ≤
        |a ω - c ω| + |c ω - μ.real C| + |μ.real C - μ.real A| := by
      calc
        |a ω - μ.real A| ≤ |a ω - c ω| + |c ω - μ.real A| :=
          abs_sub_le (a ω) (c ω) (μ.real A)
        _ ≤ |a ω - c ω| +
            (|c ω - μ.real C| + |μ.real C - μ.real A|) :=
          add_le_add le_rfl (abs_sub_le (c ω) (μ.real C) (μ.real A))
        _ = _ := by ring
    exact (not_lt_of_ge hω) (lt_of_le_of_lt htri (by linarith))
  have hbound :
      μ.real {ω | ε ≤ |a ω - μ.real A|} ≤
        μ.real (A ∆ C) / (ε / 4) +
          (D / (s.card : ℝ)) / (ε / 2) ^ 2 := by
    calc
      μ.real {ω | ε ≤ |a ω - μ.real A|} ≤
          μ.real ({ω | ε / 4 ≤ r ω} ∪
            {ω | ε / 2 ≤ |c ω - μ.real C|}) := measureReal_mono hsubset
      _ ≤ μ.real {ω | ε / 4 ≤ r ω} +
          μ.real {ω | ε / 2 ≤ |c ω - μ.real C|} := measureReal_union_le _ _
      _ ≤ μ.real (A ∆ C) / (ε / 4) +
          (D / (s.card : ℝ)) / (ε / 2) ^ 2 := by
        apply add_le_add
        · exact longRangeMeasure_real_translatedIndicator_discrepancy_le
            hA hC.measurableSet p s hs (by positivity)
        · simpa [μ, D] using
            longRangeMeasure_real_translatedCylinderAverage_deviation_le
              hC p s hs (by positivity : 0 < ε / 2)
  have hfirst : μ.real (A ∆ C) / (ε / 4) < η / 2 := by
    apply (div_lt_iff₀ (by positivity : 0 < ε / 4)).2
    nlinarith
  have hsecond : (D / (s.card : ℝ)) / (ε / 2) ^ 2 < η / 2 := by
    have hnonneg : 0 ≤ (D / (s.card : ℝ)) / (ε / 2) ^ 2 := by
      dsimp [D]
      positivity
    have hn' := hN n hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg] at hn'
    exact hn'
  rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg]
  change μ.real {ω | ε ≤ |a ω - μ.real A|} < η
  exact hbound.trans_lt (by linarith)

/-- At least one translate indexed by `s` occurs. -/
def longRangeTranslateOccursIn (A : Set LongRangeConfiguration) (s : Finset ℤ) :
    Set LongRangeConfiguration :=
  {ω | ∃ a ∈ s, ω ∈ longRangeTranslatedEvent a A}

theorem measurableSet_longRangeTranslateOccursIn
    {A : Set LongRangeConfiguration} (hA : MeasurableSet A) (s : Finset ℤ) :
    MeasurableSet (longRangeTranslateOccursIn A s) := by
  rw [show longRangeTranslateOccursIn A s =
      ⋃ a : s, longRangeTranslatedEvent a A by
    ext ω
    simp [longRangeTranslateOccursIn]]
  exact MeasurableSet.iUnion fun a ↦ measurableSet_longRangeTranslatedEvent hA a

/-- Some translate at an index at least `m` occurs. -/
def longRangeTranslateOccursEventually (A : Set LongRangeConfiguration) (m : ℤ) :
    Set LongRangeConfiguration :=
  {ω | ∃ a : ℤ, m ≤ a ∧ ω ∈ longRangeTranslatedEvent a A}

theorem measurableSet_longRangeTranslateOccursEventually
    {A : Set LongRangeConfiguration} (hA : MeasurableSet A) (m : ℤ) :
    MeasurableSet (longRangeTranslateOccursEventually A m) := by
  rw [show longRangeTranslateOccursEventually A m =
      ⋃ a : ℤ, if m ≤ a then longRangeTranslatedEvent a A else ∅ by
    ext ω
    simp [longRangeTranslateOccursEventually]]
  exact MeasurableSet.iUnion fun a ↦ by
    split_ifs
    · exact measurableSet_longRangeTranslatedEvent hA a
    · exact MeasurableSet.empty

theorem longRangeTranslateOccursIn_subset_eventually
    (A : Set LongRangeConfiguration) (m : ℤ) (n : ℕ) :
    longRangeTranslateOccursIn A (longRangeTranslationInterval m n) ⊆
      longRangeTranslateOccursEventually A m := by
  rintro ω ⟨a, ha, hω⟩
  exact ⟨a, (Finset.mem_Icc.mp ha).1, hω⟩

/-- A positive-probability measurable event has a translate arbitrarily far to the right almost
surely.  This is the weak-law substitute for the ergodic theorem in Grimmett's proof of (12.1). -/
theorem longRangeMeasure_real_translateOccursEventually_eq_one
    (p : LongRangeProfile) {A : Set LongRangeConfiguration}
    (hA : MeasurableSet A) (hApos : 0 < (longRangeMeasure p).real A) (m : ℤ) :
    (longRangeMeasure p).real (longRangeTranslateOccursEventually A m) = 1 := by
  let q := (longRangeMeasure p).real A
  have hq : 0 < q := hApos
  let U : ℕ → Set LongRangeConfiguration := fun n ↦
    longRangeTranslateOccursIn A (longRangeTranslationInterval m n)
  have hUm (n : ℕ) : MeasurableSet (U n) :=
    measurableSet_longRangeTranslateOccursIn hA _
  have hcompSubset (n : ℕ) :
      (U n)ᶜ ⊆
        {ω | q / 2 ≤
          |(∑ a ∈ longRangeTranslationInterval m n,
              longRangeTranslatedIndicator A a ω) /
                ((longRangeTranslationInterval m n).card : ℝ) - q|} := by
    intro ω hω
    have hzero :
        (∑ a ∈ longRangeTranslationInterval m n,
          longRangeTranslatedIndicator A a ω) = 0 := by
      apply Finset.sum_eq_zero
      intro a ha
      have hnot : ω ∉ longRangeTranslatedEvent a A := by
        intro haω
        exact hω ⟨a, ha, haω⟩
      simp [longRangeTranslatedIndicator, eventIndicator, hnot]
    change q / 2 ≤
      |(∑ a ∈ longRangeTranslationInterval m n,
          longRangeTranslatedIndicator A a ω) /
            ((longRangeTranslationInterval m n).card : ℝ) - q|
    rw [hzero, zero_div, zero_sub, abs_neg, abs_of_pos hq]
    linarith
  have hdev := longRangeTranslatedEventAverage_measureReal_tendsto_zero
    p hA m (show 0 < q / 2 by positivity)
  have hcomp : Tendsto (fun n ↦ (longRangeMeasure p).real (U n)ᶜ)
      atTop (nhds 0) := by
    exact squeeze_zero
      (f := fun n ↦ (longRangeMeasure p).real (U n)ᶜ)
      (g := fun n ↦ (longRangeMeasure p).real
        {ω | q / 2 ≤
          |(∑ a ∈ longRangeTranslationInterval m n,
              longRangeTranslatedIndicator A a ω) /
                ((longRangeTranslationInterval m n).card : ℝ) - q|})
      (fun _ ↦ measureReal_nonneg)
      (fun n ↦ measureReal_mono (hcompSubset n))
      (by simpa [q] using hdev)
  have hU : Tendsto (fun n ↦ (longRangeMeasure p).real (U n))
      atTop (nhds 1) := by
    have hEq (n : ℕ) : (longRangeMeasure p).real (U n) =
        1 - (longRangeMeasure p).real (U n)ᶜ := by
      have hc := measureReal_compl (μ := longRangeMeasure p) (hUm n)
      rw [show (longRangeMeasure p).real Set.univ = 1 by simp [Measure.real]] at hc
      linarith
    have hsub : Tendsto
        (fun n ↦ (1 : ℝ) - (longRangeMeasure p).real (U n)ᶜ)
        atTop (nhds 1) := by
      simpa using (tendsto_const_nhds.sub hcomp)
    exact hsub.congr' (Filter.Eventually.of_forall fun n ↦ (hEq n).symm)
  have hle (n : ℕ) : (longRangeMeasure p).real (U n) ≤
      (longRangeMeasure p).real (longRangeTranslateOccursEventually A m) :=
    measureReal_mono (longRangeTranslateOccursIn_subset_eventually A m n)
  exact le_antisymm measureReal_le_one
    (le_of_tendsto hU (Filter.Eventually.of_forall hle))

end Percolation
