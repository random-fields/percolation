import Percolation.Critical.FiniteCylinderTranslation
import Percolation.Critical.RegionTranslation
import Percolation.Bernoulli.FiniteRangeVariance

/-!
# Finite-range fields from translated bond cylinders

The indicator translates of one finite bond event form a stationary finite-range random field.
This file proves the expectation and covariance facts needed to feed that field into the generic
finite-range variance estimate.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval

/-- Real indicator of an event. -/
noncomputable def eventIndicator {Ω : Type*} (A : Set Ω) : Ω → ℝ :=
  A.indicator fun _ ↦ 1

theorem measurable_eventIndicator {Ω : Type*} [MeasurableSpace Ω]
    {A : Set Ω} (hA : MeasurableSet A) : Measurable (eventIndicator A) :=
  measurable_const.indicator hA

theorem memLp_eventIndicator {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {A : Set Ω} (hA : MeasurableSet A) :
    MemLp (eventIndicator A) 2 μ := by
  apply memLp_of_bounded (a := 0) (b := 1)
  · filter_upwards [] with ω
    by_cases hω : ω ∈ A <;> simp [eventIndicator, hω]
  · exact (measurable_eventIndicator hA).aestronglyMeasurable

theorem integral_eventIndicator {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {A : Set Ω} (hA : MeasurableSet A) :
    ∫ ω, eventIndicator A ω ∂μ = μ.real A := by
  rw [eventIndicator, integral_indicator_const (1 : ℝ) hA,
    smul_eq_mul, mul_one]

theorem covariance_eventIndicator {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {A B : Set Ω} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    cov[eventIndicator A, eventIndicator B; μ] =
      μ.real (A ∩ B) - μ.real A * μ.real B := by
  have hmul : eventIndicator A * eventIndicator B = eventIndicator (A ∩ B) := by
    funext ω
    by_cases hωA : ω ∈ A <;> by_cases hωB : ω ∈ B <;>
      simp [eventIndicator, hωA, hωB]
  rw [covariance_eq_sub (memLp_eventIndicator hA) (memLp_eventIndicator hB), hmul,
    integral_eventIndicator (hA.inter hB), integral_eventIndicator hA,
    integral_eventIndicator hB]

theorem covariance_eventIndicator_le_one {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {A B : Set Ω} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    cov[eventIndicator A, eventIndicator B; μ] ≤ 1 := by
  rw [covariance_eventIndicator hA hB]
  have hprod : 0 ≤ μ.real A * μ.real B :=
    mul_nonneg measureReal_nonneg measureReal_nonneg
  have hinter : μ.real (A ∩ B) ≤ 1 := measureReal_le_one
  linarith

/-- Indicator field obtained by translating one origin-based finite cylinder. -/
noncomputable def translatedCylinderIndicator {d : ℕ} (A : Set (EdgeConfiguration d))
    (x : Cubic d) : EdgeConfiguration d → ℝ :=
  eventIndicator (translatedCylinderEvent x A)

theorem measurable_translatedCylinderIndicator_of_measurable {d : ℕ}
    {A : Set (EdgeConfiguration d)} (hA : MeasurableSet A) (x : Cubic d) :
    Measurable (translatedCylinderIndicator A x) :=
  measurable_eventIndicator (measurableSet_translatedCylinderEvent_of_measurable hA x)

theorem memLp_translatedCylinderIndicator_of_measurable {d : ℕ}
    {A : Set (EdgeConfiguration d)} (hA : MeasurableSet A) (p : I) (x : Cubic d) :
    MemLp (translatedCylinderIndicator A x) 2 (bernoulliBondMeasure d p) :=
  memLp_eventIndicator (measurableSet_translatedCylinderEvent_of_measurable hA x)

theorem integral_translatedCylinderIndicator_of_measurable {d : ℕ}
    {A : Set (EdgeConfiguration d)} (hA : MeasurableSet A) (p : I) (x : Cubic d) :
    ∫ ω, translatedCylinderIndicator A x ω ∂bernoulliBondMeasure d p =
      (bernoulliBondMeasure d p).real A := by
  rw [translatedCylinderIndicator,
    integral_eventIndicator (measurableSet_translatedCylinderEvent_of_measurable hA x),
    bernoulliBondMeasure_real_translatedEvent hA p x]

theorem measurable_translatedCylinderIndicator {d : ℕ}
    {E : Finset (CubicEdge d)} {A : Set (EdgeConfiguration d)}
    (hA : DependsOn E A) (x : Cubic d) :
    Measurable (translatedCylinderIndicator A x) :=
  measurable_eventIndicator (measurableSet_translatedCylinderEvent hA x)

theorem memLp_translatedCylinderIndicator {d : ℕ}
    {E : Finset (CubicEdge d)} {A : Set (EdgeConfiguration d)}
    (hA : DependsOn E A) (p : I) (x : Cubic d) :
    MemLp (translatedCylinderIndicator A x) 2 (bernoulliBondMeasure d p) :=
  memLp_eventIndicator (measurableSet_translatedCylinderEvent hA x)

theorem integral_translatedCylinderIndicator {d : ℕ}
    {E : Finset (CubicEdge d)} {A : Set (EdgeConfiguration d)}
    (hA : DependsOn E A) (p : I) (x : Cubic d) :
    ∫ ω, translatedCylinderIndicator A x ω ∂bernoulliBondMeasure d p =
      (bernoulliBondMeasure d p).real A := by
  exact integral_translatedCylinderIndicator_of_measurable hA.measurableSet p x

theorem integral_translatedCylinderAverage_of_measurable {d : ℕ}
    {A : Set (EdgeConfiguration d)} (hA : MeasurableSet A) (p : I)
    (s : Finset (Cubic d)) (hs : s.Nonempty) :
    ∫ ω, (∑ x ∈ s, translatedCylinderIndicator A x ω) / (s.card : ℝ)
        ∂bernoulliBondMeasure d p =
      (bernoulliBondMeasure d p).real A := by
  rw [integral_div, integral_finsetSum s (fun x _hx ↦
    (memLp_translatedCylinderIndicator_of_measurable hA p x).integrable one_le_two)]
  simp_rw [integral_translatedCylinderIndicator_of_measurable hA p]
  rw [Finset.sum_const, nsmul_eq_mul]
  field_simp [show (s.card : ℝ) ≠ 0 by exact_mod_cast (Finset.card_pos.mpr hs).ne']

theorem covariance_translatedCylinderIndicator_le_one {d : ℕ}
    {E : Finset (CubicEdge d)} {A : Set (EdgeConfiguration d)}
    (hA : DependsOn E A) (p : I) (x y : Cubic d) :
    cov[translatedCylinderIndicator A x, translatedCylinderIndicator A y;
        bernoulliBondMeasure d p] ≤ 1 :=
  covariance_eventIndicator_le_one
    (measurableSet_translatedCylinderEvent hA x)
    (measurableSet_translatedCylinderEvent hA y)

theorem covariance_translatedCylinderIndicator_eq_zero_of_far {d : ℕ}
    {E : Finset (CubicEdge d)} {A : Set (EdgeConfiguration d)}
    (hA : DependsOn E A) (p : I) {x y : Cubic d}
    (hxy : 2 * cubicEdgeSetRadius E < cubicLInfDist x y) :
    cov[translatedCylinderIndicator A x, translatedCylinderIndicator A y;
        bernoulliBondMeasure d p] = 0 := by
  let S := E.image (cubicTranslationIso cubicOrigin x).mapEdgeSet
  let T := E.image (cubicTranslationIso cubicOrigin y).mapEdgeSet
  have hST : Disjoint (S : Set (CubicEdge d)) (T : Set (CubicEdge d)) := by
    exact_mod_cast disjoint_cubicTranslation_image_edgeSets_of_far E hxy
  have hindep := indep_generateFrom_coordinateEvents p hST
  have hAx : MeasurableSet[MeasurableSpace.generateFrom (coordinateEvents (S : Set _))]
      (translatedCylinderEvent x A) :=
    (dependsOn_translatedCylinderEvent hA x).measurableSet_generateFrom_coordinateEvents
      (by exact_mod_cast (show S ⊆ S from Finset.Subset.rfl))
  have hAy : MeasurableSet[MeasurableSpace.generateFrom (coordinateEvents (T : Set _))]
      (translatedCylinderEvent y A) :=
    (dependsOn_translatedCylinderEvent hA y).measurableSet_generateFrom_coordinateEvents
      (by exact_mod_cast (show T ⊆ T from Finset.Subset.rfl))
  have hIndSet := hindep.indepSet_of_measurableSet hAx hAy
  have hxm := measurableSet_translatedCylinderEvent hA x
  have hym := measurableSet_translatedCylinderEvent hA y
  rw [translatedCylinderIndicator, translatedCylinderIndicator,
    covariance_eventIndicator hxm hym]
  have hprod := hIndSet.measure_inter_eq_mul
  have hprodBond :
      (bernoulliBondMeasure d p)
          (translatedCylinderEvent x A ∩ translatedCylinderEvent y A) =
        (bernoulliBondMeasure d p) (translatedCylinderEvent x A) *
          (bernoulliBondMeasure d p) (translatedCylinderEvent y A) := by
    simpa [bernoulliBondMeasure] using hprod
  have hprodReal :
      (bernoulliBondMeasure d p).real
          (translatedCylinderEvent x A ∩ translatedCylinderEvent y A) =
        (bernoulliBondMeasure d p).real (translatedCylinderEvent x A) *
          (bernoulliBondMeasure d p).real (translatedCylinderEvent y A) := by
    simpa [Measure.real, ENNReal.toReal_mul] using congrArg ENNReal.toReal hprodBond
  rw [hprodReal, sub_self]

theorem integral_translatedCylinderAverage {d : ℕ}
    {E : Finset (CubicEdge d)} {A : Set (EdgeConfiguration d)}
    (hA : DependsOn E A) (p : I) (s : Finset (Cubic d)) (hs : s.Nonempty) :
    ∫ ω, (∑ x ∈ s, translatedCylinderIndicator A x ω) / (s.card : ℝ)
        ∂bernoulliBondMeasure d p =
      (bernoulliBondMeasure d p).real A := by
  rw [integral_div, integral_finsetSum s (fun x _hx ↦
    (memLp_translatedCylinderIndicator hA p x).integrable one_le_two)]
  simp_rw [integral_translatedCylinderIndicator hA p]
  rw [Finset.sum_const, nsmul_eq_mul]
  field_simp [show (s.card : ℝ) ≠ 0 by exact_mod_cast (Finset.card_pos.mpr hs).ne']

/-- Variance bound for the average of translates of one finite cylinder over an arbitrary
nonempty finite vertex set. -/
theorem variance_translatedCylinderAverage_le {d : ℕ}
    {E : Finset (CubicEdge d)} {A : Set (EdgeConfiguration d)}
    (hA : DependsOn E A) (p : I) (s : Finset (Cubic d)) (hs : s.Nonempty) :
    Var[fun ω ↦ (∑ x ∈ s, translatedCylinderIndicator A x ω) / (s.card : ℝ);
        bernoulliBondMeasure d p] ≤
      (((2 * (2 * cubicEdgeSetRadius E) + 1) ^ d : ℕ) : ℝ) / s.card := by
  let N : Cubic d → Finset (Cubic d) := fun x ↦
    cubicMetricBox d x (2 * cubicEdgeSetRadius E)
  exact variance_finset_average_le_of_finite_covariance_neighborhood
    (bernoulliBondMeasure d p) s hs (translatedCylinderIndicator A)
    (fun x _hx ↦ memLp_translatedCylinderIndicator hA p x) N
    ((2 * (2 * cubicEdgeSetRadius E) + 1) ^ d)
    (fun x _hx ↦ by
      dsimp [N]
      rw [cubicMetricBox_card])
    (fun x _hx y _hy hyN ↦ by
      apply covariance_translatedCylinderIndicator_eq_zero_of_far hA p
      have hnot : ¬ cubicLInfDist x y ≤ 2 * cubicEdgeSetRadius E := by
        intro hle
        exact hyN (mem_cubicMetricBox_iff_lInfDist_le.mpr hle)
      omega)
    (fun x _hx y _hy ↦ covariance_translatedCylinderIndicator_le_one hA p x y)

/-- Explicit Chebyshev bound, centered at the common cylinder probability rather than at an
unexpanded integral. -/
theorem bernoulliBondMeasure_translatedCylinderAverage_deviation_le {d : ℕ}
    {E : Finset (CubicEdge d)} {A : Set (EdgeConfiguration d)}
    (hA : DependsOn E A) (p : I) (s : Finset (Cubic d)) (hs : s.Nonempty)
    {ε : ℝ} (hε : 0 < ε) :
    (bernoulliBondMeasure d p)
        {ω | ε ≤
          |(∑ x ∈ s, translatedCylinderIndicator A x ω) / (s.card : ℝ) -
            (bernoulliBondMeasure d p).real A|} ≤
      ENNReal.ofReal
        (((((2 * (2 * cubicEdgeSetRadius E) + 1) ^ d : ℕ) : ℝ) / s.card) /
          ε ^ 2) := by
  have h := measure_average_deviation_le_of_finite_covariance_neighborhood
    (bernoulliBondMeasure d p) s hs (translatedCylinderIndicator A)
    (fun x _hx ↦ memLp_translatedCylinderIndicator hA p x)
    (fun x ↦ cubicMetricBox d x (2 * cubicEdgeSetRadius E))
    ((2 * (2 * cubicEdgeSetRadius E) + 1) ^ d)
    (fun x _hx ↦ by simp [cubicMetricBox_card])
    (fun x _hx y _hy hyN ↦ by
      apply covariance_translatedCylinderIndicator_eq_zero_of_far hA p
      have hnot : ¬ cubicLInfDist x y ≤ 2 * cubicEdgeSetRadius E := by
        intro hle
        exact hyN (mem_cubicMetricBox_iff_lInfDist_le.mpr hle)
      omega)
    (fun x _hx y _hy ↦ covariance_translatedCylinderIndicator_le_one hA p x y)
    hε
  rw [integral_translatedCylinderAverage hA p s hs] at h
  exact h

/-- Real-valued form of the preceding Chebyshev estimate. -/
theorem bernoulliBondMeasure_real_translatedCylinderAverage_deviation_le {d : ℕ}
    {E : Finset (CubicEdge d)} {A : Set (EdgeConfiguration d)}
    (hA : DependsOn E A) (p : I) (s : Finset (Cubic d)) (hs : s.Nonempty)
    {ε : ℝ} (hε : 0 < ε) :
    (bernoulliBondMeasure d p).real
        {ω | ε ≤
          |(∑ x ∈ s, translatedCylinderIndicator A x ω) / (s.card : ℝ) -
            (bernoulliBondMeasure d p).real A|} ≤
      (((((2 * (2 * cubicEdgeSetRadius E) + 1) ^ d : ℕ) : ℝ) / s.card) /
        ε ^ 2) := by
  have h := bernoulliBondMeasure_translatedCylinderAverage_deviation_le
    hA p s hs hε
  have hnonneg : 0 ≤
      (((((2 * (2 * cubicEdgeSetRadius E) + 1) ^ d : ℕ) : ℝ) / s.card) /
        ε ^ 2) := by positivity
  have hreal :
      ((bernoulliBondMeasure d p)
        {ω | ε ≤
          |(∑ x ∈ s, translatedCylinderIndicator A x ω) / (s.card : ℝ) -
            (bernoulliBondMeasure d p).real A|}).toReal ≤
        (ENNReal.ofReal
          (((((2 * (2 * cubicEdgeSetRadius E) + 1) ^ d : ℕ) : ℝ) / s.card) /
            ε ^ 2)).toReal :=
    ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  simpa only [Measure.real, ENNReal.toReal_ofReal hnonneg] using hreal

end Percolation
