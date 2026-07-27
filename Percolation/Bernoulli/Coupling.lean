import Percolation.Bernoulli.FiniteCube

/-!
# The uniform coupling and monotonicity in the density (Theorem 2.1)

Source: Grimmett, *Percolation* (2nd ed., 1999), §2.1, Theorem (2.1), pp. 32–33
(source id `grimmett-percolation-1999`).

Grimmett's coupling: sample i.i.d. uniforms `(X(e))` on `[0,1]` and declare `e` open at
density `p` when `X(e) < p`, so that the configurations `η_p` are simultaneously realized
for all densities and increase with `p`. This file constructs that coupling —

* `Percolation.couplingMeasure` — the i.i.d. uniform product measure on `ι → ℝ`;
* `Percolation.thresholdConfiguration` — the configuration `η_p = {e | X e < p}`;
* `Percolation.couplingMeasure_map_thresholdConfiguration` — the marginal law of `η_p` is
  the Bernoulli product measure `setBer(Set.univ, p)` —

and derives **Theorem (2.1)**:

* `Percolation.IsIncreasingEvent.setBernoulli_real_mono` — `P_{p₁}(A) ≤ P_{p₂}(A)` for
  increasing measurable events and `p₁ ≤ p₂` (equation (2.3));
* `Percolation.IsIncreasingRandomVariable.setBernoulli_integral_mono` — the corresponding
  statement (2.2) for integrable increasing random variables;
* `Percolation.theta_mono` — the percolation probability `θ(p)` is non-decreasing in `p`,
  Grimmett's motivating application.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped ENNReal unitInterval

variable {ι : Type*}

/-- Independent uniform `[0,1]` variables, one per coordinate: the common source of
randomness for Grimmett's simultaneous coupling of all densities. -/
noncomputable def couplingMeasure (ι : Type*) : Measure (ι → ℝ) :=
  Measure.infinitePi fun _ => volume.restrict (Set.Icc (0 : ℝ) 1)

instance : IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  constructor
  rw [Measure.restrict_apply_univ, Real.volume_Icc]
  norm_num

instance : IsProbabilityMeasure (couplingMeasure ι) := by
  rw [couplingMeasure]
  infer_instance

/-- Grimmett's threshold configuration `η_p`: the coordinates whose uniform variable falls
below the density `p`. -/
def thresholdConfiguration (p : I) (X : ι → ℝ) : Set ι :=
  {e | X e < ↑p}

theorem thresholdConfiguration_mono {p q : I} (hpq : p ≤ q) (X : ι → ℝ) :
    thresholdConfiguration p X ⊆ thresholdConfiguration q X := fun e he =>
  show X e < (q : ℝ) from lt_of_lt_of_le he (Subtype.coe_le_coe.mpr hpq)

/-- The threshold indicator of a single coordinate is measurable into `Prop`. -/
theorem measurable_lt_prop (c : ℝ) : Measurable fun x : ℝ => (x < c : Prop) := by
  intro s _
  classical
  have hpre : (fun x : ℝ => (x < c : Prop)) ⁻¹' s =
      (if True ∈ s then Set.Iio c else ∅) ∪ (if False ∈ s then Set.Ici c else ∅) := by
    ext x
    by_cases hx : x < c
    · rw [Set.mem_preimage, eq_true hx]
      by_cases hT : True ∈ s <;> by_cases hF : False ∈ s <;> simp [hT, hF, hx]
    · rw [Set.mem_preimage, eq_false hx]
      by_cases hT : True ∈ s <;> by_cases hF : False ∈ s <;>
        simp [hT, hF, hx, not_lt.mp hx]
  rw [hpre]
  refine MeasurableSet.union ?_ ?_ <;> split <;>
    simp [measurableSet_Iio, measurableSet_Ici]

theorem measurable_thresholdConfiguration (p : I) :
    Measurable (thresholdConfiguration p : (ι → ℝ) → Set ι) := by
  change Measurable
    ((fun P : ι → Prop => {i | P i}) ∘ fun (X : ι → ℝ) (e : ι) => (X e < (p : ℝ) : Prop))
  refine Measurable.comp (by fun_prop) ?_
  exact measurable_pi_lambda _ fun e => (measurable_lt_prop _).comp (measurable_pi_apply e)

/-- The law of one thresholded uniform coordinate is the two-point Bernoulli measure. -/
theorem volume_restrict_map_lt_prop (p : I) :
    (volume.restrict (Set.Icc (0 : ℝ) 1)).map (fun x => (x < (p : ℝ) : Prop)) =
      unitInterval.toNNReal p • Measure.dirac True +
        unitInterval.toNNReal (σ p) • Measure.dirac False := by
  classical
  ext s hs
  rw [Measure.map_apply (measurable_lt_prop _) hs, Measure.add_apply,
    Measure.smul_apply, Measure.smul_apply, Measure.dirac_apply' _ hs,
    Measure.dirac_apply' _ hs]
  have hpre : (fun x : ℝ => (x < (p : ℝ) : Prop)) ⁻¹' s =
      (if True ∈ s then Set.Iio (p : ℝ) else ∅) ∪
        (if False ∈ s then Set.Ici (p : ℝ) else ∅) := by
    ext x
    by_cases hx : x < (p : ℝ)
    · rw [Set.mem_preimage, eq_true hx]
      by_cases hT : True ∈ s <;> by_cases hF : False ∈ s <;> simp [hT, hF, hx]
    · rw [Set.mem_preimage, eq_false hx]
      by_cases hT : True ∈ s <;> by_cases hF : False ∈ s <;>
        simp [hT, hF, hx, not_lt.mp hx]
  rw [hpre]
  have hIio : Set.Iio (p : ℝ) ∩ Set.Icc (0 : ℝ) 1 = Set.Ico (0 : ℝ) (p : ℝ) := by
    ext x
    constructor
    · rintro ⟨hxp, hx0, _⟩
      exact ⟨hx0, hxp⟩
    · rintro ⟨hx0, hxp⟩
      exact ⟨hxp, hx0, le_trans (le_of_lt hxp) p.2.2⟩
  have hIci : Set.Ici (p : ℝ) ∩ Set.Icc (0 : ℝ) 1 = Set.Icc (p : ℝ) 1 := by
    ext x
    constructor
    · rintro ⟨hxp, _, hx1⟩
      exact ⟨hxp, hx1⟩
    · rintro ⟨hxp, hx1⟩
      exact ⟨hxp, le_trans p.2.1 hxp, hx1⟩
  by_cases hT : True ∈ s <;> by_cases hF : False ∈ s
  · rw [if_pos hT, if_pos hF, Set.indicator_of_mem hT, Set.indicator_of_mem hF]
    have hunion : Set.Iio (p : ℝ) ∪ Set.Ici (p : ℝ) = Set.univ := Set.Iio_union_Ici
    rw [hunion, Measure.restrict_apply_univ, Real.volume_Icc]
    simp only [ENNReal.smul_def, smul_eq_mul, Pi.one_apply, mul_one]
    rw [← ENNReal.coe_add, unitInterval.toNNReal_add_toNNReal_symm]
    norm_num
  · rw [if_pos hT, if_neg hF, Set.union_empty, Set.indicator_of_mem hT,
      Set.indicator_of_notMem hF,
      Measure.restrict_apply measurableSet_Iio, hIio, Real.volume_Ico]
    simp only [ENNReal.smul_def, smul_eq_mul, Pi.one_apply, mul_one, mul_zero, add_zero,
      sub_zero]
    rw [ENNReal.ofReal_eq_coe_nnreal p.2.1]
    rfl
  · rw [if_neg hT, if_pos hF, Set.empty_union, Set.indicator_of_notMem hT,
      Set.indicator_of_mem hF,
      Measure.restrict_apply measurableSet_Ici, hIci, Real.volume_Icc]
    simp only [ENNReal.smul_def, smul_eq_mul, Pi.one_apply, mul_one, mul_zero, zero_add]
    have h1p : (0 : ℝ) ≤ 1 - (p : ℝ) := by
      have := p.2.2
      linarith
    rw [ENNReal.ofReal_eq_coe_nnreal h1p]
    exact congrArg _ (NNReal.coe_injective (by simp))
  · rw [if_neg hT, if_neg hF, Set.union_empty, Set.indicator_of_notMem hT,
      Set.indicator_of_notMem hF]
    simp

/-- **The marginal law of the threshold configuration** is the Bernoulli product measure:
Grimmett's coupling realizes `P_p` for every `p` on one probability space (p. 33). -/
theorem couplingMeasure_map_thresholdConfiguration (p : I) :
    (couplingMeasure ι).map (thresholdConfiguration p) =
      setBer((Set.univ : Set ι), p) := by
  have hcomp : (thresholdConfiguration p : (ι → ℝ) → Set ι) =
      (fun P : ι → Prop => {i | P i}) ∘ fun X (e : ι) => (X e < (p : ℝ) : Prop) := rfl
  have hcoord : Measurable fun (X : ι → ℝ) (e : ι) => (X e < (p : ℝ) : Prop) :=
    measurable_pi_lambda _ fun e => (measurable_lt_prop _).comp (measurable_pi_apply e)
  rw [hcomp, ← Measure.map_map (by fun_prop) hcoord, couplingMeasure,
    Measure.infinitePi_map_pi _ fun _ => measurable_lt_prop _,
    ProbabilityTheory.setBernoulli_eq_map]
  congr 1
  refine congrArg _ (funext fun i => ?_)
  rw [volume_restrict_map_lt_prop]
  have : (i ∈ (Set.univ : Set ι)) = True := eq_true (Set.mem_univ i)
  rw [this]

/-! ### Theorem 2.1 -/

/-- **Theorem (2.1), event form (2.3)**: for an increasing measurable event, the Bernoulli
probability is non-decreasing in the density. -/
theorem IsIncreasingEvent.setBernoulli_real_mono {A : Set (Set ι)}
    (hA : IsIncreasingEvent A) (hAm : MeasurableSet A) {p q : I} (hpq : p ≤ q) :
    setBer((Set.univ : Set ι), p).real A ≤ setBer((Set.univ : Set ι), q).real A := by
  rw [← couplingMeasure_map_thresholdConfiguration (ι := ι) p,
    ← couplingMeasure_map_thresholdConfiguration (ι := ι) q,
    measureReal_def, measureReal_def,
    Measure.map_apply (measurable_thresholdConfiguration p) hAm,
    Measure.map_apply (measurable_thresholdConfiguration q) hAm]
  refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono fun X hX => ?_)
  exact hA (thresholdConfiguration_mono hpq X) hX

/-- **Theorem (2.1), random-variable form (2.2)**: for an increasing measurable integrable
random variable, the Bernoulli expectation is non-decreasing in the density. -/
theorem IsIncreasingRandomVariable.setBernoulli_integral_mono {N : Set ι → ℝ}
    (hN : IsIncreasingRandomVariable N) (hNm : Measurable N) {p q : I} (hpq : p ≤ q)
    (hintp : Integrable N (setBer((Set.univ : Set ι), p)))
    (hintq : Integrable N (setBer((Set.univ : Set ι), q))) :
    ∫ ω, N ω ∂ setBer((Set.univ : Set ι), p) ≤
      ∫ ω, N ω ∂ setBer((Set.univ : Set ι), q) := by
  rw [← couplingMeasure_map_thresholdConfiguration (ι := ι) p] at hintp ⊢
  rw [← couplingMeasure_map_thresholdConfiguration (ι := ι) q] at hintq ⊢
  rw [integral_map (measurable_thresholdConfiguration p).aemeasurable
      hNm.aestronglyMeasurable,
    integral_map (measurable_thresholdConfiguration q).aemeasurable
      hNm.aestronglyMeasurable]
  refine integral_mono ?_ ?_ fun X => hN (thresholdConfiguration_mono hpq X)
  · exact (integrable_map_measure hNm.aestronglyMeasurable
      (measurable_thresholdConfiguration p).aemeasurable).mp hintp
  · exact (integrable_map_measure hNm.aestronglyMeasurable
      (measurable_thresholdConfiguration q).aemeasurable).mp hintq

/-! ### The motivating application: monotonicity of the percolation probability -/

/-- The infinite-origin-cluster event is increasing: opening more edges can only grow the
open cluster. -/
theorem isIncreasingEvent_hasInfiniteOpenCluster (d : ℕ) :
    IsIncreasingEvent {ω : EdgeConfiguration d | hasInfiniteOpenCluster d ω} := by
  intro ω η hωη hω
  refine Set.Infinite.mono ?_ hω
  rintro y ⟨w, hw⟩
  exact ⟨w, fun e he => hωη (hw e he)⟩

/-- **Monotonicity of the percolation probability** (Grimmett p. 32: `θ(p)` is
non-decreasing, the opening application of Theorem (2.1)). -/
theorem theta_mono (d : ℕ) {p q : I} (hpq : p ≤ q) : theta d p ≤ theta d q := by
  have h := (isIncreasingEvent_hasInfiniteOpenCluster d).setBernoulli_real_mono
    (measurableSet_hasInfiniteOpenCluster d) hpq
  simpa [theta, bernoulliBondMeasure] using h

end Percolation
