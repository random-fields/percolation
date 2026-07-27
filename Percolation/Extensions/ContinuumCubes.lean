import Percolation.Bernoulli.Inhomogeneous
import Percolation.Core.Cubic
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.Independence.InfinitePi

/-!
# Poisson cube discretization of the Boolean model

This is the exact product-law layer behind Grimmett (12.37)--(12.38).  Vertices are integer
indices for the cubes of side `1 / n`; storing indices rather than scaled centres avoids quotient
and floating-point encodings.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal unitInterval

/-- Poisson intensity in one `d`-dimensional cube of side `1/n`. -/
noncomputable def continuumCubeRate (d : ℕ) (intensity : ℝ≥0) (n : ℕ) : ℝ≥0 :=
  intensity / (n : ℝ≥0) ^ d

/-- Bernoulli density obtained by declaring a Poisson cube open when its count is nonzero. -/
noncomputable def continuumCubeDensity (d : ℕ) (intensity : ℝ≥0) (n : ℕ) : I :=
  ⟨1 - Real.exp (-(continuumCubeRate d intensity n : ℝ)), by
    constructor
    · have hr : 0 ≤ (continuumCubeRate d intensity n : ℝ) := by positivity
      linarith [Real.exp_le_one_iff.mpr (neg_nonpos.mpr hr)]
    · linarith [Real.exp_nonneg (-(continuumCubeRate d intensity n : ℝ))]⟩

@[simp]
theorem continuumCubeDensity_coe (d : ℕ) (intensity : ℝ≥0) (n : ℕ) :
    (continuumCubeDensity d intensity n : ℝ) =
      1 - Real.exp (-(continuumCubeRate d intensity n : ℝ)) :=
  rfl

/-- Thresholding one Poisson count at zero gives the Bernoulli law with the exact density
`1 - exp (-r)`. -/
theorem poissonMeasure_map_ne_zero (r : ℝ≥0) :
    (poissonMeasure r).map (fun k : ℕ ↦ k ≠ 0) =
      bernoulliPropMeasure
        ⟨1 - Real.exp (-(r : ℝ)), by
          constructor
          · have hr : (0 : ℝ) ≤ r := r.2
            linarith [Real.exp_le_one_iff.mpr (neg_nonpos.mpr hr)]
          · linarith [Real.exp_nonneg (-(r : ℝ))]⟩ := by
  rw [Measure.ext_iff_singleton]
  intro b
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton b)]
  by_cases hb : b
  · have hb' : b = True := propext (iff_true_intro hb)
    subst b
    have hpre : (fun k : ℕ ↦ k ≠ 0) ⁻¹' ({True} : Set Prop) = ({0} : Set ℕ)ᶜ := by
      ext k
      simp
    rw [hpre, bernoulliPropMeasure]
    have hzero := poissonMeasure_real_singleton r 0
    have hcompl := measureReal_compl (μ := poissonMeasure r) (measurableSet_singleton 0)
    rw [probReal_univ, hzero] at hcompl
    rw [← ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)]
    change (poissonMeasure r).real ({0}ᶜ : Set ℕ) = _
    simpa using hcompl
  · have hb' : b = False := propext (iff_false_intro hb)
    subst b
    have hpre : (fun k : ℕ ↦ k ≠ 0) ⁻¹' ({False} : Set Prop) = {0} := by
      ext k
      simp
    rw [hpre, poissonMeasure_singleton, bernoulliPropMeasure]
    simp
    rw [← ENNReal.toReal_eq_toReal_iff' ENNReal.ofReal_ne_top ENNReal.coe_ne_top]
    simp
    positivity

/-- One Poisson count for each cube in the `1/n` partition. -/
abbrev PoissonCubeConfiguration (d : ℕ) := Cubic d → ℕ

/-- Independent cube counts of rate `λ n⁻ᵈ`. -/
noncomputable def poissonCubeMeasure (d : ℕ) (intensity : ℝ≥0) (n : ℕ) :
    Measure (PoissonCubeConfiguration d) :=
  Measure.infinitePi fun _ : Cubic d ↦ poissonMeasure (continuumCubeRate d intensity n)

instance poissonCubeMeasure_isProbabilityMeasure (d : ℕ) (intensity : ℝ≥0) (n : ℕ) :
    IsProbabilityMeasure (poissonCubeMeasure d intensity n) := by
  unfold poissonCubeMeasure
  infer_instance

/-- A discretization vertex is open exactly when its cube contains at least one Poisson point. -/
def continuumCubeOccupiedEvent {d : ℕ} (x : Cubic d) :
    Set (PoissonCubeConfiguration d) :=
  {N | N x ≠ 0}

theorem measurableSet_continuumCubeOccupiedEvent {d : ℕ} (x : Cubic d) :
    MeasurableSet (continuumCubeOccupiedEvent x) := by
  exact (measurable_pi_apply x) (measurableSet_singleton 0) |>.compl

theorem poissonCubeMeasure_real_emptyCube {d : ℕ} (intensity : ℝ≥0) (n : ℕ)
    (x : Cubic d) :
    (poissonCubeMeasure d intensity n).real
        (continuumCubeOccupiedEvent x)ᶜ =
      Real.exp (-(continuumCubeRate d intensity n : ℝ)) := by
  have hmap := Measure.infinitePi_map_eval
    (fun _ : Cubic d ↦ poissonMeasure (continuumCubeRate d intensity n)) x
  have hsingleton := congrArg (fun μ : Measure ℕ ↦ μ.real ({0} : Set ℕ)) hmap
  change ENNReal.toReal
      ((Measure.map (fun N : PoissonCubeConfiguration d ↦ N x)
        (Measure.infinitePi fun _ : Cubic d ↦
          poissonMeasure (continuumCubeRate d intensity n))) {0}) =
      ENNReal.toReal (poissonMeasure (continuumCubeRate d intensity n) {0}) at hsingleton
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton 0)] at hsingleton
  have hpre : (fun N : PoissonCubeConfiguration d ↦ N x) ⁻¹' ({0} : Set ℕ) =
      (continuumCubeOccupiedEvent x)ᶜ := by
    ext N
    simp [continuumCubeOccupiedEvent]
  rw [hpre] at hsingleton
  change ENNReal.toReal
      ((Measure.infinitePi fun _ : Cubic d ↦
        poissonMeasure (continuumCubeRate d intensity n))
        (continuumCubeOccupiedEvent x)ᶜ) = _
  calc
    _ = ENNReal.toReal
        (poissonMeasure (continuumCubeRate d intensity n) {0}) := hsingleton
    _ = Real.exp (-(continuumCubeRate d intensity n : ℝ)) := by
      simpa [Measure.real] using
        poissonMeasure_real_singleton (continuumCubeRate d intensity n) 0

/-- Exact cube-occupation probability (12.38): `Pₙ(λ)=1-exp(-λ n⁻ᵈ)`. -/
theorem continuumCubeOccupied_probability (d : ℕ) (intensity : ℝ≥0) (n : ℕ)
    (x : Cubic d) :
    (poissonCubeMeasure d intensity n).real (continuumCubeOccupiedEvent x) =
      1 - Real.exp (-(continuumCubeRate d intensity n : ℝ)) := by
  have hcompl := measureReal_compl
    (μ := poissonCubeMeasure d intensity n)
    (measurableSet_continuumCubeOccupiedEvent x)
  rw [probReal_univ, poissonCubeMeasure_real_emptyCube] at hcompl
  linarith

/-- The cube-count coordinate process is independent. -/
theorem poissonCubeCounts_iIndep (d : ℕ) (intensity : ℝ≥0) (n : ℕ) :
    iIndepFun (fun x : Cubic d ↦
      (fun N : PoissonCubeConfiguration d ↦ N x)) (poissonCubeMeasure d intensity n) := by
  unfold poissonCubeMeasure
  exact iIndepFun_infinitePi (X := fun (_ : Cubic d) ↦ (id : ℕ → ℕ))
    fun _ ↦ measurable_id

/-- The occupied-site field obtained by thresholding the independent cube counts. -/
def continuumOccupiedSites {d : ℕ} (N : PoissonCubeConfiguration d) : Set (Cubic d) :=
  {x | N x ≠ 0}

theorem measurable_continuumOccupiedSites {d : ℕ} :
    Measurable (continuumOccupiedSites : PoissonCubeConfiguration d → Set (Cubic d)) := by
  change Measurable ((fun P : Cubic d → Prop ↦ {x | P x}) ∘
    fun (N : PoissonCubeConfiguration d) (x : Cubic d) ↦ (N x ≠ 0 : Prop))
  apply Measurable.comp (by fun_prop)
  exact measurable_pi_lambda _ fun x ↦
    ((measurableSet_singleton 0).preimage (measurable_pi_apply x)).compl.mem

/-- The thresholded cube-count field is *exactly* homogeneous iid site percolation at the
density in (12.38), not merely a field with the correct one-site marginals. -/
theorem poissonCubeMeasure_map_continuumOccupiedSites
    (d : ℕ) (intensity : ℝ≥0) (n : ℕ) :
    (poissonCubeMeasure d intensity n).map continuumOccupiedSites =
      setBer((Set.univ : Set (Cubic d)), continuumCubeDensity d intensity n) := by
  have hcomp :
      (continuumOccupiedSites : PoissonCubeConfiguration d → Set (Cubic d)) =
        (fun P : Cubic d → Prop ↦ {x | P x}) ∘
          (fun N : PoissonCubeConfiguration d ↦ fun x ↦ N x ≠ 0) := rfl
  rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop), poissonCubeMeasure]
  have hpi :
      (Measure.infinitePi fun _ : Cubic d ↦
        poissonMeasure (continuumCubeRate d intensity n)).map
          (fun N x ↦ N x ≠ 0) =
        Measure.infinitePi fun _ : Cubic d ↦
          (poissonMeasure (continuumCubeRate d intensity n)).map (fun k : ℕ ↦ k ≠ 0) := by
    exact Measure.infinitePi_map_pi
      (μ := fun _ : Cubic d ↦ poissonMeasure (continuumCubeRate d intensity n))
      (f := fun _ : Cubic d ↦ fun k : ℕ ↦ k ≠ 0)
      (fun _ ↦ measurable_of_countable _)
  rw [hpi, setBernoulli_eq_map]
  congrm Measure.map _ (Measure.infinitePi fun x ↦ ?_)
  exact poissonMeasure_map_ne_zero (continuumCubeRate d intensity n)

end Percolation
