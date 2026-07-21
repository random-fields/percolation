import Percolation.Extensions.ContinuumCentralProbability
import Mathlib.MeasureTheory.Group.Convolution

/-!
# Monotonicity of the marked Boolean model

For `lambda ≤ mu`, write a Poisson(`mu`) cube count as the sum of independent
Poisson(`lambda`) and Poisson(`mu-lambda`) counts, while using one common iid mark stream.
The lower active point set is then literally contained in the upper active point set.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory Set SimpleGraph
open scoped ENNReal MeasureTheory NNReal unitInterval

/-- One coordinate of the monotone count-and-mark coupling. -/
abbrev ContinuumMonotoneCubeSample (d : ℕ) := (ℕ × ℕ) × ContinuumMarkStream d

/-- Independent base count, increment count, and common marks. -/
noncomputable def continuumMonotoneCubeMeasure
    (d : ℕ) (base increment : ℝ≥0) : Measure (ContinuumMonotoneCubeSample d) :=
  ((poissonMeasure base).prod (poissonMeasure increment)).prod
    (continuumMarkStreamMeasure d)

noncomputable instance continuumMonotoneCubeMeasure.isProbabilityMeasure
    (d : ℕ) (base increment : ℝ≥0) :
    IsProbabilityMeasure (continuumMonotoneCubeMeasure d base increment) := by
  unfold continuumMonotoneCubeMeasure
  infer_instance

/-- Lower marked cube in the monotone coupling. -/
def continuumMonotoneLowerCube {d : ℕ}
    (z : ContinuumMonotoneCubeSample d) : ContinuumCubeSample d :=
  (z.1.1, z.2)

/-- Upper marked cube, obtained by activating the increment count as well. -/
def continuumMonotoneUpperCube {d : ℕ}
    (z : ContinuumMonotoneCubeSample d) : ContinuumCubeSample d :=
  (z.1.1 + z.1.2, z.2)

theorem measurable_continuumMonotoneLowerCube {d : ℕ} :
    Measurable (continuumMonotoneLowerCube :
      ContinuumMonotoneCubeSample d → ContinuumCubeSample d) := by
  unfold continuumMonotoneLowerCube
  exact (measurable_fst.comp measurable_fst).prodMk measurable_snd

theorem measurable_continuumMonotoneUpperCube {d : ℕ} :
    Measurable (continuumMonotoneUpperCube :
      ContinuumMonotoneCubeSample d → ContinuumCubeSample d) := by
  unfold continuumMonotoneUpperCube
  exact ((measurable_fst.comp measurable_fst).add
    (measurable_snd.comp measurable_fst)).prodMk measurable_snd

/-- The lower cube marginal has the base intensity. -/
theorem continuumMonotoneCubeMeasure_map_lower
    (d : ℕ) (base increment : ℝ≥0) :
    (continuumMonotoneCubeMeasure d base increment).map continuumMonotoneLowerCube =
      continuumCubeSampleMeasure d base := by
  unfold continuumMonotoneCubeMeasure continuumMonotoneLowerCube
    continuumCubeSampleMeasure
  change Measure.map (Prod.map Prod.fst id)
      (((poissonMeasure base).prod (poissonMeasure increment)).prod
        (continuumMarkStreamMeasure d)) = _
  rw [← Measure.map_prod_map _ _ measurable_fst measurable_id]
  simp

/-- The upper cube marginal has the summed intensity. -/
theorem continuumMonotoneCubeMeasure_map_upper
    (d : ℕ) (base increment : ℝ≥0) :
    (continuumMonotoneCubeMeasure d base increment).map continuumMonotoneUpperCube =
      continuumCubeSampleMeasure d (base + increment) := by
  unfold continuumMonotoneCubeMeasure continuumMonotoneUpperCube
    continuumCubeSampleMeasure
  change Measure.map (Prod.map (fun z : ℕ × ℕ ↦ z.1 + z.2) id)
      (((poissonMeasure base).prod (poissonMeasure increment)).prod
        (continuumMarkStreamMeasure d)) = _
  rw [← Measure.map_prod_map _ _ (by fun_prop) measurable_id]
  rw [Measure.map_id]
  change (poissonMeasure base ∗ poissonMeasure increment).prod
      (continuumMarkStreamMeasure d) = _
  rw [poissonMeasure_conv_poissonMeasure]

/-- Product coupling over all integer cubes. -/
abbrev ContinuumMonotoneConfiguration (d : ℕ) :=
  Cubic d → ContinuumMonotoneCubeSample d

/-- Independent copies of the one-cube monotone coupling. -/
noncomputable def continuumMonotoneMeasure
    (d : ℕ) (base increment : ℝ≥0) :
    Measure (ContinuumMonotoneConfiguration d) :=
  Measure.infinitePi fun _ : Cubic d ↦
    continuumMonotoneCubeMeasure d base increment

noncomputable instance continuumMonotoneMeasure.isProbabilityMeasure
    (d : ℕ) (base increment : ℝ≥0) :
    IsProbabilityMeasure (continuumMonotoneMeasure d base increment) := by
  unfold continuumMonotoneMeasure
  infer_instance

/-- Lower marked configuration extracted from the product coupling. -/
def continuumMonotoneLowerConfiguration {d : ℕ}
    (Z : ContinuumMonotoneConfiguration d) : ContinuumPoissonConfiguration d :=
  fun x ↦ continuumMonotoneLowerCube (Z x)

/-- Upper marked configuration extracted from the product coupling. -/
def continuumMonotoneUpperConfiguration {d : ℕ}
    (Z : ContinuumMonotoneConfiguration d) : ContinuumPoissonConfiguration d :=
  fun x ↦ continuumMonotoneUpperCube (Z x)

theorem measurable_continuumMonotoneLowerConfiguration {d : ℕ} :
    Measurable (continuumMonotoneLowerConfiguration :
      ContinuumMonotoneConfiguration d → ContinuumPoissonConfiguration d) := by
  exact measurable_pi_lambda _ fun x ↦
    measurable_continuumMonotoneLowerCube.comp (measurable_pi_apply x)

theorem measurable_continuumMonotoneUpperConfiguration {d : ℕ} :
    Measurable (continuumMonotoneUpperConfiguration :
      ContinuumMonotoneConfiguration d → ContinuumPoissonConfiguration d) := by
  exact measurable_pi_lambda _ fun x ↦
    measurable_continuumMonotoneUpperCube.comp (measurable_pi_apply x)

/-- The lower full-configuration marginal is the marked Poisson law at the base intensity. -/
theorem continuumMonotoneMeasure_map_lower
    (d : ℕ) (base increment : ℝ≥0) :
    (continuumMonotoneMeasure d base increment).map
        continuumMonotoneLowerConfiguration =
      continuumPoissonMeasure d base := by
  unfold continuumMonotoneMeasure continuumMonotoneLowerConfiguration
    continuumPoissonMeasure
  rw [Measure.infinitePi_map_pi]
  · congrm Measure.infinitePi fun x ↦ ?_
    exact continuumMonotoneCubeMeasure_map_lower d base increment
  · intro x
    exact measurable_continuumMonotoneLowerCube

/-- The upper full-configuration marginal is the marked Poisson law at the summed intensity. -/
theorem continuumMonotoneMeasure_map_upper
    (d : ℕ) (base increment : ℝ≥0) :
    (continuumMonotoneMeasure d base increment).map
        continuumMonotoneUpperConfiguration =
      continuumPoissonMeasure d (base + increment) := by
  unfold continuumMonotoneMeasure continuumMonotoneUpperConfiguration
    continuumPoissonMeasure
  rw [Measure.infinitePi_map_pi]
  · congrm Measure.infinitePi fun x ↦ ?_
    exact continuumMonotoneCubeMeasure_map_upper d base increment
  · intro x
    exact measurable_continuumMonotoneUpperCube

/-- Every point active in the lower realization is active in the upper realization. -/
theorem continuumMonotone_pointActive_imp {d : ℕ}
    (Z : ContinuumMonotoneConfiguration d) (a : Cubic d × ℕ)
    (ha : continuumPoissonPointActive
      (continuumMonotoneLowerConfiguration Z) a) :
    continuumPoissonPointActive
      (continuumMonotoneUpperConfiguration Z) a := by
  change a.2 < (Z a.1).1.1 at ha
  change a.2 < (Z a.1).1.1 + (Z a.1).1.2
  omega

/-- The common mark stream gives identical spatial locations to lower and upper potential
points. -/
theorem continuumMonotone_point_eq {d : ℕ}
    (Z : ContinuumMonotoneConfiguration d) (a : Cubic d × ℕ) :
    continuumPoissonPoint (continuumMonotoneLowerConfiguration Z) a =
      continuumPoissonPoint (continuumMonotoneUpperConfiguration Z) a := by
  rfl

/-- The identity on potential indices is a graph homomorphism from the lower Boolean graph to
the upper Boolean graph. -/
noncomputable def continuumMonotoneGraphHom {d : ℕ}
    (Z : ContinuumMonotoneConfiguration d) :
    continuumPoissonAmbientGraph (continuumMonotoneLowerConfiguration Z) →g
      continuumPoissonAmbientGraph (continuumMonotoneUpperConfiguration Z) where
  toFun := id
  map_rel' := by
    intro a b hab
    rw [continuumPoissonAmbientGraph_adj] at hab ⊢
    refine ⟨hab.1, continuumMonotone_pointActive_imp Z a hab.2.1,
      continuumMonotone_pointActive_imp Z b hab.2.2.1, ?_⟩
    simpa only [continuumMonotone_point_eq] using hab.2.2.2

/-- Percolation is preserved by activating the independent Poisson increment. -/
theorem continuumPoissonPercolates_monotoneCoupling {d : ℕ}
    (Z : ContinuumMonotoneConfiguration d)
    (hZ : continuumPoissonPercolates
      (continuumMonotoneLowerConfiguration Z)) :
    continuumPoissonPercolates
      (continuumMonotoneUpperConfiguration Z) := by
  obtain ⟨a, ha⟩ := hZ
  refine ⟨a, ha.mono ?_⟩
  intro b hb
  simpa using hb.map (continuumMonotoneGraphHom Z)

/-- The source event at the spatial origin is preserved by the monotone coupling. -/
theorem continuumOriginPercolates_monotoneCoupling {d : ℕ}
    (Z : ContinuumMonotoneConfiguration d)
    (hZ : continuumMonotoneLowerConfiguration Z ∈
      continuumOriginPercolatesEvent d) :
    continuumMonotoneUpperConfiguration Z ∈
      continuumOriginPercolatesEvent d := by
  obtain ⟨a, haCover, haActive, haInfinite⟩ := hZ
  refine ⟨a, ?_, continuumMonotone_pointActive_imp Z a haActive,
    haInfinite.mono ?_⟩
  · refine ⟨continuumMonotone_pointActive_imp Z a haCover.1, ?_⟩
    simpa only [continuumMonotone_point_eq] using haCover.2
  · intro b hb
    simpa using hb.map (continuumMonotoneGraphHom Z)

/-- Adding an independent nonnegative intensity can only increase Boolean percolation. -/
theorem continuumTheta_le_add (d : ℕ) (base increment : ℝ≥0) :
    continuumTheta d base ≤ continuumTheta d (base + increment) := by
  unfold continuumTheta
  rw [← continuumMonotoneMeasure_map_lower d base increment,
    ← continuumMonotoneMeasure_map_upper d base increment]
  rw [Measure.real, Measure.real,
    Measure.map_apply measurable_continuumMonotoneLowerConfiguration
      (measurableSet_continuumOriginPercolatesEvent d),
    Measure.map_apply measurable_continuumMonotoneUpperConfiguration
      (measurableSet_continuumOriginPercolatesEvent d)]
  exact measureReal_mono fun Z hZ ↦
    continuumOriginPercolates_monotoneCoupling Z hZ

/-- The Boolean-model percolation probability is monotone in intensity. -/
theorem continuumTheta_mono (d : ℕ) : Monotone (continuumTheta d) := by
  intro base upper hbase
  rw [← add_tsub_cancel_of_le hbase]
  exact continuumTheta_le_add d base (upper - base)

end Percolation
