import Percolation.Extensions.FirstPassage
import Percolation.Bernoulli.Basic

/-!
# The iid law for first-passage environments
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- The iid edge-time law with one-edge marginal `ν`. -/
noncomputable def firstPassageMeasure {d : ℕ} (ν : Measure ℝ≥0∞) :
    Measure (FirstPassageConfiguration d) :=
  Measure.infinitePi fun _ : CubicEdge d ↦ ν

instance firstPassageMeasure_isProbabilityMeasure {d : ℕ} (ν : Measure ℝ≥0∞)
    [IsProbabilityMeasure ν] : IsProbabilityMeasure (firstPassageMeasure (d := d) ν) := by
  unfold firstPassageMeasure
  infer_instance

theorem measurable_firstPassageTranslationPullback {d : ℕ} (x y : Cubic d) :
    Measurable (firstPassageTranslationPullback x y :
      FirstPassageConfiguration d → FirstPassageConfiguration d) := by
  exact measurable_pi_lambda _ fun e ↦
    measurable_pi_apply ((cubicTranslationIso x y).mapEdgeSet e)

/-- The iid environment is invariant under every lattice translation. -/
theorem firstPassageMeasure_map_translationPullback {d : ℕ} (ν : Measure ℝ≥0∞)
    [IsProbabilityMeasure ν] (x y : Cubic d) :
    (firstPassageMeasure (d := d) ν).map
        (firstPassageTranslationPullback x y) =
      firstPassageMeasure (d := d) ν := by
  simpa [firstPassageMeasure, firstPassageTranslationPullback] using
    infinitePi_map_precomp_embedding
      (cubicTranslationIso x y).mapEdgeSet.toEmbedding
      (fun _ : CubicEdge d ↦ ν)

theorem measurable_firstPassageEdgeWeight {d : ℕ} (e : Sym2 (Cubic d)) :
    Measurable fun t : FirstPassageConfiguration d ↦ firstPassageEdgeWeight t e := by
  unfold firstPassageEdgeWeight
  split_ifs with he
  · exact measurable_pi_apply (⟨e, he⟩ : CubicEdge d)
  · exact measurable_const

private theorem measurable_firstPassageListTime {d : ℕ} (l : List (Sym2 (Cubic d))) :
    Measurable fun t : FirstPassageConfiguration d ↦
      (l.map (firstPassageEdgeWeight t)).sum := by
  induction l with
  | nil => simpa using (measurable_const : Measurable fun _ : FirstPassageConfiguration d ↦
      (0 : ℝ≥0∞))
  | cons e l ih =>
      simpa using (measurable_firstPassageEdgeWeight e).add ih

theorem measurable_firstPassagePathTime {d : ℕ} {x y : Cubic d}
    (w : (cubicGraph d).Walk x y) :
    Measurable fun t : FirstPassageConfiguration d ↦ firstPassagePathTime t w := by
  exact measurable_firstPassageListTime w.edges

theorem measurable_firstPassageTime {d : ℕ} (x y : Cubic d) :
    Measurable fun t : FirstPassageConfiguration d ↦ firstPassageTime t x y := by
  letI : Countable ((cubicGraph d).Walk x y) :=
    (show Function.Injective
        (fun w : (cubicGraph d).Walk x y ↦ w.support) from
      fun _ _ h ↦ SimpleGraph.Walk.ext_support h).countable
  exact Measurable.iInf fun w ↦ measurable_firstPassagePathTime w

theorem measurable_axialPassageTime {d : ℕ} (m n : ℕ) :
    Measurable fun t : FirstPassageConfiguration d ↦ axialPassageTime t m n :=
  measurable_firstPassageTime _ _

/-- Distributional stationarity of the two-parameter axial passage-time process. -/
theorem axialPassageTime_stationary {d : ℕ} (ν : Measure ℝ≥0∞)
    [IsProbabilityMeasure ν] (k m n : ℕ) :
    Measure.map (fun t : FirstPassageConfiguration d ↦
        axialPassageTime t (k + m) (k + n)) (firstPassageMeasure ν) =
      Measure.map (fun t : FirstPassageConfiguration d ↦
        axialPassageTime t m n) (firstPassageMeasure ν) := by
  let T := firstPassageTranslationPullback cubicOrigin (cubicAxisVertex d k)
  have hmap : (firstPassageMeasure (d := d) ν).map T =
      firstPassageMeasure (d := d) ν :=
    firstPassageMeasure_map_translationPullback ν _ _
  have hmeasT : Measurable T := measurable_firstPassageTranslationPullback _ _
  have hmeasA : Measurable (fun t : FirstPassageConfiguration d ↦
      axialPassageTime t m n) := measurable_axialPassageTime m n
  let f := fun t : FirstPassageConfiguration d ↦ axialPassageTime t m n
  let g := fun t : FirstPassageConfiguration d ↦
    axialPassageTime t (k + m) (k + n)
  have hgf : g = f ∘ T := by
    funext t
    exact axialPassageTime_shift t k m n
  calc
    Measure.map g (firstPassageMeasure ν) =
        Measure.map (f ∘ T) (firstPassageMeasure ν) := by rw [hgf]
    _ = Measure.map f ((firstPassageMeasure ν).map T) :=
      (Measure.map_map hmeasA hmeasT).symm
    _ = Measure.map f (firstPassageMeasure ν) := by rw [hmap]

end Percolation
