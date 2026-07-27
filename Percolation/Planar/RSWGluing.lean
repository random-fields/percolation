import Percolation.Planar.External

/-!
# FKG gluing for the RSW theorem

This file proves all three probability inequalities in Grimmett, Lemma 11.75.  The placements
and their probabilities are handled by explicit graph automorphisms, FKG is applied in Lean,
and only the three bare planar event inclusions remain at the Proposition 11.2 topology boundary
recorded in `Percolation.Planar.External`.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval

private theorem measureReal_mono_probability {d : ℕ} (p : I)
    {A B : Set (EdgeConfiguration d)} (hAB : A ⊆ B) :
    (bernoulliBondMeasure d p).real A ≤ (bernoulliBondMeasure d p).real B :=
  measureReal_mono hAB (measure_ne_top _ _)

/-- Grimmett (11.76): two overlapping `3l × 2l` crossings and one vertical square
crossing glue to a `4l × 2l` crossing. -/
theorem rswRectangleCrossingProbability_two_ge (p : I) (l : ℕ) (hl : 1 ≤ l) :
    rswSquareCrossingProbability p l *
        rswThreeHalvesCrossingProbability p l ^ 2 ≤
      rswRectangleCrossingProbability p 2 l := by
  let μ := bernoulliBondMeasure 2 p
  let L := rswGluingTwoLeftEvent l
  let R := rswGluingTwoRightEvent l
  let V := rswGluingTwoVerticalEvent l
  have hLm : MeasurableSet L := measurableSet_rswThreeHalvesCrossingEvent l
  have hLi : IsIncreasingEvent L := isIncreasingEvent_rswThreeHalvesCrossingEvent l
  have hRm : MeasurableSet R :=
    measurableSet_rswHorizontalPlacementEvent _ _
      (measurableSet_rswThreeHalvesCrossingEvent l)
  have hRi : IsIncreasingEvent R :=
    isIncreasingEvent_rswHorizontalPlacementEvent _ _
      (isIncreasingEvent_rswThreeHalvesCrossingEvent l)
  have hVm : MeasurableSet V :=
    measurableSet_rswVerticalPlacementEvent _ _
      (measurableSet_rswSquareCrossingEvent l)
  have hVi : IsIncreasingEvent V :=
    isIncreasingEvent_rswVerticalPlacementEvent _ _
      (isIncreasingEvent_rswSquareCrossingEvent l)
  have hLR := bernoulliBondMeasure_real_fkg p hLi hRi hLm hRm
  have hLRV := bernoulliBondMeasure_real_fkg p (hLi.inter hRi) hVi
    (hLm.inter hRm) hVm
  have hLprob : μ.real L = rswThreeHalvesCrossingProbability p l := rfl
  have hRprob : μ.real R = rswThreeHalvesCrossingProbability p l := by
    exact bernoulliBondMeasure_real_rswHorizontalPlacementEvent p _ _
      (measurableSet_rswThreeHalvesCrossingEvent l)
  have hVprob : μ.real V = rswSquareCrossingProbability p l := by
    exact bernoulliBondMeasure_real_rswVerticalPlacementEvent p _ _
      (measurableSet_rswSquareCrossingEvent l)
  calc
    rswSquareCrossingProbability p l * rswThreeHalvesCrossingProbability p l ^ 2 =
        (μ.real L * μ.real R) * μ.real V := by
      rw [hLprob, hRprob, hVprob]
      ring
    _ ≤ μ.real (L ∩ R) * μ.real V := by
      exact mul_le_mul_of_nonneg_right hLR measureReal_nonneg
    _ ≤ μ.real ((L ∩ R) ∩ V) := hLRV
    _ = μ.real (rswGluingTwoIntersection l) := by
      rfl
    _ ≤ μ.real (rswRectangleCrossingEvent 2 l) :=
      measureReal_mono_probability p (rswGluingTwoIntersection_subset l hl)
    _ = rswRectangleCrossingProbability p 2 l := rfl

/-- Grimmett (11.77): two overlapping `4l × 2l` crossings and one vertical square
crossing glue to a `6l × 2l` crossing. -/
theorem rswRectangleCrossingProbability_three_ge (p : I) (l : ℕ) (hl : 1 ≤ l) :
    rswSquareCrossingProbability p l *
        rswRectangleCrossingProbability p 2 l ^ 2 ≤
      rswRectangleCrossingProbability p 3 l := by
  let μ := bernoulliBondMeasure 2 p
  let L := rswGluingThreeLeftEvent l
  let R := rswGluingThreeRightEvent l
  let V := rswGluingThreeVerticalEvent l
  have hLm : MeasurableSet L := measurableSet_rswRectangleCrossingEvent 2 l
  have hLi : IsIncreasingEvent L := isIncreasingEvent_rswRectangleCrossingEvent 2 l
  have hRm : MeasurableSet R :=
    measurableSet_rswHorizontalPlacementEvent _ _
      (measurableSet_rswRectangleCrossingEvent 2 l)
  have hRi : IsIncreasingEvent R :=
    isIncreasingEvent_rswHorizontalPlacementEvent _ _
      (isIncreasingEvent_rswRectangleCrossingEvent 2 l)
  have hVm : MeasurableSet V :=
    measurableSet_rswVerticalPlacementEvent _ _
      (measurableSet_rswSquareCrossingEvent l)
  have hVi : IsIncreasingEvent V :=
    isIncreasingEvent_rswVerticalPlacementEvent _ _
      (isIncreasingEvent_rswSquareCrossingEvent l)
  have hLR := bernoulliBondMeasure_real_fkg p hLi hRi hLm hRm
  have hLRV := bernoulliBondMeasure_real_fkg p (hLi.inter hRi) hVi
    (hLm.inter hRm) hVm
  have hLprob : μ.real L = rswRectangleCrossingProbability p 2 l := rfl
  have hRprob : μ.real R = rswRectangleCrossingProbability p 2 l := by
    exact bernoulliBondMeasure_real_rswHorizontalPlacementEvent p _ _
      (measurableSet_rswRectangleCrossingEvent 2 l)
  have hVprob : μ.real V = rswSquareCrossingProbability p l := by
    exact bernoulliBondMeasure_real_rswVerticalPlacementEvent p _ _
      (measurableSet_rswSquareCrossingEvent l)
  calc
    rswSquareCrossingProbability p l * rswRectangleCrossingProbability p 2 l ^ 2 =
        (μ.real L * μ.real R) * μ.real V := by
      rw [hLprob, hRprob, hVprob]
      ring
    _ ≤ μ.real (L ∩ R) * μ.real V := by
      exact mul_le_mul_of_nonneg_right hLR measureReal_nonneg
    _ ≤ μ.real ((L ∩ R) ∩ V) := hLRV
    _ = μ.real (rswGluingThreeIntersection l) := by
      rfl
    _ ≤ μ.real (rswRectangleCrossingEvent 3 l) :=
      measureReal_mono_probability p (rswGluingThreeIntersection_subset l hl)
    _ = rswRectangleCrossingProbability p 3 l := rfl

/-- Grimmett (11.78): four `6l × 2l` crossings glue to a surrounding open circuit. -/
theorem rswAnnulusOpenCircuitProbability_ge_rectanglePowFour
    (p : I) (l : ℕ) (hl : 1 ≤ l) :
    rswRectangleCrossingProbability p 3 l ^ 4 ≤
      rswAnnulusOpenCircuitProbability p l := by
  let μ := bernoulliBondMeasure 2 p
  let T := rswCircuitTopEvent l
  let R := rswCircuitRightEvent l
  let B := rswCircuitBottomEvent l
  let L := rswCircuitLeftEvent l
  have hbaseM := measurableSet_rswRectangleCrossingEvent 3 l
  have hbaseI := isIncreasingEvent_rswRectangleCrossingEvent 3 l
  have hTm : MeasurableSet T := measurableSet_rswHorizontalPlacementEvent _ _ hbaseM
  have hTi : IsIncreasingEvent T := isIncreasingEvent_rswHorizontalPlacementEvent _ _ hbaseI
  have hRm : MeasurableSet R := measurableSet_rswVerticalPlacementEvent _ _ hbaseM
  have hRi : IsIncreasingEvent R := isIncreasingEvent_rswVerticalPlacementEvent _ _ hbaseI
  have hBm : MeasurableSet B := measurableSet_rswHorizontalPlacementEvent _ _ hbaseM
  have hBi : IsIncreasingEvent B := isIncreasingEvent_rswHorizontalPlacementEvent _ _ hbaseI
  have hLm : MeasurableSet L := measurableSet_rswVerticalPlacementEvent _ _ hbaseM
  have hLi : IsIncreasingEvent L := isIncreasingEvent_rswVerticalPlacementEvent _ _ hbaseI
  have hBL := bernoulliBondMeasure_real_fkg p hBi hLi hBm hLm
  have hRBL := bernoulliBondMeasure_real_fkg p hRi (hBi.inter hLi)
    hRm (hBm.inter hLm)
  have hTRBL := bernoulliBondMeasure_real_fkg p hTi (hRi.inter (hBi.inter hLi))
    hTm (hRm.inter (hBm.inter hLm))
  have hTprob : μ.real T = rswRectangleCrossingProbability p 3 l :=
    bernoulliBondMeasure_real_rswHorizontalPlacementEvent p _ _ hbaseM
  have hRprob : μ.real R = rswRectangleCrossingProbability p 3 l :=
    bernoulliBondMeasure_real_rswVerticalPlacementEvent p _ _ hbaseM
  have hBprob : μ.real B = rswRectangleCrossingProbability p 3 l :=
    bernoulliBondMeasure_real_rswHorizontalPlacementEvent p _ _ hbaseM
  have hLprob : μ.real L = rswRectangleCrossingProbability p 3 l :=
    bernoulliBondMeasure_real_rswVerticalPlacementEvent p _ _ hbaseM
  calc
    rswRectangleCrossingProbability p 3 l ^ 4 =
        μ.real T * (μ.real R * (μ.real B * μ.real L)) := by
      rw [hTprob, hRprob, hBprob, hLprob]
      ring
    _ ≤ μ.real T * (μ.real R * μ.real (B ∩ L)) := by
      gcongr
    _ ≤ μ.real T * μ.real (R ∩ (B ∩ L)) := by
      exact mul_le_mul_of_nonneg_left hRBL measureReal_nonneg
    _ ≤ μ.real (T ∩ (R ∩ (B ∩ L))) := hTRBL
    _ = μ.real (rswCircuitGluingIntersection l) := by
      simp only [rswCircuitGluingIntersection, T, R, B, L, Set.inter_assoc]
    _ ≤ μ.real (rswAnnulusOpenCircuitEvent l) :=
      measureReal_mono_probability p (rswCircuitGluingIntersection_subset l hl)
    _ = rswAnnulusOpenCircuitProbability p l := rfl

/-- **Grimmett, Lemma 11.75.**  The three FKG/gluing inequalities (11.76)--(11.78),
packaged in the order in which they occur in the source. -/
theorem rsw_gluing_inequalities (p : I) (l : ℕ) (hl : 1 ≤ l) :
    (rswSquareCrossingProbability p l *
          rswThreeHalvesCrossingProbability p l ^ 2 ≤
        rswRectangleCrossingProbability p 2 l) ∧
      (rswSquareCrossingProbability p l *
          rswRectangleCrossingProbability p 2 l ^ 2 ≤
        rswRectangleCrossingProbability p 3 l) ∧
      (rswRectangleCrossingProbability p 3 l ^ 4 ≤
        rswAnnulusOpenCircuitProbability p l) := by
  exact ⟨rswRectangleCrossingProbability_two_ge p l hl,
    rswRectangleCrossingProbability_three_ge p l hl,
    rswAnnulusOpenCircuitProbability_ge_rectanglePowFour p l hl⟩

end Percolation
