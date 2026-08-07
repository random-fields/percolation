import Percolation.Bernoulli.CoordinateIndependence
import Percolation.Bernoulli.FKGInfinite

/-!
# Probability lemmas for the Bollobás--Riordan extension argument

These lemmas isolate the two measure-theoretic operations used after the deterministic
first-contact construction: the symmetric two-case estimate and exact factorization across
disjoint finite coordinate supports.
-/

namespace Percolation

open MeasureTheory
open scoped unitInterval

/-- If an event is covered by two equally likely cases, either case has at least half of its
probability.  The cases need not be disjoint. -/
theorem measureReal_div_two_le_of_subset_union_of_eq
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    {H L U : Set Ω} (hsubset : H ⊆ L ∪ U)
    (heq : μ.real U = μ.real L) :
    μ.real H / 2 ≤ μ.real L := by
  have hmono : μ.real H ≤ μ.real (L ∪ U) :=
    measureReal_mono hsubset
  have hunion : μ.real (L ∪ U) ≤ μ.real L + μ.real U :=
    measureReal_union_le L U
  rw [heq] at hunion
  linarith

/-- The square-root trick for two reflected increasing Bernoulli events.  If `H` is covered by
two increasing events of equal probability, positive association improves the elementary
`P(H) / 2` estimate to `1 - sqrt (1 - P(H))`. -/
theorem one_sub_sqrt_one_sub_measureReal_le_of_subset_union_of_eq
    {d : ℕ} (p : I)
    {H L U : Set (EdgeConfiguration d)}
    (hsubset : H ⊆ L ∪ U)
    (heq : (bernoulliBondMeasure d p).real U =
      (bernoulliBondMeasure d p).real L)
    (hLinc : IsIncreasingEvent L) (hUinc : IsIncreasingEvent U)
    (hLm : MeasurableSet L) (hUm : MeasurableSet U) :
    1 - Real.sqrt (1 - (bernoulliBondMeasure d p).real H) ≤
      (bernoulliBondMeasure d p).real L := by
  letI : IsProbabilityMeasure (bernoulliBondMeasure d p) := by
    unfold bernoulliBondMeasure
    infer_instance
  let h := (bernoulliBondMeasure d p).real H
  let a := (bernoulliBondMeasure d p).real L
  have hmono : h ≤ (bernoulliBondMeasure d p).real (L ∪ U) :=
    measureReal_mono hsubset (measure_ne_top _ _)
  have hunion : (bernoulliBondMeasure d p).real (L ∪ U) +
        (bernoulliBondMeasure d p).real (L ∩ U) =
      (bernoulliBondMeasure d p).real L +
        (bernoulliBondMeasure d p).real U :=
    measureReal_union_add_inter₀ hUm.nullMeasurableSet
  have hfkg : (bernoulliBondMeasure d p).real L *
        (bernoulliBondMeasure d p).real U ≤
      (bernoulliBondMeasure d p).real (L ∩ U) :=
    bernoulliBondMeasure_real_fkg p hLinc hUinc hLm hUm
  have hh1 : h ≤ 1 := measureReal_le_one
  have ha1 : a ≤ 1 := measureReal_le_one
  have hsqrt0 : 0 ≤ Real.sqrt (1 - h) := Real.sqrt_nonneg _
  have hsqrt_sq : Real.sqrt (1 - h) ^ 2 = 1 - h := by
    exact Real.sq_sqrt (sub_nonneg.mpr hh1)
  change 1 - Real.sqrt (1 - h) ≤ a
  dsimp [a, h] at hmono hunion hfkg heq ⊢
  nlinarith

/-- Finite-coordinate form of exact Bernoulli factorization on disjoint supports. -/
theorem bernoulliBondMeasure_real_inter_eq_mul_of_dependsOn_disjoint
    {d : ℕ} (p : I)
    {S T : Finset (CubicEdge d)} (hST : Disjoint S T)
    {A B : Set (EdgeConfiguration d)}
    (hA : DependsOn S A) (hB : DependsOn T B)
    (hAm : MeasurableSet A) (hBm : MeasurableSet B) :
    (bernoulliBondMeasure d p).real (A ∩ B) =
      (bernoulliBondMeasure d p).real A *
        (bernoulliBondMeasure d p).real B := by
  apply setBernoulli_real_inter_eq_mul_of_dependsOnCoordinates p
  · rw [Set.disjoint_left]
    intro e heS heT
    exact Finset.disjoint_left.mp hST heS heT
  · exact hA.dependsOnCoordinates
  · exact hB.dependsOnCoordinates
  · exact hAm
  · exact hBm

end Percolation
