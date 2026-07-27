import Percolation.Bernoulli.CoordinateIndependence

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
