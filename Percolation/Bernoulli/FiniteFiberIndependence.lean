import Mathlib.MeasureTheory.Measure.Real

/-!
# Finite fiber probability bounds

This file collects ratio-free summation lemmas for finite measurable partitions.  In
applications, independence or a product-measure calculation supplies the lower bound on each
fiber; the lemmas below sum those bounds without dividing by the measure of a fiber.
-/

namespace Percolation

open MeasureTheory

/-- Sum a uniform lower bound for measurable extensions over pairwise-disjoint fibers. -/
theorem mul_measureReal_biUnion_le_biUnion_inter
    {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
    (μ : Measure Ω) [IsFiniteMeasure μ] (s : Finset ι)
    (fiber extension : ι → Set Ω) (q : ℝ)
    (hpairwise : Set.PairwiseDisjoint (s : Set ι) fiber)
    (hfiber : ∀ i ∈ s, MeasurableSet (fiber i))
    (hextension : ∀ i ∈ s, MeasurableSet (extension i))
    (hlower : ∀ i ∈ s,
      q * μ.real (fiber i) ≤ μ.real (fiber i ∩ extension i)) :
    q * μ.real (⋃ i ∈ s, fiber i) ≤
      μ.real (⋃ i ∈ s, fiber i ∩ extension i) := by
  have hinterPairwise :
      Set.PairwiseDisjoint (s : Set ι) fun i ↦ fiber i ∩ extension i := by
    intro i hi j hj hij
    exact (hpairwise hi hj hij).mono Set.inter_subset_left Set.inter_subset_left
  rw [measureReal_biUnion_finset hpairwise hfiber,
    measureReal_biUnion_finset hinterPairwise fun i hi ↦
      (hfiber i hi).inter (hextension i hi),
    Finset.mul_sum]
  exact Finset.sum_le_sum fun i hi ↦ hlower i hi

/-- Rewrite a measurable event as a finite partition before summing uniform fiber bounds. -/
theorem mul_measureReal_le_biUnion_inter_of_partition
    {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
    (μ : Measure Ω) [IsFiniteMeasure μ] (s : Finset ι)
    (event : Set Ω) (fiber extension : ι → Set Ω) (q : ℝ)
    (hpartition : event = ⋃ i ∈ s, fiber i)
    (hpairwise : Set.PairwiseDisjoint (s : Set ι) fiber)
    (hfiber : ∀ i ∈ s, MeasurableSet (fiber i))
    (hextension : ∀ i ∈ s, MeasurableSet (extension i))
    (hlower : ∀ i ∈ s,
      q * μ.real (fiber i) ≤ μ.real (fiber i ∩ extension i)) :
    q * μ.real event ≤ μ.real (⋃ i ∈ s, fiber i ∩ extension i) := by
  rw [hpartition]
  exact mul_measureReal_biUnion_le_biUnion_inter μ s fiber extension q hpairwise hfiber
    hextension hlower

end Percolation
