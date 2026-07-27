import Percolation.Planar.RSWGluing
import Percolation.Planar.AnnulusDuality
import Percolation.Planar.IndependentBarriers

/-!
# The uniform-crossing interface for the square-lattice threshold

This file isolates the assumption-free end of the critical square-lattice argument. A uniform
positive lower bound for crossing `6l × 2l` rectangles at the shifted critical scales gives a
uniform positive lower bound for independent closed barriers, and hence forces the percolation
probability at the self-dual density to vanish.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval

/-- A uniform lower bound for critical `6l × 2l` crossings gives its fourth power as a
uniform lower bound for the shifted closed barriers. -/
theorem pow_four_le_expandedCriticalAnnulusBarrier_probability_of_uniform_crossing
    {c : ℝ} (hc0 : 0 ≤ c)
    (hcross : ∀ k, c ≤ rswRectangleCrossingProbability squareHalfDensity 3
      (expandedCriticalAnnulusScale k)) (k : ℕ) :
    c ^ 4 ≤ (bernoulliBondMeasure 2 squareHalfDensity).real
      (expandedCriticalAnnulusBarrierEvent k) := by
  let l := expandedCriticalAnnulusScale k
  have hl16 : 16 ≤ l := by
    simpa [l] using expandedCriticalAnnulusScale_ge_sixteen k
  have hl1 : 1 ≤ l := by omega
  have hl2 : 2 ≤ l := by omega
  have hc : c ≤ rswRectangleCrossingProbability squareHalfDensity 3 l := by
    simpa [l] using hcross k
  calc
    c ^ 4 ≤ rswRectangleCrossingProbability squareHalfDensity 3 l ^ 4 :=
      pow_le_pow_left₀ hc0 hc 4
    _ ≤ rswAnnulusOpenCircuitProbability squareHalfDensity l :=
      rswAnnulusOpenCircuitProbability_ge_rectanglePowFour squareHalfDensity l hl1
    _ ≤ (bernoulliBondMeasure 2 squareHalfDensity).real
        (squareAnnulusBarrierEvent (l - 2) (3 * l + 2)) :=
      rswAnnulusOpenCircuitProbability_le_half_expandedBarrier hl2
    _ = (bernoulliBondMeasure 2 squareHalfDensity).real
        (expandedCriticalAnnulusBarrierEvent k) := by
      rfl

/-- A uniform positive critical `6l × 2l` crossing bound at the shifted annulus scales implies
that the origin does not percolate at density `1/2`. -/
theorem theta_two_half_eq_zero_of_uniform_rswRectangleCrossingProbability
    {c : ℝ} (hc0 : 0 < c)
    (hcross : ∀ k, c ≤ rswRectangleCrossingProbability squareHalfDensity 3
      (expandedCriticalAnnulusScale k)) :
    theta 2 squareHalfDensity = 0 := by
  have hc1 : c ≤ 1 := by
    calc
      c ≤ rswRectangleCrossingProbability squareHalfDensity 3
          (expandedCriticalAnnulusScale 0) := hcross 0
      _ ≤ 1 := measureReal_le_one
  have hc4le1 : c ^ 4 ≤ 1 := by
    simpa using pow_le_pow_left₀ (le_of_lt hc0) hc1 4
  apply theta_eq_zero_of_iIndep_barriers squareHalfDensity
      expandedCriticalAnnulusBarrierEvent
      measurableSet_expandedCriticalAnnulusBarrierEvent
      (iIndepSet_expandedCriticalAnnulusBarrierEvent squareHalfDensity)
      (pow_pos hc0 4) hc4le1
  · intro k
    exact pow_four_le_expandedCriticalAnnulusBarrier_probability_of_uniform_crossing
      (le_of_lt hc0) hcross k
  · exact hasInfiniteOpenCluster_subset_iInter_expandedCriticalAnnulusBarrierEvent_compl

end Percolation
