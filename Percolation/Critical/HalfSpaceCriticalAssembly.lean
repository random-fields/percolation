import Percolation.Critical.HalfSpaceBricks
import Percolation.Critical.ThetaContinuity

/-!
# Critical half-space assembly for Grimmett Theorem 7.35

This file isolates the final finite-event continuity argument.  Lemma 7.36 supplies an
arbitrarily reliable finite brick at the critical density if half-space percolation there were
positive.  Lemma 7.52 supplies a dimension-dependent reliability threshold which forces
half-space percolation.  Continuity moves the same finite brick strictly below the critical
density, contradicting the critical-point definition.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval

/-- Exact output interface of Grimmett Lemma 7.36 at the cubic critical density. -/
def CriticalHalfSpaceReliableBricks (d : ℕ) (hd : 2 ≤ d) : Prop :=
  0 < halfSpaceTheta d (cubicCriticalProbabilityUnit d hd) →
    ∀ η : ℝ, 0 < η →
      ∃ m L H : ℕ, 1 ≤ m ∧ m ≤ L ∧ 2 * m ≤ H ∧
        1 - η <
          (bernoulliBondMeasure d (cubicCriticalProbabilityUnit d hd)).real
            (halfSpaceBrickGoodEvent (by omega : 1 ≤ d) m L H)

/-- Exact output interface of Grimmett Lemma 7.52.  The threshold may depend on the fixed
dimension but is uniform in the brick dimensions and in the percolation density. -/
def ReliableBricksForceHalfSpacePercolation (d : ℕ) (hd : 1 ≤ d) : Prop :=
  ∃ ν : ℝ, 0 < ν ∧ ν ≤ 1 ∧
    ∀ (p : I) (m L H : ℕ), 1 ≤ m → m ≤ L → 2 * m ≤ H →
      1 - ν < (bernoulliBondMeasure d p).real
        (halfSpaceBrickGoodEvent hd m L H) →
      0 < halfSpaceTheta d p

/-- Finite-event continuity assembly of Theorem 7.35.  This declaration has no geometric or
conditional-probability content left: its two hypotheses are exactly Lemmas 7.36 and 7.52. -/
theorem halfSpaceTheta_critical_eq_zero_of_reliableBricks
    {d : ℕ} (hd : 2 ≤ d)
    (h36 : CriticalHalfSpaceReliableBricks d hd)
    (h52 : ReliableBricksForceHalfSpacePercolation d (by omega)) :
    halfSpaceTheta d (cubicCriticalProbabilityUnit d hd) = 0 := by
  apply le_antisymm
  · apply le_of_not_gt
    intro hcritical
    obtain ⟨ν, hν0, hν1, hforce⟩ := h52
    obtain ⟨m, L, H, hm, hmL, hH, hgoodCritical⟩ :=
      h36 hcritical (ν / 2) (by positivity)
    have hthresholdCritical : 1 - ν <
        (bernoulliBondMeasure d (cubicCriticalProbabilityUnit d hd)).real
          (halfSpaceBrickGoodEvent (by omega : 1 ≤ d) m L H) := by
      nlinarith
    obtain ⟨q, hqpc, hgoodQ⟩ :=
      exists_lower_density_halfSpaceBrickGoodProbability_gt
        (by omega : 1 ≤ d) m L H
        ((cubicCriticalProbability_pos_lt_one hd).1) hthresholdCritical
    have hqRegionCritical : (q : ℝ) <
        regionCriticalProbability d (cubicHalfSpace d) :=
      hqpc.trans_le (cubicCriticalProbability_le_halfSpaceRegionCritical d)
    have hzero : halfSpaceTheta d q = 0 :=
      halfSpaceTheta_eq_zero_of_lt_critical hqRegionCritical
    have hpositive : 0 < halfSpaceTheta d q :=
      hforce q m L H hm hmL hH hgoodQ
    linarith
  · exact measureReal_nonneg

end Percolation
