import Percolation.Extensions.ContinuumMonotonicity
import Percolation.Extensions.ContinuumSubcritical

/-!
# The critical intensity of the Boolean model

The critical intensity is the infimum of intensities with positive percolation probability.
For dimensions at least two, the explicit low-density branching comparison and the explicit
high-density central-port comparison show that this number is strictly positive and finite.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal MeasureTheory NNReal unitInterval

/-- The set of intensities at which the marked radius-one Boolean model percolates. -/
def continuumPercolatingIntensities (d : ℕ) : Set ℝ≥0 :=
  {intensity | 0 < continuumTheta d intensity}

/-- Critical intensity `lambda_H` from Grimmett's equation (12.34). -/
noncomputable def continuumCriticalIntensity (d : ℕ) : ℝ≥0 :=
  sInf (continuumPercolatingIntensities d)

private theorem continuumPercolatingIntensities_bddBelow (d : ℕ) :
    BddBelow (continuumPercolatingIntensities d) :=
  OrderBot.bddBelow _

theorem continuumPercolatingIntensities_nonempty {d : ℕ} (hd : 2 ≤ d) :
    (continuumPercolatingIntensities d).Nonempty := by
  obtain ⟨intensity, hintensity⟩ := exists_continuumTheta_pos hd
  exact ⟨intensity, hintensity⟩

/-- Every intensity below the critical intensity is subcritical. -/
theorem continuumTheta_eq_zero_of_lt_criticalIntensity {d : ℕ}
    (hd : 2 ≤ d) {intensity : ℝ≥0}
    (hintensity : intensity < continuumCriticalIntensity d) :
    continuumTheta d intensity = 0 := by
  apply le_antisymm
  · by_contra hnot
    have hpos : 0 < continuumTheta d intensity := lt_of_not_ge hnot
    have hle : continuumCriticalIntensity d ≤ intensity := by
      exact csInf_le (continuumPercolatingIntensities_bddBelow d) hpos
    exact (not_le_of_gt hintensity) hle
  · exact measureReal_nonneg

/-- Every intensity strictly above the critical intensity percolates. -/
theorem continuumTheta_pos_of_criticalIntensity_lt {d : ℕ}
    (hd : 2 ≤ d) {intensity : ℝ≥0}
    (hintensity : continuumCriticalIntensity d < intensity) :
    0 < continuumTheta d intensity := by
  obtain ⟨lower, hlower, hlowerIntensity⟩ :=
    exists_lt_of_csInf_lt (continuumPercolatingIntensities_nonempty hd) hintensity
  exact hlower.trans_le (continuumTheta_mono d hlowerIntensity.le)

/-- The explicit low-density witness is a lower bound for the critical intensity. -/
theorem continuumSubcriticalIntensity_le_criticalIntensity {d : ℕ}
    (hd : 2 ≤ d) :
    continuumSubcriticalIntensity d ≤ continuumCriticalIntensity d := by
  apply le_csInf (continuumPercolatingIntensities_nonempty hd)
  intro intensity hintensity
  by_contra hnot
  have hle : intensity ≤ continuumSubcriticalIntensity d := le_of_not_ge hnot
  have hthetaLe := continuumTheta_mono d hle
  rw [continuumTheta_subcritical_eq_zero d] at hthetaLe
  exact (not_lt_of_ge hthetaLe) hintensity

/-- The critical intensity is strictly positive. -/
theorem continuumCriticalIntensity_pos {d : ℕ} (hd : 2 ≤ d) :
    0 < continuumCriticalIntensity d := by
  exact (continuumSubcriticalIntensity_pos d).trans_le
    (continuumSubcriticalIntensity_le_criticalIntensity hd)

/-- The explicit high-density comparison bounds the critical intensity from above. -/
theorem continuumCriticalIntensity_le_of_theta_pos {d : ℕ}
    {intensity : ℝ≥0} (hintensity : 0 < continuumTheta d intensity) :
    continuumCriticalIntensity d ≤ intensity := by
  exact csInf_le (continuumPercolatingIntensities_bddBelow d) hintensity

/-- In dimensions at least two, the Boolean-model critical intensity is finite.  Since it is
encoded in `NNReal`, this theorem supplies an explicit finite upper witness rather than a
vacuous extended-real assertion. -/
theorem exists_continuumCriticalIntensity_upperBound {d : ℕ} (hd : 2 ≤ d) :
    ∃ intensity : ℝ≥0,
      continuumCriticalIntensity d ≤ intensity ∧
        0 < continuumTheta d intensity := by
  obtain ⟨intensity, hintensity⟩ := exists_continuumTheta_pos hd
  exact ⟨intensity, continuumCriticalIntensity_le_of_theta_pos hintensity, hintensity⟩

/-- Source-facing phase-transition theorem, corresponding to Theorem 12.35.  It deliberately
makes no assertion at the critical intensity. -/
theorem continuum_phase_transition {d : ℕ} (hd : 2 ≤ d) :
    0 < continuumCriticalIntensity d ∧
      (∀ intensity < continuumCriticalIntensity d,
        continuumTheta d intensity = 0) ∧
      (∀ intensity, continuumCriticalIntensity d < intensity →
        0 < continuumTheta d intensity) := by
  refine ⟨continuumCriticalIntensity_pos hd, ?_, ?_⟩
  · intro intensity hintensity
    exact continuumTheta_eq_zero_of_lt_criticalIntensity hd hintensity
  · intro intensity hintensity
    exact continuumTheta_pos_of_criticalIntensity_lt hd hintensity

end Percolation
