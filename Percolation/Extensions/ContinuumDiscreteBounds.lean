import Percolation.Extensions.ContinuumCritical
import Percolation.Extensions.ContinuumPointComparison

/-!
# Exact critical-intensity transform for the continuum cube approximation

For the approximation lattice `L_n`, cube occupation has density
`1 - exp (-lambda / n^d)`.  This file inverts that change of variables exactly and proves the
unit-mesh instance of Grimmett's lower comparison (12.41) for the concrete rooted Boolean model.
The all-mesh Boolean comparison additionally needs invariance of the Poisson construction under
repartitioning space; it is deliberately not assumed here.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory Set
open scoped NNReal unitInterval

/-- The intensity corresponding exactly to the site threshold of `L_n`:
`-n^d log (1 - p_c(L_n))`. -/
noncomputable def continuumApproximationCriticalIntensity (d n : ℕ) : ℝ≥0 :=
  ⟨-((n : ℝ) ^ d) *
      Real.log (1 - siteCriticalProbability (continuumApproximationGraph d n)), by
    have hc0 : 0 ≤ siteCriticalProbability (continuumApproximationGraph d n) :=
      siteCriticalProbability_nonneg _
    have hc1 : siteCriticalProbability (continuumApproximationGraph d n) ≤ 1 :=
      siteCriticalProbability_le_one _
    exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr (by positivity))
      (Real.log_nonpos (sub_nonneg.mpr hc1) (by linarith))⟩

@[simp]
theorem coe_continuumApproximationCriticalIntensity (d n : ℕ) :
    (continuumApproximationCriticalIntensity d n : ℝ) =
      -((n : ℝ) ^ d) *
        Real.log (1 - siteCriticalProbability (continuumApproximationGraph d n)) :=
  rfl

private theorem continuumCubeDensity_lt_siteCriticalProbability_of_intensity_lt
    {d n : ℕ} (hd : 2 ≤ d) (hn : 0 < n) {intensity : ℝ≥0}
    (hintensity : intensity < continuumApproximationCriticalIntensity d n) :
    (continuumCubeDensity d intensity n : ℝ) <
      siteCriticalProbability (continuumApproximationGraph d n) := by
  let c := siteCriticalProbability (continuumApproximationGraph d n)
  have hc1 : c < 1 := continuumApproximation_siteCriticalProbability_lt_one hd hn
  have hgap : 0 < 1 - c := sub_pos.mpr hc1
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hscale : (0 : ℝ) < (n : ℝ) ^ d := pow_pos hnR d
  have hintensityR :
      (intensity : ℝ) < -((n : ℝ) ^ d) * Real.log (1 - c) := by
    have h := NNReal.coe_lt_coe.mpr hintensity
    simpa [continuumApproximationCriticalIntensity, c, Nat.cast_pow] using h
  have hdiv :
      (intensity : ℝ) / ((n : ℝ) ^ d) < -Real.log (1 - c) := by
    rw [div_lt_iff₀ hscale]
    calc
      (intensity : ℝ) < -((n : ℝ) ^ d) * Real.log (1 - c) := hintensityR
      _ = -Real.log (1 - c) * (n : ℝ) ^ d := by ring
  have hlog :
      Real.log (1 - c) < -((intensity : ℝ) / ((n : ℝ) ^ d)) := by
    linarith
  have hexp := Real.exp_lt_exp.mpr hlog
  rw [Real.exp_log hgap] at hexp
  change 1 - Real.exp (-(continuumCubeRate d intensity n : ℝ)) < c
  have hrate :
      (continuumCubeRate d intensity n : ℝ) =
        (intensity : ℝ) / ((n : ℝ) ^ d) := by
    simp [continuumCubeRate]
  rw [hrate]
  linarith

private theorem siteCriticalProbability_lt_continuumCubeDensity_of_lt_intensity
    {d n : ℕ} (hd : 2 ≤ d) (hn : 0 < n) {intensity : ℝ≥0}
    (hintensity : continuumApproximationCriticalIntensity d n < intensity) :
    siteCriticalProbability (continuumApproximationGraph d n) <
      (continuumCubeDensity d intensity n : ℝ) := by
  let c := siteCriticalProbability (continuumApproximationGraph d n)
  have hc1 : c < 1 := continuumApproximation_siteCriticalProbability_lt_one hd hn
  have hgap : 0 < 1 - c := sub_pos.mpr hc1
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hscale : (0 : ℝ) < (n : ℝ) ^ d := pow_pos hnR d
  have hintensityR :
      -((n : ℝ) ^ d) * Real.log (1 - c) < (intensity : ℝ) := by
    have h := NNReal.coe_lt_coe.mpr hintensity
    simpa [continuumApproximationCriticalIntensity, c, Nat.cast_pow] using h
  have hdiv :
      -Real.log (1 - c) < (intensity : ℝ) / ((n : ℝ) ^ d) := by
    rw [lt_div_iff₀ hscale]
    calc
      -Real.log (1 - c) * (n : ℝ) ^ d =
          -((n : ℝ) ^ d) * Real.log (1 - c) := by ring
      _ < (intensity : ℝ) := hintensityR
  have hlog :
      -((intensity : ℝ) / ((n : ℝ) ^ d)) < Real.log (1 - c) := by
    linarith
  have hexp := Real.exp_lt_exp.mpr hlog
  rw [Real.exp_log hgap] at hexp
  change c < 1 - Real.exp (-(continuumCubeRate d intensity n : ℝ))
  have hrate :
      (continuumCubeRate d intensity n : ℝ) =
        (intensity : ℝ) / ((n : ℝ) ^ d) := by
    simp [continuumCubeRate]
  rw [hrate]
  linarith

/-- Below the transformed site threshold, the occupied-cube approximation does not
percolate. -/
theorem continuumApproximationTheta_eq_zero_of_lt_criticalIntensity
    {d n : ℕ} (hd : 2 ≤ d) (hn : 0 < n) {intensity : ℝ≥0}
    (hintensity : intensity < continuumApproximationCriticalIntensity d n) :
    continuumApproximationTheta d intensity n = 0 := by
  rw [continuumApproximationTheta_eq_siteTheta]
  exact siteTheta_eq_zero_of_lt_criticalProbability
    (continuumCubeDensity_lt_siteCriticalProbability_of_intensity_lt
      hd hn hintensity)

/-- Above the transformed site threshold, the occupied-cube approximation percolates. -/
theorem continuumApproximationTheta_pos_of_criticalIntensity_lt
    {d n : ℕ} (hd : 2 ≤ d) (hn : 0 < n) {intensity : ℝ≥0}
    (hintensity : continuumApproximationCriticalIntensity d n < intensity) :
    0 < continuumApproximationTheta d intensity n := by
  rw [continuumApproximationTheta_eq_siteTheta]
  exact siteTheta_pos_of_criticalProbability_lt
    (siteCriticalProbability_lt_continuumCubeDensity_of_lt_intensity
      hd hn hintensity)

/-- Unit-mesh probabilistic instance of (12.40): every intensity below the exact transformed
`L_1` threshold is subcritical for the rooted Boolean model. -/
theorem continuumTheta_eq_zero_of_lt_unitApproximationCriticalIntensity
    {d : ℕ} (hd : 2 ≤ d) {intensity : ℝ≥0}
    (hintensity : intensity < continuumApproximationCriticalIntensity d 1) :
    continuumTheta d intensity = 0 := by
  apply le_antisymm
  · exact (continuumTheta_le_continuumApproximationTheta_one d intensity).trans_eq
      (continuumApproximationTheta_eq_zero_of_lt_criticalIntensity hd Nat.zero_lt_one
        hintensity)
  · exact measureReal_nonneg

/-- The unit-mesh instance of Grimmett's lower critical-intensity comparison (12.41). -/
theorem continuumApproximationCriticalIntensity_one_le_continuumCriticalIntensity
    {d : ℕ} (hd : 2 ≤ d) :
    continuumApproximationCriticalIntensity d 1 ≤ continuumCriticalIntensity d := by
  apply le_csInf (continuumPercolatingIntensities_nonempty hd)
  intro intensity hintensity
  by_contra hnot
  have hlt : intensity < continuumApproximationCriticalIntensity d 1 :=
    lt_of_not_ge hnot
  have hzero :=
    continuumTheta_eq_zero_of_lt_unitApproximationCriticalIntensity hd hlt
  have hpos : 0 < continuumTheta d intensity := hintensity
  rw [hzero] at hpos
  exact (lt_irrefl 0) hpos

end Percolation
