import Percolation.Extensions.ContinuumCluster
import Percolation.Extensions.ContinuumCritical

/-!
# Mean-cluster threshold for continuum percolation

This file introduces the second threshold in (12.42) and proves the elementary inequality
`lambda_T ≤ lambda_c` from (12.43).  The reverse inequality is the substantive discrete
comparison (12.44).
-/

namespace Percolation

open MeasureTheory ProbabilityTheory Set SimpleGraph
open scoped ENNReal MeasureTheory NNReal

theorem continuumMonotone_originCluster_subset {d : ℕ}
    (Z : ContinuumMonotoneConfiguration d) :
    continuumOriginCluster (continuumMonotoneLowerConfiguration Z) ⊆
      continuumOriginCluster (continuumMonotoneUpperConfiguration Z) := by
  rintro b ⟨a, haCover, hab⟩
  refine ⟨a, ?_, ?_⟩
  · exact ⟨continuumMonotone_pointActive_imp Z a haCover.1, by
      simpa only [continuumMonotone_point_eq] using haCover.2⟩
  · simpa using hab.map (continuumMonotoneGraphHom Z)

theorem continuumMonotone_originClusterSize_le {d : ℕ}
    (Z : ContinuumMonotoneConfiguration d) :
    continuumOriginClusterSize (continuumMonotoneLowerConfiguration Z) ≤
      continuumOriginClusterSize (continuumMonotoneUpperConfiguration Z) := by
  rw [continuumOriginClusterSize_eq_encard,
    continuumOriginClusterSize_eq_encard]
  exact_mod_cast Set.encard_mono (continuumMonotone_originCluster_subset Z)

/-- Adding independent Poisson points cannot decrease the mean origin-cluster size. -/
theorem continuumMeanClusterSize_le_add (d : ℕ) (base increment : ℝ≥0) :
    continuumMeanClusterSize d base ≤
      continuumMeanClusterSize d (base + increment) := by
  unfold continuumMeanClusterSize
  rw [← continuumMonotoneMeasure_map_lower d base increment,
    ← continuumMonotoneMeasure_map_upper d base increment]
  rw [lintegral_map (measurable_continuumOriginClusterSize d)
      measurable_continuumMonotoneLowerConfiguration,
    lintegral_map (measurable_continuumOriginClusterSize d)
      measurable_continuumMonotoneUpperConfiguration]
  exact lintegral_mono fun Z ↦ continuumMonotone_originClusterSize_le Z

theorem continuumMeanClusterSize_mono (d : ℕ) :
    Monotone (continuumMeanClusterSize d) := by
  intro base upper hbase
  rw [← add_tsub_cancel_of_le hbase]
  exact continuumMeanClusterSize_le_add d base (upper - base)

/-- Intensities with finite mean origin-cluster size. -/
def continuumFiniteMeanIntensities (d : ℕ) : Set ℝ≥0 :=
  {intensity | continuumMeanClusterSize d intensity < ⊤}

/-- Mean-cluster threshold `lambda_T` from equation (12.42). -/
noncomputable def continuumMeanClusterThreshold (d : ℕ) : ℝ≥0 :=
  sSup (continuumFiniteMeanIntensities d)

theorem continuumFiniteMeanIntensities_nonempty (d : ℕ) :
    (continuumFiniteMeanIntensities d).Nonempty := by
  refine ⟨0, ?_⟩
  simp [continuumFiniteMeanIntensities]

theorem continuumFiniteMeanIntensities_bddAbove {d : ℕ} (hd : 2 ≤ d) :
    BddAbove (continuumFiniteMeanIntensities d) := by
  obtain ⟨upper, _hcritical, hupper⟩ :=
    exists_continuumCriticalIntensity_upperBound hd
  refine ⟨upper, ?_⟩
  intro intensity hfinite
  by_contra hnot
  have hupperIntensity : upper < intensity := lt_of_not_ge hnot
  have hthetaIntensity : 0 < continuumTheta d intensity :=
    hupper.trans_le (continuumTheta_mono d hupperIntensity.le)
  have hzero := continuumTheta_eq_zero_of_meanClusterSize_lt_top hfinite
  rw [hzero] at hthetaIntensity
  exact (lt_irrefl 0) hthetaIntensity

theorem continuumMeanClusterThreshold_le_criticalIntensity
    {d : ℕ} (hd : 2 ≤ d) :
    continuumMeanClusterThreshold d ≤ continuumCriticalIntensity d := by
  unfold continuumMeanClusterThreshold
  apply csSup_le (continuumFiniteMeanIntensities_nonempty d)
  intro intensity hfinite
  by_contra hnot
  have hcriticalIntensity : continuumCriticalIntensity d < intensity :=
    lt_of_not_ge hnot
  have hpos := continuumTheta_pos_of_criticalIntensity_lt hd hcriticalIntensity
  have hzero := continuumTheta_eq_zero_of_meanClusterSize_lt_top hfinite
  rw [hzero] at hpos
  exact (lt_irrefl 0) hpos

end Percolation
