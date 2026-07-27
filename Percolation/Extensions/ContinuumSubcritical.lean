import Percolation.Critical.SiteBranching
import Percolation.Extensions.ContinuumPointComparison
import Percolation.Critical.Radius

/-!
# A positive subcritical intensity for the marked Boolean model

This file completes the elementary lower-threshold half of Grimmett's continuum argument.
The unit-mesh approximation graph has degree at most `9^d`: every neighbor of a cube lies in
the coordinate box of radius four.  The bounded-degree site branching estimate then gives an
explicit positive intensity at which the Boolean model cannot percolate.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory Set SimpleGraph
open scoped NNReal unitInterval

/-- One coordinate difference is bounded by the Euclidean distance. -/
theorem abs_sub_le_coordinateEuclideanDist {d : ℕ}
    (u v : ContinuumPoint d) (i : Fin d) :
    |u i - v i| ≤ coordinateEuclideanDist u v := by
  unfold coordinateEuclideanDist
  rw [← Real.sqrt_sq_eq_abs]
  apply Real.sqrt_le_sqrt
  exact Finset.single_le_sum (fun j _hj => sq_nonneg (u j - v j))
    (Finset.mem_univ i)

/-- At unit mesh, adjacent approximation cubes have coordinate indices differing by at most
four.  The sharp bound is three; four keeps all endpoint inequalities non-strict. -/
theorem continuumApproximationGraph_one_neighbor_mem_box
    {d : ℕ} {x y : Cubic d}
    (hxy : (continuumApproximationGraph d 1).Adj x y) :
    y ∈ cubicMetricBox d x 4 := by
  obtain ⟨_hne, u, hu, v, hv, huv⟩ := continuumApproximationGraph_adj.mp hxy
  rw [mem_cubicMetricBox]
  intro i
  have hcoord : |u i - v i| ≤ 2 :=
    (abs_sub_le_coordinateEuclideanDist u v i).trans huv
  rw [abs_le] at hcoord
  have huLow := (hu i).1
  have huHigh := (hu i).2.le
  have hvLow := (hv i).1
  have hvHigh := (hv i).2.le
  simp only [continuumCubeCenter, Nat.cast_one, div_one] at huLow huHigh hvLow hvHigh
  norm_num at huLow huHigh hvLow hvHigh
  constructor
  · exact_mod_cast (by linarith : (x i : ℝ) - 4 ≤ (y i : ℝ))
  · exact_mod_cast (by linarith : (y i : ℝ) ≤ (x i : ℝ) + 4)

/-- The unit-mesh approximation graph is locally finite. -/
noncomputable instance continuumApproximationGraph_one_locallyFinite (d : ℕ) :
    (continuumApproximationGraph d 1).LocallyFinite := by
  intro x
  have hfinite : ((continuumApproximationGraph d 1).neighborSet x).Finite := by
    apply (cubicMetricBox d x 4).finite_toSet.subset
    intro y hy
    exact continuumApproximationGraph_one_neighbor_mem_box hy
  exact hfinite.fintype

/-- Coarse but dimension-explicit degree bound for the unit-mesh approximation graph. -/
theorem continuumApproximationGraph_one_degree_le (d : ℕ) (x : Cubic d) :
    (continuumApproximationGraph d 1).degree x ≤ 9 ^ d := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  calc
    ((continuumApproximationGraph d 1).neighborFinset x).card ≤
        (cubicMetricBox d x 4).card := by
      apply Finset.card_le_card
      intro y hy
      exact continuumApproximationGraph_one_neighbor_mem_box
        ((SimpleGraph.mem_neighborFinset _ _ _).mp hy)
    _ = 9 ^ d := by simpa using cubicMetricBox_card d x 4

/-- An explicit strictly positive intensity below the Boolean transition. -/
noncomputable def continuumSubcriticalIntensity (d : ℕ) : ℝ≥0 :=
  ⟨1 / (2 * (9 : ℝ) ^ d), by positivity⟩

@[simp]
theorem coe_continuumSubcriticalIntensity (d : ℕ) :
    (continuumSubcriticalIntensity d : ℝ) =
      1 / (2 * (9 : ℝ) ^ d) := rfl

theorem continuumSubcriticalIntensity_pos (d : ℕ) :
    0 < continuumSubcriticalIntensity d := by
  rw [← NNReal.coe_pos]
  change (0 : ℝ) < 1 / (2 * (9 : ℝ) ^ d)
  positivity

theorem continuumCubeDensity_subcritical_mul_lt_one (d : ℕ) :
    ((9 ^ d : ℕ) : ℝ) *
        (continuumCubeDensity d (continuumSubcriticalIntensity d) 1 : ℝ) < 1 := by
  have hdensity :
      (continuumCubeDensity d (continuumSubcriticalIntensity d) 1 : ℝ) ≤
        (continuumSubcriticalIntensity d : ℝ) := by
    rw [continuumCubeDensity_coe]
    simp only [continuumCubeRate, Nat.cast_one, one_pow, div_one]
    linarith [Real.one_sub_le_exp_neg (continuumSubcriticalIntensity d : ℝ)]
  calc
    ((9 ^ d : ℕ) : ℝ) *
        (continuumCubeDensity d (continuumSubcriticalIntensity d) 1 : ℝ) ≤
        ((9 ^ d : ℕ) : ℝ) * (continuumSubcriticalIntensity d : ℝ) :=
      mul_le_mul_of_nonneg_left hdensity (by positivity)
    _ = 1 / 2 := by
      rw [coe_continuumSubcriticalIntensity]
      norm_cast
      field_simp
      norm_cast
      ac_rfl
    _ < 1 := by norm_num

/-- At unit mesh, cube occupation is bounded above by the Poisson intensity. -/
theorem continuumCubeDensity_one_le_intensity (d : ℕ) (intensity : ℝ≥0) :
    (continuumCubeDensity d intensity 1 : ℝ) ≤ (intensity : ℝ) := by
  rw [continuumCubeDensity_coe]
  simp only [continuumCubeRate, Nat.cast_one, one_pow, div_one]
  linarith [Real.one_sub_le_exp_neg (intensity : ℝ)]

/-- The whole explicit interval `9^d · lambda < 1` is subcritical for the occupied-cube
projection. -/
theorem continuumApproximationTheta_eq_zero_of_degree_mul_intensity_lt_one
    (d : ℕ) (intensity : ℝ≥0)
    (hsmall : ((9 ^ d : ℕ) : ℝ) * (intensity : ℝ) < 1) :
    continuumApproximationTheta d intensity 1 = 0 := by
  rw [continuumApproximationTheta_eq_siteTheta]
  apply siteTheta_eq_zero_of_degree_mul_lt_one
    (continuumApproximationGraph d 1)
    (continuumApproximationGraph_one_degree_le d)
  exact lt_of_le_of_lt
    (mul_le_mul_of_nonneg_left (continuumCubeDensity_one_le_intensity d intensity)
      (by positivity)) hsmall

/-- Source-facing low-density consequence for the literal marked Boolean model. -/
theorem continuumTheta_eq_zero_of_degree_mul_intensity_lt_one
    (d : ℕ) (intensity : ℝ≥0)
    (hsmall : ((9 ^ d : ℕ) : ℝ) * (intensity : ℝ) < 1) :
    continuumTheta d intensity = 0 := by
  apply le_antisymm
  · exact (continuumTheta_le_continuumApproximationTheta_one d intensity).trans_eq
      (continuumApproximationTheta_eq_zero_of_degree_mul_intensity_lt_one
        d intensity hsmall)
  · exact measureReal_nonneg

/-- The occupied-cube approximation is subcritical at the explicit intensity. -/
theorem continuumApproximationTheta_subcritical_eq_zero (d : ℕ) :
    continuumApproximationTheta d (continuumSubcriticalIntensity d) 1 = 0 := by
  apply continuumApproximationTheta_eq_zero_of_degree_mul_intensity_lt_one
  calc
    ((9 ^ d : ℕ) : ℝ) * (continuumSubcriticalIntensity d : ℝ) = 1 / 2 := by
      rw [coe_continuumSubcriticalIntensity]
      norm_cast
      field_simp
      norm_cast
      ac_rfl
    _ < 1 := by norm_num

/-- The literal marked Boolean model does not percolate at a positive intensity. -/
theorem continuumTheta_subcritical_eq_zero (d : ℕ) :
    continuumTheta d (continuumSubcriticalIntensity d) = 0 := by
  apply continuumTheta_eq_zero_of_degree_mul_intensity_lt_one
  calc
    ((9 ^ d : ℕ) : ℝ) * (continuumSubcriticalIntensity d : ℝ) = 1 / 2 := by
      rw [coe_continuumSubcriticalIntensity]
      norm_cast
      field_simp
      norm_cast
      ac_rfl
    _ < 1 := by norm_num

end Percolation
