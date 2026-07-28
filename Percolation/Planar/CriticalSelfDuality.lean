import Percolation.Planar.FullVerticalDuality
import Percolation.Planar.StrictDualCrossing

/-!
# Critical nonpercolation from strict planar duality

At half density, every scale at least three has a strict shifted-dual horizontal crossing with
probability at least `1 / 32`.  The finite mod-two crossing lemma makes that event disjoint from
the full primal vertical crossing.  If `theta 2 (1 / 2)` were positive, qualitative uniqueness
would force the latter crossing probabilities to tend to one, contradicting their uniform
upper bound `31 / 32`.
-/

namespace Percolation

open Filter MeasureTheory
open scoped unitInterval

/-- A strict dual horizontal crossing lies in the complement of the full primal vertical
crossing event. -/
theorem strictDualHorizontalCrossingEvent_subset_fullVerticalCrossingEvent_compl
    {n : ℕ} (hn : 3 ≤ n) :
    strictDualHorizontalCrossingEvent n ⊆ (fullVerticalCrossingEvent n)ᶜ := by
  intro omega homega
  rw [Set.mem_compl_iff]
  obtain ⟨C⟩ := exists_strictDualHorizontalCrossingWitness_of_mem hn homega
  exact dualWalkIsOpen_not_mem_fullVerticalCrossingEvent C.walk
    C.start_zero C.finish_zero C.support_subset C.isOpen

/-- Full vertical crossings stay uniformly below one at the self-dual density. -/
theorem fullVerticalCrossingProbability_half_le_thirty_one_over_thirty_two
    {n : ℕ} (hn : 3 ≤ n) :
    (bernoulliBondMeasure 2 squareHalfDensity).real
        (fullVerticalCrossingEvent n) ≤ 31 / 32 := by
  have hmono := measureReal_mono
    (strictDualHorizontalCrossingEvent_subset_fullVerticalCrossingEvent_compl hn)
    (measure_ne_top (bernoulliBondMeasure 2 squareHalfDensity)
      (fullVerticalCrossingEvent n)ᶜ)
  rw [probReal_compl_eq_one_sub (measurableSet_fullVerticalCrossingEvent n)] at hmono
  have hlower := one_thirty_second_le_strictDualHorizontalCrossingEvent_half hn
  linarith

/-- Critical half-density percolation is impossible by strict primal/dual crossing
incompatibility and qualitative supercritical crossing convergence. -/
theorem theta_two_half_eq_zero_via_strictDualCrossing :
    theta 2 squareHalfDensity = 0 := by
  apply le_antisymm
  · by_contra hthetaNonpos
    have htheta : 0 < theta 2 squareHalfDensity := lt_of_not_ge hthetaNonpos
    have htendsto :=
      fullVerticalCrossing_probability_tendsto_one squareHalfDensity htheta
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 htendsto (1 / 64) (by norm_num)
    let n := max N 3
    have hnN : N ≤ n := le_max_left N 3
    have hn3 : 3 ≤ n := le_max_right N 3
    have hdist := hN n hnN
    have hle :=
      fullVerticalCrossingProbability_half_le_thirty_one_over_thirty_two hn3
    rw [Real.dist_eq,
      abs_of_nonpos (sub_nonpos.mpr measureReal_le_one)] at hdist
    norm_num at hdist hle
    linarith
  · exact measureReal_nonneg

end Percolation
