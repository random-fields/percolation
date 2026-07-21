import Percolation.Extensions.LongRangeClusterTail

/-!
# Finite-volume mass transport for long-range blocks
-/

namespace Percolation

open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators Topology unitInterval

theorem sum_eventIndicator_clusterAtLeast_eq_count
    (ω : LongRangeConfiguration) (L m : ℕ) (z : ℤ) :
    ∑ x ∈ longRangeIntervalBlock L z,
        eventIndicator (longRangeClusterAtLeastEvent x m) ω =
      (longRangeLargeClusterVertexCount ω L m z : ℝ) := by
  classical
  change (∑ x ∈ longRangeIntervalBlock L z,
      if ω ∈ longRangeClusterAtLeastEvent x m then (1 : ℝ) else 0) =
    (((longRangeIntervalBlock L z).filter fun x ↦
      ω ∈ longRangeClusterAtLeastEvent x m).card : ℝ)
  rw [Finset.card_filter]
  push_cast
  rfl

/-- A dense internal component transports one unit of mass to each of at least `m` vertices
whose ambient cluster has size at least `m`. -/
theorem block_indicator_mul_le_sum_clusterAtLeast
    (ω : LongRangeConfiguration) (L m : ℕ) (z : ℤ) :
    (m : ℝ) * eventIndicator
        (longRangeIntervalLargeComponentEvent L m z) ω ≤
      ∑ x ∈ longRangeIntervalBlock L z,
        eventIndicator (longRangeClusterAtLeastEvent x m) ω := by
  classical
  by_cases hgood : ω ∈ longRangeIntervalLargeComponentEvent L m z
  · rw [sum_eventIndicator_clusterAtLeast_eq_count]
    rw [eventIndicator, Set.indicator_of_mem hgood]
    simp only [mul_one]
    exact_mod_cast largeComponent_implies_largeClusterVertexCount hgood
  · rw [eventIndicator, Set.indicator_of_notMem hgood]
    simp only [mul_zero]
    exact Finset.sum_nonneg fun x _hx ↦ by
      by_cases hx : ω ∈ longRangeClusterAtLeastEvent x m <;>
        simp [eventIndicator, hx]

/-- Translation invariance and finite double counting turn a good block into a root-cluster
tail lower bound. -/
theorem block_mass_le_clusterAtLeast
    (p : LongRangeProfile) (L m : ℕ) (z : ℤ) :
    (m : ℝ) * (longRangeMeasure p).real
        (longRangeIntervalLargeComponentEvent L m z) ≤
      (L : ℝ) * (longRangeMeasure p).real
        (longRangeClusterAtLeastEvent 0 m) := by
  let μ := longRangeMeasure p
  let A := longRangeIntervalLargeComponentEvent L m z
  let B := longRangeIntervalBlock L z
  have hA : MeasurableSet A :=
    measurableSet_longRangeIntervalLargeComponentEvent L m z
  have hAint : Integrable (eventIndicator A) μ :=
    (memLp_eventIndicator hA).integrable one_le_two
  have hleftInt : Integrable (fun ω ↦ (m : ℝ) * eventIndicator A ω) μ :=
    hAint.const_mul _
  have htailInt (x : ℤ) :
      Integrable (eventIndicator (longRangeClusterAtLeastEvent x m)) μ :=
    (memLp_eventIndicator (measurableSet_longRangeClusterAtLeastEvent x m)).integrable
      one_le_two
  have hrightInt : Integrable
      (fun ω ↦ ∑ x ∈ B, eventIndicator (longRangeClusterAtLeastEvent x m) ω) μ := by
    exact integrable_finset_sum B fun x _hx ↦ htailInt x
  have hmono :
      ∫ ω, (m : ℝ) * eventIndicator A ω ∂μ ≤
        ∫ ω, ∑ x ∈ B,
          eventIndicator (longRangeClusterAtLeastEvent x m) ω ∂μ := by
    exact integral_mono hleftInt hrightInt fun ω ↦
      block_indicator_mul_le_sum_clusterAtLeast ω L m z
  calc
    (m : ℝ) * (longRangeMeasure p).real
        (longRangeIntervalLargeComponentEvent L m z) =
        ∫ ω, (m : ℝ) * eventIndicator A ω ∂μ := by
      rw [integral_const_mul, integral_eventIndicator hA]
    _ ≤ ∫ ω, ∑ x ∈ B,
        eventIndicator (longRangeClusterAtLeastEvent x m) ω ∂μ := hmono
    _ = ∑ x ∈ B, (longRangeMeasure p).real
        (longRangeClusterAtLeastEvent x m) := by
      rw [integral_finset_sum B]
      · apply Finset.sum_congr rfl
        intro x hx
        exact integral_eventIndicator
          (measurableSet_longRangeClusterAtLeastEvent x m)
      · exact fun x _hx ↦ htailInt x
    _ = ∑ _x ∈ B, (longRangeMeasure p).real
        (longRangeClusterAtLeastEvent 0 m) := by
      apply Finset.sum_congr rfl
      intro x _hx
      exact longRangeMeasure_real_clusterAtLeast_eq_origin p x m
    _ = (L : ℝ) * (longRangeMeasure p).real
        (longRangeClusterAtLeastEvent 0 m) := by
      simp [B, longRangeIntervalBlock_card, mul_comm]

/-- Ratio form of the block mass estimate. -/
theorem target_density_mul_goodProbability_le_clusterAtLeast
    (p : LongRangeProfile) {L m : ℕ} (hL : 0 < L) (z : ℤ) :
    (m : ℝ) / L * (longRangeMeasure p).real
        (longRangeIntervalLargeComponentEvent L m z) ≤
      (longRangeMeasure p).real (longRangeClusterAtLeastEvent 0 m) := by
  have h := block_mass_le_clusterAtLeast p L m z
  have hLr : (0 : ℝ) < L := by positivity
  rw [div_mul_eq_mul_div, div_le_iff₀ hLr]
  simpa [mul_assoc, mul_left_comm, mul_comm] using h

end Percolation
