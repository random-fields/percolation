import Percolation.Planar.RSWHalf

/-!
# The exact square-lattice critical probability

This file closes Grimmett's RSW proof of Lemma 11.12 and Theorem 11.11.  The exact finite
self-duality count gives a uniform square-crossing lower bound, RSW turns it into a uniform
annular-circuit lower bound, shifted disjoint annuli give independent closed barriers, and the
barrier product forces the critical percolation probability to vanish.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval

/-- An explicit positive constant used for every shifted critical annulus. -/
noncomputable def squareCriticalBarrierLowerBound : ℝ :=
  (1 / 8 : ℝ) ^ 12 * (1 / 16 : ℝ) ^ 48

theorem squareCriticalBarrierLowerBound_pos :
    0 < squareCriticalBarrierLowerBound := by
  unfold squareCriticalBarrierLowerBound
  positivity

theorem squareCriticalBarrierLowerBound_le_one :
    squareCriticalBarrierLowerBound ≤ 1 := by
  unfold squareCriticalBarrierLowerBound
  norm_num

private theorem one_sixteenth_le_one_sub_sqrt_one_sub
    {r : ℝ} (hr : 1 / 8 ≤ r) (hr1 : r ≤ 1) :
    1 / 16 ≤ 1 - Real.sqrt (1 - r) := by
  have hnonneg : 0 ≤ 1 - r := by linarith
  have hsqrt0 : 0 ≤ Real.sqrt (1 - r) := Real.sqrt_nonneg _
  have hsquare : (Real.sqrt (1 - r)) ^ 2 = 1 - r := by
    simpa using Real.sq_sqrt hnonneg
  nlinarith

private theorem squareCriticalBarrierLowerBound_le_rswExpression
    {r : ℝ} (hr : 1 / 8 ≤ r) (hr1 : r ≤ 1) :
    squareCriticalBarrierLowerBound ≤
      r ^ 12 * (1 - Real.sqrt (1 - r)) ^ 48 := by
  have hr0 : 0 ≤ r := by linarith
  have hu := one_sixteenth_le_one_sub_sqrt_one_sub hr hr1
  have hu0 : 0 ≤ 1 - Real.sqrt (1 - r) := by linarith
  unfold squareCriticalBarrierLowerBound
  exact mul_le_mul
    (pow_le_pow_left₀ (by norm_num) hr 12)
    (pow_le_pow_left₀ (by norm_num) hu 48)
    (pow_nonneg (by norm_num) 48)
    (pow_nonneg hr0 12)

/-- Every shifted critical annulus has a uniformly positive closed-barrier probability at
density `1/2`. -/
theorem squareCriticalBarrierLowerBound_le_probability (k : ℕ) :
    squareCriticalBarrierLowerBound ≤
      (bernoulliBondMeasure 2 squareHalfDensity).real
        (criticalAnnulusBarrierEvent (k + 1)) := by
  let l := 4 ^ (k + 1)
  let r := rswSquareCrossingProbability squareHalfDensity l
  have hl1 : 1 ≤ l := one_le_pow₀ (by omega : 1 ≤ (4 : ℕ))
  have hl2 : 2 ≤ l := by
    dsimp [l]
    have : 4 ≤ 4 ^ (k + 1) := by
      rw [pow_succ]
      have hpos : 1 ≤ 4 ^ k := one_le_pow₀ (by omega : 1 ≤ (4 : ℕ))
      omega
    omega
  have hr : 1 / 8 ≤ r := by
    exact one_eighth_le_rswSquareCrossingProbability_half l hl2
  have hr1 : r ≤ 1 := measureReal_le_one
  calc
    squareCriticalBarrierLowerBound ≤
        r ^ 12 * (1 - Real.sqrt (1 - r)) ^ 48 :=
      squareCriticalBarrierLowerBound_le_rswExpression hr hr1
    _ ≤ rswAnnulusOpenCircuitProbability squareHalfDensity l := by
      simpa [r] using
        rswAnnulusOpenCircuitProbability_ge squareHalfDensity l hl1
    _ ≤ (bernoulliBondMeasure 2 squareHalfDensity).real
        (squareAnnulusBarrierEvent l (3 * l)) :=
      rswAnnulusOpenCircuitProbability_le_half_barrier l
    _ = (bernoulliBondMeasure 2 squareHalfDensity).real
        (criticalAnnulusBarrierEvent (k + 1)) := by
      rfl

/-- **Grimmett, Lemma 11.12.** There is no infinite open origin cluster in the square lattice
at the self-dual density `1/2`. -/
theorem theta_two_half_eq_zero : theta 2 squareHalfDensity = 0 := by
  let barrier : ℕ → Set (EdgeConfiguration 2) :=
    fun k ↦ criticalAnnulusBarrierEvent (k + 1)
  apply theta_eq_zero_of_iIndep_barriers squareHalfDensity barrier
      (fun k ↦ measurableSet_squareAnnulusBarrierEvent _ _)
      ((iIndepSet_criticalAnnulusBarrierEvent squareHalfDensity).precomp
        (g := fun k : ℕ ↦ k + 1) (by
          intro i j hij
          exact Nat.add_right_cancel hij))
      squareCriticalBarrierLowerBound_pos squareCriticalBarrierLowerBound_le_one
  · intro k
    exact squareCriticalBarrierLowerBound_le_probability k
  · intro omega hinfinite
    simp only [barrier, Set.mem_iInter, Set.mem_compl_iff]
    intro k hbarrier
    have hall :=
      hasInfiniteOpenCluster_subset_iInter_criticalAnnulusBarrierEvent_compl hinfinite
    exact (Set.mem_iInter.mp hall (k + 1)) hbarrier

/-- **Grimmett, Theorem 11.11.** The critical probability of bond percolation on
`ℤ²` is exactly `1/2`. -/
theorem cubicCriticalProbability_two_eq_half :
    cubicCriticalProbability 2 = 1 / 2 := by
  apply le_antisymm cubicCriticalProbability_two_le_half
  exact half_le_cubicCriticalProbability_two_of_theta_half_eq_zero
    theta_two_half_eq_zero

end Percolation
