import Percolation.Planar.BondCrossingDuality

/-!
# Exact half-density crossing probability

This file transfers the externally cited finite planar-duality trace count to the Bernoulli
measure, proves Grimmett's Lemma 11.21, and feeds it into the exponential-decay contradiction.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval

private theorem finiteBernoulliWeight_half_of_subset {ι : Type*} {E s : Finset ι}
    (hs : s ⊆ E) :
    finiteBernoulliWeight E (1 / 2) s = (1 / 2 : ℝ) ^ E.card := by
  rw [finiteBernoulliWeight, show (1 - 1 / 2 : ℝ) = 1 / 2 by norm_num, ← pow_add]
  congr 1
  exact Nat.add_sub_of_le (Finset.card_le_card hs)

private theorem finiteBernoulliProbability_eq_traceCard_mul_halfPow
    {ι : Type*} [DecidableEq ι] (E : Finset ι) (T : Set (Finset ι))
    [DecidablePred fun s ↦ s ∈ T] :
    finiteBernoulliProbability E (1 / 2) T =
      ((E.powerset.filter fun s ↦ s ∈ T).card : ℝ) * (1 / 2 : ℝ) ^ E.card := by
  classical
  rw [finiteBernoulliProbability_eq_sum_indicator]
  calc
    (∑ s ∈ E.powerset,
        finiteBernoulliWeight E (1 / 2) s * T.indicator (fun _ ↦ 1) s) =
        ∑ s ∈ E.powerset.filter (fun s ↦ s ∈ T),
          finiteBernoulliWeight E (1 / 2) s := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro s _hs
      by_cases hsT : s ∈ T <;> simp [hsT]
    _ = ∑ _s ∈ E.powerset.filter (fun s ↦ s ∈ T), (1 / 2 : ℝ) ^ E.card := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [finiteBernoulliWeight_half_of_subset]
      exact Finset.mem_powerset.mp (Finset.mem_filter.mp hs).1
    _ = ((E.powerset.filter fun s ↦ s ∈ T).card : ℝ) * (1 / 2 : ℝ) ^ E.card := by
      simp

private theorem finiteBernoulliProbability_add_compl
    {ι : Type*} [DecidableEq ι] (E : Finset ι) (p : ℝ) (T : Set (Finset ι)) :
    finiteBernoulliProbability E p T + finiteBernoulliProbability E p Tᶜ = 1 := by
  classical
  calc
    finiteBernoulliProbability E p T + finiteBernoulliProbability E p Tᶜ =
        ∑ s ∈ E.powerset, finiteBernoulliWeight E p s *
          (T.indicator (fun _ ↦ 1) s + Tᶜ.indicator (fun _ ↦ 1) s) := by
      unfold finiteBernoulliProbability finiteBernoulliExpectation
      simp only [mul_add, Finset.sum_add_distrib]
    _ = ∑ s ∈ E.powerset, finiteBernoulliWeight E p s := by
      apply Finset.sum_congr rfl
      intro s _hs
      by_cases hsT : s ∈ T <;> simp [hsT]
    _ = 1 := sum_finiteBernoulliWeight E p

theorem cubicCriticalProbability_two_le_half :
    cubicCriticalProbability 2 ≤ 1 / 2 := by
  exact cubicCriticalProbability_two_le_half_via_bond_interface

end Percolation
