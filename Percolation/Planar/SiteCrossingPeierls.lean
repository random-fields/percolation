import Percolation.Planar.SquareStar
import Percolation.Bernoulli.Basic

/-!
# Peierls count for closed star paths

This file proves the probability-counting half of Grimmett (7.70). A self-avoiding length-`n`
star path has `n+1` distinct sites, so a fixed code is closed with probability `(1-p)^(n+1)`.
There are at most `8^n` codes from a fixed start.

The separate planar frontier file constructs a closed separator when a left-right site crossing
fails. The remaining geometric theorem must extract a top-bottom star path from that separator;
once supplied, the bound here gives the exponential estimate without any additional probability
input.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval BigOperators

/-- Some self-avoiding star walk of length `n` from `x` has all its sites closed. -/
def closedSquareStarSelfAvoidingWalkEvent
    (x : SquareVertex) (n : ℕ) : Set (Set SquareVertex) :=
  ⋃ c : SquareStarSelfAvoidingCode x n,
    {eta : Set SquareVertex |
      Disjoint
        ((squareStarWalkFromVector x c.1).2.support.toFinset : Set SquareVertex) eta}

theorem measurableSet_closedSquareStarSelfAvoidingWalkEvent
    (x : SquareVertex) (n : ℕ) :
    MeasurableSet (closedSquareStarSelfAvoidingWalkEvent x n) := by
  apply MeasurableSet.iUnion
  intro c
  exact measurableSet_disjoint_finset _

/-- Fixed-start degree-eight Peierls bound for closed star paths. -/
theorem setBernoulli_real_closedSquareStarSelfAvoidingWalkEvent_le
    (p : I) (x : SquareVertex) (n : ℕ) :
    setBer((Set.univ : Set SquareVertex), p).real
        (closedSquareStarSelfAvoidingWalkEvent x n) ≤
      (8 : ℝ) ^ n * (1 - (p : ℝ)) ^ (n + 1) := by
  classical
  calc
    setBer((Set.univ : Set SquareVertex), p).real
        (closedSquareStarSelfAvoidingWalkEvent x n) ≤
        ∑ c : SquareStarSelfAvoidingCode x n,
          setBer((Set.univ : Set SquareVertex), p).real
            {eta : Set SquareVertex |
              Disjoint
                ((squareStarWalkFromVector x c.1).2.support.toFinset : Set SquareVertex) eta} :=
      measureReal_iUnion_fintype_le _
    _ = Fintype.card (SquareStarSelfAvoidingCode x n) *
        (1 - (p : ℝ)) ^ (n + 1) := by
      have hcard (c : SquareStarSelfAvoidingCode x n) :
          (squareStarWalkFromVector x c.1).2.support.toFinset.card = n + 1 := by
        rw [List.toFinset_card_of_nodup c.2.support_nodup,
          SimpleGraph.Walk.length_support, squareStarWalkFromVector_length]
      simp_rw [setBernoulli_real_disjoint_finset_univ, hcard]
      simp
    _ ≤ (8 : ℝ) ^ n * (1 - (p : ℝ)) ^ (n + 1) := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast card_squareStarSelfAvoidingCode_le x n
      · exact pow_nonneg (sub_nonneg.mpr p.2.2) _

end Percolation
