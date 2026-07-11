import Percolation.Bernoulli.SequentialDominationCountable
import Percolation.Critical.DynamicRenormalization

/-!
# Stochastic domination adapters for site explorations

This file isolates one consequence needed near the end of Grimmett's Lemma 7.24.  Once a law on
site configurations has been shown to dominate a supercritical iid site field, positivity of an
infinite occupied cluster follows directly from stochastic domination.  Constructing that law
from the exploration histories, identifying its limiting occupied set with the exploration, and
proving the sequential-domination criterion are separate, still-open parts of Lemma 7.24.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval

/-- Domination by a supercritical iid site field forces positive probability of an infinite
cluster.  This is an adapter used after, but is not itself, the sequential exploration theorem
of Lemma 7.24. -/
theorem siteExploration_infinite_probability_pos_of_dominates
    {V : Type*} [Countable V] (G : SimpleGraph V)
    (μ : Measure (Set V)) (p : I)
    (hp : siteCriticalProbability G < (p : ℝ))
    (hdom : StochasticallyDominates μ setBer((Set.univ : Set V), p)) :
    0 < μ.real {η | hasInfiniteSiteCluster G η} := by
  have hle := hdom.measureReal_le (measurableSet_hasInfiniteSiteCluster G)
    (isIncreasingEvent_hasInfiniteSiteCluster G)
  exact (siteTheta_pos_of_criticalProbability_lt hp).trans_le (by
    simpa [siteTheta] using hle)

/-- Under a probability law dominated from below by supercritical iid sites, the sampled site
set itself is infinite with positive probability.  Applied to the pushforward law of `A∞`, this
is the probability conclusion needed by Lemma 7.24; constructing and dominating that
pushforward law remains a separate theorem. -/
theorem infinite_siteSet_probability_pos_of_dominates
    {V : Type*} [Countable V] (G : SimpleGraph V)
    (μ : Measure (Set V)) [IsProbabilityMeasure μ] (p : I)
    (hp : siteCriticalProbability G < (p : ℝ))
    (hdom : StochasticallyDominates μ setBer((Set.univ : Set V), p)) :
    0 < μ.real {η : Set V | η.Infinite} := by
  have hpos := siteExploration_infinite_probability_pos_of_dominates G μ p hp hdom
  exact hpos.trans_le <| measureReal_mono fun η hη ↦
    Set.Infinite.of_hasInfiniteSiteCluster hη

/-- The positive-probability conclusion of Lemma 7.24 once the exploration output law's finite
prefix histories have been verified.  Unlike the older full-domination adapter above, this
theorem needs only the finite ratio-free sequential inequalities and proves probability one. -/
theorem infinite_siteSet_probability_pos_of_prefixSequential
    {V : Type*} [Countable V] [DecidableEq V] (e : ℕ ≃ V)
    (μ : Measure (Set V)) [IsProbabilityMeasure μ] (p : I) (hp : 0 < (p : ℝ))
    (hseq : ∀ n,
      HasFiniteSequentialLowerBound (enumerationPrefixLaw e n μ) (p : ℝ)) :
    0 < μ.real {η : Set V | η.Infinite} := by
  rw [infinite_siteSet_probability_eq_one_of_prefixSequential e μ p hp hseq]
  norm_num

/-- A history-wise ratio-free success estimate automatically gives the usual conditional ratio
on every positive-mass history. -/
theorem historySuccessLowerBound_conditional_of_pos {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {success history : Set Ω} {γ : ℝ}
    (h : HistorySuccessLowerBound μ success history γ)
    (hh : 0 < μ.real history) :
    γ ≤ μ.real (success ∩ history) / μ.real history :=
  h.conditionalRatio hh

end Percolation
