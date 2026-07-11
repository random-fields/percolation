import Percolation.Critical.HalfSpaceBricks
import Percolation.Critical.SiteExplorationDomination
import Percolation.Planar.Crossings
import Percolation.Core.EdgeMenger
import Percolation.Bernoulli.SequentialDomination

/-!
# Chapter 7 infrastructure oracle tests

Small compiling applications and endpoint checks generated from the informal Chapter 7
statements.  These tests intentionally exercise conventions that could otherwise conceal junk
values.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval

example (k : ℕ) : cubicSlab 2 k = Set.univ := cubicSlab_two k

example : Fintype.card (BrickFacetKind 2) = 6 := by native_decide
example : Fintype.card (BrickFacetKind 3) = 12 := by native_decide
example : Fintype.card (BrickFacetKind 4) = 20 := by native_decide

example (d : ℕ) (G : SimpleGraph (Fin d)) : siteTheta G (0 : I) = 0 :=
  siteTheta_zero G

example (d n N : ℕ) (x : Cubic d) : twoArmSeparationEvent d n N x x = ∅ :=
  twoArmSeparationEvent_self d n N x

example (d m n : ℕ) (x : Cubic d) (h : 2 * n < m) :
    secondMacroscopicClusterEvent d m n x = ∅ :=
  secondMacroscopicClusterEvent_eq_empty_of_two_mul_lt x h

example (n : ℕ) : squareRectangleCrossingEvent 0 n = Set.univ :=
  squareRectangleCrossingEvent_zero_left n

example : siteSquareRectangleCrossingEvent 0 0 =
    {η : Set SquareVertex | squareVertex 0 0 ∈ η} :=
  siteSquareRectangleCrossingEvent_zero

example (m n : ℕ) (hm : 1 ≤ m) :
    maxEdgeDisjointSquareRectangleCrossings m n (∅ : EdgeConfiguration 2) = 0 :=
  maxEdgeDisjointSquareRectangleCrossings_empty hm

example (d : ℕ) (F : Set (Cubic d)) (k : ℕ) :
    cubicDilatedThickening d F k = cubicDilatedMinkowskiSum d F k :=
  cubicDilatedThickening_eq_minkowskiSum d F k

example (d : ℕ) (p : I) (ε : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    KDependent (cubicGraph d) (3 * d) (epsilonGoodBlockLaw d p ε n) :=
  epsilonGoodBlockLaw_kDependent d p ε hn

example {d m n : ℕ} (hd : 2 ≤ d) (i : Fin d) (ω : EdgeConfiguration d)
    (hn : n < 2 * m) : seededBoundaryPoints d i m n ω = ∅ :=
  seededBoundaryPoints_eq_empty_of_lt_two_mul hd i ω hn

/-- Reversing the density order would fail the iid stochastic-order oracle: the proved direction
is that the law at the larger density dominates the law at the smaller density. -/
example {ι : Type*} [Countable ι] {p q : I} (hpq : p ≤ q) :
    StochasticallyDominates setBer((Set.univ : Set ι), q)
      setBer((Set.univ : Set ι), p) :=
  setBernoulli_stochasticallyDominates hpq

example {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (u v : V) (k : ℕ) :
    G.IsEdgeReachable k u v ↔
      ∃ P : Fin k → G.Walk u v,
        (∀ i, (P i).IsPath) ∧
          Pairwise fun i j ↦ (P i).edges.Disjoint (P j).edges :=
  EdgeMenger.isEdgeReachable_iff_exists_pairwise_edgeDisjoint_paths

/-- With no coordinates, the ratio-free prefix hypothesis is vacuous and the finite sequential
criterion correctly compares every probability law with the unique iid law. -/
example (μ : Measure (Set (Fin 0))) [IsProbabilityMeasure μ] (p : I) :
    StochasticallyDominates μ setBer((Set.univ : Set (Fin 0)), p) := by
  apply finiteSequentialLowerBound_stochasticallyDominates μ p
  intro i hi
  omega

end Percolation
