import Percolation.Critical.HalfSpaceBricks
import Percolation.Critical.SiteExplorationDomination
import Percolation.Planar.Crossings
import Percolation.Planar.CrossingMenger
import Percolation.Core.EdgeMenger
import Percolation.Core.EdgeMengerToSet
import Percolation.Bernoulli.SequentialDomination
import Percolation.Bernoulli.SequentialDominationCountable
import Percolation.Critical.ExplorationLaw
import Percolation.Critical.StaticBlockTranslation
import Percolation.Critical.StaticBlockAdjacency
import Percolation.Critical.RegionTranslation
import Percolation.Critical.RegionSymmetry
import Percolation.Critical.SiteSymmetry

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

example (d k l : ℕ) (hkl : k ≤ l) :
    slabCriticalProbability d l ≤ slabCriticalProbability d k :=
  slabCriticalProbability_antitone d hkl

example (d k : ℕ) :
    cubicCriticalProbability d ≤ slabCriticalProbability d k :=
  cubicCriticalProbability_le_slabCriticalProbability d k

example : Fintype.card (BrickFacetKind 2) = 6 := by native_decide
example : Fintype.card (BrickFacetKind 3) = 12 := by native_decide
example : Fintype.card (BrickFacetKind 4) = 20 := by native_decide

example (d : ℕ) (G : SimpleGraph (Fin d)) : siteTheta G (0 : I) = 0 :=
  siteTheta_zero G

example {V W : Type*} [Countable V] [Countable W]
    {G : SimpleGraph V} {H : SimpleGraph W} (F : G ≃g H) (p : I) :
    siteTheta H p = siteTheta G p :=
  siteTheta_graphIso F p

example {V W : Type*} [Countable V] [Countable W]
    {G : SimpleGraph V} {H : SimpleGraph W} (F : G ≃g H) :
    siteCriticalProbability H = siteCriticalProbability G :=
  siteCriticalProbability_graphIso F

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

example (m n r : ℕ) (ω : EdgeConfiguration 2) :
    ω ∈ interiorDepth r (squareRectangleCrossingEvent m n) ↔
      HasEdgeDisjointSquareRectangleCrossings m n (r + 1) ω :=
  mem_interiorDepth_squareRectangleCrossingEvent_iff m n r ω

example {m n r : ℕ} (hm : 1 ≤ m) (ω : EdgeConfiguration 2) :
    ω ∈ interiorDepth r (squareRectangleCrossingEvent m n) ↔
      r + 1 ≤ maxEdgeDisjointSquareRectangleCrossings m n ω :=
  mem_interiorDepth_squareRectangleCrossingEvent_iff_le_max hm ω

example {p₁ p₂ : I} (h12 : (p₁ : ℝ) < p₂) {r : ℕ} (hr : 1 ≤ r)
    {m n : ℕ} (hm : 1 ≤ m) :
    (bernoulliBondMeasure 2 p₂).real
        {ω | maxEdgeDisjointSquareRectangleCrossings m n ω ≤ r} ≤
      ((p₂ : ℝ) / ((p₂ : ℝ) - p₁)) ^ r *
        (1 - (bernoulliBondMeasure 2 p₁).real (squareRectangleCrossingEvent m n)) :=
  bernoulliBondMeasure_real_maxCrossings_le_le h12 hr hm

example (d : ℕ) (F : Set (Cubic d)) (k : ℕ) :
    cubicDilatedThickening d F k = cubicDilatedMinkowskiSum d F k :=
  cubicDilatedThickening_eq_minkowskiSum d F k

example (d : ℕ) (A : Set (Cubic d)) (x y : Cubic d) :
    regionCriticalProbability d (cubicTranslateRegion x y A) =
      regionCriticalProbability d A :=
  regionCriticalProbability_translate A x y

example {d : ℕ} (F : cubicGraph d ≃g cubicGraph d) (A : Set (Cubic d)) :
    regionCriticalProbability d (cubicGraphIsoRegion F A) =
      regionCriticalProbability d A :=
  regionCriticalProbability_graphIso F A

example {d : ℕ} (e : Fin d ≃ Fin d) (A : Set (Cubic d)) :
    regionCriticalProbability d
        (cubicGraphIsoRegion (cubicCoordinatePermutationIso e) A) =
      regionCriticalProbability d A :=
  regionCriticalProbability_coordinatePermutation e A

example {d : ℕ} (i : Fin d) (A : Set (Cubic d)) :
    regionCriticalProbability d
        (cubicGraphIsoRegion (cubicCoordinateReflectionIso i) A) =
      regionCriticalProbability d A :=
  regionCriticalProbability_coordinateReflection i A

example (d : ℕ) (p : I) (ε : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    KDependent (cubicGraph d) (3 * d) (epsilonGoodBlockLaw d p ε n) :=
  epsilonGoodBlockLaw_kDependent d p ε hn

/-- Stationarity is an equality of the full translated site-field laws, not merely equality of
the one-site marginals. -/
example (d : ℕ) (p : I) (ε : ℝ) (n : ℕ) (x y : Cubic d) :
    (epsilonGoodBlockLaw d p ε n).map (cubicSiteTranslationPullback x y) =
      epsilonGoodBlockLaw d p ε n :=
  epsilonGoodBlockLaw_map_cubicSiteTranslationPullback d p ε n x y

example {d : ℕ} {G : SimpleGraph (Cubic d)} (hG : G ≤ cubicGraph d)
    {u v : Cubic d} (w : G.Walk u v) (i : Fin d) (a : ℤ)
    (hu : a ≤ u i) (hv : v i ≤ a) :
    ∃ z : Cubic d, ∃ q : G.Walk u z,
      z i = a ∧ (∀ x ∈ q.support, a ≤ x i) ∧
        ∀ x ∈ q.support, x ∈ w.support :=
  exists_cubicWalk_prefix_to_level_of_end_le hG w i a hu hv

/-- Equation (7.59) is tested at its source-facing event interface: neighboring good blocks'
selected clusters share an actual lattice vertex. -/
example {d n : ℕ} (p : I) (ε : ℝ) (ω : EdgeConfiguration d)
    (x : Cubic d) (a : CubicDirection d)
    (hx : ω ∈ epsilonGoodBoxEvent d p ε (epsilonGoodBlockCenter n x) n)
    (hy : ω ∈ epsilonGoodBoxEvent d p ε
      (epsilonGoodBlockCenter n (cubicStepFrom x a)) n) :
    ∃ u : Cubic d,
      u ∈ finiteBoxGraphComponentVertices
        (finiteBoxGraphLargestComponent (epsilonGoodBlockCenter n x) n
          (finiteBoxOpenGraph d ω (epsilonGoodBlockCenter n x) n)) ∧
      u ∈ finiteBoxGraphComponentVertices
        (finiteBoxGraphLargestComponent
          (epsilonGoodBlockCenter n (cubicStepFrom x a)) n
          (finiteBoxOpenGraph d ω
            (epsilonGoodBlockCenter n (cubicStepFrom x a)) n)) :=
  finiteBoxGraphLargestComponents_inter_of_mem_goodBoxEvents p ε ω x a hx hy

example (d : ℕ) (p : I) (ε : ℝ) (n : ℕ) (x y : Cubic d) :
  (bernoulliBondMeasure d p).real (epsilonGoodBoxEvent d p ε x n) =
      (bernoulliBondMeasure d p).real (epsilonGoodBoxEvent d p ε y n) :=
  bernoulliBondMeasure_real_epsilonGoodBoxEvent_eq p ε x y n

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

example {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (A B : Finset V) (k : ℕ) :
    EdgeMenger.IsEdgeReachableBetweenFinsets G k A B ↔
      ∃ P : Fin k → EdgeMenger.WalkBetweenFinsets G A B,
        Pairwise fun i j ↦ (P i).walk.edges.Disjoint (P j).walk.edges :=
  EdgeMenger.isEdgeReachableBetweenFinsets_iff_exists_pairwise_edgeDisjoint_walks

/-- Shared terminals correctly permit arbitrarily many zero-edge walks; the terminal gadget
must not introduce a spurious capacity-one bottleneck at that vertex. -/
example {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (A B : Finset V) (v : V) (hvA : v ∈ A) (hvB : v ∈ B) (k : ℕ) :
    EdgeMenger.IsEdgeReachableBetweenFinsets G k A B := by
  intro s hs
  exact ⟨v, hvA, v, hvB, .nil, by simp⟩

/-- With no coordinates, the ratio-free prefix hypothesis is vacuous and the finite sequential
criterion correctly compares every probability law with the unique iid law. -/
example (μ : Measure (Set (Fin 0))) [IsProbabilityMeasure μ] (p : I) :
    StochasticallyDominates μ setBer((Set.univ : Set (Fin 0)), p) := by
  apply finiteSequentialLowerBound_stochasticallyDominates μ p
  intro i hi
  omega

example {V : Type*} [DecidableEq V] (e : ℕ ≃ V) (R : Finset V) (v : V)
    (hv : v ∈ R) :
    ∃ i : Fin (enumerationSupportLength e R), enumerationPrefixEmbedding e _ i = v :=
  support_subset_range_enumerationPrefixEmbedding e R hv

end Percolation
