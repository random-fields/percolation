import Percolation.Critical.HalfSpaceBricks
import Percolation.Critical.FiniteSiteExplorationCompleteness
import Percolation.Critical.FiniteExplorationBellman
import Percolation.Critical.AdaptiveDecisionOutcome
import Percolation.Critical.AdaptiveDecisionRealization
import Percolation.Critical.AdaptiveTargetExhaustion
import Percolation.Critical.AdaptiveRegionShells
import Percolation.Critical.AdaptiveSiteExplorationTheorem
import Percolation.Critical.SiteExplorationDomination
import Percolation.Planar.Crossings
import Percolation.Planar.CrossingMenger
import Percolation.Core.EdgeMenger
import Percolation.Core.EdgeMengerToSet
import Percolation.Bernoulli.SequentialDomination
import Percolation.Bernoulli.SequentialDominationCountable
import Percolation.Bernoulli.TailZeroOne
import Percolation.Bernoulli.FiniteRangeVariance
import Percolation.Critical.ExplorationLaw
import Percolation.Critical.StaticBlockTranslation
import Percolation.Critical.StaticBlockAdjacency
import Percolation.Critical.StaticBlockPath
import Percolation.Critical.RegionTranslation
import Percolation.Critical.RegionSymmetry
import Percolation.Critical.SiteSymmetry
import Percolation.Critical.InfiniteClusterDensity
import Percolation.Critical.StaticCoalescence
import Percolation.Critical.StaticGoodAssembly
import Percolation.Critical.StaticLargeCrossing
import Percolation.Critical.SlabConnectivity
import Percolation.Critical.FiniteSlabLowerBound
import Percolation.Critical.FiniteSlabTLowerBound
import Percolation.Critical.StaticRenormalizationFromSlab
import Percolation.Critical.InfiniteClusterZeroOne
import Percolation.Critical.BoundaryContacts
import Percolation.Critical.BoundaryOrthants
import Percolation.Critical.SeedAmplification
import Percolation.Critical.RestartSprinkling
import Percolation.Critical.DynamicSteeringSymmetry
import Percolation.Critical.AdaptiveAnswerHistory
import Percolation.Critical.DynamicBlockAnswerLaw
import Percolation.Critical.AdaptiveQueryDomination
import Percolation.Critical.AdaptiveDecisionTree
import Percolation.Critical.FiniteExplorationTermination
import Percolation.Critical.RestartGeometry
import Percolation.Critical.DynamicBlockGeometry
import Percolation.Critical.DynamicRevealBudget
import Percolation.Critical.DynamicSteering
import Percolation.Critical.RootedSiteExploration
import Percolation.Critical.AdaptiveExploration
import Percolation.Critical.DynamicBlockCertificate
import Percolation.Critical.BlockSuccessComposition
import Percolation.Critical.DynamicBlockParameters
import Percolation.Critical.ExplorationHistory
import Percolation.Bernoulli.CouplingSymmetry
import Percolation.Critical.StaticSecondCluster
import Percolation.Critical.StaticAnnularPeeling
import Percolation.Critical.StaticLogInset
import Percolation.Critical.HalfSpaceCriticalAssembly
import Percolation.Critical.SlabLimitAssembly

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

example {V : Type*} [DecidableEq V] [LinearOrder V]
    (E : SiteExploration V) (answer : V → Bool) (root : V)
    (hinitial : E.OpenRootedAt root E.initial)
    (hInf : (E.occupiedLimit answer).Infinite) :
    hasInfiniteSiteCluster E.graph (E.occupiedLimit answer) :=
  E.hasInfiniteSiteCluster_occupiedLimit_of_infinite answer root hinitial hInf

example {V : Type*} [Countable V] [DecidableEq V] [LinearOrder V]
    (E : SiteExploration V) (μ : Measure (Set V)) [IsProbabilityMeasure μ]
    (e : ℕ ≃ V) (p : I) (hp : 0 < (p : ℝ)) (root : V)
    (hinitial : E.OpenRootedAt root E.initial)
    (hseq : E.OccupiedLimitHasPrefixLowerBound μ e (p : ℝ)) :
    0 < μ.real {η : Set V |
      hasInfiniteSiteCluster E.graph (E.occupiedLimit (configurationAnswer η))} :=
  siteExploration_infinite_probability_pos E μ e p hp root hinitial hseq

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

example {d n : ℕ} (p : I) (ε : ℝ) (ω : EdgeConfiguration d)
    {x y : Cubic d} (w : (cubicGraph d).Walk x y)
    (hgood : ∀ z ∈ w.support,
      ω ∈ epsilonGoodBoxEvent d p ε (epsilonGoodBlockCenter n z) n)
    {u v : Cubic d}
    (hu : u ∈ epsilonGoodBlockClusterVertices d ω n x)
    (hv : v ∈ epsilonGoodBlockClusterVertices d ω n y) :
    (cubicOpenGraph d ω).Reachable u v :=
  epsilonGoodBlockClusterVertices_reachable_of_good_walk p ε ω w hgood hu hv

example {d n : ℕ} (p : I) (ε : ℝ) (ω : EdgeConfiguration d)
    {x y : Cubic d} (w : (cubicGraph d).Walk x y)
    (hgood : ∀ z ∈ w.support,
      ω ∈ epsilonGoodBoxEvent d p ε (epsilonGoodBlockCenter n z) n)
    (i : Fin d) :
    ∃ u ∈ cubicBoxFace d (epsilonGoodBlockCenter n x) n i false,
      ∃ v ∈ cubicBoxFace d (epsilonGoodBlockCenter n y) n i true,
        ω ∈ connectionEvent d u v :=
  exists_connectionEvent_between_faces_of_good_walk p ε ω w hgood i

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

example {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (s : Finset ι) (hs : s.Nonempty) (X : ι → Ω → ℝ)
    (hX : ∀ i ∈ s, MemLp (X i) 2 μ)
    (N : ι → Finset ι) (D : ℕ)
    (hNcard : ∀ i ∈ s, (N i).card ≤ D)
    (hcovZero : ∀ i ∈ s, ∀ j ∈ s, j ∉ N i →
      ProbabilityTheory.covariance (X i) (X j) μ = 0)
    (hcovLe : ∀ i ∈ s, ∀ j ∈ s,
      ProbabilityTheory.covariance (X i) (X j) μ ≤ 1) :
    ProbabilityTheory.variance
        (fun ω ↦ (∑ i ∈ s, X i ω) / (s.card : ℝ)) μ ≤
      (D : ℝ) / s.card :=
  variance_finset_average_le_of_finite_covariance_neighborhood
    μ s hs X hX N D hNcard hcovZero hcovLe

example (d : ℕ) (x : Cubic d) :
    translatedCylinderEvent x (infiniteClusterVertexEvent d cubicOrigin) =
      infiniteClusterVertexEvent d x :=
  translatedCylinderEvent_infiniteClusterOrigin d x

/-- The density law is tested in the source range `d ≥ 2`; the implementation exposes the
sharp nondegenerate assumption `1 ≤ d`. -/
example (p : I) {ε : ℝ} (hε : 0 < ε) :
    Filter.Tendsto
      (fun n ↦ (bernoulliBondMeasure 2 p).real
        {ω | ε ≤
          |infiniteClusterVertexDensity 2 (cubicMetricBox 2 cubicOrigin n) ω -
            theta 2 p|})
      Filter.atTop (nhds 0) :=
  infiniteClusterVertexDensity_measureReal_tendsto_zero (by omega) p hε

example (p : I) (hp : 0 < theta 2 p) {δ : ℝ} (hδ : 0 < δ) :
    Filter.Tendsto
      (fun n ↦ (bernoulliBondMeasure 2 p).real
        (denseInfiniteClusterVertexEvent 2 p δ n))
      Filter.atTop (nhds 1) :=
  denseInfiniteClusterVertexEvent_probability_tendsto_one (by omega) p hp hδ

example {d : ℕ} {p : I} {δ : ℝ} {n : ℕ} {ω : EdgeConfiguration d} :
    ω ∈ denseInfiniteClusterVertexEvent d p δ n ↔
      (1 - δ) * theta d p * ((cubicMetricBox d cubicOrigin n).card : ℝ) ≤
        (infiniteClusterVerticesIn d (cubicMetricBox d cubicOrigin n) ω).card :=
  mem_denseInfiniteClusterVertexEvent_iff_card

example {d n N : ℕ} {ω : EdgeConfiguration d} {x y : Cubic d}
    (hx : x ∈ cubicMetricBox d cubicOrigin n)
    (hy : y ∈ cubicMetricBox d cubicOrigin n)
    (hnN : n ≤ N)
    (hxInf : hasInfiniteOpenClusterFrom d ω x)
    (hyInf : hasInfiniteOpenClusterFrom d ω y)
    (hnot : ω ∉ twoArmSeparationEvent d n N x y) :
    ω ∈ connectionEventIn d (cubicBoxEdges d cubicOrigin N) x y :=
  connectionEventIn_of_infinite_of_not_twoArm hx hy hnN hxInf hyInf hnot

example {d n N : ℕ} (p : I) (hnN : n ≤ N) :
    (bernoulliBondMeasure d p).real (infiniteClusterCoalescenceEvent d n N)ᶜ ≤
      ∑ x ∈ cubicMetricBox d cubicOrigin n,
        ∑ y ∈ cubicMetricBox d cubicOrigin n,
          (bernoulliBondMeasure d p).real (twoArmSeparationEvent d n N x y) :=
  bernoulliBondMeasure_real_infiniteClusterCoalescenceEvent_compl_le_sum p hnN

example {d n L : ℕ} {x : Cubic d} :
    x ∈ finiteThickSlabSVertices d n L ↔
      ∀ i : Fin d,
        if i.val < 2 then (x i).natAbs ≤ n else 0 ≤ x i ∧ x i ≤ L :=
  mem_finiteThickSlabSVertices_iff

example {d n L : ℕ} {x : Cubic d} :
    x ∈ finiteThickSlabTVertices d n L ↔
      ∀ i : Fin d,
        if i.val + 1 = d then 0 ≤ x i ∧ x i ≤ L else (x i).natAbs ≤ n :=
  mem_finiteThickSlabTVertices_iff

example {d n L : ℕ} {x : Cubic d} (hx : x ∈ finiteThickSlabSVertices d n L) :
    finiteThickSlabSConnectionEvent d n L x x = Set.univ :=
  finiteThickSlabSConnectionEvent_self hx

example (d m L : ℕ) (k : Fin 4) :
    slabCornerVertex d m k ∈ slabCornerBoxVertices d m L :=
  slabCornerVertex_mem d m L k

example (d : ℕ) (hd : 2 ≤ d) (p : I) (m L : ℕ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hprob : ∀ k : Fin 4, δ ≤ (bernoulliBondMeasure d p).real
      (slabCornerConnectionEvent d hd m L k)) :
    δ ^ 4 ≤ (bernoulliBondMeasure d p).real
      (allSlabCornerConnectionEvents d hd m L) :=
  slabCornerConnection_lowerBound_pow_four d hd p m L hδ hprob

example {d : ℕ} (p : I) {A B : Set (EdgeConfiguration d)}
    (E : Finset (CubicEdge d)) (hAinc : IsIncreasingEvent A) (hAm : MeasurableSet A)
    (hsub : A ∩ openEdgeSetEvent d E ⊆ B) :
    (bernoulliBondMeasure d p).real A * (p : ℝ) ^ E.card ≤
      (bernoulliBondMeasure d p).real B :=
  bernoulliBondMeasure_real_mul_pow_card_le_of_inter_openEdgeSet_subset
    p E hAinc hAm hsub

example {ι : Type*} (A : Set (Set ι)) : upwardDistanceAtMost 0 A = A :=
  upwardDistanceAtMost_zero A

example {d : ℕ} {A : Set (EdgeConfiguration d)}
    (hAinc : IsIncreasingEvent A) (hAm : MeasurableSet A)
    {p₁ p₂ : I} (h12 : (p₁ : ℝ) < p₂) (r : ℕ) :
    (((p₂ : ℝ) - p₁) / (1 - (p₁ : ℝ))) ^ r *
        (bernoulliBondMeasure d p₁).real (upwardDistanceAtMost r A) ≤
      (bernoulliBondMeasure d p₂).real A :=
  hAinc.bernoulliBondMeasure_real_upwardDistanceAtMost_le hAm h12 r

example {d m L : ℕ} (hd : 2 ≤ d) {u v : Cubic d}
    (hu : u ∈ slabCornerBoxVertices d m L)
    (hv : v ∈ slabCornerBoxVertices d m L)
    (hagrees : ∀ i : Fin d, i.val < 2 → u i = v i)
    (ω : EdgeConfiguration d) :
    ω ∈ upwardDistanceAtMost ((d - 2) * L)
      (connectionEventWithinVertices d
        (slabCornerBoxVertices d m L : Set (Cubic d)) u v) :=
  mem_upwardDistanceAtMost_connectionWithin_slabCorner_of_agree_first_two
    hd hu hv hagrees ω

/-- A transverse edge contracts to a stutter under the first-two-coordinate projection. -/
example (x : Cubic 3) (b : Bool) :
    cubicFirstTwoProjection (by decide)
        (cubicStepFrom x (⟨2, by decide⟩, b)) =
      cubicFirstTwoProjection (by decide) x := by
  ext i
  fin_cases i <;>
    simp [cubicFirstTwoProjection, cubicRestrict, cubicStepFrom]

example {d : ℕ} (hd : 2 ≤ d) {x₁ y₁ x₂ y₂ : Cubic d}
    (w₁ : (cubicGraph d).Walk x₁ y₁) (w₂ : (cubicGraph d).Walk x₂ y₂) :
    (∃ z, z ∈ (projectCubicWalkFirstTwo hd w₁).support ∧
        z ∈ (projectCubicWalkFirstTwo hd w₂).support) ↔
      ∃ u ∈ w₁.support, ∃ v ∈ w₂.support,
        ∀ i : Fin d, i.val < 2 → u i = v i :=
  projectCubicWalkFirstTwo_support_inter_iff hd w₁ w₂

example {ι : Type*} {r s : ℕ} {A : Set (Set ι)} (hrs : r ≤ s) :
    upwardDistanceAtMost r A ⊆ upwardDistanceAtMost s A :=
  upwardDistanceAtMost_mono_radius hrs

example {d n k : ℕ} {i : Fin d} {φ : ℤ} {x : Cubic d}
    (hk : 1 ≤ k) (hx : x ∈ coordinateHyperplaneVertices d n i φ) :
    forwardTwoArmSeparationEvent d n i φ k x x = ∅ :=
  forwardTwoArmSeparationEvent_self_eq_empty hk hx

example {d n k : ℕ} {i : Fin d} {φ : ℤ} {x y : Cubic d}
    (hfar : (n : ℤ) < φ + k) :
    forwardTwoArmSeparationEvent d n i φ k x y = ∅ :=
  forwardTwoArmSeparationEvent_eq_empty_of_nat_lt hfar

example {d n k l : ℕ} {i : Fin d} {φ : ℤ} {x y : Cubic d}
    (hx : x ∈ coordinateHyperplaneVertices d n i φ)
    (hy : y ∈ coordinateHyperplaneVertices d n i φ) (hkl : k ≤ l) :
    forwardTwoArmSeparationEvent d n i φ l x y ⊆
      forwardTwoArmSeparationEvent d n i φ k x y :=
  forwardTwoArmSeparationEvent_anti_width hx hy hkl

example {d m n : ℕ} (hd : 1 ≤ d) (p : I) {q : ℝ} (hq : 0 ≤ q)
    (hpair : ∀ i : Fin d, ∀ x ∈ cubicMetricBox d cubicOrigin n,
      ∀ y ∈ cubicMetricBox d cubicOrigin n, x i = y i →
        (bernoulliBondMeasure d p).real
          (forwardTwoArmSeparationEvent d n i (x i) m x y) ≤ q) :
    (bernoulliBondMeasure d p).real
        (secondMacroscopicClusterEvent d m n cubicOrigin) ≤
      d * (2 * n + 1 : ℝ) ^ (2 * d) * q :=
  secondMacroscopicCluster_probability_le_boxPolynomial_mul hd p hq hpair

example {q : ℝ} {M : ℕ} (hq0 : 0 < q) (hq1 : q < 1) (hM : 1 ≤ M) :
    0 < secondClusterPeelingRate q M :=
  secondClusterPeelingRate_pos hq0 hq1 hM

example {q : ℝ} {m M : ℕ} (hq0 : 0 < q) (hq1 : q < 1)
    (hM : 1 ≤ M) (hm : M ≤ m) :
    q ^ (m / M) ≤ Real.exp (-(secondClusterPeelingRate q M) * m) :=
  pow_natDiv_le_exp_neg_secondClusterPeelingRate hq0 hq1 hM hm

/-- Oracle for the exact translated/rotated identification used in the 7.104 strip step. -/
example {d n L : ℕ} (hd : 1 ≤ d) (i : Fin d) (r : ℤ)
    (hrlower : -(n : ℤ) ≤ r) (hrupper : r + L ≤ n) (x : Cubic d) :
    coordinateBandToLastIso hd i r x ∈ finiteThickSlabTVertices d n L ↔
      x ∈ coordinateClosedStripVertices d n i r (r + L) :=
  coordinateBandToLastIso_mem_finiteThickSlabTVertices_iff
    hd i r hrlower hrupper x

/-- The one-block estimate is derived from the actual finite-slab package, rather than accepted
as a theorem parameter. -/
example {d n L : ℕ} (hd : 1 ≤ d) (p : I) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hslab : UniformFiniteSlabConnectionLowerBound d p L δ)
    (hn : 1 ≤ n) {i : Fin d} {φ : ℤ} {x y : Cubic d}
    (hx : x ∈ coordinateHyperplaneVertices d n i φ)
    (hy : y ∈ coordinateHyperplaneVertices d n i φ) :
    ∀ j,
      (bernoulliBondMeasure d p).real
          (forwardTwoArmSeparationEvent d n i φ ((j + 1) * (L + 2)) x y) ≤
        (1 - (p : ℝ) ^ 2 * δ) * (bernoulliBondMeasure d p).real
          (forwardTwoArmSeparationEvent d n i φ (j * (L + 2)) x y) :=
  forwardTwoArmSeparation_uniform_block_step_of_uniformFiniteSlab
    hd p hδ0 hδ1 hslab hn hx hy

/-- Exact polynomial-times-exponential 7.104 conclusion from Lemma 7.78's source-facing
finite-slab conclusion. -/
example {d L : ℕ} (hd : 1 ≤ d) (p : I) (hp0 : 0 < (p : ℝ))
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hslab : UniformFiniteSlabConnectionLowerBound d p L δ) :
    ∃ μ : ℝ, 0 < μ ∧ ∀ m n : ℕ, 1 ≤ m → 1 ≤ n →
      (bernoulliBondMeasure d p).real
          (secondMacroscopicClusterEvent d m n cubicOrigin) ≤
        d * (2 * n + 1 : ℝ) ^ (2 * d) * Real.exp (-μ * m) :=
  exists_secondMacroscopicCluster_probability_le_exp_of_uniformFiniteSlab
    hd p hp0 hδ0 hδ1 hslab

example {d : ℕ} (p : I) (r R : ℕ → ℕ) (q : ℕ → ℝ)
    (hrR : ∀ n, r n ≤ R n)
    (hpair : ∀ n, ∀ x ∈ cubicMetricBox d cubicOrigin (r n),
      ∀ y ∈ cubicMetricBox d cubicOrigin (r n),
        (bernoulliBondMeasure d p).real
          (twoArmSeparationEvent d (r n) (R n) x y) ≤ q n)
    (hdecay : Filter.Tendsto
      (fun n ↦ ((cubicMetricBox d cubicOrigin (r n)).card : ℝ) ^ 2 * q n)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun n ↦ (bernoulliBondMeasure d p).real
        (infiniteClusterCoalescenceEvent d (r n) (R n)))
      Filter.atTop (nhds 1) :=
  infiniteClusterCoalescenceEvent_probability_tendsto_one_of_twoArm_bound
    p r R q hrR hpair hdecay

example {d n N M : ℕ} (p : I) {x y : Cubic d} {q : ℝ}
    (hnN : n ≤ N) (hq : 0 ≤ q)
    (hstep : ∀ k,
      (bernoulliBondMeasure d p).real
          (annularPeelingSeparationEvent d n M (k + 1) x y) ≤
        q * (bernoulliBondMeasure d p).real
          (annularPeelingSeparationEvent d n M k x y)) :
    (bernoulliBondMeasure d p).real (twoArmSeparationEvent d n N x y) ≤
      q ^ ((N - n) / M) :=
  twoArmSeparation_probability_le_pow_of_annular_block_step p hnN hq hstep

example {d r L : ℕ} (hd : 2 ≤ d) (j : Fin d) :
    ∃ i : Fin d, ∃ positive : Bool,
      boxShellChainCorner d (boxShellOuterRadius r L) j.castSucc ∈
          boxShellSliceVertices d r L i positive ∧
        boxShellChainCorner d (boxShellOuterRadius r L) j.succ ∈
          boxShellSliceVertices d r L i positive :=
  exists_boxShellSlice_pair_chainCorners hd j

example {d r L : ℕ} (hd : 2 ≤ d) (p : I) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hslab : UniformFiniteSlabConnectionLowerBound d p L δ)
    {iu iv : Fin d} {su sv : Bool} {u v : Cubic d}
    (hu : u ∈ cubicBoxSurface d cubicOrigin r)
    (hv : v ∈ cubicBoxSurface d cubicOrigin r)
    (huface : if su then u iu = r else u iu = -(r : ℤ))
    (hvface : if sv then v iv = r else v iv = -(r : ℤ)) :
    (p : ℝ) ^ 2 * δ ^ (d + 2) ≤ (bernoulliBondMeasure d p).real
      (boxShellBridgeEvent hd r L iu su u iv sv v) :=
  boxShellBridge_probability_ge_of_uniformFiniteSlab
    hd p hδ0 hslab hu hv huface hvface

example {d n k L : ℕ} (hd : 2 ≤ d) (p : I) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hslab : UniformFiniteSlabConnectionLowerBound d p L δ)
    (x y : Cubic d) :
    (bernoulliBondMeasure d p).real
        (annularPeelingSeparationEvent d n (L + 1) (k + 1) x y) ≤
      (1 - (p : ℝ) ^ 2 * δ ^ (d + 2)) *
        (bernoulliBondMeasure d p).real
          (annularPeelingSeparationEvent d n (L + 1) k x y) :=
  annularPeeling_probability_block_step_of_uniformFiniteSlab hd p hδ0 hslab x y

example {d n N : ℕ} (p : I) {x y : Cubic d} (hnN : n < N) :
    (bernoulliBondMeasure d p).real (twoArmSeparationEvent d n N x y) ≤
      1 - (1 - (p : ℝ)) ^ (2 * d) :=
  twoArmSeparation_probability_le_one_sub_isolation p hnN

example {d n N L : ℕ} (hd : 2 ≤ d) (p : I) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hslab : UniformFiniteSlabConnectionLowerBound d p L δ)
    (hnN : n ≤ N) (x y : Cubic d) :
    (bernoulliBondMeasure d p).real (twoArmSeparationEvent d n N x y) ≤
      (1 - (p : ℝ) ^ 2 * δ ^ (d + 2)) ^ ((N - n) / (L + 1)) :=
  twoArmSeparation_probability_le_pow_of_uniformFiniteSlab
    hd p hδ0 hslab hnN x y

example {d L : ℕ} (hd : 2 ≤ d) (p : I) (hp0 : 0 < (p : ℝ))
    (hp1 : (p : ℝ) < 1) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hslab : UniformFiniteSlabConnectionLowerBound d p L δ) :
    ∃ ξ : ℝ, 0 < ξ ∧ ∀ n N : ℕ, n < N → ∀ x y : Cubic d,
      (bernoulliBondMeasure d p).real (twoArmSeparationEvent d n N x y) ≤
        Real.exp (-ξ * ((N - n : ℕ) : ℝ)) :=
  exists_twoArmSeparation_probability_le_exp_of_uniformFiniteSlab
    hd p hp0 hp1 hδ0 hδ1 hslab

example {d L : ℕ} (hd : 2 ≤ d) (p : I) (hp0 : 0 < (p : ℝ))
    (hp1 : (p : ℝ) < 1) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hslab : UniformFiniteSlabConnectionLowerBound d p L δ) :
    ∃ ξ : ℝ, 0 < ξ ∧ ∀ n : ℕ, 1 ≤ n → ∀ a : ℝ, 1 < a →
      ∀ x ∈ cubicMetricBox d cubicOrigin n,
      ∀ y ∈ cubicMetricBox d cubicOrigin n,
        (bernoulliBondMeasure d p).real
            (twoArmSeparationEvent d n (scaledBoxRadius a n) x y) ≤
          Real.exp (-(n : ℝ) * (a - 1) * ξ) :=
  exists_scaledTwoArmSeparation_probability_le_exp_of_uniformFiniteSlab
    hd p hp0 hp1 hδ0 hδ1 hslab

example (d : ℕ) {ξ : ℝ} (hξ : 0 < ξ) :
    Filter.Tendsto
      (fun n : ℕ ↦ ((cubicMetricBox d cubicOrigin n).card : ℝ) ^ 2 *
        Real.exp (-ξ * n))
      Filter.atTop (nhds 0) :=
  tendsto_cubicMetricBox_card_sq_mul_exp_neg_nat d hξ

example {d L : ℕ} (hd : 2 ≤ d) (p : I) (hp0 : 0 < (p : ℝ))
    (hp1 : (p : ℝ) < 1) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hslab : UniformFiniteSlabConnectionLowerBound d p L δ) :
    Filter.Tendsto
      (fun n ↦ (bernoulliBondMeasure d p).real
        (infiniteClusterCoalescenceEvent d n (2 * n)))
      Filter.atTop (nhds 1) :=
  infiniteClusterCoalescenceEvent_probability_tendsto_one_of_uniformFiniteSlab
    hd p hp0 hp1 hδ0 hδ1 hslab

example {d L : ℕ} (hd : 1 ≤ d) (p : I) (hp0 : 0 < (p : ℝ))
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hslab : UniformFiniteSlabConnectionLowerBound d p L δ) :
    Filter.Tendsto
      (fun n ↦ (bernoulliBondMeasure d p).real
        (secondMacroscopicClusterEvent d n n cubicOrigin))
      Filter.atTop (nhds 0) :=
  secondMacroscopicCluster_probability_tendsto_zero_of_uniformFiniteSlab
    hd p hp0 hδ0 hδ1 hslab

example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (E : Set Ω) (A : ℕ → Set Ω) (q : ℝ) (hq : 0 ≤ q) (K : ℕ)
    (hEA : E ⊆ A K)
    (hstep : ∀ k, μ.real (A (k + 1)) ≤ q * μ.real (A k)) :
    μ.real E ≤ q ^ K :=
  measureReal_event_le_pow_of_peeling μ E A q hq K hEA hstep

example {d : ℕ} (p : I) (ε : ℝ) (x : Cubic d) (n m q : ℕ)
    (hmn : m ≤ n)
    (hqBox : (2 * m + 1) ^ d < q)
    (hqDensity : (1 - ε) * theta d p * (cubicMetricBox d x n).card ≤ q) :
    (epsilonGoodBoxEvent d p ε x n)ᶜ ⊆
      (largeCrossingClusterEvent d q n x)ᶜ ∪
        secondMacroscopicClusterEvent d m n x :=
  epsilonGoodBoxEvent_compl_subset_largeCrossing_compl_union_secondMacroscopic
    p ε x n m q hmn hqBox hqDensity

example {d : ℕ} (p : I) (ε : ℝ) (x : Cubic d) (m q : ℕ → ℕ)
    (hconstraints : ∀ᶠ n in Filter.atTop,
      m n ≤ n ∧ (2 * m n + 1) ^ d < q n ∧
        (1 - ε) * theta d p * (cubicMetricBox d x n).card ≤ q n)
    (hlarge : Filter.Tendsto
      (fun n ↦ (bernoulliBondMeasure d p).real
        (largeCrossingClusterEvent d (q n) n x)) Filter.atTop (nhds 1))
    (hsecond : Filter.Tendsto
      (fun n ↦ (bernoulliBondMeasure d p).real
        (secondMacroscopicClusterEvent d (m n) n x)) Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun n ↦ (bernoulliBondMeasure d p).real
        (epsilonGoodBoxEvent d p ε x n)) Filter.atTop (nhds 1) :=
  epsilonGoodBox_probability_tendsto_one_of_largeCrossing_of_second
    p ε x m q hconstraints hlarge hsecond

example {d n N q : ℕ} (hq : 1 ≤ q) (hnN : n ≤ N) {ω : EdgeConfiguration d}
    (hdense : q ≤ (infiniteClusterVerticesIn d
      (cubicMetricBox d cubicOrigin n) ω).card)
    (hcoalesce : ω ∈ infiniteClusterCoalescenceEvent d n N)
    (hfaces : ∀ i : Fin d, ∀ positive : Bool,
      ω ∈ innerInfiniteClusterReachesFaceEvent d n N i positive) :
    ω ∈ largeCrossingClusterEvent d q N cubicOrigin :=
  mem_largeCrossingClusterEvent_of_dense_of_coalescence_of_allFaces
    hq hnN hdense hcoalesce hfaces

example {d : ℕ} (hd : 1 ≤ d) (p : I) (hp : 0 < theta d p) :
    Filter.Tendsto
      (fun n ↦ (bernoulliBondMeasure d p).real
        (allInnerInfiniteClusterFacesEvent d n (2 * n)))
      Filter.atTop (nhds 1) :=
  allInnerInfiniteClusterFacesEvent_probability_tendsto_one hd p hp

/-- Oracle case for the paired-radius interface used by the logarithmic-annulus proof of
Lemma 7.97: no hidden equality between the inner and outer radius is required. -/
example {d : ℕ} (hd : 1 ≤ d) (p : I) (hp : 0 < theta d p)
    (r R : ℕ → ℕ) (hr : Filter.Tendsto r Filter.atTop Filter.atTop)
    (hrR : ∀ n, r n ≤ R n) :
    Filter.Tendsto
      (fun n ↦ (bernoulliBondMeasure d p).real
        (allInnerInfiniteClusterFacesEvent d (r n) (R n)))
      Filter.atTop (nhds 1) :=
  allInnerInfiniteClusterFacesEvent_probability_tendsto_one_of_radii
    hd p hp r R hr hrR

example {d n N : ℕ} (p : I) (e : Fin d ≃ Fin d) (i : Fin d) (positive : Bool) :
    (bernoulliBondMeasure d p).real
        (innerInfiniteClusterReachesFaceEvent d n N i positive) =
      (bernoulliBondMeasure d p).real
        (innerInfiniteClusterReachesFaceEvent d n N (e i) positive) :=
  innerInfiniteClusterReachesFaceProbability_permutation p e i positive

example (v : ℝ) (n : ℕ) : logarithmicInsetRadius v n ≤ n :=
  logarithmicInsetRadius_le v n

example {v : ℝ} (hv : 0 ≤ v) :
    Filter.Tendsto (fun n : ℕ ↦ (logarithmicInsetRadius v n : ℝ) / n)
      Filter.atTop (nhds 1) :=
  tendsto_logarithmicInsetRadius_div_nat hv

example {d : ℕ} {v : ℝ} (hv : 0 ≤ v) :
    Filter.Tendsto
      (fun n : ℕ ↦
        ((cubicMetricBox d cubicOrigin (logarithmicInsetRadius v n)).card : ℝ) /
          (cubicMetricBox d cubicOrigin n).card)
      Filter.atTop (nhds 1) :=
  tendsto_logarithmicInset_boxCard_ratio hv

example {d L : ℕ} (hd : 2 ≤ d) (p : I) (hp0 : 0 < (p : ℝ))
    (hp1 : (p : ℝ) < 1) (hθ : 0 < theta d p)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hslab : UniformFiniteSlabConnectionLowerBound d p L δ)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    Filter.Tendsto
      (fun n ↦ (bernoulliBondMeasure d p).real
        (epsilonDenseCrossingClusterEvent d p ε n cubicOrigin))
      Filter.atTop (nhds 1) :=
  epsilonDenseCrossingCluster_probability_tendsto_one_of_uniformFiniteSlab
    hd p hp0 hp1 hθ hδ0 hδ1 hslab hε0 hε1

example {d L : ℕ} (hd : 2 ≤ d) (p : I) (hp0 : 0 < (p : ℝ))
    (hp1 : (p : ℝ) < 1) (hθ : 0 < theta d p)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hslab : UniformFiniteSlabConnectionLowerBound d p L δ)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    Filter.Tendsto
      (fun n ↦ (bernoulliBondMeasure d p).real
        (epsilonGoodBoxEvent d p ε cubicOrigin n))
      Filter.atTop (nhds 1) :=
  epsilonGoodBox_probability_tendsto_one_of_uniformFiniteSlab
    hd p hp0 hp1 hθ hδ0 hδ1 hslab hε0 hε1

example {d : ℕ} (hd : 2 ≤ d)
    (h36 : CriticalHalfSpaceReliableBricks d hd)
    (h52 : ReliableBricksForceHalfSpacePercolation d (by omega)) :
    halfSpaceTheta d (cubicCriticalProbabilityUnit d hd) = 0 :=
  halfSpaceTheta_critical_eq_zero_of_reliableBricks hd h36 h52

example (d : ℕ) (happrox : SlabCriticalApproximation d) :
    Filter.Tendsto (slabCriticalProbability d) Filter.atTop
      (nhds (cubicCriticalProbability d)) :=
  slabCriticalProbability_tendsto_cubicCriticalProbability_of_approximation d happrox

example {d L : ℕ} {hd : 2 ≤ d} {ω : EdgeConfiguration d}
    (W : SlabCornerConnectionWitnessFamily hd 0 L ω) :
    W.HasProjectedChain :=
  W.hasProjectedChain_zero

example {d m L : ℕ} {hd : 2 ≤ d} {ω : EdgeConfiguration d}
    (W : SlabCornerConnectionWitnessFamily hd m L ω) :
    W.HasProjectedChain :=
  W.hasProjectedChain

example : SlabCornerProjectedChainGeometry :=
  slabCornerProjectedChainGeometry

example (G : SlabCornerProjectedChainGeometry)
    (d : ℕ) (hd : 2 ≤ d) {p₁ p₂ : I} (h12 : (p₁ : ℝ) < p₂)
    (m L : ℕ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hprob : ∀ k : Fin 4, δ ≤ (bernoulliBondMeasure d p₁).real
      (slabCornerConnectionEvent d hd m L k)) :
    (((p₂ : ℝ) - p₁) / (1 - (p₁ : ℝ))) ^ (4 * ((d - 2) * L)) * δ ^ 4 ≤
      (bernoulliBondMeasure d p₂).real
        (allSlabCornersConnectedEvent d m L) :=
  slabCornersConnected_probability_ge_of_projectedChainGeometry
    G d hd h12 m L hδ hprob

example (d : ℕ) (hd : 2 ≤ d) {p₁ p₂ : I} (h12 : (p₁ : ℝ) < p₂)
    (m L : ℕ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hprob : ∀ k : Fin 4, δ ≤ (bernoulliBondMeasure d p₁).real
      (slabCornerConnectionEvent d hd m L k)) :
    (((p₂ : ℝ) - p₁) / (1 - (p₁ : ℝ))) ^ (4 * ((d - 2) * L)) * δ ^ 4 ≤
      (bernoulliBondMeasure d p₂).real
        (allSlabCornersConnectedEvent d m L) :=
  slabCornersConnected_probability_ge d hd h12 m L hδ hprob

example (d L : ℕ) : cubicOrigin ∈ cubicQuarterSlab d L :=
  cubicOrigin_mem_cubicQuarterSlab d L

example (d : ℕ) (hd : 2 ≤ d) (p : I) (m L : ℕ) (k : Fin 4) :
    regionThetaFrom d (cubicQuarterSlab d L) p cubicOrigin / 2 ≤
      (bernoulliBondMeasure d p).real
        (slabCornerConnectionEvent d hd m L k) :=
  regionThetaFrom_half_le_slabCornerConnectionEvent d hd p m L k

example (d L : ℕ) {p₁ p₂ : I}
    (hcrit : regionCriticalProbability d (cubicQuarterSlab d L) < (p₁ : ℝ))
    (h12 : (p₁ : ℝ) < p₂) :
    0 < slabCornerAllConnectionLowerBound d L p₁ p₂ :=
  slabCornerAllConnectionLowerBound_pos d L hcrit h12

example (d : ℕ) (hd : 2 ≤ d) (L : ℕ) {p₁ p₂ : I}
    (h12 : (p₁ : ℝ) < p₂) (m : ℕ) :
    slabCornerAllConnectionLowerBound d L p₁ p₂ ≤
      (bernoulliBondMeasure d p₂).real
        (allSlabCornersConnectedEvent d m L) :=
  slabCornerAllConnectionLowerBound_le d hd L h12 m

example (d : ℕ) (hd : 2 ≤ d) (p : I) {a b n L : ℕ}
    (hab : a ≤ b) (hbn : b ≤ n) {δ : ℝ} (hδ : 0 ≤ δ)
    (hcorner : ∀ m, δ ≤ (bernoulliBondMeasure d p).real
      (allSlabCornersConnectedEvent d m L)) :
    δ ^ 2 ≤ (bernoulliBondMeasure d p).real
      (finiteThickSlabSConnectionEvent d n L cubicOrigin
        (figure715PlanarVertex d a b)) :=
  sq_slabCornerLowerBound_le_figure715PlanarConnection
    d hd p hab hbn hδ hcorner

example (d : ℕ) (hd : 2 ≤ d) (p : I) {z : Cubic d} {a b n L : ℕ}
    (hz : z ∈ slabCornerBoxVertices d n L)
    (hz0 : z ⟨0, by omega⟩ = a) (hz1 : z ⟨1, hd⟩ = b)
    (hab : a ≤ b) (hbn : b ≤ n) {δ : ℝ} (hδ : 0 ≤ δ)
    (hcorner : ∀ m, δ ≤ (bernoulliBondMeasure d p).real
      (allSlabCornersConnectedEvent d m L)) :
    (p : ℝ) ^ ((d - 2) * L) * δ ^ 2 ≤
      (bernoulliBondMeasure d p).real
        (finiteThickSlabSConnectionEvent d n L cubicOrigin z) :=
  transverseCost_mul_sq_slabCornerLowerBound_le_normalizedConnectionS
    d hd p hz hz0 hz1 hab hbn hδ hcorner

example (d : ℕ) (hd : 2 ≤ d) (p : I) {n L : ℕ} {x y : Cubic d}
    (hx : x ∈ finiteThickSlabSVertices d n L)
    (hy : y ∈ finiteThickSlabSVertices d n L)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hcorner : ∀ m, δ ≤ (bernoulliBondMeasure d p).real
      (allSlabCornersConnectedEvent d m L)) :
    ((p : ℝ) ^ ((d - 2) * L) * δ ^ 2) ^ 2 ≤
      (bernoulliBondMeasure d p).real
        (finiteThickSlabSConnectionEvent d n L x y) :=
  slabCornerLowerBound_four_mul_transverse_le_connectionS
    d hd p hx hy hδ hcorner

example (d : ℕ) (hd : 2 ≤ d) (L : ℕ) {p₁ p₂ : I}
    (h12 : (p₁ : ℝ) < p₂) {n : ℕ} {x y : Cubic d}
    (hx : x ∈ finiteThickSlabSVertices d n L)
    (hy : y ∈ finiteThickSlabSVertices d n L) :
    finiteThickSlabSConnectionLowerBound d L p₁ p₂ ≤
      (bernoulliBondMeasure d p₂).real
        (finiteThickSlabSConnectionEvent d n L x y) :=
  finiteThickSlabSConnectionLowerBound_le d hd L h12 hx hy

example (d : ℕ) (hd : 3 ≤ d) (L : ℕ) {p₁ p₂ : I}
    (h12 : (p₁ : ℝ) < p₂) {n : ℕ} (hnL : L ≤ n) {x y : Cubic d}
    (hx : x ∈ finiteThickSlabTVertices d n L)
    (hy : y ∈ finiteThickSlabTVertices d n L) :
    (finiteThickSlabSConnectionLowerBound d L p₁ p₂ ^ (d - 1)) ^ 2 ≤
      (bernoulliBondMeasure d p₂).real
        (finiteThickSlabTConnectionEvent d n L x y) :=
  finiteThickSlabSConnectionLowerBound_pow_le_connectionT_of_L_le_n
    d hd L h12 hnL hx hy

example {d n L : ℕ} (p : I) (hnL : n < L) {x y : Cubic d}
    (hx : x ∈ finiteThickSlabTVertices d n L)
    (hy : y ∈ finiteThickSlabTVertices d n L) :
    (p : ℝ) ^ (d * (3 * L)) ≤ (bernoulliBondMeasure d p).real
      (finiteThickSlabTConnectionEvent d n L x y) :=
  pow_d_mul_three_L_le_connectionT_of_n_lt_L p hnL hx hy

example (d : ℕ) (hd : 3 ≤ d) (L : ℕ) {p₁ p₂ : I}
    (h12 : (p₁ : ℝ) < p₂) {n : ℕ} {x y : Cubic d}
    (hx : x ∈ finiteThickSlabTVertices d n L)
    (hy : y ∈ finiteThickSlabTVertices d n L) :
    finiteThickSlabTConnectionLowerBound d L p₁ p₂ ≤
      (bernoulliBondMeasure d p₂).real
        (finiteThickSlabTConnectionEvent d n L x y) :=
  finiteThickSlabTConnectionLowerBound_le d hd L h12 hx hy

example (d : ℕ) (hd : 3 ≤ d) (L : ℕ) (p : I)
    (hp : regionCriticalProbability d (cubicQuarterSlab d L) < (p : ℝ)) :
    ∃ delta : ℝ, 0 < delta ∧
      UniformFiniteSlabConnectionLowerBound d p L delta :=
  exists_uniformFiniteSlabConnectionLowerBound_of_critical_lt d hd L p hp

example {d L : ℕ} (hd : 3 ≤ d) (p : I) (hp1 : (p : ℝ) < 1)
    (hcrit : regionCriticalProbability d (cubicQuarterSlab d L) < (p : ℝ))
    {epsilon : ℝ} (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon < 1) :
    Filter.Tendsto
      (fun n ↦ (bernoulliBondMeasure d p).real
        (epsilonGoodBoxEvent d p epsilon cubicOrigin n))
      Filter.atTop (nhds 1) :=
  epsilonGoodBox_probability_tendsto_one_of_quarterSlabCritical_lt
    hd p hp1 hcrit hepsilon0 hepsilon1

example (p : I) :
    setBer((Set.univ : Set ℕ), p) (Set.univ : Set (Set ℕ)) = 0 ∨
      setBer((Set.univ : Set ℕ), p) (Set.univ : Set (Set ℕ)) = 1 := by
  apply bernoulli_zero_or_one_of_invariantUnderFiniteClosing p MeasurableSet.univ
  intro E omega
  simp

example : Function.Injective (separatedAxisEdge (d := 3) (by omega)) :=
  separatedAxisEdge_injective (by omega)

example (E : Finset (CubicEdge 3)) (omega : EdgeConfiguration 3) :
    hasInfiniteOpenClusterInVertices 3 Set.univ (spliceOn E ∅ omega) ↔
      hasInfiniteOpenClusterInVertices 3 Set.univ omega :=
  isInvariantUnderFiniteClosing_hasInfiniteOpenClusterInVertices_univ 3 E omega

example (p : I) :
    regionHasInfiniteClusterProbability 3 Set.univ p = 0 ∨
      regionHasInfiniteClusterProbability 3 Set.univ p = 1 :=
  regionHasInfiniteClusterProbability_univ_eq_zero_or_one 3 p

example (p : I) (hp : 0 < theta 3 p) :
    regionHasInfiniteClusterProbability 3 Set.univ p = 1 :=
  regionHasInfiniteClusterProbability_univ_eq_one_of_theta_pos 3 p hp

example (omega : EdgeConfiguration 3) (m n : ℕ) (hmn : m ≤ n)
    (homega : omega ∈ centralBoxMeetsInfiniteClusterEvent 3 m) :
    1 ≤ (boxBoundaryContacts 3 m n omega).card :=
  centralBoxMeetsInfiniteClusterEvent_subset_one_le_contactCard hmn homega

example (n ell : ℕ) (S : Finset (Cubic 3)) (hS : S.card < ell) :
    (boxBoundaryExitEdges 3 n S).card ≤ (ell - 1) * 6 := by
  calc
    (boxBoundaryExitEdges 3 n S).card ≤ S.card * (2 * 3) :=
      boxBoundaryExitEdges_card_le 3 n S
    _ ≤ (ell - 1) * 6 := by omega

example (p : I) (hp : 0 < theta 3 p) (hp1 : (p : ℝ) < 1)
    (ell : ℕ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ m n : ℕ, m ≤ n ∧
      1 - epsilon <
        (bernoulliBondMeasure 3 p).real (boundaryContactCardGeEvent 3 m n ell) :=
  exists_boundaryContactCardGe_probability_gt 3 p hp hp1 ell hepsilon

example : Fintype.card (BoxSurfaceOrthantIndex 3) = 24 := by
  simpa using card_boxSurfaceOrthantIndex 3

example (i : Fin 3) (n : ℕ) :
    boxSurfaceOrthant 3 n (allPositiveBoxSurfaceOrthantIndex i) =
      seededBoundaryQuadrant 3 i n :=
  boxSurfaceOrthant_allPositive_eq_seededBoundaryQuadrant i

example (p : I) (hp : 0 < theta 3 p) (hp1 : (p : ℝ) < 1)
    (i : Fin 3) (ell : ℕ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ m n : ℕ, m ≤ n ∧
      1 - epsilon <
        (bernoulliBondMeasure 3 p).real
          (orthantBoundaryContactCardGeEvent 3 m n
            (allPositiveBoxSurfaceOrthantIndex i) ell) :=
  exists_allPositiveOrthantContactCardGe_probability_gt 3 (by omega) p hp hp1 i ell hepsilon

example (i : Fin 3) {m n : ℕ} {y : Cubic 3}
    (hmn : 2 * m ≤ n) (hy : y ∈ seededBoundaryQuadrant 3 i n) :
    cubicStepFrom y (i, true) ∈
      cubicMetricBox 3 (canonicalBoundarySeedCenter i m n y) m :=
  cubicStepFrom_mem_canonicalBoundarySeedBox i hmn hy

example (i : Fin 3) {m n : ℕ} {y : Cubic 3}
    (hmn : 2 * m ≤ n) (hy : y ∈ seededBoundaryQuadrant 3 i n) :
    SeedBoxWithinBoundaryLayer 3 i m n (canonicalBoundarySeedCenter i m n y) :=
  canonicalBoundarySeedBoxWithinBoundaryLayer i hmn hy

example (p : I) (hp : 0 < theta 3 p) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (i : Fin 3) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ m n : ℕ, 2 * m < n ∧
      1 - epsilon <
        (bernoulliBondMeasure 3 p).real (seedConnectionEvent 3 i m n) :=
  seedConnection_probability_gt 3 (by omega) p hp hp0 hp1 i hepsilon

example :
    (couplingMeasure (Fin 2)).real
        (boundaryClosedHistoryEvent Finset.univ (fun _ => (0 : I))) = 1 := by
  rw [couplingMeasure_real_boundaryClosedHistoryEvent]
  simp

example :
    (couplingMeasure (Fin 2)).real
        (sprinkledAvailableExitFailureEvent (fun _ => (0 : I)) (1 / 2 : ℝ)
          (fun _ => (Finset.univ : Finset (Fin 2))) ∩
          boundaryClosedHistoryEvent Finset.univ (fun _ => (0 : I))) ≤ 1 / 4 := by
  let U : (Fin 2 → ℝ) → Finset (Fin 2) := fun _ => Finset.univ
  have hU : ∀ X, U X ⊆ (Finset.univ : Finset (Fin 2)) := fun _ => Finset.subset_univ _
  have hexact : ∀ S ⊆ (Finset.univ : Finset (Fin 2)),
      MeasurableSet[coordSigma (Fin 2)
        ((((Finset.univ : Finset (Fin 2)) : Set (Fin 2)))ᶜ)]
        (exactAvailableExitSetEvent U S) := by
    intro S _hS
    by_cases hS : S = Finset.univ
    · subst S
      convert MeasurableSet.univ
      ext X
      simp [exactAvailableExitSetEvent, U]
    · convert MeasurableSet.empty
      ext X
      simp [exactAvailableExitSetEvent, U, hS, eq_comm]
  have h := couplingMeasure_real_sprinkledFailure_inter_history_le
    (Finset.univ : Finset (Fin 2)) (fun _ => (0 : I)) (1 / 2 : ℝ) U 1 hU
      (by norm_num) (by norm_num) (by intro e he; norm_num) hexact
  have h' :
      (couplingMeasure (Fin 2)).real
          (sprinkledAvailableExitFailureEvent (fun _ => (0 : I)) (1 / 2 : ℝ)
            (fun _ => (Finset.univ : Finset (Fin 2))) ∩
            boundaryClosedHistoryEvent Finset.univ (fun _ => (0 : I))) ≤
        (1 - (1 / 2 : ℝ)) ^ 2 := by
    simpa [U, fewAvailableExitsEvent,
      couplingMeasure_real_boundaryClosedHistoryEvent] using h
  norm_num at h' ⊢
  exact h'

example {R K : Finset (Cubic 3)} {n : ℕ} {omega : EdgeConfiguration 3}
    (hKR : Disjoint K R) :
    omega ∈ regionConnectionToFiniteTargetEvent 3 R n K ↔
      ∃ e ∈ regionAvailableExitEdges 3 R n K omega, e ∈ omega :=
  mem_regionConnectionToFiniteTargetEvent_iff_exists_open_availableExit hKR

example (i : Fin 3) (p : I) (hpTheta : 0 < theta 3 p)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    {epsilon delta : ℝ} (hepsilon : 0 < epsilon)
    (hdelta : 0 < delta) (hdelta1 : delta ≤ 1) :
    ∃ m n : ℕ, 2 * m < n ∧
      ∀ (R : Finset (Cubic 3)) (beta : CubicEdge 3 → I),
        cubicMetricBox 3 cubicOrigin m ⊆ R →
        R ⊆ cubicMetricBox 3 cubicOrigin n →
        RegionAvoidsSeededBoundaryQuadrant 3 i n R →
        (∀ e ∈ cubicRegionBoundaryEdgesWithinBox 3 R n,
          (beta e : ℝ) + delta ≤ 1) →
        (1 - epsilon) *
            (couplingMeasure (CubicEdge 3)).real
              (boundaryClosedHistoryEvent
                (cubicRegionBoundaryEdgesWithinBox 3 R n) beta) <
          (couplingMeasure (CubicEdge 3)).real
            (sprinkledRestartEvent 3 i m n R p beta delta ∩
              boundaryClosedHistoryEvent
                (cubicRegionBoundaryEdgesWithinBox 3 R n) beta) :=
  sprinkledRestart_inter_history_gt 3 (by omega) i p hpTheta hp0 hp1
    hepsilon hdelta hdelta1

example (N : ℕ) (x : Cubic 3) :
    (grimmettMarstrandSiteBox 3 N x : Set (Cubic 3)) ⊆
      grimmettMarstrandThickening 3 Set.univ N :=
  grimmettMarstrandSiteBox_subset_thickening (by simp)

example (N : ℕ) (x : Cubic 3) (a : CubicDirection 3) :
    (grimmettMarstrandHalfwayBox 3 N x a : Set (Cubic 3)) ⊆
      grimmettMarstrandThickening 3 Set.univ N :=
  grimmettMarstrandHalfwayBox_subset_thickening (by simp) (by simp)

example :
    (⟨[{0}, {0, 1}]⟩ : FiniteRevealSchedule (Fin 2)).multiplicity 0 = 2 := by
  simp [FiniteRevealSchedule.multiplicity]

example (S : FiniteRevealSchedule (Fin 2))
    (hS : S.HasOverlapBound 7) (p eta : ℝ) (heta : 0 ≤ eta) (e : Fin 2) :
    S.accumulatedThreshold p (eta / 7) e ≤ p + eta := by
  simpa using S.accumulatedThreshold_le_add_budget (by norm_num) hS p eta heta e

example (i : Fin 3) {m n : ℕ} {y : Cubic 3}
    (hmn : 2 * m ≤ n) (hy : y ∈ seededBoundaryQuadrant 3 i n) :
    cubicTranslateRegion cubicOrigin (canonicalBoundarySeedCenter i m n y)
        (steeredPositiveBoundaryLayerRegion 3 i m n) ⊆
      (grimmettMarstrandHalfwayBox 3 (m + n + 1) cubicOrigin (i, true) :
        Set (Cubic 3)) :=
  translated_steeredBoundaryLayer_subset_halfwayBox i hmn hy

example (i : Fin 3) {m n : ℕ} {y : Cubic 3}
    (hmn : 2 * m ≤ n) (hy : y ∈ seededBoundaryQuadrant 3 i n) :
    cubicTranslateRegion cubicOrigin (canonicalBoundarySeedCenter i m n y)
        (steeredPositiveRestartRegion 3 i m n) ⊆
      (cubicMetricBox 3 cubicOrigin (2 * (m + n + 1)) : Set (Cubic 3)) ∪
        (cubicMetricBox 3
          (grimmettMarstrandSiteCenter (m + n + 1)
            (cubicStepFrom cubicOrigin (i, true)))
          (2 * (m + n + 1)) : Set (Cubic 3)) :=
  translated_steeredRestartRegion_subset_endpointBoxes i hmn hy

example :
    (rootedSiteExploration (⊥ : SimpleGraph (Fin 1)) (fun _ ↦ ∅)
      (by simp) 0).initial.WellFormed :=
  rootedSiteExploration_initial_wellFormed
    (⊥ : SimpleGraph (Fin 1)) (fun _ ↦ ∅) (by simp) 0

example :
    (rootedSiteExploration (⊥ : SimpleGraph (Fin 1)) (fun _ ↦ ∅)
      (by simp) 0).OpenRootedAt 0
        (rootedSiteExploration (⊥ : SimpleGraph (Fin 1)) (fun _ ↦ ∅)
          (by simp) 0).initial :=
  rootedSiteExploration_initial_openRootedAt
    (⊥ : SimpleGraph (Fin 1)) (fun _ ↦ ∅) (by simp) 0

example {V Omega : Type*} [Countable V] [DecidableEq V] [LinearOrder V]
    [MeasurableSpace Omega] (E : AdaptiveSiteExploration V)
    (answer : Omega → List (V × Bool) → V → Bool)
    (hanswer : AdaptiveSiteExploration.MeasurableAnswer answer) :
    Measurable fun omega ↦ E.occupiedLimit (answer omega) :=
  E.measurable_occupiedLimit hanswer

example {V Omega : Type*} [Countable V] [DecidableEq V] [LinearOrder V]
    [MeasurableSpace Omega] (E : AdaptiveSiteExploration V)
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (answer : Omega → List (V × Bool) → V → Bool)
    (hanswer : AdaptiveSiteExploration.MeasurableAnswer answer) (e : ℕ ≃ V)
    (p : I) (hp : 0 < (p : ℝ)) (root : V)
    (hinitial : E.OpenRootedAt root E.initial)
    (hseq : ∀ n, HasFiniteSequentialLowerBound
      (enumerationPrefixLaw e n (E.occupiedLimitLaw mu answer)) (p : ℝ)) :
    0 < mu.real {omega |
      hasInfiniteSiteCluster E.graph (E.occupiedLimit (answer omega))} :=
  E.infiniteCluster_probability_pos_of_prefixLowerBound
    mu answer hanswer e p hp root hinitial hseq

example {V : Type*} {d : ℕ} {A : Set (Cubic d)} {omega : EdgeConfiguration d}
    {S : Set V} (hS : S.Infinite) (anchor : V → Cubic d)
    (hinj : Set.InjOn anchor S) {root : V} (hroot : root ∈ S)
    (hA : ∀ v ∈ S, anchor v ∈ A)
    (hconn : ∀ v ∈ S,
      omega ∈ connectionEventWithinVertices d A (anchor root) (anchor v)) :
    hasInfiniteOpenClusterInVertices d A omega :=
  hasInfiniteOpenClusterInVertices_of_infinite_anchor_connections
    hS anchor hinj hroot hA hconn

example {Omega iota : Type*} [MeasurableSpace Omega] [Fintype iota] [Nonempty iota]
    {mu : Measure Omega} [IsFiniteMeasure mu]
    (G : iota → Set Omega) (H : Set Omega)
    (hG : ∀ i, MeasurableSet (G i)) (hH : MeasurableSet H)
    (epsilon : ℝ)
    (hsuccess : ∀ i, (1 - epsilon) * mu.real H < mu.real (G i ∩ H)) :
    (1 - Fintype.card iota * epsilon) * mu.real H <
      mu.real ((⋂ i, G i) ∩ H) :=
  allSuccess_inter_history_gt G H hG hH epsilon hsuccess

example (eta : ℝ) : dynamicBlockIncrement 3 eta = eta / 14 := by
  simp [dynamicBlockIncrement]
  ring

example (pcSite : ℝ) :
    dynamicBlockRestartError 3 pcSite = (1 - pcSite) / 24 := by
  norm_num [dynamicBlockRestartError]

example {pcSite : ℝ} (hsite0 : 0 ≤ pcSite) (hsite1 : pcSite < 1) :
    dynamicBlockSiteDensity pcSite <
      (1 - 6 * dynamicBlockRestartError 3 pcSite) *
        (1 - dynamicBlockRestartError 3 pcSite) ^ 6 := by
  have h := dynamicBlock_successFactor_gt_siteDensity (d := 3) (by norm_num)
    hsite0 hsite1
  norm_num at h ⊢
  exact h

example :
    explorationHistoryAccepted ([(0, true), (1, false), (2, true)] :
      List (Fin 3 × Bool)) = {0, 2} := by
  decide

example :
    explorationHistoryRejected ([(0, true), (1, false), (2, true)] :
      List (Fin 3 × Bool)) = {1} := by
  decide

example {alpha : Type*} {A : Set (alpha → ℝ)} (hA : MeasurableSet A) :
    (couplingMeasure alpha).real
        (couplingReindex (Equiv.refl alpha) ⁻¹' A) =
      (couplingMeasure alpha).real A :=
  couplingMeasure_real_preimage_reindex (Equiv.refl alpha) hA

example (center : Cubic 3) (a : CubicDirection 3) :
    cubicDirectionOrientationIso center a cubicOrigin = center :=
  cubicDirectionOrientationIso_origin center a

example (center : Cubic 3) (a : CubicDirection 3) :
    cubicDirectionOrientationIso center a
        (cubicStepFrom cubicOrigin (a.1, true)) =
      cubicStepFrom center a :=
  cubicDirectionOrientationIso_positiveStep center a

example (center : Cubic 3) (a : CubicDirection 3)
    {A : Set (CubicEdge 3 → ℝ)} (hA : MeasurableSet A) :
    (couplingMeasure (CubicEdge 3)).real
        (orientedCouplingTransportEvent center a A) =
      (couplingMeasure (CubicEdge 3)).real A :=
  couplingMeasure_real_orientedTransportEvent center a hA

example (center : Cubic 3) (a : CubicDirection 3) (p : I)
    (X : CubicEdge 3 → ℝ) :
    thresholdConfiguration p
        (cubicGraphIsoCouplingReindex (cubicDirectionOrientationIso center a) X) =
      cubicGraphIsoConfigurationPullback (cubicDirectionOrientationIso center a)
        (thresholdConfiguration p X) :=
  thresholdConfiguration_orientedCouplingReindex center a p X

example (x : Cubic 3) (a : CubicDirection 3) {m n : ℕ} {y : Cubic 3}
    (hmn : 2 * m ≤ n) (hy : y ∈ seededBoundaryQuadrant 3 a.1 n) :
    orientedSteeredRestartRegion (m + n + 1) x a m n y ⊆
      (cubicMetricBox 3 (grimmettMarstrandSiteCenter (m + n + 1) x)
          (2 * (m + n + 1)) : Set (Cubic 3)) ∪
        (cubicMetricBox 3
          (grimmettMarstrandSiteCenter (m + n + 1) (cubicStepFrom x a))
          (2 * (m + n + 1)) : Set (Cubic 3)) :=
  orientedSteeredRestartRegion_subset_endpointBoxes x a hmn hy

example :
    AdaptiveSiteExploration.adaptiveAnswerHistoryEvent
        (fun (_omega : Fin 1) (_history : List (Fin 1 × Bool)) (_v : Fin 1) => true)
        [((0 : Fin 1), true)] = Set.univ := by
  ext omega
  simp [AdaptiveSiteExploration.adaptiveAnswerHistoryEvent,
    AdaptiveSiteExploration.adaptiveAnswerHistoryEventFrom]

example {Omega V : Type*} [MeasurableSpace Omega]
    (success : List (V × Bool) → V → Set Omega)
    (omega : Omega) (history : List (V × Bool)) (v : V) :
    AdaptiveSiteExploration.eventAdaptiveAnswer success omega history v = true ↔
      omega ∈ success history v :=
  AdaptiveSiteExploration.eventAdaptiveAnswer_eq_true_iff success omega history v

example (q : ℝ) :
    AdaptiveSiteExploration.iidAdaptiveDecisionValue q
        (fun _history : List (Unit × Bool) => ())
        (fun history => history.any fun entry => entry.2) [] 1 = q := by
  simp [AdaptiveSiteExploration.iidAdaptiveDecisionValue]

example {Omega V : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega)
    (answer : Omega → List (V × Bool) → V → Bool)
    (query : List (V × Bool) → V)
    (win : List (V × Bool) → Prop) (history : List (V × Bool)) (depth : ℕ) :
    AdaptiveSiteExploration.adaptiveDecisionWinMass
        mu answer query win history (depth + 1) =
      AdaptiveSiteExploration.adaptiveDecisionWinMass
          mu answer query win (history ++ [(query history, true)]) depth +
        AdaptiveSiteExploration.adaptiveDecisionWinMass
          mu answer query win (history ++ [(query history, false)]) depth :=
  AdaptiveSiteExploration.adaptiveDecisionWinMass_succ
    mu answer query win history depth

example {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (E : SiteExploration V) (answer : V → Bool)
    (hinitial : E.initial.WellFormed) :
    (E.stateAfter answer (Fintype.card V)).frontier = ∅ :=
  E.stateAfter_card_frontier_eq_empty answer hinitial

example {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (E : AdaptiveSiteExploration V)
    (answer : List (V × Bool) → V → Bool)
    (hinitial : E.initial.WellFormed) :
    (E.stateAfter answer (Fintype.card V)).frontier = ∅ :=
  E.stateAfter_card_frontier_eq_empty answer hinitial

example {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) (neighbors : V → Finset V)
    (mem_neighbors : ∀ {x y}, y ∈ neighbors x ↔ G.Adj x y)
    (root : V) (eta : Set V) (hroot : root ∈ eta) :
    (((rootedSiteExploration G neighbors mem_neighbors root).stateAfter
      (configurationAnswer eta) (Fintype.card V)).occupied : Set V) =
        siteOpenCluster G eta root :=
  rootedSiteExploration_stateAfter_card_occupied_eq_siteOpenCluster
    G neighbors mem_neighbors root eta hroot

example {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) (neighbors : V → Finset V)
    (mem_neighbors : ∀ {x y}, y ∈ neighbors x ↔ G.Adj x y)
    (root : V) (target : Finset V) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    finiteBernoulliProbability Finset.univ q
        (SiteExploration.finiteSiteHitsTarget G root target) ≤
      (rootedSiteExploration G neighbors mem_neighbors root).completionHitProbability
        q root target (rootedSiteExploration G neighbors mem_neighbors root).initial :=
  SiteExploration.finiteBernoulliProbability_finiteSiteHitsTarget_le_rooted_completion
    G neighbors mem_neighbors root target hq0 hq1

example :
    AdaptiveSiteExploration.adaptiveDecisionWinEvent
        (fun (_omega : Fin 1) (_history : List (Unit × Bool)) (_v : Unit) => true)
        (fun _history => ())
        (fun history => history.any fun entry => entry.2) 1 = Set.univ := by
  ext omega
  simp only [AdaptiveSiteExploration.adaptiveDecisionWinEvent,
    AdaptiveSiteExploration.adaptiveDecisionLeafEvent, Set.mem_iUnion,
    Set.mem_univ, iff_true]
  refine ⟨fun _ => true, ?_⟩
  constructor
  · change omega ∈ ({_omega : Fin 1 | true = true} ∩ Set.univ)
    simp
  · simp [AdaptiveSiteExploration.adaptiveQueryHistory,
      AdaptiveSiteExploration.adaptiveQueryHistoryFrom]

example (answer : Fin 1 → List (Fin 1 × Bool) → Fin 1 → Bool) (omega : Fin 1) :
    SiteExploration.prefixedAdaptiveAnswer [((0 : Fin 1), true)] answer omega [] 0 =
      answer omega [((0 : Fin 1), true)] 0 := by
  rfl

example {V Omega : Type*} [DecidableEq V] [LinearOrder V]
    (E : SiteExploration V)
    (answer : Omega → List (V × Bool) → V → Bool)
    (target : Finset V) (n : ℕ) :
    E.adaptiveTargetHitEvent answer target n ⊆
      E.adaptiveLimitTargetHitEvent answer target :=
  E.adaptiveTargetHitEvent_subset_adaptiveLimitTargetHitEvent answer target n

example {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (A : ℕ → Set Omega) (B : Set Omega) (c : ℝ)
    (hA : ∀ n, MeasurableSet (A n)) (hanti : Antitone A)
    (hsub : (⋂ n, A n) ⊆ B) (hlower : ∀ n, c ≤ mu.real (A n)) :
    c ≤ mu.real B :=
  measureReal_limitEvent_ge_of_antitone_exhaustion mu A B c hA hanti hsub hlower

example (d : ℕ) (F : Set (Cubic d)) (root : F) :
    root ∈ cubicRegionMetricSphere d F root 0 := by
  simp

example (d : ℕ) (F : Set (Cubic d)) (root : F) (n : ℕ)
    (v : {v : F // v ∈ cubicRegionMetricBall d F root n}) :
    AdaptiveSiteExploration.mapDecisionHistory
      (SiteExploration.cubicRegionBallEmbedding d F root n) [(v, true)] =
        [((v : F), true)] := by
  rfl

example {Omega : Type*} (d : ℕ) (F : Set (Cubic d)) [LinearOrder F]
    (root : F) (n : ℕ)
    (answer : Omega → List (F × Bool) → F → Bool) :
    (SiteExploration.cubicRegionBallSiteExploration d F root n).adaptiveLimitTargetHitEvent
        (SiteExploration.cubicRegionBallAdaptiveAnswer d F root n answer)
        (cubicRegionBallTarget d F root n) ⊆
      (cubicRegionSiteExploration d F root).adaptiveLimitTargetHitEvent
        answer (cubicRegionMetricSphere d F root n) :=
  SiteExploration.cubicRegionBall_adaptiveLimitTargetHitEvent_subset
    d F root n answer

example {V Omega : Type*}
    (success : List (V × Bool) → V → Set Omega)
    (history : List (V × Bool)) (v : V) :
    AdaptiveSiteExploration.adaptiveAnswerHistoryEvent
        (AdaptiveSiteExploration.eventAdaptiveAnswer success)
        (history ++ [(v, true)]) =
      AdaptiveSiteExploration.adaptiveAnswerHistoryEvent
          (AdaptiveSiteExploration.eventAdaptiveAnswer success) history ∩
        success history v :=
  AdaptiveSiteExploration.adaptiveAnswerHistoryEvent_eventAdaptiveAnswer_append_true
    success history v

end Percolation
