import Percolation.Critical.DynamicRecursiveEdgeState
import Percolation.Critical.DynamicFramedRevealIntervals
import Percolation.Critical.DynamicSourceEdgeState

/-!
# Canonical recursive states as framed restart cells

The deterministic recursion records exactly two finite pieces of information: the explored
edges, which are open below their current upper thresholds, and the literal line boundary,
which is closed at its current lower thresholds.  A framed restart reuses the latter boundary
coordinates.  This file proves the adapter needed by the probabilistic construction: once the
query boundary is the state's actual boundary, peeling the reused closed coordinates leaves
only the explored edges as the past support.
-/

namespace Percolation

open MeasureTheory
open scoped unitInterval

namespace FiniteEdgeRevealState

/-- After peeling the complete canonical boundary, the remaining support is exactly the
explored edge set. -/
@[simp]
theorem withoutClosed_boundary_support {d : ℕ} (S : FiniteEdgeRevealState d) :
    ((S.profile.withoutClosed S.boundary).support) = S.explored := by
  classical
  ext e
  simp [FiniteRevealIntervalProfile.support, profile]

/-- The canonical profile factors into its explored-edge past and its literal closed
line-boundary history. -/
theorem profile_event_eq_past_inter_boundary {d : ℕ}
    (S : FiniteEdgeRevealState d) :
    S.profile.event =
      (S.profile.withoutClosed S.boundary).event ∩
        boundaryClosedHistoryEvent S.boundary S.lower := by
  apply S.profile.event_eq_withoutClosed_inter_boundaryClosedHistoryEvent
  intro e he
  exact he

/-- The peeled past cylinder is measurable on the explored edges alone. -/
theorem measurableSet_pastEvent_coordSigma {d : ℕ}
    (S : FiniteEdgeRevealState d) :
    MeasurableSet[coordSigma (CubicEdge d) (S.explored : Set (CubicEdge d))]
      (S.profile.withoutClosed S.boundary).event := by
  rw [← S.withoutClosed_boundary_support]
  exact (S.profile.withoutClosed S.boundary).measurableSet_event_coordSigma

end FiniteEdgeRevealState

namespace AdaptiveSiteExploration

variable {C : Type*} [Fintype C] [DecidableEq C]

/-- Construct a partitioned framed restart directly from canonical recursive edge states.

The equality `hboundary` is the geometric handoff: the transported restart boundary must be
the literal line boundary derived from the explored set.  Consequently all residual closed
constraints disappear, and `hfresh` concerns only the already-explored open coordinates.
-/
noncomputable def PartitionedFramedRestartStage.ofFiniteEdgeStateRealization
    {d m n : ℕ} {p : I} {delta epsilon : ℝ}
    (history : Set (CubicEdge d → ℝ))
    (realizedCell : (CubicEdge d → ℝ) → C)
    (query : C → FramedRestartQuery d)
    (state : C → FiniteEdgeRevealState d)
    (hboundary : ∀ c, (query c).boundarySupport n = (state c).boundary)
    (hlower : ∀ c e, e ∈ (state c).boundary →
      (state c).lower e = (query c).physicalBoundaryThreshold e)
    (hfiber : ∀ c, (state c).profile.event =
      exactRevealCellEvent history realizedCell c)
    (hfresh : ∀ c,
      Disjoint ((state c).explored : Set (CubicEdge d))
        ((query c).restartSupport m n : Set (CubicEdge d)))
    (hrestart : ∀ c,
      (1 - epsilon) * (couplingMeasure (CubicEdge d)).real
          ((query c).boundaryHistoryEvent n) <
        (couplingMeasure (CubicEdge d)).real
          ((query c).successEvent m n p delta ∩
            (query c).boundaryHistoryEvent n)) :
    PartitionedFramedRestartStage d C m n p delta epsilon := by
  classical
  apply PartitionedFramedRestartStage.ofIntervalProfileRealization
    history realizedCell query (fun c ↦ (state c).profile)
  · intro c e he
    simpa [FiniteEdgeRevealState.profile, ← hboundary c] using he
  · intro c e he
    apply hlower c e
    simpa [← hboundary c] using he
  · exact hfiber
  · intro c
    simp [FiniteEdgeRevealState.profile, hboundary c]
  · intro c
    simpa [FiniteEdgeRevealState.profile] using hfresh c
  · exact hrestart

/-- The canonical-state cells cover the supplied outer history exactly. -/
theorem PartitionedFramedRestartStage.cellUnion_ofFiniteEdgeStateRealization
    {d m n : ℕ} {p : I} {delta epsilon : ℝ}
    (history : Set (CubicEdge d → ℝ))
    (realizedCell : (CubicEdge d → ℝ) → C)
    (query : C → FramedRestartQuery d)
    (state : C → FiniteEdgeRevealState d)
    (hboundary : ∀ c, (query c).boundarySupport n = (state c).boundary)
    (hlower : ∀ c e, e ∈ (state c).boundary →
      (state c).lower e = (query c).physicalBoundaryThreshold e)
    (hfiber : ∀ c, (state c).profile.event =
      exactRevealCellEvent history realizedCell c)
    (hfresh : ∀ c,
      Disjoint ((state c).explored : Set (CubicEdge d))
        ((query c).restartSupport m n : Set (CubicEdge d)))
    (hrestart : ∀ c,
      (1 - epsilon) * (couplingMeasure (CubicEdge d)).real
          ((query c).boundaryHistoryEvent n) <
        (couplingMeasure (CubicEdge d)).real
          ((query c).successEvent m n p delta ∩
            (query c).boundaryHistoryEvent n)) :
    (PartitionedFramedRestartStage.ofFiniteEdgeStateRealization
      history realizedCell query state hboundary hlower hfiber hfresh hrestart).cellUnion =
        history := by
  classical
  unfold PartitionedFramedRestartStage.ofFiniteEdgeStateRealization
  apply PartitionedFramedRestartStage.cellUnion_ofIntervalProfileRealization

end AdaptiveSiteExploration

/-! ### Literal global-boundary source states -/

/-- A cubic graph automorphism preserves adjacency in the induced edge-line graph. -/
theorem cubicEdgeLineGraph_adj_mapEdgeSet_iff
    {d : ℕ} (F : cubicGraph d ≃g cubicGraph d) (e f : CubicEdge d) :
    (cubicEdgeLineGraph d).Adj (F.mapEdgeSet e) (F.mapEdgeSet f) ↔
      (cubicEdgeLineGraph d).Adj e f := by
  constructor
  · rintro ⟨hef, y, hye, hyf⟩
    obtain ⟨x, rfl⟩ := F.surjective y
    have hxe : x ∈ (e : Sym2 (Cubic d)) := by
      change F x ∈ Sym2.map F (e : Sym2 (Cubic d)) at hye
      rw [Sym2.mem_map] at hye
      obtain ⟨z, hz, hzx⟩ := hye
      simpa [F.injective hzx] using hz
    have hxf : x ∈ (f : Sym2 (Cubic d)) := by
      change F x ∈ Sym2.map F (f : Sym2 (Cubic d)) at hyf
      rw [Sym2.mem_map] at hyf
      obtain ⟨z, hz, hzx⟩ := hyf
      simpa [F.injective hzx] using hz
    exact ⟨fun h ↦ hef (congrArg F.mapEdgeSet h), x, hxe, hxf⟩
  · rintro ⟨hef, x, hxe, hxf⟩
    refine ⟨fun h ↦ hef (F.mapEdgeSet.injective h), F x, ?_, ?_⟩
    · change F x ∈ Sym2.map F (e : Sym2 (Cubic d))
      rw [Sym2.mem_map]
      exact ⟨x, hxe, rfl⟩
    · change F x ∈ Sym2.map F (f : Sym2 (Cubic d))
      rw [Sym2.mem_map]
      exact ⟨x, hxf, rfl⟩

/-- The literal global edge boundary is equivariant under every cubic graph automorphism. -/
theorem cubicEdgeBoundary_image_cubicGraphIso
    {d : ℕ} (F : cubicGraph d ≃g cubicGraph d) (E : Finset (CubicEdge d)) :
    (cubicEdgeBoundary E).image F.mapEdgeSet =
      cubicEdgeBoundary (E.image F.mapEdgeSet) := by
  classical
  ext e
  constructor
  · rw [Finset.mem_image]
    rintro ⟨f, hfBoundary, rfl⟩
    obtain ⟨hfNotE, g, hgE, hgf⟩ := mem_cubicEdgeBoundary_iff.mp hfBoundary
    apply mem_cubicEdgeBoundary_iff.mpr
    refine ⟨?_, F.mapEdgeSet g, Finset.mem_image.mpr ⟨g, hgE, rfl⟩, ?_⟩
    · intro hfImage
      obtain ⟨h, hhE, hhf⟩ := Finset.mem_image.mp hfImage
      exact hfNotE (by simpa [F.mapEdgeSet.injective hhf] using hhE)
    · exact (cubicEdgeLineGraph_adj_mapEdgeSet_iff F g f).2 hgf
  · intro heBoundary
    obtain ⟨f, rfl⟩ := F.mapEdgeSet.surjective e
    rw [Finset.mem_image]
    refine ⟨f, ?_, rfl⟩
    obtain ⟨hfNotImage, g', hg'Image, hg'f⟩ :=
      mem_cubicEdgeBoundary_iff.mp heBoundary
    obtain ⟨g, hgE, rfl⟩ := Finset.mem_image.mp hg'Image
    apply mem_cubicEdgeBoundary_iff.mpr
    refine ⟨?_, g, hgE, (cubicEdgeLineGraph_adj_mapEdgeSet_iff F g f).1 hg'f⟩
    intro hfE
    exact hfNotImage (Finset.mem_image.mpr ⟨f, hfE, rfl⟩)

namespace SourceFiniteEdgeRevealState

/-- Express the physical explored edge set in the reference coordinates of a steering frame. -/
noncomputable def referenceExploredEdges {d : ℕ} (S : SourceFiniteEdgeRevealState d)
    (F : cubicGraph d ≃g cubicGraph d) : Finset (CubicEdge d) :=
  S.explored.image F.symm.mapEdgeSet

/-- Mapping the reference explored edges back through the frame recovers the physical set. -/
theorem referenceExploredEdges_image {d : ℕ} (S : SourceFiniteEdgeRevealState d)
    (F : cubicGraph d ≃g cubicGraph d) :
    (S.referenceExploredEdges F).image F.mapEdgeSet = S.explored := by
  classical
  have hsymm : F.symm.mapEdgeSet = F.mapEdgeSet.symm := by
    ext e
    rfl
  rw [referenceExploredEdges, hsymm, Finset.image_image]
  simpa using Finset.image_id S.explored

/-- Canonical framed query extracted from a literal source state.  Its reference vertex region
is the endpoint set of the physical explored edges pulled back through the steering frame, and
its reference threshold is the physical lower threshold pulled through that same frame. -/
noncomputable def framedQuery {d : ℕ} (S : SourceFiniteEdgeRevealState d)
    (center : Cubic d) (a : CubicDirection d) (transverseFlip : Fin d → Bool) :
    FramedRestartQuery d :=
  let F := cubicRestartFrameIso center a transverseFlip
  { center := center
    direction := a
    transverseFlip := transverseFlip
    region := cubicEdgeEndpointVertices (S.referenceExploredEdges F)
    beta := fun e ↦ S.lower (F.mapEdgeSet e) }

/-- Enlarging the physical explored edge set enlarges the reference vertex region of every
fixed framed query.  Threshold data play no role in this geometric monotonicity statement. -/
theorem framedQuery_region_mono {d : ℕ} {S T : SourceFiniteEdgeRevealState d}
    (hST : S.explored ⊆ T.explored) (center : Cubic d)
    (a : CubicDirection d) (transverseFlip : Fin d → Bool) :
    (S.framedQuery center a transverseFlip).region ⊆
      (T.framedQuery center a transverseFlip).region := by
  classical
  let F := cubicRestartFrameIso center a transverseFlip
  intro z hz
  change z ∈ cubicEdgeEndpointVertices (S.referenceExploredEdges F) at hz
  change z ∈ cubicEdgeEndpointVertices (T.referenceExploredEdges F)
  obtain ⟨e, heS, hze⟩ := mem_cubicEdgeEndpointVertices_iff.mp hz
  apply mem_cubicEdgeEndpointVertices_iff.mpr
  refine ⟨e, ?_, hze⟩
  rw [SourceFiniteEdgeRevealState.referenceExploredEdges, Finset.mem_image] at heS ⊢
  obtain ⟨f, hfS, hfe⟩ := heS
  exact ⟨f, hST hfS, hfe⟩

/-- If the physical explored state contains the complete seed box around the center of a
canonical frame, then the query's reference-coordinate region contains the inlet box around
the origin.  This is the generic handoff between consecutive successful restart slots. -/
theorem cubicMetricBox_subset_framedQuery_region_of_seedBox
    {d m : ℕ} [NeZero d] (S : SourceFiniteEdgeRevealState d)
    (hm : 1 ≤ m) (center : Cubic d) (a : CubicDirection d)
    (transverseFlip : Fin d → Bool)
    (hseed : cubicBoxEdges d center m ⊆ S.explored) :
    cubicMetricBox d cubicOrigin m ⊆
      (S.framedQuery center a transverseFlip).region := by
  classical
  let F := cubicRestartFrameIso center a transverseFlip
  intro z hz
  have hzEndpoint : z ∈ cubicEdgeEndpointVertices (cubicBoxEdges d cubicOrigin m) :=
    cubicMetricBox_subset_cubicEdgeEndpointVertices_cubicBoxEdges hm hz
  obtain ⟨f, hfBox, hzf⟩ := mem_cubicEdgeEndpointVertices_iff.mp hzEndpoint
  have hfPhysicalBox : F.mapEdgeSet f ∈ cubicBoxEdges d center m := by
    have hfImage : F.mapEdgeSet f ∈
        (cubicBoxEdges d cubicOrigin m).image F.mapEdgeSet :=
      Finset.mem_image.mpr ⟨f, hfBox, rfl⟩
    rw [show (cubicBoxEdges d cubicOrigin m).image F.mapEdgeSet =
        cubicBoxEdges d center m by
      simpa [F] using cubicRestartFrameIso_image_cubicBoxEdges_eq
        (n := m) center a transverseFlip] at hfImage
    exact hfImage
  have hfExplored : F.mapEdgeSet f ∈ S.explored := hseed hfPhysicalBox
  have hfReference : f ∈ S.referenceExploredEdges F := by
    rw [SourceFiniteEdgeRevealState.referenceExploredEdges, Finset.mem_image]
    refine ⟨F.mapEdgeSet f, hfExplored, ?_⟩
    change F.mapEdgeSet.symm (F.mapEdgeSet f) = f
    exact F.mapEdgeSet.symm_apply_apply f
  change z ∈ cubicEdgeEndpointVertices (S.referenceExploredEdges F)
  exact mem_cubicEdgeEndpointVertices_iff.mpr ⟨f, hfReference, hzf⟩

/-- The canonical query's transported boundary threshold is exactly the source state's
physical lower threshold. -/
@[simp]
theorem framedQuery_physicalBoundaryThreshold {d : ℕ}
    (S : SourceFiniteEdgeRevealState d) (center : Cubic d)
    (a : CubicDirection d) (transverseFlip : Fin d → Bool)
    (e : CubicEdge d) :
    (S.framedQuery center a transverseFlip).physicalBoundaryThreshold e = S.lower e := by
  let F := cubicRestartFrameIso center a transverseFlip
  change S.lower (F.mapEdgeSet (F.symm.mapEdgeSet e)) = S.lower e
  have hsymm : F.symm.mapEdgeSet e = F.mapEdgeSet.symm e := rfl
  rw [hsymm, Equiv.apply_symm_apply]

/-- Lemma 7.17 for a canonical source-state query.  Once the inlet seed, unused target layer,
and one-step threshold budget are known, the transported threshold bound is automatic. -/
theorem framedQuery_uniformRestart
    {d m n : ℕ} (S : SourceFiniteEdgeRevealState d)
    (center : Cubic d) (a : CubicDirection d) (transverseFlip : Fin d → Bool)
    (p : I) (delta epsilon : ℝ)
    (huniform : UniformRestartBounds d m n p delta epsilon)
    (hmn : m ≤ n)
    (hseed : cubicMetricBox d cubicOrigin m ⊆
      (S.framedQuery center a transverseFlip).region)
    (hAvoid : RegionAvoidsSeededBoundaryQuadrant d a.1 n
      ((S.framedQuery center a transverseFlip).croppedRegion n))
    (hbudget : S.HasIncrementBudget delta) :
    let Q := S.framedQuery center a transverseFlip
    (1 - epsilon) * (couplingMeasure (CubicEdge d)).real
        (Q.boundaryHistoryEvent n) <
      (couplingMeasure (CubicEdge d)).real
        (Q.successEvent m n p delta ∩ Q.boundaryHistoryEvent n) := by
  let Q := S.framedQuery center a transverseFlip
  apply Q.uniformRestartBounds_of_croppedRegion p delta epsilon huniform hmn hseed hAvoid
  intro e _he
  change (S.lower ((cubicRestartFrameIso center a transverseFlip).mapEdgeSet e) : ℝ) +
      delta ≤ 1
  exact hbudget _

/-- The exact framed boundary identity required by
`ofSourceEdgeStateRealization`.  Internal closed chords are omitted by the restart support;
after transport, it remains only to prove that the genuinely new target-seed coordinates do
not meet the old global boundary. -/
theorem framedQuery_boundarySupport_eq_boundary_inter_restartSupport
    {d m n : ℕ} (S : SourceFiniteEdgeRevealState d)
    (center : Cubic d) (a : CubicDirection d) (transverseFlip : Fin d → Bool)
    (hTargetFresh :
      let F := cubicRestartFrameIso center a transverseFlip
      Disjoint (cubicEdgeBoundary (S.referenceExploredEdges F))
        (seededBoundaryTargetSupport d a.1 m n)) :
    (S.framedQuery center a transverseFlip).boundarySupport n =
      S.boundary ∩
        (S.framedQuery center a transverseFlip).restartSupport m n := by
  classical
  let F := cubicRestartFrameIso center a transverseFlip
  change
    (cubicRegionBoundaryEdgesWithinBox d
        (cubicEdgeEndpointVertices (S.referenceExploredEdges F)) n).image F.mapEdgeSet =
      cubicEdgeBoundary S.explored ∩
        (restartEventSupport d a.1 m n
          (cubicEdgeEndpointVertices (S.referenceExploredEdges F))).image F.mapEdgeSet
  rw [cubicRegionBoundary_endpointVertices_eq_boundary_inter_restartEventSupport
      (S.referenceExploredEdges F) a.1 hTargetFresh,
    Finset.image_inter _ _ F.mapEdgeSet.injective,
    cubicEdgeBoundary_image_cubicGraphIso,
    S.referenceExploredEdges_image]

/-- Endpoint separation is the single geometric premise needed for the canonical framed
boundary identity.  In particular, a steering proof does not have to reason separately about
the line-graph boundary of the previously explored edge set. -/
theorem framedQuery_boundarySupport_eq_boundary_inter_restartSupport_of_targetEndpointFresh
    {d m n : ℕ} (S : SourceFiniteEdgeRevealState d)
    (center : Cubic d) (a : CubicDirection d) (transverseFlip : Fin d → Bool)
    (hVertices :
      let F := cubicRestartFrameIso center a transverseFlip
      Disjoint (cubicEdgeEndpointVertices (S.referenceExploredEdges F))
        (cubicEdgeEndpointVertices (seededBoundaryTargetSupport d a.1 m n))) :
    (S.framedQuery center a transverseFlip).boundarySupport n =
      S.boundary ∩
        (S.framedQuery center a transverseFlip).restartSupport m n := by
  apply S.framedQuery_boundarySupport_eq_boundary_inter_restartSupport
  exact disjoint_cubicEdgeBoundary_target_of_endpointVertices _ _ hVertices

/-- The same endpoint separation also proves that no previously explored open edge is read by
the new framed restart.  Boundary and exterior coordinates are fresh by construction; target
coordinates are fresh because neither endpoint has previously been incident to an explored
edge. -/
theorem framedQuery_explored_disjoint_restartSupport_of_targetEndpointFresh
    {d m n : ℕ} (S : SourceFiniteEdgeRevealState d)
    (center : Cubic d) (a : CubicDirection d) (transverseFlip : Fin d → Bool)
    (hVertices :
      let F := cubicRestartFrameIso center a transverseFlip
      Disjoint (cubicEdgeEndpointVertices (S.referenceExploredEdges F))
        (cubicEdgeEndpointVertices (seededBoundaryTargetSupport d a.1 m n))) :
    Disjoint (S.explored : Set (CubicEdge d))
      ((S.framedQuery center a transverseFlip).restartSupport m n :
        Set (CubicEdge d)) := by
  classical
  let F := cubicRestartFrameIso center a transverseFlip
  have href : Disjoint (S.referenceExploredEdges F)
      (restartEventSupport d a.1 m n
        (cubicEdgeEndpointVertices (S.referenceExploredEdges F))) :=
    disjoint_explored_restartEventSupport_of_targetEndpointFresh
      (S.referenceExploredEdges F) a.1 hVertices
  rw [Set.disjoint_left]
  intro e heExplored heRestart
  change e ∈ (S.framedQuery center a transverseFlip).restartSupport m n at heRestart
  rw [FramedRestartQuery.restartSupport, framedRestartSupport, Finset.mem_image] at heRestart
  obtain ⟨f, hfRestart, rfl⟩ := heRestart
  have hfImage : F.mapEdgeSet f ∈
      (S.referenceExploredEdges F).image F.mapEdgeSet := by
    rw [S.referenceExploredEdges_image F]
    exact heExplored
  obtain ⟨g, hgExplored, hgf⟩ := Finset.mem_image.mp hfImage
  have hgf' : g = f := F.mapEdgeSet.injective hgf
  subst g
  exact Finset.disjoint_left.mp href hgExplored hfRestart

end SourceFiniteEdgeRevealState

namespace AdaptiveSiteExploration

variable {C : Type*} [Fintype C] [DecidableEq C]

/-- If a query consumes exactly the part of the global boundary in its restart support, then
the unconsumed global-boundary constraints are disjoint from that support. -/
theorem sourceBoundary_sdiff_query_disjoint_restartSupport
    {d m n : ℕ} (S : SourceFiniteEdgeRevealState d) (Q : FramedRestartQuery d)
    (hboundary : Q.boundarySupport n = S.boundary ∩ Q.restartSupport m n) :
    Disjoint (((S.boundary \ Q.boundarySupport n : Finset (CubicEdge d)) :
      Set (CubicEdge d))) (Q.restartSupport m n : Set (CubicEdge d)) := by
  rw [Set.disjoint_left]
  intro e heResidual heRestart
  change e ∈ S.boundary \ Q.boundarySupport n at heResidual
  have heBoundary := (Finset.mem_sdiff.mp heResidual).1
  have heQuery : e ∈ Q.boundarySupport n := by
    rw [hboundary]
    exact Finset.mem_inter.mpr ⟨heBoundary, heRestart⟩
  exact (Finset.mem_sdiff.mp heResidual).2 heQuery

/-- Construct a partitioned framed restart from the source-faithful global-boundary state.

Unlike the fixed-ambient helper above, the source state retains every edge of the global
line-graph boundary `ΔE`.  The current framed query uses exactly the intersection of that
boundary with its restart support.  This equality automatically proves that every residual
closed constraint is fresh from the query; the only remaining freshness obligation concerns
the already explored open edges.
-/
noncomputable def PartitionedFramedRestartStage.ofSourceEdgeStateRealization
    {d m n : ℕ} {p : I} {delta epsilon : ℝ}
    (history : Set (CubicEdge d → ℝ))
    (realizedCell : (CubicEdge d → ℝ) → C)
    (query : C → FramedRestartQuery d)
    (state : C → SourceFiniteEdgeRevealState d)
    (hboundary : ∀ c, (query c).boundarySupport n =
      (state c).boundary ∩ (query c).restartSupport m n)
    (hlower : ∀ c e, e ∈ (query c).boundarySupport n →
      (state c).lower e = (query c).physicalBoundaryThreshold e)
    (hfiber : ∀ c, (state c).historyProfile.event =
      exactRevealCellEvent history realizedCell c)
    (hfreshOpen : ∀ c,
      Disjoint ((state c).explored : Set (CubicEdge d))
        ((query c).restartSupport m n : Set (CubicEdge d)))
    (hrestart : ∀ c,
      (1 - epsilon) * (couplingMeasure (CubicEdge d)).real
          ((query c).boundaryHistoryEvent n) <
        (couplingMeasure (CubicEdge d)).real
          ((query c).successEvent m n p delta ∩
            (query c).boundaryHistoryEvent n)) :
    PartitionedFramedRestartStage d C m n p delta epsilon := by
  classical
  apply PartitionedFramedRestartStage.ofIntervalProfileRealization
    history realizedCell query (fun c ↦ (state c).historyProfile)
  · intro c e he
    change e ∈ (state c).explored ∪ (state c).boundary
    rw [hboundary c] at he
    exact Finset.mem_union_right _ (Finset.mem_inter.mp he).1
  · exact hlower
  · exact hfiber
  · intro c
    rw [Set.disjoint_left]
    intro e heResidual heRestart
    change e ∈
      ((state c).explored ∪ (state c).boundary) \ (query c).boundarySupport n at heResidual
    obtain ⟨heHistory, heNotQuery⟩ := Finset.mem_sdiff.mp heResidual
    rcases Finset.mem_union.mp heHistory with heExplored | heBoundary
    · exact Set.disjoint_left.mp (hfreshOpen c) heExplored heRestart
    · have hresidual : e ∈ (state c).boundary \ (query c).boundarySupport n :=
        Finset.mem_sdiff.mpr ⟨heBoundary, heNotQuery⟩
      exact Set.disjoint_left.mp
        (sourceBoundary_sdiff_query_disjoint_restartSupport
          (state c) (query c) (hboundary c)) hresidual heRestart
  · intro c
    simpa [SourceFiniteEdgeRevealState.historyProfile] using hfreshOpen c
  · exact hrestart

/-- The literal source-state cells cover the supplied history exactly. -/
theorem PartitionedFramedRestartStage.cellUnion_ofSourceEdgeStateRealization
    {d m n : ℕ} {p : I} {delta epsilon : ℝ}
    (history : Set (CubicEdge d → ℝ))
    (realizedCell : (CubicEdge d → ℝ) → C)
    (query : C → FramedRestartQuery d)
    (state : C → SourceFiniteEdgeRevealState d)
    (hboundary : ∀ c, (query c).boundarySupport n =
      (state c).boundary ∩ (query c).restartSupport m n)
    (hlower : ∀ c e, e ∈ (query c).boundarySupport n →
      (state c).lower e = (query c).physicalBoundaryThreshold e)
    (hfiber : ∀ c, (state c).historyProfile.event =
      exactRevealCellEvent history realizedCell c)
    (hfreshOpen : ∀ c,
      Disjoint ((state c).explored : Set (CubicEdge d))
        ((query c).restartSupport m n : Set (CubicEdge d)))
    (hrestart : ∀ c,
      (1 - epsilon) * (couplingMeasure (CubicEdge d)).real
          ((query c).boundaryHistoryEvent n) <
        (couplingMeasure (CubicEdge d)).real
          ((query c).successEvent m n p delta ∩
            (query c).boundaryHistoryEvent n)) :
    (PartitionedFramedRestartStage.ofSourceEdgeStateRealization
      history realizedCell query state hboundary hlower hfiber hfreshOpen hrestart).cellUnion =
        history := by
  classical
  unfold PartitionedFramedRestartStage.ofSourceEdgeStateRealization
  apply PartitionedFramedRestartStage.cellUnion_ofIntervalProfileRealization

/-- Canonical source-stage constructor.  The query, its random endpoint region, and its
transported threshold profile are derived from the source state itself.  Therefore the generic
boundary and threshold obligations disappear: a caller supplies only target-seed freshness,
freshness of the already explored open edges, the exact finite fiber, and Lemma 7.17. -/
noncomputable def PartitionedFramedRestartStage.ofCanonicalSourceEdgeStateRealization
    {d m n : ℕ} {p : I} {delta epsilon : ℝ}
    (history : Set (CubicEdge d → ℝ))
    (realizedCell : (CubicEdge d → ℝ) → C)
    (center : C → Cubic d) (direction : C → CubicDirection d)
    (transverseFlip : C → Fin d → Bool)
    (state : C → SourceFiniteEdgeRevealState d)
    (hTargetFresh : ∀ c,
      let F := cubicRestartFrameIso (center c) (direction c) (transverseFlip c)
      Disjoint (cubicEdgeBoundary ((state c).referenceExploredEdges F))
        (seededBoundaryTargetSupport d (direction c).1 m n))
    (hfiber : ∀ c, (state c).historyProfile.event =
      exactRevealCellEvent history realizedCell c)
    (hfreshOpen : ∀ c,
      Disjoint ((state c).explored : Set (CubicEdge d))
        (((state c).framedQuery (center c) (direction c) (transverseFlip c)).restartSupport
          m n : Set (CubicEdge d)))
    (hrestart : ∀ c,
      let Q := (state c).framedQuery (center c) (direction c) (transverseFlip c)
      (1 - epsilon) * (couplingMeasure (CubicEdge d)).real
          (Q.boundaryHistoryEvent n) <
        (couplingMeasure (CubicEdge d)).real
          (Q.successEvent m n p delta ∩ Q.boundaryHistoryEvent n)) :
    PartitionedFramedRestartStage d C m n p delta epsilon := by
  let query : C → FramedRestartQuery d := fun c ↦
    (state c).framedQuery (center c) (direction c) (transverseFlip c)
  apply PartitionedFramedRestartStage.ofSourceEdgeStateRealization
    history realizedCell query state
  · intro c
    exact (state c).framedQuery_boundarySupport_eq_boundary_inter_restartSupport
      (center c) (direction c) (transverseFlip c) (hTargetFresh c)
  · intro c e _he
    exact ((state c).framedQuery_physicalBoundaryThreshold
      (center c) (direction c) (transverseFlip c) e).symm
  · exact hfiber
  · exact hfreshOpen
  · exact hrestart

/-- The canonical source-state cells cover their outer history exactly. -/
theorem PartitionedFramedRestartStage.cellUnion_ofCanonicalSourceEdgeStateRealization
    {d m n : ℕ} {p : I} {delta epsilon : ℝ}
    (history : Set (CubicEdge d → ℝ))
    (realizedCell : (CubicEdge d → ℝ) → C)
    (center : C → Cubic d) (direction : C → CubicDirection d)
    (transverseFlip : C → Fin d → Bool)
    (state : C → SourceFiniteEdgeRevealState d)
    (hTargetFresh : ∀ c,
      let F := cubicRestartFrameIso (center c) (direction c) (transverseFlip c)
      Disjoint (cubicEdgeBoundary ((state c).referenceExploredEdges F))
        (seededBoundaryTargetSupport d (direction c).1 m n))
    (hfiber : ∀ c, (state c).historyProfile.event =
      exactRevealCellEvent history realizedCell c)
    (hfreshOpen : ∀ c,
      Disjoint ((state c).explored : Set (CubicEdge d))
        (((state c).framedQuery (center c) (direction c) (transverseFlip c)).restartSupport
          m n : Set (CubicEdge d)))
    (hrestart : ∀ c,
      let Q := (state c).framedQuery (center c) (direction c) (transverseFlip c)
      (1 - epsilon) * (couplingMeasure (CubicEdge d)).real
          (Q.boundaryHistoryEvent n) <
        (couplingMeasure (CubicEdge d)).real
          (Q.successEvent m n p delta ∩ Q.boundaryHistoryEvent n)) :
    (PartitionedFramedRestartStage.ofCanonicalSourceEdgeStateRealization
      history realizedCell center direction transverseFlip state hTargetFresh hfiber
        hfreshOpen hrestart).cellUnion = history := by
  classical
  unfold PartitionedFramedRestartStage.ofCanonicalSourceEdgeStateRealization
  apply PartitionedFramedRestartStage.cellUnion_ofSourceEdgeStateRealization

/-- Fully reduced canonical source-stage constructor.  Both freshness conditions required by
the probabilistic partition theorem follow from one source-geometric statement: in reference
coordinates, no endpoint of the new target-seed support has previously been incident to an
explored edge. -/
noncomputable def
    PartitionedFramedRestartStage.ofCanonicalSourceEdgeStateRealizationOfTargetEndpointFresh
    {d m n : ℕ} {p : I} {delta epsilon : ℝ}
    (history : Set (CubicEdge d → ℝ))
    (realizedCell : (CubicEdge d → ℝ) → C)
    (center : C → Cubic d) (direction : C → CubicDirection d)
    (transverseFlip : C → Fin d → Bool)
    (state : C → SourceFiniteEdgeRevealState d)
    (hVertices : ∀ c,
      let F := cubicRestartFrameIso (center c) (direction c) (transverseFlip c)
      Disjoint (cubicEdgeEndpointVertices ((state c).referenceExploredEdges F))
        (cubicEdgeEndpointVertices
          (seededBoundaryTargetSupport d (direction c).1 m n)))
    (hfiber : ∀ c, (state c).historyProfile.event =
      exactRevealCellEvent history realizedCell c)
    (hrestart : ∀ c,
      let Q := (state c).framedQuery (center c) (direction c) (transverseFlip c)
      (1 - epsilon) * (couplingMeasure (CubicEdge d)).real
          (Q.boundaryHistoryEvent n) <
        (couplingMeasure (CubicEdge d)).real
          (Q.successEvent m n p delta ∩ Q.boundaryHistoryEvent n)) :
    PartitionedFramedRestartStage d C m n p delta epsilon := by
  apply PartitionedFramedRestartStage.ofCanonicalSourceEdgeStateRealization
    history realizedCell center direction transverseFlip state
  · intro c
    exact disjoint_cubicEdgeBoundary_target_of_endpointVertices _ _ (hVertices c)
  · exact hfiber
  · intro c
    exact (state c).framedQuery_explored_disjoint_restartSupport_of_targetEndpointFresh
      (center c) (direction c) (transverseFlip c) (hVertices c)
  · exact hrestart

@[simp]
theorem
    PartitionedFramedRestartStage.query_ofCanonicalSourceEdgeStateRealizationOfTargetEndpointFresh
    {d m n : ℕ} {p : I} {delta epsilon : ℝ}
    (history : Set (CubicEdge d → ℝ))
    (realizedCell : (CubicEdge d → ℝ) → C)
    (center : C → Cubic d) (direction : C → CubicDirection d)
    (transverseFlip : C → Fin d → Bool)
    (state : C → SourceFiniteEdgeRevealState d)
    (hVertices : ∀ c,
      let F := cubicRestartFrameIso (center c) (direction c) (transverseFlip c)
      Disjoint (cubicEdgeEndpointVertices ((state c).referenceExploredEdges F))
        (cubicEdgeEndpointVertices
          (seededBoundaryTargetSupport d (direction c).1 m n)))
    (hfiber : ∀ c, (state c).historyProfile.event =
      exactRevealCellEvent history realizedCell c)
    (hrestart : ∀ c,
      let Q := (state c).framedQuery (center c) (direction c) (transverseFlip c)
      (1 - epsilon) * (couplingMeasure (CubicEdge d)).real
          (Q.boundaryHistoryEvent n) <
        (couplingMeasure (CubicEdge d)).real
          (Q.successEvent m n p delta ∩ Q.boundaryHistoryEvent n))
    (c : C) :
    (PartitionedFramedRestartStage.ofCanonicalSourceEdgeStateRealizationOfTargetEndpointFresh
      history realizedCell center direction transverseFlip state hVertices hfiber
        hrestart).query c =
      (state c).framedQuery (center c) (direction c) (transverseFlip c) :=
  rfl

/-- The reduced canonical source-state constructor retains each literal accumulated-history
cell. -/
theorem
    PartitionedFramedRestartStage.cell_ofCanonicalSourceEdgeStateRealizationOfTargetEndpointFresh
    {d m n : ℕ} {p : I} {delta epsilon : ℝ}
    (history : Set (CubicEdge d → ℝ))
    (realizedCell : (CubicEdge d → ℝ) → C)
    (center : C → Cubic d) (direction : C → CubicDirection d)
    (transverseFlip : C → Fin d → Bool)
    (state : C → SourceFiniteEdgeRevealState d)
    (hVertices : ∀ c,
      let F := cubicRestartFrameIso (center c) (direction c) (transverseFlip c)
      Disjoint (cubicEdgeEndpointVertices ((state c).referenceExploredEdges F))
        (cubicEdgeEndpointVertices
          (seededBoundaryTargetSupport d (direction c).1 m n)))
    (hfiber : ∀ c, (state c).historyProfile.event =
      exactRevealCellEvent history realizedCell c)
    (hrestart : ∀ c,
      let Q := (state c).framedQuery (center c) (direction c) (transverseFlip c)
      (1 - epsilon) * (couplingMeasure (CubicEdge d)).real
          (Q.boundaryHistoryEvent n) <
        (couplingMeasure (CubicEdge d)).real
          (Q.successEvent m n p delta ∩ Q.boundaryHistoryEvent n))
    (c : C) :
    (PartitionedFramedRestartStage.ofCanonicalSourceEdgeStateRealizationOfTargetEndpointFresh
      history realizedCell center direction transverseFlip state hVertices hfiber
        hrestart).cell c = (state c).historyProfile.event := by
  unfold PartitionedFramedRestartStage.ofCanonicalSourceEdgeStateRealizationOfTargetEndpointFresh
  unfold PartitionedFramedRestartStage.ofCanonicalSourceEdgeStateRealization
  unfold PartitionedFramedRestartStage.ofSourceEdgeStateRealization
  apply PartitionedFramedRestartStage.cell_ofIntervalProfileRealization

/-- Exact coverage of the outer history for the endpoint-fresh canonical constructor. -/
theorem
    PartitionedFramedRestartStage.cellUnion_ofCanonicalSourceEdgeStateRealizationOfTargetEndpointFresh
    {d m n : ℕ} {p : I} {delta epsilon : ℝ}
    (history : Set (CubicEdge d → ℝ))
    (realizedCell : (CubicEdge d → ℝ) → C)
    (center : C → Cubic d) (direction : C → CubicDirection d)
    (transverseFlip : C → Fin d → Bool)
    (state : C → SourceFiniteEdgeRevealState d)
    (hVertices : ∀ c,
      let F := cubicRestartFrameIso (center c) (direction c) (transverseFlip c)
      Disjoint (cubicEdgeEndpointVertices ((state c).referenceExploredEdges F))
        (cubicEdgeEndpointVertices
          (seededBoundaryTargetSupport d (direction c).1 m n)))
    (hfiber : ∀ c, (state c).historyProfile.event =
      exactRevealCellEvent history realizedCell c)
    (hrestart : ∀ c,
      let Q := (state c).framedQuery (center c) (direction c) (transverseFlip c)
      (1 - epsilon) * (couplingMeasure (CubicEdge d)).real
          (Q.boundaryHistoryEvent n) <
        (couplingMeasure (CubicEdge d)).real
          (Q.successEvent m n p delta ∩ Q.boundaryHistoryEvent n)) :
    (PartitionedFramedRestartStage.ofCanonicalSourceEdgeStateRealizationOfTargetEndpointFresh
        history realizedCell center direction transverseFlip state hVertices hfiber
          hrestart).cellUnion = history := by
  classical
  unfold PartitionedFramedRestartStage.ofCanonicalSourceEdgeStateRealizationOfTargetEndpointFresh
  apply PartitionedFramedRestartStage.cellUnion_ofCanonicalSourceEdgeStateRealization

/-- Semantic form of the endpoint-fresh canonical constructor: its successful union uses the
query belonging to the exact source-state cell realized by the configuration. -/
theorem
    PartitionedFramedRestartStage.successEvent_eq_semantic_ofCanonicalSourceEdgeStateRealizationOfTargetEndpointFresh
    {d m n : ℕ} {p : I} {delta epsilon : ℝ}
    (history : Set (CubicEdge d → ℝ))
    (realizedCell : (CubicEdge d → ℝ) → C)
    (center : C → Cubic d) (direction : C → CubicDirection d)
    (transverseFlip : C → Fin d → Bool)
    (state : C → SourceFiniteEdgeRevealState d)
    (hVertices : ∀ c,
      let F := cubicRestartFrameIso (center c) (direction c) (transverseFlip c)
      Disjoint (cubicEdgeEndpointVertices ((state c).referenceExploredEdges F))
        (cubicEdgeEndpointVertices
          (seededBoundaryTargetSupport d (direction c).1 m n)))
    (hfiber : ∀ c, (state c).historyProfile.event =
      exactRevealCellEvent history realizedCell c)
    (hrestart : ∀ c,
      let Q := (state c).framedQuery (center c) (direction c) (transverseFlip c)
      (1 - epsilon) * (couplingMeasure (CubicEdge d)).real
          (Q.boundaryHistoryEvent n) <
        (couplingMeasure (CubicEdge d)).real
          (Q.successEvent m n p delta ∩ Q.boundaryHistoryEvent n)) :
    (PartitionedFramedRestartStage.ofCanonicalSourceEdgeStateRealizationOfTargetEndpointFresh
      history realizedCell center direction transverseFlip state hVertices hfiber
        hrestart).successEvent =
      {X | X ∈ history ∧
        X ∈ ((state (realizedCell X)).framedQuery (center (realizedCell X))
          (direction (realizedCell X)) (transverseFlip (realizedCell X))).successEvent
            m n p delta} := by
  let S :=
    PartitionedFramedRestartStage.ofCanonicalSourceEdgeStateRealizationOfTargetEndpointFresh
      history realizedCell center direction transverseFlip state hVertices hfiber hrestart
  apply S.successEvent_eq_semantic_of_exactRealization history realizedCell rfl
  intro c
  simpa [S] using
    (PartitionedFramedRestartStage.cell_ofCanonicalSourceEdgeStateRealizationOfTargetEndpointFresh
      history realizedCell center direction transverseFlip state hVertices hfiber hrestart c
      |>.trans (hfiber c))

end AdaptiveSiteExploration

end Percolation
