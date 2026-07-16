import Percolation.Critical.DynamicFramedStateStage
import Percolation.Critical.DynamicSeedWitness

/-!
# Stability of a successful framed restart under the source update

The literal source recursion records an accumulated interval history after every finite
restart.  This file proves the local semantic fact needed to compose those restarts: an exit
edge absorbed from the old boundary remains open at its incremented threshold, while every
newly explored exterior edge remains open at the background density.
-/

namespace Percolation

open scoped unitInterval

namespace SourceFiniteEdgeRevealState

/-- An absorbed old-boundary edge remains open at its incremented threshold throughout the
successor accumulated-history cell. -/
theorem label_lt_incremented_of_mem_nextHistoryProfile
    {d : ℕ} (S : SourceFiniteEdgeRevealState d)
    (stageRegion : Finset (CubicEdge d)) (p : I)
    (incremented : CubicEdge d → I) (X Y : CubicEdge d → ℝ) {e : CubicEdge d}
    (heBoundary : e ∈ S.boundary)
    (heNext : e ∈ S.nextExplored stageRegion p incremented X)
    (hY : Y ∈ (S.next stageRegion p incremented X).historyProfile.event) :
    Y e < (incremented e : ℝ) := by
  have heNotOld : e ∉ S.explored :=
    (mem_cubicEdgeBoundary_iff.mp heBoundary).1
  have hOpen := hY.2 e heNext
  change Y e <
    ((S.updateData stageRegion p incremented X).updatedUpper e : ℝ) at hOpen
  rw [RevealThresholdUpdateData.updatedUpper_eq_incremented_of_mem_absorbedBoundary
    _ heNotOld heBoundary heNext] at hOpen
  exact hOpen

/-- A newly explored edge outside the old explored set and its global boundary remains open
at the background density throughout the successor accumulated-history cell. -/
theorem label_lt_density_of_mem_nextHistoryProfile
    {d : ℕ} (S : SourceFiniteEdgeRevealState d)
    (stageRegion : Finset (CubicEdge d)) (p : I)
    (incremented : CubicEdge d → I) (X Y : CubicEdge d → ℝ) {e : CubicEdge d}
    (heNotOld : e ∉ S.explored) (heNotBoundary : e ∉ S.boundary)
    (heNext : e ∈ S.nextExplored stageRegion p incremented X)
    (hY : Y ∈ (S.next stageRegion p incremented X).historyProfile.event) :
    Y e < (p : ℝ) := by
  have hOpen := hY.2 e heNext
  change Y e <
    ((S.updateData stageRegion p incremented X).updatedUpper e : ℝ) at hOpen
  rw [RevealThresholdUpdateData.updatedUpper_eq_density_of_mem_newInterior
    _ heNotOld heNotBoundary heNext] at hOpen
  exact hOpen

end SourceFiniteEdgeRevealState

/-- A non-boundary reference coordinate read by a canonical framed query is a genuinely new
interior coordinate of the physical source update.  Endpoint freshness rules out an old
explored target edge, while the canonical boundary identity rules out an old global-boundary
edge. -/
theorem SourceFiniteEdgeRevealState.mapEdgeSet_mem_sourceStageExterior_of_restartSupport
    {d m n : ℕ} (S : SourceFiniteEdgeRevealState d)
    (center : Cubic d) (a : CubicDirection d) (transverseFlip : Fin d → Bool)
    (hTargetFresh :
      let F := cubicRestartFrameIso center a transverseFlip
      Disjoint (cubicEdgeEndpointVertices (S.referenceExploredEdges F))
        (cubicEdgeEndpointVertices (seededBoundaryTargetSupport d a.1 m n)))
    {f : CubicEdge d}
    (hfSupport : f ∈ restartEventSupport d a.1 m n
      (cubicEdgeEndpointVertices
        (S.referenceExploredEdges (cubicRestartFrameIso center a transverseFlip))))
    (hfNotBoundary : f ∉ cubicRegionBoundaryEdgesWithinBox d
      (cubicEdgeEndpointVertices
        (S.referenceExploredEdges (cubicRestartFrameIso center a transverseFlip))) n) :
    (cubicRestartFrameIso center a transverseFlip).mapEdgeSet f ∈
      sourceStageExterior S.explored
        ((S.framedQuery center a transverseFlip).restartSupport m n) := by
  classical
  let F := cubicRestartFrameIso center a transverseFlip
  let Q := S.framedQuery center a transverseFlip
  have hfStage : F.mapEdgeSet f ∈ Q.restartSupport m n := by
    exact Finset.mem_image.mpr ⟨f, hfSupport, rfl⟩
  have hDisjoint : Disjoint (S.explored : Set (CubicEdge d))
      (Q.restartSupport m n : Set (CubicEdge d)) :=
    S.framedQuery_explored_disjoint_restartSupport_of_targetEndpointFresh
      center a transverseFlip hTargetFresh
  have hfNotOld : F.mapEdgeSet f ∉ S.explored := fun hfOld ↦
    Set.disjoint_left.mp hDisjoint hfOld hfStage
  have hboundary : Q.boundarySupport n =
      S.boundary ∩ Q.restartSupport m n :=
    S.framedQuery_boundarySupport_eq_boundary_inter_restartSupport_of_targetEndpointFresh
      center a transverseFlip hTargetFresh
  have hfNotOldBoundary : F.mapEdgeSet f ∉ S.boundary := by
    intro hfOldBoundary
    have hfPhysical : F.mapEdgeSet f ∈ Q.boundarySupport n := by
      rw [hboundary]
      exact Finset.mem_inter.mpr ⟨hfOldBoundary, hfStage⟩
    change F.mapEdgeSet f ∈
      framedBoundaryHistorySupport center a transverseFlip
        (cubicEdgeEndpointVertices (S.referenceExploredEdges F)) n at hfPhysical
    rw [framedBoundaryHistorySupport, Finset.mem_image] at hfPhysical
    obtain ⟨g, hgBoundary, hgf⟩ := hfPhysical
    have hgf' : g = f := F.mapEdgeSet.injective hgf
    exact hfNotBoundary (hgf' ▸ hgBoundary)
  rw [sourceStageExterior, Finset.mem_sdiff]
  exact ⟨hfStage, by
    intro h
    exact (Finset.mem_union.mp h).elim hfNotOld hfNotOldBoundary⟩

/-- The physical seed named by a successful mixed-threshold framed restart is absorbed into
the explored edge set of the literal successor state.  This is the geometric state invariant
used to start the next restart from the seed produced by the preceding one. -/
theorem SourceFiniteEdgeRevealState.mixedWitness_seedBox_subset_nextExplored_of_eq
    {d m n : ℕ} (S : SourceFiniteEdgeRevealState d)
    (center : Cubic d) (a : CubicDirection d) (transverseFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (incremented : CubicEdge d → I)
    (X : CubicEdge d → ℝ)
    (hTargetFresh :
      let F := cubicRestartFrameIso center a transverseFlip
      Disjoint (cubicEdgeEndpointVertices (S.referenceExploredEdges F))
        (cubicEdgeEndpointVertices (seededBoundaryTargetSupport d a.1 m n)))
    (hincremented : ∀ e ∈ (S.framedQuery center a transverseFlip).boundarySupport n,
      (incremented e : ℝ) =
        ((S.framedQuery center a transverseFlip).physicalBoundaryThreshold e : ℝ) + delta)
    (W : RestartSeedWitnessIndex d a.1 m n)
    (hW : W.IsMixedRestartWitness
      (S.framedQuery center a transverseFlip).region p
      (S.framedQuery center a transverseFlip).beta delta
      (cubicGraphIsoCouplingReindex
        (cubicRestartFrameIso center a transverseFlip) X)) :
    cubicBoxEdges d
        (cubicRestartFrameIso center a transverseFlip W.seedCenter.1) m ⊆
      S.nextExplored
        ((S.framedQuery center a transverseFlip).restartSupport m n)
        p incremented X := by
  classical
  let F := cubicRestartFrameIso center a transverseFlip
  let R := cubicEdgeEndpointVertices (S.referenceExploredEdges F)
  let Q := S.framedQuery center a transverseFlip
  let E := cubicRegionBoundaryEdgesWithinBox d R n
  let stageRegion := Q.restartSupport m n
  let Xref := cubicGraphIsoCouplingReindex F X
  let active := activeCubicEdgeBoundary S.explored stageRegion
  let exterior := sourceStageExterior S.explored stageRegion
  let B := finiteEdgesBelowFamily active incremented X
  let A := B ∪ finiteEdgesBelow exterior p X
  let C := finiteEdgeReachableClosure A B
  change W.IsMixedRestartWitness R p Q.beta delta Xref at hW
  rcases hW with ⟨hrealized, e, heBoundary, hconnection, heIncrement⟩
  rcases hrealized with ⟨hoCleared, hentryBox, hcLayer, hcSeed⟩
  rcases hconnection with ⟨w, hwOpen, hwExterior⟩
  have hePhysicalSupport : F.mapEdgeSet e ∈ Q.boundarySupport n := by
    change F.mapEdgeSet e ∈
      framedBoundaryHistorySupport center a transverseFlip R n
    exact Finset.mem_image.mpr ⟨e, heBoundary, rfl⟩
  have hboundary : Q.boundarySupport n = S.boundary ∩ stageRegion := by
    simpa [Q, stageRegion] using
      (S.framedQuery_boundarySupport_eq_boundary_inter_restartSupport_of_targetEndpointFresh
        center a transverseFlip hTargetFresh :
          Q.boundarySupport n = S.boundary ∩ Q.restartSupport m n)
  have heActive : F.mapEdgeSet e ∈ active := by
    change F.mapEdgeSet e ∈ S.boundary ∩ stageRegion
    exact hboundary ▸ hePhysicalSupport
  have hePhysicalOpen : X (F.mapEdgeSet e) < (incremented (F.mapEdgeSet e) : ℝ) := by
    rw [hincremented (F.mapEdgeSet e) (by simpa [Q] using hePhysicalSupport)]
    rw [S.framedQuery_physicalBoundaryThreshold]
    change Xref e < (S.lower (F.mapEdgeSet e) : ℝ) + delta
    change Xref e < (S.lower (F.mapEdgeSet e) : ℝ) + delta at heIncrement
    exact heIncrement
  have heB : F.mapEdgeSet e ∈ B :=
    mem_finiteEdgesBelowFamily_iff.mpr ⟨heActive, hePhysicalOpen⟩
  have heC : F.mapEdgeSet e ∈ C :=
    sources_subset_finiteEdgeReachableClosure
      (allowed := A) (sources := B) Finset.subset_union_left heB
  have referenceOpen_mem_A : ∀ {f : CubicEdge d},
      f ∈ restartEventSupport d a.1 m n R → f ∉ E → Xref f < (p : ℝ) →
        F.mapEdgeSet f ∈ A := by
    intro f hfSupport hfNotBoundary hfOpen
    apply Finset.mem_union_right
    rw [mem_finiteEdgesBelow_iff]
    refine ⟨?_, hfOpen⟩
    exact S.mapEdgeSet_mem_sourceStageExterior_of_restartSupport
      center a transverseFlip hTargetFresh hfSupport hfNotBoundary
  let y : Cubic d := W.boundaryPoint.1
  let o : CubicEdge d := cubicStepEdge y (a.1, true)
  have hoTarget : o ∈ seededBoundaryTargetSupport d a.1 m n :=
    cubicStepEdge_mem_seededBoundaryTargetSupport W.boundaryPoint.2
  have hoSupport : o ∈ restartEventSupport d a.1 m n R :=
    target_subset_restartEventSupport d a.1 m n R hoTarget
  have hoA : F.mapEdgeSet o ∈ A :=
    referenceOpen_mem_A hoSupport hoCleared.2 hoCleared.1
  let step : (cubicGraph d).Walk y (cubicStepFrom y (a.1, true)) :=
    SimpleGraph.Walk.cons (cubicGraph_adj_stepFrom y (a.1, true)) SimpleGraph.Walk.nil
  let q : (cubicGraph d).Walk
      (cubicRegionBoundaryOutsideEndpoint R e) (cubicStepFrom y (a.1, true)) :=
    w.append step
  let qPhysical := q.map F.toHom
  have hqPhysicalAllowed : walkEdgeFinset qPhysical ⊆ A := by
    intro g hg
    rw [mem_walkEdgeFinset_iff, SimpleGraph.Walk.edges_map] at hg
    obtain ⟨fSym, hfq, hfg⟩ := List.mem_map.mp hg
    let f : CubicEdge d := ⟨fSym, q.edges_subset_edgeSet hfq⟩
    have hmap : F.mapEdgeSet f = g := by
      apply Subtype.ext
      exact hfg
    rw [← hmap]
    change fSym ∈ (w.append step).edges at hfq
    rw [SimpleGraph.Walk.edges_append] at hfq
    rcases List.mem_append.mp hfq with hfw | hfstep
    · have hfExterior : f ∈ cubicRegionExteriorEdgesWithinBox d R n :=
        hwExterior ((mem_walkEdgeFinset_iff w f).mpr hfw)
      have hfCleared := hwOpen f.1 hfw
      exact referenceOpen_mem_A
        (exterior_subset_restartEventSupport d a.1 m n R hfExterior)
        hfCleared.2 hfCleared.1
    · have hfo : f = o := by
        apply Subtype.ext
        simpa [step, o] using hfstep
      simpa [hfo] using hoA
  have heStart : F (cubicRegionBoundaryOutsideEndpoint R e) ∈
      (F.mapEdgeSet e : Sym2 (Cubic d)) := by
    change F (cubicRegionBoundaryOutsideEndpoint R e) ∈ Sym2.map F (e : Sym2 (Cubic d))
    apply Sym2.mem_map.mpr
    refine ⟨cubicRegionBoundaryOutsideEndpoint R e, ?_, rfl⟩
    rw [← cubicRegionBoundaryEndpoints_edge heBoundary]
    simp
  have hqClosure : walkEdgeFinset qPhysical ⊆ C :=
    walkEdgeFinset_subset_finiteEdgeReachableClosure_of_incident
      qPhysical heC heStart hqPhysicalAllowed
  have hoPhysicalWalk : F.mapEdgeSet o ∈ walkEdgeFinset qPhysical := by
    rw [mem_walkEdgeFinset_iff, SimpleGraph.Walk.edges_map]
    apply List.mem_map.mpr
    refine ⟨(o : Sym2 (Cubic d)), ?_, rfl⟩
    change (o : Sym2 (Cubic d)) ∈ (w.append step).edges
    rw [SimpleGraph.Walk.edges_append]
    apply List.mem_append_right
    simp only [step, SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil,
      List.mem_singleton]
    rfl
  have hoC : F.mapEdgeSet o ∈ C := hqClosure hoPhysicalWalk
  have hseedAllowed : (cubicBoxEdges d W.seedCenter.1 m).image F.mapEdgeSet ⊆ A := by
    intro g hg
    obtain ⟨f, hfSeed, rfl⟩ := Finset.mem_image.mp hg
    have hfTarget := seedEdge_mem_seededBoundaryTargetSupport
      W.boundaryPoint.2 hentryBox hcLayer hfSeed
    have hfCleared := hcSeed hfSeed
    exact referenceOpen_mem_A
      (target_subset_restartEventSupport d a.1 m n R hfTarget)
      hfCleared.2 hfCleared.1
  have hentry : F (cubicStepFrom y (a.1, true)) ∈
      (F.mapEdgeSet o : Sym2 (Cubic d)) := by
    change F (cubicStepFrom y (a.1, true)) ∈ Sym2.map F (o : Sym2 (Cubic d))
    apply Sym2.mem_map.mpr
    exact ⟨cubicStepFrom y (a.1, true), by simp [o, cubicStepEdge], rfl⟩
  have hentryBox : F (cubicStepFrom y (a.1, true)) ∈
      cubicMetricBox d (F W.seedCenter.1) m :=
    (cubicRestartFrameIso_mem_cubicMetricBox_iff
      center a transverseFlip W.seedCenter.1 (cubicStepFrom y (a.1, true))).2 hentryBox
  have hseedClosure : cubicBoxEdges d (F W.seedCenter.1) m ⊆ C := by
    apply cubicBoxEdges_subset_finiteEdgeReachableClosure_of_incident
      hoC hentry hentryBox
    intro g hg
    obtain ⟨f, rfl⟩ := F.mapEdgeSet.surjective g
    apply hseedAllowed
    apply Finset.mem_image.mpr
    refine ⟨f, ?_, rfl⟩
    apply mem_cubicBoxEdges_of_endpoints
    intro z hz
    apply (cubicRestartFrameIso_mem_cubicMetricBox_iff
      center a transverseFlip W.seedCenter.1 z).1
    apply endpoint_mem_cubicMetricBox_of_edge_mem_cubicBoxEdges hg
    change F z ∈ Sym2.map F (f : Sym2 (Cubic d))
    exact Sym2.mem_map.mpr ⟨z, hz, rfl⟩
  intro g hg
  change g ∈ S.explored ∪ C
  exact Finset.mem_union_right _ (hseedClosure hg)

/-- A successful canonical framed restart remains successful throughout the accumulated-history
cell of its literal source successor.  The increment hypothesis is imposed only on the actual
physical boundary support; this is exactly the `beta(e)+delta` update used by Grimmett. -/
theorem SourceFiniteEdgeRevealState.framedSuccessEvent_of_mem_nextHistoryProfile
    {d m n : ℕ} (S : SourceFiniteEdgeRevealState d)
    (center : Cubic d) (a : CubicDirection d) (transverseFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (incremented : CubicEdge d → I)
    (X Y : CubicEdge d → ℝ)
    (hTargetFresh :
      let F := cubicRestartFrameIso center a transverseFlip
      Disjoint (cubicEdgeEndpointVertices (S.referenceExploredEdges F))
        (cubicEdgeEndpointVertices (seededBoundaryTargetSupport d a.1 m n)))
    (hincremented : ∀ e ∈ (S.framedQuery center a transverseFlip).boundarySupport n,
      (incremented e : ℝ) =
        ((S.framedQuery center a transverseFlip).physicalBoundaryThreshold e : ℝ) + delta)
    (hsuccess : X ∈ (S.framedQuery center a transverseFlip).successEvent m n p delta)
    (hY : Y ∈ (S.next
      ((S.framedQuery center a transverseFlip).restartSupport m n)
      p incremented X).historyProfile.event) :
    Y ∈ (S.framedQuery center a transverseFlip).successEvent m n p delta := by
  classical
  let F := cubicRestartFrameIso center a transverseFlip
  let R := cubicEdgeEndpointVertices (S.referenceExploredEdges F)
  let Q := S.framedQuery center a transverseFlip
  let E := cubicRegionBoundaryEdgesWithinBox d R n
  let stageRegion := Q.restartSupport m n
  let Xref := cubicGraphIsoCouplingReindex F X
  let Yref := cubicGraphIsoCouplingReindex F Y
  let active := activeCubicEdgeBoundary S.explored stageRegion
  let exterior := sourceStageExterior S.explored stageRegion
  let B := finiteEdgesBelowFamily active incremented X
  let A := B ∪ finiteEdgesBelow exterior p X
  let C := finiteEdgeReachableClosure A B
  change Xref ∈ sprinkledRestartEvent d a.1 m n R p Q.beta delta at hsuccess
  rcases hsuccess with ⟨e, heAvailable, heIncrement⟩
  change e ∈ seededRegionAvailableExitEdges d a.1 m n R
    (clearedThreshold E p Xref) at heAvailable
  rw [seededRegionAvailableExitEdges, mem_regionAvailableExitEdges_iff] at heAvailable
  rcases heAvailable with ⟨heBoundary, y, hyTarget, w, hwOpen, hwExterior⟩
  rw [mem_seededBoundaryPointFinset_iff] at hyTarget
  rcases hyTarget with ⟨hyQuadrant, hyOutward, c, hyc, hcLayer, hcSeed⟩
  have hePhysicalSupport : F.mapEdgeSet e ∈ Q.boundarySupport n := by
    change F.mapEdgeSet e ∈
      framedBoundaryHistorySupport center a transverseFlip R n
    exact Finset.mem_image.mpr ⟨e, heBoundary, rfl⟩
  have hboundary : Q.boundarySupport n = S.boundary ∩ stageRegion := by
    simpa [Q, stageRegion] using
      (S.framedQuery_boundarySupport_eq_boundary_inter_restartSupport_of_targetEndpointFresh
        center a transverseFlip hTargetFresh :
          Q.boundarySupport n = S.boundary ∩ Q.restartSupport m n)
  have heActive : F.mapEdgeSet e ∈ active := by
    change F.mapEdgeSet e ∈ S.boundary ∩ stageRegion
    exact hboundary ▸ hePhysicalSupport
  have hePhysicalOpen : X (F.mapEdgeSet e) < (incremented (F.mapEdgeSet e) : ℝ) := by
    rw [hincremented (F.mapEdgeSet e) (by simpa [Q] using hePhysicalSupport)]
    rw [S.framedQuery_physicalBoundaryThreshold]
    change Xref e < (S.lower (F.mapEdgeSet e) : ℝ) + delta
    change Xref e < (S.lower (F.mapEdgeSet e) : ℝ) + delta at heIncrement
    exact heIncrement
  have heB : F.mapEdgeSet e ∈ B :=
    mem_finiteEdgesBelowFamily_iff.mpr ⟨heActive, hePhysicalOpen⟩
  have heC : F.mapEdgeSet e ∈ C :=
    sources_subset_finiteEdgeReachableClosure
      (allowed := A) (sources := B) Finset.subset_union_left heB
  have heNext : F.mapEdgeSet e ∈ S.nextExplored stageRegion p incremented X := by
    change F.mapEdgeSet e ∈ S.explored ∪ C
    exact Finset.mem_union_right _ heC
  have referenceOpen_mem_A : ∀ {f : CubicEdge d},
      f ∈ restartEventSupport d a.1 m n R → f ∉ E → Xref f < (p : ℝ) →
        F.mapEdgeSet f ∈ A := by
    intro f hfSupport hfNotBoundary hfOpen
    apply Finset.mem_union_right
    rw [mem_finiteEdgesBelow_iff]
    refine ⟨?_, hfOpen⟩
    exact S.mapEdgeSet_mem_sourceStageExterior_of_restartSupport
      center a transverseFlip hTargetFresh hfSupport hfNotBoundary
  let o : CubicEdge d := cubicStepEdge y (a.1, true)
  have hoTarget : o ∈ seededBoundaryTargetSupport d a.1 m n :=
    cubicStepEdge_mem_seededBoundaryTargetSupport hyQuadrant
  have hoSupport : o ∈ restartEventSupport d a.1 m n R :=
    target_subset_restartEventSupport d a.1 m n R hoTarget
  have hoA : F.mapEdgeSet o ∈ A :=
    referenceOpen_mem_A hoSupport hyOutward.2 hyOutward.1
  let step : (cubicGraph d).Walk y (cubicStepFrom y (a.1, true)) :=
    SimpleGraph.Walk.cons (cubicGraph_adj_stepFrom y (a.1, true)) SimpleGraph.Walk.nil
  let q : (cubicGraph d).Walk
      (cubicRegionBoundaryOutsideEndpoint R e) (cubicStepFrom y (a.1, true)) :=
    w.append step
  let qPhysical := q.map F.toHom
  have hqPhysicalAllowed : walkEdgeFinset qPhysical ⊆ A := by
    intro g hg
    rw [mem_walkEdgeFinset_iff, SimpleGraph.Walk.edges_map] at hg
    obtain ⟨fSym, hfq, hfg⟩ := List.mem_map.mp hg
    let f : CubicEdge d := ⟨fSym, q.edges_subset_edgeSet hfq⟩
    have hmap : F.mapEdgeSet f = g := by
      apply Subtype.ext
      exact hfg
    rw [← hmap]
    change fSym ∈ (w.append step).edges at hfq
    rw [SimpleGraph.Walk.edges_append] at hfq
    rcases List.mem_append.mp hfq with hfw | hfstep
    · have hfExterior : f ∈ cubicRegionExteriorEdgesWithinBox d R n :=
        hwExterior ((mem_walkEdgeFinset_iff w f).mpr hfw)
      have hfCleared := hwOpen f.1 hfw
      exact referenceOpen_mem_A
        (exterior_subset_restartEventSupport d a.1 m n R hfExterior)
        hfCleared.2 hfCleared.1
    · have hfo : f = o := by
        apply Subtype.ext
        simpa [step, o] using hfstep
      simpa [hfo] using hoA
  have heStart : F (cubicRegionBoundaryOutsideEndpoint R e) ∈
      (F.mapEdgeSet e : Sym2 (Cubic d)) := by
    change F (cubicRegionBoundaryOutsideEndpoint R e) ∈ Sym2.map F (e : Sym2 (Cubic d))
    apply Sym2.mem_map.mpr
    refine ⟨cubicRegionBoundaryOutsideEndpoint R e, ?_, rfl⟩
    rw [← cubicRegionBoundaryEndpoints_edge heBoundary]
    simp
  have hqClosure : walkEdgeFinset qPhysical ⊆ C :=
    walkEdgeFinset_subset_finiteEdgeReachableClosure_of_incident
      qPhysical heC heStart hqPhysicalAllowed
  have hoPhysicalWalk : F.mapEdgeSet o ∈ walkEdgeFinset qPhysical := by
    rw [mem_walkEdgeFinset_iff, SimpleGraph.Walk.edges_map]
    apply List.mem_map.mpr
    refine ⟨(o : Sym2 (Cubic d)), ?_, rfl⟩
    change (o : Sym2 (Cubic d)) ∈ (w.append step).edges
    rw [SimpleGraph.Walk.edges_append]
    apply List.mem_append_right
    simp only [step, SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil,
      List.mem_singleton]
    rfl
  have hoC : F.mapEdgeSet o ∈ C := hqClosure hoPhysicalWalk
  have hoNext : F.mapEdgeSet o ∈ S.nextExplored stageRegion p incremented X := by
    change F.mapEdgeSet o ∈ S.explored ∪ C
    exact Finset.mem_union_right _ hoC
  have hseedAllowed : (cubicBoxEdges d c m).image F.mapEdgeSet ⊆ A := by
    intro g hg
    obtain ⟨f, hfSeed, rfl⟩ := Finset.mem_image.mp hg
    have hfTarget := seedEdge_mem_seededBoundaryTargetSupport
      hyQuadrant hyc hcLayer hfSeed
    have hfCleared := hcSeed hfSeed
    exact referenceOpen_mem_A
      (target_subset_restartEventSupport d a.1 m n R hfTarget)
      hfCleared.2 hfCleared.1
  have hentry : F (cubicStepFrom y (a.1, true)) ∈
      (F.mapEdgeSet o : Sym2 (Cubic d)) := by
    change F (cubicStepFrom y (a.1, true)) ∈ Sym2.map F (o : Sym2 (Cubic d))
    apply Sym2.mem_map.mpr
    exact ⟨cubicStepFrom y (a.1, true), by simp [o, cubicStepEdge], rfl⟩
  have hentryBox : F (cubicStepFrom y (a.1, true)) ∈ cubicMetricBox d (F c) m :=
    (cubicRestartFrameIso_mem_cubicMetricBox_iff
      center a transverseFlip c (cubicStepFrom y (a.1, true))).2 hyc
  have hseedClosure : cubicBoxEdges d (F c) m ⊆ C := by
    apply cubicBoxEdges_subset_finiteEdgeReachableClosure_of_incident
      hoC hentry hentryBox
    intro g hg
    obtain ⟨f, rfl⟩ := F.mapEdgeSet.surjective g
    apply hseedAllowed
    apply Finset.mem_image.mpr
    refine ⟨f, ?_, rfl⟩
    apply mem_cubicBoxEdges_of_endpoints
    intro z hz
    apply (cubicRestartFrameIso_mem_cubicMetricBox_iff
      center a transverseFlip c z).1
    apply endpoint_mem_cubicMetricBox_of_edge_mem_cubicBoxEdges hg
    change F z ∈ Sym2.map F (f : Sym2 (Cubic d))
    exact Sym2.mem_map.mpr ⟨z, hz, rfl⟩
  change Yref ∈ sprinkledRestartEvent d a.1 m n R p Q.beta delta
  refine ⟨e, ?_, ?_⟩
  · change e ∈ seededRegionAvailableExitEdges d a.1 m n R
      (clearedThreshold E p Yref)
    rw [seededRegionAvailableExitEdges, mem_regionAvailableExitEdges_iff]
    refine ⟨heBoundary, y, ?_, w, ?_, hwExterior⟩
    · rw [mem_seededBoundaryPointFinset_iff]
      refine ⟨hyQuadrant, ?_, c, hyc, hcLayer, ?_⟩
      · change Yref o < (p : ℝ) ∧ o ∉ E
        refine ⟨?_, hyOutward.2⟩
        change Y (F.mapEdgeSet o) < (p : ℝ)
        have hoExterior := S.mapEdgeSet_mem_sourceStageExterior_of_restartSupport
          center a transverseFlip hTargetFresh hoSupport hyOutward.2
        exact S.label_lt_density_of_mem_nextHistoryProfile stageRegion p incremented X Y
          (fun hOld ↦ (Finset.mem_sdiff.mp hoExterior).2
            (Finset.mem_union_left _ hOld))
          (fun hBoundary ↦ (Finset.mem_sdiff.mp hoExterior).2
            (Finset.mem_union_right _ hBoundary)) hoNext hY
      · intro f hfSeed
        have hfTarget := seedEdge_mem_seededBoundaryTargetSupport
          hyQuadrant hyc hcLayer hfSeed
        have hfSupport := target_subset_restartEventSupport d a.1 m n R hfTarget
        have hfCleared := hcSeed hfSeed
        have hfExterior := S.mapEdgeSet_mem_sourceStageExterior_of_restartSupport
          center a transverseFlip hTargetFresh hfSupport hfCleared.2
        have hfClosure : F.mapEdgeSet f ∈ C := by
          apply hseedClosure
          apply mem_cubicBoxEdges_of_endpoints
          intro z hz
          change z ∈ Sym2.map F (f : Sym2 (Cubic d)) at hz
          obtain ⟨t, htf, rfl⟩ := Sym2.mem_map.mp hz
          exact (cubicRestartFrameIso_mem_cubicMetricBox_iff
            center a transverseFlip c t).2
              (endpoint_mem_cubicMetricBox_of_edge_mem_cubicBoxEdges hfSeed htf)
        have hfNext : F.mapEdgeSet f ∈ S.nextExplored stageRegion p incremented X := by
          change F.mapEdgeSet f ∈ S.explored ∪ C
          exact Finset.mem_union_right _ hfClosure
        change Yref f < (p : ℝ) ∧ f ∉ E
        refine ⟨?_, hfCleared.2⟩
        change Y (F.mapEdgeSet f) < (p : ℝ)
        exact S.label_lt_density_of_mem_nextHistoryProfile stageRegion p incremented X Y
          (fun hOld ↦ (Finset.mem_sdiff.mp hfExterior).2
            (Finset.mem_union_left _ hOld))
          (fun hBoundary ↦ (Finset.mem_sdiff.mp hfExterior).2
            (Finset.mem_union_right _ hBoundary)) hfNext hY
    · intro fSym hfWalk
      let f : CubicEdge d := ⟨fSym, w.edges_subset_edgeSet hfWalk⟩
      have hfFinset : f ∈ walkEdgeFinset w :=
        (mem_walkEdgeFinset_iff w f).mpr hfWalk
      have hfPhysicalWalk : F.mapEdgeSet f ∈ walkEdgeFinset qPhysical := by
        rw [mem_walkEdgeFinset_iff, SimpleGraph.Walk.edges_map]
        apply List.mem_map.mpr
        refine ⟨(f : Sym2 (Cubic d)), ?_, rfl⟩
        change (f : Sym2 (Cubic d)) ∈ (w.append step).edges
        rw [SimpleGraph.Walk.edges_append]
        exact List.mem_append_left _ hfWalk
      have hfNext : F.mapEdgeSet f ∈ S.nextExplored stageRegion p incremented X := by
        change F.mapEdgeSet f ∈ S.explored ∪ C
        exact Finset.mem_union_right _ (hqClosure hfPhysicalWalk)
      have hfExteriorRef := hwExterior hfFinset
      have hfCleared := hwOpen f.1 hfWalk
      have hfSupport := exterior_subset_restartEventSupport d a.1 m n R hfExteriorRef
      have hfExterior := S.mapEdgeSet_mem_sourceStageExterior_of_restartSupport
        center a transverseFlip hTargetFresh hfSupport hfCleared.2
      change Yref f < (p : ℝ) ∧ f ∉ E
      refine ⟨?_, hfCleared.2⟩
      change Y (F.mapEdgeSet f) < (p : ℝ)
      exact S.label_lt_density_of_mem_nextHistoryProfile stageRegion p incremented X Y
        (fun hOld ↦ (Finset.mem_sdiff.mp hfExterior).2
          (Finset.mem_union_left _ hOld))
        (fun hBoundary ↦ (Finset.mem_sdiff.mp hfExterior).2
          (Finset.mem_union_right _ hBoundary)) hfNext hY
  · change Yref e < (Q.beta e : ℝ) + delta
    have heOldBoundary : F.mapEdgeSet e ∈ S.boundary :=
      (Finset.mem_inter.mp (hboundary ▸ hePhysicalSupport)).1
    have heOpen := S.label_lt_incremented_of_mem_nextHistoryProfile
      stageRegion p incremented X Y heOldBoundary heNext hY
    change Y (F.mapEdgeSet e) < (S.lower (F.mapEdgeSet e) : ℝ) + delta
    have hinc := hincremented (F.mapEdgeSet e) (by simpa [Q] using hePhysicalSupport)
    rw [S.framedQuery_physicalBoundaryThreshold] at hinc
    rw [← hinc]
    exact heOpen

end Percolation
