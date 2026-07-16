import Percolation.Critical.DynamicFramedSuccessStability
import Percolation.Critical.DynamicSeedWitness

/-!
# Mixed restart witnesses in the recursive source state

The source recursion must continue from a seed reached by the literal heterogeneous restart,
not from a seed selected only after all edges are raised to a later uniform density.  This file
extracts the seed-containment fact implicit in the framed-success stability proof: every edge
of a named mixed witness's physical seed box belongs to the successor explored set.
-/

namespace Percolation

open scoped unitInterval

/-- A named mixed-threshold witness carries its entire physical target seed into the literal
successor explored state.  The increment comparison is needed only on the actual transported
boundary support. -/
theorem SourceFiniteEdgeRevealState.mixedWitness_exploredCertificate
    {d m n : ℕ} (S : SourceFiniteEdgeRevealState d)
    (center : Cubic d) (a : CubicDirection d) (transverseFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (incremented : CubicEdge d → I)
    (X : CubicEdge d → ℝ) (W : RestartSeedWitnessIndex d a.1 m n)
    (hTargetFresh :
      let F := cubicRestartFrameIso center a transverseFlip
      Disjoint (cubicEdgeEndpointVertices (S.referenceExploredEdges F))
        (cubicEdgeEndpointVertices (seededBoundaryTargetSupport d a.1 m n)))
    (hincremented : ∀ e ∈ (S.framedQuery center a transverseFlip).boundarySupport n,
      ((S.framedQuery center a transverseFlip).physicalBoundaryThreshold e : ℝ) + delta ≤
        (incremented e : ℝ))
    (hW : W.IsMixedRestartWitness
      (S.framedQuery center a transverseFlip).region p
      (S.framedQuery center a transverseFlip).beta delta
      (cubicGraphIsoCouplingReindex
        (cubicRestartFrameIso center a transverseFlip) X)) :
    ∃ (e : CubicEdge d)
        (w : (cubicGraph d).Walk
          (cubicRegionBoundaryOutsideEndpoint
            (S.framedQuery center a transverseFlip).region e) W.boundaryPoint.1),
      e ∈ cubicRegionBoundaryEdgesWithinBox d
          (S.framedQuery center a transverseFlip).region n ∧
      walkEdgeFinset w ⊆ cubicRegionExteriorEdgesWithinBox d
        (S.framedQuery center a transverseFlip).region n ∧
      (cubicRestartFrameIso center a transverseFlip).mapEdgeSet e ∈
        S.nextExplored
          ((S.framedQuery center a transverseFlip).restartSupport m n)
          p incremented X ∧
      (∀ f ∈ walkEdgeFinset w,
        (cubicRestartFrameIso center a transverseFlip).mapEdgeSet f ∈
          S.nextExplored
            ((S.framedQuery center a transverseFlip).restartSupport m n)
            p incremented X ∧
        (cubicRestartFrameIso center a transverseFlip).mapEdgeSet f ∈
          sourceStageExterior S.explored
            ((S.framedQuery center a transverseFlip).restartSupport m n)) ∧
      (cubicRestartFrameIso center a transverseFlip).mapEdgeSet
          (cubicStepEdge W.boundaryPoint.1 (a.1, true)) ∈
        S.nextExplored
          ((S.framedQuery center a transverseFlip).restartSupport m n)
          p incremented X ∧
      (cubicRestartFrameIso center a transverseFlip).mapEdgeSet
          (cubicStepEdge W.boundaryPoint.1 (a.1, true)) ∈
        sourceStageExterior S.explored
          ((S.framedQuery center a transverseFlip).restartSupport m n) ∧
      ∀ f ∈ cubicBoxEdges d W.seedCenter.1 m,
        (cubicRestartFrameIso center a transverseFlip).mapEdgeSet f ∈
          S.nextExplored
            ((S.framedQuery center a transverseFlip).restartSupport m n)
            p incremented X ∧
        (cubicRestartFrameIso center a transverseFlip).mapEdgeSet f ∈
          sourceStageExterior S.explored
            ((S.framedQuery center a transverseFlip).restartSupport m n) := by
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
    have hle := hincremented (F.mapEdgeSet e) (by simpa [Q] using hePhysicalSupport)
    rw [S.framedQuery_physicalBoundaryThreshold] at hle
    change Xref e < (S.lower (F.mapEdgeSet e) : ℝ) + delta at heIncrement
    exact heIncrement.trans_le hle
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
  have hentryPhysicalBox : F (cubicStepFrom y (a.1, true)) ∈
      cubicMetricBox d (F W.seedCenter.1) m :=
    (cubicRestartFrameIso_mem_cubicMetricBox_iff
      center a transverseFlip W.seedCenter.1 (cubicStepFrom y (a.1, true))).2 hentryBox
  have hseedClosure : cubicBoxEdges d (F W.seedCenter.1) m ⊆ C := by
    apply cubicBoxEdges_subset_finiteEdgeReachableClosure_of_incident
      hoC hentry hentryPhysicalBox
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
  have heNext : F.mapEdgeSet e ∈ S.nextExplored stageRegion p incremented X := by
    change F.mapEdgeSet e ∈ S.explored ∪ C
    exact Finset.mem_union_right _ heC
  have hoNext : F.mapEdgeSet o ∈ S.nextExplored stageRegion p incremented X := by
    change F.mapEdgeSet o ∈ S.explored ∪ C
    exact Finset.mem_union_right _ hoC
  have hoExterior : F.mapEdgeSet o ∈ sourceStageExterior S.explored stageRegion :=
    S.mapEdgeSet_mem_sourceStageExterior_of_restartSupport
      center a transverseFlip hTargetFresh hoSupport hoCleared.2
  refine ⟨e, w, heBoundary, hwExterior, heNext, ?_, hoNext, hoExterior, ?_⟩
  · intro f hfWalk
    have hfPhysicalWalk : F.mapEdgeSet f ∈ walkEdgeFinset qPhysical := by
      rw [mem_walkEdgeFinset_iff, SimpleGraph.Walk.edges_map]
      apply List.mem_map.mpr
      refine ⟨(f : Sym2 (Cubic d)), ?_, rfl⟩
      change (f : Sym2 (Cubic d)) ∈ (w.append step).edges
      rw [SimpleGraph.Walk.edges_append]
      exact List.mem_append_left _ ((mem_walkEdgeFinset_iff w f).mp hfWalk)
    have hfNext : F.mapEdgeSet f ∈ S.nextExplored stageRegion p incremented X := by
      change F.mapEdgeSet f ∈ S.explored ∪ C
      exact Finset.mem_union_right _ (hqClosure hfPhysicalWalk)
    have hfExteriorRef := hwExterior hfWalk
    have hfCleared := hwOpen f.1 ((mem_walkEdgeFinset_iff w f).mp hfWalk)
    have hfExterior := S.mapEdgeSet_mem_sourceStageExterior_of_restartSupport
      center a transverseFlip hTargetFresh
        (exterior_subset_restartEventSupport d a.1 m n R hfExteriorRef)
        hfCleared.2
    exact ⟨hfNext, hfExterior⟩
  · intro f hfSeed
    have hfPhysicalBox : F.mapEdgeSet f ∈ cubicBoxEdges d (F W.seedCenter.1) m := by
      apply mem_cubicBoxEdges_of_endpoints
      intro z hz
      change z ∈ Sym2.map F (f : Sym2 (Cubic d)) at hz
      obtain ⟨u, huf, rfl⟩ := Sym2.mem_map.mp hz
      exact (cubicRestartFrameIso_mem_cubicMetricBox_iff
        center a transverseFlip W.seedCenter.1 u).2
          (endpoint_mem_cubicMetricBox_of_edge_mem_cubicBoxEdges hfSeed huf)
    have hfNext : F.mapEdgeSet f ∈ S.nextExplored stageRegion p incremented X := by
      change F.mapEdgeSet f ∈ S.explored ∪ C
      exact Finset.mem_union_right _ (hseedClosure hfPhysicalBox)
    have hfTarget := seedEdge_mem_seededBoundaryTargetSupport
      W.boundaryPoint.2 hentryBox hcLayer hfSeed
    have hfCleared := hcSeed hfSeed
    have hfExterior := S.mapEdgeSet_mem_sourceStageExterior_of_restartSupport
      center a transverseFlip hTargetFresh
        (target_subset_restartEventSupport d a.1 m n R hfTarget)
        hfCleared.2
    exact ⟨hfNext, hfExterior⟩

/-- In particular, a named mixed witness's physical seed box is present in the successor
explored set. -/
theorem SourceFiniteEdgeRevealState.mixedWitness_seedBox_subset_nextExplored
    {d m n : ℕ} (S : SourceFiniteEdgeRevealState d)
    (center : Cubic d) (a : CubicDirection d) (transverseFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (incremented : CubicEdge d → I)
    (X : CubicEdge d → ℝ) (W : RestartSeedWitnessIndex d a.1 m n)
    (hTargetFresh :
      let F := cubicRestartFrameIso center a transverseFlip
      Disjoint (cubicEdgeEndpointVertices (S.referenceExploredEdges F))
        (cubicEdgeEndpointVertices (seededBoundaryTargetSupport d a.1 m n)))
    (hincremented : ∀ e ∈ (S.framedQuery center a transverseFlip).boundarySupport n,
      ((S.framedQuery center a transverseFlip).physicalBoundaryThreshold e : ℝ) + delta ≤
        (incremented e : ℝ))
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
  obtain ⟨_e, _w, _he, _hw, _heNext, _hwNext, _hoNext, _hoExterior, hseed⟩ :=
    S.mixedWitness_exploredCertificate center a transverseFlip p delta incremented X W
      hTargetFresh hincremented hW
  intro g hg
  let F := cubicRestartFrameIso center a transverseFlip
  obtain ⟨f, rfl⟩ := F.mapEdgeSet.surjective g
  apply (hseed f ?_).1
  apply mem_cubicBoxEdges_of_endpoints
  intro z hz
  apply (cubicRestartFrameIso_mem_cubicMetricBox_iff
    center a transverseFlip W.seedCenter.1 z).1
  apply endpoint_mem_cubicMetricBox_of_edge_mem_cubicBoxEdges hg
  change F z ∈ Sym2.map F (f : Sym2 (Cubic d))
  exact Sym2.mem_map.mpr ⟨z, hz, rfl⟩

/-- The same named mixed witness remains valid throughout the literal successor accumulated-
history cell.  Thus a finite history cell may carry a deterministic next seed without making
an additional, potentially overlapping reveal. -/
theorem SourceFiniteEdgeRevealState.mixedWitness_of_mem_nextHistoryProfile
    {d m n : ℕ} (S : SourceFiniteEdgeRevealState d)
    (center : Cubic d) (a : CubicDirection d) (transverseFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (incremented : CubicEdge d → I)
    (X Y : CubicEdge d → ℝ) (W : RestartSeedWitnessIndex d a.1 m n)
    (hTargetFresh :
      let F := cubicRestartFrameIso center a transverseFlip
      Disjoint (cubicEdgeEndpointVertices (S.referenceExploredEdges F))
        (cubicEdgeEndpointVertices (seededBoundaryTargetSupport d a.1 m n)))
    (hincremented : ∀ e ∈ (S.framedQuery center a transverseFlip).boundarySupport n,
      (incremented e : ℝ) =
        ((S.framedQuery center a transverseFlip).physicalBoundaryThreshold e : ℝ) + delta)
    (hW : W.IsMixedRestartWitness
      (S.framedQuery center a transverseFlip).region p
      (S.framedQuery center a transverseFlip).beta delta
      (cubicGraphIsoCouplingReindex
        (cubicRestartFrameIso center a transverseFlip) X))
    (hY : Y ∈ (S.next
      ((S.framedQuery center a transverseFlip).restartSupport m n)
      p incremented X).historyProfile.event) :
    W.IsMixedRestartWitness
      (S.framedQuery center a transverseFlip).region p
      (S.framedQuery center a transverseFlip).beta delta
      (cubicGraphIsoCouplingReindex
        (cubicRestartFrameIso center a transverseFlip) Y) := by
  classical
  let F := cubicRestartFrameIso center a transverseFlip
  let R := cubicEdgeEndpointVertices (S.referenceExploredEdges F)
  let Q := S.framedQuery center a transverseFlip
  let E := cubicRegionBoundaryEdgesWithinBox d R n
  let stageRegion := Q.restartSupport m n
  let Xref := cubicGraphIsoCouplingReindex F X
  let Yref := cubicGraphIsoCouplingReindex F Y
  obtain ⟨e, w, heBoundary, hwExterior, heNext, hwCertificate,
      hoNext, hoExterior, hseedCertificate⟩ :=
    S.mixedWitness_exploredCertificate center a transverseFlip p delta incremented X W
      hTargetFresh (fun g hg ↦ (hincremented g hg).ge) hW
  have hrealizedX := hW.1
  rcases hrealizedX with ⟨hoCleared, hentryBox, hcLayer, hcSeed⟩
  have hboundary : Q.boundarySupport n = S.boundary ∩ stageRegion := by
    simpa [Q, stageRegion] using
      (S.framedQuery_boundarySupport_eq_boundary_inter_restartSupport_of_targetEndpointFresh
        center a transverseFlip hTargetFresh :
          Q.boundarySupport n = S.boundary ∩ Q.restartSupport m n)
  change W.IsMixedRestartWitness R p Q.beta delta Yref
  refine ⟨?_, e, heBoundary, ?_, ?_⟩
  · refine ⟨?_, hentryBox, hcLayer, ?_⟩
    · change Yref (cubicStepEdge W.boundaryPoint.1 (a.1, true)) < (p : ℝ) ∧
        cubicStepEdge W.boundaryPoint.1 (a.1, true) ∉ E
      constructor
      · change Y (F.mapEdgeSet
          (cubicStepEdge W.boundaryPoint.1 (a.1, true))) < (p : ℝ)
        exact S.label_lt_density_of_mem_nextHistoryProfile
          stageRegion p incremented X Y
          (fun hOld ↦ (Finset.mem_sdiff.mp hoExterior).2
            (Finset.mem_union_left _ hOld))
          (fun hBoundary ↦ (Finset.mem_sdiff.mp hoExterior).2
            (Finset.mem_union_right _ hBoundary)) hoNext hY
      · exact hoCleared.2
    · intro f hfSeed
      change Yref f < (p : ℝ) ∧ f ∉ E
      have hfCertificate := hseedCertificate f hfSeed
      constructor
      · change Y (F.mapEdgeSet f) < (p : ℝ)
        exact S.label_lt_density_of_mem_nextHistoryProfile
          stageRegion p incremented X Y
          (fun hOld ↦ (Finset.mem_sdiff.mp hfCertificate.2).2
            (Finset.mem_union_left _ hOld))
          (fun hBoundary ↦ (Finset.mem_sdiff.mp hfCertificate.2).2
            (Finset.mem_union_right _ hBoundary)) hfCertificate.1 hY
      · exact (hcSeed hfSeed).2
  · refine ⟨w, ?_, hwExterior⟩
    intro fSym hfWalk
    let f : CubicEdge d := ⟨fSym, w.edges_subset_edgeSet hfWalk⟩
    have hfFinset : f ∈ walkEdgeFinset w :=
      (mem_walkEdgeFinset_iff w f).mpr hfWalk
    have hfCertificate := hwCertificate f hfFinset
    change Yref f < (p : ℝ) ∧ f ∉ E
    constructor
    · change Y (F.mapEdgeSet f) < (p : ℝ)
      exact S.label_lt_density_of_mem_nextHistoryProfile
        stageRegion p incremented X Y
        (fun hOld ↦ (Finset.mem_sdiff.mp hfCertificate.2).2
          (Finset.mem_union_left _ hOld))
        (fun hBoundary ↦ (Finset.mem_sdiff.mp hfCertificate.2).2
          (Finset.mem_union_right _ hBoundary)) hfCertificate.1 hY
    · intro hfBoundary
      exact Set.disjoint_left.mp
        (disjoint_cubicRegionExteriorEdgesWithinBox_boundary d R n)
        (hwExterior hfFinset) hfBoundary
  · change Yref e < (Q.beta e : ℝ) + delta
    have hePhysicalSupport : F.mapEdgeSet e ∈ Q.boundarySupport n := by
      change F.mapEdgeSet e ∈ framedBoundaryHistorySupport center a transverseFlip R n
      exact Finset.mem_image.mpr ⟨e, heBoundary, rfl⟩
    have heOldBoundary : F.mapEdgeSet e ∈ S.boundary :=
      (Finset.mem_inter.mp (hboundary ▸ hePhysicalSupport)).1
    have heOpen := S.label_lt_incremented_of_mem_nextHistoryProfile
      stageRegion p incremented X Y heOldBoundary heNext hY
    change Y (F.mapEdgeSet e) < (S.lower (F.mapEdgeSet e) : ℝ) + delta
    have hinc := hincremented (F.mapEdgeSet e) (by simpa [Q] using hePhysicalSupport)
    rw [S.framedQuery_physicalBoundaryThreshold] at hinc
    rw [← hinc]
    exact heOpen

/-- On a realized successor history cell, the complete finite table of mixed witnesses is
constant. -/
theorem SourceFiniteEdgeRevealState.mixedRestartSeedWitnesses_eq_of_mem_nextHistoryProfile
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
    (hcurrent : X ∈ S.historyProfile.event)
    (hnonneg : X ∈ nonnegativeCouplingEvent)
    (hY : Y ∈ (S.next
      ((S.framedQuery center a transverseFlip).restartSupport m n)
      p incremented X).historyProfile.event) :
    mixedRestartSeedWitnesses d a.1 m n
        (S.framedQuery center a transverseFlip).region p
        (S.framedQuery center a transverseFlip).beta delta
        (cubicGraphIsoCouplingReindex
          (cubicRestartFrameIso center a transverseFlip) Y) =
      mixedRestartSeedWitnesses d a.1 m n
        (S.framedQuery center a transverseFlip).region p
        (S.framedQuery center a transverseFlip).beta delta
        (cubicGraphIsoCouplingReindex
          (cubicRestartFrameIso center a transverseFlip) X) := by
  classical
  let Q := S.framedQuery center a transverseFlip
  let stageRegion := Q.restartSupport m n
  have hstate : S.next stageRegion p incremented Y =
      S.next stageRegion p incremented X :=
    S.next_eq_of_mem_next_historyProfile stageRegion p incremented X Y hY
  have hXnext : X ∈ (S.next stageRegion p incremented X).historyProfile.event :=
    S.mem_next_historyProfile stageRegion p incremented X hcurrent hnonneg
  have hXnextY : X ∈ (S.next stageRegion p incremented Y).historyProfile.event := by
    rw [hstate]
    exact hXnext
  ext W
  rw [mem_mixedRestartSeedWitnesses_iff, mem_mixedRestartSeedWitnesses_iff]
  constructor
  · intro hW
    exact S.mixedWitness_of_mem_nextHistoryProfile
      center a transverseFlip p delta incremented Y X W hTargetFresh hincremented hW
        (by simpa [Q, stageRegion] using hXnextY)
  · intro hW
    exact S.mixedWitness_of_mem_nextHistoryProfile
      center a transverseFlip p delta incremented X Y W hTargetFresh hincremented hW hY

/-- Consequently, the deterministic selector of an actually reached mixed witness is also
constant on every realized successor history cell. -/
theorem SourceFiniteEdgeRevealState.selectedMixedRestartSeedWitness_eq_of_mem_nextHistoryProfile
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
    (hcurrent : X ∈ S.historyProfile.event)
    (hnonneg : X ∈ nonnegativeCouplingEvent)
    (hY : Y ∈ (S.next
      ((S.framedQuery center a transverseFlip).restartSupport m n)
      p incremented X).historyProfile.event) :
    selectedMixedRestartSeedWitness d a.1 m n
        (S.framedQuery center a transverseFlip).region p
        (S.framedQuery center a transverseFlip).beta delta
        (cubicGraphIsoCouplingReindex
          (cubicRestartFrameIso center a transverseFlip) Y) =
      selectedMixedRestartSeedWitness d a.1 m n
        (S.framedQuery center a transverseFlip).region p
        (S.framedQuery center a transverseFlip).beta delta
        (cubicGraphIsoCouplingReindex
          (cubicRestartFrameIso center a transverseFlip) X) := by
  unfold selectedMixedRestartSeedWitness
  rw [S.mixedRestartSeedWitnesses_eq_of_mem_nextHistoryProfile
    center a transverseFlip p delta incremented X Y hTargetFresh hincremented
      hcurrent hnonneg hY]

namespace SourceFiniteEdgeRevealState

/-- Deterministic target seed selected from the literal mixed restart of the canonical query. -/
noncomputable def selectedMixedWitness
    {d m n : ℕ} (S : SourceFiniteEdgeRevealState d)
    (center : Cubic d) (a : CubicDirection d) (transverseFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (X : CubicEdge d → ℝ) :
    Option (RestartSeedWitnessIndex d a.1 m n) :=
  selectedMixedRestartSeedWitness d a.1 m n
    (S.framedQuery center a transverseFlip).region p
    (S.framedQuery center a transverseFlip).beta delta
    (cubicGraphIsoCouplingReindex
      (cubicRestartFrameIso center a transverseFlip) X)

/-- Physical center of that selected seed. -/
noncomputable def selectedMixedPhysicalSeedCenter
    {d m n : ℕ} (S : SourceFiniteEdgeRevealState d)
    (center : Cubic d) (a : CubicDirection d) (transverseFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (X : CubicEdge d → ℝ) : Option (Cubic d) :=
  (S.selectedMixedWitness (m := m) (n := n) center a transverseFlip p delta X).map
    fun W ↦ cubicRestartFrameIso center a transverseFlip W.seedCenter.1

/-- Literal success supplies a selected mixed witness, not merely a final-density witness. -/
theorem exists_selectedMixedWitness_of_success
    {d m n : ℕ} (S : SourceFiniteEdgeRevealState d)
    (center : Cubic d) (a : CubicDirection d) (transverseFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (X : CubicEdge d → ℝ)
    (hsuccess : X ∈ (S.framedQuery center a transverseFlip).successEvent m n p delta) :
    ∃ W : RestartSeedWitnessIndex d a.1 m n,
      S.selectedMixedWitness (m := m) (n := n)
        center a transverseFlip p delta X = some W ∧
      W.IsMixedRestartWitness
        (S.framedQuery center a transverseFlip).region p
        (S.framedQuery center a transverseFlip).beta delta
        (cubicGraphIsoCouplingReindex
          (cubicRestartFrameIso center a transverseFlip) X) := by
  change cubicGraphIsoCouplingReindex
      (cubicRestartFrameIso center a transverseFlip) X ∈
    sprinkledRestartEvent d a.1 m n
      (S.framedQuery center a transverseFlip).region p
      (S.framedQuery center a transverseFlip).beta delta at hsuccess
  exact selectedMixedRestartSeedWitness_eq_some_of_success hsuccess

/-- The corresponding selected physical center is present whenever the canonical framed
restart succeeds. -/
theorem exists_selectedMixedPhysicalSeedCenter_of_success
    {d m n : ℕ} (S : SourceFiniteEdgeRevealState d)
    (center : Cubic d) (a : CubicDirection d) (transverseFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (X : CubicEdge d → ℝ)
    (hsuccess : X ∈ (S.framedQuery center a transverseFlip).successEvent m n p delta) :
    ∃ W : RestartSeedWitnessIndex d a.1 m n,
      S.selectedMixedPhysicalSeedCenter (m := m) (n := n)
        center a transverseFlip p delta X =
        some (cubicRestartFrameIso center a transverseFlip W.seedCenter.1) ∧
      W.IsMixedRestartWitness
        (S.framedQuery center a transverseFlip).region p
        (S.framedQuery center a transverseFlip).beta delta
        (cubicGraphIsoCouplingReindex
          (cubicRestartFrameIso center a transverseFlip) X) := by
  obtain ⟨W, hselected, hW⟩ :=
    S.exists_selectedMixedWitness_of_success center a transverseFlip p delta X hsuccess
  refine ⟨W, ?_, hW⟩
  simp [selectedMixedPhysicalSeedCenter, hselected]

/-- The selected physical seed center is constant on a realized successor history cell. -/
theorem selectedMixedPhysicalSeedCenter_eq_of_mem_nextHistoryProfile
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
    (hcurrent : X ∈ S.historyProfile.event)
    (hnonneg : X ∈ nonnegativeCouplingEvent)
    (hY : Y ∈ (S.next
      ((S.framedQuery center a transverseFlip).restartSupport m n)
      p incremented X).historyProfile.event) :
    S.selectedMixedPhysicalSeedCenter (m := m) (n := n)
        center a transverseFlip p delta Y =
      S.selectedMixedPhysicalSeedCenter (m := m) (n := n)
        center a transverseFlip p delta X := by
  unfold selectedMixedPhysicalSeedCenter selectedMixedWitness
  rw [S.selectedMixedRestartSeedWitness_eq_of_mem_nextHistoryProfile
    center a transverseFlip p delta incremented X Y hTargetFresh hincremented
      hcurrent hnonneg hY]

end SourceFiniteEdgeRevealState

end Percolation
