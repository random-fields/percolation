import Percolation.Critical.DynamicRootRecursiveState
import Percolation.Critical.DynamicSourceEdgeState

/-!
# Handoff from the special root phase to the global source recursion

The root radial search was first developed using a finite local boundary.  This file proves
that, on its concrete support, that local boundary is exactly the active part of Grimmett's
global `ΔE₁`.  It then initializes the source-faithful changing-region state and carries every
radial realization satisfying the explicit probability-one label bounds into that state.
-/

namespace Percolation

open scoped unitInterval

/-- Source state at (7.28)--(7.29), before the simultaneous radial update. -/
noncomputable def rootInitialSourceEdgeState (d m : ℕ) (p : I) :
    SourceFiniteEdgeRevealState d where
  explored := rootInitialExploredEdges d m
  lower := initialRevealLower
  upper := initialRevealUpper (rootInitialExploredEdges d m) p
  lower_eq_zero_off := by
    intro e _he _hb
    rfl

/-- On the radial finite region, the active global boundary is the exact boundary used by the
six (or `2d`) simultaneous root branches. -/
theorem activeCubicEdgeBoundary_rootInitial_eq
    {d m n : ℕ} [NeZero d] (hm : 1 ≤ m) (hmn : m + 1 ≤ n) :
    activeCubicEdgeBoundary (rootInitialExploredEdges d m)
        (rootRadialEdgeSupport d m n) =
      rootInitialBoundaryEdges d m n := by
  rw [activeCubicEdgeBoundary, Finset.inter_comm,
    ← cubicEdgeBoundaryWithin_eq_inter]
  exact rootEdgeLineBoundary_eq_rootInitialBoundaryEdges hm hmn

/-- The exterior part of the radial finite region is unchanged by replacing the local
boundary with the literal global boundary. -/
theorem sourceStageExterior_rootInitial_eq
    {d m n : ℕ} [NeZero d] (hm : 1 ≤ m) (hmn : m + 1 ≤ n) :
    sourceStageExterior (rootInitialExploredEdges d m)
        (rootRadialEdgeSupport d m n) =
      rootRadialExteriorEdges d m n := by
  rw [sourceStageExterior_eq_sdiff_activeBoundary,
    activeCubicEdgeBoundary_rootInitial_eq hm hmn]
  rfl

/-- The source-global step computes exactly the already constructed radial edge set `E₂`. -/
theorem sourceExploredEdgeStep_rootInitial_eq
    {d m n : ℕ} [NeZero d] (hm : 1 ≤ m) (hmn : m + 1 ≤ n)
    (p incremented : I) (X : CubicEdge d → ℝ) :
    sourceExploredEdgeStep (rootInitialExploredEdges d m)
        (rootRadialEdgeSupport d m n) p (fun _ ↦ incremented) X =
      rootRadialExploredEdges d m n p incremented X := by
  rw [sourceExploredEdgeStep, activeCubicEdgeBoundary_rootInitial_eq hm hmn,
    sourceStageExterior_rootInitial_eq hm hmn]
  exact exploredEdgeStepFamily_const _ _ _ _ _ _

/-- Canonical source-faithful state immediately after the special radial phase. -/
noncomputable def rootPostRadialSourceEdgeState
    (d m n : ℕ) (p incremented : I) (X : CubicEdge d → ℝ) :
    SourceFiniteEdgeRevealState d :=
  (rootInitialSourceEdgeState d m p).next (rootRadialEdgeSupport d m n) p
    (fun _ ↦ incremented) X

/-- Immediately after the simultaneous radial phase, every lower threshold is bounded by the
larger of the background density and the radial increment. -/
theorem coe_rootPostRadialSourceEdgeState_lower_le_max
    {d m n : ℕ} (p incremented : I) (X : CubicEdge d → ℝ)
    (e : CubicEdge d) :
    ((rootPostRadialSourceEdgeState d m n p incremented X).lower e : ℝ) ≤
      max (p : ℝ) (incremented : ℝ) := by
  unfold rootPostRadialSourceEdgeState
  apply (rootInitialSourceEdgeState d m p).coe_next_lower_le_of_le
  · intro f
    change (0 : ℝ) ≤ max (p : ℝ) (incremented : ℝ)
    exact le_max_of_le_left (p.2.1)
  · intro f
    exact le_max_right _ _
  · exact le_max_left _ _

theorem rootPostRadialSourceEdgeState_explored
    {d m n : ℕ} [NeZero d] (hm : 1 ≤ m) (hmn : m + 1 ≤ n)
    (p incremented : I) (X : CubicEdge d → ℝ) :
    (rootPostRadialSourceEdgeState d m n p incremented X).explored =
      rootRadialExploredEdges d m n p incremented X := by
  exact sourceExploredEdgeStep_rootInitial_eq hm hmn p incremented X

/-- The central seed plus the explicit probability-one boundary cylinder is exactly enough to
initialize the global source interval profile. -/
theorem rootInitialSourceEdgeState_mem_profile
    {d m : ℕ} (p : I) (X : CubicEdge d → ℝ)
    (hseed : X ∈ rootSeedLabelEvent d m p)
    (hnonneg : X ∈ SourceFiniteEdgeRevealState.nonnegativeBoundaryEvent
      (cubicEdgeBoundary (rootInitialExploredEdges d m))) :
    X ∈ (rootInitialSourceEdgeState d m p).profile.event := by
  constructor
  · exact hnonneg
  · intro e he
    change e ∈ rootInitialExploredEdges d m at he
    have heOpen := hseed he
    change X e < (initialRevealUpper (rootInitialExploredEdges d m) p e : ℝ)
    simpa [initialRevealUpper, he] using heOpen

/-- On the common-uniform support, the central seed initializes the exact accumulated-history
profile, including lower endpoint zero on the already open seed edges. -/
theorem rootInitialSourceEdgeState_mem_historyProfile
    {d m : ℕ} (p : I) (X : CubicEdge d → ℝ)
    (hseed : X ∈ rootSeedLabelEvent d m p)
    (hnonneg : X ∈ SourceFiniteEdgeRevealState.nonnegativeCouplingEvent) :
    X ∈ (rootInitialSourceEdgeState d m p).historyProfile.event := by
  constructor
  · intro e _he
    change (0 : ℝ) ≤ X e
    exact SourceFiniteEdgeRevealState.mem_nonnegativeCouplingEvent_iff.mp hnonneg e
  · intro e he
    change e ∈ rootInitialExploredEdges d m at he
    have heOpen := hseed he
    change X e < (initialRevealUpper (rootInitialExploredEdges d m) p e : ℝ)
    simpa [initialRevealUpper, he] using heOpen

/-- Source-faithful post-radial handoff.  The explicit nonnegativity premises make the
set-level statement true on the ambient real-valued label space; they are automatic on the
probability-one support where every coupling label lies in `[0,1]`. -/
theorem rootRadialEvent_mem_postRadialSourceProfile
    {d m n : ℕ} [NeZero d]
    (p incremented : I) (delta : ℝ) (X : CubicEdge d → ℝ)
    (hradial : X ∈ rootRadialEvent d m n p delta)
    (hinitial : X ∈ SourceFiniteEdgeRevealState.nonnegativeBoundaryEvent
      (cubicEdgeBoundary (rootInitialExploredEdges d m)))
    (hnext : X ∈ SourceFiniteEdgeRevealState.nonnegativeBoundaryEvent
      (cubicEdgeBoundary
        ((rootInitialSourceEdgeState d m p).nextExplored
          (rootRadialEdgeSupport d m n) p (fun _ ↦ incremented) X))) :
    X ∈ (rootPostRadialSourceEdgeState d m n p incremented X).profile.event := by
  apply (rootInitialSourceEdgeState d m p).mem_next_profile_of_mem_nonnegativeBoundaryEvent
  · exact rootInitialSourceEdgeState_mem_profile p X hradial.1 hinitial
  · exact hnext

/-- Exact accumulated-history handoff after the simultaneous radial phase. -/
theorem rootRadialEvent_mem_postRadialSourceHistoryProfile
    {d m n : ℕ} [NeZero d]
    (p incremented : I) (delta : ℝ) (X : CubicEdge d → ℝ)
    (hradial : X ∈ rootRadialEvent d m n p delta)
    (hnonneg : X ∈ SourceFiniteEdgeRevealState.nonnegativeCouplingEvent) :
    X ∈ (rootPostRadialSourceEdgeState d m n p incremented X).historyProfile.event := by
  apply (rootInitialSourceEdgeState d m p).mem_next_historyProfile
    (rootRadialEdgeSupport d m n) p (fun _ ↦ incremented) X
  · exact rootInitialSourceEdgeState_mem_historyProfile p X hradial.1 hnonneg
  · exact hnonneg

/-- Every realization in a post-radial accumulated-history cell retains the original central
seed.  This is the first semantic-stability component needed to show that radial success is
constant on canonical exploration-state cells; importantly, it follows from the unchanged
state interval itself and adds no threshold-pattern constraints. -/
theorem rootSeedLabelEvent_of_mem_rootPostRadialSourceHistoryProfile
    {d m n : ℕ} (p incremented : I) (X Y : CubicEdge d → ℝ)
    (hY : Y ∈
      (rootPostRadialSourceEdgeState d m n p incremented X).historyProfile.event) :
    Y ∈ rootSeedLabelEvent d m p := by
  intro e heSeed
  have heOld : e ∈ (rootInitialSourceEdgeState d m p).explored := heSeed
  have heNext : e ∈
      (rootPostRadialSourceEdgeState d m n p incremented X).explored := by
    exact (rootInitialSourceEdgeState d m p).explored_subset_nextExplored
      (rootRadialEdgeSupport d m n) p (fun _ ↦ incremented) X heOld
  have hOpen := hY.2 e heNext
  change Y e <
    (((rootInitialSourceEdgeState d m p).updateData
      (rootRadialEdgeSupport d m n) p (fun _ ↦ incremented) X).updatedUpper e : I) at hOpen
  rw [RevealThresholdUpdateData.updatedUpper_eq_old_of_mem_oldExplored _ heOld] at hOpen
  change Y e < ((rootInitialSourceEdgeState d m p).upper e : ℝ) at hOpen
  change Y e < ((if e ∈ cubicBoxEdges d cubicOrigin m then p else 1 : I) : ℝ) at hOpen
  have heSeedFinset : e ∈ cubicBoxEdges d cubicOrigin m := heSeed
  rw [if_pos heSeedFinset] at hOpen
  change Y e < (p : ℝ)
  exact hOpen

/-- An absorbed physical last-exit edge remains open at the radial increment throughout its
unchanged post-radial accumulated-history cell. -/
theorem label_lt_incremented_of_mem_rootPostRadialSourceHistoryProfile
    {d m n : ℕ} [NeZero d] (hm : 1 ≤ m) (hmn : m + 1 ≤ n)
    (p incremented : I) (X Y : CubicEdge d → ℝ) {e : CubicEdge d}
    (heBoundary : e ∈ rootInitialBoundaryEdges d m n)
    (heExplored : e ∈ rootRadialExploredEdges d m n p incremented X)
    (hY : Y ∈
      (rootPostRadialSourceEdgeState d m n p incremented X).historyProfile.event) :
    Y e < (incremented : ℝ) := by
  have heNotOld : e ∉ (rootInitialSourceEdgeState d m p).explored := by
    exact fun heOld ↦ Finset.disjoint_left.mp
      (disjoint_rootInitialBoundaryEdges_rootInitialExploredEdges d m n)
      heBoundary heOld
  have heOldBoundary : e ∈ (rootInitialSourceEdgeState d m p).boundary := by
    have heWithin := rootInitialBoundaryEdges_subset_rootEdgeLineBoundary hm heBoundary
    obtain ⟨_heAmbient, heNot, f, hf, hfe⟩ :=
      mem_cubicEdgeBoundaryWithin_iff.mp heWithin
    exact mem_cubicEdgeBoundary_iff.mpr ⟨heNot, f, hf, hfe⟩
  have heNext : e ∈
      (rootPostRadialSourceEdgeState d m n p incremented X).explored := by
    rw [rootPostRadialSourceEdgeState_explored hm hmn]
    exact heExplored
  have hOpen := hY.2 e heNext
  change Y e <
    (((rootInitialSourceEdgeState d m p).updateData
      (rootRadialEdgeSupport d m n) p (fun _ ↦ incremented) X).updatedUpper e : I) at hOpen
  rw [RevealThresholdUpdateData.updatedUpper_eq_incremented_of_mem_absorbedBoundary
    _ heNotOld heOldBoundary heNext] at hOpen
  exact hOpen

/-- Every explored radial-exterior coordinate remains `p`-open throughout the unchanged
post-radial accumulated-history cell. -/
theorem label_lt_density_of_mem_rootPostRadialSourceHistoryProfile
    {d m n : ℕ} [NeZero d] (hm : 1 ≤ m) (hmn : m + 1 ≤ n)
    (p incremented : I) (X Y : CubicEdge d → ℝ) {e : CubicEdge d}
    (heExterior : e ∈ rootRadialExteriorEdges d m n)
    (heExplored : e ∈ rootRadialExploredEdges d m n p incremented X)
    (hY : Y ∈
      (rootPostRadialSourceEdgeState d m n p incremented X).historyProfile.event) :
    Y e < (p : ℝ) := by
  have heSupport : e ∈ rootRadialEdgeSupport d m n :=
    (Finset.mem_sdiff.mp heExterior).1
  have heNot : e ∉ rootInitialExploredEdges d m ∪ rootInitialBoundaryEdges d m n :=
    (Finset.mem_sdiff.mp heExterior).2
  have heNotOld : e ∉ (rootInitialSourceEdgeState d m p).explored :=
    fun heOld ↦ heNot (Finset.mem_union_left _ heOld)
  have heNotOldBoundary : e ∉ (rootInitialSourceEdgeState d m p).boundary := by
    intro heBoundary
    have heActive : e ∈ activeCubicEdgeBoundary
        (rootInitialExploredEdges d m) (rootRadialEdgeSupport d m n) :=
      Finset.mem_inter.mpr ⟨heBoundary, heSupport⟩
    rw [activeCubicEdgeBoundary_rootInitial_eq hm hmn] at heActive
    exact heNot (Finset.mem_union_right _ heActive)
  have heNext : e ∈
      (rootPostRadialSourceEdgeState d m n p incremented X).explored := by
    rw [rootPostRadialSourceEdgeState_explored hm hmn]
    exact heExplored
  have hOpen := hY.2 e heNext
  change Y e <
    (((rootInitialSourceEdgeState d m p).updateData
      (rootRadialEdgeSupport d m n) p (fun _ ↦ incremented) X).updatedUpper e : I) at hOpen
  rw [RevealThresholdUpdateData.updatedUpper_eq_density_of_mem_newInterior
    _ heNotOld heNotOldBoundary heNext] at hOpen
  exact hOpen

/-- A successful framed radial branch leaves a complete source-faithful certificate in the
simultaneous explored edge set: its last exit, exterior connection, outward target edge, and
every edge of one target seed are all explored, with all non-exit edges classified as radial
exterior coordinates. -/
theorem exists_rootBranchExploredCertificate_of_success
    {d m n : ℕ} (hmn : m ≤ n) (a : CubicDirection d)
    (p incremented : I) {delta : ℝ} (hdelta : delta = (incremented : ℝ))
    (X : CubicEdge d → ℝ)
    (hsuccess : X ∈ rootBranchSuccessEvent d m n p delta a) :
    ∃ (e : CubicEdge d) (y c : Cubic d)
        (w : (cubicGraph d).Walk
          (cubicRegionBoundaryOutsideEndpoint (cubicMetricBox d cubicOrigin m) e) y),
      e ∈ cubicRegionBoundaryEdgesWithinBox d
          (cubicMetricBox d cubicOrigin m) n ∧
      y ∈ seededBoundaryQuadrant d a.1 n ∧
      cubicStepFrom y (a.1, true) ∈ cubicMetricBox d c m ∧
      SeedBoxWithinBoundaryLayer d a.1 m n c ∧
      walkEdgeFinset w ⊆ cubicRegionExteriorEdgesWithinBox d
        (cubicMetricBox d cubicOrigin m) n ∧
      (cubicRestartFrameIso cubicOrigin a (rootRadialTransverseFlip a)).mapEdgeSet e ∈
        rootRadialExploredEdges d m n p incremented X ∧
      (∀ f ∈ walkEdgeFinset w,
        (cubicRestartFrameIso cubicOrigin a
            (rootRadialTransverseFlip a)).mapEdgeSet f ∈
          rootRadialExploredEdges d m n p incremented X ∧
        (cubicRestartFrameIso cubicOrigin a
            (rootRadialTransverseFlip a)).mapEdgeSet f ∈
          rootRadialExteriorEdges d m n) ∧
      (cubicRestartFrameIso cubicOrigin a
          (rootRadialTransverseFlip a)).mapEdgeSet
          (cubicStepEdge y (a.1, true)) ∈
        rootRadialExploredEdges d m n p incremented X ∧
      (cubicRestartFrameIso cubicOrigin a
          (rootRadialTransverseFlip a)).mapEdgeSet
          (cubicStepEdge y (a.1, true)) ∈
        rootRadialExteriorEdges d m n ∧
      ∀ f ∈ cubicBoxEdges d c m,
        (cubicRestartFrameIso cubicOrigin a
            (rootRadialTransverseFlip a)).mapEdgeSet f ∈
          rootRadialExploredEdges d m n p incremented X ∧
        (cubicRestartFrameIso cubicOrigin a
            (rootRadialTransverseFlip a)).mapEdgeSet f ∈
          rootRadialExteriorEdges d m n := by
  classical
  let R := cubicMetricBox d cubicOrigin m
  let E := cubicRegionBoundaryEdgesWithinBox d R n
  let F := cubicRestartFrameIso cubicOrigin a (rootRadialTransverseFlip a)
  let Xref := cubicGraphIsoCouplingReindex F X
  let B := finiteEdgesBelow (rootInitialBoundaryEdges d m n) incremented X
  let A := B ∪ finiteEdgesBelow (rootRadialExteriorEdges d m n) p X
  let C := finiteEdgeReachableClosure A B
  change Xref ∈ sprinkledRestartEvent d a.1 m n R p (fun _ ↦ 0) delta at hsuccess
  rcases hsuccess with ⟨e, heAvailable, heIncrement⟩
  change e ∈ seededRegionAvailableExitEdges d a.1 m n R
    (clearedThreshold E p Xref) at heAvailable
  rw [seededRegionAvailableExitEdges, mem_regionAvailableExitEdges_iff] at heAvailable
  rcases heAvailable with ⟨heBoundary, y, hyTarget, w, hwOpen, hwExterior⟩
  rw [mem_seededBoundaryPointFinset_iff] at hyTarget
  rcases hyTarget with ⟨hyQuadrant, hyOutward, c, hyc, hcLayer, hcSeed⟩
  have hePhysicalBoundary : F.mapEdgeSet e ∈ rootInitialBoundaryEdges d m n := by
    exact rootBranch_mapEdgeSet_mem_rootInitialBoundaryEdges a heBoundary
  have hePhysicalOpen : X (F.mapEdgeSet e) < (incremented : ℝ) := by
    change Xref e < (incremented : ℝ)
    simpa [hdelta] using heIncrement
  have heB : F.mapEdgeSet e ∈ B := by
    exact mem_finiteEdgesBelow_iff.mpr ⟨hePhysicalBoundary, hePhysicalOpen⟩
  have hBA : B ⊆ A := Finset.subset_union_left
  have heC : F.mapEdgeSet e ∈ C :=
    sources_subset_finiteEdgeReachableClosure (allowed := A) (sources := B) hBA heB
  have heExplored : F.mapEdgeSet e ∈
      rootRadialExploredEdges d m n p incremented X := by
    change F.mapEdgeSet e ∈
      nextExploredEdgeSet (rootInitialExploredEdges d m) A B
    exact Finset.mem_union_right _ heC
  have referenceOpen_mem_A : ∀ {f : CubicEdge d},
      f ∈ restartEventSupport d a.1 m n R → f ∉ E → Xref f < (p : ℝ) →
        F.mapEdgeSet f ∈ A := by
    intro f hfSupport hfNotBoundary hfOpen
    apply Finset.mem_union_right
    rw [mem_finiteEdgesBelow_iff]
    refine ⟨rootBranch_mapEdgeSet_mem_rootRadialExteriorEdges_of_restartSupport
      hmn a hfSupport ?_, ?_⟩
    · simpa [R, E] using hfNotBoundary
    · exact hfOpen
  let o : CubicEdge d := cubicStepEdge y (a.1, true)
  have hoTarget : o ∈ seededBoundaryTargetSupport d a.1 m n :=
    cubicStepEdge_mem_seededBoundaryTargetSupport hyQuadrant
  have hoSupport : o ∈ restartEventSupport d a.1 m n R :=
    target_subset_restartEventSupport d a.1 m n R hoTarget
  have hoOpen : Xref o < (p : ℝ) := hyOutward.1
  have hoNotBoundary : o ∉ E := hyOutward.2
  have hoA : F.mapEdgeSet o ∈ A :=
    referenceOpen_mem_A hoSupport hoNotBoundary hoOpen
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
    change F (cubicRegionBoundaryOutsideEndpoint R e) ∈
      Sym2.map F (e : Sym2 (Cubic d))
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
    refine ⟨(o : Sym2 (Cubic d)), ?_, ?_⟩
    · change (o : Sym2 (Cubic d)) ∈ (w.append step).edges
      rw [SimpleGraph.Walk.edges_append]
      apply List.mem_append_right
      simp only [step, SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil,
        List.mem_singleton]
      rfl
    · rfl
  have hoC : F.mapEdgeSet o ∈ C := hqClosure hoPhysicalWalk
  have hoExplored : F.mapEdgeSet o ∈
      rootRadialExploredEdges d m n p incremented X := by
    change F.mapEdgeSet o ∈
      nextExploredEdgeSet (rootInitialExploredEdges d m) A B
    exact Finset.mem_union_right _ hoC
  have hoNotBoundary' : o ∉ cubicRegionBoundaryEdgesWithinBox d
      (cubicMetricBox d cubicOrigin m) n := by
    simpa [E, R] using hoNotBoundary
  have hoExterior : F.mapEdgeSet o ∈ rootRadialExteriorEdges d m n :=
    rootBranch_mapEdgeSet_mem_rootRadialExteriorEdges_of_restartSupport
      hmn a hoSupport hoNotBoundary'
  have hseedAllowed :
      (cubicBoxEdges d c m).image F.mapEdgeSet ⊆ A := by
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
  have hentryBox : F (cubicStepFrom y (a.1, true)) ∈
      cubicMetricBox d (F c) m :=
    (cubicRestartFrameIso_mem_cubicMetricBox_iff
      cubicOrigin a (rootRadialTransverseFlip a) c
      (cubicStepFrom y (a.1, true))).2 hyc
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
      cubicOrigin a (rootRadialTransverseFlip a) c z).1
    apply endpoint_mem_cubicMetricBox_of_edge_mem_cubicBoxEdges hg
    change F z ∈ Sym2.map F (f : Sym2 (Cubic d))
    exact Sym2.mem_map.mpr ⟨z, hz, rfl⟩
  refine ⟨e, y, c, w, heBoundary, hyQuadrant, hyc, hcLayer, hwExterior, heExplored, ?_,
    hoExplored, hoExterior, ?_⟩
  · intro f hfw
    have hfPhysicalWalk : F.mapEdgeSet f ∈ walkEdgeFinset qPhysical := by
      rw [mem_walkEdgeFinset_iff, SimpleGraph.Walk.edges_map]
      apply List.mem_map.mpr
      refine ⟨(f : Sym2 (Cubic d)), ?_, rfl⟩
      change (f : Sym2 (Cubic d)) ∈ (w.append step).edges
      rw [SimpleGraph.Walk.edges_append]
      exact List.mem_append_left _ ((mem_walkEdgeFinset_iff w f).mp hfw)
    have hfC := hqClosure hfPhysicalWalk
    refine ⟨?_, ?_⟩
    · change F.mapEdgeSet f ∈
        nextExploredEdgeSet (rootInitialExploredEdges d m) A B
      exact Finset.mem_union_right _ hfC
    · have hfExterior := hwExterior hfw
      exact rootBranch_mapEdgeSet_mem_rootRadialExteriorEdges a hfExterior
  · intro f hfSeed
    have hfClosure : F.mapEdgeSet f ∈ C := by
      apply hseedClosure
      apply mem_cubicBoxEdges_of_endpoints
      intro z hz
      change z ∈ Sym2.map F (f : Sym2 (Cubic d)) at hz
      obtain ⟨y, hyf, rfl⟩ := Sym2.mem_map.mp hz
      exact (cubicRestartFrameIso_mem_cubicMetricBox_iff
        cubicOrigin a (rootRadialTransverseFlip a) c y).2
          (endpoint_mem_cubicMetricBox_of_edge_mem_cubicBoxEdges hfSeed hyf)
    refine ⟨?_, ?_⟩
    · change F.mapEdgeSet f ∈
        nextExploredEdgeSet (rootInitialExploredEdges d m) A B
      exact Finset.mem_union_right _ hfClosure
    · have hfTarget := seedEdge_mem_seededBoundaryTargetSupport
        hyQuadrant hyc hcLayer hfSeed
      exact rootBranch_mapEdgeSet_mem_rootRadialExteriorEdges_of_restartSupport
        hmn a (target_subset_restartEventSupport d a.1 m n R hfTarget)
        (by exact (hcSeed hfSeed).2)

/-- Directional radial success is stable on the unchanged accumulated post-radial state cell.
Unlike the rejected full threshold-pattern refinement, this theorem uses only the source
history's old-boundary and explored-edge intervals. -/
theorem rootBranchSuccessEvent_of_mem_rootPostRadialSourceHistoryProfile
    {d m n : ℕ} [NeZero d] (hm : 1 ≤ m) (hmn : m + 1 ≤ n)
    (a : CubicDirection d) (p incremented : I) {delta : ℝ}
    (hdelta : delta = (incremented : ℝ)) (X Y : CubicEdge d → ℝ)
    (hsuccess : X ∈ rootBranchSuccessEvent d m n p delta a)
    (hY : Y ∈
      (rootPostRadialSourceEdgeState d m n p incremented X).historyProfile.event) :
    Y ∈ rootBranchSuccessEvent d m n p delta a := by
  classical
  have hmn' : m ≤ n := by omega
  obtain ⟨e, y, c, w, heBoundary, hyQuadrant, hyc, hcLayer, hwExterior,
      heExplored, hwCertificate, hoExplored, hoExterior, hseedCertificate⟩ :=
    exists_rootBranchExploredCertificate_of_success hmn' a p incremented
      hdelta X hsuccess
  let R := cubicMetricBox d cubicOrigin m
  let E := cubicRegionBoundaryEdgesWithinBox d R n
  let F := cubicRestartFrameIso cubicOrigin a (rootRadialTransverseFlip a)
  let Yref := cubicGraphIsoCouplingReindex F Y
  change Yref ∈ sprinkledRestartEvent d a.1 m n R p (fun _ ↦ 0) delta
  refine ⟨e, ?_, ?_⟩
  · change e ∈ seededRegionAvailableExitEdges d a.1 m n R
      (clearedThreshold E p Yref)
    rw [seededRegionAvailableExitEdges, mem_regionAvailableExitEdges_iff]
    refine ⟨heBoundary, y, ?_, w, ?_, ?_⟩
    · rw [mem_seededBoundaryPointFinset_iff]
      refine ⟨hyQuadrant, ?_, c, hyc, hcLayer, ?_⟩
      · change Yref (cubicStepEdge y (a.1, true)) < (p : ℝ) ∧
          cubicStepEdge y (a.1, true) ∉ E
        constructor
        · change Y (F.mapEdgeSet (cubicStepEdge y (a.1, true))) < (p : ℝ)
          exact label_lt_density_of_mem_rootPostRadialSourceHistoryProfile
            hm hmn p incremented X Y hoExterior hoExplored hY
        · intro hoBoundary
          have hoBox := (mem_cubicRegionBoundaryEdgesWithinBox_iff.mp hoBoundary).1
          exact (Finset.mem_sdiff.mp
            (cubicStepEdge_mem_seededBoundaryTargetSupport (m := m) hyQuadrant)).2 hoBox
      · intro f hfSeed
        change Yref f < (p : ℝ) ∧ f ∉ E
        have hfCertificate := hseedCertificate f hfSeed
        constructor
        · change Y (F.mapEdgeSet f) < (p : ℝ)
          exact label_lt_density_of_mem_rootPostRadialSourceHistoryProfile
            hm hmn p incremented X Y hfCertificate.2 hfCertificate.1 hY
        · intro hfBoundary
          have hfBox := (mem_cubicRegionBoundaryEdgesWithinBox_iff.mp hfBoundary).1
          exact (Finset.mem_sdiff.mp
            (seedEdge_mem_seededBoundaryTargetSupport
              hyQuadrant hyc hcLayer hfSeed)).2 hfBox
    · intro fSym hfWalk
      let f : CubicEdge d := ⟨fSym, w.edges_subset_edgeSet hfWalk⟩
      have hfFinset : f ∈ walkEdgeFinset w :=
        (mem_walkEdgeFinset_iff w f).mpr hfWalk
      have hfCertificate := hwCertificate f hfFinset
      change Yref f < (p : ℝ) ∧ f ∉ E
      constructor
      · change Y (F.mapEdgeSet f) < (p : ℝ)
        exact label_lt_density_of_mem_rootPostRadialSourceHistoryProfile
          hm hmn p incremented X Y hfCertificate.2 hfCertificate.1 hY
      · intro hfBoundary
        exact Set.disjoint_left.mp
          (disjoint_cubicRegionExteriorEdgesWithinBox_boundary d R n)
          (hwExterior hfFinset) hfBoundary
    · exact hwExterior
  · change Yref e < ((fun _ : CubicEdge d ↦ (0 : I)) e : ℝ) + delta
    have hePhysicalBoundary := rootBranch_mapEdgeSet_mem_rootInitialBoundaryEdges a
      heBoundary
    have heOpen := label_lt_incremented_of_mem_rootPostRadialSourceHistoryProfile
      hm hmn p incremented X Y hePhysicalBoundary heExplored hY
    simpa [Yref, F, hdelta] using heOpen

/-- The complete simultaneous radial event is constant on every reachable post-radial
accumulated-history cell. -/
theorem rootRadialEvent_of_mem_rootPostRadialSourceHistoryProfile
    {d m n : ℕ} [NeZero d] (hm : 1 ≤ m) (hmn : m + 1 ≤ n)
    (p incremented : I) {delta : ℝ} (hdelta : delta = (incremented : ℝ))
    (X Y : CubicEdge d → ℝ) (hradial : X ∈ rootRadialEvent d m n p delta)
    (hY : Y ∈
      (rootPostRadialSourceEdgeState d m n p incremented X).historyProfile.event) :
    Y ∈ rootRadialEvent d m n p delta := by
  refine ⟨rootSeedLabelEvent_of_mem_rootPostRadialSourceHistoryProfile
    p incremented X Y hY, ?_⟩
  rw [Set.mem_iInter]
  intro a
  exact rootBranchSuccessEvent_of_mem_rootPostRadialSourceHistoryProfile
    hm hmn a p incremented hdelta X Y (Set.mem_iInter.mp hradial.2 a) hY

end Percolation
