import Percolation.Critical.DynamicEdgeExploration
import Percolation.Critical.DynamicRootInitialization

/-!
# The literal edge state after the root radial phase

This file constructs Grimmett's `E₁`, the finite radial exploration support, and the resulting
`E₂` as an edge-line-graph reachable closure.  It then instantiates the displayed threshold
updates (7.31)--(7.32).  The construction is deliberately separate from the event-level union
bound (7.30): `rootRadialEvent` proves that every directional target is reached, while the edge
state records all edges actually revealed by the simultaneous radial search.
-/

namespace Percolation

open scoped unitInterval

/-- Source `E₁`: every edge internal to the central seed box. -/
noncomputable def rootInitialExploredEdges (d m : ℕ) : Finset (CubicEdge d) :=
  cubicBoxEdges d cubicOrigin m

/-- The boundary `Delta E₁` used by all simultaneous radial branches. -/
noncomputable def rootInitialBoundaryEdges (d m n : ℕ) : Finset (CubicEdge d) :=
  cubicRegionBoundaryEdgesWithinBox d (cubicMetricBox d cubicOrigin m) n

/-- Finite union of all coordinates used in the simultaneous signed radial phase. -/
noncomputable def rootRadialEdgeSupport (d m n : ℕ) : Finset (CubicEdge d) := by
  classical
  exact rootInitialExploredEdges d m ∪ rootInitialBoundaryEdges d m n ∪
    (Finset.univ : Finset (CubicDirection d)).biUnion fun a ↦
      (rootBranchQuery d m a).restartSupport m n

/-- Coordinates available after crossing the old boundary. -/
noncomputable def rootRadialExteriorEdges (d m n : ℕ) : Finset (CubicEdge d) :=
  rootRadialEdgeSupport d m n \
    (rootInitialExploredEdges d m ∪ rootInitialBoundaryEdges d m n)

/-- A reference last-exit edge for one radial branch is a physical old-boundary edge after
transport through that branch's signed coordinate frame. -/
theorem rootBranch_mapEdgeSet_mem_rootInitialBoundaryEdges
    {d m n : ℕ} (a : CubicDirection d) {e : CubicEdge d}
    (he : e ∈ cubicRegionBoundaryEdgesWithinBox d
      (cubicMetricBox d cubicOrigin m) n) :
    (cubicRestartFrameIso cubicOrigin a (rootRadialTransverseFlip a)).mapEdgeSet e ∈
      rootInitialBoundaryEdges d m n := by
  classical
  let F := cubicRestartFrameIso cubicOrigin a (rootRadialTransverseFlip a)
  have heBox := (mem_cubicRegionBoundaryEdgesWithinBox_iff.mp he).1
  have hePhysicalBox : F.mapEdgeSet e ∈ cubicBoxEdges d cubicOrigin n := by
    have himage : F.mapEdgeSet e ∈
        (cubicBoxEdges d cubicOrigin n).image F.mapEdgeSet :=
      Finset.mem_image.mpr ⟨e, heBox, rfl⟩
    simpa [F, cubicRestartFrameIso_image_cubicBoxEdges_eq] using himage
  let x := cubicRegionBoundaryInsideEndpoint (cubicMetricBox d cubicOrigin m) e
  let y := cubicRegionBoundaryOutsideEndpoint (cubicMetricBox d cubicOrigin m) e
  have hxR : x ∈ cubicMetricBox d cubicOrigin m :=
    cubicRegionBoundaryInsideEndpoint_mem he
  have hyR : y ∉ cubicMetricBox d cubicOrigin m :=
    cubicRegionBoundaryOutsideEndpoint_not_mem he
  have hFxR : F x ∈ cubicMetricBox d cubicOrigin m := by
    simpa [F, cubicOrigin] using
      (cubicRestartFrameIso_mem_cubicMetricBox_iff
        cubicOrigin a (rootRadialTransverseFlip a) cubicOrigin x).2 hxR
  have hFyR : F y ∉ cubicMetricBox d cubicOrigin m := by
    intro hFy
    apply hyR
    exact (cubicRestartFrameIso_mem_cubicMetricBox_iff
      cubicOrigin a (rootRadialTransverseFlip a) cubicOrigin y).1 (by
        simpa [F, cubicOrigin] using hFy)
  apply mem_cubicRegionBoundaryEdgesWithinBox_of_endpoints hePhysicalBox
    (x := F x) (y := F y)
  · change F x ∈ Sym2.map F (e : Sym2 (Cubic d))
    exact Sym2.mem_map.mpr ⟨x, by
      rw [← cubicRegionBoundaryEndpoints_edge he]
      simp [x, y], rfl⟩
  · change F y ∈ Sym2.map F (e : Sym2 (Cubic d))
    exact Sym2.mem_map.mpr ⟨y, by
      rw [← cubicRegionBoundaryEndpoints_edge he]
      simp [x, y], rfl⟩
  · exact hFxR
  · exact hFyR

theorem rootBranch_mapEdgeSet_mem_rootInitialBoundaryEdges_iff
    {d m n : ℕ} (a : CubicDirection d) {e : CubicEdge d} :
    (cubicRestartFrameIso cubicOrigin a (rootRadialTransverseFlip a)).mapEdgeSet e ∈
        rootInitialBoundaryEdges d m n ↔
      e ∈ cubicRegionBoundaryEdgesWithinBox d
        (cubicMetricBox d cubicOrigin m) n := by
  classical
  let F := cubicRestartFrameIso cubicOrigin a (rootRadialTransverseFlip a)
  constructor
  · intro hePhysical
    change F.mapEdgeSet e ∈ rootInitialBoundaryEdges d m n at hePhysical
    have hePhysicalBox :=
      (mem_cubicRegionBoundaryEdgesWithinBox_iff.mp hePhysical).1
    have heImage : F.mapEdgeSet e ∈
        (cubicBoxEdges d cubicOrigin n).image F.mapEdgeSet := by
      simpa [F, cubicRestartFrameIso_image_cubicBoxEdges_eq] using hePhysicalBox
    obtain ⟨f, hfBox, hfe⟩ := Finset.mem_image.mp heImage
    have heBox : e ∈ cubicBoxEdges d cubicOrigin n := by
      have : f = e := F.mapEdgeSet.injective hfe
      simpa [this] using hfBox
    let x := cubicRegionBoundaryInsideEndpoint (cubicMetricBox d cubicOrigin m)
      (F.mapEdgeSet e)
    let y := cubicRegionBoundaryOutsideEndpoint (cubicMetricBox d cubicOrigin m)
      (F.mapEdgeSet e)
    have hxPhysical : x ∈ cubicMetricBox d cubicOrigin m :=
      cubicRegionBoundaryInsideEndpoint_mem hePhysical
    have hyPhysical : y ∉ cubicMetricBox d cubicOrigin m :=
      cubicRegionBoundaryOutsideEndpoint_not_mem hePhysical
    have hxMap : x ∈ (F.mapEdgeSet e : Sym2 (Cubic d)) := by
      rw [← cubicRegionBoundaryEndpoints_edge hePhysical]
      simp [x]
    have hyMap : y ∈ (F.mapEdgeSet e : Sym2 (Cubic d)) := by
      rw [← cubicRegionBoundaryEndpoints_edge hePhysical]
      simp [y]
    change x ∈ Sym2.map F (e : Sym2 (Cubic d)) at hxMap
    change y ∈ Sym2.map F (e : Sym2 (Cubic d)) at hyMap
    obtain ⟨xRef, hxRefEdge, hxEq⟩ := Sym2.mem_map.mp hxMap
    obtain ⟨yRef, hyRefEdge, hyEq⟩ := Sym2.mem_map.mp hyMap
    have hxRef : xRef ∈ cubicMetricBox d cubicOrigin m :=
      (cubicRestartFrameIso_mem_cubicMetricBox_iff
        cubicOrigin a (rootRadialTransverseFlip a) cubicOrigin xRef).1 (by
          simpa [F, cubicOrigin, hxEq] using hxPhysical)
    have hyRef : yRef ∉ cubicMetricBox d cubicOrigin m := by
      intro hy
      apply hyPhysical
      simpa [F, cubicOrigin, hxEq, hyEq] using
        (cubicRestartFrameIso_mem_cubicMetricBox_iff
          cubicOrigin a (rootRadialTransverseFlip a) cubicOrigin yRef).2 hy
    exact mem_cubicRegionBoundaryEdgesWithinBox_of_endpoints heBox
      hxRefEdge hyRefEdge hxRef hyRef
  · exact rootBranch_mapEdgeSet_mem_rootInitialBoundaryEdges a

/-- Every non-boundary coordinate of one framed radial restart is a physical radial exterior
coordinate. -/
theorem rootBranch_mapEdgeSet_mem_rootRadialExteriorEdges_of_restartSupport
    {d m n : ℕ} (hmn : m ≤ n) (a : CubicDirection d) {e : CubicEdge d}
    (heSupport : e ∈ restartEventSupport d a.1 m n
      (cubicMetricBox d cubicOrigin m))
    (heNotBoundary : e ∉ cubicRegionBoundaryEdgesWithinBox d
      (cubicMetricBox d cubicOrigin m) n) :
    (cubicRestartFrameIso cubicOrigin a (rootRadialTransverseFlip a)).mapEdgeSet e ∈
      rootRadialExteriorEdges d m n := by
  classical
  let F := cubicRestartFrameIso cubicOrigin a (rootRadialTransverseFlip a)
  rw [rootRadialExteriorEdges, Finset.mem_sdiff, Finset.mem_union]
  refine ⟨?_, ?_⟩
  · rw [rootRadialEdgeSupport]
    apply Finset.mem_union_right
    rw [Finset.mem_biUnion]
    refine ⟨a, Finset.mem_univ a, ?_⟩
    change F.mapEdgeSet e ∈ framedRestartSupport cubicOrigin a
      (rootRadialTransverseFlip a) m n (cubicMetricBox d cubicOrigin m)
    rw [framedRestartSupport]
    exact Finset.mem_image.mpr ⟨e, heSupport, rfl⟩
  · intro h
    rcases h with hSeed | hBoundary
    · change F.mapEdgeSet e ∈ cubicBoxEdges d cubicOrigin m at hSeed
      exact Set.disjoint_left.mp
        (disjoint_rootSeedSupport_rootBranchRestartSupport (d := d)
          (m := m) (n := n) hmn a)
        hSeed (by
          change F.mapEdgeSet e ∈ framedRestartSupport cubicOrigin a
            (rootRadialTransverseFlip a) m n (cubicMetricBox d cubicOrigin m)
          rw [framedRestartSupport]
          exact Finset.mem_image.mpr ⟨e, heSupport, rfl⟩)
    · exact heNotBoundary
        ((rootBranch_mapEdgeSet_mem_rootInitialBoundaryEdges_iff a).mp hBoundary)

/-- A reference exterior edge used by one radial branch lands in the physical simultaneous
radial exterior support. -/
theorem rootBranch_mapEdgeSet_mem_rootRadialExteriorEdges
    {d m n : ℕ} (a : CubicDirection d) {e : CubicEdge d}
    (he : e ∈ cubicRegionExteriorEdgesWithinBox d
      (cubicMetricBox d cubicOrigin m) n) :
    (cubicRestartFrameIso cubicOrigin a (rootRadialTransverseFlip a)).mapEdgeSet e ∈
      rootRadialExteriorEdges d m n := by
  classical
  let F := cubicRestartFrameIso cubicOrigin a (rootRadialTransverseFlip a)
  have heBox := (mem_cubicRegionExteriorEdgesWithinBox_iff.mp he).1
  have heEnds := (mem_cubicRegionExteriorEdgesWithinBox_iff.mp he).2
  have hePhysicalBox : F.mapEdgeSet e ∈ cubicBoxEdges d cubicOrigin n := by
    have himage : F.mapEdgeSet e ∈
        (cubicBoxEdges d cubicOrigin n).image F.mapEdgeSet :=
      Finset.mem_image.mpr ⟨e, heBox, rfl⟩
    simpa [F, cubicRestartFrameIso_image_cubicBoxEdges_eq] using himage
  have hePhysicalExterior : F.mapEdgeSet e ∈
      cubicRegionExteriorEdgesWithinBox d (cubicMetricBox d cubicOrigin m) n := by
    rw [mem_cubicRegionExteriorEdgesWithinBox_iff]
    refine ⟨hePhysicalBox, ?_⟩
    intro z hz hzin
    change z ∈ Sym2.map F (e : Sym2 (Cubic d)) at hz
    obtain ⟨y, hye, rfl⟩ := Sym2.mem_map.mp hz
    apply heEnds y hye
    exact (cubicRestartFrameIso_mem_cubicMetricBox_iff
      cubicOrigin a (rootRadialTransverseFlip a) cubicOrigin y).1 (by
        simpa [F, cubicOrigin] using hzin)
  rw [rootRadialExteriorEdges, Finset.mem_sdiff, Finset.mem_union]
  refine ⟨?_, ?_⟩
  · rw [rootRadialEdgeSupport]
    apply Finset.mem_union_right
    rw [Finset.mem_biUnion]
    refine ⟨a, Finset.mem_univ a, ?_⟩
    rw [FramedRestartQuery.restartSupport, framedRestartSupport]
    exact Finset.mem_image.mpr
      ⟨e, exterior_subset_restartEventSupport d a.1 m n
        (cubicMetricBox d cubicOrigin m) he, rfl⟩
  · intro h
    rcases h with hSeed | hBoundary
    · exact (mem_cubicRegionExteriorEdgesWithinBox_iff.mp hePhysicalExterior).2
        _ (Sym2.out_fst_mem _)
        (endpoint_mem_cubicMetricBox_of_edge_mem_cubicBoxEdges hSeed
          (Sym2.out_fst_mem _))
    · change F.mapEdgeSet e ∈ cubicRegionBoundaryEdgesWithinBox d
        (cubicMetricBox d cubicOrigin m) n at hBoundary
      exact Set.disjoint_left.mp
        (disjoint_cubicRegionExteriorEdgesWithinBox_boundary d
          (cubicMetricBox d cubicOrigin m) n)
        hePhysicalExterior hBoundary

/-- Source `E₂`, obtained from `E₁` by adjoining every radial exterior edge reachable from an
exit which opens in the first increment. -/
noncomputable def rootRadialExploredEdges
    (d m n : ℕ) (p incremented : I) (X : CubicEdge d → ℝ) :
    Finset (CubicEdge d) :=
  exploredEdgeStep (rootInitialExploredEdges d m)
    (rootInitialBoundaryEdges d m n) (rootRadialExteriorEdges d m n)
      p incremented X

/-- One simultaneous radial branch reads only the common radius `n + 2m + 1` box. -/
theorem rootBranchQuery_restartSupport_subset_wideBox
    {d m n : ℕ} (a : CubicDirection d) :
    (rootBranchQuery d m a).restartSupport m n ⊆
      cubicBoxEdges d cubicOrigin (n + 2 * m + 1) := by
  classical
  let F := cubicRestartFrameIso cubicOrigin a (rootRadialTransverseFlip a)
  intro e he
  change e ∈ framedRestartSupport cubicOrigin a (rootRadialTransverseFlip a)
    m n (cubicMetricBox d cubicOrigin m) at he
  rw [framedRestartSupport, Finset.mem_image] at he
  obtain ⟨f, hfRestart, rfl⟩ := he
  have hfWide := restartEventSupport_subset_cubicBoxEdges_wide
    d a.1 m n (cubicMetricBox d cubicOrigin m) hfRestart
  have hImage : F.mapEdgeSet f ∈
      (cubicBoxEdges d cubicOrigin (n + 2 * m + 1)).image F.mapEdgeSet :=
    Finset.mem_image.mpr ⟨f, hfWide, rfl⟩
  rw [show (cubicBoxEdges d cubicOrigin (n + 2 * m + 1)).image F.mapEdgeSet =
      cubicBoxEdges d cubicOrigin (n + 2 * m + 1) by
    simpa [F] using cubicRestartFrameIso_image_cubicBoxEdges_eq
      (n := n + 2 * m + 1) cubicOrigin a (rootRadialTransverseFlip a)] at hImage
  exact hImage

/-- The union of all simultaneous root-branch reveal coordinates has the same wide-box
bound. -/
theorem rootRadialEdgeSupport_subset_wideBox (d m n : ℕ) :
    rootRadialEdgeSupport d m n ⊆
      cubicBoxEdges d cubicOrigin (n + 2 * m + 1) := by
  classical
  intro e he
  simp only [rootRadialEdgeSupport, Finset.mem_union, Finset.mem_biUnion] at he
  rcases he with (heInitial | heBoundary) | ⟨a, _ha, heBranch⟩
  · exact cubicBoxEdges_mono_radius (by omega) heInitial
  · exact cubicBoxEdges_mono_radius (by omega)
      (mem_cubicRegionBoundaryEdgesWithinBox_iff.mp heBoundary).1
  · exact rootBranchQuery_restartSupport_subset_wideBox a heBranch

/-- The new line-graph boundary `Delta E₂`, restricted to the finite radial support. -/
noncomputable def rootRadialNewBoundaryEdges
    (d m n : ℕ) (p incremented : I) (X : CubicEdge d → ℝ) :
    Finset (CubicEdge d) :=
  cubicEdgeBoundaryWithin (rootRadialExploredEdges d m n p incremented X)
    (rootRadialEdgeSupport d m n)

theorem rootInitialExploredEdges_subset_rootRadialExploredEdges
    (d m n : ℕ) (p incremented : I) (X : CubicEdge d → ℝ) :
    rootInitialExploredEdges d m ⊆ rootRadialExploredEdges d m n p incremented X :=
  oldExplored_subset_exploredEdgeStep _ _ _ _ _ _

theorem rootRadialExploredEdges_subset_support
    (d m n : ℕ) (p incremented : I) (X : CubicEdge d → ℝ) :
    rootRadialExploredEdges d m n p incremented X ⊆ rootRadialEdgeSupport d m n := by
  intro e he
  have hstep := exploredEdgeStep_subset
    (rootInitialExploredEdges d m) (rootInitialBoundaryEdges d m n)
      (rootRadialExteriorEdges d m n) p incremented X he
  simp only [rootRadialExteriorEdges, Finset.mem_union, Finset.mem_sdiff] at hstep
  rcases hstep with (heSeed | heBoundary) | ⟨heSupport, _⟩
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ heSeed)
  · exact Finset.mem_union_left _ (Finset.mem_union_right _ heBoundary)
  · exact heSupport

/-- A region boundary edge cannot be an internal central-seed edge. -/
theorem disjoint_rootInitialBoundaryEdges_rootInitialExploredEdges
    (d m n : ℕ) :
    Disjoint (rootInitialBoundaryEdges d m n) (rootInitialExploredEdges d m) := by
  rw [Finset.disjoint_left]
  intro e heBoundary heSeed
  have heEnds : ∀ x ∈ (e : Sym2 (Cubic d)),
      x ∈ cubicMetricBox d cubicOrigin m := by
    intro x hx
    exact endpoint_mem_cubicMetricBox_of_edge_mem_cubicBoxEdges heSeed hx
  rcases (mem_cubicRegionBoundaryEdgesWithinBox_iff.mp heBoundary).2 with h | h
  · exact h.2 (heEnds e.1.out.2 (Sym2.out_snd_mem e.1))
  · exact h.2 (heEnds e.1.out.1 (Sym2.out_fst_mem e.1))

/-- For the central box, the source's vertex-region boundary contains the literal line-graph
boundary of `E₁`.  The one-layer hypothesis is exactly what places every adjacent edge inside
the finite radius-`n` support used by the restart. -/
theorem rootEdgeLineBoundary_subset_rootInitialBoundaryEdges
    {d m n : ℕ} (hmn : m + 1 ≤ n) :
    cubicEdgeBoundaryWithin (rootInitialExploredEdges d m)
      (rootRadialEdgeSupport d m n) ⊆ rootInitialBoundaryEdges d m n := by
  classical
  intro f hf
  obtain ⟨_hfAmbient, hfNotInitial, e, heInitial, hef⟩ :=
    mem_cubicEdgeBoundaryWithin_iff.mp hf
  obtain ⟨x, hxe, hxf⟩ := hef.2
  have hxBox : x ∈ cubicMetricBox d cubicOrigin m :=
    endpoint_mem_cubicMetricBox_of_edge_mem_cubicBoxEdges heInitial hxe
  have hfAdj : (cubicGraph d).Adj f.1.out.1 f.1.out.2 := by
    exact (SimpleGraph.mem_edgeSet (cubicGraph d)).mp (by
      simpa [f.1.out_eq] using f.2)
  have endpointStepBox (u v : Cubic d) (hu : u ∈ cubicMetricBox d cubicOrigin m)
      (huv : (cubicGraph d).Adj u v) :
      v ∈ cubicMetricBox d cubicOrigin (m + 1) := by
    obtain ⟨a, rfl⟩ := (cubicGraph_adj_iff_exists_stepFrom u v).mp huv
    apply mem_cubicMetricBox_iff_lInfDist_le.mpr
    calc
      cubicLInfDist cubicOrigin (cubicStepFrom u a) ≤
          cubicLInfDist cubicOrigin u + cubicLInfDist u (cubicStepFrom u a) :=
        cubicLInfDist_triangle _ _ _
      _ ≤ m + 1 := Nat.add_le_add
        (mem_cubicMetricBox_iff_lInfDist_le.mp hu)
        (cubicLInfDist_stepFrom_le_one u a)
  rw [← f.1.out_eq, Sym2.mem_iff] at hxf
  rcases hxf with hxf | hxf
  · have hfFirst : f.1.out.1 ∈ cubicMetricBox d cubicOrigin m := hxf ▸ hxBox
    have hfSecond : f.1.out.2 ∈ cubicMetricBox d cubicOrigin (m + 1) :=
      endpointStepBox _ _ hfFirst hfAdj
    have hfFirstWide : f.1.out.1 ∈ cubicMetricBox d cubicOrigin (m + 1) :=
      mem_cubicMetricBox_iff_lInfDist_le.mpr
        ((mem_cubicMetricBox_iff_lInfDist_le.mp hfFirst).trans (by omega))
    have hfBoxN : f ∈ cubicBoxEdges d cubicOrigin n :=
      mem_cubicBoxEdges_of_endpoints fun z hz ↦ by
        rw [← f.1.out_eq, Sym2.mem_iff] at hz
        rcases hz with rfl | rfl
        · exact mem_cubicMetricBox_iff_lInfDist_le.mpr
            ((mem_cubicMetricBox_iff_lInfDist_le.mp hfFirstWide).trans hmn)
        · exact mem_cubicMetricBox_iff_lInfDist_le.mpr
            ((mem_cubicMetricBox_iff_lInfDist_le.mp hfSecond).trans hmn)
    have hfSecondOutside : f.1.out.2 ∉ cubicMetricBox d cubicOrigin m := by
      intro hfSecondInside
      apply hfNotInitial
      exact mem_cubicBoxEdges_of_endpoints fun z hz ↦ by
        rw [← f.1.out_eq, Sym2.mem_iff] at hz
        exact hz.elim (fun h ↦ h ▸ hfFirst) (fun h ↦ h ▸ hfSecondInside)
    change f ∈ cubicRegionBoundaryEdgesWithinBox d
      (cubicMetricBox d cubicOrigin m) n
    rw [mem_cubicRegionBoundaryEdgesWithinBox_iff]
    exact ⟨hfBoxN, Or.inl ⟨hfFirst, hfSecondOutside⟩⟩
  · have hfSecond : f.1.out.2 ∈ cubicMetricBox d cubicOrigin m := hxf ▸ hxBox
    have hfFirst : f.1.out.1 ∈ cubicMetricBox d cubicOrigin (m + 1) :=
      endpointStepBox _ _ hfSecond hfAdj.symm
    have hfSecondWide : f.1.out.2 ∈ cubicMetricBox d cubicOrigin (m + 1) :=
      mem_cubicMetricBox_iff_lInfDist_le.mpr
        ((mem_cubicMetricBox_iff_lInfDist_le.mp hfSecond).trans (by omega))
    have hfBoxN : f ∈ cubicBoxEdges d cubicOrigin n :=
      mem_cubicBoxEdges_of_endpoints fun z hz ↦ by
        rw [← f.1.out_eq, Sym2.mem_iff] at hz
        rcases hz with rfl | rfl
        · exact mem_cubicMetricBox_iff_lInfDist_le.mpr
            ((mem_cubicMetricBox_iff_lInfDist_le.mp hfFirst).trans hmn)
        · exact mem_cubicMetricBox_iff_lInfDist_le.mpr
            ((mem_cubicMetricBox_iff_lInfDist_le.mp hfSecondWide).trans hmn)
    have hfFirstOutside : f.1.out.1 ∉ cubicMetricBox d cubicOrigin m := by
      intro hfFirstInside
      apply hfNotInitial
      exact mem_cubicBoxEdges_of_endpoints fun z hz ↦ by
        rw [← f.1.out_eq, Sym2.mem_iff] at hz
        exact hz.elim (fun h ↦ h ▸ hfFirstInside) (fun h ↦ h ▸ hfSecond)
    change f ∈ cubicRegionBoundaryEdgesWithinBox d
      (cubicMetricBox d cubicOrigin m) n
    rw [mem_cubicRegionBoundaryEdgesWithinBox_iff]
    exact ⟨hfBoxN, Or.inr ⟨hfSecond, hfFirstOutside⟩⟩

theorem rootInitialBoundaryEdges_subset_rootRadialEdgeSupport
    (d m n : ℕ) :
    rootInitialBoundaryEdges d m n ⊆ rootRadialEdgeSupport d m n := by
  intro e he
  exact Finset.mem_union_left _ (Finset.mem_union_right _ he)

theorem disjoint_rootRadialNewBoundaryEdges_rootRadialExploredEdges
    (d m n : ℕ) (p incremented : I) (X : CubicEdge d → ℝ) :
    Disjoint (rootRadialNewBoundaryEdges d m n p incremented X)
      (rootRadialExploredEdges d m n p incremented X) :=
  disjoint_cubicEdgeBoundaryWithin_left _ _

/-- Concrete threshold-update data for the displayed root equations (7.31)--(7.32). -/
noncomputable def rootRadialRevealThresholdUpdate
    (d m n : ℕ) (p incremented : I) (X : CubicEdge d → ℝ) :
    RevealThresholdUpdateData (CubicEdge d) :=
  firstRadialRevealUpdate
    (rootInitialExploredEdges d m)
    (rootRadialExploredEdges d m n p incremented X)
    (rootInitialBoundaryEdges d m n)
    (rootRadialNewBoundaryEdges d m n p incremented X)
    (rootRadialEdgeSupport d m n) p incremented

/-- The concrete radial output really is an interval profile. -/
theorem rootRadialReveal_updatedLower_le_updatedUpper
    (d m n : ℕ) (p incremented : I) (X : CubicEdge d → ℝ)
    (e : CubicEdge d) :
    (rootRadialRevealThresholdUpdate d m n p incremented X).updatedLower e ≤
      (rootRadialRevealThresholdUpdate d m n p incremented X).updatedUpper e := by
  exact firstRadial_updatedLower_le_updatedUpper
    (rootInitialExploredEdges d m)
    (rootRadialExploredEdges d m n p incremented X)
    (rootInitialBoundaryEdges d m n)
    (rootRadialNewBoundaryEdges d m n p incremented X)
    (rootRadialEdgeSupport d m n) p incremented
    (disjoint_rootInitialBoundaryEdges_rootInitialExploredEdges d m n)
    (disjoint_rootRadialNewBoundaryEdges_rootRadialExploredEdges
      d m n p incremented X) e

/-- The literal root edge exploration realizes the complete updated reveal interval cell. -/
theorem rootRadialExploredEdges_mem_updatedProfile
    {d m n : ℕ} (hmn : m + 1 ≤ n) (p incremented : I)
    (X : CubicEdge d → ℝ)
    (hseed : X ∈ rootSeedLabelEvent d m p) :
    X ∈ (rootRadialRevealThresholdUpdate d m n p incremented X).updatedProfile.event := by
  apply exploredEdgeStep_mem_firstRadial_updatedProfile
    (rootInitialExploredEdges d m) (rootInitialBoundaryEdges d m n)
    (rootRadialEdgeSupport d m n) p incremented X
    (disjoint_rootInitialBoundaryEdges_rootInitialExploredEdges d m n)
    (rootInitialBoundaryEdges_subset_rootRadialEdgeSupport d m n)
    (rootEdgeLineBoundary_subset_rootInitialBoundaryEdges hmn)
  intro e he
  have heOpen := hseed he
  simpa [thresholdConfiguration] using heOpen

/-- Every realization of the source's simultaneous radial event therefore lies in the exact
post-radial interval fiber. -/
theorem rootRadialEvent_subset_updatedProfile
    {d m n : ℕ} (hmn : m + 1 ≤ n) (p incremented : I) (delta : ℝ) :
    rootRadialEvent d m n p delta ⊆
      {X | X ∈
        (rootRadialRevealThresholdUpdate d m n p incremented X).updatedProfile.event} := by
  intro X hX
  exact rootRadialExploredEdges_mem_updatedProfile hmn p incremented X hX.1

end Percolation
