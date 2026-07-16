import Percolation.Critical.ConcreteAnimals
import Percolation.Critical.RestartSprinkling

/-!
# Region boundaries and available exits for Grimmett Lemma 7.17

This file instantiates the finite-coordinate restart kernel with the geometry of a finite
vertex region `R ⊆ B(n)`.  Boundary edges are oriented only through canonical endpoint
functions; the underlying cubic edge remains unordered.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval

/-- Edges of `B(n)` with exactly one endpoint in the finite region `R`. -/
noncomputable def cubicRegionBoundaryEdgesWithinBox
    (d : ℕ) (R : Finset (Cubic d)) (n : ℕ) : Finset (CubicEdge d) := by
  classical
  exact (cubicBoxEdges d cubicOrigin n).filter fun e =>
    (e.1.out.1 ∈ R ∧ e.1.out.2 ∉ R) ∨ (e.1.out.2 ∈ R ∧ e.1.out.1 ∉ R)

@[simp]
theorem mem_cubicRegionBoundaryEdgesWithinBox_iff
    {d n : ℕ} {R : Finset (Cubic d)} {e : CubicEdge d} :
    e ∈ cubicRegionBoundaryEdgesWithinBox d R n ↔
      e ∈ cubicBoxEdges d cubicOrigin n ∧
        ((e.1.out.1 ∈ R ∧ e.1.out.2 ∉ R) ∨
          (e.1.out.2 ∈ R ∧ e.1.out.1 ∉ R)) := by
  classical
  simp [cubicRegionBoundaryEdgesWithinBox]

/-- The part of a restart region outside `B(n)` is observationally irrelevant to its
box-confined edge boundary.  This is the safe adapter used by dynamic explorations whose
global explored endpoint region is not itself contained in the current restart box. -/
@[simp]
theorem cubicRegionBoundaryEdgesWithinBox_inter_cubicMetricBox
    (d : ℕ) (R : Finset (Cubic d)) (n : ℕ) :
    cubicRegionBoundaryEdgesWithinBox d
        (R ∩ cubicMetricBox d cubicOrigin n) n =
      cubicRegionBoundaryEdgesWithinBox d R n := by
  classical
  ext e
  simp only [mem_cubicRegionBoundaryEdgesWithinBox_iff, Finset.mem_inter]
  constructor
  · rintro ⟨heBox, h | h⟩
    · refine ⟨heBox, Or.inl ⟨h.1.1, ?_⟩⟩
      intro hyR
      exact h.2 ⟨hyR,
        endpoint_mem_cubicMetricBox_of_edge_mem_cubicBoxEdges heBox
          (Sym2.out_snd_mem e.1)⟩
    · refine ⟨heBox, Or.inr ⟨h.1.1, ?_⟩⟩
      intro hxR
      exact h.2 ⟨hxR,
        endpoint_mem_cubicMetricBox_of_edge_mem_cubicBoxEdges heBox
          (Sym2.out_fst_mem e.1)⟩
  · rintro ⟨heBox, h | h⟩
    · exact ⟨heBox, Or.inl
        ⟨⟨h.1, endpoint_mem_cubicMetricBox_of_edge_mem_cubicBoxEdges heBox
            (Sym2.out_fst_mem e.1)⟩, fun hy ↦ h.2 hy.1⟩⟩
    · exact ⟨heBox, Or.inr
        ⟨⟨h.1, endpoint_mem_cubicMetricBox_of_edge_mem_cubicBoxEdges heBox
            (Sym2.out_snd_mem e.1)⟩, fun hx ↦ h.2 hx.1⟩⟩

/-- Canonical endpoint of a region-boundary edge lying in `R`. -/
noncomputable def cubicRegionBoundaryInsideEndpoint
    {d : ℕ} (R : Finset (Cubic d)) (e : CubicEdge d) : Cubic d :=
  if e.1.out.1 ∈ R then e.1.out.1 else e.1.out.2

/-- Canonical endpoint of a region-boundary edge lying outside `R`. -/
noncomputable def cubicRegionBoundaryOutsideEndpoint
    {d : ℕ} (R : Finset (Cubic d)) (e : CubicEdge d) : Cubic d :=
  if e.1.out.1 ∈ R then e.1.out.2 else e.1.out.1

theorem cubicRegionBoundaryInsideEndpoint_mem
    {d n : ℕ} {R : Finset (Cubic d)} {e : CubicEdge d}
    (he : e ∈ cubicRegionBoundaryEdgesWithinBox d R n) :
    cubicRegionBoundaryInsideEndpoint R e ∈ R := by
  classical
  rcases (mem_cubicRegionBoundaryEdgesWithinBox_iff.mp he).2 with h | h
  · simp [cubicRegionBoundaryInsideEndpoint, h.1]
  · simp [cubicRegionBoundaryInsideEndpoint, h.2, h.1]

theorem cubicRegionBoundaryOutsideEndpoint_not_mem
    {d n : ℕ} {R : Finset (Cubic d)} {e : CubicEdge d}
    (he : e ∈ cubicRegionBoundaryEdgesWithinBox d R n) :
    cubicRegionBoundaryOutsideEndpoint R e ∉ R := by
  classical
  rcases (mem_cubicRegionBoundaryEdgesWithinBox_iff.mp he).2 with h | h
  · simpa [cubicRegionBoundaryOutsideEndpoint, h.1] using h.2
  · simp [cubicRegionBoundaryOutsideEndpoint, h.2]

theorem cubicRegionBoundaryEndpoints_edge
    {d n : ℕ} {R : Finset (Cubic d)} {e : CubicEdge d}
    (he : e ∈ cubicRegionBoundaryEdgesWithinBox d R n) :
    s(cubicRegionBoundaryInsideEndpoint R e,
      cubicRegionBoundaryOutsideEndpoint R e) = (e : Sym2 (Cubic d)) := by
  classical
  rcases (mem_cubicRegionBoundaryEdgesWithinBox_iff.mp he).2 with h | h
  · simp [cubicRegionBoundaryInsideEndpoint, cubicRegionBoundaryOutsideEndpoint, h.1,
      e.1.out_eq]
  · simp [cubicRegionBoundaryInsideEndpoint, cubicRegionBoundaryOutsideEndpoint, h.2,
      Sym2.eq_swap, e.1.out_eq]

/-- Edges inside `B(n)` having no endpoint in `R`.  These are precisely the coordinates
permitted after the last exit from `R`. -/
noncomputable def cubicRegionExteriorEdgesWithinBox
    (d : ℕ) (R : Finset (Cubic d)) (n : ℕ) : Finset (CubicEdge d) :=
  cubicBoxEdges d cubicOrigin n \ cubicIncidentEdges d R

theorem mem_cubicRegionExteriorEdgesWithinBox_iff
    {d n : ℕ} {R : Finset (Cubic d)} {e : CubicEdge d} :
    e ∈ cubicRegionExteriorEdgesWithinBox d R n ↔
      e ∈ cubicBoxEdges d cubicOrigin n ∧
        ∀ x ∈ (e : Sym2 (Cubic d)), x ∉ R := by
  classical
  rw [cubicRegionExteriorEdgesWithinBox, Finset.mem_sdiff,
    mem_cubicIncidentEdges_iff_exists_endpoint]
  constructor
  · rintro ⟨heBox, hnot⟩
    exact ⟨heBox, fun x hxe hxR => hnot ⟨x, hxR, hxe⟩⟩
  · rintro ⟨heBox, hends⟩
    refine ⟨heBox, ?_⟩
    rintro ⟨x, hxR, hxe⟩
    exact hends x hxe hxR

/-- Cropping a region to `B(n)` also leaves its box-confined exterior edge set unchanged. -/
@[simp]
theorem cubicRegionExteriorEdgesWithinBox_inter_cubicMetricBox
    (d : ℕ) (R : Finset (Cubic d)) (n : ℕ) :
    cubicRegionExteriorEdgesWithinBox d
        (R ∩ cubicMetricBox d cubicOrigin n) n =
      cubicRegionExteriorEdgesWithinBox d R n := by
  classical
  ext e
  simp only [mem_cubicRegionExteriorEdgesWithinBox_iff, Finset.mem_inter]
  constructor
  · rintro ⟨heBox, hends⟩
    refine ⟨heBox, fun x hxe hxR ↦ ?_⟩
    exact hends x hxe ⟨hxR,
      endpoint_mem_cubicMetricBox_of_edge_mem_cubicBoxEdges heBox hxe⟩
  · rintro ⟨heBox, hends⟩
    exact ⟨heBox, fun x hxe hxR ↦ hends x hxe hxR.1⟩

/-- On a box edge, the canonical inside endpoint is unchanged by cropping the region to the
box. -/
theorem cubicRegionBoundaryInsideEndpoint_inter_cubicMetricBox
    {d n : ℕ} (R : Finset (Cubic d)) {e : CubicEdge d}
    (heBox : e ∈ cubicBoxEdges d cubicOrigin n) :
    cubicRegionBoundaryInsideEndpoint
        (R ∩ cubicMetricBox d cubicOrigin n) e =
      cubicRegionBoundaryInsideEndpoint R e := by
  classical
  have hfst : e.1.out.1 ∈ cubicMetricBox d cubicOrigin n :=
    endpoint_mem_cubicMetricBox_of_edge_mem_cubicBoxEdges heBox
      (Sym2.out_fst_mem e.1)
  simp [cubicRegionBoundaryInsideEndpoint, hfst]

/-- On a box edge, the canonical outside endpoint is unchanged by cropping the region to the
box. -/
theorem cubicRegionBoundaryOutsideEndpoint_inter_cubicMetricBox
    {d n : ℕ} (R : Finset (Cubic d)) {e : CubicEdge d}
    (heBox : e ∈ cubicBoxEdges d cubicOrigin n) :
    cubicRegionBoundaryOutsideEndpoint
        (R ∩ cubicMetricBox d cubicOrigin n) e =
      cubicRegionBoundaryOutsideEndpoint R e := by
  classical
  have hfst : e.1.out.1 ∈ cubicMetricBox d cubicOrigin n :=
    endpoint_mem_cubicMetricBox_of_edge_mem_cubicBoxEdges heBox
      (Sym2.out_fst_mem e.1)
  simp [cubicRegionBoundaryOutsideEndpoint, hfst]

theorem mem_cubicRegionBoundaryEdgesWithinBox_of_endpoints
    {d n : ℕ} {R : Finset (Cubic d)} {e : CubicEdge d} {x y : Cubic d}
    (heBox : e ∈ cubicBoxEdges d cubicOrigin n)
    (hxe : x ∈ (e : Sym2 (Cubic d))) (hye : y ∈ (e : Sym2 (Cubic d)))
    (hxR : x ∈ R) (hyR : y ∉ R) :
    e ∈ cubicRegionBoundaryEdgesWithinBox d R n := by
  rw [mem_cubicRegionBoundaryEdgesWithinBox_iff]
  refine ⟨heBox, ?_⟩
  rw [← e.1.out_eq] at hxe hye
  rw [Sym2.mem_iff] at hxe hye
  rcases hxe with hxe | hxe <;> rcases hye with hye | hye
  · subst x; subst y; exact (hyR hxR).elim
  · subst x; subst y; exact Or.inl ⟨hxR, hyR⟩
  · subst x; subst y; exact Or.inr ⟨hxR, hyR⟩
  · subst x; subst y; exact (hyR hxR).elim

theorem cubicRegionBoundaryOutsideEndpoint_eq_of_mem_of_not_mem
    {d n : ℕ} {R : Finset (Cubic d)} {e : CubicEdge d} {y : Cubic d}
    (he : e ∈ cubicRegionBoundaryEdgesWithinBox d R n)
    (hye : y ∈ (e : Sym2 (Cubic d))) (hyR : y ∉ R) :
    cubicRegionBoundaryOutsideEndpoint R e = y := by
  classical
  rw [← e.1.out_eq] at hye
  rw [Sym2.mem_iff] at hye
  rcases hye with rfl | rfl
  · have hnot : e.1.out.1 ∉ R := hyR
    simp [cubicRegionBoundaryOutsideEndpoint, hnot]
  · rcases (mem_cubicRegionBoundaryEdgesWithinBox_iff.mp he).2 with h | h
    · simp [cubicRegionBoundaryOutsideEndpoint, h.1]
    · exact (hyR h.1).elim

theorem disjoint_cubicRegionExteriorEdgesWithinBox_boundary
    (d : ℕ) (R : Finset (Cubic d)) (n : ℕ) :
    Disjoint (cubicRegionExteriorEdgesWithinBox d R n : Set (CubicEdge d))
      (cubicRegionBoundaryEdgesWithinBox d R n : Set (CubicEdge d)) := by
  rw [Set.disjoint_left]
  intro e heExterior heBoundary
  have hinside := cubicRegionBoundaryInsideEndpoint_mem heBoundary
  have hinsideEdge : cubicRegionBoundaryInsideEndpoint R e ∈ (e : Sym2 (Cubic d)) := by
    rw [← cubicRegionBoundaryEndpoints_edge heBoundary]
    simp
  exact (mem_cubicRegionExteriorEdgesWithinBox_iff.mp heExterior).2 _ hinsideEdge hinside

theorem walkIsOpen_diff_regionBoundary_of_exterior
    {d n : ℕ} {R : Finset (Cubic d)} {omega : EdgeConfiguration d}
    {x y : Cubic d} {w : (cubicGraph d).Walk x y}
    (hopen : walkIsOpen omega w)
    (hsub : walkEdgeFinset w ⊆ cubicRegionExteriorEdgesWithinBox d R n) :
    walkIsOpen (omega \ (cubicRegionBoundaryEdgesWithinBox d R n : Set (CubicEdge d))) w := by
  intro e he
  refine ⟨hopen e he, ?_⟩
  intro heBoundary
  let f : CubicEdge d := ⟨e, w.edges_subset_edgeSet he⟩
  have heExterior : f ∈
      cubicRegionExteriorEdgesWithinBox d R n :=
    hsub ((mem_walkEdgeFinset_iff w f).mpr he)
  exact Set.disjoint_left.mp
    (disjoint_cubicRegionExteriorEdgesWithinBox_boundary d R n)
      heExterior heBoundary

/-- Coordinates used only by the boundary target and its seed, excluding all edges of the
exploratory box. -/
noncomputable def seededBoundaryTargetSupport
    (d : ℕ) (i : Fin d) (m n : ℕ) : Finset (CubicEdge d) :=
  seedConnectionSupport d i m n \ cubicBoxEdges d cubicOrigin n

/-- Every vertex of the layered target lies strictly beyond the positive `i`-face. -/
theorem seededBoundaryLayerRegion_coord_gt
    {d m n : ℕ} {i : Fin d} {z : Cubic d}
    (hz : z ∈ seededBoundaryLayerRegion d i m n) :
    (n : ℤ) < z i := by
  rcases hz with ⟨r, hr1, _hr2, y, hyQuadrant, rfl⟩
  have hyFace := mem_cubicBoxFace.mp
    (mem_seededBoundaryQuadrant_iff.mp hyQuadrant).1
  have hyi : y i = (n : ℤ) := by
    simpa [cubicOrigin] using hyFace.1
  rw [cubicTranslateAlongCoordinate_same, hyi]
  omega

/-- Transverse coordinates of the layered target never leave the original radius-`n` box.
The target extends beyond the selected face only in its axial coordinate. -/
theorem seededBoundaryLayerRegion_transverse_bounds
    {d m n : ℕ} {i j : Fin d} (hji : j ≠ i) {z : Cubic d}
    (hz : z ∈ seededBoundaryLayerRegion d i m n) :
    -(n : ℤ) ≤ z j ∧ z j ≤ (n : ℤ) := by
  rcases hz with ⟨r, _hr1, _hr2, y, hyQuadrant, rfl⟩
  rw [cubicTranslateAlongCoordinate_of_ne y hji r]
  have hyFace := mem_cubicBoxFace.mp
    (mem_seededBoundaryQuadrant_iff.mp hyQuadrant).1
  have hjBounds := hyFace.2 j hji
  simpa [cubicOrigin] using hjBounds

/-- Every endpoint read by the exact seeded-connection support stays in the radius-`n`
transverse strip.  This anisotropic bound is sharper than the axial wide-box bound and is the
geometric input for separating different root directions. -/
theorem endpoint_mem_seedConnectionSupport_transverse_bounds
    {d m n : ℕ} {i j : Fin d} (hji : j ≠ i)
    {e : CubicEdge d} (he : e ∈ seedConnectionSupport d i m n)
    {z : Cubic d} (hze : z ∈ (e : Sym2 (Cubic d))) :
    -(n : ℤ) ≤ z j ∧ z j ≤ (n : ℤ) := by
  rw [seedConnectionSupport] at he
  simp only [Finset.mem_union] at he
  rcases he with (heBox | heStep) | heSeed
  · have hzBox := endpoint_mem_cubicMetricBox_of_edge_mem_cubicBoxEdges heBox hze
    simpa [mem_cubicMetricBox, cubicOrigin] using (mem_cubicMetricBox.mp hzBox j)
  · obtain ⟨y, hyQuadrant, rfl⟩ := Finset.mem_image.mp heStep
    change z ∈ s(y, cubicStepFrom y (i, true)) at hze
    rw [Sym2.mem_iff] at hze
    have hyFace := mem_cubicBoxFace.mp
      (mem_seededBoundaryQuadrant_iff.mp hyQuadrant).1
    have hjBounds := hyFace.2 j hji
    rcases hze with rfl | rfl
    · simpa [cubicOrigin] using hjBounds
    · simpa [cubicStepFrom, hji, cubicOrigin] using hjBounds
  · rw [Finset.mem_biUnion] at heSeed
    obtain ⟨c, hcAdmissible, heBox⟩ := heSeed
    have hzBox := endpoint_mem_cubicMetricBox_of_edge_mem_cubicBoxEdges heBox hze
    have hzLayer :=
      (mem_seededBoundaryAdmissibleCenters_iff.mp hcAdmissible).2 z hzBox
    exact seededBoundaryLayerRegion_transverse_bounds hji hzLayer

/-- The tightened target dependency set has no junk vertices behind its selected face: every
endpoint has `i`-coordinate at least `n`.  This is false for the former coarse support that
included every seed center in an ambient box. -/
theorem endpoint_mem_seededBoundaryTargetSupport_coord_ge
    {d m n : ℕ} {i : Fin d} {e : CubicEdge d} {z : Cubic d}
    (he : e ∈ seededBoundaryTargetSupport d i m n)
    (hze : z ∈ (e : Sym2 (Cubic d))) :
    (n : ℤ) ≤ z i := by
  obtain ⟨heSupport, heNotBox⟩ := Finset.mem_sdiff.mp he
  rw [seedConnectionSupport] at heSupport
  simp only [Finset.mem_union] at heSupport
  rcases heSupport with (heBox | heStep) | heSeed
  · exact (heNotBox heBox).elim
  · obtain ⟨y, hyQuadrant, rfl⟩ := Finset.mem_image.mp heStep
    change z ∈ s(y, cubicStepFrom y (i, true)) at hze
    rw [Sym2.mem_iff] at hze
    have hyFace := mem_cubicBoxFace.mp
      (mem_seededBoundaryQuadrant_iff.mp hyQuadrant).1
    have hyi : y i = (n : ℤ) := by
      simpa [cubicOrigin] using hyFace.1
    rcases hze with rfl | rfl
    · exact hyi.ge
    · simp [cubicStepFrom, cubicDirectionIncrement, hyi]
  · rw [Finset.mem_biUnion] at heSeed
    obtain ⟨c, hcAdmissible, heBox⟩ := heSeed
    have hzBox := endpoint_mem_cubicMetricBox_of_edge_mem_cubicBoxEdges heBox hze
    have hzLayer :=
      (mem_seededBoundaryAdmissibleCenters_iff.mp hcAdmissible).2 z hzBox
    exact (seededBoundaryLayerRegion_coord_gt hzLayer).le

/-- Exact finite support of one restart after the explored region `R` is frozen: its boundary,
the as-yet-unexplored exterior box edges, and the target-seed coordinates beyond the box.  In
particular, already revealed edges strictly inside `R` are not charged again. -/
noncomputable def restartEventSupport
    (d : ℕ) (i : Fin d) (m n : ℕ) (R : Finset (Cubic d)) :
    Finset (CubicEdge d) :=
  cubicRegionBoundaryEdgesWithinBox d R n ∪
    cubicRegionExteriorEdgesWithinBox d R n ∪
      seededBoundaryTargetSupport d i m n

/-- A restart's exact finite support is unchanged when its region is cropped to the box in
which the restart is performed. -/
@[simp]
theorem restartEventSupport_inter_cubicMetricBox
    (d : ℕ) (i : Fin d) (m n : ℕ) (R : Finset (Cubic d)) :
    restartEventSupport d i m n (R ∩ cubicMetricBox d cubicOrigin n) =
      restartEventSupport d i m n R := by
  simp [restartEventSupport]

theorem boundary_subset_restartEventSupport
    (d : ℕ) (i : Fin d) (m n : ℕ) (R : Finset (Cubic d)) :
    cubicRegionBoundaryEdgesWithinBox d R n ⊆ restartEventSupport d i m n R := by
  exact Finset.subset_union_left.trans Finset.subset_union_left

theorem exterior_subset_restartEventSupport
    (d : ℕ) (i : Fin d) (m n : ℕ) (R : Finset (Cubic d)) :
    cubicRegionExteriorEdgesWithinBox d R n ⊆ restartEventSupport d i m n R := by
  exact Finset.subset_union_right.trans Finset.subset_union_left

theorem target_subset_restartEventSupport
    (d : ℕ) (i : Fin d) (m n : ℕ) (R : Finset (Cubic d)) :
    seededBoundaryTargetSupport d i m n ⊆ restartEventSupport d i m n R :=
  Finset.subset_union_right

/-- Every coordinate read by a restart belongs to the exact seeded-connection dependency set. -/
theorem restartEventSupport_subset_seedConnectionSupport
    (d : ℕ) (i : Fin d) (m n : ℕ) (R : Finset (Cubic d)) :
    restartEventSupport d i m n R ⊆ seedConnectionSupport d i m n := by
  intro e he
  simp only [restartEventSupport, Finset.mem_union] at he
  rcases he with (heBoundary | heExterior) | heTarget
  · rw [seedConnectionSupport]
    exact Finset.mem_union_left _ (Finset.mem_union_left _
      (mem_cubicRegionBoundaryEdgesWithinBox_iff.mp heBoundary).1)
  · rw [seedConnectionSupport]
    exact Finset.mem_union_left _ (Finset.mem_union_left _
      (mem_cubicRegionExteriorEdgesWithinBox_iff.mp heExterior).1)
  · exact (Finset.mem_sdiff.mp heTarget).1

/-- Consequently a restart reads no edge outside the radius `n + 2m + 1` reference box. -/
theorem restartEventSupport_subset_cubicBoxEdges_wide
    (d : ℕ) (i : Fin d) (m n : ℕ) (R : Finset (Cubic d)) :
    restartEventSupport d i m n R ⊆
      cubicBoxEdges d cubicOrigin (n + 2 * m + 1) :=
  (restartEventSupport_subset_seedConnectionSupport d i m n R).trans
    (seedConnectionSupport_subset_cubicBoxEdges_wide d i m n)

/-- Transverse endpoint bound inherited by every exact restart support. -/
theorem endpoint_mem_restartEventSupport_transverse_bounds
    {d m n : ℕ} {i j : Fin d} (hji : j ≠ i)
    {R : Finset (Cubic d)} {e : CubicEdge d}
    (he : e ∈ restartEventSupport d i m n R)
    {z : Cubic d} (hze : z ∈ (e : Sym2 (Cubic d))) :
    -(n : ℤ) ≤ z j ∧ z j ≤ (n : ℤ) :=
  endpoint_mem_seedConnectionSupport_transverse_bounds hji
    (restartEventSupport_subset_seedConnectionSupport d i m n R he) hze

/-- Finite version of the random target set `K(m,n)`. -/
noncomputable def seededBoundaryPointFinset
    (d : ℕ) (i : Fin d) (m n : ℕ) (omega : EdgeConfiguration d) : Finset (Cubic d) := by
  classical
  exact (seededBoundaryQuadrant d i n).filter fun y =>
    IsSeededBoundaryPoint d i m n omega y

@[simp]
theorem mem_seededBoundaryPointFinset_iff
    {d m n : ℕ} {i : Fin d} {omega : EdgeConfiguration d} {y : Cubic d} :
    y ∈ seededBoundaryPointFinset d i m n omega ↔
      IsSeededBoundaryPoint d i m n omega y := by
  classical
  simp only [seededBoundaryPointFinset, Finset.mem_filter]
  constructor
  · exact And.right
  · intro hy
    exact ⟨hy.1, hy⟩

theorem cubicBoxEdges_subset_seedConnectionSupport
    (d : ℕ) (i : Fin d) (m n : ℕ) :
    cubicBoxEdges d cubicOrigin n ⊆ seedConnectionSupport d i m n := by
  intro e he
  rw [seedConnectionSupport]
  exact Finset.mem_union_left _ (Finset.mem_union_left _ he)

theorem cubicRegionBoundaryEdgesWithinBox_subset_seedConnectionSupport
    (d : ℕ) (i : Fin d) (m n : ℕ) (R : Finset (Cubic d)) :
    cubicRegionBoundaryEdgesWithinBox d R n ⊆ seedConnectionSupport d i m n := by
  intro e he
  exact cubicBoxEdges_subset_seedConnectionSupport d i m n
    (mem_cubicRegionBoundaryEdgesWithinBox_iff.mp he).1

/-- The target predicate `y ∈ K(m,n)` is decided by the same finite support as the complete
seeded connection event. -/
theorem isSeededBoundaryPoint_congr_of_eqOn_seedConnectionSupport
    {d m n : ℕ} {i : Fin d} {omega eta : EdgeConfiguration d}
    (hagree : ∀ e ∈ seedConnectionSupport d i m n, (e ∈ omega ↔ e ∈ eta))
    (y : Cubic d) :
    IsSeededBoundaryPoint d i m n omega y ↔
      IsSeededBoundaryPoint d i m n eta y := by
  classical
  constructor
  · rintro ⟨hyQ, hyedge, c, hyc, hcLayer, hcSeed⟩
    have hedgeSupport : cubicStepEdge y (i, true) ∈ seedConnectionSupport d i m n := by
      rw [seedConnectionSupport]
      apply Finset.mem_union_left
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨y, hyQ, rfl⟩
    have hcCenter : c ∈ seededBoundaryAdmissibleCenters d i m n :=
      seedCenter_mem_seededBoundaryAdmissibleCenters hyQ hyc hcLayer
    have hcSeed' : eta ∈ cubicSeedEvent d c m := by
      intro e he
      apply (hagree e ?_).mp (hcSeed he)
      rw [seedConnectionSupport]
      apply Finset.mem_union_right
      rw [Finset.mem_biUnion]
      exact ⟨c, hcCenter, he⟩
    exact ⟨hyQ, (hagree _ hedgeSupport).mp hyedge, c, hyc, hcLayer, hcSeed'⟩
  · rintro ⟨hyQ, hyedge, c, hyc, hcLayer, hcSeed⟩
    have hedgeSupport : cubicStepEdge y (i, true) ∈ seedConnectionSupport d i m n := by
      rw [seedConnectionSupport]
      apply Finset.mem_union_left
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨y, hyQ, rfl⟩
    have hcCenter : c ∈ seededBoundaryAdmissibleCenters d i m n :=
      seedCenter_mem_seededBoundaryAdmissibleCenters hyQ hyc hcLayer
    have hcSeed' : omega ∈ cubicSeedEvent d c m := by
      intro e he
      apply (hagree e ?_).mpr (hcSeed he)
      rw [seedConnectionSupport]
      apply Finset.mem_union_right
      rw [Finset.mem_biUnion]
      exact ⟨c, hcCenter, he⟩
    exact ⟨hyQ, (hagree _ hedgeSupport).mpr hyedge, c, hyc, hcLayer, hcSeed'⟩

theorem seededBoundaryPointFinset_congr_of_eqOn_seedConnectionSupport
    {d m n : ℕ} {i : Fin d} {omega eta : EdgeConfiguration d}
    (hagree : ∀ e ∈ seedConnectionSupport d i m n, (e ∈ omega ↔ e ∈ eta)) :
    seededBoundaryPointFinset d i m n omega =
      seededBoundaryPointFinset d i m n eta := by
  ext y
  simp only [mem_seededBoundaryPointFinset_iff]
  exact isSeededBoundaryPoint_congr_of_eqOn_seedConnectionSupport hagree y

theorem seededBoundaryLayerRegion_disjoint_innerBox
    {d m n : ℕ} {i : Fin d} {z : Cubic d}
    (hz : z ∈ seededBoundaryLayerRegion d i m n) :
    z ∉ cubicMetricBox d cubicOrigin n := by
  rintro hzBox
  rcases hz with ⟨r, hr1, _hr2, y, hyQ, rfl⟩
  have hyFace := mem_cubicBoxFace.mp (mem_seededBoundaryQuadrant_iff.mp hyQ).1
  have hyi : y i = (n : ℤ) := by simpa [cubicOrigin] using hyFace.1
  have hzCoord := (mem_cubicMetricBox.mp hzBox) i
  rw [cubicTranslateAlongCoordinate_same, hyi] at hzCoord
  simp [cubicOrigin] at hzCoord
  omega

theorem cubicStepEdge_mem_seededBoundaryTargetSupport
    {d m n : ℕ} {i : Fin d} {y : Cubic d}
    (hy : y ∈ seededBoundaryQuadrant d i n) :
    cubicStepEdge y (i, true) ∈ seededBoundaryTargetSupport d i m n := by
  rw [seededBoundaryTargetSupport, Finset.mem_sdiff]
  refine ⟨?_, ?_⟩
  · rw [seedConnectionSupport]
    apply Finset.mem_union_left
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨y, hy, rfl⟩
  · intro heBox
    have hstepMem : cubicStepFrom y (i, true) ∈
        (cubicStepEdge y (i, true) : Sym2 (Cubic d)) := by
      simp [cubicStepEdge]
    have hstepBox := endpoint_mem_cubicMetricBox_of_edge_mem_cubicBoxEdges heBox hstepMem
    have hyFace := mem_cubicBoxFace.mp (mem_seededBoundaryQuadrant_iff.mp hy).1
    have hyi : y i = (n : ℤ) := by simpa [cubicOrigin] using hyFace.1
    have hcoord := (mem_cubicMetricBox.mp hstepBox) i
    rw [show cubicStepFrom y (i, true) i = y i + 1 by
      simp [cubicStepFrom, cubicDirectionIncrement], hyi] at hcoord
    simp [cubicOrigin] at hcoord

theorem seedEdge_mem_seededBoundaryTargetSupport
    {d m n : ℕ} {i : Fin d} {y c : Cubic d} {e : CubicEdge d}
    (hy : y ∈ seededBoundaryQuadrant d i n)
    (hyc : cubicStepFrom y (i, true) ∈ cubicMetricBox d c m)
    (hcLayer : SeedBoxWithinBoundaryLayer d i m n c)
    (heSeed : e ∈ cubicBoxEdges d c m) :
    e ∈ seededBoundaryTargetSupport d i m n := by
  rw [seededBoundaryTargetSupport, Finset.mem_sdiff]
  refine ⟨?_, ?_⟩
  · rw [seedConnectionSupport]
    apply Finset.mem_union_right
    rw [Finset.mem_biUnion]
    exact ⟨c,
      seedCenter_mem_seededBoundaryAdmissibleCenters hy hyc hcLayer, heSeed⟩
  · intro heBox
    have hzSeed := endpoint_mem_cubicMetricBox_of_edge_mem_cubicBoxEdges heSeed
      (Sym2.out_fst_mem e.1)
    have hzLayer := hcLayer e.1.out.1 hzSeed
    exact seededBoundaryLayerRegion_disjoint_innerBox hzLayer
      (endpoint_mem_cubicMetricBox_of_edge_mem_cubicBoxEdges heBox
        (Sym2.out_fst_mem e.1))

/-- The seeded target itself uses only the portion of `seedConnectionSupport` beyond `B(n)`. -/
theorem isSeededBoundaryPoint_congr_of_eqOn_targetSupport
    {d m n : ℕ} {i : Fin d} {omega eta : EdgeConfiguration d}
    (hagree : ∀ e ∈ seededBoundaryTargetSupport d i m n, (e ∈ omega ↔ e ∈ eta))
    (y : Cubic d) :
    IsSeededBoundaryPoint d i m n omega y ↔
      IsSeededBoundaryPoint d i m n eta y := by
  constructor
  · rintro ⟨hyQ, hyedge, c, hyc, hcLayer, hcSeed⟩
    refine ⟨hyQ, (hagree _ (cubicStepEdge_mem_seededBoundaryTargetSupport hyQ)).mp hyedge,
      c, hyc, hcLayer, ?_⟩
    intro e heSeed
    exact (hagree e
      (seedEdge_mem_seededBoundaryTargetSupport hyQ hyc hcLayer heSeed)).mp (hcSeed heSeed)
  · rintro ⟨hyQ, hyedge, c, hyc, hcLayer, hcSeed⟩
    refine ⟨hyQ, (hagree _ (cubicStepEdge_mem_seededBoundaryTargetSupport hyQ)).mpr hyedge,
      c, hyc, hcLayer, ?_⟩
    intro e heSeed
    exact (hagree e
      (seedEdge_mem_seededBoundaryTargetSupport hyQ hyc hcLayer heSeed)).mpr (hcSeed heSeed)

theorem seededBoundaryPointFinset_congr_of_eqOn_targetSupport
    {d m n : ℕ} {i : Fin d} {omega eta : EdgeConfiguration d}
    (hagree : ∀ e ∈ seededBoundaryTargetSupport d i m n, (e ∈ omega ↔ e ∈ eta)) :
    seededBoundaryPointFinset d i m n omega =
      seededBoundaryPointFinset d i m n eta := by
  ext y
  simp only [mem_seededBoundaryPointFinset_iff]
  exact isSeededBoundaryPoint_congr_of_eqOn_targetSupport hagree y

theorem IsSeededBoundaryPoint.diff_innerBoxEdges
    {d m n : ℕ} {i : Fin d} {omega : EdgeConfiguration d} {y : Cubic d}
    (hy : IsSeededBoundaryPoint d i m n omega y)
    (E : Finset (CubicEdge d)) (hE : E ⊆ cubicBoxEdges d cubicOrigin n) :
    IsSeededBoundaryPoint d i m n (omega \ (E : Set (CubicEdge d))) y := by
  rcases hy with ⟨hyQ, hyEdge, c, hyc, hcLayer, hcSeed⟩
  refine ⟨hyQ, ⟨hyEdge, ?_⟩, c, hyc, hcLayer, ?_⟩
  · intro heE
    have heBox := hE heE
    have hstepMem : cubicStepFrom y (i, true) ∈
        (cubicStepEdge y (i, true) : Sym2 (Cubic d)) := by
      simp [cubicStepEdge]
    have hstepBox := endpoint_mem_cubicMetricBox_of_edge_mem_cubicBoxEdges heBox hstepMem
    have hyFace := mem_cubicBoxFace.mp (mem_seededBoundaryQuadrant_iff.mp hyQ).1
    have hyi : y i = (n : ℤ) := by simpa [cubicOrigin] using hyFace.1
    have hcoord := (mem_cubicMetricBox.mp hstepBox) i
    rw [show cubicStepFrom y (i, true) i = y i + 1 by
      simp [cubicStepFrom, cubicDirectionIncrement], hyi] at hcoord
    simp [cubicOrigin] at hcoord
  · intro e heSeed
    refine ⟨hcSeed heSeed, ?_⟩
    intro heE
    have heBox := hE heE
    have hzSeed := endpoint_mem_cubicMetricBox_of_edge_mem_cubicBoxEdges heSeed
      (Sym2.out_fst_mem e.1)
    have hzLayer := hcLayer e.1.out.1 hzSeed
    exact seededBoundaryLayerRegion_disjoint_innerBox hzLayer
      (endpoint_mem_cubicMetricBox_of_edge_mem_cubicBoxEdges heBox
        (Sym2.out_fst_mem e.1))

/-- Boundary edges whose outside endpoint is joined to the target `K` without using an edge
incident to `R`.  This is Grimmett's `U(K)`. -/
noncomputable def regionAvailableExitEdges
    (d : ℕ) (R : Finset (Cubic d)) (n : ℕ)
    (K : Finset (Cubic d)) (omega : EdgeConfiguration d) : Finset (CubicEdge d) := by
  classical
  exact (cubicRegionBoundaryEdgesWithinBox d R n).filter fun e =>
    ∃ y ∈ K, omega ∈ connectionEventIn d (cubicRegionExteriorEdgesWithinBox d R n)
      (cubicRegionBoundaryOutsideEndpoint R e) y

theorem regionAvailableExitEdges_subset_boundary
    (d : ℕ) (R : Finset (Cubic d)) (n : ℕ)
    (K : Finset (Cubic d)) (omega : EdgeConfiguration d) :
    regionAvailableExitEdges d R n K omega ⊆
      cubicRegionBoundaryEdgesWithinBox d R n := by
  classical
  exact Finset.filter_subset _ _

@[simp]
theorem mem_regionAvailableExitEdges_iff
    {d n : ℕ} {R : Finset (Cubic d)} {K : Finset (Cubic d)}
    {omega : EdgeConfiguration d} {e : CubicEdge d} :
    e ∈ regionAvailableExitEdges d R n K omega ↔
      e ∈ cubicRegionBoundaryEdgesWithinBox d R n ∧
        ∃ y ∈ K, omega ∈ connectionEventIn d (cubicRegionExteriorEdgesWithinBox d R n)
          (cubicRegionBoundaryOutsideEndpoint R e) y := by
  classical
  simp [regionAvailableExitEdges]

/-- Some vertex of `R` is joined inside `B(n)` to the finite target `K`. -/
def regionConnectionToFiniteTargetEvent
    (d : ℕ) (R : Finset (Cubic d)) (n : ℕ) (K : Finset (Cubic d)) :
    Set (EdgeConfiguration d) :=
  {omega | ∃ x ∈ R, ∃ y ∈ K,
    omega ∈ connectionEventIn d (cubicBoxEdges d cubicOrigin n) x y}

/-- Last-exit decomposition: a box-confined connection from `R` to a target disjoint from `R`
uses an open boundary edge which is available in Grimmett's sense. -/
theorem mem_regionConnectionToFiniteTargetEvent_iff_exists_open_availableExit
    {d n : ℕ} {R K : Finset (Cubic d)} {omega : EdgeConfiguration d}
    (hKR : Disjoint K R) :
    omega ∈ regionConnectionToFiniteTargetEvent d R n K ↔
      ∃ e ∈ regionAvailableExitEdges d R n K omega, e ∈ omega := by
  classical
  constructor
  · rintro ⟨x, hxR, y, hyK, w, hwOpen, hwBox⟩
    have hyNotR : y ∉ R := fun hyR => Finset.disjoint_left.mp hKR hyK hyR
    obtain ⟨z, hzR, q, hqSub, hqOutside⟩ :=
      exists_isSubwalk_suffix_from_last_region w
        ⟨x, w.start_mem_support, hxR⟩ hyNotR
    have hqOpen : walkIsOpen omega q := walkIsOpen_of_isSubwalk hwOpen hqSub
    have hqBox : walkEdgeFinset q ⊆ cubicBoxEdges d cubicOrigin n := by
      intro e he
      apply hwBox
      rw [mem_walkEdgeFinset_iff] at he ⊢
      exact hqSub.edges_subset he
    cases q with
    | nil => exact (hyNotR hzR).elim
    | @cons z v _ hzv p =>
        let e : CubicEdge d := ⟨s(z, v), (SimpleGraph.mem_edgeSet _).mpr hzv⟩
        have hvNotR : v ∉ R := by
          apply hqOutside v
          simp
        have heBox : e ∈ cubicBoxEdges d cubicOrigin n := by
          apply hqBox
          rw [mem_walkEdgeFinset_iff]
          simp [e]
        have heBoundary : e ∈ cubicRegionBoundaryEdgesWithinBox d R n := by
          apply mem_cubicRegionBoundaryEdgesWithinBox_of_endpoints heBox
            (x := z) (y := v) (by simp [e]) (by simp [e]) hzR hvNotR
        have hout : cubicRegionBoundaryOutsideEndpoint R e = v := by
          exact cubicRegionBoundaryOutsideEndpoint_eq_of_mem_of_not_mem heBoundary
            (by simp [e]) hvNotR
        have hpExterior : walkEdgeFinset p ⊆ cubicRegionExteriorEdgesWithinBox d R n := by
          intro f hf
          rw [mem_cubicRegionExteriorEdgesWithinBox_iff]
          refine ⟨?_, ?_⟩
          · apply hqBox
            rw [mem_walkEdgeFinset_iff] at hf ⊢
            simp only [SimpleGraph.Walk.edges_cons, List.mem_cons]
            exact Or.inr hf
          · intro a ha
            apply hqOutside a
            have haSupport : a ∈ p.support := by
              exact SimpleGraph.Walk.mem_support_of_mem_edges
                ((mem_walkEdgeFinset_iff p f).mp hf) ha
            simpa using haSupport
        have hpOpen : walkIsOpen omega p := by
          intro f hf
          exact hqOpen f (by simp [SimpleGraph.Walk.edges_cons, hf])
        refine ⟨e, ?_, ?_⟩
        · rw [mem_regionAvailableExitEdges_iff]
          exact ⟨heBoundary, y, hyK, by simpa [hout] using
            (show omega ∈ connectionEventIn d (cubicRegionExteriorEdgesWithinBox d R n) v y
              from ⟨p, hpOpen, hpExterior⟩)⟩
        · exact hqOpen _ (by simp [SimpleGraph.Walk.edges_cons])
  · rintro ⟨e, heU, heOpen⟩
    rw [mem_regionAvailableExitEdges_iff] at heU
    rcases heU with ⟨heBoundary, y, hyK, w, hwOpen, hwExterior⟩
    let x := cubicRegionBoundaryInsideEndpoint R e
    let z := cubicRegionBoundaryOutsideEndpoint R e
    have hxR : x ∈ R := cubicRegionBoundaryInsideEndpoint_mem heBoundary
    have hadj : (cubicGraph d).Adj x z := by
      rw [← SimpleGraph.mem_edgeSet]
      rw [cubicRegionBoundaryEndpoints_edge heBoundary]
      exact e.2
    let q : (cubicGraph d).Walk x y := SimpleGraph.Walk.cons hadj w
    have hqOpen : walkIsOpen omega q := by
      intro f hf
      simp only [q, SimpleGraph.Walk.edges_cons, List.mem_cons] at hf
      rcases hf with hf | hf
      · have hfe : f = (e : Sym2 (Cubic d)) := by
          exact hf.trans (cubicRegionBoundaryEndpoints_edge heBoundary)
        simpa [hfe] using heOpen
      · exact hwOpen f hf
    have hqBox : walkEdgeFinset q ⊆ cubicBoxEdges d cubicOrigin n := by
      intro f hf
      rw [mem_walkEdgeFinset_iff] at hf
      simp only [q, SimpleGraph.Walk.edges_cons, List.mem_cons] at hf
      rcases hf with hf | hf
      · have hfe : f = e := by
          apply Subtype.ext
          exact hf.trans (cubicRegionBoundaryEndpoints_edge heBoundary)
        simpa [hfe] using (mem_cubicRegionBoundaryEdgesWithinBox_iff.mp heBoundary).1
      · exact Finset.sdiff_subset (hwExterior ((mem_walkEdgeFinset_iff w f).mpr hf))
    exact ⟨x, hxR, y, hyK, q, hqOpen, hqBox⟩

/-- Available exits to the actual seeded target `K(m,n)`. -/
noncomputable def seededRegionAvailableExitEdges
    (d : ℕ) (i : Fin d) (m n : ℕ) (R : Finset (Cubic d))
    (omega : EdgeConfiguration d) : Finset (CubicEdge d) :=
  regionAvailableExitEdges d R n (seededBoundaryPointFinset d i m n omega) omega

/-- Available exits are a box-local observable: vertices of `R` outside `B(n)` cannot affect
the boundary edge, its outside endpoint, or an exterior path confined to box edges. -/
@[simp]
theorem seededRegionAvailableExitEdges_inter_cubicMetricBox
    (d : ℕ) (i : Fin d) (m n : ℕ) (R : Finset (Cubic d))
    (omega : EdgeConfiguration d) :
    seededRegionAvailableExitEdges d i m n
        (R ∩ cubicMetricBox d cubicOrigin n) omega =
      seededRegionAvailableExitEdges d i m n R omega := by
  classical
  ext e
  simp only [seededRegionAvailableExitEdges, mem_regionAvailableExitEdges_iff]
  constructor
  · rintro ⟨heBoundary, y, hyTarget, hconn⟩
    have heBox : e ∈ cubicBoxEdges d cubicOrigin n :=
      (mem_cubicRegionBoundaryEdgesWithinBox_iff.mp heBoundary).1
    refine ⟨?_, y, hyTarget, ?_⟩
    · simpa using heBoundary
    · simpa only [cubicRegionExteriorEdgesWithinBox_inter_cubicMetricBox,
        cubicRegionBoundaryOutsideEndpoint_inter_cubicMetricBox R heBox] using hconn
  · rintro ⟨heBoundary, y, hyTarget, hconn⟩
    have heBox : e ∈ cubicBoxEdges d cubicOrigin n :=
      (mem_cubicRegionBoundaryEdgesWithinBox_iff.mp heBoundary).1
    refine ⟨?_, y, hyTarget, ?_⟩
    · simpa using heBoundary
    · simpa only [cubicRegionExteriorEdgesWithinBox_inter_cubicMetricBox,
        cubicRegionBoundaryOutsideEndpoint_inter_cubicMetricBox R heBox] using hconn

theorem seededRegionAvailableExitEdges_subset_boundary
    (d : ℕ) (i : Fin d) (m n : ℕ) (R : Finset (Cubic d))
    (omega : EdgeConfiguration d) :
    seededRegionAvailableExitEdges d i m n R omega ⊆
      cubicRegionBoundaryEdgesWithinBox d R n :=
  regionAvailableExitEdges_subset_boundary d R n _ omega

/-- The complete finite available-exit set is determined by `seedConnectionSupport`: box edges
decide the exterior paths and the remaining support coordinates decide the target seeds. -/
theorem seededRegionAvailableExitEdges_congr_of_eqOn_seedConnectionSupport
    {d m n : ℕ} {i : Fin d} {R : Finset (Cubic d)}
    {omega eta : EdgeConfiguration d}
    (hagree : ∀ e ∈ seedConnectionSupport d i m n, (e ∈ omega ↔ e ∈ eta)) :
    seededRegionAvailableExitEdges d i m n R omega =
      seededRegionAvailableExitEdges d i m n R eta := by
  classical
  have htarget := seededBoundaryPointFinset_congr_of_eqOn_seedConnectionSupport hagree
  ext e
  simp only [seededRegionAvailableExitEdges, mem_regionAvailableExitEdges_iff]
  constructor
  · rintro ⟨heBoundary, y, hyTarget, hconn⟩
    refine ⟨heBoundary, y, ?_, ?_⟩
    · simpa [htarget] using hyTarget
    · exact (dependsOn_connectionEventIn d
        (cubicRegionExteriorEdgesWithinBox d R n)
        (cubicRegionBoundaryOutsideEndpoint R e) y
        (fun f hf ↦ hagree f <|
          cubicBoxEdges_subset_seedConnectionSupport d i m n
            (Finset.sdiff_subset hf))).mp hconn
  · rintro ⟨heBoundary, y, hyTarget, hconn⟩
    refine ⟨heBoundary, y, ?_, ?_⟩
    · simpa [htarget] using hyTarget
    · exact (dependsOn_connectionEventIn d
        (cubicRegionExteriorEdgesWithinBox d R n)
        (cubicRegionBoundaryOutsideEndpoint R e) y
        (fun f hf ↦ hagree f <|
          cubicBoxEdges_subset_seedConnectionSupport d i m n
            (Finset.sdiff_subset hf))).mpr hconn

theorem seededRegionAvailableExitEdges_congr_of_eqOn_restartEventSupport
    {d m n : ℕ} {i : Fin d} {R : Finset (Cubic d)}
    {omega eta : EdgeConfiguration d}
    (hagree : ∀ e ∈ restartEventSupport d i m n R, (e ∈ omega ↔ e ∈ eta)) :
    seededRegionAvailableExitEdges d i m n R omega =
      seededRegionAvailableExitEdges d i m n R eta := by
  classical
  have htarget : seededBoundaryPointFinset d i m n omega =
      seededBoundaryPointFinset d i m n eta :=
    seededBoundaryPointFinset_congr_of_eqOn_targetSupport fun e he =>
      hagree e (target_subset_restartEventSupport d i m n R he)
  ext e
  simp only [seededRegionAvailableExitEdges, mem_regionAvailableExitEdges_iff]
  constructor
  · rintro ⟨heBoundary, y, hyTarget, hconn⟩
    refine ⟨heBoundary, y, ?_, ?_⟩
    · simpa [htarget] using hyTarget
    · exact (dependsOn_connectionEventIn d
        (cubicRegionExteriorEdgesWithinBox d R n)
        (cubicRegionBoundaryOutsideEndpoint R e) y
        (fun f hf => hagree f
          (exterior_subset_restartEventSupport d i m n R hf))).mp hconn
  · rintro ⟨heBoundary, y, hyTarget, hconn⟩
    refine ⟨heBoundary, y, ?_, ?_⟩
    · simpa [htarget] using hyTarget
    · exact (dependsOn_connectionEventIn d
        (cubicRegionExteriorEdgesWithinBox d R n)
        (cubicRegionBoundaryOutsideEndpoint R e) y
        (fun f hf => hagree f
          (exterior_subset_restartEventSupport d i m n R hf))).mpr hconn

theorem measurableSet_mem_seededRegionAvailableExitEdges
    (d : ℕ) (i : Fin d) (m n : ℕ) (R : Finset (Cubic d)) (e : CubicEdge d) :
    MeasurableSet {omega : EdgeConfiguration d |
      e ∈ seededRegionAvailableExitEdges d i m n R omega} := by
  classical
  by_cases he : e ∈ cubicRegionBoundaryEdgesWithinBox d R n
  · have hevent : {omega : EdgeConfiguration d |
        e ∈ seededRegionAvailableExitEdges d i m n R omega} =
        ⋃ y ∈ seededBoundaryQuadrant d i n,
          {omega | IsSeededBoundaryPoint d i m n omega y} ∩
            connectionEventIn d (cubicRegionExteriorEdgesWithinBox d R n)
              (cubicRegionBoundaryOutsideEndpoint R e) y := by
      ext omega
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff,
        seededRegionAvailableExitEdges, mem_regionAvailableExitEdges_iff,
        mem_seededBoundaryPointFinset_iff, he, true_and]
      constructor
      · rintro ⟨y, hySeed, hconn⟩
        exact ⟨y, hySeed.1, hySeed, hconn⟩
      · rintro ⟨y, _hyQ, hySeed, hconn⟩
        exact ⟨y, hySeed, hconn⟩
    rw [hevent]
    exact (seededBoundaryQuadrant d i n).measurableSet_biUnion fun y _hy =>
      (measurableSet_isSeededBoundaryPoint d i m n y).inter
        (dependsOn_connectionEventIn d (cubicRegionExteriorEdgesWithinBox d R n)
          (cubicRegionBoundaryOutsideEndpoint R e) y).measurableSet
  · have hevent : {omega : EdgeConfiguration d |
        e ∈ seededRegionAvailableExitEdges d i m n R omega} = ∅ := by
      ext omega
      simp [seededRegionAvailableExitEdges, mem_regionAvailableExitEdges_iff, he]
    rw [hevent]
    exact MeasurableSet.empty

theorem measurableSet_seededRegionAvailableExitEdges_eq
    (d : ℕ) (i : Fin d) (m n : ℕ) (R : Finset (Cubic d))
    (S : Finset (CubicEdge d)) :
    MeasurableSet {omega : EdgeConfiguration d |
      seededRegionAvailableExitEdges d i m n R omega = S} := by
  classical
  let E := cubicRegionBoundaryEdgesWithinBox d R n
  by_cases hSE : S ⊆ E
  · have hevent : {omega : EdgeConfiguration d |
        seededRegionAvailableExitEdges d i m n R omega = S} =
        (⋂ e ∈ S, {omega | e ∈ seededRegionAvailableExitEdges d i m n R omega}) ∩
          ⋂ e ∈ E \ S,
            {omega | e ∈ seededRegionAvailableExitEdges d i m n R omega}ᶜ := by
      ext omega
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter,
        Set.mem_compl_iff, Finset.mem_sdiff]
      constructor
      · intro hEq
        subst S
        exact ⟨fun e he => he, fun e h => h.2⟩
      · rintro ⟨hmem, hnot⟩
        apply Finset.Subset.antisymm
        · intro e heU
          by_contra heS
          exact hnot e ⟨seededRegionAvailableExitEdges_subset_boundary
            d i m n R omega heU, heS⟩ heU
        · exact fun e heS => hmem e heS
    rw [hevent]
    exact (MeasurableSet.biInter S.countable_toSet fun e _he =>
      measurableSet_mem_seededRegionAvailableExitEdges d i m n R e).inter
        (MeasurableSet.biInter (E \ S).countable_toSet fun e _he =>
          (measurableSet_mem_seededRegionAvailableExitEdges d i m n R e).compl)
  · have hevent : {omega : EdgeConfiguration d |
        seededRegionAvailableExitEdges d i m n R omega = S} = ∅ := by
      ext omega
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hEq
      apply hSE
      rw [← hEq]
      exact seededRegionAvailableExitEdges_subset_boundary d i m n R omega
    rw [hevent]
    exact MeasurableSet.empty

/-- The coupling-space version of `U(K(m,n))`, with every region-boundary coordinate cleared
before the available set is computed.  Hence it is genuinely determined off the boundary. -/
noncomputable def restartAvailableExitEdges
    (d : ℕ) (i : Fin d) (m n : ℕ) (R : Finset (Cubic d)) (p : I)
    (X : CubicEdge d → ℝ) : Finset (CubicEdge d) :=
  seededRegionAvailableExitEdges d i m n R
    (clearedThreshold (cubicRegionBoundaryEdgesWithinBox d R n) p X)

/-- The coupling-space available-exit set is unchanged by box-cropping the region. -/
@[simp]
theorem restartAvailableExitEdges_inter_cubicMetricBox
    (d : ℕ) (i : Fin d) (m n : ℕ) (R : Finset (Cubic d)) (p : I)
    (X : CubicEdge d → ℝ) :
    restartAvailableExitEdges d i m n
        (R ∩ cubicMetricBox d cubicOrigin n) p X =
      restartAvailableExitEdges d i m n R p X := by
  simp [restartAvailableExitEdges]

/-- Equality on the finite restart support gives the same off-boundary available-exit set. -/
theorem restartAvailableExitEdges_congr_of_eqOn_seedConnectionSupport
    {d m n : ℕ} {i : Fin d} {R : Finset (Cubic d)} {p : I}
    {X Y : CubicEdge d → ℝ}
    (hXY : ∀ e ∈ seedConnectionSupport d i m n, X e = Y e) :
    restartAvailableExitEdges d i m n R p X =
      restartAvailableExitEdges d i m n R p Y := by
  apply seededRegionAvailableExitEdges_congr_of_eqOn_seedConnectionSupport
  intro e heSupport
  simp only [clearedThreshold, Set.mem_diff, thresholdConfiguration, Set.mem_setOf_eq,
    Finset.mem_coe]
  by_cases heBoundary : e ∈ cubicRegionBoundaryEdgesWithinBox d R n
  · simp [heBoundary]
  · simp [heBoundary, hXY e heSupport]

theorem restartAvailableExitEdges_congr_of_eqOn_restartEventSupport
    {d m n : ℕ} {i : Fin d} {R : Finset (Cubic d)} {p : I}
    {X Y : CubicEdge d → ℝ}
    (hXY : ∀ e ∈ restartEventSupport d i m n R, X e = Y e) :
    restartAvailableExitEdges d i m n R p X =
      restartAvailableExitEdges d i m n R p Y := by
  apply seededRegionAvailableExitEdges_congr_of_eqOn_restartEventSupport
  intro e heSupport
  simp only [clearedThreshold, Set.mem_diff, thresholdConfiguration, Set.mem_setOf_eq,
    Finset.mem_coe]
  by_cases heBoundary : e ∈ cubicRegionBoundaryEdgesWithinBox d R n
  · simp [heBoundary]
  · simp [heBoundary, hXY e heSupport]

theorem restartAvailableExitEdges_subset_boundary
    (d : ℕ) (i : Fin d) (m n : ℕ) (R : Finset (Cubic d)) (p : I)
    (X : CubicEdge d → ℝ) :
    restartAvailableExitEdges d i m n R p X ⊆
      cubicRegionBoundaryEdgesWithinBox d R n :=
  seededRegionAvailableExitEdges_subset_boundary d i m n R _

/-- A seeded connection at density `p` supplies a `p`-open member of the off-boundary
available-exit set.  This is the pathwise bridge from Lemma 7.9 to equations (7.22)–(7.23). -/
theorem seedConnectionEvent_threshold_subset_sprinkledAvailableExitEvent
    {d m n : ℕ} (i : Fin d) (R : Finset (Cubic d)) (p : I)
    (hBmR : cubicMetricBox d cubicOrigin m ⊆ R)
    (hQuadrantR : Disjoint (seededBoundaryQuadrant d i n) R) :
    (thresholdConfiguration p) ⁻¹' seedConnectionEvent d i m n ⊆
      sprinkledAvailableExitEvent (fun _ => (0 : I)) (p : ℝ)
        (restartAvailableExitEdges d i m n R p) := by
  classical
  intro X hseed
  let omega : EdgeConfiguration d := thresholdConfiguration p X
  let E := cubicRegionBoundaryEdgesWithinBox d R n
  rcases hseed with ⟨x, hxBox, y, hySeed, hxy⟩
  have hxR : x ∈ R := hBmR hxBox
  have hyNotR : y ∉ R := fun hyR =>
    Finset.disjoint_left.mp hQuadrantR hySeed.1 hyR
  have hconn : omega ∈ regionConnectionToFiniteTargetEvent d R n {y} :=
    ⟨x, hxR, y, by simp, hxy⟩
  have hdisj : Disjoint ({y} : Finset (Cubic d)) R := by
    rw [Finset.disjoint_left]
    intro z hz hyR
    rw [Finset.mem_singleton] at hz
    subst z
    exact hyNotR hyR
  obtain ⟨e, heAvailable, heOpen⟩ :=
    (mem_regionConnectionToFiniteTargetEvent_iff_exists_open_availableExit hdisj).mp hconn
  rw [mem_regionAvailableExitEdges_iff] at heAvailable
  rcases heAvailable with ⟨heBoundary, z, hzSingleton, w, hwOpen, hwExterior⟩
  have hzy : z = y := by simpa using hzSingleton
  subst z
  have hyCleared : IsSeededBoundaryPoint d i m n
      (clearedThreshold E p X) y := by
    change IsSeededBoundaryPoint d i m n (omega \ (E : Set (CubicEdge d))) y
    exact hySeed.diff_innerBoxEdges E fun e heE =>
      (mem_cubicRegionBoundaryEdgesWithinBox_iff.mp heE).1
  have hwCleared : walkIsOpen (clearedThreshold E p X) w := by
    change walkIsOpen (omega \ (E : Set (CubicEdge d))) w
    exact walkIsOpen_diff_regionBoundary_of_exterior hwOpen hwExterior
  refine ⟨e, ?_, ?_⟩
  · change e ∈ seededRegionAvailableExitEdges d i m n R (clearedThreshold E p X)
    rw [seededRegionAvailableExitEdges, mem_regionAvailableExitEdges_iff]
    exact ⟨heBoundary, y, mem_seededBoundaryPointFinset_iff.mpr hyCleared,
      w, hwCleared, hwExterior⟩
  · simpa [omega, thresholdConfiguration] using heOpen

theorem measurableSet_restartAvailableExitEdges_eq_coordSigma
    (d : ℕ) (i : Fin d) (m n : ℕ) (R : Finset (Cubic d)) (p : I)
    (S : Finset (CubicEdge d)) :
    MeasurableSet[coordSigma (CubicEdge d)
      ((cubicRegionBoundaryEdgesWithinBox d R n : Set (CubicEdge d))ᶜ)]
      (exactAvailableExitSetEvent (restartAvailableExitEdges d i m n R p) S) := by
  change MeasurableSet[coordSigma (CubicEdge d)
      ((cubicRegionBoundaryEdgesWithinBox d R n : Set (CubicEdge d))ᶜ)]
    ((clearedThreshold (cubicRegionBoundaryEdgesWithinBox d R n) p) ⁻¹'
      {omega : EdgeConfiguration d |
        seededRegionAvailableExitEdges d i m n R omega = S})
  exact (measurableSet_seededRegionAvailableExitEdges_eq d i m n R S).preimage
    (measurable_clearedThreshold_coordSigma
      (cubicRegionBoundaryEdgesWithinBox d R n) p)

/-- Equations (7.22)–(7.23): a seeded connection probability above `1-eta` forces the
off-boundary available-exit set to be large, quantitatively. -/
theorem one_sub_p_pow_mul_restartAvailableExit_few_probability_lt
    {d m n : ℕ} (i : Fin d) (R : Finset (Cubic d)) (p : I) (t : ℕ) (eta : ℝ)
    (hBmR : cubicMetricBox d cubicOrigin m ⊆ R)
    (hQuadrantR : Disjoint (seededBoundaryQuadrant d i n) R)
    (hseed : 1 - eta <
      (bernoulliBondMeasure d p).real (seedConnectionEvent d i m n)) :
    (1 - (p : ℝ)) ^ t *
        (couplingMeasure (CubicEdge d)).real
          (fewAvailableExitsEvent (restartAvailableExitEdges d i m n R p) t) < eta := by
  let E := cubicRegionBoundaryEdgesWithinBox d R n
  let U := restartAvailableExitEdges d i m n R p
  let success := sprinkledAvailableExitEvent (fun _ => (0 : I)) (p : ℝ) U
  let failure := sprinkledAvailableExitFailureEvent (fun _ => (0 : I)) (p : ℝ) U
  let mu := couplingMeasure (CubicEdge d)
  have hU : ∀ X, U X ⊆ E :=
    restartAvailableExitEdges_subset_boundary d i m n R p
  have hexact : ∀ S ⊆ E,
      MeasurableSet[coordSigma (CubicEdge d) ((E : Set (CubicEdge d))ᶜ)]
        (exactAvailableExitSetEvent U S) := by
    intro S _hSE
    exact measurableSet_restartAvailableExitEdges_eq_coordSigma d i m n R p S
  have hsuccessMeas : MeasurableSet success :=
    measurableSet_sprinkledAvailableExitEvent E (fun _ => (0 : I)) (p : ℝ) U hU hexact
  have hpreimageMass :
      mu.real ((thresholdConfiguration p) ⁻¹' seedConnectionEvent d i m n) =
        (bernoulliBondMeasure d p).real (seedConnectionEvent d i m n) := by
    dsimp [mu, bernoulliBondMeasure]
    rw [← couplingMeasure_map_thresholdConfiguration (ι := CubicEdge d) p]
    simp only [Measure.real]
    rw [Measure.map_apply (measurable_thresholdConfiguration p)
      (measurableSet_seedConnectionEvent d i m n)]
  have hsuccessMass :
      mu.real ((thresholdConfiguration p) ⁻¹' seedConnectionEvent d i m n) ≤
        mu.real success := by
    exact measureReal_mono
      (seedConnectionEvent_threshold_subset_sprinkledAvailableExitEvent i R p hBmR hQuadrantR)
      (by finiteness)
  have hsuccessGt : 1 - eta < mu.real success := by
    rw [hpreimageMass] at hsuccessMass
    exact hseed.trans_le hsuccessMass
  have hfailureLt : mu.real failure < eta := by
    have hcompl := probReal_add_probReal_compl (μ := mu) hsuccessMeas
    rw [← sprinkledAvailableExitFailureEvent_eq_compl] at hcompl
    dsimp [success, failure] at hcompl hsuccessGt ⊢
    linarith
  have huncertainty := one_sub_pow_mul_fewAvailableExits_le_allAvailableExitsClosed
    E p U t hU hexact
  have hfailureInterLe :
      mu.real
          (sprinkledAvailableExitFailureEvent (fun _ => (0 : I)) (p : ℝ) U ∩
            boundaryClosedHistoryEvent E (fun _ => (0 : I))) ≤ mu.real failure := by
    exact measureReal_mono Set.inter_subset_left (by finiteness)
  exact huncertainty.trans_lt (hfailureInterLe.trans_lt hfailureLt)

/-- Exterior vertex boundary of a finite cubic region. -/
noncomputable def cubicRegionExteriorVertexBoundary
    (d : ℕ) (R : Finset (Cubic d)) : Finset (Cubic d) := by
  classical
  exact (R.biUnion fun x => Finset.univ.image fun a : CubicDirection d =>
    cubicStepFrom x a).filter fun y => y ∉ R

/-- Literal finite encoding of the source condition
`(R ∪ ∂ᵥR) ∩ T(n) = ∅`. -/
def RegionAvoidsSeededBoundaryQuadrant
    (d : ℕ) (i : Fin d) (n : ℕ) (R : Finset (Cubic d)) : Prop :=
  Disjoint (R ∪ cubicRegionExteriorVertexBoundary d R) (seededBoundaryQuadrant d i n)

/-- A one-layer axial gap is sufficient for the source avoidance condition: if every vertex
of `R`, even after one positive coordinate step, remains strictly behind the target face, then
neither `R` nor its exterior vertex boundary meets the seeded quadrant. -/
theorem regionAvoidsSeededBoundaryQuadrant_of_coord_add_one_lt
    {d n : ℕ} {i : Fin d} {R : Finset (Cubic d)}
    (hbehind : ∀ x ∈ R, x i + 1 < (n : ℤ)) :
    RegionAvoidsSeededBoundaryQuadrant d i n R := by
  rw [RegionAvoidsSeededBoundaryQuadrant, Finset.disjoint_left]
  intro y hy hyQuadrant
  have hyFace := (mem_cubicBoxFace.mp
    (mem_seededBoundaryQuadrant_iff.mp hyQuadrant).1).1
  have hyCoord : y i = (n : ℤ) := by
    simpa [cubicOrigin] using hyFace
  rw [Finset.mem_union] at hy
  rcases hy with hyR | hyBoundary
  · have := hbehind y hyR
    omega
  · simp only [cubicRegionExteriorVertexBoundary, Finset.mem_filter,
      Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ, true_and] at hyBoundary
    obtain ⟨⟨x, hxR, a, rfl⟩, _⟩ := hyBoundary
    have hxBehind := hbehind x hxR
    have hstep := cubicStepFrom_coord_le_add_one x a i
    omega

theorem RegionAvoidsSeededBoundaryQuadrant.disjoint_quadrant_region
    {d n : ℕ} {i : Fin d} {R : Finset (Cubic d)}
    (h : RegionAvoidsSeededBoundaryQuadrant d i n R) :
    Disjoint (seededBoundaryQuadrant d i n) R := by
  rw [Finset.disjoint_left]
  intro x hxQ hxR
  exact Finset.disjoint_left.mp h (Finset.mem_union_left _ hxR) hxQ

/-- Source event `G` in Lemma 7.17, expressed through the off-boundary available-exit set.
The exterior portion and the seed are `p`-open; the unique last-exit edge is open at its
individual threshold `beta(e)+delta`. -/
def sprinkledRestartEvent
    (d : ℕ) (i : Fin d) (m n : ℕ) (R : Finset (Cubic d))
    (p : I) (beta : CubicEdge d → I) (delta : ℝ) :
    Set (CubicEdge d → ℝ) :=
  sprinkledAvailableExitEvent beta delta (restartAvailableExitEdges d i m n R p)

/-- The source restart success event is invariant under cropping the explored region to its
declared box. -/
@[simp]
theorem sprinkledRestartEvent_inter_cubicMetricBox
    (d : ℕ) (i : Fin d) (m n : ℕ) (R : Finset (Cubic d))
    (p : I) (beta : CubicEdge d → I) (delta : ℝ) :
    sprinkledRestartEvent d i m n
        (R ∩ cubicMetricBox d cubicOrigin n) p beta delta =
      sprinkledRestartEvent d i m n R p beta delta := by
  have hU : restartAvailableExitEdges d i m n
        (R ∩ cubicMetricBox d cubicOrigin n) p =
      restartAvailableExitEdges d i m n R p := by
    funext X
    exact restartAvailableExitEdges_inter_cubicMetricBox d i m n R p X
  simp [sprinkledRestartEvent, hU]

/-- The accompanying heterogeneous closed-boundary history is invariant under the same
box-cropping operation. -/
@[simp]
theorem boundaryClosedHistoryEvent_cubicRegion_inter_cubicMetricBox
    (d : ℕ) (R : Finset (Cubic d)) (n : ℕ) (beta : CubicEdge d → I) :
    boundaryClosedHistoryEvent
        (cubicRegionBoundaryEdgesWithinBox d
          (R ∩ cubicMetricBox d cubicOrigin n) n) beta =
      boundaryClosedHistoryEvent
        (cubicRegionBoundaryEdgesWithinBox d R n) beta := by
  simp

theorem measurableSet_sprinkledRestartEvent
    (d : ℕ) (i : Fin d) (m n : ℕ) (R : Finset (Cubic d))
    (p : I) (beta : CubicEdge d → I) (delta : ℝ) :
    MeasurableSet (sprinkledRestartEvent d i m n R p beta delta) := by
  let E := cubicRegionBoundaryEdgesWithinBox d R n
  let U := restartAvailableExitEdges d i m n R p
  apply measurableSet_sprinkledAvailableExitEvent E beta delta U
  · exact restartAvailableExitEdges_subset_boundary d i m n R p
  · intro S _hSE
    exact measurableSet_restartAvailableExitEdges_eq_coordSigma d i m n R p S

/-- A reference restart event is a finite cylinder on `seedConnectionSupport`. -/
theorem sprinkledRestartEvent_congr_of_eqOn_seedConnectionSupport
    {d m n : ℕ} {i : Fin d} {R : Finset (Cubic d)} {p : I}
    {beta : CubicEdge d → I} {delta : ℝ} {X Y : CubicEdge d → ℝ}
    (hXY : ∀ e ∈ seedConnectionSupport d i m n, X e = Y e) :
    X ∈ sprinkledRestartEvent d i m n R p beta delta ↔
      Y ∈ sprinkledRestartEvent d i m n R p beta delta := by
  classical
  let U := restartAvailableExitEdges d i m n R p
  have hU : U X = U Y :=
    restartAvailableExitEdges_congr_of_eqOn_seedConnectionSupport hXY
  constructor
  · rintro ⟨e, heU, heOpen⟩
    refine ⟨e, ?_, ?_⟩
    · simpa [U, hU] using heU
    · rw [← hXY e]
      · exact heOpen
      · exact cubicRegionBoundaryEdgesWithinBox_subset_seedConnectionSupport d i m n R
          (restartAvailableExitEdges_subset_boundary d i m n R p X heU)
  · rintro ⟨e, heU, heOpen⟩
    refine ⟨e, ?_, ?_⟩
    · simpa [U, hU] using heU
    · rw [hXY e]
      · exact heOpen
      · exact cubicRegionBoundaryEdgesWithinBox_subset_seedConnectionSupport d i m n R
          (restartAvailableExitEdges_subset_boundary d i m n R p Y heU)

/-- Exact finite-support version, excluding already explored interior edges. -/
theorem sprinkledRestartEvent_congr_of_eqOn_restartEventSupport
    {d m n : ℕ} {i : Fin d} {R : Finset (Cubic d)} {p : I}
    {beta : CubicEdge d → I} {delta : ℝ} {X Y : CubicEdge d → ℝ}
    (hXY : ∀ e ∈ restartEventSupport d i m n R, X e = Y e) :
    X ∈ sprinkledRestartEvent d i m n R p beta delta ↔
      Y ∈ sprinkledRestartEvent d i m n R p beta delta := by
  classical
  let U := restartAvailableExitEdges d i m n R p
  have hU : U X = U Y :=
    restartAvailableExitEdges_congr_of_eqOn_restartEventSupport hXY
  constructor
  · rintro ⟨e, heU, heOpen⟩
    refine ⟨e, ?_, ?_⟩
    · simpa [U, hU] using heU
    · rw [← hXY e]
      · exact heOpen
      · exact boundary_subset_restartEventSupport d i m n R
          (restartAvailableExitEdges_subset_boundary d i m n R p X heU)
  · rintro ⟨e, heU, heOpen⟩
    refine ⟨e, ?_, ?_⟩
    · simpa [U, hU] using heU
    · rw [hXY e]
      · exact heOpen
      · exact boundary_subset_restartEventSupport d i m n R
          (restartAvailableExitEdges_subset_boundary d i m n R p Y heU)

/-- A restart depends only on the background-`p` open/closed pattern on its finite support and
the incremented open/closed pattern on its boundary.  Exact equality of real labels is much
stronger than needed and is unavailable after passing to an accumulated interval cell. -/
theorem sprinkledRestartEvent_congr_of_thresholdIffOn_restartEventSupport
    {d m n : ℕ} {i : Fin d} {R : Finset (Cubic d)} {p : I}
    {beta : CubicEdge d → I} {delta : ℝ} {X Y : CubicEdge d → ℝ}
    (hp : ∀ e ∈ restartEventSupport d i m n R,
      (X e < (p : ℝ) ↔ Y e < (p : ℝ)))
    (hincremented : ∀ e ∈ cubicRegionBoundaryEdgesWithinBox d R n,
      (X e < (beta e : ℝ) + delta ↔ Y e < (beta e : ℝ) + delta)) :
    X ∈ sprinkledRestartEvent d i m n R p beta delta ↔
      Y ∈ sprinkledRestartEvent d i m n R p beta delta := by
  classical
  let E := cubicRegionBoundaryEdgesWithinBox d R n
  let U := restartAvailableExitEdges d i m n R p
  have hcleared : ∀ e ∈ restartEventSupport d i m n R,
      (e ∈ clearedThreshold E p X ↔ e ∈ clearedThreshold E p Y) := by
    intro e heSupport
    by_cases heE : e ∈ E
    · simp [clearedThreshold, heE]
    · simpa [clearedThreshold, heE] using hp e heSupport
  have hU : U X = U Y := by
    apply seededRegionAvailableExitEdges_congr_of_eqOn_restartEventSupport
    exact hcleared
  constructor
  · rintro ⟨e, heU, heOpen⟩
    refine ⟨e, ?_, ?_⟩
    · simpa [U, hU] using heU
    · exact (hincremented e
        (restartAvailableExitEdges_subset_boundary d i m n R p X heU)).mp heOpen
  · rintro ⟨e, heU, heOpen⟩
    refine ⟨e, ?_, ?_⟩
    · simpa [U, hU] using heU
    · exact (hincremented e
        (restartAvailableExitEdges_subset_boundary d i m n R p Y heU)).mpr heOpen

theorem measurableSet_sprinkledRestartEvent_coordSigma
    (d : ℕ) (i : Fin d) (m n : ℕ) (R : Finset (Cubic d))
    (p : I) (beta : CubicEdge d → I) (delta : ℝ) :
    MeasurableSet[coordSigma (CubicEdge d)
      (seedConnectionSupport d i m n : Set (CubicEdge d))]
      (sprinkledRestartEvent d i m n R p beta delta) := by
  apply measurableSet_coordSigma_of_eqOn
    (measurableSet_sprinkledRestartEvent d i m n R p beta delta)
  intro X Y hXY
  exact sprinkledRestartEvent_congr_of_eqOn_seedConnectionSupport
    (fun e he => hXY e he)

theorem measurableSet_sprinkledRestartEvent_restartCoordSigma
    (d : ℕ) (i : Fin d) (m n : ℕ) (R : Finset (Cubic d))
    (p : I) (beta : CubicEdge d → I) (delta : ℝ) :
    MeasurableSet[coordSigma (CubicEdge d)
      (restartEventSupport d i m n R : Set (CubicEdge d))]
      (sprinkledRestartEvent d i m n R p beta delta) := by
  apply measurableSet_coordSigma_of_eqOn
    (measurableSet_sprinkledRestartEvent d i m n R p beta delta)
  intro X Y hXY
  exact sprinkledRestartEvent_congr_of_eqOn_restartEventSupport
    (fun e he => hXY e he)

/-- Quantitative assembly of Lemma 7.17 once `m,n,t,eta` satisfy Grimmett's choices
(7.18)–(7.20). -/
theorem sprinkledRestart_inter_history_gt_of_seedConnection
    {d m n t : ℕ} (i : Fin d) (R : Finset (Cubic d))
    (p : I) (beta : CubicEdge d → I) (delta epsilon eta : ℝ)
    (hp1 : (p : ℝ) < 1)
    (hBmR : cubicMetricBox d cubicOrigin m ⊆ R)
    (hAvoid : RegionAvoidsSeededBoundaryQuadrant d i n R)
    (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hupper : ∀ e ∈ cubicRegionBoundaryEdgesWithinBox d R n,
      (beta e : ℝ) + delta ≤ 1)
    (hseed : 1 - eta <
      (bernoulliBondMeasure d p).real (seedConnectionEvent d i m n))
    (heta : eta < epsilon / 2 * (1 - (p : ℝ)) ^ t)
    (hmiss : (1 - delta) ^ (t + 1) < epsilon / 2) :
    (1 - epsilon) *
        (couplingMeasure (CubicEdge d)).real
          (boundaryClosedHistoryEvent (cubicRegionBoundaryEdgesWithinBox d R n) beta) <
      (couplingMeasure (CubicEdge d)).real
        (sprinkledRestartEvent d i m n R p beta delta ∩
          boundaryClosedHistoryEvent (cubicRegionBoundaryEdgesWithinBox d R n) beta) := by
  let E := cubicRegionBoundaryEdgesWithinBox d R n
  let U := restartAvailableExitEdges d i m n R p
  have hU : ∀ X, U X ⊆ E :=
    restartAvailableExitEdges_subset_boundary d i m n R p
  have hexact : ∀ S ⊆ E,
      MeasurableSet[coordSigma (CubicEdge d) ((E : Set (CubicEdge d))ᶜ)]
        (exactAvailableExitSetEvent U S) := by
    intro S _hSE
    exact measurableSet_restartAvailableExitEdges_eq_coordSigma d i m n R p S
  have hpBase : 0 < (1 - (p : ℝ)) ^ t :=
    pow_pos (sub_pos.mpr hp1) t
  have hfewMul := one_sub_p_pow_mul_restartAvailableExit_few_probability_lt
    i R p t eta hBmR hAvoid.disjoint_quadrant_region hseed
  have hfew :
      (couplingMeasure (CubicEdge d)).real (fewAvailableExitsEvent U t) < epsilon / 2 := by
    have hmul : (1 - (p : ℝ)) ^ t *
        (couplingMeasure (CubicEdge d)).real (fewAvailableExitsEvent U t) <
          epsilon / 2 * (1 - (p : ℝ)) ^ t := hfewMul.trans heta
    nlinarith [hmul]
  have hsmall :
      (couplingMeasure (CubicEdge d)).real (fewAvailableExitsEvent U t) +
        (1 - delta) ^ (t + 1) < epsilon := by linarith
  exact sprinkledAvailableExit_inter_history_gt E beta delta epsilon U t hU hdelta hdelta1
    hupper hexact hsmall

/-- Conditional-ratio version of the preceding quantitative assembly. -/
theorem sprinkledRestart_conditionalProbability_gt_of_seedConnection
    {d m n t : ℕ} (i : Fin d) (R : Finset (Cubic d))
    (p : I) (beta : CubicEdge d → I) (delta epsilon eta : ℝ)
    (hp1 : (p : ℝ) < 1)
    (hBmR : cubicMetricBox d cubicOrigin m ⊆ R)
    (hAvoid : RegionAvoidsSeededBoundaryQuadrant d i n R)
    (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hupper : ∀ e ∈ cubicRegionBoundaryEdgesWithinBox d R n,
      (beta e : ℝ) + delta ≤ 1)
    (hseed : 1 - eta <
      (bernoulliBondMeasure d p).real (seedConnectionEvent d i m n))
    (heta : eta < epsilon / 2 * (1 - (p : ℝ)) ^ t)
    (hmiss : (1 - delta) ^ (t + 1) < epsilon / 2) :
    1 - epsilon <
      (couplingMeasure (CubicEdge d)).real
          (sprinkledRestartEvent d i m n R p beta delta ∩
            boundaryClosedHistoryEvent (cubicRegionBoundaryEdgesWithinBox d R n) beta) /
        (couplingMeasure (CubicEdge d)).real
          (boundaryClosedHistoryEvent (cubicRegionBoundaryEdgesWithinBox d R n) beta) := by
  have hHpos : 0 < (couplingMeasure (CubicEdge d)).real
      (boundaryClosedHistoryEvent (cubicRegionBoundaryEdgesWithinBox d R n) beta) := by
    apply couplingMeasure_real_boundaryClosedHistoryEvent_pos
    intro e heE
    have := hupper e heE
    linarith
  exact (lt_div_iff₀ hHpos).2
    (sprinkledRestart_inter_history_gt_of_seedConnection i R p beta delta epsilon eta hp1
      hBmR hAvoid hdelta hdelta1 hupper hseed heta hmiss)

/-- **Grimmett Lemma 7.17**, strict ratio-free form, in the nontrivial density range used by
the dynamic block construction.  The chosen `m,n` are uniform over the region `R` and the
heterogeneous boundary threshold profile `beta`. -/
theorem sprinkledRestart_inter_history_gt
    (d : ℕ) [NeZero d] (hd : 0 < d) (i : Fin d) (p : I)
    (htheta : 0 < theta d p) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    {epsilon delta : ℝ} (hepsilon : 0 < epsilon)
    (hdelta : 0 < delta) (hdelta1 : delta ≤ 1) :
    ∃ m n : ℕ, 2 * m < n ∧
      ∀ (R : Finset (Cubic d)) (beta : CubicEdge d → I),
        cubicMetricBox d cubicOrigin m ⊆ R →
        R ⊆ cubicMetricBox d cubicOrigin n →
        RegionAvoidsSeededBoundaryQuadrant d i n R →
        (∀ e ∈ cubicRegionBoundaryEdgesWithinBox d R n,
          (beta e : ℝ) + delta ≤ 1) →
        (1 - epsilon) *
            (couplingMeasure (CubicEdge d)).real
              (boundaryClosedHistoryEvent
                (cubicRegionBoundaryEdgesWithinBox d R n) beta) <
          (couplingMeasure (CubicEdge d)).real
            (sprinkledRestartEvent d i m n R p beta delta ∩
              boundaryClosedHistoryEvent
                (cubicRegionBoundaryEdgesWithinBox d R n) beta) := by
  let q : ℝ := 1 - delta
  have hq0 : 0 ≤ q := sub_nonneg.mpr hdelta1
  have hq1 : q < 1 := by dsimp [q]; linarith
  have hqTendsto : Filter.Tendsto (fun k : ℕ => q ^ k) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
  have hqEventually : ∀ᶠ k : ℕ in Filter.atTop, q ^ k < epsilon / 2 :=
    hqTendsto.eventually (Iio_mem_nhds (half_pos hepsilon))
  obtain ⟨t, ht⟩ := hqEventually.exists
  have hmiss : (1 - delta) ^ (t + 1) < epsilon / 2 := by
    have hpow : q ^ (t + 1) ≤ q ^ t :=
      pow_le_pow_of_le_one hq0 (le_of_lt hq1) (Nat.le_succ t)
    exact (by simpa [q] using hpow.trans_lt ht)
  let eta : ℝ := epsilon / 4 * (1 - (p : ℝ)) ^ t
  have hetaPos : 0 < eta := mul_pos (by positivity) (pow_pos (sub_pos.mpr hp1) t)
  obtain ⟨m, n, hmn, hseed⟩ :=
    seedConnection_probability_gt d hd p htheta hp0 hp1 i hetaPos
  refine ⟨m, n, hmn, ?_⟩
  intro R beta hBmR _hRBn hAvoid hupper
  have heta : eta < epsilon / 2 * (1 - (p : ℝ)) ^ t := by
    dsimp [eta]
    have hbase := pow_pos (sub_pos.mpr hp1) t
    nlinarith
  exact sprinkledRestart_inter_history_gt_of_seedConnection i R p beta delta epsilon eta hp1
    hBmR hAvoid hdelta hdelta1 hupper hseed heta hmiss

/-- Coordinate-uniform ratio-free Lemma 7.17.  A single pair of radii works for every
coordinate direction; signed directions are obtained by `framedSprinkledRestart_inter_history_gt`.
This is the form needed by the simultaneous root construction. -/
theorem sprinkledRestart_inter_history_gt_allCoordinates
    (d : ℕ) [NeZero d] (hd : 0 < d) (p : I)
    (htheta : 0 < theta d p) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    {epsilon delta : ℝ} (hepsilon : 0 < epsilon)
    (hdelta : 0 < delta) (hdelta1 : delta ≤ 1) :
    ∃ m n : ℕ, 2 * m < n ∧ m + 1 < n ∧
      ∀ (i : Fin d) (R : Finset (Cubic d)) (beta : CubicEdge d → I),
        cubicMetricBox d cubicOrigin m ⊆ R →
        R ⊆ cubicMetricBox d cubicOrigin n →
        RegionAvoidsSeededBoundaryQuadrant d i n R →
        (∀ e ∈ cubicRegionBoundaryEdgesWithinBox d R n,
          (beta e : ℝ) + delta ≤ 1) →
        (1 - epsilon) *
            (couplingMeasure (CubicEdge d)).real
              (boundaryClosedHistoryEvent
                (cubicRegionBoundaryEdgesWithinBox d R n) beta) <
          (couplingMeasure (CubicEdge d)).real
            (sprinkledRestartEvent d i m n R p beta delta ∩
              boundaryClosedHistoryEvent
                (cubicRegionBoundaryEdgesWithinBox d R n) beta) := by
  let q : ℝ := 1 - delta
  have hq0 : 0 ≤ q := sub_nonneg.mpr hdelta1
  have hq1 : q < 1 := by dsimp [q]; linarith
  have hqTendsto : Filter.Tendsto (fun k : ℕ => q ^ k) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
  have hqEventually : ∀ᶠ k : ℕ in Filter.atTop, q ^ k < epsilon / 2 :=
    hqTendsto.eventually (Iio_mem_nhds (half_pos hepsilon))
  obtain ⟨t, ht⟩ := hqEventually.exists
  have hmiss : (1 - delta) ^ (t + 1) < epsilon / 2 := by
    have hpow : q ^ (t + 1) ≤ q ^ t :=
      pow_le_pow_of_le_one hq0 (le_of_lt hq1) (Nat.le_succ t)
    exact (by simpa [q] using hpow.trans_lt ht)
  let eta : ℝ := epsilon / 4 * (1 - (p : ℝ)) ^ t
  have hetaPos : 0 < eta := mul_pos (by positivity) (pow_pos (sub_pos.mpr hp1) t)
  obtain ⟨m, n, hmn, hmnBoundary, hseed⟩ :=
    seedConnection_probability_gt_allCoordinates d hd p htheta hp0 hp1 hetaPos
  refine ⟨m, n, hmn, hmnBoundary, ?_⟩
  intro i R beta hBmR _hRBn hAvoid hupper
  have heta : eta < epsilon / 2 * (1 - (p : ℝ)) ^ t := by
    dsimp [eta]
    have hbase := pow_pos (sub_pos.mpr hp1) t
    nlinarith
  exact sprinkledRestart_inter_history_gt_of_seedConnection i R p beta delta epsilon eta hp1
    hBmR hAvoid hdelta hdelta1 hupper (hseed i) heta hmiss

/-- Compact name for the all-coordinate, all-admissible-region conclusion of Lemma 7.17 at
fixed radii.  It is the reusable probabilistic payload carried by a dynamic block package. -/
def UniformRestartBounds
    (d m n : ℕ) (p : I) (delta epsilon : ℝ) : Prop :=
  ∀ (i : Fin d) (R : Finset (Cubic d)) (beta : CubicEdge d → I),
    cubicMetricBox d cubicOrigin m ⊆ R →
    R ⊆ cubicMetricBox d cubicOrigin n →
    RegionAvoidsSeededBoundaryQuadrant d i n R →
    (∀ e ∈ cubicRegionBoundaryEdgesWithinBox d R n,
      (beta e : ℝ) + delta ≤ 1) →
    (1 - epsilon) *
        (couplingMeasure (CubicEdge d)).real
          (boundaryClosedHistoryEvent
            (cubicRegionBoundaryEdgesWithinBox d R n) beta) <
      (couplingMeasure (CubicEdge d)).real
        (sprinkledRestartEvent d i m n R p beta delta ∩
          boundaryClosedHistoryEvent
            (cubicRegionBoundaryEdgesWithinBox d R n) beta)

/-- Packaged coordinate-uniform Lemma 7.17 with its two geometric radius gaps. -/
theorem exists_uniformRestartBounds
    (d : ℕ) [NeZero d] (hd : 0 < d) (p : I)
    (htheta : 0 < theta d p) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    {epsilon delta : ℝ} (hepsilon : 0 < epsilon)
    (hdelta : 0 < delta) (hdelta1 : delta ≤ 1) :
    ∃ m n : ℕ, 2 * m < n ∧ m + 1 < n ∧
      UniformRestartBounds d m n p delta epsilon := by
  simpa only [UniformRestartBounds] using
    sprinkledRestart_inter_history_gt_allCoordinates
      d hd p htheta hp0 hp1 hepsilon hdelta hdelta1

/-- Conditional-probability form of Grimmett Lemma 7.17.  Positivity of the heterogeneous
history is discharged before division. -/
theorem sprinkledRestart_conditionalProbability_gt
    (d : ℕ) [NeZero d] (hd : 0 < d) (i : Fin d) (p : I)
    (htheta : 0 < theta d p) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    {epsilon delta : ℝ} (hepsilon : 0 < epsilon)
    (hdelta : 0 < delta) (hdelta1 : delta ≤ 1) :
    ∃ m n : ℕ, 2 * m < n ∧
      ∀ (R : Finset (Cubic d)) (beta : CubicEdge d → I),
        cubicMetricBox d cubicOrigin m ⊆ R →
        R ⊆ cubicMetricBox d cubicOrigin n →
        RegionAvoidsSeededBoundaryQuadrant d i n R →
        (∀ e ∈ cubicRegionBoundaryEdgesWithinBox d R n,
          (beta e : ℝ) + delta ≤ 1) →
        1 - epsilon <
          (couplingMeasure (CubicEdge d)).real
              (sprinkledRestartEvent d i m n R p beta delta ∩
                boundaryClosedHistoryEvent
                  (cubicRegionBoundaryEdgesWithinBox d R n) beta) /
            (couplingMeasure (CubicEdge d)).real
              (boundaryClosedHistoryEvent
                (cubicRegionBoundaryEdgesWithinBox d R n) beta) := by
  obtain ⟨m, n, hmn, hrestart⟩ :=
    sprinkledRestart_inter_history_gt d hd i p htheta hp0 hp1 hepsilon hdelta hdelta1
  refine ⟨m, n, hmn, ?_⟩
  intro R beta hBmR hRBn hAvoid hupper
  have hHpos : 0 < (couplingMeasure (CubicEdge d)).real
      (boundaryClosedHistoryEvent (cubicRegionBoundaryEdgesWithinBox d R n) beta) := by
    apply couplingMeasure_real_boundaryClosedHistoryEvent_pos
    intro e heE
    have := hupper e heE
    linarith
  exact (lt_div_iff₀ hHpos).2
    (hrestart R beta hBmR hRBn hAvoid hupper)

end Percolation
