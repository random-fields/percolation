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

/-- Canonical endpoint of a region-boundary edge lying in `R`. -/
def cubicRegionBoundaryInsideEndpoint
    {d : ℕ} (R : Finset (Cubic d)) (e : CubicEdge d) : Cubic d :=
  if e.1.out.1 ∈ R then e.1.out.1 else e.1.out.2

/-- Canonical endpoint of a region-boundary edge lying outside `R`. -/
def cubicRegionBoundaryOutsideEndpoint
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
  · simpa [cubicRegionBoundaryOutsideEndpoint, h.2] using h.2

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
  push Not
  rfl

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
  have heExterior : (⟨e, w.edges_subset_edgeSet he⟩ : CubicEdge d) ∈
      cubicRegionExteriorEdgesWithinBox d R n :=
    hsub ((mem_walkEdgeFinset_iff w e).mpr he)
  exact Set.disjoint_left.mp
    (disjoint_cubicRegionExteriorEdgesWithinBox_boundary d R n)
      heExterior heBoundary

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

theorem IsSeededBoundaryPoint.diff_innerBoxEdges
    {d m n : ℕ} {i : Fin d} {omega : EdgeConfiguration d} {y : Cubic d}
    (hy : IsSeededBoundaryPoint d i m n omega y)
    (E : Finset (CubicEdge d)) (hE : E ⊆ cubicBoxEdges d cubicOrigin n) :
    IsSeededBoundaryPoint d i m n (omega \ (E : Set (CubicEdge d))) y := by
  rcases hy with ⟨hyQ, hyEdge, c, hyc, hcLayer, hcSeed⟩
  refine ⟨hyQ, ⟨hyEdge, ?_⟩, c, hyc, hcLayer, ?_⟩
  · intro heE
    have heBox := hE heE
    have hstepBox := endpoint_mem_cubicMetricBox_of_edge_mem_cubicBoxEdges heBox (by
      simp [cubicStepEdge])
    have hyFace := mem_cubicBoxFace.mp (mem_seededBoundaryQuadrant_iff.mp hyQ).1
    have hyi : y i = (n : ℤ) := by simpa [cubicOrigin] using hyFace.1
    have hcoord := (mem_cubicMetricBox.mp hstepBox) i
    rw [cubicStepFrom_same, hyi] at hcoord
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
          rw [mem_cubicRegionBoundaryEdgesWithinBox_iff]
          refine ⟨heBox, ?_⟩
          change (z ∈ R ∧ v ∉ R) ∨ (v ∈ R ∧ z ∉ R)
          exact Or.inl ⟨hzR, hvNotR⟩
        have hout : cubicRegionBoundaryOutsideEndpoint R e = v := by
          simp [cubicRegionBoundaryOutsideEndpoint, e, hzR]
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
              rw [SimpleGraph.Walk.mem_support_iff]
              rw [← SimpleGraph.mem_edgeSet] at f
              exact (p.adj_support_of_mem_edges hf).resolve_left fun haz => by
                subst a
                exact (SimpleGraph.loopless _ f)
            simpa using haSupport
        have hpOpen : walkIsOpen omega p := by
          intro f hf
          exact hqOpen f (by simp [SimpleGraph.Walk.edges_cons, hf])
        refine ⟨e, ?_, ?_⟩
        · rw [mem_regionAvailableExitEdges_iff]
          exact ⟨heBoundary, y, hyK, by simpa [hout] using
            (show omega ∈ connectionEventIn d (cubicRegionExteriorEdgesWithinBox d R n) v y
              from ⟨p, hpOpen, hpExterior⟩)⟩
        · exact hqOpen _ (by simp [SimpleGraph.Walk.edges_cons, e])
  · rintro ⟨e, heU, heOpen⟩
    rw [mem_regionAvailableExitEdges_iff] at heU
    rcases heU with ⟨heBoundary, y, hyK, w, hwOpen, hwExterior⟩
    let x := cubicRegionBoundaryInsideEndpoint R e
    let z := cubicRegionBoundaryOutsideEndpoint R e
    have hxR : x ∈ R := cubicRegionBoundaryInsideEndpoint_mem heBoundary
    have hadj : (cubicGraph d).Adj x z := by
      rw [← SimpleGraph.mem_edgeSet]
      change s(x, z) ∈ (cubicGraph d).edgeSet
      rw [cubicRegionBoundaryEndpoints_edge heBoundary]
      exact e.2
    let q : (cubicGraph d).Walk x y := SimpleGraph.Walk.cons hadj w
    have hqOpen : walkIsOpen omega q := by
      intro f hf
      simp only [q, SimpleGraph.Walk.edges_cons, List.mem_cons] at hf
      rcases hf with hf | hf
      · have hfe : f = (e : Sym2 (Cubic d)) := by
          rw [← hf]
          exact cubicRegionBoundaryEndpoints_edge heBoundary
        simpa [hfe] using heOpen
      · exact hwOpen f hf
    have hqBox : walkEdgeFinset q ⊆ cubicBoxEdges d cubicOrigin n := by
      intro f hf
      rw [mem_walkEdgeFinset_iff] at hf
      simp only [q, SimpleGraph.Walk.edges_cons, List.mem_cons] at hf
      rcases hf with hf | hf
      · have hfe : (⟨f, q.edges_subset_edgeSet (by simp [q, hf])⟩ : CubicEdge d) = e := by
          apply Subtype.ext
          rw [← hf]
          exact cubicRegionBoundaryEndpoints_edge heBoundary
        simpa [hfe] using (mem_cubicRegionBoundaryEdgesWithinBox_iff.mp heBoundary).1
      · exact Finset.sdiff_subset (hwExterior ((mem_walkEdgeFinset_iff w f).mpr hf))
    exact ⟨x, hxR, y, hyK, q, hqOpen, hqBox⟩

/-- Available exits to the actual seeded target `K(m,n)`. -/
noncomputable def seededRegionAvailableExitEdges
    (d : ℕ) (i : Fin d) (m n : ℕ) (R : Finset (Cubic d))
    (omega : EdgeConfiguration d) : Finset (CubicEdge d) :=
  regionAvailableExitEdges d R n (seededBoundaryPointFinset d i m n omega) omega

theorem seededRegionAvailableExitEdges_subset_boundary
    (d : ℕ) (i : Fin d) (m n : ℕ) (R : Finset (Cubic d))
    (omega : EdgeConfiguration d) :
    seededRegionAvailableExitEdges d i m n R omega ⊆
      cubicRegionBoundaryEdgesWithinBox d R n :=
  regionAvailableExitEdges_subset_boundary d R n _ omega

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
      simp [seededRegionAvailableExitEdges, mem_regionAvailableExitEdges_iff, he]
    rw [hevent]
    exact MeasurableSet.biUnion_finset fun y _hy =>
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
        exact ⟨fun e he => he, fun e heE heNot => heNot⟩
      · rintro ⟨hmem, hnot⟩
        apply Finset.Subset.antisymm (seededRegionAvailableExitEdges_subset_boundary
          d i m n R omega) hSE
        · intro e heU
          by_contra heS
          exact hnot e (seededRegionAvailableExitEdges_subset_boundary
            d i m n R omega heU) heS heU
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
    simpa using hyNotR hyR
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
  · exact heOpen

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
    rw [Measure.real, ← couplingMeasure_map_thresholdConfiguration (ι := CubicEdge d) p,
      Measure.map_apply (measurable_thresholdConfiguration p)
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
    exact (mul_lt_mul_right hpBase).mp (by simpa [mul_comm] using hmul)
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
