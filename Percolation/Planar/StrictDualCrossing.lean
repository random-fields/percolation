import Percolation.Planar.BondCrossingDuality
import Percolation.Planar.BRDualExploration
import Percolation.Planar.RSWHalf

/-!
# Uniform strict shifted-dual crossings at half density

This file adds one fresh edge to the left of the three-edge trace witness from `RSWHalf`.
After translation, the resulting open walk runs across the complete shifted-dual frame from
`x = -1` to `x = 2n`. Pulling the event back through `dualSquareConfiguration` turns every
edge of the walk into a closed primal bond. The fourth fresh edge changes the axiom-free
uniform lower bound from `1 / 16` to `1 / 32`.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval Sym2

/-- The second outward edge to the left of a selected Grimmett crossing. -/
def grimmettTraceLeftSecondExtensionEdge
    {n : ℕ} {s : Finset SquareEdge} (W : GrimmettRectangleTraceCrossing n s) : SquareEdge :=
  cubicStepEdge (grimmettTraceLeftOuterVertex W) ((0 : Fin 2), false)

/-- The endpoint two steps to the left of a selected Grimmett crossing. -/
def grimmettTraceLeftSecondOuterVertex
    {n : ℕ} {s : Finset SquareEdge} (W : GrimmettRectangleTraceCrossing n s) :
    SquareVertex :=
  cubicStepFrom (grimmettTraceLeftOuterVertex W) ((0 : Fin 2), false)

/-- A selected trace crossing with two fresh edges on each horizontal side. -/
def grimmettTraceExtendedWalkFour
    {n : ℕ} {s : Finset SquareEdge} (W : GrimmettRectangleTraceCrossing n s) :
    squareGraph.Walk (grimmettTraceLeftSecondOuterVertex W)
      (grimmettTraceRightSecondOuterVertex W) :=
  (SimpleGraph.Walk.cons
      (cubicGraph_adj_stepFrom (grimmettTraceLeftOuterVertex W) ((0 : Fin 2), false)).symm
      SimpleGraph.Walk.nil).append
    (grimmettTraceExtendedWalkThree W)

/-- Four trace-dependent fresh edges: two on each horizontal side. -/
noncomputable def grimmettRectangleFreshExtensionEdgesFour
    (n : ℕ) (s : Finset SquareEdge) : Finset SquareEdge := by
  classical
  exact if hs : s ∈ grimmettRectangleCrossingTraces n then
    let W := selectedGrimmettRectangleTraceCrossing n ⟨s, hs⟩
    insert (grimmettTraceLeftSecondExtensionEdge W)
      (grimmettRectangleFreshExtensionEdgesThree n s)
  else ∅

private theorem grimmettTraceLeftSecondExtensionEdge_not_mem
    {n : ℕ} {s : Finset SquareEdge} (W : GrimmettRectangleTraceCrossing n s) :
    grimmettTraceLeftSecondExtensionEdge W ∉ grimmettRectangleEdges n := by
  intro he
  have hzEdge : grimmettTraceLeftSecondOuterVertex W ∈
      (grimmettTraceLeftSecondExtensionEdge W : Sym2 SquareVertex) := by
    simp [grimmettTraceLeftSecondOuterVertex, grimmettTraceLeftSecondExtensionEdge,
      cubicStepEdge]
  have hzRect := endpoint_mem_grimmettRectangleVertices_of_edge_mem he hzEdge
  have hz0 := (mem_grimmettRectangleVertices_iff.mp hzRect).1
  have hs0 := (mem_grimmettRectangleLeft_iff.mp W.start_mem).1
  simp [grimmettTraceLeftSecondOuterVertex, grimmettTraceLeftOuterVertex,
    cubicStepFrom, cubicDirectionIncrement, hs0] at hz0

private theorem grimmettTraceLeftSecondExtensionEdge_ne_left
    {n : ℕ} {s : Finset SquareEdge} (W : GrimmettRectangleTraceCrossing n s) :
    grimmettTraceLeftSecondExtensionEdge W ≠ grimmettTraceLeftExtensionEdge W := by
  intro h
  have hz : grimmettTraceLeftSecondOuterVertex W ∈
      (grimmettTraceLeftSecondExtensionEdge W : Sym2 SquareVertex) := by
    simp [grimmettTraceLeftSecondOuterVertex, grimmettTraceLeftSecondExtensionEdge,
      cubicStepEdge]
  rw [h, grimmettTraceLeftExtensionEdge, cubicStepEdge, Sym2.mem_iff] at hz
  have hs0 := (mem_grimmettRectangleLeft_iff.mp W.start_mem).1
  rcases hz with hz | hz
  · have hz0 := congrFun hz 0
    simp [grimmettTraceLeftSecondOuterVertex, grimmettTraceLeftOuterVertex,
      cubicStepFrom, cubicDirectionIncrement, hs0] at hz0
  · have hz0 := congrFun hz 0
    simp [grimmettTraceLeftSecondOuterVertex, grimmettTraceLeftOuterVertex,
      cubicStepFrom, cubicDirectionIncrement, hs0] at hz0

private theorem grimmettTraceLeftSecondExtensionEdge_ne_right
    {n : ℕ} {s : Finset SquareEdge} (W : GrimmettRectangleTraceCrossing n s) :
    grimmettTraceLeftSecondExtensionEdge W ≠ grimmettTraceRightExtensionEdge W := by
  intro h
  have hz : grimmettTraceLeftSecondOuterVertex W ∈
      (grimmettTraceLeftSecondExtensionEdge W : Sym2 SquareVertex) := by
    simp [grimmettTraceLeftSecondOuterVertex, grimmettTraceLeftSecondExtensionEdge,
      cubicStepEdge]
  rw [h, grimmettTraceRightExtensionEdge, cubicStepEdge, Sym2.mem_iff] at hz
  have hs0 := (mem_grimmettRectangleLeft_iff.mp W.start_mem).1
  have hf0 := (mem_grimmettRectangleRight_iff.mp W.finish_mem).1
  rcases hz with hz | hz
  · have hz0 := congrFun hz 0
    simp [grimmettTraceLeftSecondOuterVertex, grimmettTraceLeftOuterVertex,
      cubicStepFrom, cubicDirectionIncrement, hs0, hf0] at hz0
    omega
  · have hz0 := congrFun hz 0
    simp [grimmettTraceLeftSecondOuterVertex, grimmettTraceLeftOuterVertex,
      cubicStepFrom, cubicDirectionIncrement, hs0, hf0] at hz0
    omega

private theorem grimmettTraceLeftSecondExtensionEdge_ne_rightSecond
    {n : ℕ} {s : Finset SquareEdge} (W : GrimmettRectangleTraceCrossing n s) :
    grimmettTraceLeftSecondExtensionEdge W ≠ grimmettTraceRightSecondExtensionEdge W := by
  intro h
  have hz : grimmettTraceLeftSecondOuterVertex W ∈
      (grimmettTraceLeftSecondExtensionEdge W : Sym2 SquareVertex) := by
    simp [grimmettTraceLeftSecondOuterVertex, grimmettTraceLeftSecondExtensionEdge,
      cubicStepEdge]
  rw [h, grimmettTraceRightSecondExtensionEdge, cubicStepEdge, Sym2.mem_iff] at hz
  have hs0 := (mem_grimmettRectangleLeft_iff.mp W.start_mem).1
  have hf0 := (mem_grimmettRectangleRight_iff.mp W.finish_mem).1
  rcases hz with hz | hz
  · have hz0 := congrFun hz 0
    simp [grimmettTraceLeftSecondOuterVertex, grimmettTraceLeftOuterVertex,
      grimmettTraceRightOuterVertex, cubicStepFrom, cubicDirectionIncrement,
      hs0, hf0] at hz0
    omega
  · have hz0 := congrFun hz 0
    simp [grimmettTraceLeftSecondOuterVertex, grimmettTraceLeftOuterVertex,
      grimmettTraceRightOuterVertex, cubicStepFrom, cubicDirectionIncrement,
      hs0, hf0] at hz0
    omega

theorem grimmettRectangleFreshExtensionEdgesFour_disjoint
    (n : ℕ) (s : Finset SquareEdge) (hs : s ∈ grimmettRectangleCrossingTraces n) :
    Disjoint (grimmettRectangleFreshExtensionEdgesFour n s)
      (grimmettRectangleEdges n) := by
  classical
  let W := selectedGrimmettRectangleTraceCrossing n ⟨s, hs⟩
  rw [Finset.disjoint_left]
  intro e he hE
  simp only [grimmettRectangleFreshExtensionEdgesFour, dif_pos hs,
    Finset.mem_insert] at he
  rcases he with rfl | he
  · exact grimmettTraceLeftSecondExtensionEdge_not_mem W hE
  · exact (Finset.disjoint_left.mp
      (grimmettRectangleFreshExtensionEdgesThree_disjoint n s hs)) he hE

theorem card_grimmettRectangleFreshExtensionEdgesFour
    (n : ℕ) (s : Finset SquareEdge) (hs : s ∈ grimmettRectangleCrossingTraces n) :
    (grimmettRectangleFreshExtensionEdgesFour n s).card = 4 := by
  classical
  let W := selectedGrimmettRectangleTraceCrossing n ⟨s, hs⟩
  have hnot : grimmettTraceLeftSecondExtensionEdge W ∉
      grimmettRectangleFreshExtensionEdgesThree n s := by
    simp only [grimmettRectangleFreshExtensionEdgesThree, dif_pos hs,
      grimmettRectangleFreshExtensionEdges, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨grimmettTraceLeftSecondExtensionEdge_ne_rightSecond W,
      grimmettTraceLeftSecondExtensionEdge_ne_left W,
      grimmettTraceLeftSecondExtensionEdge_ne_right W⟩
  rw [grimmettRectangleFreshExtensionEdgesFour, dif_pos hs,
    Finset.card_insert_of_notMem hnot,
    card_grimmettRectangleFreshExtensionEdgesThree n s hs]

/-- The four-fresh-edge extension event for an even Grimmett rectangle. -/
noncomputable def grimmettRectangleFreshCrossingEventFour (n : ℕ) :
    Set (EdgeConfiguration 2) :=
  adaptiveFreshOpenExtensionEvent (grimmettRectangleEdges n)
    (grimmettRectangleCrossingTraces n) (grimmettRectangleFreshExtensionEdgesFour n)

theorem measurableSet_grimmettRectangleFreshCrossingEventFour (n : ℕ) :
    MeasurableSet (grimmettRectangleFreshCrossingEventFour n) := by
  classical
  apply measurableSet_adaptiveFreshOpenExtensionEvent
  intro s hs
  exact (Finset.mem_filter.mp hs).1

set_option maxHeartbeats 800000 in
private theorem selectedGrimmettTraceExtendedWalkFour_isOpen
    {n : ℕ} {s : Finset SquareEdge} (hs : s ∈ grimmettRectangleCrossingTraces n)
    {omega : EdgeConfiguration 2}
    (hcyl : omega ∈ finiteCylinder (grimmettRectangleEdges n) s)
    (hfresh : omega ∈ openEdgeSetEvent 2 (grimmettRectangleFreshExtensionEdgesFour n s)) :
    walkIsOpen omega (grimmettTraceExtendedWalkFour
      (selectedGrimmettRectangleTraceCrossing n ⟨s, hs⟩)) := by
  classical
  let W := selectedGrimmettRectangleTraceCrossing n ⟨s, hs⟩
  have hWopen : walkIsOpen omega W.walk := by
    intro e he
    let ee : SquareEdge := ⟨e, W.walk.edges_subset_edgeSet he⟩
    have heE : ee ∈ grimmettRectangleEdges n :=
      W.edges_subset ((mem_walkEdgeFinset_iff W.walk ee).mpr he)
    exact (mem_finiteCylinder.mp hcyl ee heE).mpr (W.isOpen e he)
  have hleftSecondMem : grimmettTraceLeftSecondExtensionEdge W ∈
      grimmettRectangleFreshExtensionEdgesFour n s := by
    simp [grimmettRectangleFreshExtensionEdgesFour, hs, W]
  have hleftMem : grimmettTraceLeftExtensionEdge W ∈
      grimmettRectangleFreshExtensionEdgesFour n s := by
    simp [grimmettRectangleFreshExtensionEdgesFour,
      grimmettRectangleFreshExtensionEdgesThree,
      grimmettRectangleFreshExtensionEdges, hs, W]
  have hrightMem : grimmettTraceRightExtensionEdge W ∈
      grimmettRectangleFreshExtensionEdgesFour n s := by
    simp [grimmettRectangleFreshExtensionEdgesFour,
      grimmettRectangleFreshExtensionEdgesThree,
      grimmettRectangleFreshExtensionEdges, hs, W]
  have hrightSecondMem : grimmettTraceRightSecondExtensionEdge W ∈
      grimmettRectangleFreshExtensionEdgesFour n s := by
    simp [grimmettRectangleFreshExtensionEdgesFour,
      grimmettRectangleFreshExtensionEdgesThree, hs, W]
  have hleftSecond : walkIsOpen omega
      (SimpleGraph.Walk.cons
        (cubicGraph_adj_stepFrom (grimmettTraceLeftOuterVertex W)
          ((0 : Fin 2), false)).symm SimpleGraph.Walk.nil) := by
    intro e he
    simp only [SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil,
      List.mem_cons, List.not_mem_nil, or_false] at he
    subst e
    simpa [grimmettTraceLeftSecondExtensionEdge, cubicStepEdge, Sym2.eq_swap] using
      hfresh hleftSecondMem
  have hleft : walkIsOpen omega
      (SimpleGraph.Walk.cons
        (cubicGraph_adj_stepFrom W.start ((0 : Fin 2), false)).symm
        SimpleGraph.Walk.nil) := by
    intro e he
    simp only [SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil,
      List.mem_cons, List.not_mem_nil, or_false] at he
    subst e
    simpa [grimmettTraceLeftExtensionEdge, cubicStepEdge, Sym2.eq_swap] using
      hfresh hleftMem
  have hright : walkIsOpen omega
      (SimpleGraph.Walk.cons
        (cubicGraph_adj_stepFrom W.finish ((0 : Fin 2), true))
        SimpleGraph.Walk.nil) := by
    intro e he
    simp only [SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil,
      List.mem_cons, List.not_mem_nil, or_false] at he
    subst e
    simpa [grimmettTraceRightExtensionEdge, cubicStepEdge] using hfresh hrightMem
  have hrightSecond : walkIsOpen omega
      (SimpleGraph.Walk.cons
        (cubicGraph_adj_stepFrom (grimmettTraceRightOuterVertex W)
          ((0 : Fin 2), true)) SimpleGraph.Walk.nil) := by
    intro e he
    simp only [SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil,
      List.mem_cons, List.not_mem_nil, or_false] at he
    subst e
    simpa [grimmettTraceRightSecondExtensionEdge, cubicStepEdge] using
      hfresh hrightSecondMem
  change walkIsOpen omega (grimmettTraceExtendedWalkFour W)
  exact walkIsOpen_append hleftSecond
    (walkIsOpen_append
      (walkIsOpen_append hleft (walkIsOpen_append hWopen hright)) hrightSecond)

private theorem strictDual_grimmettTraceExtendedWalk_edge_bounds
    {n : ℕ} {s : Finset SquareEdge} (W : GrimmettRectangleTraceCrossing n s)
    {e : Sym2 SquareVertex} (he : e ∈ (grimmettTraceExtendedWalk W).edges)
    {z : SquareVertex} (hz : z ∈ e) :
    (-1 : ℤ) ≤ z 0 ∧ z 0 ≤ (n + 2 : ℕ) ∧ 0 ≤ z 1 ∧ z 1 ≤ (n : ℤ) := by
  classical
  simp only [grimmettTraceExtendedWalk, SimpleGraph.Walk.edges_append,
    SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [Sym2.mem_iff] at hz
    rcases hz with rfl | rfl
    · have hs := mem_grimmettRectangleLeft_iff.mp W.start_mem
      simp [grimmettTraceLeftOuterVertex, cubicStepFrom, cubicDirectionIncrement, hs]
      omega
    · have hs := mem_grimmettRectangleLeft_iff.mp W.start_mem
      simp [hs]
      omega
  · let ee : SquareEdge := ⟨e, W.walk.edges_subset_edgeSet he⟩
    have heE : ee ∈ grimmettRectangleEdges n :=
      W.edges_subset ((mem_walkEdgeFinset_iff W.walk ee).mpr he)
    have hzRect := endpoint_mem_grimmettRectangleVertices_of_edge_mem heE hz
    have hz' := mem_grimmettRectangleVertices_iff.mp hzRect
    omega
  · rcases he with he | he
    · subst e
      rw [Sym2.mem_iff] at hz
      rcases hz with rfl | rfl
      · have hf := mem_grimmettRectangleRight_iff.mp W.finish_mem
        simp [hf]
        omega
      · have hf := mem_grimmettRectangleRight_iff.mp W.finish_mem
        simp [cubicStepFrom, cubicDirectionIncrement, hf]
        omega
    · change e ∈ ([] : List (Sym2 SquareVertex)) at he
      simp at he

private theorem strictDual_grimmettTraceExtendedWalkThree_edge_bounds
    {n : ℕ} {s : Finset SquareEdge} (W : GrimmettRectangleTraceCrossing n s)
    {e : Sym2 SquareVertex} (he : e ∈ (grimmettTraceExtendedWalkThree W).edges)
    {z : SquareVertex} (hz : z ∈ e) :
    (-1 : ℤ) ≤ z 0 ∧ z 0 ≤ (n + 3 : ℕ) ∧ 0 ≤ z 1 ∧ z 1 ≤ (n : ℤ) := by
  simp only [grimmettTraceExtendedWalkThree, SimpleGraph.Walk.edges_append,
    SimpleGraph.Walk.edges_cons, List.mem_append, List.mem_cons] at he
  rcases he with he | he
  · have h := strictDual_grimmettTraceExtendedWalk_edge_bounds W he hz
    omega
  · rcases he with rfl | he
    · rw [Sym2.mem_iff] at hz
      have hf := mem_grimmettRectangleRight_iff.mp W.finish_mem
      rcases hz with rfl | rfl <;>
        simp [grimmettTraceRightOuterVertex, cubicStepFrom,
          cubicDirectionIncrement, hf] <;> omega
    · change e ∈ ([] : List (Sym2 SquareVertex)) at he
      simp at he

private theorem grimmettTraceExtendedWalkFour_edge_bounds
    {n : ℕ} {s : Finset SquareEdge} (W : GrimmettRectangleTraceCrossing n s)
    {e : Sym2 SquareVertex} (he : e ∈ (grimmettTraceExtendedWalkFour W).edges)
    {z : SquareVertex} (hz : z ∈ e) :
    (-2 : ℤ) ≤ z 0 ∧ z 0 ≤ (n + 3 : ℕ) ∧ 0 ≤ z 1 ∧ z 1 ≤ (n : ℤ) := by
  change e ∈ ((SimpleGraph.Walk.cons
      (cubicGraph_adj_stepFrom (grimmettTraceLeftOuterVertex W)
        ((0 : Fin 2), false)).symm SimpleGraph.Walk.nil).append
      (grimmettTraceExtendedWalkThree W)).edges at he
  rw [SimpleGraph.Walk.edges_append, List.mem_append] at he
  rcases he with hleft | hthree
  · have heq : e = s(grimmettTraceLeftSecondOuterVertex W,
        grimmettTraceLeftOuterVertex W) := by
      simpa only [SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil,
        List.mem_cons, List.not_mem_nil, or_false, Sym2.eq_swap] using hleft
    subst e
    rw [Sym2.mem_iff] at hz
    have hs := mem_grimmettRectangleLeft_iff.mp W.start_mem
    rcases hz with rfl | rfl <;>
      simp [grimmettTraceLeftSecondOuterVertex, grimmettTraceLeftOuterVertex,
        cubicStepFrom, cubicDirectionIncrement, hs] <;> omega
  · have h := strictDual_grimmettTraceExtendedWalkThree_edge_bounds W hthree hz
    omega

private theorem grimmettTraceExtendedWalkFour_support_bounds
    {n : ℕ} {s : Finset SquareEdge} (W : GrimmettRectangleTraceCrossing n s)
    {z : SquareVertex} (hz : z ∈ (grimmettTraceExtendedWalkFour W).support) :
    (-2 : ℤ) ≤ z 0 ∧ z 0 ≤ (n + 3 : ℕ) ∧ 0 ≤ z 1 ∧ z 1 ≤ (n : ℤ) := by
  have hnonNil : ¬(grimmettTraceExtendedWalkFour W).Nil := by
    apply SimpleGraph.Walk.not_nil_of_ne
    intro h
    have h0 := congrFun h 0
    have hs := mem_grimmettRectangleLeft_iff.mp W.start_mem
    have hf := mem_grimmettRectangleRight_iff.mp W.finish_mem
    simp [grimmettTraceLeftSecondOuterVertex, grimmettTraceLeftOuterVertex,
      grimmettTraceRightSecondOuterVertex, grimmettTraceRightOuterVertex,
      cubicStepFrom, cubicDirectionIncrement, hs, hf] at h0
    omega
  obtain ⟨e, he, hze⟩ :=
    (SimpleGraph.Walk.mem_support_iff_exists_mem_edges_of_not_nil hnonNil).mp hz
  exact grimmettTraceExtendedWalkFour_edge_bounds W he hze

@[simp]
private theorem strictDual_grimmettFreshSquareIso_apply_zero (l : ℕ) (z : SquareVertex) :
    grimmettFreshSquareIso l z 0 = z 0 + 1 := by
  simp [grimmettFreshSquareIso, cubicTranslate, cubicOrigin]

@[simp]
private theorem strictDual_grimmettFreshSquareIso_apply_one (l : ℕ) (z : SquareVertex) :
    grimmettFreshSquareIso l z 1 = z 1 - l := by
  simp [grimmettFreshSquareIso, cubicTranslate, cubicOrigin, sub_eq_add_neg]

private theorem mapped_grimmettTraceExtendedWalkFour_support_mem_frame
    {l : ℕ} {s : Finset SquareEdge} (W : GrimmettRectangleTraceCrossing (2 * l) s)
    {z : DualSquareVertex}
    (hz : z ∈ ((grimmettTraceExtendedWalkFour W).map
      (grimmettFreshSquareIso l).toHom).support) :
    z ∈ brLeftmostDualFaces (l + 2) := by
  rw [SimpleGraph.Walk.support_map] at hz
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hz
  have hb := grimmettTraceExtendedWalkFour_support_bounds W hu
  rw [mem_brLeftmostDualFaces_iff]
  change (-1 : ℤ) ≤ grimmettFreshSquareIso l u 0 ∧
    grimmettFreshSquareIso l u 0 ≤ 2 * ((l + 2 : ℕ) : ℤ) ∧
      -((l + 2 : ℕ) : ℤ) ≤ grimmettFreshSquareIso l u 1 ∧
        grimmettFreshSquareIso l u 1 < ((l + 2 : ℕ) : ℤ)
  rw [strictDual_grimmettFreshSquareIso_apply_zero,
    strictDual_grimmettFreshSquareIso_apply_one]
  omega

theorem one_thirty_second_le_grimmettRectangleFreshCrossingEventFour_half
    (l : ℕ) (hl : 0 < l) :
    1 / 32 ≤ (bernoulliBondMeasure 2 squareHalfDensity).real
      (grimmettRectangleFreshCrossingEventFour (2 * l)) := by
  classical
  have hT : grimmettRectangleCrossingTraces (2 * l) ⊆
      (grimmettRectangleEdges (2 * l)).powerset := by
    intro s hs
    exact (Finset.mem_filter.mp hs).1
  have hext := bernoulliBondMeasure_real_adaptiveFreshOpenExtensionEvent
    (k := 4) squareHalfDensity (grimmettRectangleEdges (2 * l))
    (grimmettRectangleCrossingTraces (2 * l)) hT
    (grimmettRectangleFreshExtensionEdgesFour (2 * l))
    (grimmettRectangleFreshExtensionEdgesFour_disjoint (2 * l))
    (card_grimmettRectangleFreshExtensionEdgesFour (2 * l))
  have hsum : 1 / 2 ≤
      ∑ s ∈ grimmettRectangleCrossingTraces (2 * l),
        finiteBernoulliWeight (grimmettRectangleEdges (2 * l)) (1 / 2) s := by
    have hfinite :=
      (dependsOn_grimmettRectangleCrossingEvent (2 * l)
        ).bernoulliBondMeasure_real_eq_finiteBernoulliProbability squareHalfDensity
    have hlower := half_le_grimmettRectangleCrossingProbability_even l hl
    rw [hfinite, finiteBernoulliProbability_eq_sum_filter] at hlower
    simpa [grimmettRectangleCrossingTraces, coe_squareHalfDensity] using hlower
  rw [grimmettRectangleFreshCrossingEventFour, hext, coe_squareHalfDensity]
  norm_num at hsum ⊢
  linarith

/-- At scale `n`, use the even trace rectangle of height `2 * (n - 2)`, translate it into
the dual frame, and pull it back through primal/dual complementation. -/
noncomputable def strictDualHorizontalCrossingEvent (n : ℕ) :
    Set (EdgeConfiguration 2) :=
  dualSquareConfiguration ⁻¹' cubicGraphIsoEvent (grimmettFreshSquareIso (n - 2))
    (grimmettRectangleFreshCrossingEventFour (2 * (n - 2)))

theorem measurableSet_strictDualHorizontalCrossingEvent (n : ℕ) :
    MeasurableSet (strictDualHorizontalCrossingEvent n) := by
  exact (measurableSet_cubicGraphIsoEvent _
    (measurableSet_grimmettRectangleFreshCrossingEventFour _)).preimage
      measurable_dualSquareConfiguration

/-- A shifted-dual open walk crossing the complete frame from its left exterior column to its
right exterior column. Dual openness means that every crossed primal edge is closed. -/
structure StrictDualHorizontalCrossingWitness
    (n : ℕ) (omega : EdgeConfiguration 2) where
  start : DualSquareVertex
  finish : DualSquareVertex
  walk : dualSquareGraph.Walk start finish
  start_zero : start 0 = -1
  finish_zero : finish 0 = 2 * (n : ℤ)
  support_subset : ∀ z ∈ walk.support, z ∈ brLeftmostDualFaces n
  isOpen : dualWalkIsOpen omega walk

namespace StrictDualHorizontalCrossingWitness

/-- Every dual edge of a strict crossing witnesses a closed crossed primal edge. -/
theorem crossedPrimalEdge_not_mem
    {n : ℕ} {omega : EdgeConfiguration 2}
    (C : StrictDualHorizontalCrossingWitness n omega)
    {e : Sym2 DualSquareVertex} (he : e ∈ C.walk.edges) :
    squareEdgeDualCrossingEquiv.symm ⟨e, C.walk.edges_subset_edgeSet he⟩ ∉ omega := by
  let ed : DualSquareEdge := ⟨e, C.walk.edges_subset_edgeSet he⟩
  have hedOpen : ed ∈ dualSquareConfiguration omega := C.isOpen e he
  exact (dualSquareConfiguration_open_iff omega ed).mp hedOpen

end StrictDualHorizontalCrossingWitness

/-- Membership in the finite event supplies the strict shifted-dual walk used in the parity
contradiction. -/
theorem exists_strictDualHorizontalCrossingWitness_of_mem
    {n : ℕ} (hn : 3 ≤ n) {omega : EdgeConfiguration 2}
    (homega : omega ∈ strictDualHorizontalCrossingEvent n) :
    Nonempty (StrictDualHorizontalCrossingWitness n omega) := by
  classical
  let l := n - 2
  change cubicGraphIsoConfigurationPullback (grimmettFreshSquareIso l)
      (dualSquareConfiguration omega) ∈
    grimmettRectangleFreshCrossingEventFour (2 * l) at homega
  simp only [grimmettRectangleFreshCrossingEventFour,
    adaptiveFreshOpenExtensionEvent, Set.mem_iUnion, Set.mem_inter_iff] at homega
  obtain ⟨s, hs, hcyl, hfresh⟩ := homega
  let W := selectedGrimmettRectangleTraceCrossing (2 * l) ⟨s, hs⟩
  let q := (grimmettTraceExtendedWalkFour W).map (grimmettFreshSquareIso l).toHom
  have hsource : walkIsOpen
      (cubicGraphIsoConfigurationPullback (grimmettFreshSquareIso l)
        (dualSquareConfiguration omega)) (grimmettTraceExtendedWalkFour W) :=
    selectedGrimmettTraceExtendedWalkFour_isOpen hs hcyl hfresh
  have hopen : dualWalkIsOpen omega q :=
    walkIsOpen_map_cubicGraphIso (grimmettFreshSquareIso l)
      (grimmettTraceExtendedWalkFour W) hsource
  have hstart : grimmettFreshSquareIso l (grimmettTraceLeftSecondOuterVertex W) 0 = -1 := by
    have hs' := mem_grimmettRectangleLeft_iff.mp W.start_mem
    simp [grimmettTraceLeftSecondOuterVertex, grimmettTraceLeftOuterVertex,
      cubicStepFrom, cubicDirectionIncrement, hs']
  have hfinish : grimmettFreshSquareIso l (grimmettTraceRightSecondOuterVertex W) 0 =
      2 * (n : ℤ) := by
    have hf' := mem_grimmettRectangleRight_iff.mp W.finish_mem
    simp [grimmettTraceRightSecondOuterVertex, grimmettTraceRightOuterVertex,
      cubicStepFrom, cubicDirectionIncrement, hf']
    dsimp [l]
    omega
  have hscale : l + 2 = n := by
    dsimp [l]
    omega
  refine ⟨{
    start := grimmettFreshSquareIso l (grimmettTraceLeftSecondOuterVertex W)
    finish := grimmettFreshSquareIso l (grimmettTraceRightSecondOuterVertex W)
    walk := q
    start_zero := hstart
    finish_zero := hfinish
    support_subset := ?_
    isOpen := hopen }⟩
  intro z hz
  have hzFrame := mapped_grimmettTraceExtendedWalkFour_support_mem_frame W hz
  simpa only [hscale] using hzFrame

/-- Strict dual horizontal crossings have a scale-uniform probability lower bound at the
self-dual density. -/
theorem one_thirty_second_le_strictDualHorizontalCrossingEvent_half
    {n : ℕ} (hn : 3 ≤ n) :
    1 / 32 ≤ (bernoulliBondMeasure 2 squareHalfDensity).real
      (strictDualHorizontalCrossingEvent n) := by
  let l := n - 2
  let μ := bernoulliBondMeasure 2 squareHalfDensity
  let D := (dualSquareConfiguration : EdgeConfiguration 2 → EdgeConfiguration 2)
  let A := cubicGraphIsoEvent (grimmettFreshSquareIso l)
    (grimmettRectangleFreshCrossingEventFour (2 * l))
  have hl : 0 < l := by omega
  have hA : MeasurableSet A :=
    measurableSet_cubicGraphIsoEvent _
      (measurableSet_grimmettRectangleFreshCrossingEventFour _)
  have hmap : μ.map D = μ := by
    have hsigma : σ squareHalfDensity = squareHalfDensity := by
      ext
      norm_num [squareHalfDensity]
    dsimp [μ, D]
    rw [bernoulliBondMeasure_map_dualSquareConfiguration, hsigma]
  change 1 / 32 ≤ μ.real (D ⁻¹' A)
  calc
    (1 / 32 : ℝ) ≤ μ.real
        (grimmettRectangleFreshCrossingEventFour (2 * l)) :=
      one_thirty_second_le_grimmettRectangleFreshCrossingEventFour_half l hl
    _ = μ.real A := by
      symm
      exact bernoulliBondMeasure_real_cubicGraphIsoEvent squareHalfDensity _
        (measurableSet_grimmettRectangleFreshCrossingEventFour _)
    _ = (μ.map D).real A := by rw [hmap]
    _ = μ.real (D ⁻¹' A) :=
      map_measureReal_apply measurable_dualSquareConfiguration hA

end Percolation
