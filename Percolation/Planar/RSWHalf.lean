import Percolation.Bernoulli.AdaptiveFreshExtension
import Percolation.Planar.SquareThreshold

/-!
# A uniform critical square-crossing lower bound

This file makes rigorous the fresh-edge extension immediately after Grimmett, Lemma 11.21.
For each finite crossing trace we select one left and one right endpoint and then require the two
outward edges to be open.  The choice is trace-dependent, but the adaptive fresh-extension lemma
shows that it costs exactly `p²`.  After translating the enlarged rectangle into a square, the
result is a boundary-edge-free RSW crossing.  The constant obtained here is `1/8`; Grimmett's
one-edge trimming improves it to `1/4`, but the uniform positive constant is the only input used
in the critical-point argument.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval Sym2

/-- A concrete crossing carried by a finite trace of Grimmett's rectangle. -/
structure GrimmettRectangleTraceCrossing (n : ℕ) (s : Finset SquareEdge) where
  start : SquareVertex
  finish : SquareVertex
  walk : squareGraph.Walk start finish
  start_mem : start ∈ grimmettRectangleLeft n
  finish_mem : finish ∈ grimmettRectangleRight n
  isOpen : walkIsOpen (↑s : EdgeConfiguration 2) walk
  edges_subset : walkEdgeFinset walk ⊆ grimmettRectangleEdges n

private theorem exists_grimmettRectangleTraceCrossing
    (n : ℕ) (s : {s // s ∈ grimmettRectangleCrossingTraces n}) :
    Nonempty (GrimmettRectangleTraceCrossing n s.1) := by
  classical
  have hs := (Finset.mem_filter.mp s.2).2
  change (↑s.1 : EdgeConfiguration 2) ∈ grimmettRectangleCrossingEvent n at hs
  simp only [grimmettRectangleCrossingEvent, Set.mem_iUnion] at hs
  obtain ⟨x, hx, y, hy, w, hwopen, hwedges⟩ := hs
  exact ⟨⟨x, y, w, hx, hy, hwopen, hwedges⟩⟩

/-- A deterministic selected crossing for each crossing trace. -/
noncomputable def selectedGrimmettRectangleTraceCrossing
    (n : ℕ) (s : {s // s ∈ grimmettRectangleCrossingTraces n}) :
    GrimmettRectangleTraceCrossing n s.1 :=
  Classical.choice (exists_grimmettRectangleTraceCrossing n s)

/-- The outward edge at the selected left endpoint. -/
def grimmettTraceLeftExtensionEdge
    {n : ℕ} {s : Finset SquareEdge} (W : GrimmettRectangleTraceCrossing n s) : SquareEdge :=
  cubicStepEdge W.start ((0 : Fin 2), false)

/-- The outward edge at the selected right endpoint. -/
def grimmettTraceRightExtensionEdge
    {n : ℕ} {s : Finset SquareEdge} (W : GrimmettRectangleTraceCrossing n s) : SquareEdge :=
  cubicStepEdge W.finish ((0 : Fin 2), true)

/-- The vertex one step immediately to the left of the selected crossing. -/
def grimmettTraceLeftOuterVertex
    {n : ℕ} {s : Finset SquareEdge} (W : GrimmettRectangleTraceCrossing n s) :
    SquareVertex :=
  cubicStepFrom W.start ((0 : Fin 2), false)

/-- The vertex one step immediately to the right of the selected crossing. -/
def grimmettTraceRightOuterVertex
    {n : ℕ} {s : Finset SquareEdge} (W : GrimmettRectangleTraceCrossing n s) :
    SquareVertex :=
  cubicStepFrom W.finish ((0 : Fin 2), true)

/-- The selected crossing with one outward edge attached at each end. -/
def grimmettTraceExtendedWalk
    {n : ℕ} {s : Finset SquareEdge} (W : GrimmettRectangleTraceCrossing n s) :
    squareGraph.Walk (grimmettTraceLeftOuterVertex W) (grimmettTraceRightOuterVertex W) :=
  let leftStep : squareGraph.Walk (grimmettTraceLeftOuterVertex W) W.start :=
    SimpleGraph.Walk.cons (cubicGraph_adj_stepFrom W.start ((0 : Fin 2), false)).symm
      SimpleGraph.Walk.nil
  let rightStep : squareGraph.Walk W.finish (grimmettTraceRightOuterVertex W) :=
    SimpleGraph.Walk.cons (cubicGraph_adj_stepFrom W.finish ((0 : Fin 2), true))
      SimpleGraph.Walk.nil
  leftStep.append (W.walk.append rightStep)

/-- The two trace-dependent fresh edges.  It is empty off the crossing trace family. -/
noncomputable def grimmettRectangleFreshExtensionEdges
    (n : ℕ) (s : Finset SquareEdge) : Finset SquareEdge := by
  classical
  exact if hs : s ∈ grimmettRectangleCrossingTraces n then
    let W := selectedGrimmettRectangleTraceCrossing n ⟨s, hs⟩
    {grimmettTraceLeftExtensionEdge W, grimmettTraceRightExtensionEdge W}
  else ∅

private theorem grimmettTraceLeftExtensionEdge_not_mem
    {n : ℕ} {s : Finset SquareEdge} (W : GrimmettRectangleTraceCrossing n s) :
    grimmettTraceLeftExtensionEdge W ∉ grimmettRectangleEdges n := by
  intro he
  let z := cubicStepFrom W.start ((0 : Fin 2), false)
  have hzEdge : z ∈ (grimmettTraceLeftExtensionEdge W : Sym2 SquareVertex) := by
    simp [z, grimmettTraceLeftExtensionEdge, cubicStepEdge]
  have hzRect := endpoint_mem_grimmettRectangleVertices_of_edge_mem he hzEdge
  have hz0 := (mem_grimmettRectangleVertices_iff.mp hzRect).1
  have hs0 := (mem_grimmettRectangleLeft_iff.mp W.start_mem).1
  simp [z, cubicStepFrom, cubicDirectionIncrement, hs0] at hz0

private theorem grimmettTraceRightExtensionEdge_not_mem
    {n : ℕ} {s : Finset SquareEdge} (W : GrimmettRectangleTraceCrossing n s) :
    grimmettTraceRightExtensionEdge W ∉ grimmettRectangleEdges n := by
  intro he
  let z := cubicStepFrom W.finish ((0 : Fin 2), true)
  have hzEdge : z ∈ (grimmettTraceRightExtensionEdge W : Sym2 SquareVertex) := by
    simp [z, grimmettTraceRightExtensionEdge, cubicStepEdge]
  have hzRect := endpoint_mem_grimmettRectangleVertices_of_edge_mem he hzEdge
  have hz0 := (mem_grimmettRectangleVertices_iff.mp hzRect).2.1
  have hs0 := (mem_grimmettRectangleRight_iff.mp W.finish_mem).1
  simp [z, cubicStepFrom, cubicDirectionIncrement, hs0] at hz0

private theorem grimmettTraceExtensionEdges_ne
    {n : ℕ} {s : Finset SquareEdge} (W : GrimmettRectangleTraceCrossing n s) :
    grimmettTraceLeftExtensionEdge W ≠ grimmettTraceRightExtensionEdge W := by
  intro h
  let z := cubicStepFrom W.start ((0 : Fin 2), false)
  have hzLeft : z ∈ (grimmettTraceLeftExtensionEdge W : Sym2 SquareVertex) := by
    simp [z, grimmettTraceLeftExtensionEdge, cubicStepEdge]
  have hzRight : z ∈ (grimmettTraceRightExtensionEdge W : Sym2 SquareVertex) := by
    rw [← h]
    exact hzLeft
  rw [grimmettTraceRightExtensionEdge, cubicStepEdge, Sym2.mem_iff] at hzRight
  have hs0 := (mem_grimmettRectangleLeft_iff.mp W.start_mem).1
  have hf0 := (mem_grimmettRectangleRight_iff.mp W.finish_mem).1
  rcases hzRight with hz | hz
  · have := congrFun hz 0
    simp [z, cubicStepFrom, cubicDirectionIncrement, hs0, hf0] at this
    omega
  · have := congrFun hz 0
    simp [z, cubicStepFrom, cubicDirectionIncrement, hs0, hf0] at this
    omega

theorem grimmettRectangleFreshExtensionEdges_disjoint
    (n : ℕ) (s : Finset SquareEdge) (hs : s ∈ grimmettRectangleCrossingTraces n) :
    Disjoint (grimmettRectangleFreshExtensionEdges n s) (grimmettRectangleEdges n) := by
  classical
  let W := selectedGrimmettRectangleTraceCrossing n ⟨s, hs⟩
  rw [Finset.disjoint_left]
  intro e he hE
  simp only [grimmettRectangleFreshExtensionEdges, dif_pos hs,
    Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl
  · exact grimmettTraceLeftExtensionEdge_not_mem W hE
  · exact grimmettTraceRightExtensionEdge_not_mem W hE

theorem card_grimmettRectangleFreshExtensionEdges
    (n : ℕ) (s : Finset SquareEdge) (hs : s ∈ grimmettRectangleCrossingTraces n) :
    (grimmettRectangleFreshExtensionEdges n s).card = 2 := by
  classical
  have hne := grimmettTraceExtensionEdges_ne
    (selectedGrimmettRectangleTraceCrossing n ⟨s, hs⟩)
  simp [grimmettRectangleFreshExtensionEdges, hs, hne]

set_option maxHeartbeats 800000 in
private theorem selectedGrimmettTraceExtendedWalk_isOpen
    {n : ℕ} {s : Finset SquareEdge} (hs : s ∈ grimmettRectangleCrossingTraces n)
    {omega : EdgeConfiguration 2}
    (hcyl : omega ∈ finiteCylinder (grimmettRectangleEdges n) s)
    (hfresh : omega ∈ openEdgeSetEvent 2 (grimmettRectangleFreshExtensionEdges n s)) :
    walkIsOpen omega (grimmettTraceExtendedWalk
      (selectedGrimmettRectangleTraceCrossing n ⟨s, hs⟩)) := by
  classical
  let W := selectedGrimmettRectangleTraceCrossing n ⟨s, hs⟩
  have hWopen : walkIsOpen omega W.walk := by
    intro e he
    let ee : SquareEdge := ⟨e, W.walk.edges_subset_edgeSet he⟩
    have heE : ee ∈ grimmettRectangleEdges n :=
      W.edges_subset ((mem_walkEdgeFinset_iff W.walk ee).mpr he)
    exact (mem_finiteCylinder.mp hcyl ee heE).mpr (W.isOpen e he)
  have hleftMem : grimmettTraceLeftExtensionEdge W ∈
      grimmettRectangleFreshExtensionEdges n s := by
    simp [grimmettRectangleFreshExtensionEdges, hs, W]
  have hrightMem : grimmettTraceRightExtensionEdge W ∈
      grimmettRectangleFreshExtensionEdges n s := by
    simp [grimmettRectangleFreshExtensionEdges, hs, W]
  have hleftOpen : walkIsOpen omega
      (SimpleGraph.Walk.cons
        (cubicGraph_adj_stepFrom W.start ((0 : Fin 2), false)).symm
        SimpleGraph.Walk.nil) := by
    intro e he
    simp only [SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil,
      List.mem_cons, List.not_mem_nil, or_false] at he
    subst e
    simpa [grimmettTraceLeftExtensionEdge, cubicStepEdge, Sym2.eq_swap] using
      hfresh hleftMem
  have hrightOpen : walkIsOpen omega
      (SimpleGraph.Walk.cons
        (cubicGraph_adj_stepFrom W.finish ((0 : Fin 2), true))
        SimpleGraph.Walk.nil) := by
    intro e he
    simp only [SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil,
      List.mem_cons, List.not_mem_nil, or_false] at he
    subst e
    simpa [grimmettTraceRightExtensionEdge, cubicStepEdge] using hfresh hrightMem
  change walkIsOpen omega (grimmettTraceExtendedWalk W)
  exact walkIsOpen_append hleftOpen (walkIsOpen_append hWopen hrightOpen)

private theorem grimmettTraceExtendedWalk_edge_bounds
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
        simp [grimmettTraceRightOuterVertex, cubicStepFrom, cubicDirectionIncrement, hf]
        omega
    · change e ∈ ([] : List (Sym2 SquareVertex)) at he
      simp at he

private theorem grimmettTraceExtendedWalk_edge_has_rectangle_endpoint
    {n : ℕ} {s : Finset SquareEdge} (W : GrimmettRectangleTraceCrossing n s)
    {e : Sym2 SquareVertex} (he : e ∈ (grimmettTraceExtendedWalk W).edges) :
    ∃ z ∈ e, z ∈ grimmettRectangleVertices n := by
  classical
  simp only [grimmettTraceExtendedWalk, SimpleGraph.Walk.edges_append,
    SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    have hs := mem_grimmettRectangleLeft_iff.mp W.start_mem
    exact ⟨W.start, by simp, mem_grimmettRectangleVertices_iff.mpr
      ⟨hs.1.ge, by omega, hs.2.1, hs.2.2⟩⟩
  · let ee : SquareEdge := ⟨e, W.walk.edges_subset_edgeSet he⟩
    have heE : ee ∈ grimmettRectangleEdges n :=
      W.edges_subset ((mem_walkEdgeFinset_iff W.walk ee).mpr he)
    exact ⟨e.out.1, Sym2.out_fst_mem e,
      endpoint_mem_grimmettRectangleVertices_of_edge_mem heE (Sym2.out_fst_mem e)⟩
  · rcases he with he | he
    · subst e
      have hf := mem_grimmettRectangleRight_iff.mp W.finish_mem
      exact ⟨W.finish, by simp, mem_grimmettRectangleVertices_iff.mpr
        ⟨by omega, hf.1.le, hf.2.1, hf.2.2⟩⟩
    · change e ∈ ([] : List (Sym2 SquareVertex)) at he
      simp at he

private theorem grimmettTraceExtendedWalk_support_bounds
    {n : ℕ} {s : Finset SquareEdge} (W : GrimmettRectangleTraceCrossing n s)
    {z : SquareVertex} (hz : z ∈ (grimmettTraceExtendedWalk W).support) :
    (-1 : ℤ) ≤ z 0 ∧ z 0 ≤ (n + 2 : ℕ) ∧ 0 ≤ z 1 ∧ z 1 ≤ (n : ℤ) := by
  have hnonNil : ¬(grimmettTraceExtendedWalk W).Nil := by
    simp [grimmettTraceExtendedWalk]
  obtain ⟨e, he, hze⟩ :=
    (SimpleGraph.Walk.mem_support_iff_exists_mem_edges_of_not_nil hnonNil).mp hz
  exact grimmettTraceExtendedWalk_edge_bounds W he hze

/-- Translate the lower-left corner `(-1,l)` of an extended Grimmett crossing to the origin. -/
def grimmettFreshSquareIso (l : ℕ) : squareGraph ≃g squareGraph :=
  cubicTranslationIso (squareVertex (-1) l) cubicOrigin

@[simp]
private theorem grimmettFreshSquareIso_apply_zero (l : ℕ) (z : SquareVertex) :
    grimmettFreshSquareIso l z 0 = z 0 + 1 := by
  simp [grimmettFreshSquareIso, cubicTranslate, cubicOrigin]

@[simp]
private theorem grimmettFreshSquareIso_apply_one (l : ℕ) (z : SquareVertex) :
    grimmettFreshSquareIso l z 1 = z 1 - l := by
  simp [grimmettFreshSquareIso, cubicTranslate, cubicOrigin, sub_eq_add_neg]

/-- The adaptive extension event based on the exact half-density crossing traces. -/
noncomputable def grimmettRectangleFreshCrossingEvent (n : ℕ) :
    Set (EdgeConfiguration 2) :=
  adaptiveFreshOpenExtensionEvent (grimmettRectangleEdges n)
    (grimmettRectangleCrossingTraces n) (grimmettRectangleFreshExtensionEdges n)

theorem measurableSet_grimmettRectangleFreshCrossingEvent (n : ℕ) :
    MeasurableSet (grimmettRectangleFreshCrossingEvent n) := by
  classical
  apply measurableSet_adaptiveFreshOpenExtensionEvent
  intro s hs
  exact (Finset.mem_filter.mp hs).1

/-- A fresh-edge crossing, transported into the boundary-edge-free RSW square at the next
integer scale. -/
noncomputable def rswHalfSquareWitnessEvent (l : ℕ) : Set (EdgeConfiguration 2) :=
  cubicGraphIsoEvent (grimmettFreshSquareIso l)
    (grimmettRectangleFreshCrossingEvent (2 * l - 1))

private theorem mapped_grimmettTraceExtendedWalk_support_mem_square
    {l : ℕ} (hl : 1 ≤ l) {s : Finset SquareEdge}
    (W : GrimmettRectangleTraceCrossing (2 * l - 1) s) {z : SquareVertex}
    (hz : z ∈ ((grimmettTraceExtendedWalk W).map
      (grimmettFreshSquareIso l).toHom).support) :
    z ∈ squareRectangleVertices (2 * (l + 1)) (l + 1) := by
  rw [SimpleGraph.Walk.support_map] at hz
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hz
  have hb := grimmettTraceExtendedWalk_support_bounds W hu
  rw [mem_squareRectangleVertices_iff]
  change 0 ≤ grimmettFreshSquareIso l u 0 ∧
    grimmettFreshSquareIso l u 0 ≤ (2 * (l + 1) : ℕ) ∧
    -(l + 1 : ℕ) ≤ grimmettFreshSquareIso l u 1 ∧
    grimmettFreshSquareIso l u 1 ≤ (l + 1 : ℕ)
  simp only [grimmettFreshSquareIso_apply_zero, grimmettFreshSquareIso_apply_one]
  omega

private theorem mapped_grimmettTraceExtendedWalk_edge_not_boundary
    {l : ℕ} (hl : 1 ≤ l) {s : Finset SquareEdge}
    (W : GrimmettRectangleTraceCrossing (2 * l - 1) s)
    {e : Sym2 SquareVertex}
    (he : e ∈ ((grimmettTraceExtendedWalk W).map
      (grimmettFreshSquareIso l).toHom).edges) :
    ¬(squareRectangleBoundaryVertex (2 * (l + 1)) (l + 1) e.out.1 ∧
      squareRectangleBoundaryVertex (2 * (l + 1)) (l + 1) e.out.2) := by
  rw [SimpleGraph.Walk.edges_map] at he
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp he
  obtain ⟨u, huf, huRect⟩ :=
    grimmettTraceExtendedWalk_edge_has_rectangle_endpoint W hf
  have hu' := mem_grimmettRectangleVertices_iff.mp huRect
  have hnot : ¬squareRectangleBoundaryVertex (2 * (l + 1)) (l + 1)
      (grimmettFreshSquareIso l u) := by
    simp only [squareRectangleBoundaryVertex, grimmettFreshSquareIso_apply_zero,
      grimmettFreshSquareIso_apply_one]
    omega
  intro hboundary
  apply hnot
  have humap : grimmettFreshSquareIso l u ∈
      Sym2.map (grimmettFreshSquareIso l) f :=
    Sym2.mem_map.mpr ⟨u, huf, rfl⟩
  rw [← (Sym2.map (grimmettFreshSquareIso l) f).out_eq, Sym2.mem_iff] at humap
  rcases humap with humap | humap
  · simpa [humap] using hboundary.1
  · simpa [humap] using hboundary.2

private theorem mapped_grimmettTraceExtendedWalk_edges_subset_boundaryFreeSquare
    {l : ℕ} (hl : 1 ≤ l) {s : Finset SquareEdge}
    (W : GrimmettRectangleTraceCrossing (2 * l - 1) s) :
    walkEdgeFinset ((grimmettTraceExtendedWalk W).map
        (grimmettFreshSquareIso l).toHom) ⊆
      squareBoundaryFreeRectangleEdges (2 * (l + 1)) (l + 1) := by
  classical
  let q := (grimmettTraceExtendedWalk W).map (grimmettFreshSquareIso l).toHom
  have hrect : walkEdgeFinset q ⊆ squareRectangleEdges (2 * (l + 1)) (l + 1) :=
    walkEdgeFinset_subset_squareRectangleEdges_of_support q
      (fun z hz ↦ mapped_grimmettTraceExtendedWalk_support_mem_square hl W hz)
  intro e he
  rw [squareBoundaryFreeRectangleEdges, Finset.mem_filter]
  refine ⟨hrect he, ?_⟩
  exact mapped_grimmettTraceExtendedWalk_edge_not_boundary hl W
    ((mem_walkEdgeFinset_iff q e).mp he)

/-- Every transported fresh-edge witness is a literal boundary-edge-free square crossing. -/
theorem rswHalfSquareWitnessEvent_subset (l : ℕ) (hl : 1 ≤ l) :
    rswHalfSquareWitnessEvent l ⊆ rswSquareCrossingEvent (l + 1) := by
  classical
  intro omega homega
  change cubicGraphIsoConfigurationPullback (grimmettFreshSquareIso l) omega ∈
    grimmettRectangleFreshCrossingEvent (2 * l - 1) at homega
  simp only [grimmettRectangleFreshCrossingEvent,
    adaptiveFreshOpenExtensionEvent, Set.mem_iUnion, Set.mem_inter_iff] at homega
  obtain ⟨s, hs, hcyl, hfresh⟩ := homega
  let W := selectedGrimmettRectangleTraceCrossing (2 * l - 1) ⟨s, hs⟩
  let q := (grimmettTraceExtendedWalk W).map (grimmettFreshSquareIso l).toHom
  have hsource : walkIsOpen
      (cubicGraphIsoConfigurationPullback (grimmettFreshSquareIso l) omega)
      (grimmettTraceExtendedWalk W) := by
    exact selectedGrimmettTraceExtendedWalk_isOpen hs hcyl hfresh
  have hopen : walkIsOpen omega q :=
    walkIsOpen_map_cubicGraphIso (grimmettFreshSquareIso l)
      (grimmettTraceExtendedWalk W) hsource
  have hleft : grimmettFreshSquareIso l (grimmettTraceLeftOuterVertex W) ∈
      squareRectangleLeft (2 * (l + 1)) (l + 1) := by
    rw [mem_squareRectangleLeft_iff]
    have hs' := mem_grimmettRectangleLeft_iff.mp W.start_mem
    simp only [grimmettFreshSquareIso_apply_zero, grimmettFreshSquareIso_apply_one]
    simp [grimmettTraceLeftOuterVertex, cubicStepFrom, cubicDirectionIncrement, hs']
    omega
  have hright : grimmettFreshSquareIso l (grimmettTraceRightOuterVertex W) ∈
      squareRectangleRight (2 * (l + 1)) (l + 1) := by
    rw [mem_squareRectangleRight_iff]
    have hf' := mem_grimmettRectangleRight_iff.mp W.finish_mem
    simp only [grimmettFreshSquareIso_apply_zero, grimmettFreshSquareIso_apply_one]
    simp [grimmettTraceRightOuterVertex, cubicStepFrom, cubicDirectionIncrement, hf']
    omega
  simp only [rswSquareCrossingEvent, rswRectangleCrossingEvent,
    squareBoundaryFreeRectangleCrossingEvent, Set.mem_iUnion]
  refine ⟨grimmettFreshSquareIso l (grimmettTraceLeftOuterVertex W), ?_,
    grimmettFreshSquareIso l (grimmettTraceRightOuterVertex W), ?_, q, hopen, ?_⟩
  · simpa [Nat.mul_assoc] using hleft
  · simpa [Nat.mul_assoc] using hright
  · simpa [q, Nat.mul_assoc] using
      mapped_grimmettTraceExtendedWalk_edges_subset_boundaryFreeSquare hl W

def grimmettTraceRightSecondExtensionEdge
    {n : ℕ} {s : Finset SquareEdge} (W : GrimmettRectangleTraceCrossing n s) : SquareEdge :=
  cubicStepEdge (grimmettTraceRightOuterVertex W) ((0 : Fin 2), true)

/-- The endpoint two steps to the right of a selected Grimmett crossing. -/
def grimmettTraceRightSecondOuterVertex
    {n : ℕ} {s : Finset SquareEdge} (W : GrimmettRectangleTraceCrossing n s) :
    SquareVertex :=
  cubicStepFrom (grimmettTraceRightOuterVertex W) ((0 : Fin 2), true)

/-- The selected crossing with one fresh edge on the left and two on the right. -/
def grimmettTraceExtendedWalkThree
    {n : ℕ} {s : Finset SquareEdge} (W : GrimmettRectangleTraceCrossing n s) :
    squareGraph.Walk (grimmettTraceLeftOuterVertex W)
      (grimmettTraceRightSecondOuterVertex W) :=
  (grimmettTraceExtendedWalk W).append
    (SimpleGraph.Walk.cons
      (cubicGraph_adj_stepFrom (grimmettTraceRightOuterVertex W) ((0 : Fin 2), true))
      SimpleGraph.Walk.nil)

/-- The three trace-dependent fresh edges used by the even-rectangle variant. -/
noncomputable def grimmettRectangleFreshExtensionEdgesThree
    (n : ℕ) (s : Finset SquareEdge) : Finset SquareEdge := by
  classical
  exact if hs : s ∈ grimmettRectangleCrossingTraces n then
    let W := selectedGrimmettRectangleTraceCrossing n ⟨s, hs⟩
    insert (grimmettTraceRightSecondExtensionEdge W)
      (grimmettRectangleFreshExtensionEdges n s)
  else ∅

private theorem grimmettTraceRightSecondExtensionEdge_not_mem
    {n : ℕ} {s : Finset SquareEdge} (W : GrimmettRectangleTraceCrossing n s) :
    grimmettTraceRightSecondExtensionEdge W ∉ grimmettRectangleEdges n := by
  intro he
  have hzEdge : grimmettTraceRightSecondOuterVertex W ∈
      (grimmettTraceRightSecondExtensionEdge W : Sym2 SquareVertex) := by
    simp [grimmettTraceRightSecondOuterVertex,
      grimmettTraceRightSecondExtensionEdge, cubicStepEdge]
  have hzRect := endpoint_mem_grimmettRectangleVertices_of_edge_mem he hzEdge
  have hz0 := (mem_grimmettRectangleVertices_iff.mp hzRect).2.1
  have hf0 := (mem_grimmettRectangleRight_iff.mp W.finish_mem).1
  simp [grimmettTraceRightSecondOuterVertex, grimmettTraceRightOuterVertex,
    cubicStepFrom, cubicDirectionIncrement, hf0] at hz0

private theorem grimmettTraceRightSecondExtensionEdge_ne_left
    {n : ℕ} {s : Finset SquareEdge} (W : GrimmettRectangleTraceCrossing n s) :
    grimmettTraceRightSecondExtensionEdge W ≠ grimmettTraceLeftExtensionEdge W := by
  intro h
  have hz : grimmettTraceRightSecondOuterVertex W ∈
      (grimmettTraceRightSecondExtensionEdge W : Sym2 SquareVertex) := by
    simp [grimmettTraceRightSecondOuterVertex,
      grimmettTraceRightSecondExtensionEdge, cubicStepEdge]
  rw [h, grimmettTraceLeftExtensionEdge, cubicStepEdge, Sym2.mem_iff] at hz
  have hs0 := (mem_grimmettRectangleLeft_iff.mp W.start_mem).1
  have hf0 := (mem_grimmettRectangleRight_iff.mp W.finish_mem).1
  rcases hz with hz | hz
  · have hz0 := congrFun hz 0
    simp [grimmettTraceRightSecondOuterVertex, grimmettTraceRightOuterVertex,
      cubicStepFrom, cubicDirectionIncrement, hs0, hf0] at hz0
    omega
  · have hz0 := congrFun hz 0
    simp [grimmettTraceRightSecondOuterVertex, grimmettTraceRightOuterVertex,
      cubicStepFrom, cubicDirectionIncrement, hs0, hf0] at hz0
    omega

private theorem grimmettTraceRightSecondExtensionEdge_ne_right
    {n : ℕ} {s : Finset SquareEdge} (W : GrimmettRectangleTraceCrossing n s) :
    grimmettTraceRightSecondExtensionEdge W ≠ grimmettTraceRightExtensionEdge W := by
  intro h
  have hz : grimmettTraceRightSecondOuterVertex W ∈
      (grimmettTraceRightSecondExtensionEdge W : Sym2 SquareVertex) := by
    simp [grimmettTraceRightSecondOuterVertex,
      grimmettTraceRightSecondExtensionEdge, cubicStepEdge]
  rw [h, grimmettTraceRightExtensionEdge, cubicStepEdge, Sym2.mem_iff] at hz
  have hf0 := (mem_grimmettRectangleRight_iff.mp W.finish_mem).1
  rcases hz with hz | hz
  · have hz0 := congrFun hz 0
    simp [grimmettTraceRightSecondOuterVertex, grimmettTraceRightOuterVertex,
      cubicStepFrom, cubicDirectionIncrement, hf0] at hz0
    omega
  · have hz0 := congrFun hz 0
    simp [grimmettTraceRightSecondOuterVertex, grimmettTraceRightOuterVertex,
      cubicStepFrom, cubicDirectionIncrement, hf0] at hz0

theorem grimmettRectangleFreshExtensionEdgesThree_disjoint
    (n : ℕ) (s : Finset SquareEdge) (hs : s ∈ grimmettRectangleCrossingTraces n) :
    Disjoint (grimmettRectangleFreshExtensionEdgesThree n s)
      (grimmettRectangleEdges n) := by
  classical
  let W := selectedGrimmettRectangleTraceCrossing n ⟨s, hs⟩
  rw [Finset.disjoint_left]
  intro e he hE
  simp only [grimmettRectangleFreshExtensionEdgesThree, dif_pos hs,
    Finset.mem_insert] at he
  rcases he with rfl | he
  · exact grimmettTraceRightSecondExtensionEdge_not_mem W hE
  · exact (Finset.disjoint_left.mp
      (grimmettRectangleFreshExtensionEdges_disjoint n s hs)) he hE

theorem card_grimmettRectangleFreshExtensionEdgesThree
    (n : ℕ) (s : Finset SquareEdge) (hs : s ∈ grimmettRectangleCrossingTraces n) :
    (grimmettRectangleFreshExtensionEdgesThree n s).card = 3 := by
  classical
  let W := selectedGrimmettRectangleTraceCrossing n ⟨s, hs⟩
  have hnot : grimmettTraceRightSecondExtensionEdge W ∉
      grimmettRectangleFreshExtensionEdges n s := by
    simp only [grimmettRectangleFreshExtensionEdges, dif_pos hs,
      Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨grimmettTraceRightSecondExtensionEdge_ne_left W,
      grimmettTraceRightSecondExtensionEdge_ne_right W⟩
  rw [grimmettRectangleFreshExtensionEdgesThree, dif_pos hs,
    Finset.card_insert_of_notMem hnot,
    card_grimmettRectangleFreshExtensionEdges n s hs]

set_option maxHeartbeats 800000 in
theorem selectedGrimmettTraceExtendedWalkThree_isOpen
    {n : ℕ} {s : Finset SquareEdge} (hs : s ∈ grimmettRectangleCrossingTraces n)
    {ω : EdgeConfiguration 2}
    (hcyl : ω ∈ finiteCylinder (grimmettRectangleEdges n) s)
    (hfresh : ω ∈ openEdgeSetEvent 2
      (grimmettRectangleFreshExtensionEdgesThree n s)) :
    walkIsOpen ω (grimmettTraceExtendedWalkThree
      (selectedGrimmettRectangleTraceCrossing n ⟨s, hs⟩)) := by
  classical
  let W := selectedGrimmettRectangleTraceCrossing n ⟨s, hs⟩
  have hfreshOld : ω ∈ openEdgeSetEvent 2
      (grimmettRectangleFreshExtensionEdges n s) := by
    intro e he
    apply hfresh
    simp [grimmettRectangleFreshExtensionEdgesThree, hs, he]
  have hOld : walkIsOpen ω (grimmettTraceExtendedWalk W) :=
    selectedGrimmettTraceExtendedWalk_isOpen hs hcyl hfreshOld
  have hsecondMem : grimmettTraceRightSecondExtensionEdge W ∈
      grimmettRectangleFreshExtensionEdgesThree n s := by
    simp [grimmettRectangleFreshExtensionEdgesThree, hs, W]
  have hsecond : walkIsOpen ω
      (SimpleGraph.Walk.cons
        (cubicGraph_adj_stepFrom (grimmettTraceRightOuterVertex W)
          ((0 : Fin 2), true)) SimpleGraph.Walk.nil) := by
    intro e he
    simp only [SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil,
      List.mem_cons, List.not_mem_nil, or_false] at he
    subst e
    simpa [grimmettTraceRightSecondExtensionEdge, cubicStepEdge] using
      hfresh hsecondMem
  exact walkIsOpen_append hOld hsecond

private theorem grimmettTraceExtendedWalkThree_edge_bounds
    {n : ℕ} {s : Finset SquareEdge} (W : GrimmettRectangleTraceCrossing n s)
    {e : Sym2 SquareVertex} (he : e ∈ (grimmettTraceExtendedWalkThree W).edges)
    {z : SquareVertex} (hz : z ∈ e) :
    (-1 : ℤ) ≤ z 0 ∧ z 0 ≤ (n + 3 : ℕ) ∧ 0 ≤ z 1 ∧ z 1 ≤ (n : ℤ) := by
  simp only [grimmettTraceExtendedWalkThree, SimpleGraph.Walk.edges_append,
    SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · have h := grimmettTraceExtendedWalk_edge_bounds W he hz
    omega
  · rcases he with rfl | he
    · rw [Sym2.mem_iff] at hz
      have hf := mem_grimmettRectangleRight_iff.mp W.finish_mem
      rcases hz with rfl | rfl <;>
        simp [grimmettTraceRightSecondOuterVertex, grimmettTraceRightOuterVertex,
          cubicStepFrom, cubicDirectionIncrement, hf] <;> omega
    · change e ∈ ([] : List (Sym2 SquareVertex)) at he
      simp at he

theorem grimmettTraceExtendedWalkThree_support_bounds
    {n : ℕ} {s : Finset SquareEdge} (W : GrimmettRectangleTraceCrossing n s)
    {z : SquareVertex} (hz : z ∈ (grimmettTraceExtendedWalkThree W).support) :
    (-1 : ℤ) ≤ z 0 ∧ z 0 ≤ (n + 3 : ℕ) ∧ 0 ≤ z 1 ∧ z 1 ≤ (n : ℤ) := by
  have hnonNil : ¬(grimmettTraceExtendedWalkThree W).Nil := by
    simp [grimmettTraceExtendedWalkThree, grimmettTraceExtendedWalk]
  obtain ⟨e, he, hze⟩ :=
    (SimpleGraph.Walk.mem_support_iff_exists_mem_edges_of_not_nil hnonNil).mp hz
  exact grimmettTraceExtendedWalkThree_edge_bounds W he hze

/-- The three-edge adaptive extension event for an even Grimmett rectangle. -/
noncomputable def grimmettRectangleFreshCrossingEventThree (n : ℕ) :
    Set (EdgeConfiguration 2) :=
  adaptiveFreshOpenExtensionEvent (grimmettRectangleEdges n)
    (grimmettRectangleCrossingTraces n) (grimmettRectangleFreshExtensionEdgesThree n)

theorem measurableSet_grimmettRectangleFreshCrossingEventThree (n : ℕ) :
    MeasurableSet (grimmettRectangleFreshCrossingEventThree n) := by
  classical
  apply measurableSet_adaptiveFreshOpenExtensionEvent
  intro s hs
  exact (Finset.mem_filter.mp hs).1

/-- The even-source witness, transported into the boundary-free RSW square two scales up. -/
noncomputable def rswHalfSquareWitnessEventThree (l : ℕ) : Set (EdgeConfiguration 2) :=
  cubicGraphIsoEvent (grimmettFreshSquareIso l)
    (grimmettRectangleFreshCrossingEventThree (2 * l))

private theorem mapped_grimmettTraceExtendedWalkThree_support_mem_square
    {l : ℕ} {s : Finset SquareEdge}
    (W : GrimmettRectangleTraceCrossing (2 * l) s) {z : SquareVertex}
    (hz : z ∈ ((grimmettTraceExtendedWalkThree W).map
      (grimmettFreshSquareIso l).toHom).support) :
    z ∈ squareRectangleVertices (2 * (l + 2)) (l + 2) := by
  rw [SimpleGraph.Walk.support_map] at hz
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hz
  have hb := grimmettTraceExtendedWalkThree_support_bounds W hu
  rw [mem_squareRectangleVertices_iff]
  change 0 ≤ grimmettFreshSquareIso l u 0 ∧
    grimmettFreshSquareIso l u 0 ≤ (2 * (l + 2) : ℕ) ∧
    -(l + 2 : ℕ) ≤ grimmettFreshSquareIso l u 1 ∧
    grimmettFreshSquareIso l u 1 ≤ (l + 2 : ℕ)
  simp only [grimmettFreshSquareIso_apply_zero, grimmettFreshSquareIso_apply_one]
  omega

private theorem mapped_grimmettTraceExtendedWalkThree_edge_not_boundary
    {l : ℕ} {s : Finset SquareEdge}
    (W : GrimmettRectangleTraceCrossing (2 * l) s)
    {e : Sym2 SquareVertex}
    (he : e ∈ ((grimmettTraceExtendedWalkThree W).map
      (grimmettFreshSquareIso l).toHom).edges) :
    ¬(squareRectangleBoundaryVertex (2 * (l + 2)) (l + 2) e.out.1 ∧
      squareRectangleBoundaryVertex (2 * (l + 2)) (l + 2) e.out.2) := by
  rw [SimpleGraph.Walk.edges_map] at he
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp he
  simp only [grimmettTraceExtendedWalkThree, SimpleGraph.Walk.edges_append,
    SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with hf | hf
  · obtain ⟨u, huf, huRect⟩ :=
      grimmettTraceExtendedWalk_edge_has_rectangle_endpoint W hf
    have hu := mem_grimmettRectangleVertices_iff.mp huRect
    have hnot : ¬squareRectangleBoundaryVertex (2 * (l + 2)) (l + 2)
        (grimmettFreshSquareIso l u) := by
      simp only [squareRectangleBoundaryVertex, grimmettFreshSquareIso_apply_zero,
        grimmettFreshSquareIso_apply_one]
      omega
    intro hb
    apply hnot
    have humap : grimmettFreshSquareIso l u ∈
        Sym2.map (grimmettFreshSquareIso l) f :=
      Sym2.mem_map.mpr ⟨u, huf, rfl⟩
    rw [← (Sym2.map (grimmettFreshSquareIso l) f).out_eq, Sym2.mem_iff] at humap
    exact humap.elim (fun h ↦ h ▸ hb.1) (fun h ↦ h ▸ hb.2)
  · rcases hf with rfl | hf
    · intro hb
      have hf := mem_grimmettRectangleRight_iff.mp W.finish_mem
      have hfirst : ¬squareRectangleBoundaryVertex (2 * (l + 2)) (l + 2)
          (grimmettFreshSquareIso l (grimmettTraceRightOuterVertex W)) := by
        simp [squareRectangleBoundaryVertex, grimmettTraceRightOuterVertex,
          cubicStepFrom, cubicDirectionIncrement, hf]
        omega
      apply hfirst
      have hmem : grimmettFreshSquareIso l (grimmettTraceRightOuterVertex W) ∈
          Sym2.map (grimmettFreshSquareIso l)
            s(grimmettTraceRightOuterVertex W,
              grimmettTraceRightSecondOuterVertex W) := by
        exact Sym2.mem_map.mpr ⟨_, by simp, rfl⟩
      rw [← (Sym2.map (grimmettFreshSquareIso l)
        s(grimmettTraceRightOuterVertex W,
          grimmettTraceRightSecondOuterVertex W)).out_eq, Sym2.mem_iff] at hmem
      exact hmem.elim (fun h ↦ h ▸ hb.1) (fun h ↦ h ▸ hb.2)
    · change f ∈ ([] : List (Sym2 SquareVertex)) at hf
      simp at hf

private theorem mapped_grimmettTraceExtendedWalkThree_edges_subset_boundaryFreeSquare
    {l : ℕ} {s : Finset SquareEdge}
    (W : GrimmettRectangleTraceCrossing (2 * l) s) :
    walkEdgeFinset ((grimmettTraceExtendedWalkThree W).map
        (grimmettFreshSquareIso l).toHom) ⊆
      squareBoundaryFreeRectangleEdges (2 * (l + 2)) (l + 2) := by
  let q := (grimmettTraceExtendedWalkThree W).map (grimmettFreshSquareIso l).toHom
  have hrect : walkEdgeFinset q ⊆ squareRectangleEdges (2 * (l + 2)) (l + 2) :=
    walkEdgeFinset_subset_squareRectangleEdges_of_support q
      (fun z hz ↦ mapped_grimmettTraceExtendedWalkThree_support_mem_square W hz)
  intro e he
  rw [squareBoundaryFreeRectangleEdges, Finset.mem_filter]
  refine ⟨hrect he, ?_⟩
  exact mapped_grimmettTraceExtendedWalkThree_edge_not_boundary W
    ((mem_walkEdgeFinset_iff q e).mp he)

theorem rswHalfSquareWitnessEventThree_subset (l : ℕ) :
    rswHalfSquareWitnessEventThree l ⊆ rswSquareCrossingEvent (l + 2) := by
  classical
  intro ω hω
  change cubicGraphIsoConfigurationPullback (grimmettFreshSquareIso l) ω ∈
    grimmettRectangleFreshCrossingEventThree (2 * l) at hω
  simp only [grimmettRectangleFreshCrossingEventThree,
    adaptiveFreshOpenExtensionEvent, Set.mem_iUnion, Set.mem_inter_iff] at hω
  obtain ⟨s, hs, hcyl, hfresh⟩ := hω
  let W := selectedGrimmettRectangleTraceCrossing (2 * l) ⟨s, hs⟩
  let q := (grimmettTraceExtendedWalkThree W).map (grimmettFreshSquareIso l).toHom
  have hsource : walkIsOpen
      (cubicGraphIsoConfigurationPullback (grimmettFreshSquareIso l) ω)
      (grimmettTraceExtendedWalkThree W) :=
    selectedGrimmettTraceExtendedWalkThree_isOpen hs hcyl hfresh
  have hopen : walkIsOpen ω q :=
    walkIsOpen_map_cubicGraphIso (grimmettFreshSquareIso l)
      (grimmettTraceExtendedWalkThree W) hsource
  have hleft : grimmettFreshSquareIso l (grimmettTraceLeftOuterVertex W) ∈
      squareRectangleLeft (2 * (l + 2)) (l + 2) := by
    rw [mem_squareRectangleLeft_iff]
    have hs' := mem_grimmettRectangleLeft_iff.mp W.start_mem
    simp [grimmettTraceLeftOuterVertex, cubicStepFrom, cubicDirectionIncrement, hs']
    omega
  have hright : grimmettFreshSquareIso l (grimmettTraceRightSecondOuterVertex W) ∈
      squareRectangleRight (2 * (l + 2)) (l + 2) := by
    rw [mem_squareRectangleRight_iff]
    have hf' := mem_grimmettRectangleRight_iff.mp W.finish_mem
    simp [grimmettTraceRightSecondOuterVertex, grimmettTraceRightOuterVertex,
      cubicStepFrom, cubicDirectionIncrement, hf']
    omega
  simp only [rswSquareCrossingEvent, rswRectangleCrossingEvent,
    squareBoundaryFreeRectangleCrossingEvent, Set.mem_iUnion]
  exact ⟨_, hleft, _, hright, q, hopen,
    mapped_grimmettTraceExtendedWalkThree_edges_subset_boundaryFreeSquare W⟩

theorem one_sixteenth_le_bernoulliBondMeasure_real_grimmettRectangleFreshCrossingEventThree
    (l : ℕ) (hl : 0 < l) :
    1 / 16 ≤ (bernoulliBondMeasure 2 squareHalfDensity).real
      (grimmettRectangleFreshCrossingEventThree (2 * l)) := by
  classical
  have hT : grimmettRectangleCrossingTraces (2 * l) ⊆
      (grimmettRectangleEdges (2 * l)).powerset := by
    intro s hs
    exact (Finset.mem_filter.mp hs).1
  have hext := bernoulliBondMeasure_real_adaptiveFreshOpenExtensionEvent
    (k := 3) squareHalfDensity (grimmettRectangleEdges (2 * l))
    (grimmettRectangleCrossingTraces (2 * l)) hT
    (grimmettRectangleFreshExtensionEdgesThree (2 * l))
    (grimmettRectangleFreshExtensionEdgesThree_disjoint (2 * l))
    (card_grimmettRectangleFreshExtensionEdgesThree (2 * l))
  have hsum : 1 / 2 ≤
      ∑ s ∈ grimmettRectangleCrossingTraces (2 * l),
        finiteBernoulliWeight (grimmettRectangleEdges (2 * l)) (1 / 2) s := by
    have hfinite :=
      (dependsOn_grimmettRectangleCrossingEvent (2 * l)
        ).bernoulliBondMeasure_real_eq_finiteBernoulliProbability squareHalfDensity
    have hlower := half_le_grimmettRectangleCrossingProbability_even l hl
    rw [hfinite, finiteBernoulliProbability_eq_sum_filter] at hlower
    simpa [grimmettRectangleCrossingTraces, coe_squareHalfDensity] using hlower
  rw [grimmettRectangleFreshCrossingEventThree, hext, coe_squareHalfDensity]
  norm_num at hsum ⊢
  linarith

theorem one_sixteenth_le_bernoulliBondMeasure_real_rswHalfSquareWitnessEventThree
    (l : ℕ) (hl : 0 < l) :
    1 / 16 ≤ (bernoulliBondMeasure 2 squareHalfDensity).real
      (rswHalfSquareWitnessEventThree l) := by
  rw [rswHalfSquareWitnessEventThree,
    bernoulliBondMeasure_real_cubicGraphIsoEvent squareHalfDensity
      (grimmettFreshSquareIso l)
      (measurableSet_grimmettRectangleFreshCrossingEventThree (2 * l))]
  exact one_sixteenth_le_bernoulliBondMeasure_real_grimmettRectangleFreshCrossingEventThree l hl

/-- A completely axiom-free scale-uniform square-crossing input for the critical RSW argument. -/
theorem one_sixteenth_le_rswSquareCrossingProbability_half
    (l : ℕ) (hl : 3 ≤ l) :
    1 / 16 ≤ rswSquareCrossingProbability squareHalfDensity l := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hl
  rw [show 3 + k = (k + 1) + 2 by omega]
  change 1 / 16 ≤ (bernoulliBondMeasure 2 squareHalfDensity).real
    (rswSquareCrossingEvent ((k + 1) + 2))
  calc
    (1 / 16 : ℝ) ≤ (bernoulliBondMeasure 2 squareHalfDensity).real
        (rswHalfSquareWitnessEventThree (k + 1)) :=
      one_sixteenth_le_bernoulliBondMeasure_real_rswHalfSquareWitnessEventThree
        (k + 1) (by omega)
    _ ≤ (bernoulliBondMeasure 2 squareHalfDensity).real
        (rswSquareCrossingEvent ((k + 1) + 2)) :=
      measureReal_mono (rswHalfSquareWitnessEventThree_subset (k + 1))
        (measure_ne_top _ _)

end Percolation
