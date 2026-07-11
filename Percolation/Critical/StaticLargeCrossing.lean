import Percolation.Critical.StaticGoodAssembly
import Percolation.Critical.BoxFaces

/-!
# From coalescing infinite-cluster vertices to a large finite-box cluster

This file formalizes the deterministic graph conversion in the proof of Lemma 7.97.  Truncated
bond connections are converted to reachability in the induced finite open graph, after which
coalescing infinite-cluster vertices can be collected in one finite-box component.
-/

namespace Percolation

/-- If a walk starts in a coordinate box and every traversed edge is an internal box edge, its
entire support lies in the box. -/
theorem walk_support_subset_cubicMetricBox_of_edges
    {d N : ℕ} {c u v : Cubic d}
    (hu : u ∈ cubicMetricBox d c N) (w : (cubicGraph d).Walk u v)
    (hw : walkEdgeFinset w ⊆ cubicBoxEdges d c N) :
    ∀ z ∈ w.support, z ∈ cubicMetricBox d c N := by
  induction w with
  | nil => simpa using hu
  | @cons u y v huy q ih =>
      intro z hz
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact hu
      · let e : CubicEdge d := ⟨s(u, y), by
          rw [SimpleGraph.mem_edgeSet]
          exact huy⟩
        have hew : e ∈ walkEdgeFinset (SimpleGraph.Walk.cons huy q) := by
          rw [mem_walkEdgeFinset_iff]
          simp [e]
        have hy : y ∈ cubicMetricBox d c N :=
          endpoint_mem_cubicMetricBox_of_edge_mem_cubicBoxEdges (hw hew) (by simp [e])
        have hq : walkEdgeFinset q ⊆ cubicBoxEdges d c N := by
          intro f hf
          apply hw
          rw [mem_walkEdgeFinset_iff] at hf ⊢
          simp [hf]
        exact ih hy hq z hz

/-- An open cubic walk supported in a coordinate box becomes a walk in the induced finite open
graph. -/
theorem nonempty_finiteBoxOpenGraph_walk_of_walkIsOpen_of_support
    {d N : ℕ} {ω : EdgeConfiguration d} {c u v : Cubic d}
    (w : (cubicGraph d).Walk u v) (hopen : walkIsOpen ω w)
    (hbox : ∀ z ∈ w.support, z ∈ cubicMetricBox d c N) :
    Nonempty ((finiteBoxOpenGraph d ω c N).Walk
      ⟨u, hbox u w.start_mem_support⟩ ⟨v, hbox v w.end_mem_support⟩) := by
  induction w with
  | nil => exact ⟨SimpleGraph.Walk.nil⟩
  | @cons u y v huy q ih =>
      have hopenTail : walkIsOpen ω q := by
        intro e he
        exact hopen e (by simp [SimpleGraph.Walk.edges_cons, he])
      have hboxTail : ∀ z ∈ q.support, z ∈ cubicMetricBox d c N := by
        intro z hz
        exact hbox z (by simp [hz])
      obtain ⟨qBox⟩ := ih hopenTail hboxTail
      have hopenHead :
          (⟨s(u, y), (SimpleGraph.mem_edgeSet (cubicGraph d)).mpr huy⟩ : CubicEdge d) ∈ ω := by
        apply hopen
        simp [SimpleGraph.Walk.edges_cons]
      have hAdjOpen : (cubicOpenGraph d ω).Adj u y :=
        cubicOpenGraph_adj.mpr ⟨huy, hopenHead⟩
      have hAdjBox : (finiteBoxOpenGraph d ω c N).Adj
          ⟨u, hbox u (by simp)⟩ ⟨y, hboxTail y (by simp)⟩ := hAdjOpen
      exact ⟨SimpleGraph.Walk.cons hAdjBox qBox⟩

/-- A truncated connection using the internal edge support of a box is exactly enough to obtain
reachability in the induced finite open graph. -/
theorem finiteBoxOpenGraph_reachable_of_mem_connectionEventIn
    {d N : ℕ} {ω : EdgeConfiguration d} {c u v : Cubic d}
    (hu : u ∈ cubicMetricBox d c N) (hv : v ∈ cubicMetricBox d c N)
    (hconn : ω ∈ connectionEventIn d (cubicBoxEdges d c N) u v) :
    (finiteBoxOpenGraph d ω c N).Reachable ⟨u, hu⟩ ⟨v, hv⟩ := by
  obtain ⟨w, hwOpen, hwEdges⟩ := hconn
  have hsupport := walk_support_subset_cubicMetricBox_of_edges hu w hwEdges
  obtain ⟨q⟩ := nonempty_finiteBoxOpenGraph_walk_of_walkIsOpen_of_support w hwOpen hsupport
  exact ⟨q.copy (Subtype.ext (by rfl)) (Subtype.ext (by rfl))⟩

/-- Some infinite-cluster vertex of the inner box connects inside the outer box to a selected
outer face.  This is Grimmett's event `E_{i,a}` in the proof of Lemma 7.97. -/
def innerInfiniteClusterReachesFaceEvent
    (d n N : ℕ) (i : Fin d) (positive : Bool) : Set (EdgeConfiguration d) :=
  ⋃ x ∈ cubicMetricBox d cubicOrigin n,
    infiniteClusterVertexEvent d x ∩
      ⋃ y ∈ cubicBoxFace d cubicOrigin N i positive,
        connectionEventIn d (cubicBoxEdges d cubicOrigin N) x y

theorem measurableSet_innerInfiniteClusterReachesFaceEvent
    (d n N : ℕ) (i : Fin d) (positive : Bool) :
    MeasurableSet (innerInfiniteClusterReachesFaceEvent d n N i positive) := by
  apply (cubicMetricBox d cubicOrigin n).measurableSet_biUnion
  intro x hx
  exact (measurableSet_infiniteClusterVertexEvent d x).inter <|
    (cubicBoxFace d cubicOrigin N i positive).measurableSet_biUnion fun y hy ↦
      (dependsOn_connectionEventIn d (cubicBoxEdges d cubicOrigin N) x y).measurableSet

theorem mem_innerInfiniteClusterReachesFaceEvent_iff
    {d n N : ℕ} {i : Fin d} {positive : Bool} {ω : EdgeConfiguration d} :
    ω ∈ innerInfiniteClusterReachesFaceEvent d n N i positive ↔
      ∃ x ∈ cubicMetricBox d cubicOrigin n,
        hasInfiniteOpenClusterFrom d ω x ∧
          ∃ y ∈ cubicBoxFace d cubicOrigin N i positive,
            ω ∈ connectionEventIn d (cubicBoxEdges d cubicOrigin N) x y := by
  constructor
  · intro h
    obtain ⟨x, hx⟩ := Set.mem_iUnion.mp h
    obtain ⟨hxBox, hx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hxInf, hy⟩ := hx
    obtain ⟨y, hy⟩ := Set.mem_iUnion.mp hy
    obtain ⟨hyFace, hxy⟩ := Set.mem_iUnion.mp hy
    exact ⟨x, hxBox, hxInf, y, hyFace, hxy⟩
  · rintro ⟨x, hxBox, hxInf, y, hyFace, hxy⟩
    exact Set.mem_iUnion.mpr ⟨x, Set.mem_iUnion.mpr ⟨hxBox,
      ⟨hxInf, Set.mem_iUnion.mpr ⟨y, Set.mem_iUnion.mpr ⟨hyFace, hxy⟩⟩⟩⟩⟩

/-- Coalescence, positive inner density, and access to all outer faces produce one finite-box
crossing component containing all inner infinite-cluster vertices.  This is the deterministic
core of Lemma 7.97. -/
theorem mem_largeCrossingClusterEvent_of_dense_of_coalescence_of_allFaces
    {d n N q : ℕ} (hq : 1 ≤ q) (hnN : n ≤ N) {ω : EdgeConfiguration d}
    (hdense : q ≤ (infiniteClusterVerticesIn d
      (cubicMetricBox d cubicOrigin n) ω).card)
    (hcoalesce : ω ∈ infiniteClusterCoalescenceEvent d n N)
    (hfaces : ∀ i : Fin d, ∀ positive : Bool,
      ω ∈ innerInfiniteClusterReachesFaceEvent d n N i positive) :
    ω ∈ largeCrossingClusterEvent d q N cubicOrigin := by
  classical
  let K := infiniteClusterVerticesIn d (cubicMetricBox d cubicOrigin n) ω
  have hKpos : 0 < K.card := lt_of_lt_of_le (by omega : 0 < q) hdense
  obtain ⟨u, huK⟩ := Finset.card_pos.mp hKpos
  have huData := mem_infiniteClusterVerticesIn.mp huK
  have huOuter : u ∈ cubicMetricBox d cubicOrigin N :=
    mem_cubicMetricBox_iff_lInfDist_le.mpr
      ((mem_cubicMetricBox_iff_lInfDist_le.mp huData.1).trans hnN)
  let G := finiteBoxOpenGraph d ω cubicOrigin N
  let uBox : {z : Cubic d // z ∈ cubicMetricBox d cubicOrigin N} := ⟨u, huOuter⟩
  let C : G.ConnectedComponent := G.connectedComponentMk uBox
  have hKsubset : K ⊆ finiteBoxGraphComponentVertices C := by
    intro z hzK
    have hzData := mem_infiniteClusterVerticesIn.mp hzK
    have hzOuter : z ∈ cubicMetricBox d cubicOrigin N :=
      mem_cubicMetricBox_iff_lInfDist_le.mpr
        ((mem_cubicMetricBox_iff_lInfDist_le.mp hzData.1).trans hnN)
    have huz := (mem_infiniteClusterCoalescenceEvent_iff.mp hcoalesce)
      u huData.1 z hzData.1 huData.2 hzData.2
    have hreach : G.Reachable uBox ⟨z, hzOuter⟩ :=
      finiteBoxOpenGraph_reachable_of_mem_connectionEventIn huOuter hzOuter huz
    rw [finiteBoxGraphComponentVertices, Finset.mem_filter]
    refine ⟨hzOuter, hzOuter, ?_⟩
    change (⟨z, hzOuter⟩ : {z : Cubic d // z ∈ cubicMetricBox d cubicOrigin N}) ∈ C.supp
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
    exact SimpleGraph.ConnectedComponent.sound hreach.symm
  have hvertexOfFace (i : Fin d) (positive : Bool) :
      ∃ y ∈ finiteBoxGraphComponentVertices C,
        y ∈ cubicBoxFace d cubicOrigin N i positive := by
    obtain ⟨x, hxInner, hxInf, y, hyFace, hxy⟩ :=
      mem_innerInfiniteClusterReachesFaceEvent_iff.mp (hfaces i positive)
    have hxOuter : x ∈ cubicMetricBox d cubicOrigin N :=
      mem_cubicMetricBox_iff_lInfDist_le.mpr
        ((mem_cubicMetricBox_iff_lInfDist_le.mp hxInner).trans hnN)
    have hySurface := cubicBoxFace_subset_surface cubicOrigin i positive hyFace
    have hyOuter : y ∈ cubicMetricBox d cubicOrigin N :=
      mem_cubicMetricBox_iff_lInfDist_le.mpr (mem_cubicBoxSurface.mp hySurface).le
    have hux := (mem_infiniteClusterCoalescenceEvent_iff.mp hcoalesce)
      u huData.1 x hxInner huData.2 hxInf
    have hreachUX : G.Reachable uBox ⟨x, hxOuter⟩ :=
      finiteBoxOpenGraph_reachable_of_mem_connectionEventIn huOuter hxOuter hux
    have hreachXY : G.Reachable ⟨x, hxOuter⟩ ⟨y, hyOuter⟩ :=
      finiteBoxOpenGraph_reachable_of_mem_connectionEventIn hxOuter hyOuter hxy
    have hreachUY := hreachUX.trans hreachXY
    refine ⟨y, ?_, hyFace⟩
    rw [finiteBoxGraphComponentVertices, Finset.mem_filter]
    refine ⟨hyOuter, hyOuter, ?_⟩
    change (⟨y, hyOuter⟩ : {z : Cubic d // z ∈ cubicMetricBox d cubicOrigin N}) ∈ C.supp
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
    exact SimpleGraph.ConnectedComponent.sound hreachUY.symm
  refine ⟨C, ?_, ?_⟩
  · intro i
    exact ⟨hvertexOfFace i false, hvertexOfFace i true⟩
  · exact hdense.trans (Finset.card_le_card hKsubset)

end Percolation
