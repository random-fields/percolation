import Percolation.Critical.StaticGoodAssembly
import Percolation.Critical.BoxFaces
import Percolation.Critical.RegionSymmetry

/-!
# From coalescing infinite-cluster vertices to a large finite-box cluster

This file formalizes the deterministic graph conversion in the proof of Lemma 7.97.  Truncated
bond connections are converted to reachability in the induced finite open graph, after which
coalescing infinite-cluster vertices can be collected in one finite-box component.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval

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

private theorem cubicGraphIsoConfigurationPullback_mem_innerInfiniteClusterReachesFaceEvent_of_map
    {d n N : ℕ} {i j : Fin d} {positive negative : Bool}
    (F : cubicGraph d ≃g cubicGraph d)
    (hinner : ∀ x, x ∈ cubicMetricBox d cubicOrigin n →
      F x ∈ cubicMetricBox d cubicOrigin n)
    (hface : ∀ y, y ∈ cubicBoxFace d cubicOrigin N i positive →
      F y ∈ cubicBoxFace d cubicOrigin N j negative)
    (hedges : (cubicBoxEdges d cubicOrigin N).image F.mapEdgeSet =
      cubicBoxEdges d cubicOrigin N)
    (ω : EdgeConfiguration d)
    (hω : cubicGraphIsoConfigurationPullback F ω ∈
      innerInfiniteClusterReachesFaceEvent d n N i positive) :
    ω ∈ innerInfiniteClusterReachesFaceEvent d n N j negative := by
  obtain ⟨x, hxBox, hxInf, y, hyFace, hxy⟩ :=
    mem_innerInfiniteClusterReachesFaceEvent_iff.mp hω
  refine mem_innerInfiniteClusterReachesFaceEvent_iff.mpr
    ⟨F x, hinner x hxBox, ?_, F y, hface y hyFace, ?_⟩
  · exact (cubicGraphIsoConfigurationPullback_hasInfiniteOpenClusterFrom_iff
      F ω x).mp hxInf
  · have hmap :=
      (cubicGraphIsoConfigurationPullback_mem_connectionEventIn_iff
        F (cubicBoxEdges d cubicOrigin N) ω x y).mp hxy
    simpa [hedges] using hmap

private theorem cubicGraphIsoConfigurationPullback_mem_innerInfiniteClusterReachesFaceEvent_iff
    {d n N : ℕ} {i j : Fin d} {positive negative : Bool}
    (F : cubicGraph d ≃g cubicGraph d)
    (hinner : ∀ x, x ∈ cubicMetricBox d cubicOrigin n →
      F x ∈ cubicMetricBox d cubicOrigin n)
    (hinnerBack : ∀ x, x ∈ cubicMetricBox d cubicOrigin n →
      F.symm x ∈ cubicMetricBox d cubicOrigin n)
    (hface : ∀ y, y ∈ cubicBoxFace d cubicOrigin N i positive →
      F y ∈ cubicBoxFace d cubicOrigin N j negative)
    (hfaceBack : ∀ y, y ∈ cubicBoxFace d cubicOrigin N j negative →
      F.symm y ∈ cubicBoxFace d cubicOrigin N i positive)
    (hedges : (cubicBoxEdges d cubicOrigin N).image F.mapEdgeSet =
      cubicBoxEdges d cubicOrigin N)
    (hedgesBack : (cubicBoxEdges d cubicOrigin N).image F.symm.mapEdgeSet =
      cubicBoxEdges d cubicOrigin N)
    (ω : EdgeConfiguration d) :
    cubicGraphIsoConfigurationPullback F ω ∈
        innerInfiniteClusterReachesFaceEvent d n N i positive ↔
      ω ∈ innerInfiniteClusterReachesFaceEvent d n N j negative := by
  constructor
  · exact cubicGraphIsoConfigurationPullback_mem_innerInfiniteClusterReachesFaceEvent_of_map
      F hinner hface hedges ω
  · intro hω
    have hback : cubicGraphIsoConfigurationPullback F.symm
        (cubicGraphIsoConfigurationPullback F ω) ∈
          innerInfiniteClusterReachesFaceEvent d n N j negative := by
      simpa using hω
    exact cubicGraphIsoConfigurationPullback_mem_innerInfiniteClusterReachesFaceEvent_of_map
      F.symm hinnerBack hfaceBack hedgesBack
      (cubicGraphIsoConfigurationPullback F ω) hback

private theorem innerInfiniteClusterReachesFaceProbability_eq_of_iso
    {d n N : ℕ} {i j : Fin d} {positive negative : Bool}
    (p : I) (F : cubicGraph d ≃g cubicGraph d)
    (hinner : ∀ x, x ∈ cubicMetricBox d cubicOrigin n →
      F x ∈ cubicMetricBox d cubicOrigin n)
    (hinnerBack : ∀ x, x ∈ cubicMetricBox d cubicOrigin n →
      F.symm x ∈ cubicMetricBox d cubicOrigin n)
    (hface : ∀ y, y ∈ cubicBoxFace d cubicOrigin N i positive →
      F y ∈ cubicBoxFace d cubicOrigin N j negative)
    (hfaceBack : ∀ y, y ∈ cubicBoxFace d cubicOrigin N j negative →
      F.symm y ∈ cubicBoxFace d cubicOrigin N i positive)
    (hedges : (cubicBoxEdges d cubicOrigin N).image F.mapEdgeSet =
      cubicBoxEdges d cubicOrigin N)
    (hedgesBack : (cubicBoxEdges d cubicOrigin N).image F.symm.mapEdgeSet =
      cubicBoxEdges d cubicOrigin N) :
    (bernoulliBondMeasure d p).real
        (innerInfiniteClusterReachesFaceEvent d n N i positive) =
      (bernoulliBondMeasure d p).real
        (innerInfiniteClusterReachesFaceEvent d n N j negative) := by
  let T := cubicGraphIsoConfigurationPullback F
  have hpre : T ⁻¹' innerInfiniteClusterReachesFaceEvent d n N i positive =
      innerInfiniteClusterReachesFaceEvent d n N j negative := by
    ext ω
    exact cubicGraphIsoConfigurationPullback_mem_innerInfiniteClusterReachesFaceEvent_iff
      F hinner hinnerBack hface hfaceBack hedges hedgesBack ω
  have hmap := congrArg
    (fun μ : Measure (EdgeConfiguration d) ↦
      μ.real (innerInfiniteClusterReachesFaceEvent d n N i positive))
    (bernoulliBondMeasure_map_cubicGraphIsoConfigurationPullback p F)
  change (Measure.map T (bernoulliBondMeasure d p)).real
      (innerInfiniteClusterReachesFaceEvent d n N i positive) =
    (bernoulliBondMeasure d p).real
      (innerInfiniteClusterReachesFaceEvent d n N i positive) at hmap
  rw [map_measureReal_apply (measurable_cubicGraphIsoConfigurationPullback F)
    (measurableSet_innerInfiniteClusterReachesFaceEvent d n N i positive), hpre] at hmap
  exact hmap.symm

theorem innerInfiniteClusterReachesFaceProbability_permutation
    {d n N : ℕ} (p : I) (e : Fin d ≃ Fin d) (i : Fin d) (positive : Bool) :
    (bernoulliBondMeasure d p).real
        (innerInfiniteClusterReachesFaceEvent d n N i positive) =
      (bernoulliBondMeasure d p).real
        (innerInfiniteClusterReachesFaceEvent d n N (e i) positive) := by
  apply innerInfiniteClusterReachesFaceProbability_eq_of_iso p
    (cubicCoordinatePermutationIso e)
  · exact fun x hx ↦ cubicCoordinatePermutation_mem_cubicMetricBox_origin e hx
  · exact fun x hx ↦ cubicCoordinatePermutation_mem_cubicMetricBox_origin e.symm hx
  · exact fun y hy ↦ cubicCoordinatePermutation_mem_boxFace e i positive hy
  · intro y hy
    simpa using cubicCoordinatePermutation_mem_boxFace e.symm (e i) positive hy
  · exact cubicCoordinatePermutation_image_cubicBoxEdges_eq e
  · exact cubicCoordinatePermutation_image_cubicBoxEdges_eq e.symm

theorem innerInfiniteClusterReachesFaceProbability_true_eq_false
    {d n N : ℕ} (p : I) (i : Fin d) :
    (bernoulliBondMeasure d p).real
        (innerInfiniteClusterReachesFaceEvent d n N i true) =
      (bernoulliBondMeasure d p).real
        (innerInfiniteClusterReachesFaceEvent d n N i false) := by
  apply innerInfiniteClusterReachesFaceProbability_eq_of_iso p
    (cubicCoordinateReflectionIso i)
  · exact fun x hx ↦ cubicCoordinateReflection_mem_cubicMetricBox_origin i hx
  · exact fun x hx ↦ by simpa using
      cubicCoordinateReflection_mem_cubicMetricBox_origin i hx
  · exact fun y hy ↦ cubicCoordinateReflection_mem_boxFace_true i hy
  · exact fun y hy ↦ cubicCoordinateReflection_mem_boxFace_false i hy
  · exact cubicCoordinateReflection_image_cubicBoxEdges_eq i
  · simpa using cubicCoordinateReflection_image_cubicBoxEdges_eq i

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

/-- The inner box contains at least one vertex belonging to an infinite open cluster. -/
def innerHasInfiniteClusterVertexEvent (d n : ℕ) : Set (EdgeConfiguration d) :=
  ⋃ x ∈ cubicMetricBox d cubicOrigin n, infiniteClusterVertexEvent d x

theorem measurableSet_innerHasInfiniteClusterVertexEvent (d n : ℕ) :
    MeasurableSet (innerHasInfiniteClusterVertexEvent d n) :=
  (cubicMetricBox d cubicOrigin n).measurableSet_biUnion fun x _hx ↦
    measurableSet_infiniteClusterVertexEvent d x

theorem isIncreasingEvent_innerHasInfiniteClusterVertexEvent (d n : ℕ) :
    IsIncreasingEvent (innerHasInfiniteClusterVertexEvent d n) := by
  intro ω η hωη hω
  obtain ⟨x, hx⟩ := Set.mem_iUnion.mp hω
  obtain ⟨hxBox, hxInf⟩ := Set.mem_iUnion.mp hx
  exact Set.mem_iUnion.mpr ⟨x, Set.mem_iUnion.mpr ⟨hxBox,
    isIncreasingEvent_hasInfiniteOpenClusterFrom d x hωη hxInf⟩⟩

theorem isIncreasingEvent_innerInfiniteClusterReachesFaceEvent
    (d n N : ℕ) (i : Fin d) (positive : Bool) :
    IsIncreasingEvent (innerInfiniteClusterReachesFaceEvent d n N i positive) := by
  intro ω η hωη hω
  obtain ⟨x, hxBox, hxInf, y, hyFace, hxy⟩ :=
    mem_innerInfiniteClusterReachesFaceEvent_iff.mp hω
  exact mem_innerInfiniteClusterReachesFaceEvent_iff.mpr
    ⟨x, hxBox, isIncreasingEvent_hasInfiniteOpenClusterFrom d x hωη hxInf,
      y, hyFace,
      isIncreasingEvent_connectionEventIn d (cubicBoxEdges d cubicOrigin N) x y hωη hxy⟩

/-- A nonempty family of inner infinite-cluster vertices reaches at least one signed face of
every larger box. -/
theorem innerHasInfiniteClusterVertexEvent_subset_iUnion_reachesFace
    {d n N : ℕ} (hd : 0 < d) (hnN : n ≤ N) :
    innerHasInfiniteClusterVertexEvent d n ⊆
      ⋃ k : Fin d × Bool,
        innerInfiniteClusterReachesFaceEvent d n N k.1 k.2 := by
  intro ω hω
  obtain ⟨x, hx⟩ := Set.mem_iUnion.mp hω
  obtain ⟨hxBox, hxInf⟩ := Set.mem_iUnion.mp hx
  have hxOuter : x ∈ cubicMetricBox d cubicOrigin N :=
    mem_cubicMetricBox_iff_lInfDist_le.mpr
      ((mem_cubicMetricBox_iff_lInfDist_le.mp hxBox).trans hnN)
  have hsurfaceConn :=
    hasInfiniteOpenClusterFrom_mem_connectionToBoxSurfaceEvent hxOuter hxInf
  obtain ⟨z, hz⟩ := Set.mem_iUnion.mp hsurfaceConn
  obtain ⟨hzSurface, hxz⟩ := Set.mem_iUnion.mp hz
  have hzFaces := cubicBoxSurface_subset_faces hd cubicOrigin hzSurface
  rw [cubicBoxFaces, Finset.mem_biUnion] at hzFaces
  obtain ⟨i, hi, hzFace⟩ := hzFaces
  rw [Finset.mem_union] at hzFace
  rcases hzFace with hzFace | hzFace
  · exact Set.mem_iUnion.mpr ⟨(i, true),
      mem_innerInfiniteClusterReachesFaceEvent_iff.mpr
        ⟨x, hxBox, hxInf, z, hzFace, hxz⟩⟩
  · exact Set.mem_iUnion.mpr ⟨(i, false),
      mem_innerInfiniteClusterReachesFaceEvent_iff.mpr
        ⟨x, hxBox, hxInf, z, hzFace, hxz⟩⟩

/-- Positive infinite-cluster density implies that the inner box contains such a vertex with
probability tending to one. -/
theorem innerHasInfiniteClusterVertexEvent_probability_tendsto_one
    {d : ℕ} (hd : 1 ≤ d) (p : I) (hp : 0 < theta d p) :
    Filter.Tendsto
      (fun n ↦ (bernoulliBondMeasure d p).real
        (innerHasInfiniteClusterVertexEvent d n))
      Filter.atTop (nhds 1) := by
  have hdense := denseInfiniteClusterVertexEvent_probability_tendsto_one
    hd p hp (δ := (1 / 2 : ℝ)) (by norm_num)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hdense tendsto_const_nhds
  · intro n
    apply measureReal_mono (h₂ := measure_ne_top _ _)
    intro ω hω
    have hcard := mem_denseInfiniteClusterVertexEvent_iff_card.mp hω
    let K := infiniteClusterVerticesIn d (cubicMetricBox d cubicOrigin n) ω
    have hboxCard : (0 : ℝ) < (cubicMetricBox d cubicOrigin n).card := by
      exact_mod_cast Finset.card_pos.mpr
        (show (cubicMetricBox d cubicOrigin n).Nonempty from
          ⟨cubicOrigin, mem_cubicMetricBox_iff_lInfDist_le.mpr (by simp)⟩)
    have hKpos : 0 < K.card := by
      have hleft : 0 < (1 - (1 / 2 : ℝ)) * theta d p *
          ((cubicMetricBox d cubicOrigin n).card : ℝ) := by positivity
      exact_mod_cast lt_of_lt_of_le hleft hcard
    obtain ⟨x, hxK⟩ := Finset.card_pos.mp hKpos
    have hx := mem_infiniteClusterVerticesIn.mp hxK
    exact Set.mem_iUnion.mpr ⟨x, Set.mem_iUnion.mpr ⟨hx.1, hx.2⟩⟩
  · intro n
    exact measureReal_le_one

/-- Simultaneous access to every signed coordinate face. -/
def allInnerInfiniteClusterFacesEvent (d n N : ℕ) : Set (EdgeConfiguration d) :=
  ⋂ k ∈ (Finset.univ : Finset (Fin d × Bool)),
    innerInfiniteClusterReachesFaceEvent d n N k.1 k.2

theorem measurableSet_allInnerInfiniteClusterFacesEvent (d n N : ℕ) :
    MeasurableSet (allInnerInfiniteClusterFacesEvent d n N) :=
  (Finset.univ : Finset (Fin d × Bool)).measurableSet_biInter fun k _hk ↦
    measurableSet_innerInfiniteClusterReachesFaceEvent d n N k.1 k.2

theorem mem_allInnerInfiniteClusterFacesEvent_iff {d n N : ℕ}
    {ω : EdgeConfiguration d} :
    ω ∈ allInnerInfiniteClusterFacesEvent d n N ↔
      ∀ i : Fin d, ∀ positive : Bool,
        ω ∈ innerInfiniteClusterReachesFaceEvent d n N i positive := by
  simp [allInnerInfiniteClusterFacesEvent]

/-- Iterated FKG lower bound for the `2d` face-reaching events in (7.103). -/
theorem prod_faceProbabilities_le_allInnerInfiniteClusterFacesProbability
    (d n N : ℕ) (p : I) :
    (∏ k ∈ (Finset.univ : Finset (Fin d × Bool)),
      (bernoulliBondMeasure d p).real
        (innerInfiniteClusterReachesFaceEvent d n N k.1 k.2)) ≤
      (bernoulliBondMeasure d p).real
        (allInnerInfiniteClusterFacesEvent d n N) := by
  exact bernoulliBondMeasure_prod_le_real_biInter_fkg' p
    (fun k hk ↦ isIncreasingEvent_innerInfiniteClusterReachesFaceEvent
      d n N k.1 k.2)
    (fun k hk ↦ measurableSet_innerInfiniteClusterReachesFaceEvent
      d n N k.1 k.2)

/-- Decreasing FKG plus the fact that every inner infinite cluster reaches some face.  This is
the first inequality in Grimmett's argument for (7.103). -/
theorem prod_complFaceProbabilities_le_innerHasInfiniteClusterVertexEvent_compl
    {d n N : ℕ} (hd : 0 < d) (hnN : n ≤ N) (p : I) :
    (∏ k ∈ (Finset.univ : Finset (Fin d × Bool)),
      (bernoulliBondMeasure d p).real
        (innerInfiniteClusterReachesFaceEvent d n N k.1 k.2)ᶜ) ≤
      (bernoulliBondMeasure d p).real
        (innerHasInfiniteClusterVertexEvent d n)ᶜ := by
  let J : Finset (Fin d × Bool) := Finset.univ
  let A : Fin d × Bool → Set (EdgeConfiguration d) := fun k ↦
    (innerInfiniteClusterReachesFaceEvent d n N k.1 k.2)ᶜ
  have hfkg := bernoulliBondMeasure_prod_le_real_biInter_fkg_of_decreasing p
    (J := J) (A := A)
    (fun k hk ↦ (isIncreasingEvent_innerInfiniteClusterReachesFaceEvent
      d n N k.1 k.2).compl)
    (fun k hk ↦ (measurableSet_innerInfiniteClusterReachesFaceEvent
      d n N k.1 k.2).compl)
  calc
    (∏ k ∈ (Finset.univ : Finset (Fin d × Bool)),
        (bernoulliBondMeasure d p).real
          (innerInfiniteClusterReachesFaceEvent d n N k.1 k.2)ᶜ) ≤
      (bernoulliBondMeasure d p).real (⋂ k ∈ J, A k) := hfkg
    _ ≤ (bernoulliBondMeasure d p).real
        (innerHasInfiniteClusterVertexEvent d n)ᶜ := by
      apply measureReal_mono (h₂ := measure_ne_top _ _)
      intro ω hfaces hinner
      have hone := innerHasInfiniteClusterVertexEvent_subset_iUnion_reachesFace
        hd hnN hinner
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hone
      have hkcompl : ω ∈ A k := by
        simp only [Set.mem_iInter] at hfaces
        exact hfaces k (Finset.mem_univ k)
      exact hkcompl hk

/-- Every one of the `2d` face-reaching events has the same probability. -/
theorem innerInfiniteClusterReachesFaceProbability_eq_reference
    {d n N : ℕ} (hd : 0 < d) (p : I) (k : Fin d × Bool) :
    (bernoulliBondMeasure d p).real
        (innerInfiniteClusterReachesFaceEvent d n N k.1 k.2) =
      (bernoulliBondMeasure d p).real
        (innerInfiniteClusterReachesFaceEvent d n N ⟨0, hd⟩ true) := by
  let i0 : Fin d := ⟨0, hd⟩
  let e : Fin d ≃ Fin d := Equiv.swap i0 k.1
  have hperm := innerInfiniteClusterReachesFaceProbability_permutation
    (n := n) (N := N) p e i0 true
  have hei : e i0 = k.1 := Equiv.swap_apply_left i0 k.1
  rw [hei] at hperm
  by_cases hk : k.2 = true
  · rw [hk]
    exact hperm.symm
  · have hkfalse : k.2 = false := Bool.eq_false_of_not_eq_true hk
    rw [hkfalse]
    exact (innerInfiniteClusterReachesFaceProbability_true_eq_false
      (n := n) (N := N) p k.1).symm.trans hperm.symm

theorem one_sub_referenceFaceProbability_pow_le_innerHasInfiniteClusterVertexEvent_compl
    {d n N : ℕ} (hd : 0 < d) (hnN : n ≤ N) (p : I) :
    (1 - (bernoulliBondMeasure d p).real
      (innerInfiniteClusterReachesFaceEvent d n N ⟨0, hd⟩ true)) ^ (2 * d) ≤
      (bernoulliBondMeasure d p).real
        (innerHasInfiniteClusterVertexEvent d n)ᶜ := by
  have hprod := prod_complFaceProbabilities_le_innerHasInfiniteClusterVertexEvent_compl
    hd hnN p
  have hfactor (k : Fin d × Bool) :
      (bernoulliBondMeasure d p).real
          (innerInfiniteClusterReachesFaceEvent d n N k.1 k.2)ᶜ =
        1 - (bernoulliBondMeasure d p).real
          (innerInfiniteClusterReachesFaceEvent d n N ⟨0, hd⟩ true) := by
    rw [probReal_compl_eq_one_sub
      (measurableSet_innerInfiniteClusterReachesFaceEvent d n N k.1 k.2),
      innerInfiniteClusterReachesFaceProbability_eq_reference hd p k]
  simp_rw [hfactor] at hprod
  simpa [Fintype.card_prod, mul_comm] using hprod

/-- The failure probability of one reference face tends to zero once the inner box contains an
infinite-cluster vertex with high probability.  The proof uses the `2d`-th power inequality
rather than introducing a totalized real root. -/
theorem one_sub_referenceFaceProbability_tendsto_zero_of_radii
    {d : ℕ} (hd : 1 ≤ d) (p : I) (hp : 0 < theta d p)
    (r R : ℕ → ℕ) (hr : Filter.Tendsto r Filter.atTop Filter.atTop)
    (hR : ∀ n, r n ≤ R n) :
    Filter.Tendsto
      (fun n ↦ 1 - (bernoulliBondMeasure d p).real
        (innerInfiniteClusterReachesFaceEvent d (r n) (R n) ⟨0, hd⟩ true))
      Filter.atTop (nhds 0) := by
  let emptyProb : ℕ → ℝ := fun n ↦
    (bernoulliBondMeasure d p).real (innerHasInfiniteClusterVertexEvent d (r n))ᶜ
  have hinner :=
    (innerHasInfiniteClusterVertexEvent_probability_tendsto_one hd p hp).comp hr
  have hempty : Filter.Tendsto emptyProb Filter.atTop (nhds 0) := by
    have hEq : emptyProb = fun n ↦
        1 - (bernoulliBondMeasure d p).real
          (innerHasInfiniteClusterVertexEvent d (r n)) := by
      funext n
      change (bernoulliBondMeasure d p).real
        (innerHasInfiniteClusterVertexEvent d (r n))ᶜ = _
      rw [probReal_compl_eq_one_sub
        (measurableSet_innerHasInfiniteClusterVertexEvent d (r n))]
    rw [hEq]
    convert (tendsto_const_nhds (x := (1 : ℝ))).sub hinner using 1 <;> norm_num
  apply Metric.tendsto_atTop.2
  intro ε hε
  by_cases hε1 : 1 < ε
  · refine ⟨0, fun n hn ↦ ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (sub_nonneg.mpr measureReal_le_one)]
    have hprob0 : 0 ≤ (bernoulliBondMeasure d p).real
        (innerInfiniteClusterReachesFaceEvent d (r n) (R n) ⟨0, hd⟩ true) :=
      measureReal_nonneg
    linarith
  · have hpowPos : 0 < ε ^ (2 * d) := pow_pos hε _
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hempty (ε ^ (2 * d)) hpowPos
    refine ⟨N, fun n hn ↦ ?_⟩
    let b := 1 - (bernoulliBondMeasure d p).real
      (innerInfiniteClusterReachesFaceEvent d (r n) (R n) ⟨0, hd⟩ true)
    have hb0 : 0 ≤ b := sub_nonneg.mpr measureReal_le_one
    have hbpow : b ^ (2 * d) ≤ emptyProb n := by
      simpa [b, emptyProb] using
        one_sub_referenceFaceProbability_pow_le_innerHasInfiniteClusterVertexEvent_compl
          (Nat.zero_lt_one.trans_le hd) (hR n) p
    have hemptyLt : emptyProb n < ε ^ (2 * d) := by
      have h := hN n hn
      rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg] at h
      exact h
    have hbε : b < ε := by
      by_contra hnot
      have hεb : ε ≤ b := le_of_not_gt hnot
      have := pow_le_pow_left₀ hε.le hεb (2 * d)
      linarith
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hb0]
    exact hbε

theorem one_sub_referenceFaceProbability_tendsto_zero_of_outer
    {d : ℕ} (hd : 1 ≤ d) (p : I) (hp : 0 < theta d p)
    (R : ℕ → ℕ) (hR : ∀ n, n ≤ R n) :
    Filter.Tendsto
      (fun n ↦ 1 - (bernoulliBondMeasure d p).real
        (innerInfiniteClusterReachesFaceEvent d n (R n) ⟨0, hd⟩ true))
      Filter.atTop (nhds 0) :=
  one_sub_referenceFaceProbability_tendsto_zero_of_radii hd p hp id R
    Filter.tendsto_id hR

theorem one_sub_referenceFaceProbability_tendsto_zero
    {d : ℕ} (hd : 1 ≤ d) (p : I) (hp : 0 < theta d p) :
    Filter.Tendsto
      (fun n ↦ 1 - (bernoulliBondMeasure d p).real
        (innerInfiniteClusterReachesFaceEvent d n (2 * n) ⟨0, hd⟩ true))
      Filter.atTop (nhds 0) :=
  one_sub_referenceFaceProbability_tendsto_zero_of_outer hd p hp
    (fun n ↦ 2 * n) (fun n ↦ by dsimp; omega)

theorem referenceFaceProbability_tendsto_one_of_radii
    {d : ℕ} (hd : 1 ≤ d) (p : I) (hp : 0 < theta d p)
    (r R : ℕ → ℕ) (hr : Filter.Tendsto r Filter.atTop Filter.atTop)
    (hR : ∀ n, r n ≤ R n) :
    Filter.Tendsto
      (fun n ↦ (bernoulliBondMeasure d p).real
        (innerInfiniteClusterReachesFaceEvent d (r n) (R n) ⟨0, hd⟩ true))
      Filter.atTop (nhds 1) := by
  have hfail := one_sub_referenceFaceProbability_tendsto_zero_of_radii
    hd p hp r R hr hR
  have h := (tendsto_const_nhds (x := (1 : ℝ))).sub hfail
  convert h using 1 <;> norm_num

theorem referenceFaceProbability_tendsto_one_of_outer
    {d : ℕ} (hd : 1 ≤ d) (p : I) (hp : 0 < theta d p)
    (R : ℕ → ℕ) (hR : ∀ n, n ≤ R n) :
    Filter.Tendsto
      (fun n ↦ (bernoulliBondMeasure d p).real
        (innerInfiniteClusterReachesFaceEvent d n (R n) ⟨0, hd⟩ true))
      Filter.atTop (nhds 1) :=
  referenceFaceProbability_tendsto_one_of_radii hd p hp id R Filter.tendsto_id hR

theorem referenceFaceProbability_tendsto_one
    {d : ℕ} (hd : 1 ≤ d) (p : I) (hp : 0 < theta d p) :
    Filter.Tendsto
      (fun n ↦ (bernoulliBondMeasure d p).real
        (innerInfiniteClusterReachesFaceEvent d n (2 * n) ⟨0, hd⟩ true))
      Filter.atTop (nhds 1) :=
  referenceFaceProbability_tendsto_one_of_outer hd p hp
    (fun n ↦ 2 * n) (fun n ↦ by dsimp; omega)

theorem referenceFaceProbability_pow_le_allInnerInfiniteClusterFacesProbability
    {d n N : ℕ} (hd : 0 < d) (p : I) :
    ((bernoulliBondMeasure d p).real
      (innerInfiniteClusterReachesFaceEvent d n N ⟨0, hd⟩ true)) ^ (2 * d) ≤
      (bernoulliBondMeasure d p).real
        (allInnerInfiniteClusterFacesEvent d n N) := by
  have hfkg := prod_faceProbabilities_le_allInnerInfiniteClusterFacesProbability d n N p
  have hfactor (k : Fin d × Bool) :
      (bernoulliBondMeasure d p).real
          (innerInfiniteClusterReachesFaceEvent d n N k.1 k.2) =
        (bernoulliBondMeasure d p).real
          (innerInfiniteClusterReachesFaceEvent d n N ⟨0, hd⟩ true) :=
    innerInfiniteClusterReachesFaceProbability_eq_reference hd p k
  simp_rw [hfactor] at hfkg
  simpa [Fintype.card_prod, mul_comm] using hfkg

/-- Equation (7.103) at the convenient outer radius `2n`: all signed faces are reached by the
same coalescing family with probability tending to one.  The coalescence itself is handled by
the separate two-arm estimate. -/
theorem allInnerInfiniteClusterFacesEvent_probability_tendsto_one_of_radii
    {d : ℕ} (hd : 1 ≤ d) (p : I) (hp : 0 < theta d p)
    (r R : ℕ → ℕ) (hr : Filter.Tendsto r Filter.atTop Filter.atTop)
    (hR : ∀ n, r n ≤ R n) :
    Filter.Tendsto
      (fun n ↦ (bernoulliBondMeasure d p).real
        (allInnerInfiniteClusterFacesEvent d (r n) (R n)))
      Filter.atTop (nhds 1) := by
  have href := referenceFaceProbability_tendsto_one_of_radii hd p hp r R hr hR
  have hlower : Filter.Tendsto
      (fun n ↦ ((bernoulliBondMeasure d p).real
        (innerInfiniteClusterReachesFaceEvent d (r n) (R n) ⟨0, hd⟩ true)) ^ (2 * d))
      Filter.atTop (nhds 1) := by
    simpa using href.pow (2 * d)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlower tendsto_const_nhds
  · intro n
    exact referenceFaceProbability_pow_le_allInnerInfiniteClusterFacesProbability
      (Nat.zero_lt_one.trans_le hd) p
  · intro n
    exact measureReal_le_one

theorem allInnerInfiniteClusterFacesEvent_probability_tendsto_one_of_outer
    {d : ℕ} (hd : 1 ≤ d) (p : I) (hp : 0 < theta d p)
    (R : ℕ → ℕ) (hR : ∀ n, n ≤ R n) :
    Filter.Tendsto
      (fun n ↦ (bernoulliBondMeasure d p).real
        (allInnerInfiniteClusterFacesEvent d n (R n)))
      Filter.atTop (nhds 1) :=
  allInnerInfiniteClusterFacesEvent_probability_tendsto_one_of_radii
    hd p hp id R Filter.tendsto_id hR

theorem allInnerInfiniteClusterFacesEvent_probability_tendsto_one
    {d : ℕ} (hd : 1 ≤ d) (p : I) (hp : 0 < theta d p) :
    Filter.Tendsto
      (fun n ↦ (bernoulliBondMeasure d p).real
        (allInnerInfiniteClusterFacesEvent d n (2 * n)))
      Filter.atTop (nhds 1) :=
  allInnerInfiniteClusterFacesEvent_probability_tendsto_one_of_outer hd p hp
    (fun n ↦ 2 * n) (fun n ↦ by dsimp; omega)

/-- Probability-level assembly of Lemma 7.97.  The geometric two-arm argument is isolated in
the hypothesis that all inner infinite-cluster vertices coalesce in the outer box with
probability tending to one.  Thus a later proof of Lemma 7.89 plugs into this declaration
without duplicating the density or all-face arguments. -/
theorem largeCrossingCluster_probability_tendsto_one_of_coalescence
    {d : ℕ} (hd : 1 ≤ d) (p : I) (hp : 0 < theta d p)
    {δ : ℝ} (hδ : 0 < δ) (r R q : ℕ → ℕ)
    (hr : Filter.Tendsto r Filter.atTop Filter.atTop)
    (hrR : ∀ n, r n ≤ R n)
    (hq : ∀ᶠ n : ℕ in Filter.atTop, 1 ≤ q n)
    (hqDensity : ∀ᶠ n : ℕ in Filter.atTop, (q n : ℝ) ≤
      (1 - δ) * theta d p * ((cubicMetricBox d cubicOrigin (r n)).card : ℝ))
    (hcoalesce : Filter.Tendsto
      (fun n ↦ (bernoulliBondMeasure d p).real
        (infiniteClusterCoalescenceEvent d (r n) (R n)))
      Filter.atTop (nhds 1)) :
    Filter.Tendsto
      (fun n ↦ (bernoulliBondMeasure d p).real
        (largeCrossingClusterEvent d (q n) (R n) cubicOrigin))
      Filter.atTop (nhds 1) := by
  let μ := bernoulliBondMeasure d p
  let D : ℕ → Set (EdgeConfiguration d) := fun n ↦
    denseInfiniteClusterVertexEvent d p δ (r n)
  let C : ℕ → Set (EdgeConfiguration d) := fun n ↦
    infiniteClusterCoalescenceEvent d (r n) (R n)
  let F : ℕ → Set (EdgeConfiguration d) := fun n ↦
    allInnerInfiniteClusterFacesEvent d (r n) (R n)
  let L : ℕ → Set (EdgeConfiguration d) := fun n ↦
    largeCrossingClusterEvent d (q n) (R n) cubicOrigin
  have hdenseFail : Filter.Tendsto (fun n ↦ μ.real (D n)ᶜ)
      Filter.atTop (nhds 0) := by
    simpa [μ, D] using
      (denseInfiniteClusterVertexEvent_compl_measureReal_tendsto_zero
        hd p hp hδ).comp hr
  have hcoalesceFail : Filter.Tendsto (fun n ↦ μ.real (C n)ᶜ)
      Filter.atTop (nhds 0) := by
    have hEq : (fun n ↦ μ.real (C n)ᶜ) =
        fun n ↦ 1 - μ.real (C n) := by
      funext n
      rw [probReal_compl_eq_one_sub
        (measurableSet_infiniteClusterCoalescenceEvent d (r n) (R n))]
    rw [hEq]
    simpa [μ, C] using (tendsto_const_nhds (x := (1 : ℝ))).sub hcoalesce
  have hfaces := allInnerInfiniteClusterFacesEvent_probability_tendsto_one_of_radii
    hd p hp r R hr hrR
  have hfacesFail : Filter.Tendsto (fun n ↦ μ.real (F n)ᶜ)
      Filter.atTop (nhds 0) := by
    have hEq : (fun n ↦ μ.real (F n)ᶜ) =
        fun n ↦ 1 - μ.real (F n) := by
      funext n
      rw [probReal_compl_eq_one_sub
        (measurableSet_allInnerInfiniteClusterFacesEvent d (r n) (R n))]
    rw [hEq]
    simpa [μ, F] using (tendsto_const_nhds (x := (1 : ℝ))).sub hfaces
  have hsum : Filter.Tendsto
      (fun n ↦ μ.real (D n)ᶜ + μ.real (C n)ᶜ + μ.real (F n)ᶜ)
      Filter.atTop (nhds 0) := by
    simpa using (hdenseFail.add hcoalesceFail).add hfacesFail
  have hfailure : Filter.Tendsto (fun n ↦ μ.real (L n)ᶜ)
      Filter.atTop (nhds 0) := by
    apply squeeze_zero' (Filter.Eventually.of_forall fun n ↦ measureReal_nonneg)
      (by
        filter_upwards [hq, hqDensity] with n hqN hqDensityN
        show μ.real (L n)ᶜ ≤ _
        have hsubset : (L n)ᶜ ⊆ (D n)ᶜ ∪ (C n)ᶜ ∪ (F n)ᶜ := by
          intro ω hω
          by_cases hD : ω ∈ D n
          · by_cases hC : ω ∈ C n
            · by_cases hF : ω ∈ F n
              · exfalso
                apply hω
                apply mem_largeCrossingClusterEvent_of_dense_of_coalescence_of_allFaces
                  hqN (hrR n)
                · have hcardReal := hqDensityN.trans
                    (mem_denseInfiniteClusterVertexEvent_iff_card.mp hD)
                  exact_mod_cast hcardReal
                · exact hC
                · exact mem_allInnerInfiniteClusterFacesEvent_iff.mp hF
              · exact Or.inr hF
            · exact Or.inl (Or.inr hC)
          · exact Or.inl (Or.inl hD)
        calc
          μ.real (L n)ᶜ ≤ μ.real ((D n)ᶜ ∪ (C n)ᶜ ∪ (F n)ᶜ) :=
            measureReal_mono hsubset (measure_ne_top _ _)
          _ ≤ μ.real ((D n)ᶜ ∪ (C n)ᶜ) + μ.real (F n)ᶜ :=
            measureReal_union_le _ _
          _ ≤ μ.real (D n)ᶜ + μ.real (C n)ᶜ + μ.real (F n)ᶜ := by
            gcongr
            exact measureReal_union_le _ _) hsum
  have hEq : (fun n ↦ μ.real (L n)) = fun n ↦ 1 - μ.real (L n)ᶜ := by
    funext n
    rw [probReal_compl_eq_one_sub
      (measurableSet_largeCrossingClusterEvent d (q n) (R n) cubicOrigin)]
    linarith
  rw [hEq]
  simpa [μ, L] using (tendsto_const_nhds (x := (1 : ℝ))).sub hfailure

end Percolation
