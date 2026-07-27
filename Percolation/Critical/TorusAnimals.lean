import Percolation.Critical.ConcreteClusterSeries
import Percolation.Critical.TorusDifferential

/-!
# Concrete bond animals on the periodic cubic lattice

This file constructs the finite-volume animal table used in Grimmett's Appendix I.  The
periodic animal carries an explicit `2 ≤ N` witness, so all vertex and edge types are finite.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators unitInterval

noncomputable section

def cubicEdgeToTorus {d N : ℕ} (hN : 2 ≤ N) (e : CubicEdge d) :
    CubicTorusEdge d N := by
  refine ⟨Sym2.map (cubicToTorus N) e.1, ?_⟩
  induction heval : e.1 using Sym2.inductionOn with
  | _ x y =>
      rw [Sym2.map_mk, SimpleGraph.mem_edgeSet]
      apply (cubicToTorusHom hN).map_rel
      rw [← SimpleGraph.mem_edgeSet]
      rw [← heval]
      exact e.2

@[simp]
theorem cubicEdgeToTorus_val {d N : ℕ} (hN : 2 ≤ N) (e : CubicEdge d) :
    (cubicEdgeToTorus hN e).1 = Sym2.map (cubicToTorus N) e.1 := rfl

theorem cubicEdgeToTorus_injOn {d N r : ℕ} (hN : 2 ≤ N) (hrN : r < N) :
    Set.InjOn (cubicEdgeToTorus (d := d) (N := N) hN)
      {e : CubicEdge d | ∀ x ∈ e.1, cubicL1Dist cubicOrigin x ≤ r} := by
  intro e he f hf hef
  apply Subtype.ext
  have hefval := congrArg Subtype.val hef
  simp only [cubicEdgeToTorus_val] at hefval
  apply Sym2.ext
  intro x
  constructor
  · intro hx
    have hxmap : cubicToTorus N x ∈ Sym2.map (cubicToTorus N) f.1 := by
      rw [← hefval]
      exact Sym2.mem_map.mpr ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hyx⟩ := Sym2.mem_map.mp hxmap
    have hxy : x = y := cubicToTorus_injOn_metricBall hrN
      (he x hx) (hf y hy) hyx.symm
    simpa [hxy] using hy
  · intro hx
    have hxmap : cubicToTorus N x ∈ Sym2.map (cubicToTorus N) e.1 := by
      rw [hefval]
      exact Sym2.mem_map.mpr ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hyx⟩ := Sym2.mem_map.mp hxmap
    have hxy : x = y := cubicToTorus_injOn_metricBall hrN
      (hf x hx) (he y hy) hyx.symm
    simpa [hxy] using hy

noncomputable def cubicTorusIncidentEdges (d N : ℕ) (hN : 2 ≤ N)
    (V : Finset (CubicTorus d N)) : Finset (CubicTorusEdge d N) :=
  by
    classical
    exact (cubicTorusEdgeFinset d N hN).filter fun e ↦ ∃ x ∈ e.1, x ∈ V

@[simp]
theorem mem_cubicTorusIncidentEdges {d N : ℕ} {hN : 2 ≤ N}
    {V : Finset (CubicTorus d N)} {e : CubicTorusEdge d N} :
    e ∈ cubicTorusIncidentEdges d N hN V ↔ ∃ x ∈ e.1, x ∈ V := by
  classical
  simp [cubicTorusIncidentEdges]

noncomputable def torusFiniteClusterEdges (d N : ℕ) (hN : 2 ≤ N)
    (S : Finset (CubicTorus d N)) (w : CubicTorusEdgeConfiguration d N) :
    Finset (CubicTorusEdge d N) :=
  by
    classical
    exact (cubicTorusIncidentEdges d N hN S).filter fun e ↦ e ∈ w

@[simp]
theorem mem_torusFiniteClusterEdges {d N : ℕ} {hN : 2 ≤ N}
    {S : Finset (CubicTorus d N)} {w : CubicTorusEdgeConfiguration d N}
    {e : CubicTorusEdge d N} :
    e ∈ torusFiniteClusterEdges d N hN S w ↔
      e ∈ cubicTorusIncidentEdges d N hN S ∧ e ∈ w := by
  classical
  simp [torusFiniteClusterEdges]

theorem endpoint_mem_torusOpenCluster_of_open_incident
    {d N : ℕ} {w : CubicTorusEdgeConfiguration d N}
    {e : CubicTorusEdge d N} (heopen : e ∈ w)
    {x y : CubicTorus d N} (hxC : x ∈ cubicTorusOpenCluster d N w)
    (hx : x ∈ e.1) (hy : y ∈ e.1) :
    y ∈ cubicTorusOpenCluster d N w := by
  by_cases hxy : x = y
  · simpa [hxy] using hxC
  · rcases hxC with ⟨q, hq⟩
    have heq : e.1 = s(x, y) := (Sym2.mem_and_mem_iff hxy).mp ⟨hx, hy⟩
    have hxyAdj : (cubicTorusGraph d N).Adj x y := by
      rw [← SimpleGraph.mem_edgeSet]
      exact heq ▸ e.2
    refine ⟨q.concat hxyAdj, ?_⟩
    intro f hf
    rw [SimpleGraph.Walk.edges_concat, List.concat_eq_append,
      List.mem_append, List.mem_singleton] at hf
    rcases hf with hf | hf
    · exact hq f hf
    · have hfe : (⟨f, (q.concat hxyAdj).edges_subset_edgeSet
          (by rw [SimpleGraph.Walk.edges_concat, List.concat_eq_append,
            List.mem_append]; exact Or.inr (by simpa using hf))⟩ :
          CubicTorusEdge d N) = e := by
        apply Subtype.ext
        exact hf.trans heq.symm
      simpa [hfe] using heopen

/-- A rooted finite bond animal on the periodic lattice. -/
structure CubicTorusBondAnimal (d N n : ℕ) (hN : 2 ≤ N) where
  vertices : Finset (CubicTorus d N)
  vertices_subset : vertices ⊆ cubicTorusVertexFinset d N hN
  edges : Finset (CubicTorusEdge d N)
  edges_subset : edges ⊆ cubicTorusEdgeFinset d N hN
  origin_mem : cubicTorusOrigin d N ∈ vertices
  vertices_card : vertices.card = n
  edge_endpoints : ∀ e ∈ edges, ∀ x ∈ e.1, x ∈ vertices
  connected : ∀ x ∈ vertices,
    ∃ q : (cubicTorusGraph d N).Walk (cubicTorusOrigin d N) x,
      ∀ e (he : e ∈ q.edges),
        (⟨e, q.edges_subset_edgeSet he⟩ : CubicTorusEdge d N) ∈ edges

namespace CubicTorusBondAnimal

variable {d N n : ℕ} {hN : 2 ≤ N}

noncomputable instance : DecidableEq (CubicTorusBondAnimal d N n hN) :=
  Classical.decEq _

private def candidateEmbedding (d N n : ℕ) (hN : 2 ≤ N) :
    CubicTorusBondAnimal d N n hN ↪
      ({V // V ∈ (cubicTorusVertexFinset d N hN).powerset} ×
        {E // E ∈ (cubicTorusEdgeFinset d N hN).powerset}) where
  toFun A :=
    (⟨A.vertices, Finset.mem_powerset.mpr A.vertices_subset⟩,
      ⟨A.edges, Finset.mem_powerset.mpr A.edges_subset⟩)
  inj' := by
    intro A B h
    have hV : A.vertices = B.vertices := congrArg (fun z ↦ z.1.1) h
    have hE : A.edges = B.edges := congrArg (fun z ↦ z.2.1) h
    cases A
    cases B
    simp_all

instance : Finite (CubicTorusBondAnimal d N n hN) :=
  Finite.of_injective (candidateEmbedding d N n hN)
    (candidateEmbedding d N n hN).injective

noncomputable instance : Fintype (CubicTorusBondAnimal d N n hN) :=
  Fintype.ofFinite _

noncomputable def boundary (A : CubicTorusBondAnimal d N n hN) :
    Finset (CubicTorusEdge d N) :=
  cubicTorusIncidentEdges d N hN A.vertices \ A.edges

theorem edges_subset_incident (A : CubicTorusBondAnimal d N n hN) :
    A.edges ⊆ cubicTorusIncidentEdges d N hN A.vertices := by
  intro e he
  exact mem_cubicTorusIncidentEdges.mpr
    ⟨e.1.out.1, Sym2.out_fst_mem e.1,
      A.edge_endpoints e he _ (Sym2.out_fst_mem e.1)⟩

/-- Project a cubic animal of size `n < N` into the periodic lattice. -/
noncomputable def ofCubicBondAnimal (hnN : n < N) (A : CubicBondAnimal d n) :
    CubicTorusBondAnimal d N n hN where
  vertices := A.vertices.image (cubicToTorus N)
  vertices_subset := by
    intro x hx
    exact mem_cubicTorusVertexFinset hN x
  edges := A.edges.image (cubicEdgeToTorus hN)
  edges_subset := by
    intro e he
    exact mem_cubicTorusEdgeFinset hN e
  origin_mem := by
    rw [Finset.mem_image]
    exact ⟨cubicOrigin, A.origin_mem, cubicToTorus_origin d N⟩
  vertices_card := by
    have hinj : Set.InjOn (cubicToTorus N) (A.vertices : Set (Cubic d)) := by
      intro x hx y hy hxy
      apply cubicToTorus_injOn_metricBall (N := N) (r := n - 1) (by omega)
      · exact (mem_cubicMetricBall_iff_l1Dist_le.mp (A.vertices_subset hx))
      · exact (mem_cubicMetricBall_iff_l1Dist_le.mp (A.vertices_subset hy))
      · exact hxy
    rw [Finset.card_image_iff.mpr hinj, A.vertices_card]
  edge_endpoints := by
    intro e he x hx
    obtain ⟨f, hf, hfe⟩ := Finset.mem_image.mp he
    have hx' : x ∈ Sym2.map (cubicToTorus N) f.1 := by
      simpa [← hfe] using hx
    obtain ⟨y, hyf, hyx⟩ := Sym2.mem_map.mp hx'
    apply Finset.mem_image.mpr
    exact ⟨y, A.edge_endpoints f hf y hyf, hyx⟩
  connected := by
    intro x hx
    obtain ⟨y, hyA, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨q, hqA⟩ := A.connected y hyA
    let qT : (cubicTorusGraph d N).Walk (cubicTorusOrigin d N) (cubicToTorus N y) :=
      (q.map (cubicToTorusHom hN)).copy (cubicToTorus_origin d N) rfl
    refine ⟨qT, fun e he ↦ ?_⟩
    have heMap : e ∈ (q.map (cubicToTorusHom hN)).edges := by
      simpa [qT] using he
    rw [SimpleGraph.Walk.edges_map] at heMap
    obtain ⟨f, hf, hfe⟩ := List.mem_map.mp heMap
    let f' : CubicEdge d := ⟨f, q.edges_subset_edgeSet hf⟩
    apply Finset.mem_image.mpr
    refine ⟨f', hqA ((mem_walkEdgeFinset_iff q f').mpr hf), ?_⟩
    apply Subtype.ext
    exact hfe

theorem ofCubicBondAnimal_edges_card (hnN : n < N) (A : CubicBondAnimal d n) :
    (ofCubicBondAnimal (hN := hN) hnN A).edges.card = A.edges.card := by
  unfold ofCubicBondAnimal
  apply Finset.card_image_iff.mpr
  intro e he f hf hef
  apply cubicEdgeToTorus_injOn hN (r := n - 1) (by omega)
  · intro x hx
    exact mem_cubicMetricBall_iff_l1Dist_le.mp (A.vertices_subset
      (A.edge_endpoints e he x hx))
  · intro x hx
    exact mem_cubicMetricBall_iff_l1Dist_le.mp (A.vertices_subset
      (A.edge_endpoints f hf x hx))
  · exact hef

theorem cubicEdge_endpoint_mem_metricBall_of_incident
    {A : CubicBondAnimal d n} {e : CubicEdge d}
    (he : e ∈ cubicIncidentEdges d A.vertices) {y : Cubic d} (hy : y ∈ e.1) :
    cubicL1Dist cubicOrigin y ≤ n := by
  obtain ⟨x, hxA, hxe⟩ := mem_cubicIncidentEdges_iff_exists_endpoint.mp he
  have hxball := mem_cubicMetricBall_iff_l1Dist_le.mp (A.vertices_subset hxA)
  have hn : 0 < n := by
    rw [← A.vertices_card, Finset.card_pos]
    exact ⟨cubicOrigin, A.origin_mem⟩
  by_cases hxy : x = y
  · simpa [hxy] using hxball.trans (Nat.sub_le n 1)
  · have heq : e.1 = s(x, y) := (Sym2.mem_and_mem_iff hxy).mp ⟨hxe, hy⟩
    have hxyAdj : (cubicGraph d).Adj x y := by
      rw [← SimpleGraph.mem_edgeSet]
      exact heq ▸ e.2
    obtain ⟨a, ha⟩ := (cubicGraph_adj_iff_exists_stepFrom x y).mp hxyAdj
    calc
      cubicL1Dist cubicOrigin y ≤
          cubicL1Dist cubicOrigin x + cubicL1Dist x y :=
        cubicL1Dist_triangle _ _ _
      _ = cubicL1Dist cubicOrigin x + 1 := by
        rw [ha, cubicL1Dist_stepFrom]
      _ ≤ n := by omega

theorem cubicEdgeToTorus_injective_on_incident (hnN : n < N)
    (A : CubicBondAnimal d n) :
    Set.InjOn (cubicEdgeToTorus hN)
      (cubicIncidentEdges d A.vertices : Set (CubicEdge d)) := by
  intro e he f hf hef
  apply cubicEdgeToTorus_injOn hN (r := n) hnN
  · exact fun x hx ↦ cubicEdge_endpoint_mem_metricBall_of_incident he hx
  · exact fun x hx ↦ cubicEdge_endpoint_mem_metricBall_of_incident hf hx
  · exact hef

theorem cubicEdgeToTorus_cubicStepEdge {x : Cubic d} (a : CubicDirection d) :
    cubicEdgeToTorus hN (cubicStepEdge x a) =
      ⟨s(cubicToTorus N x, cubicTorusStepFrom (cubicToTorus N x) a),
        (SimpleGraph.mem_edgeSet (cubicTorusGraph d N)).mpr
          (cubicTorusGraph_adj_stepFrom hN _ _)⟩ := by
  apply Subtype.ext
  simp [cubicEdgeToTorus_val, cubicStepEdge, cubicToTorus_stepFrom]

theorem image_cubicIncidentEdges_eq_torusIncidentEdges (hnN : n < N)
    (A : CubicBondAnimal d n) :
    (cubicIncidentEdges d A.vertices).image (cubicEdgeToTorus hN) =
      cubicTorusIncidentEdges d N hN
        (A.vertices.image (cubicToTorus N)) := by
  ext e
  constructor
  · intro he
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨x, hxA, hxf⟩ :=
      mem_cubicIncidentEdges_iff_exists_endpoint.mp hf
    apply mem_cubicTorusIncidentEdges.mpr
    exact ⟨cubicToTorus N x,
      (by simpa [cubicEdgeToTorus_val] using Sym2.mem_map.mpr ⟨x, hxf, rfl⟩),
      Finset.mem_image.mpr ⟨x, hxA, rfl⟩⟩
  · intro he
    obtain ⟨z, hze, hzV⟩ := mem_cubicTorusIncidentEdges.mp he
    obtain ⟨x, hxA, hxz⟩ := Finset.mem_image.mp hzV
    subst z
    obtain ⟨y, hey⟩ := Sym2.mem_iff_exists.mp hze
    have hxyAdj : (cubicTorusGraph d N).Adj (cubicToTorus N x) y := by
      rw [← SimpleGraph.mem_edgeSet]
      exact hey ▸ e.2
    obtain ⟨a, ha⟩ :=
      (cubicTorusGraph_adj_iff_exists_stepFrom hN _ _).mp hxyAdj
    let f := cubicStepEdge x a
    apply Finset.mem_image.mpr
    refine ⟨f, cubicStepEdge_mem_cubicIncidentEdges hxA a, ?_⟩
    apply Subtype.ext
    rw [show (cubicEdgeToTorus hN f).1 =
        s(cubicToTorus N x, cubicTorusStepFrom (cubicToTorus N x) a) by
      exact congrArg Subtype.val (cubicEdgeToTorus_cubicStepEdge (hN := hN) a)]
    rw [← ha, ← hey]

theorem image_cubicBoundary_eq_torusBoundary (hnN : n < N)
    (A : CubicBondAnimal d n) :
    A.boundary.image (cubicEdgeToTorus hN) =
      (ofCubicBondAnimal (hN := hN) hnN A).boundary := by
  change A.boundary.image (cubicEdgeToTorus hN) =
    cubicTorusIncidentEdges d N hN (A.vertices.image (cubicToTorus N)) \
      A.edges.image (cubicEdgeToTorus hN)
  have hinj := cubicEdgeToTorus_injective_on_incident (hN := hN) hnN A
  have hincident := image_cubicIncidentEdges_eq_torusIncidentEdges
    (hN := hN) hnN A
  ext e
  constructor
  · intro he
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
    have hfdata := Finset.mem_sdiff.mp hf
    apply Finset.mem_sdiff.mpr
    constructor
    · rw [← hincident]
      exact Finset.mem_image.mpr ⟨f, hfdata.1, rfl⟩
    · intro heA
      change cubicEdgeToTorus hN f ∈ A.edges.image (cubicEdgeToTorus hN) at heA
      obtain ⟨g, hgA, hgf⟩ := Finset.mem_image.mp heA
      have hgInc := A.edges_subset_incident hgA
      have hfg : f = g := hinj hfdata.1 hgInc hgf.symm
      exact hfdata.2 (hfg ▸ hgA)
  · intro he
    have hedata := Finset.mem_sdiff.mp he
    rw [← hincident] at hedata
    obtain ⟨f, hfInc, hfe⟩ := Finset.mem_image.mp hedata.1
    apply Finset.mem_image.mpr
    refine ⟨f, Finset.mem_sdiff.mpr ⟨hfInc, ?_⟩, hfe⟩
    intro hfA
    apply hedata.2
    change e ∈ A.edges.image (cubicEdgeToTorus hN)
    exact Finset.mem_image.mpr ⟨f, hfA, hfe⟩

theorem ofCubicBondAnimal_boundary_card (hnN : n < N) (A : CubicBondAnimal d n) :
    (ofCubicBondAnimal (hN := hN) hnN A).boundary.card = A.boundary.card := by
  rw [← image_cubicBoundary_eq_torusBoundary (hN := hN) hnN A]
  apply Finset.card_image_iff.mpr
  intro e he f hf hef
  apply cubicEdgeToTorus_injective_on_incident (hN := hN) hnN A
  · exact (Finset.mem_sdiff.mp he).1
  · exact (Finset.mem_sdiff.mp hf).1
  · exact hef

/-! ### Lifting a small periodic animal -/

structure PathToVertex (A : CubicTorusBondAnimal d N n hN) (x : A.vertices) where
  walk : (cubicTorusGraph d N).Walk (cubicTorusOrigin d N) x.1
  isPath : walk.IsPath
  edges_mem : ∀ e (he : e ∈ walk.edges),
    (⟨e, walk.edges_subset_edgeSet he⟩ : CubicTorusEdge d N) ∈ A.edges

theorem nonempty_pathToVertex (A : CubicTorusBondAnimal d N n hN) (x : A.vertices) :
    Nonempty (PathToVertex A x) := by
  obtain ⟨w, hw⟩ := A.connected x.1 x.2
  let q : (cubicTorusGraph d N).Walk (cubicTorusOrigin d N) x.1 := w.toPath
  refine ⟨⟨q, w.toPath.2, fun e he ↦ ?_⟩⟩
  have hew : e ∈ w.edges := SimpleGraph.Walk.edges_toPath_subset w he
  let ew : CubicTorusEdge d N := ⟨e, w.edges_subset_edgeSet hew⟩
  have heA : ew ∈ A.edges := hw e hew
  simpa [q, ew] using heA

noncomputable def pathToVertex (A : CubicTorusBondAnimal d N n hN)
    (x : A.vertices) : PathToVertex A x :=
  Classical.choice (nonempty_pathToVertex A x)

theorem walk_endpoint_mem_of_edges_mem
    (A : CubicTorusBondAnimal d N n hN)
    {u v : CubicTorus d N} (hu : u ∈ A.vertices)
    (q : (cubicTorusGraph d N).Walk u v)
    (hq : ∀ e (he : e ∈ q.edges),
      (⟨e, q.edges_subset_edgeSet he⟩ : CubicTorusEdge d N) ∈ A.edges) :
    v ∈ A.vertices := by
  induction q with
  | nil => exact hu
  | @cons u y v huy p ih =>
      let e : CubicTorusEdge d N := ⟨s(u, y), by
        rw [SimpleGraph.mem_edgeSet]
        exact huy⟩
      have heA : e ∈ A.edges := hq e (by simp [e])
      have hyA : y ∈ A.vertices := A.edge_endpoints e heA y (by simp [e])
      apply ih hyA
      intro f hf
      exact hq f (by simp [hf])

theorem pathToVertex_support_subset (A : CubicTorusBondAnimal d N n hN)
    (x : A.vertices) : ∀ y ∈ (pathToVertex A x).walk.support, y ∈ A.vertices := by
  intro y hy
  let q := (pathToVertex A x).walk
  let r := q.takeUntil y hy
  apply walk_endpoint_mem_of_edges_mem A A.origin_mem r
  intro e he
  have heq : e ∈ q.edges := (q.isSubwalk_takeUntil hy).edges_subset he
  exact (pathToVertex A x).edges_mem e heq

theorem pathToVertex_length_lt_card (A : CubicTorusBondAnimal d N n hN)
    (x : A.vertices) : (pathToVertex A x).walk.length < n := by
  let q := (pathToVertex A x).walk
  change q.length < n
  have hsub : q.support.toFinset ⊆ A.vertices := by
    intro y hy
    exact pathToVertex_support_subset A x y (by simpa using hy)
  have hcard : q.support.toFinset.card ≤ A.vertices.card := Finset.card_le_card hsub
  have hnodup := (pathToVertex A x).isPath.support_nodup
  rw [List.toFinset_card_of_nodup hnodup, q.length_support, A.vertices_card] at hcard
  omega

noncomputable def liftVertex (A : CubicTorusBondAnimal d N n hN)
    (x : A.vertices) : Cubic d :=
  cubicEndpointFrom cubicOrigin
    (cubicTorusWalkDirections hN (pathToVertex A x).walk)

theorem liftVertex_projection (A : CubicTorusBondAnimal d N n hN)
    (x : A.vertices) : cubicToTorus N (liftVertex A x) = x.1 := by
  unfold liftVertex
  apply cubicLiftOfTorusWalk_endpoint_projection hN (pathToVertex A x).walk
  exact cubicToTorus_origin d N

theorem liftVertex_dist_lt (A : CubicTorusBondAnimal d N n hN)
    (x : A.vertices) : cubicL1Dist cubicOrigin (liftVertex A x) < n := by
  have hdist := cubicL1Dist_le_walk_length
    (cubicLiftOfTorusWalk hN (pathToVertex A x).walk cubicOrigin)
  rw [cubicLiftOfTorusWalk, cubicWalkFrom_length,
    cubicTorusWalkDirections_length] at hdist
  exact hdist.trans_lt (pathToVertex_length_lt_card A x)

theorem liftVertex_injective (A : CubicTorusBondAnimal d N n hN) :
    Function.Injective (liftVertex A) := by
  intro x y hxy
  apply Subtype.ext
  rw [← liftVertex_projection A x, ← liftVertex_projection A y, hxy]

theorem liftVertex_step_eq (hnN : n < N)
    (A : CubicTorusBondAnimal d N n hN) (u v : A.vertices)
    (huv : (cubicTorusGraph d N).Adj u.1 v.1) :
    cubicStepFrom (liftVertex A u)
        (cubicTorusDartDirection hN ⟨(u.1, v.1), huv⟩) =
      liftVertex A v := by
  let a := cubicTorusDartDirection hN ⟨(u.1, v.1), huv⟩
  have hproj : cubicToTorus N (cubicStepFrom (liftVertex A u) a) = v.1 := by
    rw [cubicToTorus_stepFrom, liftVertex_projection]
    exact (cubicTorusDartDirection_spec hN ⟨(u.1, v.1), huv⟩).symm
  have huDist : cubicL1Dist cubicOrigin (liftVertex A u) < n := liftVertex_dist_lt A u
  have hstepDist : cubicL1Dist cubicOrigin (cubicStepFrom (liftVertex A u) a) ≤ n := by
    calc
      cubicL1Dist cubicOrigin (cubicStepFrom (liftVertex A u) a) ≤
          cubicL1Dist cubicOrigin (liftVertex A u) +
            cubicL1Dist (liftVertex A u) (cubicStepFrom (liftVertex A u) a) :=
        cubicL1Dist_triangle _ _ _
      _ = cubicL1Dist cubicOrigin (liftVertex A u) + 1 := by
        rw [cubicL1Dist_stepFrom]
      _ ≤ n := by omega
  apply cubicToTorus_injOn_metricBall (r := n) hnN hstepDist
    (liftVertex_dist_lt A v).le
  rw [hproj, liftVertex_projection]

noncomputable def liftEdge (hnN : n < N)
    (A : CubicTorusBondAnimal d N n hN) (e : A.edges) : CubicEdge d := by
  let u : A.vertices :=
    ⟨e.1.1.out.1, A.edge_endpoints e.1 e.2 _ (Sym2.out_fst_mem e.1.1)⟩
  let a := cubicTorusDartDirection hN
    ⟨(e.1.1.out.1, e.1.1.out.2), by
      rw [← SimpleGraph.mem_edgeSet]
      convert e.1.2 using 1
      exact e.1.1.out_eq⟩
  exact cubicStepEdge (liftVertex A u) a

theorem cubicEdgeToTorus_liftEdge (hnN : n < N)
    (A : CubicTorusBondAnimal d N n hN) (e : A.edges) :
    cubicEdgeToTorus hN (liftEdge hnN A e) = e.1 := by
  let u : A.vertices :=
    ⟨e.1.1.out.1, A.edge_endpoints e.1 e.2 _ (Sym2.out_fst_mem e.1.1)⟩
  let huv : (cubicTorusGraph d N).Adj e.1.1.out.1 e.1.1.out.2 := by
    rw [← SimpleGraph.mem_edgeSet]
    convert e.1.2 using 1
    exact e.1.1.out_eq
  let a := cubicTorusDartDirection hN ⟨(e.1.1.out.1, e.1.1.out.2), huv⟩
  have ha : e.1.1.out.2 = cubicTorusStepFrom e.1.1.out.1 a :=
    cubicTorusDartDirection_spec hN ⟨(e.1.1.out.1, e.1.1.out.2), huv⟩
  apply Subtype.ext
  change (cubicEdgeToTorus hN (cubicStepEdge (liftVertex A u) a)).1 = e.1.1
  rw [congrArg Subtype.val (cubicEdgeToTorus_cubicStepEdge (hN := hN) a)]
  change s(cubicToTorus N (liftVertex A u),
    cubicTorusStepFrom (cubicToTorus N (liftVertex A u)) a) = e.1.1
  rw [liftVertex_projection]
  change s(e.1.1.out.1, cubicTorusStepFrom e.1.1.out.1 a) = e.1.1
  rw [← ha]
  exact e.1.1.out_eq

theorem liftEdge_injective (hnN : n < N)
    (A : CubicTorusBondAnimal d N n hN) :
    Function.Injective (liftEdge hnN A) := by
  intro e f hef
  apply Subtype.ext
  have h := congrArg (cubicEdgeToTorus hN) hef
  simpa [cubicEdgeToTorus_liftEdge] using h

theorem liftEdge_val_eq (hnN : n < N)
    (A : CubicTorusBondAnimal d N n hN) (e : A.edges) :
    (liftEdge hnN A e).1 =
      s(liftVertex A
          ⟨e.1.1.out.1, A.edge_endpoints e.1 e.2 _ (Sym2.out_fst_mem e.1.1)⟩,
        liftVertex A
          ⟨e.1.1.out.2, A.edge_endpoints e.1 e.2 _ (Sym2.out_snd_mem e.1.1)⟩) := by
  let u : A.vertices :=
    ⟨e.1.1.out.1, A.edge_endpoints e.1 e.2 _ (Sym2.out_fst_mem e.1.1)⟩
  let v : A.vertices :=
    ⟨e.1.1.out.2, A.edge_endpoints e.1 e.2 _ (Sym2.out_snd_mem e.1.1)⟩
  let huv : (cubicTorusGraph d N).Adj u.1 v.1 := by
    rw [← SimpleGraph.mem_edgeSet]
    convert e.1.2 using 1
    exact e.1.1.out_eq
  let a := cubicTorusDartDirection hN ⟨(u.1, v.1), huv⟩
  change (cubicStepEdge (liftVertex A u) a).1 = s(liftVertex A u, liftVertex A v)
  change s(liftVertex A u, cubicStepFrom (liftVertex A u) a) = _
  rw [liftVertex_step_eq hnN A u v huv]

theorem liftEdge_val_eq_of_eq (hnN : n < N)
    (A : CubicTorusBondAnimal d N n hN) (e : A.edges)
    {x y : CubicTorus d N} (hx : x ∈ A.vertices) (hy : y ∈ A.vertices)
    (heq : e.1.1 = s(x, y)) :
    (liftEdge hnN A e).1 =
      s(liftVertex A ⟨x, hx⟩, liftVertex A ⟨y, hy⟩) := by
  rw [liftEdge_val_eq hnN A e]
  have hout : s(e.1.1.out.1, e.1.1.out.2) = s(x, y) := e.1.1.out_eq.trans heq
  rw [Sym2.eq_iff] at hout ⊢
  rcases hout with h | h
  · exact Or.inl ⟨
      congrArg (liftVertex A) (Subtype.ext h.1),
      congrArg (liftVertex A) (Subtype.ext h.2)⟩
  · exact Or.inr ⟨
      congrArg (liftVertex A) (Subtype.ext h.1),
      congrArg (liftVertex A) (Subtype.ext h.2)⟩

theorem liftVertex_origin (hnN : n < N)
    (A : CubicTorusBondAnimal d N n hN) :
    liftVertex A ⟨cubicTorusOrigin d N, A.origin_mem⟩ = cubicOrigin := by
  have hn : 0 < n := by
    rw [← A.vertices_card, Finset.card_pos]
    exact ⟨cubicTorusOrigin d N, A.origin_mem⟩
  apply cubicToTorus_injOn_metricBall (N := N) (r := n - 1) (by omega)
  · change cubicL1Dist cubicOrigin (liftVertex A _) ≤ n - 1
    have h := liftVertex_dist_lt A
      ⟨cubicTorusOrigin d N, A.origin_mem⟩
    omega
  · change cubicL1Dist cubicOrigin cubicOrigin ≤ n - 1
    simp
  · rw [liftVertex_projection, cubicToTorus_origin]
    rfl

structure LiftedAnimalWalk (hnN : n < N) (A : CubicTorusBondAnimal d N n hN)
    (u v : A.vertices) where
  walk : (cubicGraph d).Walk (liftVertex A u) (liftVertex A v)
  edges_mem : walkEdgeFinset walk ⊆ A.edges.attach.image (liftEdge hnN A)

theorem nonempty_liftedAnimalWalk (hnN : n < N)
    (A : CubicTorusBondAnimal d N n hN)
    {u v : CubicTorus d N} (hu : u ∈ A.vertices) (hv : v ∈ A.vertices)
    (q : (cubicTorusGraph d N).Walk u v)
    (hq : ∀ e (he : e ∈ q.edges),
      (⟨e, q.edges_subset_edgeSet he⟩ : CubicTorusEdge d N) ∈ A.edges) :
    Nonempty (LiftedAnimalWalk hnN A ⟨u, hu⟩ ⟨v, hv⟩) := by
  induction q with
  | nil => exact ⟨⟨.nil, by
      intro f hf
      rw [mem_walkEdgeFinset_iff] at hf
      cases hf⟩⟩
  | @cons u y v huy p ih =>
      let e : CubicTorusEdge d N := ⟨s(u, y), by
        rw [SimpleGraph.mem_edgeSet]
        exact huy⟩
      have heA : e ∈ A.edges := hq e (by simp [e])
      let eA : A.edges := ⟨e, heA⟩
      have hy : y ∈ A.vertices := A.edge_endpoints e heA y (by simp [e])
      obtain ⟨W⟩ := ih hy hv (fun f hf ↦ hq f (by simp [hf]))
      have hadj : (cubicGraph d).Adj
          (liftVertex A ⟨u, hu⟩) (liftVertex A ⟨y, hy⟩) := by
        rw [← SimpleGraph.mem_edgeSet]
        have hval := liftEdge_val_eq_of_eq hnN A eA hu hy (by rfl)
        change s(liftVertex A ⟨u, hu⟩, liftVertex A ⟨y, hy⟩) ∈
          (cubicGraph d).edgeSet
        rw [← hval]
        exact (liftEdge hnN A eA).2
      let w := SimpleGraph.Walk.cons hadj W.walk
      refine ⟨⟨w, ?_⟩⟩
      intro f hf
      rw [mem_walkEdgeFinset_iff] at hf
      simp only [w, SimpleGraph.Walk.edges_cons, List.mem_cons] at hf
      rcases hf with hf | hf
      · apply Finset.mem_image.mpr
        refine ⟨eA, Finset.mem_attach _ _, ?_⟩
        apply Subtype.ext
        rw [liftEdge_val_eq_of_eq hnN A eA hu hy (by rfl)]
        exact hf.symm
      · exact W.edges_mem ((mem_walkEdgeFinset_iff W.walk _).mpr hf)

theorem liftEdge_endpoint_eq (hnN : n < N)
    (A : CubicTorusBondAnimal d N n hN) (e : A.edges)
    {x : Cubic d} (hx : x ∈ (liftEdge hnN A e).1) :
    x = liftVertex A
        ⟨e.1.1.out.1, A.edge_endpoints e.1 e.2 _ (Sym2.out_fst_mem e.1.1)⟩ ∨
      x = liftVertex A
        ⟨e.1.1.out.2, A.edge_endpoints e.1 e.2 _ (Sym2.out_snd_mem e.1.1)⟩ := by
  rw [liftEdge_val_eq hnN A e] at hx
  simpa using hx

noncomputable def toCubicBondAnimal (hnN : n < N)
    (A : CubicTorusBondAnimal d N n hN) : CubicBondAnimal d n where
  vertices := A.vertices.attach.image (liftVertex A)
  vertices_subset := by
    intro x hx
    obtain ⟨y, _hy, rfl⟩ := Finset.mem_image.mp hx
    rw [mem_cubicMetricBall_iff_l1Dist_le]
    have h := liftVertex_dist_lt A y
    omega
  edges := A.edges.attach.image (liftEdge hnN A)
  edges_subset := by
    intro e he
    obtain ⟨f, _hf, rfl⟩ := Finset.mem_image.mp he
    apply cubicEdge_mem_cubicMetricBallEdges_of_out_mem
    · rw [mem_cubicMetricBall_iff_l1Dist_le]
      rcases liftEdge_endpoint_eq hnN A f (Sym2.out_fst_mem (liftEdge hnN A f).1) with h | h
      · rw [h]
        have ht := liftVertex_dist_lt A
          ⟨f.1.1.out.1,
            A.edge_endpoints f.1 f.2 _ (Sym2.out_fst_mem f.1.1)⟩
        omega
      · rw [h]
        have ht := liftVertex_dist_lt A
          ⟨f.1.1.out.2,
            A.edge_endpoints f.1 f.2 _ (Sym2.out_snd_mem f.1.1)⟩
        omega
    · rw [mem_cubicMetricBall_iff_l1Dist_le]
      rcases liftEdge_endpoint_eq hnN A f (Sym2.out_snd_mem (liftEdge hnN A f).1) with h | h
      · rw [h]
        have ht := liftVertex_dist_lt A
          ⟨f.1.1.out.1,
            A.edge_endpoints f.1 f.2 _ (Sym2.out_fst_mem f.1.1)⟩
        omega
      · rw [h]
        have ht := liftVertex_dist_lt A
          ⟨f.1.1.out.2,
            A.edge_endpoints f.1 f.2 _ (Sym2.out_snd_mem f.1.1)⟩
        omega
  origin_mem := by
    rw [Finset.mem_image]
    let o : A.vertices := ⟨cubicTorusOrigin d N, A.origin_mem⟩
    exact ⟨o, Finset.mem_attach _ _, by simpa [o] using liftVertex_origin hnN A⟩
  vertices_card := by
    have hinj : Set.InjOn (liftVertex A) (A.vertices.attach : Set A.vertices) :=
      (liftVertex_injective A).injOn
    rw [Finset.card_image_iff.mpr hinj]
    simp [A.vertices_card]
  edge_endpoints := by
    intro e he x hx
    obtain ⟨f, _hf, rfl⟩ := Finset.mem_image.mp he
    rcases liftEdge_endpoint_eq hnN A f hx with h | h
    · rw [h]
      exact Finset.mem_image.mpr ⟨_, Finset.mem_attach _ _, rfl⟩
    · rw [h]
      exact Finset.mem_image.mpr ⟨_, Finset.mem_attach _ _, rfl⟩
  connected := by
    intro x hx
    obtain ⟨y, _hy, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨q, hqA⟩ := A.connected y.1 y.2
    obtain ⟨W⟩ := nonempty_liftedAnimalWalk hnN A A.origin_mem y.2 q
      (fun e he ↦ hqA e he)
    let q' : (cubicGraph d).Walk cubicOrigin (liftVertex A y) :=
      W.walk.copy (liftVertex_origin hnN A) rfl
    refine ⟨q', fun e he ↦ W.edges_mem ?_⟩
    rw [mem_walkEdgeFinset_iff] at he ⊢
    simpa [q', SimpleGraph.Walk.edges_copy] using he

theorem toCubicBondAnimal_edges_card (hnN : n < N)
    (A : CubicTorusBondAnimal d N n hN) :
    (toCubicBondAnimal hnN A).edges.card = A.edges.card := by
  unfold toCubicBondAnimal
  have hinj : Set.InjOn (liftEdge hnN A) (A.edges.attach : Set A.edges) :=
    (liftEdge_injective hnN A).injOn
  rw [Finset.card_image_iff.mpr hinj]
  simp

theorem liftVertex_ofCubicBondAnimal (hnN : n < N)
    (A : CubicBondAnimal d n) (x : Cubic d) (hx : x ∈ A.vertices) :
    liftVertex (ofCubicBondAnimal (hN := hN) hnN A)
        ⟨cubicToTorus N x, Finset.mem_image.mpr ⟨x, hx, rfl⟩⟩ = x := by
  let B := ofCubicBondAnimal (hN := hN) hnN A
  have hn : 0 < n := by
    rw [← A.vertices_card, Finset.card_pos]
    exact ⟨cubicOrigin, A.origin_mem⟩
  apply cubicToTorus_injOn_metricBall (N := N) (r := n - 1) (by omega)
  · have hdist := liftVertex_dist_lt B
      ⟨cubicToTorus N x, Finset.mem_image.mpr ⟨x, hx, rfl⟩⟩
    exact Nat.le_sub_one_of_lt hdist
  · exact mem_cubicMetricBall_iff_l1Dist_le.mp (A.vertices_subset hx)
  · exact liftVertex_projection B _

theorem liftEdge_ofCubicBondAnimal (hnN : n < N)
    (A : CubicBondAnimal d n) (e : CubicEdge d) (he : e ∈ A.edges) :
    liftEdge hnN (ofCubicBondAnimal (hN := hN) hnN A)
        ⟨cubicEdgeToTorus hN e, Finset.mem_image.mpr ⟨e, he, rfl⟩⟩ = e := by
  let B := ofCubicBondAnimal (hN := hN) hnN A
  let f : B.edges :=
    ⟨cubicEdgeToTorus hN e, Finset.mem_image.mpr ⟨e, he, rfl⟩⟩
  apply cubicEdgeToTorus_injOn hN (r := n - 1) (by omega)
  · intro x hx
    rcases liftEdge_endpoint_eq hnN B f hx with hx | hx
    · rw [hx]
      have hdist := liftVertex_dist_lt B
        ⟨f.1.1.out.1, B.edge_endpoints f.1 f.2 _ (Sym2.out_fst_mem f.1.1)⟩
      exact Nat.le_sub_one_of_lt hdist
    · rw [hx]
      have hdist := liftVertex_dist_lt B
        ⟨f.1.1.out.2, B.edge_endpoints f.1 f.2 _ (Sym2.out_snd_mem f.1.1)⟩
      exact Nat.le_sub_one_of_lt hdist
  · intro x hx
    exact mem_cubicMetricBall_iff_l1Dist_le.mp
      (A.vertices_subset (A.edge_endpoints e he x hx))
  · exact cubicEdgeToTorus_liftEdge hnN B f

private theorem cubicBondAnimal_ext_data (A B : CubicBondAnimal d n)
    (hV : A.vertices = B.vertices) (hE : A.edges = B.edges) : A = B := by
  cases A
  cases B
  simp_all

private theorem ext_data (A B : CubicTorusBondAnimal d N n hN)
    (hV : A.vertices = B.vertices) (hE : A.edges = B.edges) : A = B := by
  cases A
  cases B
  simp_all

theorem toCubicBondAnimal_ofCubicBondAnimal (hnN : n < N)
    (A : CubicBondAnimal d n) :
    toCubicBondAnimal hnN (ofCubicBondAnimal (hN := hN) hnN A) = A := by
  let B := ofCubicBondAnimal (hN := hN) hnN A
  have hV : (toCubicBondAnimal hnN B).vertices = A.vertices := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, _hy, hxy⟩ := Finset.mem_image.mp hx
      obtain ⟨z, hz, hzy⟩ := Finset.mem_image.mp y.2
      have hy : y =
          ⟨cubicToTorus N z, Finset.mem_image.mpr ⟨z, hz, rfl⟩⟩ :=
        Subtype.ext hzy.symm
      have hlift := liftVertex_ofCubicBondAnimal (hN := hN) hnN A z hz
      rw [hy, hlift] at hxy
      simpa [← hxy] using hz
    · intro hx
      let y : B.vertices :=
        ⟨cubicToTorus N x, Finset.mem_image.mpr ⟨x, hx, rfl⟩⟩
      apply Finset.mem_image.mpr
      refine ⟨y, Finset.mem_attach _ _, ?_⟩
      exact liftVertex_ofCubicBondAnimal (hN := hN) hnN A x hx
  have hE : (toCubicBondAnimal hnN B).edges = A.edges := by
    ext e
    constructor
    · intro heLift
      obtain ⟨f, _hf, hfe⟩ := Finset.mem_image.mp heLift
      obtain ⟨g, hg, hgf⟩ := Finset.mem_image.mp f.2
      have hf : f =
          ⟨cubicEdgeToTorus hN g, Finset.mem_image.mpr ⟨g, hg, rfl⟩⟩ :=
        Subtype.ext hgf.symm
      have hlift := liftEdge_ofCubicBondAnimal (hN := hN) hnN A g hg
      rw [hf, hlift] at hfe
      simpa [← hfe] using hg
    · intro he
      let f : B.edges :=
        ⟨cubicEdgeToTorus hN e, Finset.mem_image.mpr ⟨e, he, rfl⟩⟩
      apply Finset.mem_image.mpr
      refine ⟨f, Finset.mem_attach _ _, ?_⟩
      exact liftEdge_ofCubicBondAnimal (hN := hN) hnN A e he
  exact cubicBondAnimal_ext_data _ _ hV hE

theorem ofCubicBondAnimal_toCubicBondAnimal (hnN : n < N)
    (A : CubicTorusBondAnimal d N n hN) :
    ofCubicBondAnimal (hN := hN) hnN (toCubicBondAnimal hnN A) = A := by
  have hV : (ofCubicBondAnimal (hN := hN) hnN
      (toCubicBondAnimal hnN A)).vertices =
      A.vertices := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp hx
      obtain ⟨z, _hz, hzy⟩ := Finset.mem_image.mp hy
      have hproj := liftVertex_projection A z
      rw [hzy] at hproj
      simpa [← hyx, hproj] using z.2
    · intro hx
      let z : A.vertices := ⟨x, hx⟩
      apply Finset.mem_image.mpr
      refine ⟨liftVertex A z, Finset.mem_image.mpr
        ⟨z, Finset.mem_attach _ _, rfl⟩, ?_⟩
      exact liftVertex_projection A z
  have hE : (ofCubicBondAnimal (hN := hN) hnN
      (toCubicBondAnimal hnN A)).edges =
      A.edges := by
    ext e
    constructor
    · intro he
      obtain ⟨f, hf, hfe⟩ := Finset.mem_image.mp he
      obtain ⟨g, _hg, hgf⟩ := Finset.mem_image.mp hf
      have hproj := cubicEdgeToTorus_liftEdge hnN A g
      rw [hgf] at hproj
      simpa [← hfe, hproj] using g.2
    · intro he
      let g : A.edges := ⟨e, he⟩
      apply Finset.mem_image.mpr
      refine ⟨liftEdge hnN A g, Finset.mem_image.mpr
        ⟨g, Finset.mem_attach _ _, rfl⟩, ?_⟩
      exact cubicEdgeToTorus_liftEdge hnN A g
  exact ext_data _ _ hV hE

/-- Below the covering radius, rooted cubic and periodic bond animals are exactly equivalent. -/
noncomputable def smallAnimalEquiv (hnN : n < N) :
    CubicBondAnimal d n ≃ CubicTorusBondAnimal d N n hN where
  toFun := ofCubicBondAnimal hnN
  invFun := toCubicBondAnimal hnN
  left_inv := toCubicBondAnimal_ofCubicBondAnimal hnN
  right_inv := ofCubicBondAnimal_toCubicBondAnimal hnN

theorem toCubicBondAnimal_boundary_card (hnN : n < N)
    (A : CubicTorusBondAnimal d N n hN) :
    (toCubicBondAnimal hnN A).boundary.card = A.boundary.card := by
  have hproject := ofCubicBondAnimal_boundary_card (hN := hN) hnN
    (toCubicBondAnimal hnN A)
  rw [ofCubicBondAnimal_toCubicBondAnimal (hN := hN) hnN A] at hproject
  exact hproject.symm

noncomputable def smallAnimalProfileEquiv (hnN : n < N) (m b : ℕ) :
    {A : CubicBondAnimal d n // A.edges.card = m ∧ A.boundary.card = b} ≃
      {A : CubicTorusBondAnimal d N n hN //
        A.edges.card = m ∧ A.boundary.card = b} where
  toFun A := ⟨ofCubicBondAnimal hnN A.1, by
    rw [ofCubicBondAnimal_edges_card (hN := hN) hnN A.1,
      ofCubicBondAnimal_boundary_card (hN := hN) hnN A.1]
    exact A.2⟩
  invFun A := ⟨toCubicBondAnimal hnN A.1, by
    rw [toCubicBondAnimal_edges_card hnN A.1,
      toCubicBondAnimal_boundary_card hnN A.1]
    exact A.2⟩
  left_inv A := Subtype.ext (toCubicBondAnimal_ofCubicBondAnimal hnN A.1)
  right_inv A := Subtype.ext (ofCubicBondAnimal_toCubicBondAnimal hnN A.1)

noncomputable def ofConfiguration (w : CubicTorusEdgeConfiguration d N)
    (hcard : (cubicTorusOpenClusterFinset d N hN w).card = n) :
    CubicTorusBondAnimal d N n hN where
  vertices := cubicTorusOpenClusterFinset d N hN w
  vertices_subset := restrictTo_subset _ _
  edges := torusFiniteClusterEdges d N hN
    (cubicTorusOpenClusterFinset d N hN w) w
  edges_subset := by
    intro e he
    exact mem_cubicTorusEdgeFinset hN e
  origin_mem := (mem_cubicTorusOpenClusterFinset hN).mpr
    (cubicTorusOrigin_mem_openCluster d N w)
  vertices_card := hcard
  edge_endpoints := by
    intro e he x hx
    have he' := mem_torusFiniteClusterEdges.mp he
    rcases mem_cubicTorusIncidentEdges.mp he'.1 with ⟨y, hye, hyC⟩
    apply (mem_cubicTorusOpenClusterFinset hN).mpr
    apply endpoint_mem_torusOpenCluster_of_open_incident he'.2
      ((mem_cubicTorusOpenClusterFinset hN).mp hyC) hye hx
  connected := by
    intro x hx
    obtain ⟨q, hq⟩ := (mem_cubicTorusOpenClusterFinset hN).mp hx
    refine ⟨q, fun e he ↦ ?_⟩
    apply mem_torusFiniteClusterEdges.mpr
    constructor
    · apply mem_cubicTorusIncidentEdges.mpr
      let e' : CubicTorusEdge d N := ⟨e, q.edges_subset_edgeSet he⟩
      refine ⟨e'.1.out.1, Sym2.out_fst_mem e'.1, ?_⟩
      apply (mem_cubicTorusOpenClusterFinset hN).mpr
      let hmem := q.mem_support_of_mem_edges he (Sym2.out_fst_mem e'.1)
      exact ⟨q.takeUntil e'.1.out.1 hmem, fun f hf ↦ hq f
          ((q.isSubwalk_takeUntil hmem).edges_subset hf)⟩
    · exact hq e he

theorem edges_disjoint_boundary (A : CubicTorusBondAnimal d N n hN) :
    Disjoint A.edges A.boundary := by
  rw [Finset.disjoint_left]
  intro e heA heB
  exact (Finset.mem_sdiff.mp heB).2 heA

def clusterCylinder (A : CubicTorusBondAnimal d N n hN) :
    Set (CubicTorusEdgeConfiguration d N) :=
  finiteCylinder (A.edges ∪ A.boundary) A.edges

theorem edges_subset_support (A : CubicTorusBondAnimal d N n hN) :
    A.edges ⊆ A.edges ∪ A.boundary := Finset.subset_union_left

theorem torusOpenClusterFinset_eq_vertices_of_mem_clusterCylinder
    (A : CubicTorusBondAnimal d N n hN) {w : CubicTorusEdgeConfiguration d N}
    (hw : w ∈ A.clusterCylinder) :
    cubicTorusOpenClusterFinset d N hN w = A.vertices := by
  have endpoint_of_open_walk : ∀ {u v : CubicTorus d N},
      u ∈ A.vertices →
      (q : (cubicTorusGraph d N).Walk u v) → torusWalkIsOpen w q →
      v ∈ A.vertices := by
    intro u v hu q hq
    induction q with
    | nil => exact hu
    | @cons u y v huy p ih =>
        let e : CubicTorusEdge d N := ⟨s(u, y), by
          rw [SimpleGraph.mem_edgeSet]
          exact huy⟩
        have heopen : e ∈ w := hq e (by simp [e])
        have hyA : y ∈ A.vertices := by
          by_contra hy
          have heInc : e ∈ cubicTorusIncidentEdges d N hN A.vertices :=
            mem_cubicTorusIncidentEdges.mpr ⟨u, by simp [e], hu⟩
          have heNot : e ∉ A.edges := by
            intro heA
            exact hy (A.edge_endpoints e heA y (by simp [e]))
          have heBoundary : e ∈ A.boundary := Finset.mem_sdiff.mpr ⟨heInc, heNot⟩
          have htrace := (mem_finiteCylinder.mp hw) e
            (Finset.mem_union_right _ heBoundary)
          exact heNot (htrace.mp heopen)
        exact ih hyA (fun e he ↦ hq e (by simp [he]))
  apply Finset.ext
  intro x
  rw [mem_cubicTorusOpenClusterFinset]
  constructor
  · rintro ⟨q, hq⟩
    exact endpoint_of_open_walk A.origin_mem q hq
  · intro hx
    obtain ⟨q, hqA⟩ := A.connected x hx
    refine ⟨q, fun e he ↦ ?_⟩
    let e' : CubicTorusEdge d N := ⟨e, q.edges_subset_edgeSet he⟩
    have heA : e' ∈ A.edges := hqA e he
    exact (mem_finiteCylinder.mp hw e'
      (Finset.mem_union_left _ heA)).mpr heA

theorem ofConfiguration_mem_clusterCylinder
    (w : CubicTorusEdgeConfiguration d N)
    (hcard : (cubicTorusOpenClusterFinset d N hN w).card = n) :
    w ∈ (ofConfiguration w hcard).clusterCylinder := by
  rw [clusterCylinder, mem_finiteCylinder]
  intro e heSupport
  rw [Finset.mem_union] at heSupport
  constructor
  · intro hew
    apply mem_torusFiniteClusterEdges.mpr
    constructor
    · rcases heSupport with he | he
      · exact (ofConfiguration w hcard).edges_subset_incident he
      · exact (Finset.mem_sdiff.mp he).1
    · exact hew
  · intro heA
    exact (mem_torusFiniteClusterEdges
      (d := d) (N := N) (hN := hN)
      (S := cubicTorusOpenClusterFinset d N hN w)).mp heA |>.2

theorem eq_of_mem_clusterCylinder
    (A B : CubicTorusBondAnimal d N n hN)
    {w : CubicTorusEdgeConfiguration d N}
    (hA : w ∈ A.clusterCylinder) (hB : w ∈ B.clusterCylinder) : A = B := by
  have hV : A.vertices = B.vertices := by
    rw [← A.torusOpenClusterFinset_eq_vertices_of_mem_clusterCylinder hA,
      ← B.torusOpenClusterFinset_eq_vertices_of_mem_clusterCylinder hB]
  have hE : A.edges = B.edges := by
    ext e
    constructor <;> intro he
    · have hew := (mem_finiteCylinder.mp hA e
          (Finset.mem_union_left _ he)).mpr he
      by_contra heB
      have heIncB : e ∈ cubicTorusIncidentEdges d N hN B.vertices := by
        simpa [hV] using A.edges_subset_incident he
      have heBd : e ∈ B.boundary := Finset.mem_sdiff.mpr ⟨heIncB, heB⟩
      exact heB ((mem_finiteCylinder.mp hB e
        (Finset.mem_union_right _ heBd)).mp hew)
    · have hew := (mem_finiteCylinder.mp hB e
          (Finset.mem_union_left _ he)).mpr he
      by_contra heA'
      have heIncA : e ∈ cubicTorusIncidentEdges d N hN A.vertices := by
        simpa [hV] using B.edges_subset_incident he
      have heAd : e ∈ A.boundary := Finset.mem_sdiff.mpr ⟨heIncA, heA'⟩
      exact heA' ((mem_finiteCylinder.mp hA e
        (Finset.mem_union_right _ heAd)).mp hew)
  cases A
  cases B
  simp_all

theorem clusterCylinder_pairwiseDisjoint :
    Pairwise (Function.onFun Disjoint
      fun A : CubicTorusBondAnimal d N n hN ↦ A.clusterCylinder) := by
  intro A B hAB
  change Disjoint A.clusterCylinder B.clusterCylinder
  rw [Set.disjoint_left]
  intro w hA hB
  exact hAB (eq_of_mem_clusterCylinder A B hA hB)

theorem measurableSet_clusterCylinder (A : CubicTorusBondAnimal d N n hN) :
    MeasurableSet A.clusterCylinder :=
  measurableSet_finiteCylinder A.edges_subset_support

theorem torusBondMeasure_real_clusterCylinder
    (A : CubicTorusBondAnimal d N n hN) (p : I) :
    (torusBondMeasure d N p).real A.clusterCylinder =
      (p : ℝ) ^ A.edges.card * (1 - (p : ℝ)) ^ A.boundary.card := by
  unfold torusBondMeasure clusterCylinder
  rw [setBernoulli_real_finiteCylinder A.edges_subset_support p]
  unfold finiteBernoulliWeight
  rw [Finset.card_union_of_disjoint A.edges_disjoint_boundary,
    Nat.add_sub_cancel_left]

end CubicTorusBondAnimal

/-- The finite periodic coefficient `a⁽ᴺ⁾ₙₘᵦ`. -/
noncomputable def cubicTorusAnimalCount (d N n m b : ℕ) (hN : 2 ≤ N) : ℕ :=
  Fintype.card {A : CubicTorusBondAnimal d N n hN //
    A.edges.card = m ∧ A.boundary.card = b}

/-- Appendix I coefficient stabilization: for `n < N`, the periodic animal table is the
infinite-lattice table, profile by profile. -/
theorem cubicTorusAnimalCount_eq_cubicAnimalCount
    {d N n : ℕ} (hN : 2 ≤ N) (hnN : n < N) (m b : ℕ) :
    cubicTorusAnimalCount d N n m b hN = cubicAnimalCount d n m b := by
  unfold cubicTorusAnimalCount cubicAnimalCount
  exact (Fintype.card_congr
    (CubicTorusBondAnimal.smallAnimalProfileEquiv (hN := hN) hnN m b)).symm

def torusFiniteClusterSizeEvent (d N : ℕ) (hN : 2 ≤ N) (n : ℕ) :
    Set (CubicTorusEdgeConfiguration d N) :=
  {w | (cubicTorusOpenClusterFinset d N hN w).card = n}

noncomputable def torusFiniteClusterSizeProbability
    (d N : ℕ) (hN : 2 ≤ N) (p : I) (n : ℕ) : ℝ :=
  (torusBondMeasure d N p).real (torusFiniteClusterSizeEvent d N hN n)

theorem iUnion_torusBondAnimal_clusterCylinder (d N n : ℕ) (hN : 2 ≤ N) :
    (⋃ A : CubicTorusBondAnimal d N n hN, A.clusterCylinder) =
      torusFiniteClusterSizeEvent d N hN n := by
  ext w
  constructor
  · intro hw
    obtain ⟨A, hA⟩ := Set.mem_iUnion.mp hw
    have hcluster := A.torusOpenClusterFinset_eq_vertices_of_mem_clusterCylinder hA
    change (cubicTorusOpenClusterFinset d N hN w).card = n
    rw [hcluster, A.vertices_card]
  · intro hw
    exact Set.mem_iUnion.mpr
      ⟨CubicTorusBondAnimal.ofConfiguration w hw,
        CubicTorusBondAnimal.ofConfiguration_mem_clusterCylinder w hw⟩

theorem torusFiniteClusterSizeProbability_eq_sum_animals
    (d N n : ℕ) (hN : 2 ≤ N) (p : I) :
    torusFiniteClusterSizeProbability d N hN p n =
      ∑ A : CubicTorusBondAnimal d N n hN,
        (p : ℝ) ^ A.edges.card * (1 - (p : ℝ)) ^ A.boundary.card := by
  let F : CubicTorusBondAnimal d N n hN → Set (CubicTorusEdgeConfiguration d N) :=
    fun A ↦ A.clusterCylinder
  have hsum := measureReal_iUnion_fintype
    (μ := torusBondMeasure d N p)
    (f := fun A : CubicTorusBondAnimal d N n hN ↦ A.clusterCylinder)
    (CubicTorusBondAnimal.clusterCylinder_pairwiseDisjoint)
    (fun A ↦ A.measurableSet_clusterCylinder)
  change (torusBondMeasure d N p).real (torusFiniteClusterSizeEvent d N hN n) = _
  rw [← iUnion_torusBondAnimal_clusterCylinder d N n hN]
  calc
    (torusBondMeasure d N p).real
        (⋃ A : CubicTorusBondAnimal d N n hN, A.clusterCylinder) =
        ∑ A : CubicTorusBondAnimal d N n hN,
          (torusBondMeasure d N p).real A.clusterCylinder := hsum
    _ = _ := by
      apply Finset.sum_congr rfl
      intro A _hA
      exact A.torusBondMeasure_real_clusterCylinder p

/-- The exact origin-cluster size law stabilizes once the periodic covering radius exceeds the
cluster size.  This is the probabilistic core of Grimmett's Appendix I. -/
theorem torusFiniteClusterSizeProbability_eq_finiteClusterSizeProbability
    {d N n : ℕ} (hN : 2 ≤ N) (hnN : n < N) (p : I) :
    torusFiniteClusterSizeProbability d N hN p n =
      finiteClusterSizeProbability d p n := by
  rw [torusFiniteClusterSizeProbability_eq_sum_animals d N n hN p,
    finiteClusterSizeProbability_eq_sum_animals d n p]
  let e := CubicTorusBondAnimal.smallAnimalEquiv (d := d) (hN := hN) hnN
  calc
    (∑ A : CubicTorusBondAnimal d N n hN,
        (p : ℝ) ^ A.edges.card * (1 - (p : ℝ)) ^ A.boundary.card) =
        ∑ A : CubicBondAnimal d n,
          (p : ℝ) ^ (e A).edges.card *
            (1 - (p : ℝ)) ^ (e A).boundary.card := by
      exact (e.sum_comp fun A ↦
        (p : ℝ) ^ A.edges.card * (1 - (p : ℝ)) ^ A.boundary.card).symm
    _ = ∑ A : CubicBondAnimal d n,
        (p : ℝ) ^ A.edges.card * (1 - (p : ℝ)) ^ A.boundary.card := by
      apply Finset.sum_congr rfl
      intro A _hA
      change (p : ℝ) ^
          (CubicTorusBondAnimal.ofCubicBondAnimal (hN := hN) hnN A).edges.card *
            (1 - (p : ℝ)) ^
              (CubicTorusBondAnimal.ofCubicBondAnimal
                (hN := hN) hnN A).boundary.card = _
      rw [CubicTorusBondAnimal.ofCubicBondAnimal_edges_card (hN := hN) hnN A,
        CubicTorusBondAnimal.ofCubicBondAnimal_boundary_card (hN := hN) hnN A]

def torusClusterSizeTrace (d N : ℕ) (hN : 2 ≤ N) (n : ℕ) :
    Set (Finset (CubicTorusEdge d N)) :=
  {ω | (cubicTorusOpenClusterFinset d N hN
    (ω : Set (CubicTorusEdge d N))).card = n}

theorem dependsOn_torusFiniteClusterSizeEvent (d N : ℕ) (hN : 2 ≤ N) (n : ℕ) :
    DependsOn (cubicTorusEdgeFinset d N hN)
      (torusFiniteClusterSizeEvent d N hN n) := by
  intro ω η hagree
  have hωη : ω = η := by
    ext e
    exact hagree e (mem_cubicTorusEdgeFinset hN e)
  subst η
  rfl

theorem torusFiniteClusterSizeProbability_eq_finiteBernoulliProbability
    (d N : ℕ) (hN : 2 ≤ N) (p : I) (n : ℕ) :
    torusFiniteClusterSizeProbability d N hN p n =
      finiteBernoulliProbability (cubicTorusEdgeFinset d N hN) p
        (torusClusterSizeTrace d N hN n) := by
  unfold torusFiniteClusterSizeProbability torusBondMeasure
  rw [(dependsOn_torusFiniteClusterSizeEvent d N hN n).setBernoulli_real_eq_finiteBernoulliProbability]
  rfl

theorem finiteBernoulliProbability_torusClusterSizeTrace_eq_filter_sum
    (d N : ℕ) (hN : 2 ≤ N) (p : ℝ) (n : ℕ) :
    finiteBernoulliProbability (cubicTorusEdgeFinset d N hN) p
        (torusClusterSizeTrace d N hN n) =
      Finset.sum
        ((cubicTorusEdgeFinset d N hN).powerset.filter fun
          ω : Finset (CubicTorusEdge d N) ↦
            (cubicTorusOpenClusterFinset d N hN
              (ω : Set (CubicTorusEdge d N))).card = n)
        (finiteBernoulliWeight (cubicTorusEdgeFinset d N hN) p) := by
  classical
  unfold finiteBernoulliProbability finiteBernoulliExpectation
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro ω hω
  by_cases hcard : (cubicTorusOpenClusterFinset d N hN
      (ω : Set (CubicTorusEdge d N))).card = n
  · simp [torusClusterSizeTrace, hcard]
  · simp [torusClusterSizeTrace, hcard]

theorem torusFiniteBernoulliExpectation_eq_sum_clusterSizes
    (d N : ℕ) (hN : 2 ≤ N) (p : ℝ) (F : ℕ → ℝ) :
    finiteBernoulliExpectation (cubicTorusEdgeFinset d N hN) p
        (fun ω ↦ F ((cubicTorusOpenClusterFinset d N hN
          (ω : Set (CubicTorusEdge d N))).card)) =
      ∑ n ∈ Finset.range ((cubicTorusVertexFinset d N hN).card + 1),
        F n * finiteBernoulliProbability (cubicTorusEdgeFinset d N hN) p
          (torusClusterSizeTrace d N hN n) := by
  classical
  let E := cubicTorusEdgeFinset d N hN
  let V := cubicTorusVertexFinset d N hN
  let g : Finset (CubicTorusEdge d N) → ℕ := fun ω ↦
    (cubicTorusOpenClusterFinset d N hN
      (ω : Set (CubicTorusEdge d N))).card
  let f : Finset (CubicTorusEdge d N) → ℝ := fun ω ↦
    finiteBernoulliWeight E p ω * F (g ω)
  have hmaps : ∀ ω ∈ E.powerset, g ω ∈ Finset.range (V.card + 1) := by
    intro ω hω
    rw [Finset.mem_range]
    have hsub : cubicTorusOpenClusterFinset d N hN
        (ω : Set (CubicTorusEdge d N)) ⊆ V := restrictTo_subset _ _
    exact Nat.lt_succ_of_le (Finset.card_le_card hsub)
  change ∑ ω ∈ E.powerset, f ω = _
  rw [← Finset.sum_fiberwise_of_maps_to hmaps f]
  apply Finset.sum_congr rfl
  intro n hn
  rw [finiteBernoulliProbability_torusClusterSizeTrace_eq_filter_sum]
  change (∑ ω ∈ E.powerset with g ω = n, f ω) =
    F n * ∑ ω ∈ E.powerset with g ω = n, finiteBernoulliWeight E p ω
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω hω
  have hcard := (Finset.mem_filter.mp hω).2
  simp only [f, hcard]
  ring

theorem sum_torusFiniteClusterSizeProbability_eq_one
    (d N : ℕ) (hN : 2 ≤ N) (p : I) :
    (∑ n ∈ Finset.range ((cubicTorusVertexFinset d N hN).card + 1),
      torusFiniteClusterSizeProbability d N hN p n) = 1 := by
  rw [show (∑ n ∈ Finset.range ((cubicTorusVertexFinset d N hN).card + 1),
      torusFiniteClusterSizeProbability d N hN p n) =
      ∑ n ∈ Finset.range ((cubicTorusVertexFinset d N hN).card + 1),
        (1 : ℝ) * finiteBernoulliProbability (cubicTorusEdgeFinset d N hN) p
          (torusClusterSizeTrace d N hN n) by
    apply Finset.sum_congr rfl
    intro n hn
    rw [one_mul,
      torusFiniteClusterSizeProbability_eq_finiteBernoulliProbability]]
  rw [← torusFiniteBernoulliExpectation_eq_sum_clusterSizes]
  exact finiteBernoulliExpectation_one _ _

theorem torusFiniteClusterSizeProbability_eq_zero_of_large
    (d N : ℕ) (hN : 2 ≤ N) (p : I) {n : ℕ}
    (hn : (cubicTorusVertexFinset d N hN).card < n) :
    torusFiniteClusterSizeProbability d N hN p n = 0 := by
  rw [torusFiniteClusterSizeProbability_eq_finiteBernoulliProbability,
    finiteBernoulliProbability_torusClusterSizeTrace_eq_filter_sum]
  apply Finset.sum_eq_zero
  intro ω hω
  exfalso
  have hcard := (Finset.mem_filter.mp hω).2
  have hsub : cubicTorusOpenClusterFinset d N hN
      (ω : Set (CubicTorusEdge d N)) ⊆ cubicTorusVertexFinset d N hN :=
    restrictTo_subset _ _
  have hle := Finset.card_le_card hsub
  omega

theorem summable_torusFiniteClusterSizeProbability
    (d N : ℕ) (hN : 2 ≤ N) (p : I) :
    Summable (torusFiniteClusterSizeProbability d N hN p) := by
  apply summable_of_ne_finset_zero
    (s := Finset.range ((cubicTorusVertexFinset d N hN).card + 1))
  intro n hn
  rw [Finset.mem_range, not_lt] at hn
  apply torusFiniteClusterSizeProbability_eq_zero_of_large d N hN p
  omega

theorem tsum_torusFiniteClusterSizeProbability_eq_one
    (d N : ℕ) (hN : 2 ≤ N) (p : I) :
    (∑' n : ℕ, torusFiniteClusterSizeProbability d N hN p n) = 1 := by
  rw [tsum_eq_sum (s := Finset.range
      ((cubicTorusVertexFinset d N hN).card + 1)) fun n hn ↦ by
    rw [Finset.mem_range, not_lt] at hn
    apply torusFiniteClusterSizeProbability_eq_zero_of_large d N hN p
    omega]
  exact sum_torusFiniteClusterSizeProbability_eq_one d N hN p

noncomputable def cubicTorusStepEdge (hN : 2 ≤ N)
    (x : CubicTorus d N) (a : CubicDirection d) : CubicTorusEdge d N :=
  ⟨s(x, cubicTorusStepFrom x a),
    (SimpleGraph.mem_edgeSet (cubicTorusGraph d N)).mpr
      (cubicTorusGraph_adj_stepFrom hN x a)⟩

theorem cubicTorusIncidentEdges_card_le (d N : ℕ) (hN : 2 ≤ N)
    (V : Finset (CubicTorus d N)) :
    (cubicTorusIncidentEdges d N hN V).card ≤ V.card * (2 * d) := by
  classical
  let F : Finset (CubicTorusEdge d N) := V.biUnion fun x ↦
    Finset.univ.image (cubicTorusStepEdge hN x)
  have hsub : cubicTorusIncidentEdges d N hN V ⊆ F := by
    intro e he
    obtain ⟨x, hxe, hxV⟩ := mem_cubicTorusIncidentEdges.mp he
    obtain ⟨y, hey⟩ := Sym2.mem_iff_exists.mp hxe
    have hxy : (cubicTorusGraph d N).Adj x y := by
      rw [← SimpleGraph.mem_edgeSet]
      exact hey ▸ e.2
    obtain ⟨a, ha⟩ := (cubicTorusGraph_adj_iff_exists_stepFrom hN x y).mp hxy
    apply Finset.mem_biUnion.mpr
    refine ⟨x, hxV, Finset.mem_image.mpr ⟨a, Finset.mem_univ _, ?_⟩⟩
    apply Subtype.ext
    simpa [cubicTorusStepEdge, ha] using hey.symm
  calc
    (cubicTorusIncidentEdges d N hN V).card ≤ F.card := Finset.card_le_card hsub
    _ ≤ ∑ x ∈ V, (Finset.univ : Finset (CubicDirection d)).card := by
      dsimp only [F]
      exact Finset.card_biUnion_le.trans <|
        Finset.sum_le_sum fun x hx ↦ Finset.card_image_le
    _ = V.card * (d * 2) := by simp [Fintype.card_prod]
    _ = V.card * (2 * d) := by rw [Nat.mul_comm d 2]

theorem CubicTorusBondAnimal.edges_card_le {d N n : ℕ} {hN : 2 ≤ N}
    (A : CubicTorusBondAnimal d N n hN) :
    A.edges.card ≤ n * (2 * d) := by
  calc
    A.edges.card ≤ (cubicTorusIncidentEdges d N hN A.vertices).card :=
      Finset.card_le_card A.edges_subset_incident
    _ ≤ A.vertices.card * (2 * d) := cubicTorusIncidentEdges_card_le d N hN A.vertices
    _ = n * (2 * d) := by rw [A.vertices_card]

theorem CubicTorusBondAnimal.boundary_card_le {d N n : ℕ} {hN : 2 ≤ N}
    (A : CubicTorusBondAnimal d N n hN) :
    A.boundary.card ≤ n * (2 * d) := by
  calc
    A.boundary.card ≤ (cubicTorusIncidentEdges d N hN A.vertices).card :=
      Finset.card_le_card Finset.sdiff_subset
    _ ≤ A.vertices.card * (2 * d) := cubicTorusIncidentEdges_card_le d N hN A.vertices
    _ = n * (2 * d) := by rw [A.vertices_card]

def cubicClusterSizePolynomial (d n : ℕ) (p : ℝ) : ℝ :=
  ∑ A : CubicBondAnimal d n,
    p ^ A.edges.card * (1 - p) ^ A.boundary.card

def cubicClusterSizePolynomialDerivative (d n : ℕ) (p : ℝ) : ℝ :=
  ∑ A : CubicBondAnimal d n,
    ((A.edges.card : ℝ) * p ^ (A.edges.card - 1) * (1 - p) ^ A.boundary.card -
      (A.boundary.card : ℝ) * p ^ A.edges.card *
        (1 - p) ^ (A.boundary.card - 1))

def torusClusterSizePolynomial (d N : ℕ) (hN : 2 ≤ N) (n : ℕ) (p : ℝ) : ℝ :=
  ∑ A : CubicTorusBondAnimal d N n hN,
    p ^ A.edges.card * (1 - p) ^ A.boundary.card

def torusClusterSizePolynomialDerivative
    (d N : ℕ) (hN : 2 ≤ N) (n : ℕ) (p : ℝ) : ℝ :=
  ∑ A : CubicTorusBondAnimal d N n hN,
    ((A.edges.card : ℝ) * p ^ (A.edges.card - 1) * (1 - p) ^ A.boundary.card -
      (A.boundary.card : ℝ) * p ^ A.edges.card *
        (1 - p) ^ (A.boundary.card - 1))

theorem cubicClusterSizePolynomial_eq_probability (d n : ℕ) (p : I) :
    cubicClusterSizePolynomial d n p = finiteClusterSizeProbability d p n := by
  rw [finiteClusterSizeProbability_eq_sum_animals]
  rfl

theorem torusClusterSizePolynomial_eq_probability
    (d N : ℕ) (hN : 2 ≤ N) (n : ℕ) (p : I) :
    torusClusterSizePolynomial d N hN n p =
      torusFiniteClusterSizeProbability d N hN p n := by
  rw [torusFiniteClusterSizeProbability_eq_sum_animals]
  rfl

theorem cubicClusterSizePolynomial_hasDerivAt (d n : ℕ) (p : ℝ) :
    HasDerivAt (cubicClusterSizePolynomial d n)
      (cubicClusterSizePolynomialDerivative d n p) p := by
  unfold cubicClusterSizePolynomial cubicClusterSizePolynomialDerivative
  apply HasDerivAt.fun_sum
  intro A hA
  have hterm := ((hasDerivAt_id p).pow A.edges.card |>.mul
    (((hasDerivAt_id p).neg.add_const 1).pow A.boundary.card))
  convert hterm using 1
  · funext y
    simp only [Pi.mul_apply, Pi.pow_apply, Function.id_def, Pi.neg_apply]
    ring
  · simp only [Pi.mul_apply, Pi.pow_apply, Function.id_def, Pi.neg_apply]
    ring

theorem torusClusterSizePolynomial_hasDerivAt
    (d N : ℕ) (hN : 2 ≤ N) (n : ℕ) (p : ℝ) :
    HasDerivAt (torusClusterSizePolynomial d N hN n)
      (torusClusterSizePolynomialDerivative d N hN n p) p := by
  unfold torusClusterSizePolynomial torusClusterSizePolynomialDerivative
  apply HasDerivAt.fun_sum
  intro A hA
  have hterm := ((hasDerivAt_id p).pow A.edges.card |>.mul
    (((hasDerivAt_id p).neg.add_const 1).pow A.boundary.card))
  convert hterm using 1
  · funext y
    simp only [Pi.mul_apply, Pi.pow_apply, Function.id_def, Pi.neg_apply]
    ring
  · simp only [Pi.mul_apply, Pi.pow_apply, Function.id_def, Pi.neg_apply]
    ring

theorem torusClusterSizePolynomial_eq_cubic (hN : 2 ≤ N) (hnN : n < N) (p : ℝ) :
    torusClusterSizePolynomial d N hN n p = cubicClusterSizePolynomial d n p := by
  let e := CubicTorusBondAnimal.smallAnimalEquiv (d := d) (hN := hN) hnN
  unfold torusClusterSizePolynomial cubicClusterSizePolynomial
  calc
    (∑ A : CubicTorusBondAnimal d N n hN,
        p ^ A.edges.card * (1 - p) ^ A.boundary.card) =
        ∑ A : CubicBondAnimal d n,
          p ^ (e A).edges.card * (1 - p) ^ (e A).boundary.card := by
      exact (e.sum_comp fun A ↦ p ^ A.edges.card * (1 - p) ^ A.boundary.card).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro A hA
      change p ^ (CubicTorusBondAnimal.ofCubicBondAnimal
          (hN := hN) hnN A).edges.card *
        (1 - p) ^ (CubicTorusBondAnimal.ofCubicBondAnimal
          (hN := hN) hnN A).boundary.card = _
      rw [CubicTorusBondAnimal.ofCubicBondAnimal_edges_card (hN := hN) hnN A,
        CubicTorusBondAnimal.ofCubicBondAnimal_boundary_card (hN := hN) hnN A]

theorem torusClusterSizePolynomialDerivative_eq_cubic
    (hN : 2 ≤ N) (hnN : n < N) (p : ℝ) :
    torusClusterSizePolynomialDerivative d N hN n p =
      cubicClusterSizePolynomialDerivative d n p := by
  have hfun : torusClusterSizePolynomial d N hN n =
      cubicClusterSizePolynomial d n :=
    funext fun q ↦ torusClusterSizePolynomial_eq_cubic hN hnN q
  have htorus := torusClusterSizePolynomial_hasDerivAt d N hN n p
  rw [hfun] at htorus
  exact htorus.unique (cubicClusterSizePolynomial_hasDerivAt d n p)

/-- The periodic ghost generating polynomial grouped by the origin-cluster size. -/
theorem torusGhostThetaByCluster_eq_sum_clusterSizes
    (d N : ℕ) (hN : 2 ≤ N) (p γ : ℝ) :
    torusGhostThetaByCluster d N hN p γ =
      ∑ n ∈ Finset.range ((cubicTorusVertexFinset d N hN).card + 1),
        (1 - (1 - γ) ^ n) *
          finiteBernoulliProbability (cubicTorusEdgeFinset d N hN) p
            (torusClusterSizeTrace d N hN n) := by
  exact torusFiniteBernoulliExpectation_eq_sum_clusterSizes d N hN p
    (fun n ↦ 1 - (1 - γ) ^ n)

end

end Percolation
