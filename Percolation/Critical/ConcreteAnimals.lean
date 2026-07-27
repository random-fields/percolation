import Percolation.Critical.Radius
import Percolation.Critical.LatticeAnimals
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# Concrete rooted bond animals in the cubic lattice

This file replaces the abstract coefficient table in Chapter 4 by actual finite connected
subgraphs of the cubic lattice.  The same objects are used for the animal expansions in
Grimmett Appendix I.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped ENNReal unitInterval BigOperators

/-- The finite set of every cubic edge incident to at least one vertex of `V`. -/
noncomputable def cubicIncidentEdges (d : ℕ) (V : Finset (Cubic d)) :
    Finset (CubicEdge d) := by
  classical
  exact V.biUnion fun x ↦ Finset.univ.image fun a : CubicDirection d ↦ cubicStepEdge x a

theorem cubicStepEdge_mem_cubicIncidentEdges {d : ℕ} {V : Finset (Cubic d)}
    {x : Cubic d} (hx : x ∈ V) (a : CubicDirection d) :
    cubicStepEdge x a ∈ cubicIncidentEdges d V := by
  classical
  simp only [cubicIncidentEdges, Finset.mem_biUnion, Finset.mem_image,
    Finset.mem_univ, true_and]
  exact ⟨x, hx, a, rfl⟩

theorem cubicIncidentEdges_card_le (d : ℕ) (V : Finset (Cubic d)) :
    (cubicIncidentEdges d V).card ≤ V.card * (2 * d) := by
  classical
  calc
    (cubicIncidentEdges d V).card ≤
        ∑ _x ∈ V, (Finset.univ : Finset (CubicDirection d)).card := by
      unfold cubicIncidentEdges
      exact (Finset.card_biUnion_le.trans <|
        Finset.sum_le_sum fun _ _ ↦ Finset.card_image_le)
    _ = V.card * (d * 2) := by simp [Fintype.card_prod]
    _ = V.card * (2 * d) := by rw [Nat.mul_comm d 2]

theorem mem_cubicIncidentEdges_of_endpoint {d : ℕ} {V : Finset (Cubic d)}
    {e : CubicEdge d} {x : Cubic d} (hxV : x ∈ V) (hxe : x ∈ (e : Sym2 (Cubic d))) :
    e ∈ cubicIncidentEdges d V := by
  classical
  obtain ⟨y, hey⟩ := Sym2.mem_iff_exists.mp hxe
  have hxy : (cubicGraph d).Adj x y := by
    rw [← SimpleGraph.mem_edgeSet]
    exact hey ▸ e.2
  obtain ⟨a, hya⟩ := (cubicGraph_adj_iff_exists_stepFrom x y).mp hxy
  have he : e = cubicStepEdge x a := by
    apply Subtype.ext
    simpa [cubicStepEdge, hya] using hey
  rw [he]
  exact cubicStepEdge_mem_cubicIncidentEdges hxV a

theorem mem_cubicIncidentEdges_iff_exists_endpoint {d : ℕ} {V : Finset (Cubic d)}
    {e : CubicEdge d} :
    e ∈ cubicIncidentEdges d V ↔ ∃ x ∈ V, x ∈ (e : Sym2 (Cubic d)) := by
  constructor
  · classical
    simp only [cubicIncidentEdges, Finset.mem_biUnion, Finset.mem_image,
      Finset.mem_univ, true_and]
    rintro ⟨x, hxV, a, rfl⟩
    exact ⟨x, hxV, by simp [cubicStepEdge]⟩
  · rintro ⟨x, hxV, hxe⟩
    exact mem_cubicIncidentEdges_of_endpoint hxV hxe

/-- A finite connected origin cluster with `n` vertices lies in the graph ball of radius
`n-1`.  The proof erases loops from an open witness and counts its distinct support. -/
theorem cubicOpenCluster_subset_metricBall_of_ncard_eq {d n : ℕ}
    {ω : EdgeConfiguration d} (hfinite : (cubicOpenCluster d ω).Finite)
    (hcard : (cubicOpenCluster d ω).ncard = n) :
    cubicOpenCluster d ω ⊆ (cubicMetricBall d cubicOrigin (n - 1) : Set (Cubic d)) := by
  intro y hy
  rcases hy with ⟨w, hopen⟩
  let q : (cubicGraph d).Walk cubicOrigin y := w.toPath
  have hqpath : q.IsPath := w.toPath.2
  have hqopen : walkIsOpen ω q := walkIsOpen_toPath w hopen
  have hsupport : q.support.toFinset ⊆ hfinite.toFinset := by
    intro z hz
    rw [List.mem_toFinset] at hz
    rw [Set.Finite.mem_toFinset]
    exact mem_cubicOpenClusterFrom_of_mem_support hqopen hz
  have hqcard : q.support.toFinset.card = q.length + 1 := by
    rw [List.toFinset_card_of_nodup hqpath.support_nodup,
      SimpleGraph.Walk.length_support]
  have hclcard : hfinite.toFinset.card = n := by
    rw [← Set.ncard_eq_toFinset_card (cubicOpenCluster d ω) hfinite, hcard]
  have hlen : q.length + 1 ≤ n := by
    rw [← hqcard, ← hclcard]
    exact Finset.card_le_card hsupport
  change y ∈ cubicMetricBall d cubicOrigin (n - 1)
  rw [mem_cubicMetricBall_iff_l1Dist_le]
  exact (cubicL1Dist_le_walk_length q).trans (by omega)

/-- All open cubic edges incident to a fixed finite origin cluster.  These are exactly the
occupied edges of the corresponding bond animal. -/
noncomputable def finiteClusterEdges {d : ℕ} (ω : EdgeConfiguration d)
    (hfinite : (cubicOpenCluster d ω).Finite) : Finset (CubicEdge d) := by
  classical
  exact (cubicIncidentEdges d hfinite.toFinset).filter fun e ↦ e ∈ ω

@[simp]
theorem mem_finiteClusterEdges {d : ℕ} {ω : EdgeConfiguration d}
    {hfinite : (cubicOpenCluster d ω).Finite} {e : CubicEdge d} :
    e ∈ finiteClusterEdges ω hfinite ↔
      e ∈ cubicIncidentEdges d hfinite.toFinset ∧ e ∈ ω := by
  simp [finiteClusterEdges]

theorem endpoint_mem_cubicOpenCluster_of_mem_finiteClusterEdges {d : ℕ}
    {ω : EdgeConfiguration d} {hfinite : (cubicOpenCluster d ω).Finite}
    {e : CubicEdge d} (he : e ∈ finiteClusterEdges ω hfinite)
    {y : Cubic d} (hy : y ∈ (e : Sym2 (Cubic d))) :
    y ∈ cubicOpenCluster d ω := by
  have hedata := mem_finiteClusterEdges.mp he
  obtain ⟨x, hxV, hxe⟩ := mem_cubicIncidentEdges_iff_exists_endpoint.mp hedata.1
  have hxC : x ∈ cubicOpenCluster d ω := by
    simpa using hxV
  obtain ⟨z, heq⟩ := Sym2.mem_iff_exists.mp hxe
  have hy' : y = x ∨ y = z := by
    rw [heq, Sym2.mem_iff] at hy
    exact hy
  rcases hy' with hyx | hyz
  · simpa [hyx] using hxC
  · have hzC : z ∈ cubicOpenCluster d ω := by
      rcases hxC with ⟨w, hw⟩
      have hxz : (cubicGraph d).Adj x z := by
        rw [← SimpleGraph.mem_edgeSet]
        exact heq ▸ e.2
      refine ⟨w.concat hxz, ?_⟩
      rw [SimpleGraph.Walk.concat_eq_append]
      apply walkIsOpen_append hw
      intro f hf
      simp only [SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil,
        List.mem_singleton] at hf
      have hfedge : f ∈ (cubicGraph d).edgeSet := by
        rw [hf]
        exact (SimpleGraph.mem_edgeSet (cubicGraph d)).mpr hxz
      have hfe : (⟨f, hfedge⟩ : CubicEdge d) = e := by
        apply Subtype.ext
        exact hf.trans heq.symm
      simpa [hfe] using hedata.2
    simpa [hyz] using hzC

theorem cubicEdge_mem_cubicMetricBallEdges_of_out_mem {d n : ℕ} {x : Cubic d}
    {e : CubicEdge d}
    (hu : e.1.out.1 ∈ cubicMetricBall d x n)
    (hv : e.1.out.2 ∈ cubicMetricBall d x n) :
    e ∈ cubicMetricBallEdges d x n := by
  have hadj : (cubicGraph d).Adj e.1.out.1 e.1.out.2 := by
    rw [← SimpleGraph.mem_edgeSet]
    convert e.2 using 1
    exact e.1.out_eq
  obtain ⟨a, ha⟩ := (cubicGraph_adj_iff_exists_stepFrom _ _).mp hadj
  have heq : e = cubicStepEdge e.1.out.1 a := by
    apply Subtype.ext
    change e.1 = s(e.1.out.1, cubicStepFrom e.1.out.1 a)
    rw [← ha]
    exact e.1.out_eq.symm
  rw [heq]
  exact cubicStepEdge_mem_cubicMetricBallEdges hu (ha ▸ hv)

/-- A concrete rooted finite bond animal with exactly `n` vertices.  The ambient ball bounds
make the type manifestly finite; connectivity proves that this bound loses no rooted animal. -/
structure CubicBondAnimal (d n : ℕ) where
  vertices : Finset (Cubic d)
  vertices_subset : vertices ⊆ cubicMetricBall d cubicOrigin (n - 1)
  edges : Finset (CubicEdge d)
  edges_subset : edges ⊆ cubicMetricBallEdges d cubicOrigin (n - 1)
  origin_mem : cubicOrigin ∈ vertices
  vertices_card : vertices.card = n
  edge_endpoints : ∀ e ∈ edges, ∀ x ∈ (e : Sym2 (Cubic d)), x ∈ vertices
  connected : ∀ x ∈ vertices,
    ∃ w : (cubicGraph d).Walk cubicOrigin x, walkEdgeFinset w ⊆ edges

namespace CubicBondAnimal

variable {d n : ℕ}

/-- The finite graph whose vertices and edges are exactly those of the animal. -/
noncomputable def graph (A : CubicBondAnimal d n) : SimpleGraph A.vertices where
  Adj u v := ∃ e ∈ A.edges, (e : Sym2 (Cubic d)) = s(u.1, v.1)
  symm := by
    rintro u v ⟨e, he, huv⟩
    exact ⟨e, he, huv.trans Sym2.eq_swap⟩
  loopless := ⟨by
    rintro u ⟨e, _he, heu⟩
    have hadj : (cubicGraph d).Adj u.1 u.1 := by
      rw [← SimpleGraph.mem_edgeSet]
      exact heu ▸ e.2
    exact (cubicGraph d).loopless.irrefl u.1 hadj⟩

noncomputable instance : DecidableEq (CubicBondAnimal d n) := Classical.decEq _

private def candidateEmbedding (d n : ℕ) :
    CubicBondAnimal d n ↪
      ({V // V ∈ (cubicMetricBall d cubicOrigin (n - 1)).powerset} ×
        {E // E ∈ (cubicMetricBallEdges d cubicOrigin (n - 1)).powerset}) where
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

instance : Finite (CubicBondAnimal d n) :=
  Finite.of_injective (candidateEmbedding d n) (candidateEmbedding d n).injective

noncomputable instance : Fintype (CubicBondAnimal d n) := Fintype.ofFinite _

/-- The canonical concrete animal encoded by a finite origin cluster. -/
noncomputable def ofFiniteCluster {ω : EdgeConfiguration d}
    (hfinite : (cubicOpenCluster d ω).Finite)
    (hcard : (cubicOpenCluster d ω).ncard = n) : CubicBondAnimal d n where
  vertices := hfinite.toFinset
  vertices_subset := by
    intro x hx
    exact cubicOpenCluster_subset_metricBall_of_ncard_eq hfinite hcard (by simpa using hx)
  edges := finiteClusterEdges ω hfinite
  edges_subset := by
    intro e he
    apply cubicEdge_mem_cubicMetricBallEdges_of_out_mem
    · exact cubicOpenCluster_subset_metricBall_of_ncard_eq hfinite hcard
        (endpoint_mem_cubicOpenCluster_of_mem_finiteClusterEdges he
          (Sym2.out_fst_mem e.1))
    · exact cubicOpenCluster_subset_metricBall_of_ncard_eq hfinite hcard
        (endpoint_mem_cubicOpenCluster_of_mem_finiteClusterEdges he
          (Sym2.out_snd_mem e.1))
  origin_mem := by
    rw [Set.Finite.mem_toFinset]
    exact ⟨SimpleGraph.Walk.nil, by intro e he; cases he⟩
  vertices_card := by
    rw [← Set.ncard_eq_toFinset_card (cubicOpenCluster d ω) hfinite, hcard]
  edge_endpoints := by
    intro e he x hx
    rw [Set.Finite.mem_toFinset]
    exact endpoint_mem_cubicOpenCluster_of_mem_finiteClusterEdges he hx
  connected := by
    intro x hx
    rw [Set.Finite.mem_toFinset] at hx
    rcases hx with ⟨w, hw⟩
    refine ⟨w, ?_⟩
    intro e he
    apply mem_finiteClusterEdges.mpr
    constructor
    · apply mem_cubicIncidentEdges_of_endpoint (x := e.1.out.1)
      · rw [Set.Finite.mem_toFinset]
        exact mem_cubicOpenClusterFrom_of_mem_support hw
          (w.mem_support_of_mem_edges ((mem_walkEdgeFinset_iff w e).mp he)
            (Sym2.out_fst_mem e.1))
      · exact Sym2.out_fst_mem e.1
    · simpa using hw e.1 ((mem_walkEdgeFinset_iff w e).mp he)

theorem nonempty_graph_walk_of_cubicWalk (A : CubicBondAnimal d n)
    {u v : Cubic d} (hu : u ∈ A.vertices) (hv : v ∈ A.vertices)
    (w : (cubicGraph d).Walk u v) (hw : walkEdgeFinset w ⊆ A.edges) :
    Nonempty (A.graph.Walk (⟨u, hu⟩ : A.vertices) (⟨v, hv⟩ : A.vertices)) := by
  induction w with
  | nil => exact ⟨.nil⟩
  | @cons u z v huz p ih =>
      let e : CubicEdge d := ⟨s(u, z), by
        rw [SimpleGraph.mem_edgeSet]
        exact huz⟩
      have hew : e ∈ walkEdgeFinset (SimpleGraph.Walk.cons huz p) := by
        rw [mem_walkEdgeFinset_iff]
        simp [e]
      have heA : e ∈ A.edges := hw hew
      have hz : z ∈ A.vertices := A.edge_endpoints e heA z (by simp [e])
      have htail : walkEdgeFinset p ⊆ A.edges := by
        intro f hf
        apply hw
        rw [mem_walkEdgeFinset_iff] at hf ⊢
        simp [hf]
      obtain ⟨q⟩ := ih hz hv htail
      have hadj : A.graph.Adj (⟨u, hu⟩ : A.vertices) ⟨z, hz⟩ := by
        exact ⟨e, heA, by rfl⟩
      exact ⟨SimpleGraph.Walk.cons hadj q⟩

theorem graph_connected (A : CubicBondAnimal d n) : A.graph.Connected := by
  letI : Nonempty A.vertices := ⟨⟨cubicOrigin, A.origin_mem⟩⟩
  refine ⟨fun u v ↦ ?_⟩
  obtain ⟨wu, hu⟩ := A.connected u.1 u.2
  obtain ⟨wv, hv⟩ := A.connected v.1 v.2
  obtain ⟨qu⟩ := nonempty_graph_walk_of_cubicWalk A A.origin_mem u.2 wu hu
  obtain ⟨qv⟩ := nonempty_graph_walk_of_cubicWalk A A.origin_mem v.2 wv hv
  exact qu.reachable.symm.trans qv.reachable

noncomputable def edgeEmbedding (A : CubicBondAnimal d n) :
    A.edges ↪ A.graph.edgeSet where
  toFun e := by
    let u : A.vertices :=
      ⟨e.1.1.out.1, A.edge_endpoints e.1 e.2 _ (Sym2.out_fst_mem e.1.1)⟩
    let v : A.vertices :=
      ⟨e.1.1.out.2, A.edge_endpoints e.1 e.2 _ (Sym2.out_snd_mem e.1.1)⟩
    exact ⟨s(u, v), by
      rw [SimpleGraph.mem_edgeSet]
      exact ⟨e.1, e.2, e.1.1.out_eq.symm⟩⟩
  inj' := by
    intro e f hef
    apply Subtype.ext
    apply Subtype.ext
    change (⟨s(⟨e.1.1.out.1, _⟩, ⟨e.1.1.out.2, _⟩), _⟩ : A.graph.edgeSet) =
      ⟨s(⟨f.1.1.out.1, _⟩, ⟨f.1.1.out.2, _⟩), _⟩ at hef
    have hval := congrArg (fun z : A.graph.edgeSet ↦
      Sym2.map (fun x : A.vertices ↦ x.1) z.1) hef
    have hout : s(e.1.1.out.1, e.1.1.out.2) =
        s(f.1.1.out.1, f.1.1.out.2) := by simpa using hval
    exact e.1.1.out_eq.symm.trans (hout.trans f.1.1.out_eq)

theorem edgeEmbedding_surjective (A : CubicBondAnimal d n) :
    Function.Surjective A.edgeEmbedding := by
  intro z
  let u := z.1.out.1
  let v := z.1.out.2
  have huv : A.graph.Adj u v := by
    have hz := z.2
    rw [← z.1.out_eq, SimpleGraph.mem_edgeSet] at hz
    exact hz
  rcases huv with ⟨e, heA, heuv⟩
  let eA : A.edges := ⟨e, heA⟩
  refine ⟨eA, ?_⟩
  apply Subtype.ext
  have hout : s(e.1.out.1, e.1.out.2) = s(u.1, v.1) := by
    exact e.1.out_eq.trans heuv
  rcases Sym2.eq_iff.mp hout with h | h
  · have hu : (⟨e.1.out.1,
        A.edge_endpoints e heA _ (Sym2.out_fst_mem e.1)⟩ : A.vertices) = u :=
      Subtype.ext h.1
    have hv : (⟨e.1.out.2,
        A.edge_endpoints e heA _ (Sym2.out_snd_mem e.1)⟩ : A.vertices) = v :=
      Subtype.ext h.2
    change s(⟨e.1.out.1, _⟩, ⟨e.1.out.2, _⟩) = z.1
    rw [hu, hv]
    exact z.1.out_eq
  · have hu : (⟨e.1.out.1,
        A.edge_endpoints e heA _ (Sym2.out_fst_mem e.1)⟩ : A.vertices) = v :=
      Subtype.ext h.1
    have hv : (⟨e.1.out.2,
        A.edge_endpoints e heA _ (Sym2.out_snd_mem e.1)⟩ : A.vertices) = u :=
      Subtype.ext h.2
    rw [show (A.edgeEmbedding eA).1 = s(v, u) by
      change s(⟨e.1.out.1, _⟩, ⟨e.1.out.2, _⟩) = s(v, u)
      rw [hu, hv]]
    rw [Sym2.eq_swap]
    exact z.1.out_eq

theorem graph_edgeSet_card (A : CubicBondAnimal d n) :
    Nat.card A.graph.edgeSet = A.edges.card := by
  let equiv : A.edges ≃ A.graph.edgeSet := Equiv.ofBijective A.edgeEmbedding
    ⟨A.edgeEmbedding.injective, edgeEmbedding_surjective A⟩
  calc
    Nat.card A.graph.edgeSet = Nat.card A.edges := Nat.card_congr equiv.symm
    _ = A.edges.card := by simp

/-- Every neighbor of a vertex in the animal graph determines a unique signed cubic
direction.  This is the local degree comparison needed for `|E(A)| ≤ d |V(A)|`. -/
noncomputable def neighborDirectionEmbedding (A : CubicBondAnimal d n) (u : A.vertices) :
    A.graph.neighborSet u ↪ CubicDirection d where
  toFun v := Classical.choose <| (cubicGraph_adj_iff_exists_stepFrom u.1 v.1.1).mp <| by
    rcases v.2 with ⟨e, he, huv⟩
    rw [← SimpleGraph.mem_edgeSet]
    exact huv ▸ e.2
  inj' := by
    intro v w hvw
    apply Subtype.ext
    apply Subtype.ext
    have hv := Classical.choose_spec <|
      (cubicGraph_adj_iff_exists_stepFrom u.1 v.1.1).mp <| by
        rcases v.2 with ⟨e, he, huv⟩
        rw [← SimpleGraph.mem_edgeSet]
        exact huv ▸ e.2
    have hw := Classical.choose_spec <|
      (cubicGraph_adj_iff_exists_stepFrom u.1 w.1.1).mp <| by
        rcases w.2 with ⟨e, he, huw⟩
        rw [← SimpleGraph.mem_edgeSet]
        exact huw ▸ e.2
    rw [show (Classical.choose <|
      (cubicGraph_adj_iff_exists_stepFrom u.1 v.1.1).mp <| by
        rcases v.2 with ⟨e, he, huv⟩
        rw [← SimpleGraph.mem_edgeSet]
        exact huv ▸ e.2) =
      (Classical.choose <|
        (cubicGraph_adj_iff_exists_stepFrom u.1 w.1.1).mp <| by
          rcases w.2 with ⟨e, he, huw⟩
          rw [← SimpleGraph.mem_edgeSet]
          exact huw ▸ e.2) from hvw] at hv
    exact hv.trans hw.symm

noncomputable instance graphAdjDecidable (A : CubicBondAnimal d n) :
    DecidableRel A.graph.Adj := Classical.decRel _

theorem graph_degree_le_two_mul (A : CubicBondAnimal d n) (u : A.vertices) :
    A.graph.degree u ≤ 2 * d := by
  classical
  calc
    A.graph.degree u = Fintype.card (A.graph.neighborSet u) :=
      (A.graph.card_neighborSet_eq_degree u).symm
    _ ≤ Fintype.card (CubicDirection d) :=
      Fintype.card_le_of_injective (A.neighborDirectionEmbedding u)
        (A.neighborDirectionEmbedding u).injective
    _ = 2 * d := by simp [Fintype.card_prod, Nat.mul_comm]

theorem edges_card_upper (A : CubicBondAnimal d n) : A.edges.card ≤ d * n := by
  classical
  have hsum : ∑ u : A.vertices, A.graph.degree u ≤ n * (2 * d) := by
    calc
      ∑ u : A.vertices, A.graph.degree u ≤ ∑ _u : A.vertices, 2 * d :=
        Finset.sum_le_sum fun u _hu ↦ A.graph_degree_le_two_mul u
      _ = n * (2 * d) := by simp [A.vertices_card]
  have hedge : Fintype.card A.graph.edgeSet = A.edges.card := by
    rw [← Nat.card_eq_fintype_card]
    exact graph_edgeSet_card A
  have htwo : 2 * A.edges.card ≤ n * (2 * d) := by
    calc
      2 * A.edges.card = 2 * A.graph.edgeFinset.card := by
        rw [SimpleGraph.edgeFinset_card, hedge]
      _ = ∑ u : A.vertices, A.graph.degree u :=
        A.graph.sum_degrees_eq_twice_card_edges.symm
      _ ≤ n * (2 * d) := hsum
  exact Nat.le_of_mul_le_mul_left (by
    calc
      2 * A.edges.card ≤ n * (2 * d) := htwo
      _ = 2 * (d * n) := by ac_rfl) (by omega)

theorem vertices_card_le_edges_card_add_one (A : CubicBondAnimal d n) :
    n ≤ A.edges.card + 1 := by
  have h := A.graph_connected.card_vert_le_card_edgeSet_add_one
  rw [graph_edgeSet_card A] at h
  simpa [A.vertices_card] using h

theorem edges_card_lower (A : CubicBondAnimal d n) : n - 1 ≤ A.edges.card := by
  have := vertices_card_le_edges_card_add_one A
  omega

/-- The closed edge boundary `ΔA`: every incident cubic edge not occupied by the animal. -/
noncomputable def boundary (A : CubicBondAnimal d n) : Finset (CubicEdge d) :=
  cubicIncidentEdges d A.vertices \ A.edges

theorem boundary_card_le (A : CubicBondAnimal d n) :
    A.boundary.card ≤ 2 * d * n := by
  calc
    A.boundary.card ≤ (cubicIncidentEdges d A.vertices).card :=
      Finset.card_le_card Finset.sdiff_subset
    _ ≤ A.vertices.card * (2 * d) := cubicIncidentEdges_card_le d A.vertices
    _ = 2 * d * n := by simp [A.vertices_card, Nat.mul_comm, Nat.mul_left_comm]

theorem edges_subset_incident (A : CubicBondAnimal d n) :
    A.edges ⊆ cubicIncidentEdges d A.vertices := by
  intro e he
  exact mem_cubicIncidentEdges_of_endpoint
    (A.edge_endpoints e he e.1.out.1 (Sym2.out_fst_mem e.1)) (Sym2.out_fst_mem e.1)

theorem edges_disjoint_boundary (A : CubicBondAnimal d n) :
    Disjoint (A.edges : Set (CubicEdge d)) (A.boundary : Set (CubicEdge d)) := by
  rw [Set.disjoint_left]
  intro e heA heB
  exact (Finset.mem_sdiff.mp heB).2 heA

/-- A nonempty finite animal in a positive-dimensional cubic lattice has a boundary edge.
Choose a vertex maximizing one coordinate and step once in the positive direction. -/
theorem boundary_nonempty (A : CubicBondAnimal d n) (hd : 0 < d) :
    A.boundary.Nonempty := by
  classical
  let i : Fin d := ⟨0, hd⟩
  have hV : A.vertices.Nonempty := ⟨cubicOrigin, A.origin_mem⟩
  have hI : (A.vertices.image fun x ↦ x i).Nonempty := hV.image _
  let M : ℤ := (A.vertices.image fun x ↦ x i).max' hI
  have hMmem : M ∈ A.vertices.image fun x ↦ x i := by
    exact Finset.max'_mem _ hI
  obtain ⟨x, hxA, hxM⟩ := Finset.mem_image.mp hMmem
  let e : CubicEdge d := cubicStepEdge x (i, true)
  refine ⟨e, Finset.mem_sdiff.mpr ⟨cubicStepEdge_mem_cubicIncidentEdges hxA (i, true), ?_⟩⟩
  intro heA
  have hyA : cubicStepFrom x (i, true) ∈ A.vertices :=
    A.edge_endpoints e heA _ (by simp [e, cubicStepEdge])
  have hyI : cubicStepFrom x (i, true) i ∈ A.vertices.image fun y ↦ y i :=
    Finset.mem_image.mpr ⟨_, hyA, rfl⟩
  have hle : cubicStepFrom x (i, true) i ≤ M :=
    Finset.le_max' _ _ hyI
  dsimp [M] at hxM hle
  rw [← hxM] at hle
  simp [cubicStepFrom, cubicDirectionIncrement] at hle

theorem boundary_card_pos (A : CubicBondAnimal d n) (hd : 0 < d) :
    0 < A.boundary.card :=
  Finset.card_pos.mpr (A.boundary_nonempty hd)

/-- Cylinder in which the animal edges are open and every edge of its external edge boundary
is closed. -/
def clusterCylinder (A : CubicBondAnimal d n) : Set (EdgeConfiguration d) :=
  openEdgeSetEvent d A.edges ∩ closedEdgeSetEvent d A.boundary

theorem ofFiniteCluster_mem_clusterCylinder {ω : EdgeConfiguration d}
    (hfinite : (cubicOpenCluster d ω).Finite)
    (hcard : (cubicOpenCluster d ω).ncard = n) :
    ω ∈ (ofFiniteCluster hfinite hcard).clusterCylinder := by
  constructor
  · rw [mem_openEdgeSetEvent]
    intro e he
    exact (mem_finiteClusterEdges.mp he).2
  · rw [mem_closedEdgeSetEvent, Set.disjoint_left]
    intro e heBoundary heOpen
    have heData := Finset.mem_sdiff.mp heBoundary
    exact heData.2 (mem_finiteClusterEdges.mpr ⟨heData.1, heOpen⟩)

theorem measurableSet_clusterCylinder (A : CubicBondAnimal d n) :
    MeasurableSet A.clusterCylinder :=
  (measurableSet_openEdgeSetEvent d A.edges).inter
    (measurableSet_closedEdgeSetEvent d A.boundary)

theorem bernoulliBondMeasure_real_clusterCylinder (A : CubicBondAnimal d n) (p : I) :
    (bernoulliBondMeasure d p).real A.clusterCylinder =
      (p : ℝ) ^ A.edges.card * (1 - (p : ℝ)) ^ A.boundary.card := by
  exact bernoulliBondMeasure_real_openEdgeSetEvent_inter_closedEdgeSetEvent
    d p A.edges A.boundary A.edges_disjoint_boundary

/-- An open walk starting in an animal cannot cross its closed edge boundary. -/
theorem endpoint_mem_vertices_of_walkIsOpen_of_mem_clusterCylinder
    (A : CubicBondAnimal d n) {ω : EdgeConfiguration d} (hω : ω ∈ A.clusterCylinder)
    {u v : Cubic d} (hu : u ∈ A.vertices) (w : (cubicGraph d).Walk u v)
    (hopen : walkIsOpen ω w) : v ∈ A.vertices := by
  induction w with
  | nil => exact hu
  | @cons u z v huz p ih =>
      let e : CubicEdge d := ⟨s(u, z), by
        rw [SimpleGraph.mem_edgeSet]
        exact huz⟩
      have heopen : e ∈ ω := hopen e (by simp [e])
      have hz : z ∈ A.vertices := by
        by_contra hzA
        have heincident : e ∈ cubicIncidentEdges d A.vertices :=
          mem_cubicIncidentEdges_of_endpoint hu (by simp [e])
        have heA : e ∉ A.edges := by
          intro heA
          exact hzA (A.edge_endpoints e heA z (by simp [e]))
        have hebound : e ∈ A.boundary := Finset.mem_sdiff.mpr ⟨heincident, heA⟩
        have hclosed := (mem_closedEdgeSetEvent d A.boundary ω).mp hω.2
        exact Set.disjoint_left.mp hclosed hebound heopen
      have hpopen : walkIsOpen ω p := by
        intro f hf
        exact hopen f (by simp [hf])
      exact ih hz hpopen

/-- The cylinder really describes the exact origin cluster: no abstract coefficient table is
used. -/
theorem cubicOpenCluster_eq_vertices_of_mem_clusterCylinder
    (A : CubicBondAnimal d n) {ω : EdgeConfiguration d} (hω : ω ∈ A.clusterCylinder) :
    cubicOpenCluster d ω = (A.vertices : Set (Cubic d)) := by
  ext x
  constructor
  · rintro ⟨w, hopen⟩
    exact A.endpoint_mem_vertices_of_walkIsOpen_of_mem_clusterCylinder hω
      A.origin_mem w hopen
  · intro hx
    obtain ⟨w, hwA⟩ := A.connected x hx
    refine ⟨w, ?_⟩
    intro e hew
    let e' : CubicEdge d := ⟨e, w.edges_subset_edgeSet hew⟩
    have heA : e' ∈ A.edges := hwA ((mem_walkEdgeFinset_iff w e').mpr hew)
    exact (mem_openEdgeSetEvent d A.edges ω).mp hω.1 heA

theorem eq_of_mem_clusterCylinder (A B : CubicBondAnimal d n) {ω : EdgeConfiguration d}
    (hA : ω ∈ A.clusterCylinder) (hB : ω ∈ B.clusterCylinder) : A = B := by
  have hvertices : A.vertices = B.vertices := by
    have hAc := A.cubicOpenCluster_eq_vertices_of_mem_clusterCylinder hA
    have hBc := B.cubicOpenCluster_eq_vertices_of_mem_clusterCylinder hB
    exact Finset.coe_injective (hAc.symm.trans hBc)
  have hedges : A.edges = B.edges := by
    ext e
    constructor
    · intro heA
      by_contra heB
      have heincA := A.edges_subset_incident heA
      have heincB : e ∈ cubicIncidentEdges d B.vertices := by
        simpa [hvertices] using heincA
      have heboundB : e ∈ B.boundary := Finset.mem_sdiff.mpr ⟨heincB, heB⟩
      have heopen : e ∈ ω := (mem_openEdgeSetEvent d A.edges ω).mp hA.1 heA
      exact Set.disjoint_left.mp ((mem_closedEdgeSetEvent d B.boundary ω).mp hB.2)
        heboundB heopen
    · intro heB
      by_contra heA
      have heincB := B.edges_subset_incident heB
      have heincA : e ∈ cubicIncidentEdges d A.vertices := by
        simpa [hvertices] using heincB
      have heboundA : e ∈ A.boundary := Finset.mem_sdiff.mpr ⟨heincA, heA⟩
      have heopen : e ∈ ω := (mem_openEdgeSetEvent d B.edges ω).mp hB.1 heB
      exact Set.disjoint_left.mp ((mem_closedEdgeSetEvent d A.boundary ω).mp hA.2)
        heboundA heopen
  cases A
  cases B
  simp_all

theorem clusterCylinder_pairwiseDisjoint :
    Pairwise (Function.onFun Disjoint fun A : CubicBondAnimal d n ↦ A.clusterCylinder) := by
  intro A B hAB
  change Disjoint A.clusterCylinder B.clusterCylinder
  rw [Set.disjoint_left]
  intro ω hA hB
  exact hAB (eq_of_mem_clusterCylinder A B hA hB)

end CubicBondAnimal

/-- The concrete coefficient `aₙₘᵦ`. -/
noncomputable def cubicAnimalCount (d n m b : ℕ) : ℕ :=
  Fintype.card {A : CubicBondAnimal d n // A.edges.card = m ∧ A.boundary.card = b}

/-- The defining coefficient inequality for the concrete animal table.  It follows because
distinct exact-cluster cylinders are disjoint and all have the same Bernoulli probability. -/
theorem cubicAnimalCount_mul_weight_le_one (d n m b : ℕ) (p : I) :
    (cubicAnimalCount d n m b : ℝ) * (p : ℝ) ^ m * (1 - (p : ℝ)) ^ b ≤ 1 := by
  classical
  let T := {A : CubicBondAnimal d n // A.edges.card = m ∧ A.boundary.card = b}
  let F : T → Set (EdgeConfiguration d) := fun A ↦ A.1.clusterCylinder
  have hpair : Pairwise (Function.onFun Disjoint F) := by
    intro A B hAB
    change Disjoint A.1.clusterCylinder B.1.clusterCylinder
    apply CubicBondAnimal.clusterCylinder_pairwiseDisjoint
    intro hval
    exact hAB (Subtype.ext hval)
  have hmeas : ∀ A, MeasurableSet (F A) := fun A ↦
    CubicBondAnimal.measurableSet_clusterCylinder A.1
  have hunion : (bernoulliBondMeasure d p).real (⋃ A : T, F A) =
      ∑ A : T, (bernoulliBondMeasure d p).real (F A) :=
    measureReal_iUnion_fintype hpair hmeas
  have hle : (bernoulliBondMeasure d p).real (⋃ A : T, F A) ≤ 1 := by
    calc
      (bernoulliBondMeasure d p).real (⋃ A : T, F A) ≤
          (bernoulliBondMeasure d p).real Set.univ :=
        measureReal_mono (Set.subset_univ _)
      _ = 1 := probReal_univ
  rw [hunion] at hle
  have hsum : (∑ A : T, (bernoulliBondMeasure d p).real (F A)) =
      (cubicAnimalCount d n m b : ℝ) * ((p : ℝ) ^ m * (1 - (p : ℝ)) ^ b) := by
    calc
      (∑ A : T, (bernoulliBondMeasure d p).real (F A)) =
          ∑ _A : T, (p : ℝ) ^ m * (1 - (p : ℝ)) ^ b := by
        apply Finset.sum_congr rfl
        intro A _hA
        rw [show F A = A.1.clusterCylinder by rfl,
          CubicBondAnimal.bernoulliBondMeasure_real_clusterCylinder,
          A.2.1, A.2.2]
      _ = (Fintype.card T : ℝ) * ((p : ℝ) ^ m * (1 - (p : ℝ)) ^ b) := by simp
      _ = (cubicAnimalCount d n m b : ℝ) *
          ((p : ℝ) ^ m * (1 - (p : ℝ)) ^ b) := by
        simp [cubicAnimalCount, T]
  rw [hsum] at hle
  simpa [mul_assoc] using hle

theorem cubicAnimalCount_eq_zero_of_m_lt {d n m b : ℕ} (hm : m < n - 1) :
    cubicAnimalCount d n m b = 0 := by
  rw [cubicAnimalCount, Fintype.card_eq_zero_iff]
  refine ⟨fun A ↦ (not_lt_of_ge A.1.edges_card_lower) ?_⟩
  simpa [A.2.1] using hm

theorem cubicAnimalCount_eq_zero_of_dn_lt_m {d n m b : ℕ} (hm : d * n < m) :
    cubicAnimalCount d n m b = 0 := by
  rw [cubicAnimalCount, Fintype.card_eq_zero_iff]
  refine ⟨fun A ↦ (not_lt_of_ge A.1.edges_card_upper) ?_⟩
  simpa [A.2.1] using hm

theorem cubicAnimalCount_eq_zero_of_b_eq_zero {d n m : ℕ} (hd : 0 < d) :
    cubicAnimalCount d n m 0 = 0 := by
  rw [cubicAnimalCount, Fintype.card_eq_zero_iff]
  exact ⟨fun A ↦ (A.1.boundary_card_pos hd).ne' A.2.2⟩

theorem cubicAnimalCount_eq_zero_of_two_dn_lt_b {d n m b : ℕ} (hb : 2 * d * n < b) :
    cubicAnimalCount d n m b = 0 := by
  rw [cubicAnimalCount, Fintype.card_eq_zero_iff]
  refine ⟨fun A ↦ (not_lt_of_ge A.1.boundary_card_le) ?_⟩
  simpa [A.2.2] using hb

/-- Equation (4.25) for the actual cubic-animal coefficient table, at its maximizing
Bernoulli parameter. -/
theorem cubicAnimalCount_mul_maximizingWeight_le_one {d n m b : ℕ}
    (hm : 0 < m) (hb : 0 < b) :
    (cubicAnimalCount d n m b : ℝ) * animalOpenFraction m b ^ m *
        (1 - animalOpenFraction m b) ^ b ≤ 1 := by
  have hsum : (0 : ℝ) < (m + b : ℕ) := by positivity
  have hr0 : 0 < animalOpenFraction m b := by
    exact div_pos (by exact_mod_cast hm) hsum
  have hr1 : animalOpenFraction m b < 1 := by
    rw [animalOpenFraction, div_lt_one hsum]
    exact_mod_cast (show m < m + b by omega)
  let r : I := ⟨animalOpenFraction m b, hr0.le, hr1.le⟩
  simpa [r] using cubicAnimalCount_mul_weight_le_one d n m b r

/-- Assumption-free concrete specialization of the current coefficient-table large-deviation
bound. -/
theorem cubicAnimal_largeDeviation {d n : ℕ} {p x : ℝ}
    (hd : 0 < d) (hn : 2 ≤ n) (hp0 : 0 < p) (hp1 : p < 1) (hx : 0 < x) :
    ∑ z ∈ exceptionalAnimalPairs d n p x,
        (cubicAnimalCount d n z.1 z.2 : ℝ) * p ^ z.1 * (1 - p) ^ z.2 ≤
      (3 * d ^ 2 * n ^ 2 : ℕ) *
        Real.exp (-((n : ℝ) * x ^ 2 * p ^ 2 * (1 - p) ^ 2 / 18)) := by
  apply latticeAnimal_largeDeviation (fun m b ↦ cubicAnimalCount d n m b)
    hd hn hp0 hp1 hx
  intro m b hmb
  have hm : 0 < m := by
    have hmlo := (Finset.mem_Icc.mp (Finset.mem_product.mp hmb).1).1
    omega
  have hb : 0 < b := by
    have hblo := (Finset.mem_Icc.mp (Finset.mem_product.mp hmb).2).1
    omega
  exact cubicAnimalCount_mul_maximizingWeight_le_one hm hb

/-- **Grimmett, Theorem 4.20 (assumption-free concrete cubic-animal form).**

For `n ≥ 2` and the explicit source-faithful range `0 < x ≤ 1/100`, this has exactly the book's
prefactor and exponent.  Equation (4.25) is discharged by the concrete disjoint cluster-cylinder
enumeration rather than retained as a parameter. -/
theorem cubicAnimal_largeDeviation_sharp {d n : ℕ} {p x : ℝ}
    (hd : 0 < d) (hn : 2 ≤ n) (hp0 : 0 < p) (hp1 : p < 1)
    (hx0 : 0 < x) (hx : x ≤ 1 / 100) :
    ∑ z ∈ exceptionalAnimalPairs d n p x,
        (cubicAnimalCount d n z.1 z.2 : ℝ) * p ^ z.1 * (1 - p) ^ z.2 ≤
      (3 * d ^ 2 * n ^ 2 : ℕ) *
        Real.exp (-((n : ℝ) * x ^ 2 * p ^ 2 * (1 - p) / 3)) := by
  apply latticeAnimal_largeDeviation_sharp (fun m b ↦ cubicAnimalCount d n m b)
    hd hn hp0 hp1 hx0 hx
  intro m b hmb
  have hm : 0 < m := by
    have hmlo := (Finset.mem_Icc.mp (Finset.mem_product.mp hmb).1).1
    omega
  have hb : 0 < b := by
    have hblo := (Finset.mem_Icc.mp (Finset.mem_product.mp hmb).2).1
    omega
  exact cubicAnimalCount_mul_maximizingWeight_le_one hm hb

end Percolation
