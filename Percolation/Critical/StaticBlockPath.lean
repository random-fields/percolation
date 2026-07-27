import Percolation.Critical.StaticBlockAdjacency

/-!
# Lifting good-block walks to open bond connectivity

Neighboring good blocks have intersecting selected clusters.  Iterating that deterministic
fact along a coarse-lattice walk shows that its endpoint clusters lie in one open bond
component.  This is the path-level form of equation (7.59) used by static renormalization.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval

/-- Ambient vertices of the canonical cluster selected by the good-block construction at a
coarse vertex `x`. -/
noncomputable def epsilonGoodBlockClusterVertices
    (d : ℕ) (ω : EdgeConfiguration d) (n : ℕ) (x : Cubic d) : Finset (Cubic d) :=
  finiteBoxGraphComponentVertices
    (finiteBoxGraphLargestComponent (epsilonGoodBlockCenter n x) n
      (finiteBoxOpenGraph d ω (epsilonGoodBlockCenter n x) n))

theorem finiteBoxGraphComponentVertices_reachable_cubicOpenGraph
    {d n : ℕ} {ω : EdgeConfiguration d} {x : Cubic d}
    {C : (finiteBoxOpenGraph d ω x n).ConnectedComponent}
    {u v : Cubic d}
    (hu : u ∈ finiteBoxGraphComponentVertices C)
    (hv : v ∈ finiteBoxGraphComponentVertices C) :
    (cubicOpenGraph d ω).Reachable u v := by
  simp only [finiteBoxGraphComponentVertices, Finset.mem_filter] at hu hv
  obtain ⟨huBox, _huBox', huSupp⟩ := hu
  obtain ⟨hvBox, _hvBox', hvSupp⟩ := hv
  let uBox : {z : Cubic d // z ∈ cubicMetricBox d x n} := ⟨u, huBox⟩
  let vBox : {z : Cubic d // z ∈ cubicMetricBox d x n} := ⟨v, hvBox⟩
  have huSupp' : uBox ∈ C.supp := by simpa [uBox] using huSupp
  have hvSupp' : vBox ∈ C.supp := by simpa [vBox] using hvSupp
  let emb := SimpleGraph.Embedding.induce
    (G := cubicOpenGraph d ω) (cubicMetricBox d x n : Set (Cubic d))
  have hmap := (C.reachable_of_mem_supp huSupp' hvSupp').map emb.toHom
  simpa [uBox, vBox, emb] using hmap

/-- Two vertices of one finite-box component are joined by an open walk using only the internal
edges of that box.  This support-preserving version is needed to keep crossings from distinct
renormalized slices edge-disjoint. -/
theorem finiteBoxGraphComponentVertices_mem_connectionEventIn
    {d n : ℕ} {ω : EdgeConfiguration d} {x : Cubic d}
    {C : (finiteBoxOpenGraph d ω x n).ConnectedComponent}
    {u v : Cubic d}
    (hu : u ∈ finiteBoxGraphComponentVertices C)
    (hv : v ∈ finiteBoxGraphComponentVertices C) :
    ω ∈ connectionEventIn d (cubicBoxEdges d x n) u v := by
  classical
  simp only [finiteBoxGraphComponentVertices, Finset.mem_filter] at hu hv
  obtain ⟨huBox, _huBox', huSupp⟩ := hu
  obtain ⟨hvBox, _hvBox', hvSupp⟩ := hv
  let uBox : {z : Cubic d // z ∈ cubicMetricBox d x n} := ⟨u, huBox⟩
  let vBox : {z : Cubic d // z ∈ cubicMetricBox d x n} := ⟨v, hvBox⟩
  have huSupp' : uBox ∈ C.supp := by simpa [uBox] using huSupp
  have hvSupp' : vBox ∈ C.supp := by simpa [vBox] using hvSupp
  obtain ⟨q⟩ := C.reachable_of_mem_supp huSupp' hvSupp'
  let emb := SimpleGraph.Embedding.induce
    (G := cubicOpenGraph d ω) (cubicMetricBox d x n : Set (Cubic d))
  let qOpen := q.map emb.toHom
  let w := qOpen.map (cubicOpenGraphHom d ω)
  have hwOpen : walkIsOpen ω w := walkIsOpen_map_cubicOpenGraphHom qOpen
  have hwBox : ∀ z ∈ w.support, z ∈ cubicMetricBox d x n := by
    intro z hz
    simp only [w, SimpleGraph.Walk.support_map, List.mem_map] at hz
    obtain ⟨zOpen, hzOpen, hzEq⟩ := hz
    have hzEq' : zOpen = z := by simpa [cubicOpenGraphHom] using hzEq
    subst z
    simp only [qOpen, SimpleGraph.Walk.support_map, List.mem_map] at hzOpen
    obtain ⟨zBox, _hz, rfl⟩ := hzOpen
    exact zBox.2
  refine ⟨w.copy (by rfl) (by rfl), ?_, ?_⟩
  · simpa using hwOpen
  · simpa using walkEdgeFinset_subset_cubicBoxEdges_of_support w hwBox

/-- Underlying bond coordinates used by the boxes visited by a coarse walk. -/
noncomputable def epsilonGoodWalkEdgeSupport
    {d n : ℕ} {x y : Cubic d} (w : (cubicGraph d).Walk x y) :
    Finset (CubicEdge d) :=
  w.support.toFinset.biUnion fun z ↦
    cubicBoxEdges d (epsilonGoodBlockCenter n z) n

@[simp] theorem epsilonGoodWalkEdgeSupport_nil
    {d n : ℕ} (x : Cubic d) :
    epsilonGoodWalkEdgeSupport (n := n)
        (SimpleGraph.Walk.nil : (cubicGraph d).Walk x x) =
      cubicBoxEdges d (epsilonGoodBlockCenter n x) n := by
  simp [epsilonGoodWalkEdgeSupport]

@[simp] theorem epsilonGoodWalkEdgeSupport_cons
    {d n : ℕ} {x y z : Cubic d} (hxy : (cubicGraph d).Adj x y)
    (q : (cubicGraph d).Walk y z) :
    epsilonGoodWalkEdgeSupport (n := n) (SimpleGraph.Walk.cons hxy q) =
      cubicBoxEdges d (epsilonGoodBlockCenter n x) n ∪
        epsilonGoodWalkEdgeSupport (n := n) q := by
  simp [epsilonGoodWalkEdgeSupport, SimpleGraph.Walk.support_cons]

theorem cubicBoxEdges_subset_epsilonGoodWalkEdgeSupport_of_mem_support
    {d n : ℕ} {x y z : Cubic d} (w : (cubicGraph d).Walk x y)
    (hz : z ∈ w.support) :
    cubicBoxEdges d (epsilonGoodBlockCenter n z) n ⊆
      epsilonGoodWalkEdgeSupport (n := n) w := by
  intro e he
  rw [epsilonGoodWalkEdgeSupport, Finset.mem_biUnion]
  exact ⟨z, by simpa using hz, he⟩

theorem epsilonGoodWalkEdgeSupport_mono_of_support_subset
    {d n : ℕ} {x y x' y' : Cubic d}
    {q : (cubicGraph d).Walk x y} {w : (cubicGraph d).Walk x' y'}
    (hqw : ∀ z ∈ q.support, z ∈ w.support) :
    epsilonGoodWalkEdgeSupport (n := n) q ⊆
      epsilonGoodWalkEdgeSupport (n := n) w := by
  intro e he
  rw [epsilonGoodWalkEdgeSupport, Finset.mem_biUnion] at he ⊢
  obtain ⟨z, hz, hez⟩ := he
  exact ⟨z, by simpa using hqw z (by simpa using hz), hez⟩

private theorem connectionEventIn_trans_mem_static
    {d : ℕ} {E : Finset (CubicEdge d)} {x y z : Cubic d}
    {ω : EdgeConfiguration d}
    (hxy : ω ∈ connectionEventIn d E x y)
    (hyz : ω ∈ connectionEventIn d E y z) :
    ω ∈ connectionEventIn d E x z := by
  obtain ⟨p, hpopen, hpedges⟩ := hxy
  obtain ⟨q, hqopen, hqedges⟩ := hyz
  refine ⟨p.append q, walkIsOpen_append hpopen hqopen, ?_⟩
  intro e he
  rw [mem_walkEdgeFinset_iff, SimpleGraph.Walk.edges_append,
    List.mem_append] at he
  exact he.elim
    (fun hep ↦ hpedges ((mem_walkEdgeFinset_iff p e).mpr hep))
    (fun heq ↦ hqedges ((mem_walkEdgeFinset_iff q e).mpr heq))

/-- A good coarse walk lifts to an open bond connection whose edges remain in the union of the
finite box supports visited by that walk. -/
theorem epsilonGoodBlockClusterVertices_mem_connectionEventIn_of_good_walk
    {d n : ℕ} (p : I) (ε : ℝ) (ω : EdgeConfiguration d)
    {x y : Cubic d} (w : (cubicGraph d).Walk x y)
    (hgood : ∀ z ∈ w.support,
      ω ∈ epsilonGoodBoxEvent d p ε (epsilonGoodBlockCenter n z) n)
    {u v : Cubic d}
    (hu : u ∈ epsilonGoodBlockClusterVertices d ω n x)
    (hv : v ∈ epsilonGoodBlockClusterVertices d ω n y) :
    ω ∈ connectionEventIn d (epsilonGoodWalkEdgeSupport (n := n) w) u v := by
  classical
  induction w generalizing u with
  | nil =>
      simpa using finiteBoxGraphComponentVertices_mem_connectionEventIn hu hv
  | @cons x₀ x₁ y₀ hx₀x₁ q ih =>
      obtain ⟨a, rfl⟩ := (cubicGraph_adj_iff_exists_stepFrom x₀ x₁).mp hx₀x₁
      have hxGood : ω ∈ epsilonGoodBoxEvent d p ε
          (epsilonGoodBlockCenter n x₀) n :=
        hgood x₀ (by simp)
      have hx₁Good : ω ∈ epsilonGoodBoxEvent d p ε
          (epsilonGoodBlockCenter n (cubicStepFrom x₀ a)) n :=
        hgood (cubicStepFrom x₀ a) (by simp)
      obtain ⟨s, hs₀, hs₁⟩ :
          ∃ s : Cubic d,
            s ∈ epsilonGoodBlockClusterVertices d ω n x₀ ∧
            s ∈ epsilonGoodBlockClusterVertices d ω n (cubicStepFrom x₀ a) := by
        simpa [epsilonGoodBlockClusterVertices] using
          finiteBoxGraphLargestComponents_inter_of_mem_goodBoxEvents
            p ε ω x₀ a hxGood hx₁Good
      have hgoodTail : ∀ z ∈ q.support,
          ω ∈ epsilonGoodBoxEvent d p ε (epsilonGoodBlockCenter n z) n := by
        intro z hz
        exact hgood z (by simp [hz])
      have husBox : ω ∈ connectionEventIn d
          (cubicBoxEdges d (epsilonGoodBlockCenter n x₀) n) u s :=
        finiteBoxGraphComponentVertices_mem_connectionEventIn hu hs₀
      have hsvTail : ω ∈ connectionEventIn d
          (epsilonGoodWalkEdgeSupport (n := n) q) s v :=
        ih hgoodTail hs₁ hv
      rw [epsilonGoodWalkEdgeSupport_cons]
      exact connectionEventIn_trans_mem_static
        (connectionEventIn_mono Finset.subset_union_left u s husBox)
        (connectionEventIn_mono Finset.subset_union_right s v hsvTail)

theorem epsilonGoodBlockClusterVertices_inter_of_step
    {d n : ℕ} (p : I) (ε : ℝ) (ω : EdgeConfiguration d)
    (x : Cubic d) (a : CubicDirection d)
    (hx : ω ∈ epsilonGoodBoxEvent d p ε (epsilonGoodBlockCenter n x) n)
    (hy : ω ∈ epsilonGoodBoxEvent d p ε
      (epsilonGoodBlockCenter n (cubicStepFrom x a)) n) :
    ∃ u : Cubic d,
      u ∈ epsilonGoodBlockClusterVertices d ω n x ∧
      u ∈ epsilonGoodBlockClusterVertices d ω n (cubicStepFrom x a) := by
  simpa [epsilonGoodBlockClusterVertices] using
    finiteBoxGraphLargestComponents_inter_of_mem_goodBoxEvents p ε ω x a hx hy

theorem epsilonGoodBlockCluster_isCrossing_of_mem_goodBoxEvent
    {d n : ℕ} (p : I) (ε : ℝ) (ω : EdgeConfiguration d) (x : Cubic d)
    (hx : ω ∈ epsilonGoodBoxEvent d p ε (epsilonGoodBlockCenter n x) n) :
    finiteBoxGraphComponentIsCrossing
      (finiteBoxGraphLargestComponent (epsilonGoodBlockCenter n x) n
        (finiteBoxOpenGraph d ω (epsilonGoodBlockCenter n x) n)) := by
  exact hx.1

/-- A coarse cubic walk consisting entirely of good blocks lifts to open-bond reachability
between arbitrary vertices of its selected endpoint clusters. -/
theorem epsilonGoodBlockClusterVertices_reachable_of_good_walk
    {d n : ℕ} (p : I) (ε : ℝ) (ω : EdgeConfiguration d)
    {x y : Cubic d} (w : (cubicGraph d).Walk x y)
    (hgood : ∀ z ∈ w.support,
      ω ∈ epsilonGoodBoxEvent d p ε (epsilonGoodBlockCenter n z) n)
    {u v : Cubic d}
    (hu : u ∈ epsilonGoodBlockClusterVertices d ω n x)
    (hv : v ∈ epsilonGoodBlockClusterVertices d ω n y) :
    (cubicOpenGraph d ω).Reachable u v := by
  induction w generalizing u with
  | nil =>
      exact finiteBoxGraphComponentVertices_reachable_cubicOpenGraph hu hv
  | @cons x₀ x₁ y₀ hx₀x₁ q ih =>
      obtain ⟨a, rfl⟩ := (cubicGraph_adj_iff_exists_stepFrom x₀ x₁).mp hx₀x₁
      have hxGood : ω ∈ epsilonGoodBoxEvent d p ε
          (epsilonGoodBlockCenter n x₀) n :=
        hgood x₀ (by simp)
      have hx₁Good : ω ∈ epsilonGoodBoxEvent d p ε
          (epsilonGoodBlockCenter n (cubicStepFrom x₀ a)) n :=
        hgood (cubicStepFrom x₀ a) (by simp)
      obtain ⟨s, hs₀, hs₁⟩ :=
        epsilonGoodBlockClusterVertices_inter_of_step p ε ω x₀ a hxGood hx₁Good
      have hus : (cubicOpenGraph d ω).Reachable u s :=
        finiteBoxGraphComponentVertices_reachable_cubicOpenGraph hu hs₀
      have hgoodTail : ∀ z ∈ q.support,
          ω ∈ epsilonGoodBoxEvent d p ε (epsilonGoodBlockCenter n z) n := by
        intro z hz
        exact hgood z (by simp [hz])
      exact hus.trans (ih hgoodTail hs₁ hv)

/-- A good coarse walk yields an open-graph connection from the negative face of its first
block to the positive face of its last block, in any chosen coordinate direction. -/
theorem exists_cubicOpenGraph_reachable_between_faces_of_good_walk
    {d n : ℕ} (p : I) (ε : ℝ) (ω : EdgeConfiguration d)
    {x y : Cubic d} (w : (cubicGraph d).Walk x y)
    (hgood : ∀ z ∈ w.support,
      ω ∈ epsilonGoodBoxEvent d p ε (epsilonGoodBlockCenter n z) n)
    (i : Fin d) :
    ∃ u ∈ cubicBoxFace d (epsilonGoodBlockCenter n x) n i false,
      ∃ v ∈ cubicBoxFace d (epsilonGoodBlockCenter n y) n i true,
        (cubicOpenGraph d ω).Reachable u v := by
  have hxGood : ω ∈ epsilonGoodBoxEvent d p ε
      (epsilonGoodBlockCenter n x) n := hgood x w.start_mem_support
  have hyGood : ω ∈ epsilonGoodBoxEvent d p ε
      (epsilonGoodBlockCenter n y) n := hgood y w.end_mem_support
  have hxCross := epsilonGoodBlockCluster_isCrossing_of_mem_goodBoxEvent p ε ω x hxGood
  have hyCross := epsilonGoodBlockCluster_isCrossing_of_mem_goodBoxEvent p ε ω y hyGood
  obtain ⟨u, huM, huFace⟩ := (hxCross i).1
  obtain ⟨v, hvM, hvFace⟩ := (hyCross i).2
  refine ⟨u, huFace, v, hvFace, ?_⟩
  exact epsilonGoodBlockClusterVertices_reachable_of_good_walk p ε ω w hgood huM hvM

/-- Support-preserving bond-event form of the good-walk face connection. -/
theorem exists_connectionEventIn_between_faces_of_good_walk
    {d n : ℕ} (p : I) (ε : ℝ) (ω : EdgeConfiguration d)
    {x y : Cubic d} (w : (cubicGraph d).Walk x y)
    (hgood : ∀ z ∈ w.support,
      ω ∈ epsilonGoodBoxEvent d p ε (epsilonGoodBlockCenter n z) n)
    (i : Fin d) :
    ∃ u ∈ cubicBoxFace d (epsilonGoodBlockCenter n x) n i false,
      ∃ v ∈ cubicBoxFace d (epsilonGoodBlockCenter n y) n i true,
        ω ∈ connectionEventIn d (epsilonGoodWalkEdgeSupport (n := n) w) u v := by
  have hxGood : ω ∈ epsilonGoodBoxEvent d p ε
      (epsilonGoodBlockCenter n x) n := hgood x w.start_mem_support
  have hyGood : ω ∈ epsilonGoodBoxEvent d p ε
      (epsilonGoodBlockCenter n y) n := hgood y w.end_mem_support
  have hxCross := epsilonGoodBlockCluster_isCrossing_of_mem_goodBoxEvent p ε ω x hxGood
  have hyCross := epsilonGoodBlockCluster_isCrossing_of_mem_goodBoxEvent p ε ω y hyGood
  obtain ⟨u, huM, huFace⟩ := (hxCross i).1
  obtain ⟨v, hvM, hvFace⟩ := (hyCross i).2
  exact ⟨u, huFace, v, hvFace,
    epsilonGoodBlockClusterVertices_mem_connectionEventIn_of_good_walk
      p ε ω w hgood huM hvM⟩

/-- Source-facing bond-event form of the good-walk face connection. -/
theorem exists_connectionEvent_between_faces_of_good_walk
    {d n : ℕ} (p : I) (ε : ℝ) (ω : EdgeConfiguration d)
    {x y : Cubic d} (w : (cubicGraph d).Walk x y)
    (hgood : ∀ z ∈ w.support,
      ω ∈ epsilonGoodBoxEvent d p ε (epsilonGoodBlockCenter n z) n)
    (i : Fin d) :
    ∃ u ∈ cubicBoxFace d (epsilonGoodBlockCenter n x) n i false,
      ∃ v ∈ cubicBoxFace d (epsilonGoodBlockCenter n y) n i true,
        ω ∈ connectionEvent d u v := by
  obtain ⟨u, huFace, v, hvFace, huv⟩ :=
    exists_cubicOpenGraph_reachable_between_faces_of_good_walk p ε ω w hgood i
  obtain ⟨q⟩ := huv
  refine ⟨u, huFace, v, hvFace, q.map (cubicOpenGraphHom d ω), ?_⟩
  exact walkIsOpen_map_cubicOpenGraphHom q

end Percolation
