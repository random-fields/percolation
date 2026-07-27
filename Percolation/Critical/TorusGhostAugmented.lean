import Percolation.Critical.TorusGhostConditioning
import Percolation.Core.TwoEdgeMenger

/-!
# The augmented open graph for the torus ghost field

Green coordinates are represented as edges from their lattice vertex to one added ghost
vertex.  Thus joint edge/green disjoint occurrence becomes ordinary edge-disjoint
connectivity in a finite simple graph.
-/

namespace Percolation

open Set
open scoped Classical unitInterval

noncomputable section

abbrev TorusGhostAugmentedVertex (d N : ℕ) := Option (CubicTorus d N)

def torusGhostAugmentedEdge :
    TorusGhostCoordinate d N → Sym2 (TorusGhostAugmentedVertex d N)
  | Sum.inl e => Sym2.map some e.1
  | Sum.inr x => s(some x, none)

theorem torusGhostAugmentedEdge_injective :
    Function.Injective (torusGhostAugmentedEdge (d := d) (N := N)) := by
  intro a b hab
  rcases a with e | x <;> rcases b with f | y
  · apply congrArg Sum.inl
    apply Subtype.ext
    exact Sym2.map.injective (Option.some_injective _) hab
  · exfalso
    have hnone := congrArg (fun z : Sym2 (Option (CubicTorus d N)) ↦ none ∈ z) hab
    simp [torusGhostAugmentedEdge] at hnone
  · exfalso
    have hnone := congrArg (fun z : Sym2 (Option (CubicTorus d N)) ↦ none ∈ z) hab
    simp [torusGhostAugmentedEdge] at hnone
  · apply congrArg Sum.inr
    rw [torusGhostAugmentedEdge, torusGhostAugmentedEdge, Sym2.eq_iff] at hab
    simpa using hab

noncomputable def torusGhostAugmentedEdgeEmbedding :
    TorusGhostCoordinate d N ↪ Sym2 (TorusGhostAugmentedVertex d N) :=
  ⟨torusGhostAugmentedEdge, torusGhostAugmentedEdge_injective⟩

theorem torusGhostAugmentedEdge_not_isDiag
    (c : TorusGhostCoordinate d N) :
    ¬ (torusGhostAugmentedEdge c).IsDiag := by
  rcases c with e | x
  · rw [torusGhostAugmentedEdge, Sym2.isDiag_map (Option.some_injective _)]
    exact (cubicTorusGraph d N).not_isDiag_of_mem_edgeSet e.2
  · simp [torusGhostAugmentedEdge]

def torusGhostOpenAugmentedGraph
    (s : Finset (TorusGhostCoordinate d N)) :
    SimpleGraph (TorusGhostAugmentedVertex d N) :=
  SimpleGraph.fromEdgeSet (torusGhostAugmentedEdge '' (s : Set _))

theorem edgeSet_torusGhostOpenAugmentedGraph
    (s : Finset (TorusGhostCoordinate d N)) :
    (torusGhostOpenAugmentedGraph s).edgeSet =
      torusGhostAugmentedEdge '' (s : Set (TorusGhostCoordinate d N)) := by
  rw [torusGhostOpenAugmentedGraph, SimpleGraph.edgeSet_fromEdgeSet]
  ext e
  constructor
  · exact fun he ↦ he.1
  · intro he
    refine ⟨he, ?_⟩
    obtain ⟨c, hc, rfl⟩ := he
    exact torusGhostAugmentedEdge_not_isDiag c

/-- Erasing a joint edge/green coordinate is exactly deletion of its augmented edge. -/
theorem torusGhostOpenAugmentedGraph_erase
    (s : Finset (TorusGhostCoordinate d N))
    (c : TorusGhostCoordinate d N) :
    torusGhostOpenAugmentedGraph (s.erase c) =
      (torusGhostOpenAugmentedGraph s).deleteEdges
        {torusGhostAugmentedEdge c} := by
  apply SimpleGraph.ext
  funext u v
  simp only [← SimpleGraph.mem_edgeSet,
    edgeSet_torusGhostOpenAugmentedGraph, SimpleGraph.edgeSet_deleteEdges,
    Set.mem_diff, Set.mem_image, Set.mem_singleton_iff,
    Finset.mem_coe, Finset.mem_erase]
  apply propext
  constructor
  · rintro ⟨a, ⟨hac, has⟩, ha⟩
    refine ⟨⟨a, has, ha⟩, ?_⟩
    intro huv
    exact hac (torusGhostAugmentedEdge_injective (ha.trans huv))
  · rintro ⟨⟨a, has, ha⟩, huv⟩
    refine ⟨a, ⟨?_, has⟩, ha⟩
    intro hac
    subst a
    exact huv ha.symm

@[simp]
theorem mem_edgeSet_torusGhostOpenAugmentedGraph_iff
  (s : Finset (TorusGhostCoordinate d N))
    (e : Sym2 (TorusGhostAugmentedVertex d N)) :
    e ∈ (torusGhostOpenAugmentedGraph s).edgeSet ↔
      ∃ c ∈ s, torusGhostAugmentedEdge c = e := by
  rw [edgeSet_torusGhostOpenAugmentedGraph]
  rfl

noncomputable def torusGhostAugmentedEdgeCoordinate
    (s : Finset (TorusGhostCoordinate d N))
    (e : (torusGhostOpenAugmentedGraph s).edgeSet) :
    TorusGhostCoordinate d N := by
  have he : ∃ c ∈ s, torusGhostAugmentedEdge c = e.1 :=
    (mem_edgeSet_torusGhostOpenAugmentedGraph_iff s e.1).mp e.2
  exact Classical.choose he

theorem torusGhostAugmentedEdgeCoordinate_mem
    (s : Finset (TorusGhostCoordinate d N))
    (e : (torusGhostOpenAugmentedGraph s).edgeSet) :
    torusGhostAugmentedEdgeCoordinate s e ∈ s := by
  unfold torusGhostAugmentedEdgeCoordinate
  exact (Classical.choose_spec
    ((mem_edgeSet_torusGhostOpenAugmentedGraph_iff s e.1).mp e.2)).1

theorem torusGhostAugmentedEdge_coordinate
    (s : Finset (TorusGhostCoordinate d N))
    (e : (torusGhostOpenAugmentedGraph s).edgeSet) :
    torusGhostAugmentedEdge (torusGhostAugmentedEdgeCoordinate s e) = e.1 := by
  unfold torusGhostAugmentedEdgeCoordinate
  exact (Classical.choose_spec
    ((mem_edgeSet_torusGhostOpenAugmentedGraph_iff s e.1).mp e.2)).2

theorem torusGhostAugmentedEdgeCoordinate_injective
    (s : Finset (TorusGhostCoordinate d N)) :
    Function.Injective (torusGhostAugmentedEdgeCoordinate s) := by
  intro e f hef
  apply Subtype.ext
  rw [← torusGhostAugmentedEdge_coordinate s e,
    ← torusGhostAugmentedEdge_coordinate s f, hef]

noncomputable def torusGhostAugmentedWalkTrace
    (hN : 2 ≤ N)
    (s : Finset (TorusGhostCoordinate d N))
    {u v : TorusGhostAugmentedVertex d N}
    (p : (torusGhostOpenAugmentedGraph s).Walk u v) :
    Finset (TorusGhostCoordinate d N) :=
  (torusGhostCoordinateFinset d N hN).filter fun c ↦
    torusGhostAugmentedEdge c ∈ p.edges

theorem mem_torusGhostAugmentedWalkTrace_iff
    (hN : 2 ≤ N)
    (s : Finset (TorusGhostCoordinate d N))
    {u v : TorusGhostAugmentedVertex d N}
    (p : (torusGhostOpenAugmentedGraph s).Walk u v)
    (c : TorusGhostCoordinate d N) :
    c ∈ torusGhostAugmentedWalkTrace hN s p ↔
      torusGhostAugmentedEdge c ∈ p.edges := by
  rw [torusGhostAugmentedWalkTrace, Finset.mem_filter]
  constructor
  · exact fun h ↦ h.2
  · intro h
    refine ⟨?_, h⟩
    rcases c with e | x
    · exact Finset.inl_mem_disjSum.mpr (mem_cubicTorusEdgeFinset hN e)
    · exact Finset.inr_mem_disjSum.mpr (mem_cubicTorusVertexFinset hN x)

theorem torusGhostAugmentedWalkTrace_subset
    (hN : 2 ≤ N)
    (s : Finset (TorusGhostCoordinate d N))
    {u v : TorusGhostAugmentedVertex d N}
    (p : (torusGhostOpenAugmentedGraph s).Walk u v) :
    torusGhostAugmentedWalkTrace hN s p ⊆ s := by
  intro c hc
  rw [mem_torusGhostAugmentedWalkTrace_iff hN] at hc
  let e : (torusGhostOpenAugmentedGraph s).edgeSet :=
    ⟨torusGhostAugmentedEdge c, p.edges_subset_edgeSet hc⟩
  have hcoord := torusGhostAugmentedEdge_coordinate s e
  have hcEq : torusGhostAugmentedEdgeCoordinate s e = c :=
    torusGhostAugmentedEdge_injective hcoord
  rw [← hcEq]
  exact torusGhostAugmentedEdgeCoordinate_mem s e

theorem disjoint_torusGhostAugmentedWalkTrace
    (hN : 2 ≤ N)
    (s : Finset (TorusGhostCoordinate d N))
    {u v : TorusGhostAugmentedVertex d N}
    {p q : (torusGhostOpenAugmentedGraph s).Walk u v}
    (hpq : p.edges.Disjoint q.edges) :
    Disjoint (torusGhostAugmentedWalkTrace hN s p)
      (torusGhostAugmentedWalkTrace hN s q) := by
  rw [Finset.disjoint_left]
  intro c hcp hcq
  rw [mem_torusGhostAugmentedWalkTrace_iff hN] at hcp hcq
  exact List.disjoint_left.mp hpq hcp hcq

theorem torusGhostOpenAugmentedGraph_adj_none_iff
    (s : Finset (TorusGhostCoordinate d N))
    (v : TorusGhostAugmentedVertex d N) :
    (torusGhostOpenAugmentedGraph s).Adj v none ↔
      ∃ z : CubicTorus d N, v = some z ∧ Sum.inr z ∈ s := by
  rw [← SimpleGraph.mem_edgeSet,
    mem_edgeSet_torusGhostOpenAugmentedGraph_iff]
  constructor
  · rintro ⟨c, hc, heq⟩
    rcases c with e | z
    · exfalso
      have hnone := congrArg
        (fun q : Sym2 (Option (CubicTorus d N)) ↦ none ∈ q) heq
      simp [torusGhostAugmentedEdge] at hnone
    · refine ⟨z, ?_, hc⟩
      rw [torusGhostAugmentedEdge, Sym2.eq_iff] at heq
      rcases heq with h | h
      · exact h.1.symm
      · simp at h
  · rintro ⟨z, rfl, hz⟩
    exact ⟨Sum.inr z, hz, rfl⟩

theorem torusGhostOpenAugmentedGraph_adj_some_iff
    (s : Finset (TorusGhostCoordinate d N)) (x y : CubicTorus d N) :
    (torusGhostOpenAugmentedGraph s).Adj (some x) (some y) ↔
      ∃ e : CubicTorusEdge d N,
        Sum.inl e ∈ s ∧ e.1 = s(x, y) := by
  rw [← SimpleGraph.mem_edgeSet,
    mem_edgeSet_torusGhostOpenAugmentedGraph_iff]
  constructor
  · rintro ⟨c, hc, heq⟩
    rcases c with e | z
    · refine ⟨e, hc, ?_⟩
      apply Sym2.map.injective (Option.some_injective _)
      simpa [torusGhostAugmentedEdge] using heq
    · exfalso
      have hnone := congrArg
        (fun q : Sym2 (Option (CubicTorus d N)) ↦ none ∈ q) heq
      simp [torusGhostAugmentedEdge] at hnone
  · rintro ⟨e, he, heq⟩
    refine ⟨Sum.inl e, he, ?_⟩
    simp [torusGhostAugmentedEdge, heq]

def torusGhostAugmentedOriginalSet (d N : ℕ) :
    Set (TorusGhostAugmentedVertex d N) := Set.range some

noncomputable def torusGhostAugmentedOriginalGet
    (a : torusGhostAugmentedOriginalSet d N) : CubicTorus d N :=
  Classical.choose a.2

theorem torusGhostAugmentedOriginalGet_spec
    (a : torusGhostAugmentedOriginalSet d N) :
    some (torusGhostAugmentedOriginalGet a) = a.1 :=
  Classical.choose_spec a.2

@[simp]
theorem torusGhostAugmentedOriginalGet_mk (x : CubicTorus d N) :
    torusGhostAugmentedOriginalGet
      (⟨some x, ⟨x, rfl⟩⟩ : torusGhostAugmentedOriginalSet d N) = x := by
  apply Option.some_injective
  exact torusGhostAugmentedOriginalGet_spec _

noncomputable def torusGhostAugmentedOriginalHom
    (s : Finset (TorusGhostCoordinate d N)) :
    (torusGhostOpenAugmentedGraph s).induce
        (torusGhostAugmentedOriginalSet d N) →g cubicTorusGraph d N where
  toFun := torusGhostAugmentedOriginalGet
  map_rel' := by
    intro a b hab
    have hab' : (torusGhostOpenAugmentedGraph s).Adj a.1 b.1 :=
      SimpleGraph.induce_adj.mp hab
    rw [← torusGhostAugmentedOriginalGet_spec a,
      ← torusGhostAugmentedOriginalGet_spec b] at hab'
    obtain ⟨e, he, heq⟩ :=
      (torusGhostOpenAugmentedGraph_adj_some_iff s _ _).mp hab'
    rw [← SimpleGraph.mem_edgeSet, ← heq]
    exact e.2

structure TorusGhostAugmentedPathProjection
    (s : Finset (TorusGhostCoordinate d N)) (y : CubicTorus d N)
    (p : (torusGhostOpenAugmentedGraph s).Walk (some y) none) where
  endpoint : CubicTorus d N
  green_mem : Sum.inr endpoint ∈ s
  walk : (cubicTorusGraph d N).Walk y endpoint
  edge_subset : ∀ e ∈ walk.edges,
    Sym2.map some e ∈ p.edges
  green_edge_mem : s(some endpoint, none) ∈ p.edges

noncomputable def torusGhostAugmentedPathProjectionOfPath
    (s : Finset (TorusGhostCoordinate d N)) (y : CubicTorus d N)
    (p : (torusGhostOpenAugmentedGraph s).Walk (some y) none)
    (hp : p.IsPath) : TorusGhostAugmentedPathProjection s y p := by
  have hnil : ¬ p.Nil := by
    intro h
    exact Option.some_ne_none y h.eq
  have hnoneDrop : none ∉ p.dropLast.support := by
    have hnodup : (p.dropLast.support ++ [none]).Nodup := by
      rw [p.support_dropLast_concat hnil]
      exact hp.support_nodup
    have h := (List.nodup_append.mp hnodup).2.2
    exact fun hmem ↦ h none hmem none (by simp) rfl
  have hadj := p.adj_penultimate hnil
  have hterminal :=
    (torusGhostOpenAugmentedGraph_adj_none_iff s p.penultimate).mp hadj
  let z := Classical.choose hterminal
  have hpen : p.penultimate = some z := (Classical.choose_spec hterminal).1
  have hzGreen : Sum.inr z ∈ s := (Classical.choose_spec hterminal).2
  let r : (torusGhostOpenAugmentedGraph s).Walk (some y) (some z) :=
    p.dropLast.copy rfl hpen
  have hnoneR : none ∉ r.support := by
    simpa [r] using hnoneDrop
  have hrOriginal : ∀ a ∈ r.support,
      a ∈ torusGhostAugmentedOriginalSet d N := by
    intro a ha
    rcases a with _ | x
    · exact (hnoneR ha).elim
    · exact ⟨x, rfl⟩
  let rind := r.induce (torusGhostAugmentedOriginalSet d N) hrOriginal
  let q₀ := rind.map (torusGhostAugmentedOriginalHom s)
  have hstart : torusGhostAugmentedOriginalGet
      (⟨some y, hrOriginal _ r.start_mem_support⟩ :
        torusGhostAugmentedOriginalSet d N) = y := by simp
  have hend : torusGhostAugmentedOriginalGet
      (⟨some z, hrOriginal _ r.end_mem_support⟩ :
        torusGhostAugmentedOriginalSet d N) = z := by simp
  let q : (cubicTorusGraph d N).Walk y z := q₀.copy hstart hend
  have hedgeEq : q.edges.map (Sym2.map some) = r.edges := by
    have hind := congrArg SimpleGraph.Walk.edges
      (SimpleGraph.Walk.map_induce r hrOriginal)
    calc
      q.edges.map (Sym2.map some) =
          (rind.map (torusGhostAugmentedOriginalHom s)).edges.map
            (Sym2.map some) := by simp [q, q₀]
      _ = rind.edges.map (Sym2.map fun a ↦
          some (torusGhostAugmentedOriginalGet a)) := by
        simp [SimpleGraph.Walk.edges_map, List.map_map, Sym2.map_map,
          torusGhostAugmentedOriginalHom, Function.comp_def]
      _ = rind.edges.map (Sym2.map fun a ↦ a.1) := by
        apply List.map_congr_left
        intro f hf
        apply Sym2.map_congr
        intro a ha
        exact torusGhostAugmentedOriginalGet_spec a
      _ = r.edges := by
        rw [SimpleGraph.Walk.edges_map] at hind
        exact hind
  refine ⟨z, hzGreen, q, ?_, ?_⟩
  · intro e he
    have heMap : Sym2.map some e ∈ r.edges := by
      rw [← hedgeEq]
      exact List.mem_map.mpr ⟨e, he, rfl⟩
    have heDrop : Sym2.map some e ∈ p.dropLast.edges := by
      simpa [r] using heMap
    exact (SimpleGraph.Walk.isSubwalk_take p (p.length - 1)).edges_subset heDrop
  · have hlast : s(p.penultimate, none) ∈ p.edges := by
      have hlastDrop : s(p.penultimate, none) ∈
          (p.dropLast.concat hadj).edges := by
        rw [SimpleGraph.Walk.edges_concat, List.concat_eq_append,
          List.mem_append, List.mem_singleton]
        exact Or.inr rfl
      rwa [p.concat_dropLast hadj] at hlastDrop
    simpa [hpen] using hlast

theorem torusGhostAugmentedWalkTrace_mem_reach
    (hN : 2 ≤ N) (s : Finset (TorusGhostCoordinate d N))
    (y : CubicTorus d N)
    (p : (torusGhostOpenAugmentedGraph s).Walk (some y) none)
    (hp : p.IsPath) :
    torusGhostAugmentedWalkTrace hN s p ∈ torusGhostReachJointTrace d N y := by
  let P := torusGhostAugmentedPathProjectionOfPath s y p hp
  refine ⟨P.endpoint, ?_, P.walk, ?_⟩
  · rw [Finset.mem_toRight, mem_torusGhostAugmentedWalkTrace_iff hN]
    simpa [torusGhostAugmentedEdge] using P.green_edge_mem
  · intro e he
    rw [Finset.mem_coe, Finset.mem_toLeft,
      mem_torusGhostAugmentedWalkTrace_iff hN]
    let e' : CubicTorusEdge d N := ⟨e, P.walk.edges_subset_edgeSet he⟩
    change torusGhostAugmentedEdge (Sum.inl e') ∈ p.edges
    simpa [torusGhostAugmentedEdge, e'] using P.edge_subset e he

theorem mem_torusGhostReachJointTrace_of_augmented_reachable
    (hN : 2 ≤ N) (s : Finset (TorusGhostCoordinate d N))
    (y : CubicTorus d N)
    (h : (torusGhostOpenAugmentedGraph s).Reachable (some y) none) :
    s ∈ torusGhostReachJointTrace d N y := by
  obtain ⟨p, hp⟩ := h.exists_isPath
  exact (isIncreasingTrace_torusGhostReachJointTrace d N y)
    (torusGhostAugmentedWalkTrace_subset hN s p)
    (torusGhostAugmentedWalkTrace_mem_reach hN s y p hp)

theorem exists_torusGhostAugmentedWalk_some_some
    (s : Finset (TorusGhostCoordinate d N))
    {x y : CubicTorus d N} (w : (cubicTorusGraph d N).Walk x y)
    (hw : torusWalkIsOpen (s.toLeft : Set (CubicTorusEdge d N)) w) :
    ∃ q : (torusGhostOpenAugmentedGraph s).Walk (some x) (some y),
      none ∉ q.support := by
  induction w with
  | nil => exact ⟨.nil, by simp⟩
  | @cons x z y hxz w ih =>
      have hwTail : torusWalkIsOpen
          (s.toLeft : Set (CubicTorusEdge d N)) w := by
        intro e he
        exact hw e (by simp [he])
      obtain ⟨q, hqNone⟩ := ih hwTail
      let e : CubicTorusEdge d N :=
        ⟨s(x, z), (SimpleGraph.mem_edgeSet (cubicTorusGraph d N)).mpr hxz⟩
      have heOpen : e ∈ s.toLeft := by
        apply hw e.1
        simp [e]
      have haug : (torusGhostOpenAugmentedGraph s).Adj (some x) (some z) := by
        rw [← SimpleGraph.mem_edgeSet,
          mem_edgeSet_torusGhostOpenAugmentedGraph_iff]
        refine ⟨Sum.inl e, Finset.mem_toLeft.mp heOpen, ?_⟩
        simp [torusGhostAugmentedEdge, e]
      exact ⟨.cons haug q, by simpa using hqNone⟩

theorem torusGhostOpenAugmentedGraph_reachable_of_mem_reach
    (s : Finset (TorusGhostCoordinate d N)) (y : CubicTorus d N)
    (hs : s ∈ torusGhostReachJointTrace d N y) :
    (torusGhostOpenAugmentedGraph s).Reachable (some y) none := by
  obtain ⟨z, hzGreen, w, hw⟩ := hs
  obtain ⟨q, _hqNone⟩ := exists_torusGhostAugmentedWalk_some_some s w hw
  have hgreen : (torusGhostOpenAugmentedGraph s).Adj (some z) none := by
    rw [torusGhostOpenAugmentedGraph_adj_none_iff]
    exact ⟨z, rfl, Finset.mem_toRight.mp hzGreen⟩
  exact ⟨q.concat hgreen⟩

theorem traceDisjointOccurrence_of_augmented_isEdgeReachable_two
    (hN : 2 ≤ N) (s : Finset (TorusGhostCoordinate d N))
    (y : CubicTorus d N)
    (hreach : (torusGhostOpenAugmentedGraph s).IsEdgeReachable 2 (some y) none) :
    s ∈ TraceDisjointOccurrence (torusGhostReachJointTrace d N y)
      (torusGhostReachJointTrace d N y) := by
  letI : NeZero (2 * N) := ⟨by omega⟩
  obtain ⟨p, q, hp, hq, hpq⟩ :=
    TwoEdgeMenger.exists_two_edgeDisjoint_paths_of_isEdgeReachable_two hreach
  refine ⟨torusGhostAugmentedWalkTrace hN s p,
    torusGhostAugmentedWalkTrace hN s q, ?_, ?_, ?_, ?_, ?_⟩
  · exact disjoint_torusGhostAugmentedWalkTrace hN s hpq
  · exact torusGhostAugmentedWalkTrace_subset hN s p
  · exact torusGhostAugmentedWalkTrace_subset hN s q
  · exact torusGhostAugmentedWalkTrace_mem_reach hN s y p hp
  · exact torusGhostAugmentedWalkTrace_mem_reach hN s y q hq

theorem not_augmented_isEdgeReachable_two_of_not_traceDisjointOccurrence
    (hN : 2 ≤ N) (s : Finset (TorusGhostCoordinate d N))
    (y : CubicTorus d N)
    (hnot : s ∉ TraceDisjointOccurrence (torusGhostReachJointTrace d N y)
      (torusGhostReachJointTrace d N y)) :
    ¬(torusGhostOpenAugmentedGraph s).IsEdgeReachable 2 (some y) none :=
  fun h ↦ hnot (traceDisjointOccurrence_of_augmented_isEdgeReachable_two hN s y h)

theorem terminal_edge_not_bridge_of_atLeastTwoGreen
    (hN : 2 ≤ N) (s : Finset (TorusGhostCoordinate d N))
    (p : (torusGhostOpenAugmentedGraph s).Walk
      (some (cubicTorusOrigin d N)) none)
    (hp : p.IsPath) (hTwo : s ∈ torusAtLeastTwoGreenTrace d N hN) :
    ¬(torusGhostOpenAugmentedGraph s).IsBridge s(p.penultimate, none) := by
  have hnil : ¬ p.Nil := by
    intro h
    exact Option.some_ne_none _ h.eq
  have hadj := p.adj_penultimate hnil
  obtain ⟨z, hpen, hzGreen⟩ :=
    (torusGhostOpenAugmentedGraph_adj_none_iff s p.penultimate).mp hadj
  have hnodup : (p.dropLast.support ++ [none]).Nodup := by
    rw [p.support_dropLast_concat hnil]
    exact hp.support_nodup
  have hnoneDrop : none ∉ p.dropLast.support := by
    have h := (List.nodup_append.mp hnodup).2.2
    exact fun hmem ↦ h none hmem none (by simp) rfl
  unfold torusAtLeastTwoGreenTrace torusOriginGreenCount at hTwo
  rw [Set.mem_setOf_eq, Nat.succ_le_iff, Finset.one_lt_card] at hTwo
  obtain ⟨a, ha, b, hb, hab⟩ := hTwo
  let r := if a = z then b else a
  have hrMem : r ∈ cubicTorusOpenClusterFinset d N hN
      (s.toLeft : Set (CubicTorusEdge d N)) ∩ s.toRight := by
    dsimp only [r]
    split_ifs with haz
    · exact hb
    · exact ha
  have hrz : r ≠ z := by
    dsimp only [r]
    split_ifs with haz
    · intro hrz
      apply hab
      exact haz.trans hrz.symm
    · exact haz
  obtain ⟨hrCluster, hrGreen⟩ := Finset.mem_inter.mp hrMem
  obtain ⟨w, hw⟩ := (mem_cubicTorusOpenClusterFinset hN).mp hrCluster
  obtain ⟨q, hqNone⟩ := exists_torusGhostAugmentedWalk_some_some s w hw
  have hrAdj : (torusGhostOpenAugmentedGraph s).Adj (some r) none := by
    rw [torusGhostOpenAugmentedGraph_adj_none_iff]
    exact ⟨r, rfl, Finset.mem_toRight.mp hrGreen⟩
  let pz : (torusGhostOpenAugmentedGraph s).Walk
      (some (cubicTorusOrigin d N)) (some z) :=
    p.dropLast.copy rfl hpen
  let alt : (torusGhostOpenAugmentedGraph s).Walk (some z) none :=
    (pz.reverse.append q).concat hrAdj
  have hpzNone : none ∉ pz.support := by
    simpa [pz] using hnoneDrop
  have hterminalNot : s(some z, none) ∉ alt.edges := by
    intro he
    dsimp only [alt] at he
    rw [SimpleGraph.Walk.edges_concat, List.concat_eq_append,
      SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_reverse] at he
    simp only [List.mem_append, List.mem_reverse, List.mem_singleton] at he
    rcases he with (he | he) | he
    · exact hpzNone (pz.snd_mem_support_of_mem_edges he)
    · exact hqNone (q.snd_mem_support_of_mem_edges he)
    · rw [Sym2.eq_iff] at he
      rcases he with he | he
      · exact hrz (Option.some_injective _ he.1.symm)
      · simp at he
  intro hbridge
  have hbridge' : (torusGhostOpenAugmentedGraph s).IsBridge
      s(some z, none) := by simpa [hpen] using hbridge
  have hall :=
    (SimpleGraph.isBridge_iff_adj_and_forall_walk_mem_edges.mp hbridge').2 alt
  exact hterminalNot hall

/-- The deterministic core of Grimmett's exceptional-event decomposition (5.72).
Every exceptional configuration has an open bond whose closure is pivotal for the
origin-to-green event, while the outside endpoint retains two edge-disjoint augmented
connections to the ghost vertex. -/
theorem exists_closedPivotal_twoEdgeTail_of_mem_torusGhostExceptionalTrace
    (hN : 2 ≤ N) (s : Finset (TorusGhostCoordinate d N))
    (hs : s ∈ torusGhostExceptionalTrace d N hN) :
    ∃ (e : CubicTorusEdge d N) (x y : CubicTorus d N),
      Sum.inl e ∈ s ∧ e.1 = s(x, y) ∧
      let t := s.erase (Sum.inl e)
      t ∈ torusGhostClosedPivotalJointTrace d N e ∧
        t ∉ torusGhostHitJointTrace d N ∧
        (torusGhostOpenAugmentedGraph t).IsEdgeReachable 2 (some y) none := by
  letI : NeZero (2 * N) := ⟨by omega⟩
  have hTwo : s ∈ torusAtLeastTwoGreenTrace d N hN := hs.1
  have hHit : s ∈ torusGhostHitJointTrace d N := by
    rw [mem_torusGhostHitJointTrace_iff_originGreenCount_pos d N hN]
    unfold torusAtLeastTwoGreenTrace at hTwo
    simp only [Set.mem_setOf_eq] at hTwo
    omega
  have hReach : (torusGhostOpenAugmentedGraph s).Reachable
      (some (cubicTorusOrigin d N)) none :=
    torusGhostOpenAugmentedGraph_reachable_of_mem_reach s
      (cubicTorusOrigin d N) hHit
  obtain ⟨w, hw⟩ := hReach.exists_isPath
  have hNotTwo : ¬ (torusGhostOpenAugmentedGraph s).IsEdgeReachable 2
      (some (cubicTorusOrigin d N)) none :=
    not_augmented_isEdgeReachable_two_of_not_traceDisjointOccurrence
      hN s (cubicTorusOrigin d N) hs.2
  obtain ⟨i, hi, hbridge, htail⟩ :=
    TwoEdgeMenger.exists_bridge_before_twoEdgeReachable_tail w hNotTwo
  have hiSucc : i + 1 < w.length := by
    have hiSuccLe : i + 1 ≤ w.length := by omega
    by_contra h
    have hiSuccEq : i + 1 = w.length := by omega
    have hiEq : i = w.length - 1 := by omega
    apply terminal_edge_not_bridge_of_atLeastTwoGreen hN s w hw hTwo
    have hfirst : w.getVert i = w.penultimate := by rw [hiEq]
    have hsecond : w.getVert (i + 1) = none := by
      rw [hiSuccEq]
      exact w.getVert_length
    rw [hfirst, hsecond] at hbridge
    exact hbridge
  have hxi : w.getVert i ≠ none := by
    intro hnone
    have := (hw.getVert_eq_end_iff hi.le).mp hnone
    omega
  have hyi : w.getVert (i + 1) ≠ none := by
    intro hnone
    have := (hw.getVert_eq_end_iff hiSucc.le).mp hnone
    omega
  obtain ⟨x, hx⟩ := Option.ne_none_iff_exists.mp hxi
  obtain ⟨y, hy⟩ := Option.ne_none_iff_exists.mp hyi
  have hbridgeXY : (torusGhostOpenAugmentedGraph s).IsBridge
      s(some x, some y) := by
    simpa [hx, hy] using hbridge
  obtain ⟨e, heOpen, heVal⟩ :=
    (torusGhostOpenAugmentedGraph_adj_some_iff s x y).mp hbridgeXY.1
  have hedgeEq : torusGhostAugmentedEdge (Sum.inl e) =
      s(w.getVert i, w.getVert (i + 1)) := by
    simp [torusGhostAugmentedEdge, heVal, hx, hy]
  let t := s.erase (Sum.inl e)
  have hgraph : torusGhostOpenAugmentedGraph t =
      (torusGhostOpenAugmentedGraph s).deleteEdges
        {s(w.getVert i, w.getVert (i + 1))} := by
    calc
      torusGhostOpenAugmentedGraph t =
          (torusGhostOpenAugmentedGraph s).deleteEdges
            {torusGhostAugmentedEdge (Sum.inl e)} := by
        simpa [t] using torusGhostOpenAugmentedGraph_erase s (Sum.inl e)
      _ = _ := by rw [hedgeEq]
  have htNotHit : t ∉ torusGhostHitJointTrace d N := by
    intro htHit
    have htReach : (torusGhostOpenAugmentedGraph t).Reachable
        (some (cubicTorusOrigin d N)) none :=
      torusGhostOpenAugmentedGraph_reachable_of_mem_reach t
        (cubicTorusOrigin d N) htHit
    have hdisc := TwoEdgeMenger.not_reachable_delete_bridge_of_isPath_getVert
      w hw hi hbridge
    exact hdisc (by simpa [hgraph] using htReach)
  have htTail : (torusGhostOpenAugmentedGraph t).IsEdgeReachable 2
      (some y) none := by
    have hdel :=
      TwoEdgeMenger.delete_bridge_isEdgeReachable_two_of_isEdgeReachable_two
        hbridge htail
    rw [hgraph]
    simpa [hy] using hdel
  have heClosed : e ∉ t.toLeft := by
    simp [t, Finset.mem_toLeft]
  have htInsert : insert (Sum.inl e) t = s := by
    exact Finset.insert_erase heOpen
  have htPivotal : t.toLeft ∈ pivotalTrace
      (torusHitEdgeTrace d N t.toRight) e := by
    rw [mem_pivotalTrace,
      (isIncreasingTrace_torusHitEdgeTrace d N t.toRight).isPivotalTrace_iff]
    constructor
    · have hInsertHit : insert (Sum.inl e) t ∈
          torusGhostHitJointTrace d N := by
        rw [htInsert]
        exact hHit
      simpa [torusGhostHitJointTrace, torusHitEdgeTrace] using hInsertHit
    · intro hEraseHit
      apply htNotHit
      have htEdgeHit : t.toLeft ∈ torusHitEdgeTrace d N t.toRight := by
        have hsub : @Finset.erase (CubicTorusEdge d N) (Classical.decEq _)
            t.toLeft e ⊆ t.toLeft :=
          @Finset.erase_subset (CubicTorusEdge d N) (Classical.decEq _) e t.toLeft
        exact (isIncreasingTrace_torusHitEdgeTrace d N t.toRight)
          hsub hEraseHit
      simpa [torusGhostHitJointTrace, torusHitEdgeTrace] using htEdgeHit
  refine ⟨e, x, y, heOpen, heVal, ?_, htNotHit, htTail⟩
  exact ⟨heClosed, htPivotal⟩

/-- Two disjoint connections from `y` to green vertices, both constrained to avoid the
coordinate block exposed by an origin cluster. -/
def torusGhostReachAvoidingDisjointTrace (d N : ℕ) (hN : 2 ≤ N)
    (S : Finset (CubicTorus d N)) (y : CubicTorus d N) :
    Set (Finset (TorusGhostCoordinate d N)) :=
  TraceDisjointOccurrence
    (torusGhostReachAvoidingTrace d N hN S y)
    (torusGhostReachAvoidingTrace d N hN S y)

theorem isIncreasingTrace_torusGhostReachAvoidingTrace
    (d N : ℕ) (hN : 2 ≤ N) (S : Finset (CubicTorus d N))
    (y : CubicTorus d N) :
    IsIncreasingTrace (torusGhostReachAvoidingTrace d N hN S y) := by
  intro s t hst
  rintro ⟨z, hzG, hzS, w, hw, hav⟩
  refine ⟨z, Finset.toRight_subset_toRight hst hzG, hzS, w, ?_, hav⟩
  exact torusWalkIsOpen_mono
    (Finset.coe_subset.mpr (Finset.toLeft_subset_toLeft hst)) hw

/-- A projected augmented path avoids every coordinate exposed by a green-free origin
cluster block. -/
theorem torusGhostAugmentedWalkTrace_mem_reachAvoiding_of_ghostBlock
    {n : ℕ} (hN : 2 ≤ N) (A : CubicTorusBondAnimal d N n hN)
    (t : Finset (TorusGhostCoordinate d N)) (y : CubicTorus d N)
    (p : (torusGhostOpenAugmentedGraph t).Walk (some y) none)
    (hp : p.IsPath)
    (hblock : t ∈ finiteTraceCylinder
      A.ghostBlockSupport A.ghostBlockPattern) :
    torusGhostAugmentedWalkTrace hN t p ∈
      torusGhostReachAvoidingTrace d N hN A.vertices y := by
  let P := torusGhostAugmentedPathProjectionOfPath t y p hp
  obtain ⟨hcluster, hgreen⟩ := (A.mem_ghostBlockCylinder_iff t).mp hblock
  have hclusterEq :=
    A.torusOpenClusterFinset_eq_vertices_of_mem_clusterCylinder hcluster
  have htraceSubset : torusGhostAugmentedWalkTrace hN t p ⊆ t :=
    torusGhostAugmentedWalkTrace_subset hN t p
  have hwalkTraceOpen : torusWalkIsOpen
      ((torusGhostAugmentedWalkTrace hN t p).toLeft :
        Set (CubicTorusEdge d N)) P.walk := by
    intro f hf
    let f' : CubicTorusEdge d N := ⟨f, P.walk.edges_subset_edgeSet hf⟩
    rw [Finset.mem_coe, Finset.mem_toLeft,
      mem_torusGhostAugmentedWalkTrace_iff hN]
    change torusGhostAugmentedEdge (Sum.inl f') ∈ p.edges
    simpa [torusGhostAugmentedEdge, f'] using P.edge_subset f hf
  have hwalkOpen : torusWalkIsOpen
      (t.toLeft : Set (CubicTorusEdge d N)) P.walk :=
    torusWalkIsOpen_mono
      (Finset.coe_subset.mpr (Finset.toLeft_subset_toLeft htraceSubset))
      hwalkTraceOpen
  have hzTrace : P.endpoint ∈
      (torusGhostAugmentedWalkTrace hN t p).toRight := by
    rw [Finset.mem_toRight, mem_torusGhostAugmentedWalkTrace_iff hN]
    simpa [torusGhostAugmentedEdge] using P.green_edge_mem
  have hzOutside : P.endpoint ∉ A.vertices := by
    intro hzA
    exact Finset.disjoint_left.mp hgreen hzA
      (Finset.mem_toRight.mpr P.green_mem)
  refine ⟨P.endpoint, hzTrace, hzOutside, P.walk, hwalkTraceOpen, ?_⟩
  intro f hf hinc
  obtain ⟨c, hcf, hcA⟩ := mem_cubicTorusIncidentEdges.mp hinc
  have hcCluster : c ∈ cubicTorusOpenCluster d N
      (t.toLeft : Set (CubicTorusEdge d N)) := by
    rw [← mem_cubicTorusOpenClusterFinset hN, hclusterEq]
    exact hcA
  have hcSupport : c ∈ P.walk.support :=
    SimpleGraph.Walk.mem_support_iff_exists_mem_edges.mpr
      (Or.inr ⟨f.1, hf, hcf⟩)
  obtain ⟨q, hq⟩ := hcCluster
  have hzCluster : P.endpoint ∈ cubicTorusOpenCluster d N
      (t.toLeft : Set (CubicTorusEdge d N)) := by
    refine ⟨q.append (P.walk.dropUntil c hcSupport), ?_⟩
    intro g hg
    rw [SimpleGraph.Walk.edges_append, List.mem_append] at hg
    rcases hg with hg | hg
    · exact hq g hg
    · exact hwalkOpen g
        (P.walk.edges_dropUntil_subset hcSupport hg)
  have hzFin : P.endpoint ∈ cubicTorusOpenClusterFinset d N hN
      (t.toLeft : Set (CubicTorusEdge d N)) :=
    (mem_cubicTorusOpenClusterFinset hN).mpr hzCluster
  rw [hclusterEq] at hzFin
  exact hzOutside hzFin

theorem torusGhostReachAvoidingDisjointTrace_of_augmented_isEdgeReachable_two
    {n : ℕ} (hN : 2 ≤ N) (A : CubicTorusBondAnimal d N n hN)
    (t : Finset (TorusGhostCoordinate d N)) (y : CubicTorus d N)
    (hblock : t ∈ finiteTraceCylinder
      A.ghostBlockSupport A.ghostBlockPattern)
    (htail : (torusGhostOpenAugmentedGraph t).IsEdgeReachable 2 (some y) none) :
    t ∈ torusGhostReachAvoidingDisjointTrace d N hN A.vertices y := by
  letI : NeZero (2 * N) := ⟨by omega⟩
  obtain ⟨p, q, hp, hq, hpq⟩ :=
    TwoEdgeMenger.exists_two_edgeDisjoint_paths_of_isEdgeReachable_two htail
  refine ⟨torusGhostAugmentedWalkTrace hN t p,
    torusGhostAugmentedWalkTrace hN t q, ?_, ?_, ?_, ?_, ?_⟩
  · exact disjoint_torusGhostAugmentedWalkTrace hN t hpq
  · exact torusGhostAugmentedWalkTrace_subset hN t p
  · exact torusGhostAugmentedWalkTrace_subset hN t q
  · exact torusGhostAugmentedWalkTrace_mem_reachAvoiding_of_ghostBlock
      hN A t y p hp hblock
  · exact torusGhostAugmentedWalkTrace_mem_reachAvoiding_of_ghostBlock
      hN A t y q hq hblock

theorem traceIgnores_torusGhostReachAvoidingDisjointTrace
    (d N : ℕ) (hN : 2 ≤ N) (S : Finset (CubicTorus d N))
    (y : CubicTorus d N) :
    TraceIgnores ((cubicTorusIncidentEdges d N hN S).disjSum S)
      (torusGhostReachAvoidingDisjointTrace d N hN S y) :=
  (traceIgnores_torusGhostReachAvoidingTrace d N hN S y).traceDisjointOccurrence_self

/-- Conditional BK in the graph outside an exposed cluster: the two-connection
probability is at most one restricted connection times the unrestricted `θ_N`. -/
theorem finiteBernoulliProbabilityFamily_reachAvoidingDisjoint_le_mul_theta
    (d N : ℕ) (hN : 2 ≤ N) (p γ : I)
    (S : Finset (CubicTorus d N)) (y : CubicTorus d N) :
    finiteBernoulliProbabilityFamily (torusGhostCoordinateFinset d N hN)
        (torusGhostCoordinateDensity p γ)
        (torusGhostReachAvoidingDisjointTrace d N hN S y) ≤
      finiteBernoulliProbabilityFamily (torusGhostCoordinateFinset d N hN)
          (torusGhostCoordinateDensity p γ)
          (torusGhostReachAvoidingTrace d N hN S y) *
        torusGhostThetaPolynomial d N hN p γ := by
  let R := torusGhostReachAvoidingTrace d N hN S y
  have hbk := finiteBernoulliProbabilityFamily_traceDisjointOccurrence_le_mul
    (E := torusGhostCoordinateFinset d N hN)
    (q := torusGhostCoordinateDensity (p : ℝ) (γ : ℝ))
    (torusGhostCoordinateDensity_nonneg p γ)
    (torusGhostCoordinateDensity_le_one p γ)
    (isIncreasingTrace_torusGhostReachAvoidingTrace d N hN S y)
    (isIncreasingTrace_torusGhostReachAvoidingTrace d N hN S y)
  have hmono := finiteBernoulliProbabilityFamily_torusGhostReachAvoidingTrace_le_theta
    d N hN p γ S y
  have hnonneg : 0 ≤ finiteBernoulliProbabilityFamily
      (torusGhostCoordinateFinset d N hN)
      (torusGhostCoordinateDensity p γ) R :=
    finiteBernoulliProbabilityFamily_nonneg
      (torusGhostCoordinateDensity_nonneg p γ)
      (torusGhostCoordinateDensity_le_one p γ) R
  calc
    finiteBernoulliProbabilityFamily (torusGhostCoordinateFinset d N hN)
        (torusGhostCoordinateDensity p γ)
        (torusGhostReachAvoidingDisjointTrace d N hN S y) ≤
      finiteBernoulliProbabilityFamily (torusGhostCoordinateFinset d N hN)
          (torusGhostCoordinateDensity p γ) R *
        finiteBernoulliProbabilityFamily (torusGhostCoordinateFinset d N hN)
          (torusGhostCoordinateDensity p γ) R := by
      simpa [torusGhostReachAvoidingDisjointTrace, R] using hbk
    _ ≤ finiteBernoulliProbabilityFamily (torusGhostCoordinateFinset d N hN)
          (torusGhostCoordinateDensity p γ) R *
        torusGhostThetaPolynomial d N hN p γ :=
      mul_le_mul_of_nonneg_left hmono hnonneg

def torusGhostClusterBlockDoubleReachTrace
    {d N n : ℕ} {hN : 2 ≤ N}
    (A : CubicTorusBondAnimal d N n hN)
    (b : CubicTorus d N × CubicDirection d) :
    Set (Finset (TorusGhostCoordinate d N)) :=
  finiteTraceCylinder A.ghostBlockSupport A.ghostBlockPattern ∩
    torusGhostReachAvoidingDisjointTrace d N hN A.vertices
      (cubicTorusStepFrom b.1 b.2)

theorem finiteBernoulliProbabilityFamily_clusterBlockDoubleReach_le
    {d N n : ℕ} {hN : 2 ≤ N}
    (A : CubicTorusBondAnimal d N n hN) (p γ : I)
    (b : CubicTorus d N × CubicDirection d) :
    finiteBernoulliProbabilityFamily (torusGhostCoordinateFinset d N hN)
        (torusGhostCoordinateDensity p γ)
        (torusGhostClusterBlockDoubleReachTrace A b) ≤
      torusGhostThetaPolynomial d N hN p γ *
        finiteBernoulliProbabilityFamily (torusGhostCoordinateFinset d N hN)
          (torusGhostCoordinateDensity p γ)
          (torusGhostClusterBlockReachTrace A b) := by
  have hdoubleFactor :
      finiteBernoulliProbabilityFamily (torusGhostCoordinateFinset d N hN)
          (torusGhostCoordinateDensity p γ)
          (torusGhostClusterBlockDoubleReachTrace A b) =
        finiteBernoulliProbabilityFamily (torusGhostCoordinateFinset d N hN)
            (torusGhostCoordinateDensity p γ)
            (finiteTraceCylinder A.ghostBlockSupport A.ghostBlockPattern) *
          finiteBernoulliProbabilityFamily (torusGhostCoordinateFinset d N hN)
            (torusGhostCoordinateDensity p γ)
            (torusGhostReachAvoidingDisjointTrace d N hN A.vertices
              (cubicTorusStepFrom b.1 b.2)) := by
    unfold torusGhostClusterBlockDoubleReachTrace
    apply finiteBernoulliProbabilityFamily_finiteTraceCylinder_inter_indep
    · exact A.ghostBlockSupport_subset_coordinateFinset
    · exact A.ghostBlockPattern_subset_support
    · exact traceIgnores_torusGhostReachAvoidingDisjointTrace d N hN
        A.vertices (cubicTorusStepFrom b.1 b.2)
  have hsingleFactor := finiteBernoulliProbabilityFamily_ghostBlock_inter_reachAvoiding
    A p γ (cubicTorusStepFrom b.1 b.2)
  have houtside := finiteBernoulliProbabilityFamily_reachAvoidingDisjoint_le_mul_theta
    d N hN p γ A.vertices (cubicTorusStepFrom b.1 b.2)
  have hblockNonneg := finiteBernoulliProbabilityFamily_ghostBlock_nonneg A p γ
  rw [hdoubleFactor]
  unfold torusGhostClusterBlockReachTrace
  rw [hsingleFactor]
  have hmul := mul_le_mul_of_nonneg_left houtside hblockNonneg
  nlinarith

def torusGhostClusterBlockOpenDoubleReachTrace
    {d N n : ℕ} {hN : 2 ≤ N}
    (A : CubicTorusBondAnimal d N n hN)
    (b : CubicTorus d N × CubicDirection d) :
    Set (Finset (TorusGhostCoordinate d N)) :=
  finiteTraceCylinder A.ghostBlockSupport
      (insert (Sum.inl (cubicTorusStepEdge hN b.1 b.2))
        A.ghostBlockPattern) ∩
    torusGhostReachAvoidingDisjointTrace d N hN A.vertices
      (cubicTorusStepFrom b.1 b.2)

noncomputable def torusGhostClusterBlockOpenDoubleReachUnion
    {d N n : ℕ} {hN : 2 ≤ N}
    (A : CubicTorusBondAnimal d N n hN) :
    Set (Finset (TorusGhostCoordinate d N)) :=
  finsetUnionTrace (torusBoundarySteps d N A.vertices)
    (torusGhostClusterBlockOpenDoubleReachTrace A)

noncomputable def torusGhostClusterBlockOpenDoubleReachSizeUnion
    (d N n : ℕ) (hN : 2 ≤ N) :
    Set (Finset (TorusGhostCoordinate d N)) :=
  finsetUnionTrace (Finset.univ : Finset (CubicTorusBondAnimal d N n hN))
    torusGhostClusterBlockOpenDoubleReachUnion

noncomputable def torusGhostClusterBlockOpenDoubleReachAll
    (d N : ℕ) (hN : 2 ≤ N) :
    Set (Finset (TorusGhostCoordinate d N)) :=
  finsetUnionTrace
    (Finset.range ((cubicTorusVertexFinset d N hN).card + 1))
    (fun n ↦ torusGhostClusterBlockOpenDoubleReachSizeUnion d N n hN)

/-- Event-level form of (5.72): every exceptional configuration lies in an opened
cluster-block event with two disjoint outside connections. -/
theorem torusGhostExceptionalTrace_subset_openDoubleClusterBlocks
    (d N : ℕ) (hN : 2 ≤ N) :
    torusGhostExceptionalTrace d N hN ⊆
      torusGhostClusterBlockOpenDoubleReachAll d N hN := by
  intro s hs
  obtain ⟨e, x, y, heOpen, heVal, htClosed, htNot, htTail⟩ :=
    exists_closedPivotal_twoEdgeTail_of_mem_torusGhostExceptionalTrace hN s hs
  let t := s.erase (Sum.inl e)
  have htTailT : (torusGhostOpenAugmentedGraph t).IsEdgeReachable 2
      (some y) none := by
    simpa [t] using htTail
  let S := cubicTorusOpenClusterFinset d N hN
    (t.toLeft : Set (CubicTorusEdge d N))
  let n := S.card
  let A : CubicTorusBondAnimal d N n hN :=
    CubicTorusBondAnimal.ofConfiguration
      (t.toLeft : Set (CubicTorusEdge d N)) rfl
  have hcluster : (t.toLeft : Set (CubicTorusEdge d N)) ∈ A.clusterCylinder :=
    CubicTorusBondAnimal.ofConfiguration_mem_clusterCylinder
      (t.toLeft : Set (CubicTorusEdge d N)) rfl
  have hclusterEq :=
    A.torusOpenClusterFinset_eq_vertices_of_mem_clusterCylinder hcluster
  have hgreen : Disjoint A.vertices t.toRight := by
    rw [Finset.disjoint_left]
    intro z hzA hzGreen
    apply htNot
    refine ⟨z, hzGreen, ?_⟩
    rw [← mem_cubicTorusOpenClusterFinset hN, hclusterEq]
    exact hzA
  have hblock : t ∈ finiteTraceCylinder
      A.ghostBlockSupport A.ghostBlockPattern :=
    (A.mem_ghostBlockCylinder_iff t).mpr ⟨hcluster, hgreen⟩
  have htReachY : t ∈ torusGhostReachJointTrace d N y :=
    mem_torusGhostReachJointTrace_of_augmented_reachable hN t y
      (htTailT.reachable (by omega))
  have hyNot : y ∉ A.vertices := by
    intro hyA
    obtain ⟨z, hzGreen, w, hw⟩ := htReachY
    have hyCluster : y ∈ cubicTorusOpenCluster d N
        (t.toLeft : Set (CubicTorusEdge d N)) := by
      rw [← mem_cubicTorusOpenClusterFinset hN, hclusterEq]
      exact hyA
    obtain ⟨q, hq⟩ := hyCluster
    apply htNot
    refine ⟨z, hzGreen, q.append w, ?_⟩
    intro f hf
    rw [SimpleGraph.Walk.edges_append, List.mem_append] at hf
    rcases hf with hf | hf
    · exact hq f hf
    · exact hw f hf
  obtain ⟨heClosed, hePivotal⟩ := htClosed
  have hpivCases :=
    (isIncreasingTrace_torusHitEdgeTrace d N t.toRight).isPivotalTrace_iff
      e t.toLeft |>.mp (mem_pivotalTrace.mp hePivotal)
  obtain ⟨z, hzGreen, hzInsert⟩ := hpivCases.1
  have hzInsert' : z ∈ cubicTorusOpenCluster d N
      (insert e (t.toLeft : Set (CubicTorusEdge d N))) := by
    simpa using hzInsert
  rcases mem_openCluster_insert_edge_cases d N hN t.toLeft e hzInsert' with
    hzOld | ⟨a, hae, haCluster, b', hb'e, hb'Not, q, hqOpen, hqAvoid⟩
  · exact (htNot ⟨z, hzGreen, hzOld⟩).elim
  · have haA : a ∈ A.vertices := by
      rw [← hclusterEq, mem_cubicTorusOpenClusterFinset hN]
      exact haCluster
    have haCases : a = x ∨ a = y := by
      rw [heVal, Sym2.mem_iff] at hae
      exact hae
    have hxA : x ∈ A.vertices := by
      rcases haCases with hax | hay
      · simpa [hax] using haA
      · exact (hyNot (hay ▸ haA)).elim
    have hxyAdj : (cubicTorusGraph d N).Adj x y := by
      rw [← SimpleGraph.mem_edgeSet, ← heVal]
      exact e.2
    obtain ⟨dir, hdir⟩ :=
      (cubicTorusGraph_adj_iff_exists_stepFrom hN x y).mp hxyAdj
    let b : CubicTorus d N × CubicDirection d := (x, dir)
    have hb : b ∈ torusBoundarySteps d N A.vertices := by
      rw [mem_torusBoundarySteps]
      exact ⟨hxA, by simpa [b, hdir] using hyNot⟩
    have hbe : cubicTorusStepEdge hN b.1 b.2 = e := by
      apply Subtype.ext
      change s(x, cubicTorusStepFrom x dir) = e.1
      rw [← hdir, ← heVal]
    have hcoordSupport : Sum.inl e ∈ A.ghostBlockSupport := by
      apply Finset.inl_mem_disjSum.mpr
      apply mem_cubicTorusIncidentEdges.mpr
      exact ⟨x, by simp [heVal], hxA⟩
    have hdouble : t ∈ torusGhostReachAvoidingDisjointTrace
        d N hN A.vertices (cubicTorusStepFrom b.1 b.2) := by
      have h := torusGhostReachAvoidingDisjointTrace_of_augmented_isEdgeReachable_two
        hN A t y hblock htTailT
      simpa [b, hdir] using h
    have hopenCylinder : insert (Sum.inl e) t ∈
        finiteTraceCylinder A.ghostBlockSupport
          (insert (Sum.inl e) A.ghostBlockPattern) :=
      mem_finiteTraceCylinder_insert_pattern hblock hcoordSupport
    have hopenDouble : insert (Sum.inl e) t ∈
        torusGhostReachAvoidingDisjointTrace d N hN A.vertices
          (cubicTorusStepFrom b.1 b.2) := by
      exact (traceIgnores_torusGhostReachAvoidingDisjointTrace
        d N hN A.vertices (cubicTorusStepFrom b.1 b.2)).insert_iff
          hcoordSupport t |>.mpr hdouble
    have hinsert : insert (Sum.inl e) t = s :=
      Finset.insert_erase heOpen
    have hsOpenBlock : s ∈ torusGhostClusterBlockOpenDoubleReachTrace A b := by
      rw [← hinsert]
      unfold torusGhostClusterBlockOpenDoubleReachTrace
      rw [hbe]
      exact ⟨hopenCylinder, hopenDouble⟩
    unfold torusGhostClusterBlockOpenDoubleReachAll
      torusGhostClusterBlockOpenDoubleReachSizeUnion
      torusGhostClusterBlockOpenDoubleReachUnion finsetUnionTrace
    simp only [Set.mem_setOf_eq, Finset.mem_univ, true_and]
    refine ⟨n, ?_, A, b, hb, hsOpenBlock⟩
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (Finset.card_le_card (restrictTo_subset _ _))

theorem torusBoundaryStepsForEdge_subsingleton
    (hN : 2 ≤ N) (S : Finset (CubicTorus d N))
    (e : CubicTorusEdge d N) :
    (torusBoundaryStepsForEdge hN S e : Set
      (CubicTorus d N × CubicDirection d)).Subsingleton := by
  intro b hb c hc
  rw [torusBoundaryStepsForEdge, Finset.mem_coe, Finset.mem_filter] at hb hc
  obtain ⟨hbBoundary, hbe⟩ := hb
  obtain ⟨hcBoundary, hce⟩ := hc
  have hedge : s(b.1, cubicTorusStepFrom b.1 b.2) =
      s(c.1, cubicTorusStepFrom c.1 c.2) := by
    have := congrArg Subtype.val (hbe.trans hce.symm)
    simpa [cubicTorusStepEdge] using this
  rcases Sym2.eq_iff.mp hedge with hsame | hswap
  · apply Prod.ext
    · exact hsame.1
    · apply cubicTorusStepFrom_injective_direction hN b.1
      simpa [hsame.1] using hsame.2
  · have hbData := (mem_torusBoundarySteps.mp hbBoundary)
    have hcData := (mem_torusBoundarySteps.mp hcBoundary)
    exact (hcData.2 (hswap.1 ▸ hbData.1)).elim

/-- A closed cluster block with an outside connection makes its indexed boundary edge
closed-pivotal for the origin-to-green event. -/
theorem torusGhostClusterBlockReachTrace_subset_closedPivotal
    {d N n : ℕ} {hN : 2 ≤ N}
    (A : CubicTorusBondAnimal d N n hN)
    (b : CubicTorus d N × CubicDirection d)
    (hb : b ∈ torusBoundarySteps d N A.vertices) :
    torusGhostClusterBlockReachTrace A b ⊆
      torusGhostClosedPivotalJointTrace d N
        (cubicTorusStepEdge hN b.1 b.2) := by
  intro s hs
  obtain ⟨hblock, hreach⟩ := hs
  obtain ⟨hcluster, hgreen⟩ := (A.mem_ghostBlockCylinder_iff s).mp hblock
  obtain ⟨hbInside, hbOutside⟩ := mem_torusBoundarySteps.mp hb
  let y := cubicTorusStepFrom b.1 b.2
  let e := cubicTorusStepEdge hN b.1 b.2
  have heBoundary : e ∈ A.boundary := by
    apply Finset.mem_sdiff.mpr
    constructor
    · apply mem_cubicTorusIncidentEdges.mpr
      exact ⟨b.1, by simp [e, cubicTorusStepEdge], hbInside⟩
    · intro heA
      exact hbOutside (A.edge_endpoints e heA y
        (by simp [e, y, cubicTorusStepEdge]))
  have heClosed : e ∉ s.toLeft := by
    have htrace := (mem_finiteCylinder.mp hcluster) e
      (Finset.mem_union_right _ heBoundary)
    intro heOpen
    exact (Finset.mem_sdiff.mp heBoundary).2 (htrace.mp heOpen)
  have hnotHit : s.toLeft ∉ torusHitEdgeTrace d N s.toRight := by
    rintro ⟨z, hzGreen, hzCluster⟩
    have hzFin := (mem_cubicTorusOpenClusterFinset hN).mpr hzCluster
    rw [A.torusOpenClusterFinset_eq_vertices_of_mem_clusterCylinder hcluster] at hzFin
    exact Finset.disjoint_left.mp hgreen hzFin hzGreen
  have hinsertHit : insert e s.toLeft ∈ torusHitEdgeTrace d N s.toRight := by
    obtain ⟨z, hzGreen, hzOutside, w, hw, hav⟩ := hreach
    obtain ⟨q, hqA⟩ := A.connected b.1 hbInside
    have hqOpen : torusWalkIsOpen
        (s.toLeft : Set (CubicTorusEdge d N)) q := by
      intro f hf
      let f' : CubicTorusEdge d N := ⟨f, q.edges_subset_edgeSet hf⟩
      have hfA : f' ∈ A.edges := hqA f hf
      exact (mem_finiteCylinder.mp hcluster f'
        (Finset.mem_union_left _ hfA)).mpr hfA
    have hadj : (cubicTorusGraph d N).Adj b.1 y :=
      cubicTorusGraph_adj_stepFrom hN b.1 b.2
    let q' := (q.concat hadj).append w
    refine ⟨z, hzGreen, q', ?_⟩
    intro f hf
    rw [SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_concat,
      List.concat_eq_append, List.mem_append, List.mem_append,
      List.mem_singleton] at hf
    rcases hf with (hf | hf) | hf
    · exact Finset.mem_insert_of_mem (hqOpen f hf)
    · have hfe : (⟨f, (q.concat hadj).edges_subset_edgeSet
          (by rw [SimpleGraph.Walk.edges_concat, List.concat_eq_append,
            List.mem_append]; exact Or.inr (by simpa using hf))⟩ :
          CubicTorusEdge d N) = e := by
        apply Subtype.ext
        simpa [e, y, cubicTorusStepEdge] using hf
      simp [hfe]
    · exact Finset.mem_insert_of_mem (hw f hf)
  unfold torusGhostClosedPivotalJointTrace closedPivotalTrace
  refine ⟨heClosed, ?_⟩
  rw [mem_pivotalTrace,
    (isIncreasingTrace_torusHitEdgeTrace d N s.toRight).isPivotalTrace_iff]
  constructor
  · convert hinsertHit using 1
    ext f
    simp [e]
  intro heraseHit
  have hsub : @Finset.erase (CubicTorusEdge d N) (Classical.decEq _)
      s.toLeft (cubicTorusStepEdge hN b.1 b.2) ⊆ s.toLeft :=
    @Finset.erase_subset (CubicTorusEdge d N) (Classical.decEq _)
      (cubicTorusStepEdge hN b.1 b.2) s.toLeft
  exact hnotHit ((isIncreasingTrace_torusHitEdgeTrace d N s.toRight)
    hsub heraseHit)

theorem torusGhostClusterBlockReachUnionForEdge_subset_ghostBlock
    {d N n : ℕ} {hN : 2 ≤ N}
    (A : CubicTorusBondAnimal d N n hN) (e : CubicTorusEdge d N) :
    torusGhostClusterBlockReachUnionForEdge A e ⊆
      finiteTraceCylinder A.ghostBlockSupport A.ghostBlockPattern := by
  rintro s ⟨b, hb, hs⟩
  exact hs.1

theorem disjoint_torusGhostClusterBlockReachUnionForEdge
    {d N n : ℕ} {hN : 2 ≤ N}
    {A B : CubicTorusBondAnimal d N n hN} (hAB : A ≠ B)
    (e : CubicTorusEdge d N) :
    Disjoint (torusGhostClusterBlockReachUnionForEdge A e)
      (torusGhostClusterBlockReachUnionForEdge B e) := by
  rw [Set.disjoint_left]
  intro s hsA hsB
  have hblockA := torusGhostClusterBlockReachUnionForEdge_subset_ghostBlock A e hsA
  have hblockB := torusGhostClusterBlockReachUnionForEdge_subset_ghostBlock B e hsB
  obtain ⟨hclusterA, _⟩ := (A.mem_ghostBlockCylinder_iff s).mp hblockA
  obtain ⟨hclusterB, _⟩ := (B.mem_ghostBlockCylinder_iff s).mp hblockB
  exact Set.disjoint_left.mp
    (CubicTorusBondAnimal.clusterCylinder_pairwiseDisjoint hAB)
    hclusterA hclusterB

theorem disjoint_torusGhostClusterBlockReachSizeUnionForEdge
    (d N : ℕ) (hN : 2 ≤ N) {n m : ℕ} (hnm : n ≠ m)
    (e : CubicTorusEdge d N) :
    Disjoint (torusGhostClusterBlockReachSizeUnionForEdge d N n hN e)
      (torusGhostClusterBlockReachSizeUnionForEdge d N m hN e) := by
  rw [Set.disjoint_left]
  rintro s ⟨A, hAuniv, hsA⟩ ⟨B, hBuniv, hsB⟩
  have hblockA := torusGhostClusterBlockReachUnionForEdge_subset_ghostBlock A e hsA
  have hblockB := torusGhostClusterBlockReachUnionForEdge_subset_ghostBlock B e hsB
  obtain ⟨hclusterA, _⟩ := (A.mem_ghostBlockCylinder_iff s).mp hblockA
  obtain ⟨hclusterB, _⟩ := (B.mem_ghostBlockCylinder_iff s).mp hblockB
  apply hnm
  calc
    n = A.vertices.card := A.vertices_card.symm
    _ = (cubicTorusOpenClusterFinset d N hN
        (s.toLeft : Set (CubicTorusEdge d N))).card := by
      rw [A.torusOpenClusterFinset_eq_vertices_of_mem_clusterCylinder hclusterA]
    _ = B.vertices.card := by
      rw [B.torusOpenClusterFinset_eq_vertices_of_mem_clusterCylinder hclusterB]
    _ = m := B.vertices_card

theorem finiteBernoulliProbabilityFamily_clusterBlockReachUnionForEdge_eq_sum
    {d N n : ℕ} {hN : 2 ≤ N}
    (A : CubicTorusBondAnimal d N n hN) (e : CubicTorusEdge d N)
    (p γ : I) :
    finiteBernoulliProbabilityFamily (torusGhostCoordinateFinset d N hN)
        (torusGhostCoordinateDensity p γ)
        (torusGhostClusterBlockReachUnionForEdge A e) =
      ∑ b ∈ torusBoundaryStepsForEdge hN A.vertices e,
        finiteBernoulliProbabilityFamily (torusGhostCoordinateFinset d N hN)
          (torusGhostCoordinateDensity p γ)
          (torusGhostClusterBlockReachTrace A b) := by
  unfold torusGhostClusterBlockReachUnionForEdge
  apply finiteBernoulliProbabilityFamily_finsetUnionTrace_eq_sum_of_disjoint
  intro b hb c hc hbc
  exact (hbc (torusBoundaryStepsForEdge_subsingleton hN A.vertices e hb hc)).elim

theorem finiteBernoulliProbabilityFamily_clusterBlockReachAllForEdge_eq_sum
    (d N : ℕ) (hN : 2 ≤ N) (e : CubicTorusEdge d N) (p γ : I) :
    finiteBernoulliProbabilityFamily (torusGhostCoordinateFinset d N hN)
        (torusGhostCoordinateDensity p γ)
        (torusGhostClusterBlockReachAllForEdge d N hN e) =
      ∑ n ∈ Finset.range ((cubicTorusVertexFinset d N hN).card + 1),
        ∑ A : CubicTorusBondAnimal d N n hN,
          ∑ b ∈ torusBoundaryStepsForEdge hN A.vertices e,
            finiteBernoulliProbabilityFamily
              (torusGhostCoordinateFinset d N hN)
              (torusGhostCoordinateDensity p γ)
              (torusGhostClusterBlockReachTrace A b) := by
  unfold torusGhostClusterBlockReachAllForEdge
  rw [finiteBernoulliProbabilityFamily_finsetUnionTrace_eq_sum_of_disjoint]
  · apply Finset.sum_congr rfl
    intro n hn
    unfold torusGhostClusterBlockReachSizeUnionForEdge
    rw [finiteBernoulliProbabilityFamily_finsetUnionTrace_eq_sum_of_disjoint]
    · apply Finset.sum_congr rfl
      intro A hA
      exact finiteBernoulliProbabilityFamily_clusterBlockReachUnionForEdge_eq_sum
        A e p γ
    · intro A hA B hB hAB
      exact disjoint_torusGhostClusterBlockReachUnionForEdge hAB e
  · intro n hn m hm hnm
    exact disjoint_torusGhostClusterBlockReachSizeUnionForEdge d N hN hnm e

theorem torusGhostClusterBlockReachAllForEdge_eq_closedPivotal
    (d N : ℕ) (hN : 2 ≤ N) (e : CubicTorusEdge d N) :
    torusGhostClusterBlockReachAllForEdge d N hN e =
      torusGhostClosedPivotalJointTrace d N e := by
  apply Set.Subset.antisymm
  · rintro s ⟨n, hn, A, hA, b, hb, hs⟩
    have hbData := Finset.mem_filter.mp hb
    rw [← hbData.2]
    exact torusGhostClusterBlockReachTrace_subset_closedPivotal A b
      hbData.1 hs
  · exact torusGhostClosedPivotalJointTrace_subset_clusterBlocks d N hN e

theorem one_sub_mul_probability_openDouble_eq
    {d N n : ℕ} {hN : 2 ≤ N}
    (A : CubicTorusBondAnimal d N n hN)
    (b : CubicTorus d N × CubicDirection d)
    (hb : b ∈ torusBoundarySteps d N A.vertices) (p γ : I) :
    (1 - (p : ℝ)) *
        finiteBernoulliProbabilityFamily (torusGhostCoordinateFinset d N hN)
          (torusGhostCoordinateDensity p γ)
          (torusGhostClusterBlockOpenDoubleReachTrace A b) =
      (p : ℝ) *
        finiteBernoulliProbabilityFamily (torusGhostCoordinateFinset d N hN)
          (torusGhostCoordinateDensity p γ)
          (torusGhostClusterBlockDoubleReachTrace A b) := by
  let c : TorusGhostCoordinate d N :=
    Sum.inl (cubicTorusStepEdge hN b.1 b.2)
  have hbData := mem_torusBoundarySteps.mp hb
  have hcSupport : c ∈ A.ghostBlockSupport := by
    apply Finset.inl_mem_disjSum.mpr
    apply mem_cubicTorusIncidentEdges.mpr
    exact ⟨b.1, by simp [cubicTorusStepEdge], hbData.1⟩
  have hcPattern : c ∉ A.ghostBlockPattern := by
    intro hc
    have heA : cubicTorusStepEdge hN b.1 b.2 ∈ A.edges := by
      simpa [c, CubicTorusBondAnimal.ghostBlockPattern] using hc
    exact hbData.2 (A.edge_endpoints (cubicTorusStepEdge hN b.1 b.2)
      heA (cubicTorusStepFrom b.1 b.2) (by simp [cubicTorusStepEdge]))
  unfold torusGhostClusterBlockOpenDoubleReachTrace
    torusGhostClusterBlockDoubleReachTrace
  have h := one_sub_mul_probability_insert_pattern_eq
    (E := torusGhostCoordinateFinset d N hN)
    (R := A.ghostBlockSupport) (r := A.ghostBlockPattern) (a := c)
    (torusGhostCoordinateDensity (p : ℝ) (γ : ℝ))
    (torusGhostReachAvoidingDisjointTrace d N hN A.vertices
      (cubicTorusStepFrom b.1 b.2))
    A.ghostBlockSupport_subset_coordinateFinset
    A.ghostBlockPattern_subset_support hcSupport hcPattern
    (traceIgnores_torusGhostReachAvoidingDisjointTrace d N hN
      A.vertices (cubicTorusStepFrom b.1 b.2))
  simpa [c, torusGhostCoordinateDensity] using h

theorem one_sub_mul_probability_openDouble_le
    {d N n : ℕ} {hN : 2 ≤ N}
    (A : CubicTorusBondAnimal d N n hN)
    (b : CubicTorus d N × CubicDirection d)
    (hb : b ∈ torusBoundarySteps d N A.vertices) (p γ : I) :
    (1 - (p : ℝ)) *
        finiteBernoulliProbabilityFamily (torusGhostCoordinateFinset d N hN)
          (torusGhostCoordinateDensity p γ)
          (torusGhostClusterBlockOpenDoubleReachTrace A b) ≤
      (p : ℝ) * torusGhostThetaPolynomial d N hN p γ *
        finiteBernoulliProbabilityFamily (torusGhostCoordinateFinset d N hN)
          (torusGhostCoordinateDensity p γ)
          (torusGhostClusterBlockReachTrace A b) := by
  rw [one_sub_mul_probability_openDouble_eq A b hb p γ]
  have h := finiteBernoulliProbabilityFamily_clusterBlockDoubleReach_le A p γ b
  have hp : 0 ≤ (p : ℝ) := p.2.1
  nlinarith [mul_le_mul_of_nonneg_left h hp]

theorem finiteBernoulliProbabilityFamily_openDoubleAll_le_sum
    (d N : ℕ) (hN : 2 ≤ N) (p γ : I) :
    finiteBernoulliProbabilityFamily (torusGhostCoordinateFinset d N hN)
        (torusGhostCoordinateDensity p γ)
        (torusGhostClusterBlockOpenDoubleReachAll d N hN) ≤
      ∑ n ∈ Finset.range ((cubicTorusVertexFinset d N hN).card + 1),
        ∑ A : CubicTorusBondAnimal d N n hN,
          ∑ b ∈ torusBoundarySteps d N A.vertices,
            finiteBernoulliProbabilityFamily
              (torusGhostCoordinateFinset d N hN)
              (torusGhostCoordinateDensity p γ)
              (torusGhostClusterBlockOpenDoubleReachTrace A b) := by
  unfold torusGhostClusterBlockOpenDoubleReachAll
    torusGhostClusterBlockOpenDoubleReachSizeUnion
    torusGhostClusterBlockOpenDoubleReachUnion
  calc
    finiteBernoulliProbabilityFamily (torusGhostCoordinateFinset d N hN)
        (torusGhostCoordinateDensity p γ)
        (finsetUnionTrace
          (Finset.range ((cubicTorusVertexFinset d N hN).card + 1))
          (fun n ↦ finsetUnionTrace
            (Finset.univ : Finset (CubicTorusBondAnimal d N n hN))
            (fun A ↦ finsetUnionTrace (torusBoundarySteps d N A.vertices)
              (torusGhostClusterBlockOpenDoubleReachTrace A)))) ≤
      ∑ n ∈ Finset.range ((cubicTorusVertexFinset d N hN).card + 1),
        finiteBernoulliProbabilityFamily (torusGhostCoordinateFinset d N hN)
          (torusGhostCoordinateDensity p γ)
          (finsetUnionTrace
            (Finset.univ : Finset (CubicTorusBondAnimal d N n hN))
            (fun A ↦ finsetUnionTrace (torusBoundarySteps d N A.vertices)
              (torusGhostClusterBlockOpenDoubleReachTrace A))) := by
      exact finiteBernoulliProbabilityFamily_finsetUnionTrace_le_sum
        (torusGhostCoordinateDensity_nonneg p γ)
        (torusGhostCoordinateDensity_le_one p γ) _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro n hn
      calc
        finiteBernoulliProbabilityFamily (torusGhostCoordinateFinset d N hN)
            (torusGhostCoordinateDensity p γ)
            (finsetUnionTrace
              (Finset.univ : Finset (CubicTorusBondAnimal d N n hN))
              (fun A ↦ finsetUnionTrace (torusBoundarySteps d N A.vertices)
                (torusGhostClusterBlockOpenDoubleReachTrace A))) ≤
          ∑ A : CubicTorusBondAnimal d N n hN,
            finiteBernoulliProbabilityFamily (torusGhostCoordinateFinset d N hN)
              (torusGhostCoordinateDensity p γ)
              (finsetUnionTrace (torusBoundarySteps d N A.vertices)
                (torusGhostClusterBlockOpenDoubleReachTrace A)) := by
            simpa using finiteBernoulliProbabilityFamily_finsetUnionTrace_le_sum
              (E := torusGhostCoordinateFinset d N hN)
              (q := torusGhostCoordinateDensity p γ)
              (torusGhostCoordinateDensity_nonneg p γ)
              (torusGhostCoordinateDensity_le_one p γ)
              (Finset.univ : Finset (CubicTorusBondAnimal d N n hN))
              (fun A ↦ finsetUnionTrace (torusBoundarySteps d N A.vertices)
                (torusGhostClusterBlockOpenDoubleReachTrace A))
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro A hA
          exact finiteBernoulliProbabilityFamily_finsetUnionTrace_le_sum
            (torusGhostCoordinateDensity_nonneg p γ)
            (torusGhostCoordinateDensity_le_one p γ) _ _

theorem sum_torusBoundaryStepsForEdge_weighted
    (hN : 2 ≤ N) (S : Finset (CubicTorus d N))
    (F : (CubicTorus d N × CubicDirection d) → ℝ) :
    (∑ e ∈ cubicTorusEdgeFinset d N hN,
      ∑ b ∈ torusBoundaryStepsForEdge hN S e, F b) =
      ∑ b ∈ torusBoundarySteps d N S, F b := by
  simp_rw [torusBoundaryStepsForEdge, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  let e := cubicTorusStepEdge hN b.1 b.2
  rw [Finset.sum_eq_single e]
  · simp [e]
  · intro f hf hfe
    simp [e, hfe.symm]
  · intro heNot
    exact (heNot (mem_cubicTorusEdgeFinset hN e)).elim

theorem sum_clusterBlockReach_eq_sum_closedPivotal
    (d N : ℕ) (hN : 2 ≤ N) (p γ : I) :
    (∑ n ∈ Finset.range ((cubicTorusVertexFinset d N hN).card + 1),
      ∑ A : CubicTorusBondAnimal d N n hN,
        ∑ b ∈ torusBoundarySteps d N A.vertices,
          finiteBernoulliProbabilityFamily
            (torusGhostCoordinateFinset d N hN)
            (torusGhostCoordinateDensity p γ)
            (torusGhostClusterBlockReachTrace A b)) =
      ∑ e ∈ cubicTorusEdgeFinset d N hN,
        finiteBernoulliProbabilityFamily
          (torusGhostCoordinateFinset d N hN)
          (torusGhostCoordinateDensity p γ)
          (torusGhostClosedPivotalJointTrace d N e) := by
  calc
    (∑ n ∈ Finset.range ((cubicTorusVertexFinset d N hN).card + 1),
      ∑ A : CubicTorusBondAnimal d N n hN,
        ∑ b ∈ torusBoundarySteps d N A.vertices,
          finiteBernoulliProbabilityFamily
            (torusGhostCoordinateFinset d N hN)
            (torusGhostCoordinateDensity p γ)
            (torusGhostClusterBlockReachTrace A b)) =
      ∑ n ∈ Finset.range ((cubicTorusVertexFinset d N hN).card + 1),
        ∑ A : CubicTorusBondAnimal d N n hN,
          ∑ e ∈ cubicTorusEdgeFinset d N hN,
            ∑ b ∈ torusBoundaryStepsForEdge hN A.vertices e,
              finiteBernoulliProbabilityFamily
                (torusGhostCoordinateFinset d N hN)
                (torusGhostCoordinateDensity p γ)
                (torusGhostClusterBlockReachTrace A b) := by
        apply Finset.sum_congr rfl
        intro n hn
        apply Finset.sum_congr rfl
        intro A hA
        exact (sum_torusBoundaryStepsForEdge_weighted hN A.vertices
          (fun b ↦ finiteBernoulliProbabilityFamily
            (torusGhostCoordinateFinset d N hN)
            (torusGhostCoordinateDensity p γ)
            (torusGhostClusterBlockReachTrace A b))).symm
    _ = ∑ e ∈ cubicTorusEdgeFinset d N hN,
        ∑ n ∈ Finset.range ((cubicTorusVertexFinset d N hN).card + 1),
          ∑ A : CubicTorusBondAnimal d N n hN,
            ∑ b ∈ torusBoundaryStepsForEdge hN A.vertices e,
              finiteBernoulliProbabilityFamily
                (torusGhostCoordinateFinset d N hN)
                (torusGhostCoordinateDensity p γ)
                (torusGhostClusterBlockReachTrace A b) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro e he
      rw [← finiteBernoulliProbabilityFamily_clusterBlockReachAllForEdge_eq_sum
        d N hN e p γ,
        torusGhostClusterBlockReachAllForEdge_eq_closedPivotal]

/-- Equation (5.74) on the finite torus: the exceptional two-green event is controlled by
`p θ_N ∂ₚθ_N`. -/
theorem finiteBernoulliProbabilityFamily_torusGhostExceptionalTrace_le
    (d N : ℕ) (hN : 2 ≤ N) (p γ : I) (hp1 : (p : ℝ) < 1) :
    finiteBernoulliProbabilityFamily (torusGhostCoordinateFinset d N hN)
        (torusGhostCoordinateDensity p γ)
        (torusGhostExceptionalTrace d N hN) ≤
      (p : ℝ) * torusGhostThetaPolynomial d N hN p γ *
        torusGhostThetaPDerivative d N hN p γ := by
  let E := torusGhostCoordinateFinset d N hN
  let q : TorusGhostCoordinate d N → ℝ :=
    torusGhostCoordinateDensity (p : ℝ) (γ : ℝ)
  let O := torusGhostClusterBlockOpenDoubleReachAll d N hN
  let c := (p : ℝ) * torusGhostThetaPolynomial d N hN p γ
  let R := Finset.range ((cubicTorusVertexFinset d N hN).card + 1)
  have hexcOpen : finiteBernoulliProbabilityFamily E q
      (torusGhostExceptionalTrace d N hN) ≤
      finiteBernoulliProbabilityFamily E q O := by
    apply finiteBernoulliProbabilityFamily_mono
    · exact torusGhostCoordinateDensity_nonneg p γ
    · exact torusGhostCoordinateDensity_le_one p γ
    · exact torusGhostExceptionalTrace_subset_openDoubleClusterBlocks d N hN
  have hopenSum := finiteBernoulliProbabilityFamily_openDoubleAll_le_sum
    d N hN p γ
  have hqnonneg : 0 ≤ 1 - (p : ℝ) := sub_nonneg.mpr p.2.2
  have hscaled := mul_le_mul_of_nonneg_left hopenSum hqnonneg
  have hblocks :
      (1 - (p : ℝ)) * finiteBernoulliProbabilityFamily E q O ≤
        c * (∑ n ∈ R, ∑ A : CubicTorusBondAnimal d N n hN,
          ∑ b ∈ torusBoundarySteps d N A.vertices,
            finiteBernoulliProbabilityFamily E q
              (torusGhostClusterBlockReachTrace A b)) := by
    calc
      (1 - (p : ℝ)) * finiteBernoulliProbabilityFamily E q O ≤
          (1 - (p : ℝ)) *
            (∑ n ∈ R, ∑ A : CubicTorusBondAnimal d N n hN,
              ∑ b ∈ torusBoundarySteps d N A.vertices,
                finiteBernoulliProbabilityFamily E q
                  (torusGhostClusterBlockOpenDoubleReachTrace A b)) := by
            simpa [E, q, O, R] using hscaled
      _ = ∑ n ∈ R, ∑ A : CubicTorusBondAnimal d N n hN,
            ∑ b ∈ torusBoundarySteps d N A.vertices,
              (1 - (p : ℝ)) * finiteBernoulliProbabilityFamily E q
                (torusGhostClusterBlockOpenDoubleReachTrace A b) := by
          simp_rw [Finset.mul_sum]
      _ ≤ ∑ n ∈ R, ∑ A : CubicTorusBondAnimal d N n hN,
            ∑ b ∈ torusBoundarySteps d N A.vertices,
              c * finiteBernoulliProbabilityFamily E q
                (torusGhostClusterBlockReachTrace A b) := by
          apply Finset.sum_le_sum
          intro n hn
          apply Finset.sum_le_sum
          intro A hA
          apply Finset.sum_le_sum
          intro b hb
          simpa [E, q, c] using
            one_sub_mul_probability_openDouble_le A b hb p γ
      _ = c * (∑ n ∈ R, ∑ A : CubicTorusBondAnimal d N n hN,
          ∑ b ∈ torusBoundarySteps d N A.vertices,
            finiteBernoulliProbabilityFamily E q
              (torusGhostClusterBlockReachTrace A b)) := by
          simp_rw [Finset.mul_sum]
  have htotal := sum_clusterBlockReach_eq_sum_closedPivotal d N hN p γ
  have hclosed := one_sub_mul_torusGhostThetaPDerivative_eq_sum_closedPivotal
    d N hN p γ
  have hscaledFinal :
      (1 - (p : ℝ)) * finiteBernoulliProbabilityFamily E q O ≤
        (1 - (p : ℝ)) *
          (c * torusGhostThetaPDerivative d N hN p γ) := by
    calc
      (1 - (p : ℝ)) * finiteBernoulliProbabilityFamily E q O ≤
          c * (∑ n ∈ R, ∑ A : CubicTorusBondAnimal d N n hN,
            ∑ b ∈ torusBoundarySteps d N A.vertices,
              finiteBernoulliProbabilityFamily E q
                (torusGhostClusterBlockReachTrace A b)) := hblocks
      _ = c * (∑ e ∈ cubicTorusEdgeFinset d N hN,
          finiteBernoulliProbabilityFamily E q
            (torusGhostClosedPivotalJointTrace d N e)) := by
          rw [htotal]
      _ = c * ((1 - (p : ℝ)) *
          torusGhostThetaPDerivative d N hN p γ) := by
          rw [hclosed]
      _ = (1 - (p : ℝ)) *
          (c * torusGhostThetaPDerivative d N hN p γ) := by ring
  have hqpos : 0 < 1 - (p : ℝ) := sub_pos.mpr hp1
  have hopen : finiteBernoulliProbabilityFamily E q O ≤
      c * torusGhostThetaPDerivative d N hN p γ := by
    nlinarith
  exact hexcOpen.trans (by simpa [E, q, O, c] using hopen)

/-- Finite-volume Lemma 5.53. -/
theorem torusGhostTheta_le_differential
    (d N : ℕ) (hN : 2 ≤ N) (p γ : I)
    (hp1 : (p : ℝ) < 1) (hγ0 : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1) :
    torusGhostThetaPolynomial d N hN p γ ≤
      (γ : ℝ) * torusGhostThetaGammaDerivative d N hN p γ +
        torusGhostThetaPolynomial d N hN p γ ^ 2 +
          (p : ℝ) * torusGhostThetaPolynomial d N hN p γ *
            torusGhostThetaPDerivative d N hN p γ := by
  have hbase := torusGhostThetaPolynomial_le_gammaDerivative_add_sq_add_exceptional
    d N hN p γ hγ0 hγ1
  have hexc := finiteBernoulliProbabilityFamily_torusGhostExceptionalTrace_le
    d N hN p γ hp1
  linarith

end

end Percolation
