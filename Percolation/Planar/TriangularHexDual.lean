import Percolation.Planar.Inhomogeneous

/-!
# The hexagonal dual of the triangular lattice

The triangular lattice is represented in square coordinates, with the north-east diagonal in
each unit square.  Its triangular faces come in two orientations.  We index a face by an anchor
in `Z^2` and a Boolean orientation; the three neighbors of a face are obtained by toggling the
orientation and applying one of three explicit anchor shifts.

This coordinate model is intended for the standard-only Peierls proof used by
`TheoremsForExperiment`.  In particular, the direction label is retained: after the first step a
non-backtracking hexagonal walk has only two choices, and six consecutive turns in one direction
close a hexagon.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory SimpleGraph
open scoped Sym2 unitInterval

/-- A triangular face, represented by its square-coordinate anchor and its orientation.
`false` is the north-east (up) triangle and `true` is the south-west (down) triangle. -/
abbrev TriangularHexVertex := SquareVertex × Bool

/-- The three unoriented directions at a hexagonal-dual vertex.  The same direction label takes
a face to its neighbor and takes that neighbor back to the original face. -/
def triangularHexNeighbor (x : TriangularHexVertex) (k : Fin 3) :
    TriangularHexVertex :=
  if x.2 then
    if k = 0 then (x.1, false)
    else if k = 1 then (squareVertex (x.1 0) (x.1 1 + 1), false)
    else (squareVertex (x.1 0 - 1) (x.1 1), false)
  else
    if k = 0 then (x.1, true)
    else if k = 1 then (squareVertex (x.1 0) (x.1 1 - 1), true)
    else (squareVertex (x.1 0 + 1) (x.1 1), true)

@[simp]
theorem triangularHexNeighbor_orientation (x : TriangularHexVertex) (k : Fin 3) :
    (triangularHexNeighbor x k).2 = !x.2 := by
  rcases x with ⟨x, b⟩
  fin_cases k <;> cases b <;> simp [triangularHexNeighbor]

@[simp]
theorem triangularHexNeighbor_ne (x : TriangularHexVertex) (k : Fin 3) :
    triangularHexNeighbor x k ≠ x := by
  intro h
  have := congrArg Prod.snd h
  simp at this

@[simp]
theorem triangularHexNeighbor_involutive
    (x : TriangularHexVertex) (k : Fin 3) :
    triangularHexNeighbor (triangularHexNeighbor x k) k = x := by
  rcases x with ⟨x, b⟩
  fin_cases k <;> cases b <;> apply Prod.ext
  all_goals
    first
    | · ext i
        fin_cases i <;> simp [triangularHexNeighbor, squareVertex]
    | · simp [triangularHexNeighbor]

theorem triangularHexNeighbor_injective
    (x : TriangularHexVertex) : Function.Injective (triangularHexNeighbor x) := by
  intro i j hij
  rcases x with ⟨x, b⟩
  fin_cases i <;> fin_cases j <;> cases b
  all_goals try rfl
  all_goals
    exfalso
    have h0 := congrFun (congrArg Prod.fst hij) (0 : Fin 2)
    have h1 := congrFun (congrArg Prod.fst hij) (1 : Fin 2)
    simp [triangularHexNeighbor, squareVertex] at h0 h1 <;> omega

/-- The hexagonal dual graph. -/
def triangularHexGraph : SimpleGraph TriangularHexVertex :=
  SimpleGraph.fromRel fun x y => ∃ k : Fin 3, y = triangularHexNeighbor x k

@[simp]
theorem triangularHexGraph_adj_iff
    (x y : TriangularHexVertex) :
    triangularHexGraph.Adj x y ↔ ∃ k : Fin 3, y = triangularHexNeighbor x k := by
  rw [triangularHexGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨_hne, ⟨k, rfl⟩ | ⟨k, hk⟩⟩
    · exact ⟨k, rfl⟩
    · refine ⟨k, ?_⟩
      simpa only [hk, triangularHexNeighbor_involutive]
  · rintro ⟨k, rfl⟩
    exact ⟨(triangularHexNeighbor_ne x k).symm, Or.inl ⟨k, rfl⟩⟩

theorem triangularHexGraph_adj_neighbor
    (x : TriangularHexVertex) (k : Fin 3) :
    triangularHexGraph.Adj x (triangularHexNeighbor x k) :=
  (triangularHexGraph_adj_iff _ _).2 ⟨k, rfl⟩

theorem triangularHexGraph_neighborSet_eq_range
    (x : TriangularHexVertex) :
    triangularHexGraph.neighborSet x = Set.range (triangularHexNeighbor x) := by
  ext y
  rw [SimpleGraph.mem_neighborSet, triangularHexGraph_adj_iff, Set.mem_range]
  constructor <;> rintro ⟨k, hk⟩
  · exact ⟨k, hk.symm⟩
  · exact ⟨k, hk.symm⟩

/-- Direction labels identify the three neighbors of a hexagonal face. -/
noncomputable def triangularHexNeighborEquiv (x : TriangularHexVertex) :
    Fin 3 ≃ triangularHexGraph.neighborSet x where
  toFun k := ⟨triangularHexNeighbor x k, triangularHexGraph_adj_neighbor x k⟩
  invFun y := Classical.choose ((triangularHexGraph_adj_iff x y).mp y.2)
  left_inv k := by
    apply triangularHexNeighbor_injective x
    exact (Classical.choose_spec
      ((triangularHexGraph_adj_iff x
        (triangularHexNeighbor x k)).mp (triangularHexGraph_adj_neighbor x k))).symm
  right_inv y := by
    apply Subtype.ext
    exact (Classical.choose_spec ((triangularHexGraph_adj_iff x y).mp y.2)).symm

noncomputable instance triangularHexGraphNeighborSetFintype
    (x : TriangularHexVertex) : Fintype (triangularHexGraph.neighborSet x) :=
  Fintype.ofEquiv (Fin 3) (triangularHexNeighborEquiv x)

noncomputable instance triangularHexGraphLocallyFinite : triangularHexGraph.LocallyFinite :=
  fun x => triangularHexGraphNeighborSetFintype x

@[simp]
theorem triangularHexGraph_degree (x : TriangularHexVertex) :
    triangularHexGraph.degree x = 3 := by
  classical
  rw [← triangularHexGraph.card_neighborSet_eq_degree]
  exact Fintype.card_congr (triangularHexNeighborEquiv x)

/-! ### The crossed triangular bond -/

/-- A horizontal or vertical square-lattice step, regarded as a triangular-lattice bond. -/
def triangularCubicStepEdge (x : SquareVertex) (a : CubicDirection 2) :
    TriangularEdge := by
  let y := cubicStepFrom x a
  refine ⟨s(x, y), ?_⟩
  have hxy := cubicGraph_adj_stepFrom x a
  rw [cubicGraph, SimpleGraph.fromRel_adj] at hxy
  rw [SimpleGraph.mem_edgeSet, triangularGraph, SimpleGraph.fromRel_adj]
  exact ⟨hxy.1, hxy.2.imp (fun h => Or.inl h) (fun h => Or.inl h)⟩

/-- The north-east diagonal through an anchor, regarded as a triangular-lattice bond. -/
def triangularDiagonalEdge (x : SquareVertex) : TriangularEdge := by
  let y : SquareVertex := fun i => x i + 1
  refine ⟨s(x, y), ?_⟩
  rw [SimpleGraph.mem_edgeSet, triangularGraph, SimpleGraph.fromRel_adj]
  refine ⟨?_, Or.inl (Or.inr rfl)⟩
  intro h
  have h0 := congrFun h (0 : Fin 2)
  simp [y] at h0

/-- The primal triangular bond crossed by a directed hexagonal-dual step. -/
def triangularHexCrossedEdge (x : TriangularHexVertex) (k : Fin 3) :
    TriangularEdge :=
  if x.2 then
    if k = 0 then triangularDiagonalEdge x.1
    else if k = 1 then
        triangularCubicStepEdge (squareVertex (x.1 0) (x.1 1 + 1))
          ((0 : Fin 2), true)
    else triangularCubicStepEdge x.1 ((1 : Fin 2), true)
  else
    if k = 0 then triangularDiagonalEdge x.1
    else if k = 1 then triangularCubicStepEdge x.1 ((0 : Fin 2), true)
    else
        triangularCubicStepEdge (squareVertex (x.1 0 + 1) (x.1 1))
          ((1 : Fin 2), true)

@[simp]
theorem triangularHexCrossedEdge_neighbor
    (x : TriangularHexVertex) (k : Fin 3) :
    triangularHexCrossedEdge (triangularHexNeighbor x k) k =
      triangularHexCrossedEdge x k := by
  rcases x with ⟨x, b⟩
  fin_cases k <;> cases b <;>
    apply Subtype.ext <;>
    simp [triangularHexNeighbor, triangularHexCrossedEdge,
      triangularCubicStepEdge, triangularDiagonalEdge, cubicStepFrom,
      cubicDirectionIncrement, squareVertex, Sym2.eq_iff]

/-- The unoriented hexagonal edge traversed by a directed neighbor step. -/
def triangularHexDartEdge (x : TriangularHexVertex) (k : Fin 3) :
    Sym2 TriangularHexVertex :=
  s(x, triangularHexNeighbor x k)

theorem triangularHexDartEdge_mem_edgeSet
    (x : TriangularHexVertex) (k : Fin 3) :
    triangularHexDartEdge x k ∈ triangularHexGraph.edgeSet := by
  change triangularHexGraph.Adj x (triangularHexNeighbor x k)
  exact triangularHexGraph_adj_neighbor x k

@[simp]
theorem triangularHexDartEdge_neighbor
    (x : TriangularHexVertex) (k : Fin 3) :
    triangularHexDartEdge (triangularHexNeighbor x k) k =
      triangularHexDartEdge x k := by
  simp only [triangularHexDartEdge, triangularHexNeighbor_involutive, Sym2.eq_swap]

/-- A hexagonal edge together with the direction obtained from its two canonical endpoints. -/
noncomputable def triangularHexEdgeDirection (e : triangularHexGraph.edgeSet) : Fin 3 :=
  Classical.choose ((triangularHexGraph_adj_iff e.1.out.1 e.1.out.2).mp <| by
    rw [← SimpleGraph.mem_edgeSet]
    simpa only [e.1.out_eq] using e.2)

theorem triangularHexEdgeDirection_spec (e : triangularHexGraph.edgeSet) :
    e.1.out.2 = triangularHexNeighbor e.1.out.1 (triangularHexEdgeDirection e) :=
  Classical.choose_spec ((triangularHexGraph_adj_iff e.1.out.1 e.1.out.2).mp <| by
    rw [← SimpleGraph.mem_edgeSet]
    simpa only [e.1.out_eq] using e.2)

/-- The primal triangular bond crossed by a hexagonal-dual edge. -/
noncomputable def triangularHexEdgeCrossed (e : triangularHexGraph.edgeSet) :
    TriangularEdge :=
  triangularHexCrossedEdge e.1.out.1 (triangularHexEdgeDirection e)

theorem triangularHexEdgeCrossed_dart
    (x : TriangularHexVertex) (k : Fin 3) :
    triangularHexEdgeCrossed
        ⟨triangularHexDartEdge x k, triangularHexDartEdge_mem_edgeSet x k⟩ =
      triangularHexCrossedEdge x k := by
  let e : triangularHexGraph.edgeSet :=
    ⟨triangularHexDartEdge x k, triangularHexDartEdge_mem_edgeSet x k⟩
  have hout : s(e.1.out.1, e.1.out.2) =
      s(x, triangularHexNeighbor x k) := by
    simpa only [e, triangularHexDartEdge] using e.1.out_eq
  rcases Sym2.eq_iff.mp hout with hsame | hswap
  · have ha : e.1.out.1 = x := hsame.1
    have hb : e.1.out.2 = triangularHexNeighbor x k := hsame.2
    have hdir : triangularHexEdgeDirection e = k := by
      apply triangularHexNeighbor_injective e.1.out.1
      calc
        triangularHexNeighbor e.1.out.1 (triangularHexEdgeDirection e) =
            e.1.out.2 := (triangularHexEdgeDirection_spec e).symm
        _ = triangularHexNeighbor x k := hb
        _ = triangularHexNeighbor e.1.out.1 k := by rw [ha]
    unfold triangularHexEdgeCrossed
    rw [ha, hdir]
  · have ha : e.1.out.1 = triangularHexNeighbor x k := hswap.1
    have hb : e.1.out.2 = x := hswap.2
    have hdir : triangularHexEdgeDirection e = k := by
      apply triangularHexNeighbor_injective (triangularHexNeighbor x k)
      calc
        triangularHexNeighbor (triangularHexNeighbor x k)
            (triangularHexEdgeDirection e) =
            triangularHexNeighbor e.1.out.1 (triangularHexEdgeDirection e) := by rw [ha]
        _ = e.1.out.2 := (triangularHexEdgeDirection_spec e).symm
        _ = x := hb
        _ = triangularHexNeighbor (triangularHexNeighbor x k) k := by simp
    unfold triangularHexEdgeCrossed
    rw [ha, hdir, triangularHexCrossedEdge_neighbor]

/-! ### Recovering the dual edge from the primal bond -/

/-- Coordinate-level dual edge of an unordered pair of primal vertices.  On an actual
triangular bond, the three branches are respectively its horizontal, vertical, and north-east
diagonal cases. -/
def triangularHexDualPair (u v : SquareVertex) : Sym2 TriangularHexVertex :=
  let i := min (u 0) (v 0)
  let j := min (u 1) (v 1)
  if u 1 = v 1 then
    s((squareVertex i j, false), (squareVertex i (j - 1), true))
  else if u 0 = v 0 then
    s((squareVertex (i - 1) j, false), (squareVertex i j, true))
  else
    s((squareVertex i j, false), (squareVertex i j, true))

theorem triangularHexDualPair_comm (u v : SquareVertex) :
    triangularHexDualPair u v = triangularHexDualPair v u := by
  simp only [triangularHexDualPair, min_comm, eq_comm]

/-- The hexagonal dual edge determined by a primal unordered pair. -/
def triangularHexDualOfPrimal : Sym2 SquareVertex → Sym2 TriangularHexVertex :=
  Sym2.lift ⟨triangularHexDualPair, triangularHexDualPair_comm⟩

@[simp]
theorem triangularHexDualOfPrimal_mk (u v : SquareVertex) :
    triangularHexDualOfPrimal s(u, v) = triangularHexDualPair u v :=
  rfl

@[simp]
theorem triangularHexDualOfPrimal_crossed
    (x : TriangularHexVertex) (k : Fin 3) :
    triangularHexDualOfPrimal (triangularHexCrossedEdge x k).1 =
      triangularHexDartEdge x k := by
  rcases x with ⟨x, b⟩
  fin_cases k <;> cases b <;>
    simp [triangularHexCrossedEdge, triangularCubicStepEdge,
      triangularDiagonalEdge, triangularHexDualOfPrimal,
      triangularHexDualPair, triangularHexDartEdge, triangularHexNeighbor,
      cubicStepFrom, cubicDirectionIncrement, squareVertex, Sym2.eq_iff]

theorem triangularHexDartEdge_eq_of_crossedEdge_eq
    {x y : TriangularHexVertex} {k l : Fin 3}
    (h : triangularHexCrossedEdge x k = triangularHexCrossedEdge y l) :
    triangularHexDartEdge x k = triangularHexDartEdge y l := by
  have hval := congrArg (fun e : TriangularEdge => (e.1 : Sym2 SquareVertex)) h
  simpa only [← triangularHexDualOfPrimal_crossed] using
    congrArg triangularHexDualOfPrimal hval

theorem triangularHexEdgeCrossed_injective :
    Function.Injective triangularHexEdgeCrossed := by
  intro e f hef
  apply Subtype.ext
  have heDart : e.1 = triangularHexDartEdge e.1.out.1
      (triangularHexEdgeDirection e) := by
    rw [triangularHexDartEdge, ← triangularHexEdgeDirection_spec e]
    exact e.1.out_eq.symm
  have hfDart : f.1 = triangularHexDartEdge f.1.out.1
      (triangularHexEdgeDirection f) := by
    rw [triangularHexDartEdge, ← triangularHexEdgeDirection_spec f]
    exact f.1.out_eq.symm
  rw [heDart, hfDart]
  exact triangularHexDartEdge_eq_of_crossedEdge_eq hef

/-- The crossed-primal-bond map as an embedding. -/
noncomputable def triangularHexEdgeCrossedEmbedding :
    triangularHexGraph.edgeSet ↪ TriangularEdge :=
  ⟨triangularHexEdgeCrossed, triangularHexEdgeCrossed_injective⟩

/-! ### Finite dual walks and their crossed bonds -/

/-- The hexagonal-dual edges traversed by a walk, with membership in the dual edge set
recorded in the subtype. -/
noncomputable def triangularHexWalkEdgeList {u v : TriangularHexVertex}
    (w : triangularHexGraph.Walk u v) : List triangularHexGraph.edgeSet :=
  w.edges.attach.map fun e ↦ ⟨e.1, w.edges_subset_edgeSet e.2⟩

/-- The finite set of hexagonal-dual edges traversed by a walk. -/
noncomputable def triangularHexWalkEdgeFinset {u v : TriangularHexVertex}
    (w : triangularHexGraph.Walk u v) : Finset triangularHexGraph.edgeSet :=
  (triangularHexWalkEdgeList w).toFinset

@[simp]
theorem mem_triangularHexWalkEdgeFinset_iff {u v : TriangularHexVertex}
    (w : triangularHexGraph.Walk u v) (e : triangularHexGraph.edgeSet) :
    e ∈ triangularHexWalkEdgeFinset w ↔
      (e.1 : Sym2 TriangularHexVertex) ∈ w.edges := by
  classical
  constructor
  · intro he
    rw [triangularHexWalkEdgeFinset, List.mem_toFinset] at he
    rcases List.mem_map.mp he with ⟨a, _ha, hae⟩
    have hval : a.1 = (e.1 : Sym2 TriangularHexVertex) :=
      congrArg (fun f : triangularHexGraph.edgeSet ↦
        (f.1 : Sym2 TriangularHexVertex)) hae
    exact hval ▸ a.2
  · intro he
    rw [triangularHexWalkEdgeFinset, List.mem_toFinset]
    exact List.mem_map.mpr
      ⟨⟨e.1, he⟩, List.mem_attach _ _, Subtype.ext rfl⟩

theorem triangularHexWalkEdgeList_nodup_of_isTrail
    {u v : TriangularHexVertex} {w : triangularHexGraph.Walk u v}
    (hw : w.IsTrail) : (triangularHexWalkEdgeList w).Nodup := by
  classical
  unfold triangularHexWalkEdgeList
  exact hw.edges_nodup.attach.map (by
    intro a b hab
    exact Subtype.ext (congrArg
      (fun e : triangularHexGraph.edgeSet ↦
        (e.1 : Sym2 TriangularHexVertex)) hab))

/-- A dual trail crosses exactly one distinct primal triangular bond per step. -/
theorem triangularHexWalkEdgeFinset_card_of_isTrail
    {u v : TriangularHexVertex} {w : triangularHexGraph.Walk u v}
    (hw : w.IsTrail) : (triangularHexWalkEdgeFinset w).card = w.length := by
  classical
  rw [triangularHexWalkEdgeFinset,
    List.toFinset_card_of_nodup
      (triangularHexWalkEdgeList_nodup_of_isTrail hw)]
  simp [triangularHexWalkEdgeList, SimpleGraph.Walk.length_edges]

/-- The primal triangular bonds crossed by a finite hexagonal-dual walk. -/
noncomputable def triangularHexWalkCrossedFinset
    {u v : TriangularHexVertex} (w : triangularHexGraph.Walk u v) :
    Finset TriangularEdge :=
  (triangularHexWalkEdgeFinset w).map triangularHexEdgeCrossedEmbedding

theorem triangularHexWalkCrossedFinset_card_of_isTrail
    {u v : TriangularHexVertex} {w : triangularHexGraph.Walk u v}
    (hw : w.IsTrail) : (triangularHexWalkCrossedFinset w).card = w.length := by
  rw [triangularHexWalkCrossedFinset, Finset.card_map,
    triangularHexWalkEdgeFinset_card_of_isTrail hw]

/-- Event that every primal bond crossed by a prescribed dual walk is closed. -/
def triangularHexWalkClosedEvent {u v : TriangularHexVertex}
    (w : triangularHexGraph.Walk u v) : Set TriangularConfiguration :=
  {omega | Disjoint (triangularHexWalkCrossedFinset w : Set TriangularEdge) omega}

theorem measurableSet_triangularHexWalkClosedEvent
    {u v : TriangularHexVertex} (w : triangularHexGraph.Walk u v) :
    MeasurableSet (triangularHexWalkClosedEvent w) := by
  exact measurableSet_disjoint_finset (triangularHexWalkCrossedFinset w)

private theorem inhomogeneousTriangularBondMeasure_self_eq_setBernoulli_hex
    (p : I) :
    inhomogeneousTriangularBondMeasure p p p =
      setBernoulli (Set.univ : Set TriangularEdge) p := by
  rw [inhomogeneousTriangularBondMeasure]
  have hdensity : inhomogeneousTriangularEdgeDensity p p p =
      fun _ : TriangularEdge ↦ p := by
    funext e
    simp [inhomogeneousTriangularEdgeDensity]
  rw [hdensity, inhomogeneousSetBernoulli_const]

/-- Exact probability of a prescribed closed dual trail. -/
theorem inhomogeneousTriangularBondMeasure_real_triangularHexWalkClosedEvent
    (p : I) {u v : TriangularHexVertex} (w : triangularHexGraph.Walk u v)
    (hw : w.IsTrail) :
    (inhomogeneousTriangularBondMeasure p p p).real
        (triangularHexWalkClosedEvent w) =
      (1 - (p : ℝ)) ^ w.length := by
  rw [inhomogeneousTriangularBondMeasure_self_eq_setBernoulli_hex]
  unfold triangularHexWalkClosedEvent
  rw [setBernoulli_real_disjoint_finset_univ,
    triangularHexWalkCrossedFinset_card_of_isTrail hw]

end Percolation
