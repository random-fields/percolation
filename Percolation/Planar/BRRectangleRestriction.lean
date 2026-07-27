import Percolation.Core.CubicWalkLevel
import Percolation.Planar.RSWEvents

/-!
# Restricting boundary-free rectangle crossings in the horizontal direction

A crossing of a wider rectangle can be stopped at its first visit to a nearer vertical side.
For the boundary-free event one must additionally check that the stopped walk does not acquire
an edge whose two endpoints lie on the new boundary.  This is true once the shorter width is at
least two; at width one the statement is genuinely false because the single horizontal bond has
both endpoints on the boundary.
-/

namespace Percolation

open SimpleGraph
open scoped Sym2

noncomputable section

/-- A first-hit prefix at a coordinate level.  Besides being an edge prefix, it contains no edge
whose two endpoints both lie on the target level. -/
private theorem exists_squareWalk_firstHitPrefix_to_level
    {u v : SquareVertex} (w : squareGraph.Walk u v) (i : Fin 2) (a : ℤ)
    (hu : u i ≤ a) (hv : a ≤ v i) :
    ∃ z : SquareVertex, ∃ q : squareGraph.Walk u z,
      z i = a ∧
        (∀ x ∈ q.support, x i ≤ a) ∧
        (∀ x ∈ q.support, x ∈ w.support) ∧
        q.edges <+: w.edges ∧
        ∀ e ∈ q.edges, ¬(∀ x ∈ e, x i = a) := by
  induction w with
  | nil =>
      refine ⟨_, .nil, ?_, ?_, ?_, ?_, ?_⟩
      · omega
      · simpa using hu
      · simp
      · exact List.prefix_rfl
      · simp
  | @cons u₀ u₁ v₀ hu₀u₁ p ih =>
      by_cases hlevel : u₀ i = a
      · refine ⟨u₀, .nil, hlevel, ?_, ?_, List.nil_prefix, ?_⟩
        · simp [hlevel]
        · simp
        · simp
      · have hlt : u₀ i < a := lt_of_le_of_ne hu hlevel
        obtain ⟨dir, hstep⟩ :=
          (cubicGraph_adj_iff_exists_stepFrom u₀ u₁).mp hu₀u₁
        have hstepUpper : u₁ i ≤ u₀ i + 1 := by
          simpa [hstep] using cubicStepFrom_coord_le_add_one u₀ dir i
        have hu₁ : u₁ i ≤ a := by omega
        obtain ⟨z, q, hz, hqSide, hqSupport, hqPrefix, hqLevel⟩ := ih hu₁ hv
        refine ⟨z, q.cons hu₀u₁, hz, ?_, ?_, ?_, ?_⟩
        · intro x hx
          simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact hu
          · exact hqSide x hx
        · intro x hx
          simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hx ⊢
          rcases hx with rfl | hx
          · exact Or.inl rfl
          · exact Or.inr (hqSupport x hx)
        · simpa only [SimpleGraph.Walk.edges_cons] using
            (List.cons_prefix_cons.mpr ⟨rfl, hqPrefix⟩)
        · intro e he hends
          simp only [SimpleGraph.Walk.edges_cons, List.mem_cons] at he
          rcases he with rfl | he
          · exact (ne_of_lt hlt) (hends u₀ (by simp))
          · exact hqLevel e he hends

/-- For adjacent vertices in a rectangle of width at least two, if both lie on the shorter
rectangle's boundary, then either both already lie on the wider boundary or both lie on the new
right side. -/
private theorem boundary_pair_of_adjacent_of_le_width
    {m M n : ℕ} (hm : 2 ≤ m) (hmM : m ≤ M)
    {x y : SquareVertex} (hxy : squareGraph.Adj x y)
    (hxle : x 0 ≤ (m : ℤ)) (hyle : y 0 ≤ (m : ℤ))
    (hx : squareRectangleBoundaryVertex m n x)
    (hy : squareRectangleBoundaryVertex m n y) :
    (squareRectangleBoundaryVertex M n x ∧
        squareRectangleBoundaryVertex M n y) ∨
      (x 0 = (m : ℤ) ∧ y 0 = (m : ℤ)) := by
  rcases (cubicGraph_adj_iff_exists_stepFrom x y).mp hxy with ⟨⟨i, b⟩, rfl⟩
  fin_cases i <;> cases b <;>
    simp only [squareRectangleBoundaryVertex] at hx hy ⊢ <;>
    simp [cubicStepFrom, cubicDirectionIncrement] at hxle hyle hx hy ⊢ <;>
    omega

/-- A boundary-free left--right crossing of a wider rectangle restricts to one of every shorter
rectangle of width at least two and the same height. -/
theorem squareBoundaryFreeRectangleCrossingEvent_antitone_width
    {m M n : ℕ} (hm : 2 ≤ m) (hmM : m ≤ M) :
    squareBoundaryFreeRectangleCrossingEvent M n ⊆
      squareBoundaryFreeRectangleCrossingEvent m n := by
  classical
  intro omega homega
  simp only [squareBoundaryFreeRectangleCrossingEvent, Set.mem_iUnion] at homega ⊢
  rcases homega with ⟨u, hu, v, hv, w, hwOpen, hwEdges⟩
  have huCoords := mem_squareRectangleLeft_iff.mp hu
  have hvCoords := mem_squareRectangleRight_iff.mp hv
  obtain ⟨z, q, hz, hqSide, hqSupport, hqPrefix, hqNoLevelEdge⟩ :=
    exists_squareWalk_firstHitPrefix_to_level w (0 : Fin 2) (m : ℤ)
      (by omega) (by omega)
  have hvRect : v ∈ squareRectangleVertices M n :=
    (Finset.mem_filter.mp hv).1
  have hwRect : ∀ x ∈ w.support, x ∈ squareRectangleVertices M n := by
    intro x hx
    rw [SimpleGraph.Walk.mem_support_iff_exists_mem_edges] at hx
    rcases hx with rfl | ⟨e, he, hxe⟩
    · exact hvRect
    · let ee : SquareEdge := ⟨e, w.edges_subset_edgeSet he⟩
      exact endpoint_mem_squareRectangle_of_edge_mem
        (Finset.mem_filter.mp (hwEdges ((mem_walkEdgeFinset_iff w ee).mpr he))).1 hxe
  have hqRect : ∀ x ∈ q.support, x ∈ squareRectangleVertices m n := by
    intro x hx
    have hxWide := mem_squareRectangleVertices_iff.mp (hwRect x (hqSupport x hx))
    rw [mem_squareRectangleVertices_iff]
    have hxSide := hqSide x hx
    omega
  have hqRectangleEdges : walkEdgeFinset q ⊆ squareRectangleEdges m n :=
    walkEdgeFinset_subset_squareRectangleEdges_of_support q hqRect
  have hqBoundaryFree : walkEdgeFinset q ⊆ squareBoundaryFreeRectangleEdges m n := by
    intro e he
    rw [squareBoundaryFreeRectangleEdges, Finset.mem_filter]
    refine ⟨hqRectangleEdges he, ?_⟩
    intro hboundary
    have heq : (e : Sym2 SquareVertex) ∈ q.edges :=
      (mem_walkEdgeFinset_iff q e).mp he
    have hew : (e : Sym2 SquareVertex) ∈ w.edges := hqPrefix.subset heq
    let ew : SquareEdge := ⟨e, w.edges_subset_edgeSet hew⟩
    have heWide := Finset.mem_filter.mp
      (hwEdges ((mem_walkEdgeFinset_iff w ew).mpr hew))
    have heAdj : squareGraph.Adj e.1.out.1 e.1.out.2 := by
      have hemem := q.edges_subset_edgeSet heq
      rw [← e.1.out_eq, SimpleGraph.mem_edgeSet] at hemem
      exact hemem
    have hpair := boundary_pair_of_adjacent_of_le_width hm hmM heAdj
      (mem_squareRectangleVertices_iff.mp
        (hqRect e.1.out.1 (q.mem_support_of_mem_edges heq (Sym2.out_fst_mem _)))).2.1
      (mem_squareRectangleVertices_iff.mp
        (hqRect e.1.out.2 (q.mem_support_of_mem_edges heq (Sym2.out_snd_mem _)))).2.1
      hboundary.1 hboundary.2
    rcases hpair with hwide | hright
    · exact heWide.2 hwide
    · apply hqNoLevelEdge e heq
      intro x hx
      rw [← e.1.out_eq, Sym2.mem_iff] at hx
      exact hx.elim (fun h ↦ h ▸ hright.1) (fun h ↦ h ▸ hright.2)
  refine ⟨u, ?_, z, ?_, q, ?_, hqBoundaryFree⟩
  · rw [mem_squareRectangleLeft_iff]
    exact ⟨huCoords.1, huCoords.2.1, huCoords.2.2⟩
  · rw [mem_squareRectangleRight_iff]
    have hzRect := mem_squareRectangleVertices_iff.mp (hqRect z q.end_mem_support)
    exact ⟨hz, hzRect.2.2.1, hzRect.2.2.2⟩
  · intro e he
    exact hwOpen e (hqPrefix.subset he)

end

end Percolation
