import Percolation.Planar.CrossingMenger
import Percolation.Planar.RSWEvents
import Mathlib.Combinatorics.SimpleGraph.Walk.Counting

/-!
# Finite canonical rectangle-crossing candidates

This file supplies the finite path space on which the leftmost-crossing construction used in
Bollobás--Riordan, Lemma 6, will be defined.  The graph contains exactly the boundary-free
rectangle bonds used by the existing RSW events, so the candidate space does not introduce a
third crossing convention.
-/

namespace Percolation

open scoped unitInterval

/-- The finite rectangle graph containing exactly the boundary-free bonds used by RSW. -/
noncomputable def squareBoundaryFreeRectangleGraph (m n : ℕ) :
    SimpleGraph (SquareRectangleVertex m n) :=
  squareRectangleOpenGraph m n (squareBoundaryFreeRectangleEdges m n : Set SquareEdge)

/-- A self-avoiding left-to-right path in the finite boundary-free rectangle graph. -/
abbrev SquareBoundaryFreeCrossingPath (m n : ℕ) :=
  Σ x : {x // x ∈ squareRectangleLeftTerminals m n},
    Σ y : {y // y ∈ squareRectangleRightTerminals m n},
      (squareBoundaryFreeRectangleGraph m n).Path x.1 y.1

noncomputable instance (m n : ℕ) : Fintype (SquareBoundaryFreeCrossingPath m n) := by
  classical
  dsimp only [SquareBoundaryFreeCrossingPath]
  infer_instance

/-- The ambient square-lattice walk represented by a finite boundary-free crossing path. -/
noncomputable def SquareBoundaryFreeCrossingPath.ambientWalk {m n : ℕ}
    (P : SquareBoundaryFreeCrossingPath m n) :
    squareGraph.Walk P.1.1.1 P.2.1.1.1 :=
  ambientWalkOfSquareRectangleOpenWalk P.2.2.1

/-- A finite crossing candidate is open when all bonds of its ambient path are open. -/
def SquareBoundaryFreeCrossingPath.IsOpen {m n : ℕ}
    (P : SquareBoundaryFreeCrossingPath m n) (ω : EdgeConfiguration 2) : Prop :=
  walkIsOpen ω P.ambientWalk

/-- The finite set of bonds traversed by a boundary-free crossing candidate. -/
noncomputable def SquareBoundaryFreeCrossingPath.edgeFinset {m n : ℕ}
    (P : SquareBoundaryFreeCrossingPath m n) : Finset SquareEdge :=
  walkEdgeFinset P.ambientWalk

/-- The cylinder event on which a fixed crossing candidate is open. -/
def SquareBoundaryFreeCrossingPath.openEvent {m n : ℕ}
    (P : SquareBoundaryFreeCrossingPath m n) : Set (EdgeConfiguration 2) :=
  {ω | P.IsOpen ω}

theorem SquareBoundaryFreeCrossingPath.dependsOn_openEvent {m n : ℕ}
    (P : SquareBoundaryFreeCrossingPath m n) :
    DependsOn P.edgeFinset P.openEvent := by
  intro ω η hagree
  constructor
  · intro hω e he
    let ee : SquareEdge := ⟨e, P.ambientWalk.edges_subset_edgeSet he⟩
    exact (hagree ee ((mem_walkEdgeFinset_iff P.ambientWalk ee).mpr he)).mp (hω e he)
  · intro hη e he
    let ee : SquareEdge := ⟨e, P.ambientWalk.edges_subset_edgeSet he⟩
    exact (hagree ee ((mem_walkEdgeFinset_iff P.ambientWalk ee).mpr he)).mpr (hη e he)

/-- The finite set of all self-avoiding boundary-free left-to-right crossing candidates. -/
noncomputable def squareBoundaryFreeCrossingPaths (m n : ℕ) :
    Finset (SquareBoundaryFreeCrossingPath m n) :=
  Finset.univ

private theorem edges_liftedRectangleWalk_map
    {m n : ℕ} {ω : EdgeConfiguration 2}
    (C : OpenSquareRectangleCrossing m n ω) :
    (walkBetweenFinsetsOfOpenSquareRectangleCrossing C).walk.edges.map
        (Sym2.map Subtype.val) = C.walk.edges := by
  classical
  unfold walkBetweenFinsetsOfOpenSquareRectangleCrossing
  dsimp only
  let wOpen : (cubicOpenGraph 2 ω).Walk C.start C.finish :=
    C.walk.transfer (cubicOpenGraph 2 ω) (by
      intro e he
      let e' : SquareEdge := ⟨e, C.walk.edges_subset_edgeSet he⟩
      have hopen : e' ∈ ω := C.isOpen e' he
      let u := e.out.1
      let v := e.out.2
      have hadj : squareGraph.Adj u v := by
        rw [← SimpleGraph.mem_edgeSet]
        simpa [u, v, e.out_eq] using C.walk.edges_subset_edgeSet he
      rw [← e.out_eq, SimpleGraph.mem_edgeSet]
      apply cubicOpenGraph_adj.mpr
      refine ⟨hadj, ?_⟩
      have heq :
          (⟨s(u, v), (SimpleGraph.mem_edgeSet squareGraph).mpr hadj⟩ : SquareEdge) = e' := by
        apply Subtype.ext
        exact e.out_eq
      exact heq.symm ▸ hopen)
  have hsupport : ∀ z ∈ wOpen.support, z ∈ squareRectangleVertices m n := by
    intro z hz
    have hzC : z ∈ C.walk.support := by
      simpa [wOpen, SimpleGraph.Walk.support_transfer] using hz
    rw [SimpleGraph.Walk.mem_support_iff_exists_mem_edges] at hzC
    rcases hzC with rfl | ⟨e, he, hze⟩
    · exact (Finset.mem_filter.mp C.finish_mem).1
    · let ee : SquareEdge := ⟨e, C.walk.edges_subset_edgeSet he⟩
      exact endpoint_mem_squareRectangle_of_edge_mem
        (C.edges_subset ((mem_walkEdgeFinset_iff C.walk ee).mpr he)) hze
  let wInd := wOpen.induce (squareRectangleVertices m n : Set SquareVertex) hsupport
  have hmap := congrArg SimpleGraph.Walk.edges
    (SimpleGraph.Walk.map_induce wOpen hsupport)
  rw [SimpleGraph.Walk.edges_map] at hmap
  calc
    (wInd.copy rfl rfl).edges.map (Sym2.map Subtype.val) =
        wInd.edges.map (Sym2.map Subtype.val) := by simp
    _ = wOpen.edges := by simpa [wInd] using hmap
    _ = C.walk.edges := SimpleGraph.Walk.edges_transfer C.walk _

/-- Existing boundary-free rectangle crossings are exactly the existence of an open member of
the finite self-avoiding candidate space. -/
theorem mem_squareBoundaryFreeRectangleCrossingEvent_iff_exists_open_path
    {m n : ℕ} {ω : EdgeConfiguration 2} :
    ω ∈ squareBoundaryFreeRectangleCrossingEvent m n ↔
      ∃ P : SquareBoundaryFreeCrossingPath m n, P.IsOpen ω := by
  classical
  constructor
  · simp only [squareBoundaryFreeRectangleCrossingEvent, Set.mem_iUnion]
    rintro ⟨x, hx, y, hy, w, hwOpen, hwEdges⟩
    let full : EdgeConfiguration 2 := squareBoundaryFreeRectangleEdges m n
    let C : OpenSquareRectangleCrossing m n full :=
      { start := x
        finish := y
        walk := w
        start_mem := hx
        finish_mem := hy
        isOpen := by
          intro e he
          let ee : SquareEdge := ⟨e, w.edges_subset_edgeSet he⟩
          exact hwEdges ((mem_walkEdgeFinset_iff w ee).mpr he)
        edges_subset := fun e he ↦ (Finset.mem_filter.mp (hwEdges he)).1 }
    let Q := walkBetweenFinsetsOfOpenSquareRectangleCrossing C
    let P : SquareBoundaryFreeCrossingPath m n :=
      ⟨Q.start, Q.finish, Q.walk.toPath⟩
    refine ⟨P, ?_⟩
    intro e he
    have heAmbient : e ∈ P.ambientWalk.edges := he
    change e ∈ (ambientWalkOfSquareRectangleOpenWalk P.2.2.1).edges at heAmbient
    rw [edges_ambientWalkOfSquareRectangleOpenWalk] at heAmbient
    obtain ⟨e₀, he₀Path, he₀map⟩ := List.mem_map.mp heAmbient
    have he₀Q : e₀ ∈ Q.walk.edges := Q.walk.edges_toPath_subset he₀Path
    have hmap : Sym2.map Subtype.val e₀ ∈ C.walk.edges := by
      rw [← edges_liftedRectangleWalk_map C]
      exact List.mem_map.mpr ⟨e₀, he₀Q, rfl⟩
    have heq : Sym2.map Subtype.val e₀ = e := he₀map
    exact hwOpen e (heq ▸ hmap)
  · rintro ⟨P, hP⟩
    simp only [squareBoundaryFreeRectangleCrossingEvent, Set.mem_iUnion]
    refine ⟨P.1.1.1, mem_squareRectangleLeftTerminals.mp P.1.2,
      P.2.1.1.1, mem_squareRectangleRightTerminals.mp P.2.1.2,
      P.ambientWalk, hP, ?_⟩
    have hfull : walkIsOpen
        (squareBoundaryFreeRectangleEdges m n : Set SquareEdge) P.ambientWalk := by
      exact walkIsOpen_ambientWalkOfSquareRectangleOpenWalk P.2.2.1
    intro e he
    exact hfull e ((mem_walkEdgeFinset_iff P.ambientWalk e).mp he)

/-- The existing crossing event is the finite union of the fixed-path cylinder events. -/
theorem squareBoundaryFreeRectangleCrossingEvent_eq_biUnion_open_paths (m n : ℕ) :
    squareBoundaryFreeRectangleCrossingEvent m n =
      ⋃ P ∈ squareBoundaryFreeCrossingPaths m n, P.openEvent := by
  ext ω
  rw [mem_squareBoundaryFreeRectangleCrossingEvent_iff_exists_open_path]
  simp only [squareBoundaryFreeCrossingPaths, Finset.mem_univ, Set.mem_iUnion,
    SquareBoundaryFreeCrossingPath.openEvent, Set.mem_setOf_eq]
  constructor
  · rintro ⟨P, hP⟩
    exact ⟨P, True.intro, hP⟩
  · rintro ⟨P, -, hP⟩
    exact ⟨P, hP⟩

end Percolation
