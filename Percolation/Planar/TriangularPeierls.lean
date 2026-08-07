import Percolation.Planar.TriangularHexCounting
import Percolation.Planar.Peierls

/-!
# A Peierls frontier for homogeneous triangular bond percolation

This file supplies the finite-frontier and tail implications used to prove percolation at a
rational density strictly below one half. The dual graph is the degree-three hexagonal graph
from TriangularHexDual; all separation is expressed by finite parity.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory SimpleGraph
open scoped unitInterval Sym2

/-- The six neighbors of a triangular-lattice vertex. -/
def triangularPrimalNeighbor (x : SquareVertex) (k : Fin 6) : SquareVertex :=
  if k = 0 then squareVertex (x 0 + 1) (x 1)
  else if k = 1 then squareVertex (x 0 - 1) (x 1)
  else if k = 2 then squareVertex (x 0) (x 1 + 1)
  else if k = 3 then squareVertex (x 0) (x 1 - 1)
  else if k = 4 then squareVertex (x 0 + 1) (x 1 + 1)
  else squareVertex (x 0 - 1) (x 1 - 1)

@[simp]
theorem triangularPrimalNeighbor_ne (x : SquareVertex) (k : Fin 6) :
    triangularPrimalNeighbor x k ≠ x := by
  intro h
  fin_cases k
  all_goals
    first
    | · have h0 := congrFun h (0 : Fin 2)
        simp [triangularPrimalNeighbor, squareVertex] at h0
    | · have h1 := congrFun h (1 : Fin 2)
        simp [triangularPrimalNeighbor, squareVertex] at h1

theorem triangularGraph_adj_neighbor (x : SquareVertex) (k : Fin 6) :
    triangularGraph.Adj x (triangularPrimalNeighbor x k) := by
  fin_cases k
  · have h := cubicGraph_adj_stepFrom x ((0 : Fin 2), true)
    have heq : triangularPrimalNeighbor x 0 =
        cubicStepFrom x ((0 : Fin 2), true) := by
      ext i
      fin_cases i <;>
        simp [triangularPrimalNeighbor, cubicStepFrom,
          cubicDirectionIncrement, squareVertex]
    rw [cubicGraph, SimpleGraph.fromRel_adj] at h
    rw [triangularGraph, SimpleGraph.fromRel_adj]
    change x ≠ triangularPrimalNeighbor x (0 : Fin 6) ∧
      (triangularStep x (triangularPrimalNeighbor x (0 : Fin 6)) ∨
        triangularStep (triangularPrimalNeighbor x (0 : Fin 6)) x)
    rw [heq]
    exact ⟨h.1, h.2.imp (fun hc ↦ Or.inl hc) (fun hc ↦ Or.inl hc)⟩
  · have h := cubicGraph_adj_stepFrom x ((0 : Fin 2), false)
    have heq : triangularPrimalNeighbor x 1 =
        cubicStepFrom x ((0 : Fin 2), false) := by
      ext i
      fin_cases i <;>
        simp [triangularPrimalNeighbor, cubicStepFrom,
          cubicDirectionIncrement, squareVertex, sub_eq_add_neg]
    rw [cubicGraph, SimpleGraph.fromRel_adj] at h
    rw [triangularGraph, SimpleGraph.fromRel_adj]
    change x ≠ triangularPrimalNeighbor x (1 : Fin 6) ∧
      (triangularStep x (triangularPrimalNeighbor x (1 : Fin 6)) ∨
        triangularStep (triangularPrimalNeighbor x (1 : Fin 6)) x)
    rw [heq]
    exact ⟨h.1, h.2.imp (fun hc ↦ Or.inl hc) (fun hc ↦ Or.inl hc)⟩
  · have h := cubicGraph_adj_stepFrom x ((1 : Fin 2), true)
    have heq : triangularPrimalNeighbor x 2 =
        cubicStepFrom x ((1 : Fin 2), true) := by
      ext i
      fin_cases i <;>
        simp [triangularPrimalNeighbor, cubicStepFrom,
          cubicDirectionIncrement, squareVertex]
    rw [cubicGraph, SimpleGraph.fromRel_adj] at h
    rw [triangularGraph, SimpleGraph.fromRel_adj]
    change x ≠ triangularPrimalNeighbor x (2 : Fin 6) ∧
      (triangularStep x (triangularPrimalNeighbor x (2 : Fin 6)) ∨
        triangularStep (triangularPrimalNeighbor x (2 : Fin 6)) x)
    rw [heq]
    exact ⟨h.1, h.2.imp (fun hc ↦ Or.inl hc) (fun hc ↦ Or.inl hc)⟩
  · have h := cubicGraph_adj_stepFrom x ((1 : Fin 2), false)
    have heq : triangularPrimalNeighbor x 3 =
        cubicStepFrom x ((1 : Fin 2), false) := by
      ext i
      fin_cases i <;>
        simp [triangularPrimalNeighbor, cubicStepFrom,
          cubicDirectionIncrement, squareVertex, sub_eq_add_neg]
    rw [cubicGraph, SimpleGraph.fromRel_adj] at h
    rw [triangularGraph, SimpleGraph.fromRel_adj]
    change x ≠ triangularPrimalNeighbor x (3 : Fin 6) ∧
      (triangularStep x (triangularPrimalNeighbor x (3 : Fin 6)) ∨
        triangularStep (triangularPrimalNeighbor x (3 : Fin 6)) x)
    rw [heq]
    exact ⟨h.1, h.2.imp (fun hc ↦ Or.inl hc) (fun hc ↦ Or.inl hc)⟩
  · rw [triangularGraph, SimpleGraph.fromRel_adj]
    refine ⟨triangularPrimalNeighbor_ne x 4 |>.symm, Or.inl (Or.inr ?_)⟩
    ext i
    fin_cases i <;> simp [triangularPrimalNeighbor, triangularDiagonalStep, squareVertex]
  · rw [triangularGraph, SimpleGraph.fromRel_adj]
    refine ⟨triangularPrimalNeighbor_ne x 5 |>.symm, Or.inr (Or.inr ?_)⟩
    ext i
    fin_cases i <;> simp [triangularPrimalNeighbor, triangularDiagonalStep, squareVertex]

theorem triangularPrimalNeighbor_injective (x : SquareVertex) :
    Function.Injective (triangularPrimalNeighbor x) := by
  intro k l h
  fin_cases k <;> fin_cases l
  all_goals try rfl
  all_goals
    exfalso
    have h0 := congrFun h (0 : Fin 2)
    have h1 := congrFun h (1 : Fin 2)
    simp [triangularPrimalNeighbor, squareVertex] at h0 h1 <;> omega

theorem triangularGraph_adj_iff_exists_neighbor (x y : SquareVertex) :
    triangularGraph.Adj x y ↔ ∃ k : Fin 6, y = triangularPrimalNeighbor x k := by
  constructor
  · intro hxy
    rw [triangularGraph, SimpleGraph.fromRel_adj] at hxy
    rcases hxy with ⟨hne, hstep | hstep⟩
    · rcases hstep with hcubic | hdiag
      · have hG : (cubicGraph 2).Adj x y := by
          rw [cubicGraph, SimpleGraph.fromRel_adj]
          exact ⟨hne, Or.inl hcubic⟩
        rcases (cubicGraph_adj_iff_exists_stepFrom x y).mp hG with ⟨a, rfl⟩
        rcases a with ⟨i, b⟩
        fin_cases i <;> cases b
        · exact ⟨1, by ext j; fin_cases j <;>
            simp [triangularPrimalNeighbor, cubicStepFrom,
              cubicDirectionIncrement, squareVertex, sub_eq_add_neg]⟩
        · exact ⟨0, by ext j; fin_cases j <;>
            simp [triangularPrimalNeighbor, cubicStepFrom,
              cubicDirectionIncrement, squareVertex]⟩
        · exact ⟨3, by ext j; fin_cases j <;>
            simp [triangularPrimalNeighbor, cubicStepFrom,
              cubicDirectionIncrement, squareVertex, sub_eq_add_neg]⟩
        · exact ⟨2, by ext j; fin_cases j <;>
            simp [triangularPrimalNeighbor, cubicStepFrom,
              cubicDirectionIncrement, squareVertex]⟩
      · exact ⟨4, by
          rw [hdiag]
          ext i
          fin_cases i <;>
            simp [triangularPrimalNeighbor, triangularDiagonalStep, squareVertex]⟩
    · rcases hstep with hcubic | hdiag
      · have hG : (cubicGraph 2).Adj x y := by
          rw [cubicGraph, SimpleGraph.fromRel_adj]
          exact ⟨hne, Or.inr hcubic⟩
        rcases (cubicGraph_adj_iff_exists_stepFrom x y).mp hG with ⟨a, rfl⟩
        rcases a with ⟨i, b⟩
        fin_cases i <;> cases b
        · exact ⟨1, by ext j; fin_cases j <;>
            simp [triangularPrimalNeighbor, cubicStepFrom,
              cubicDirectionIncrement, squareVertex, sub_eq_add_neg]⟩
        · exact ⟨0, by ext j; fin_cases j <;>
            simp [triangularPrimalNeighbor, cubicStepFrom,
              cubicDirectionIncrement, squareVertex]⟩
        · exact ⟨3, by ext j; fin_cases j <;>
            simp [triangularPrimalNeighbor, cubicStepFrom,
              cubicDirectionIncrement, squareVertex, sub_eq_add_neg]⟩
        · exact ⟨2, by ext j; fin_cases j <;>
            simp [triangularPrimalNeighbor, cubicStepFrom,
              cubicDirectionIncrement, squareVertex]⟩
      · exact ⟨5, by
          ext i
          fin_cases i
          · have h := congrFun hdiag (0 : Fin 2)
            simp [triangularPrimalNeighbor, triangularDiagonalStep, squareVertex] at h ⊢
            omega
          · have h := congrFun hdiag (1 : Fin 2)
            simp [triangularPrimalNeighbor, triangularDiagonalStep, squareVertex] at h ⊢
            omega⟩
  · rintro ⟨k, rfl⟩
    exact triangularGraph_adj_neighbor x k

theorem triangularGraph_neighborSet_eq_range (x : SquareVertex) :
    triangularGraph.neighborSet x = Set.range (triangularPrimalNeighbor x) := by
  ext y
  rw [SimpleGraph.mem_neighborSet, triangularGraph_adj_iff_exists_neighbor,
    Set.mem_range]
  constructor <;> rintro ⟨k, hk⟩
  · exact ⟨k, hk.symm⟩
  · exact ⟨k, hk.symm⟩

/-- The explicit six directions identify every neighbor in the triangular lattice. -/
noncomputable def triangularPrimalNeighborEquiv (x : SquareVertex) :
    Fin 6 ≃ triangularGraph.neighborSet x where
  toFun k := ⟨triangularPrimalNeighbor x k, triangularGraph_adj_neighbor x k⟩
  invFun y := Classical.choose ((triangularGraph_adj_iff_exists_neighbor x y).mp y.2)
  left_inv k := by
    apply triangularPrimalNeighbor_injective x
    exact (Classical.choose_spec
      ((triangularGraph_adj_iff_exists_neighbor x
        (triangularPrimalNeighbor x k)).mp (triangularGraph_adj_neighbor x k))).symm
  right_inv y := by
    apply Subtype.ext
    exact (Classical.choose_spec
      ((triangularGraph_adj_iff_exists_neighbor x y).mp y.2)).symm

noncomputable instance triangularGraphNeighborSetFintype (x : SquareVertex) :
    Fintype (triangularGraph.neighborSet x) :=
  Fintype.ofEquiv (Fin 6) (triangularPrimalNeighborEquiv x)

noncomputable instance triangularGraphLocallyFinite : triangularGraph.LocallyFinite :=
  fun x ↦ triangularGraphNeighborSetFintype x

@[simp]
theorem triangularGraph_degree (x : SquareVertex) : triangularGraph.degree x = 6 := by
  classical
  rw [← triangularGraph.card_neighborSet_eq_degree]
  exact Fintype.card_congr (triangularPrimalNeighborEquiv x)

/-! ### Finite triangular boundaries and their dual parity -/

/-- A triangular bond cuts a vertex set if its unordered endpoints lie on opposite sides. -/
def triangularEdgeCuts (C : Set SquareVertex) (e : TriangularEdge) : Prop :=
  ∃ u ∈ C, ∃ v ∉ C, (e.1 : Sym2 SquareVertex) = s(u, v)

theorem triangularEdgeCuts_mk_iff (C : Set SquareVertex) {u v : SquareVertex}
    (huv : triangularGraph.Adj u v) :
    triangularEdgeCuts C ⟨s(u, v), by simpa [SimpleGraph.mem_edgeSet] using huv⟩ ↔
      (u ∈ C ∧ v ∉ C) ∨ (v ∈ C ∧ u ∉ C) := by
  constructor
  · rintro ⟨a, ha, b, hb, hab⟩
    have hab' : s(u, v) = s(a, b) := hab
    rcases Sym2.eq_iff.mp hab' with hs | hs
    · rcases hs with ⟨hbu, hav⟩
      subst b
      subst a
      exact Or.inl ⟨ha, hb⟩
    · rcases hs with ⟨hau, hbv⟩
      subst a
      subst b
      exact Or.inr ⟨ha, hb⟩
  · rintro (h | h)
    · exact ⟨u, h.1, v, h.2, rfl⟩
    · exact ⟨v, h.1, u, h.2, Sym2.eq_swap⟩

theorem triangularEdgeCuts_cubicStep_iff (C : Set SquareVertex)
    (x : SquareVertex) (a : CubicDirection 2) :
    triangularEdgeCuts C (triangularCubicStepEdge x a) ↔
      (x ∈ C ∧ cubicStepFrom x a ∉ C) ∨
        (cubicStepFrom x a ∈ C ∧ x ∉ C) := by
  simpa only [triangularCubicStepEdge] using
    triangularEdgeCuts_mk_iff C (cubicGraph_adj_stepFrom x a |> fun h ↦ by
      rw [cubicGraph, SimpleGraph.fromRel_adj] at h
      rw [triangularGraph, SimpleGraph.fromRel_adj]
      exact ⟨h.1, h.2.imp (fun hc ↦ Or.inl hc) (fun hc ↦ Or.inl hc)⟩)

theorem triangularEdgeCuts_diagonal_iff (C : Set SquareVertex) (x : SquareVertex) :
    triangularEdgeCuts C (triangularDiagonalEdge x) ↔
      (x ∈ C ∧ (fun i ↦ x i + 1) ∉ C) ∨
        ((fun i ↦ x i + 1) ∈ C ∧ x ∉ C) := by
  simpa only [triangularDiagonalEdge] using
    triangularEdgeCuts_mk_iff C (by
      rw [triangularGraph, SimpleGraph.fromRel_adj]
      refine ⟨?_, Or.inl (Or.inr rfl)⟩
      intro h
      have h0 := congrFun h (0 : Fin 2)
      simp at h0)

/-- The directions of the dual edges incident to a face whose crossed primal bond cuts `C`. -/
noncomputable def triangularHexCutDirections
    (C : Set SquareVertex) (z : TriangularHexVertex) : Finset (Fin 3) := by
  classical
  exact Finset.univ.filter fun k ↦
    triangularEdgeCuts C (triangularHexCrossedEdge z k)

private theorem card_filter_fin_three (P : Fin 3 → Prop) [DecidablePred P] :
    (Finset.univ.filter P).card =
      (if P 0 then 1 else 0) + (if P 1 then 1 else 0) +
        (if P 2 then 1 else 0) := by
  rw [show (Finset.univ : Finset (Fin 3)) = {0, 1, 2} by decide]
  by_cases h0 : P 0 <;> by_cases h1 : P 1 <;> by_cases h2 : P 2 <;>
    simp [Finset.filter_insert, Finset.filter_singleton, h0, h1, h2]

theorem even_card_triangularHexCutDirections
    (C : Set SquareVertex) (z : TriangularHexVertex) :
    Even (triangularHexCutDirections C z).card := by
  classical
  rcases z with ⟨x, b⟩
  cases b
  · unfold triangularHexCutDirections
    rw [card_filter_fin_three]
    let y := squareVertex (x 0 + 1) (x 1)
    let t := fun i ↦ x i + 1
    have hxy : Function.update x 0 (x 0 + 1) = y := by
      ext i
      fin_cases i <;> simp [y, squareVertex]
    have hyt : Function.update y 1 (x 1 + 1) = t := by
      ext i
      fin_cases i <;> simp [y, t, squareVertex]
    by_cases hx : x ∈ C <;> by_cases hy : y ∈ C <;> by_cases ht : t ∈ C <;>
      simp [triangularHexCrossedEdge,
        triangularEdgeCuts_cubicStep_iff, triangularEdgeCuts_diagonal_iff,
        cubicStepFrom, cubicDirectionIncrement, squareVertex, y, t,
        hxy, hyt, hx, hy, ht]
  · unfold triangularHexCutDirections
    rw [card_filter_fin_three]
    let y := squareVertex (x 0) (x 1 + 1)
    let t := fun i ↦ x i + 1
    have hxy : Function.update x 1 (x 1 + 1) = y := by
      ext i
      fin_cases i <;> simp [y, squareVertex]
    have hyt : Function.update y 0 (x 0 + 1) = t := by
      ext i
      fin_cases i <;> simp [y, t, squareVertex]
    by_cases hx : x ∈ C <;> by_cases hy : y ∈ C <;> by_cases ht : t ∈ C <;>
      simp [triangularHexCrossedEdge,
        triangularEdgeCuts_cubicStep_iff, triangularEdgeCuts_diagonal_iff,
        cubicStepFrom, cubicDirectionIncrement, squareVertex, y, t,
        hxy, hyt, hx, hy, ht]

/-- The set of dual edges crossing the edge boundary of `C`. -/
noncomputable def triangularHexBoundaryEdgeSet
    (C : Set SquareVertex) : Set (Sym2 TriangularHexVertex) :=
  Subtype.val '' {e : triangularHexGraph.edgeSet |
    triangularEdgeCuts C (triangularHexEdgeCrossed e)}

/-- The finite-parity dual boundary graph of a primal vertex set. -/
noncomputable def triangularHexBoundaryGraph
    (C : Set SquareVertex) : SimpleGraph TriangularHexVertex :=
  SimpleGraph.fromEdgeSet (triangularHexBoundaryEdgeSet C)

theorem mem_triangularHexBoundaryGraph_edgeSet_iff
    (C : Set SquareVertex) (e : Sym2 TriangularHexVertex) :
    e ∈ (triangularHexBoundaryGraph C).edgeSet ↔
      ∃ he : e ∈ triangularHexGraph.edgeSet,
        triangularEdgeCuts C (triangularHexEdgeCrossed ⟨e, he⟩) := by
  rw [triangularHexBoundaryGraph, SimpleGraph.edgeSet_fromEdgeSet]
  constructor
  · rintro ⟨⟨d, hd, rfl⟩, _hdiag⟩
    exact ⟨d.property, hd⟩
  · rintro ⟨he, hcut⟩
    refine ⟨⟨⟨e, he⟩, hcut, rfl⟩, ?_⟩
    exact triangularHexGraph.not_isDiag_of_mem_edgeSet he

theorem triangularHexBoundaryGraph_adj_iff
    (C : Set SquareVertex) (x y : TriangularHexVertex) :
    (triangularHexBoundaryGraph C).Adj x y ↔
      ∃ k : Fin 3, y = triangularHexNeighbor x k ∧
        triangularEdgeCuts C (triangularHexCrossedEdge x k) := by
  rw [← SimpleGraph.mem_edgeSet,
    mem_triangularHexBoundaryGraph_edgeSet_iff]
  constructor
  · rintro ⟨hxy, hcut⟩
    rcases (triangularHexGraph_adj_iff x y).mp hxy with ⟨k, rfl⟩
    refine ⟨k, rfl, ?_⟩
    change triangularEdgeCuts C
      (triangularHexEdgeCrossed
        ⟨triangularHexDartEdge x k, hxy⟩) at hcut
    have heq :
        (⟨triangularHexDartEdge x k, hxy⟩ : triangularHexGraph.edgeSet) =
          ⟨triangularHexDartEdge x k,
            triangularHexDartEdge_mem_edgeSet x k⟩ := Subtype.ext rfl
    rw [heq, triangularHexEdgeCrossed_dart] at hcut
    exact hcut
  · rintro ⟨k, rfl, hcut⟩
    refine ⟨triangularHexDartEdge_mem_edgeSet x k, ?_⟩
    change triangularEdgeCuts C
      (triangularHexEdgeCrossed
        ⟨triangularHexDartEdge x k,
          triangularHexDartEdge_mem_edgeSet x k⟩)
    rw [triangularHexEdgeCrossed_dart]
    exact hcut

/-- Boundary directions are equivalent to boundary-graph neighbors. -/
noncomputable def triangularHexBoundaryNeighborEquiv
    (C : Set SquareVertex) (x : TriangularHexVertex) :
    {k : Fin 3 // triangularEdgeCuts C (triangularHexCrossedEdge x k)} ≃
      (triangularHexBoundaryGraph C).neighborSet x where
  toFun k := ⟨triangularHexNeighbor x k.1,
    (triangularHexBoundaryGraph_adj_iff C x _).2 ⟨k.1, rfl, k.2⟩⟩
  invFun y := by
    let h := (triangularHexBoundaryGraph_adj_iff C x y).mp y.2
    exact ⟨Classical.choose h, (Classical.choose_spec h).2⟩
  left_inv k := by
    apply Subtype.ext
    apply triangularHexNeighbor_injective x
    exact (Classical.choose_spec
      ((triangularHexBoundaryGraph_adj_iff C x
        (triangularHexNeighbor x k.1)).mp
          ((triangularHexBoundaryGraph_adj_iff C x _).2
            ⟨k.1, rfl, k.2⟩))).1.symm
  right_inv y := by
    apply Subtype.ext
    exact (Classical.choose_spec
      ((triangularHexBoundaryGraph_adj_iff C x y).mp y.2)).1.symm

noncomputable instance triangularHexBoundaryGraphNeighborSetFintype
    (C : Set SquareVertex) (x : TriangularHexVertex) :
    Fintype ((triangularHexBoundaryGraph C).neighborSet x) := by
  classical
  exact Fintype.ofEquiv
    {k : Fin 3 // triangularEdgeCuts C (triangularHexCrossedEdge x k)}
    (triangularHexBoundaryNeighborEquiv C x)

noncomputable instance triangularHexBoundaryGraphLocallyFinite
    (C : Set SquareVertex) : (triangularHexBoundaryGraph C).LocallyFinite :=
  fun x ↦ triangularHexBoundaryGraphNeighborSetFintype C x

theorem triangularHexBoundaryGraph_degree_eq_cutDirections_card
    (C : Set SquareVertex) (x : TriangularHexVertex) :
    (triangularHexBoundaryGraph C).degree x =
      (triangularHexCutDirections C x).card := by
  classical
  rw [← (triangularHexBoundaryGraph C).card_neighborSet_eq_degree]
  calc
    Fintype.card ((triangularHexBoundaryGraph C).neighborSet x) =
        Fintype.card
          {k : Fin 3 // triangularEdgeCuts C (triangularHexCrossedEdge x k)} :=
      Fintype.card_congr (triangularHexBoundaryNeighborEquiv C x).symm
    _ = (Finset.univ.filter fun k ↦
        triangularEdgeCuts C (triangularHexCrossedEdge x k)).card :=
      Fintype.card_subtype _
    _ = (triangularHexCutDirections C x).card := by
      rfl

theorem even_degree_triangularHexBoundaryGraph
    (C : Set SquareVertex) (x : TriangularHexVertex) :
    Even ((triangularHexBoundaryGraph C).degree x) := by
  rw [triangularHexBoundaryGraph_degree_eq_cutDirections_card]
  exact even_card_triangularHexCutDirections C x

theorem triangularHexDualOfPrimal_edgeCrossed
    (e : triangularHexGraph.edgeSet) :
    triangularHexDualOfPrimal (triangularHexEdgeCrossed e).1 = e.1 := by
  calc
    triangularHexDualOfPrimal (triangularHexEdgeCrossed e).1 =
        triangularHexDartEdge e.1.out.1 (triangularHexEdgeDirection e) :=
      triangularHexDualOfPrimal_crossed _ _
    _ = s(e.1.out.1, e.1.out.2) := by
      rw [triangularHexDartEdge, ← triangularHexEdgeDirection_spec e]
    _ = e.1 := e.1.out_eq

theorem triangularHexBoundaryGraph_edgeSet_finite
    {C : Set SquareVertex} (hC : C.Finite) :
    (triangularHexBoundaryGraph C).edgeSet.Finite := by
  classical
  let S : Set (Sym2 SquareVertex) :=
    ⋃ x ∈ C, triangularGraph.incidenceSet x
  have hS : S.Finite := by
    exact hC.biUnion fun x _hx ↦ Set.toFinite _
  refine (hS.image triangularHexDualOfPrimal).subset ?_
  intro e he
  rw [mem_triangularHexBoundaryGraph_edgeSet_iff] at he
  rcases he with ⟨heHex, hcut⟩
  rcases hcut with ⟨u, hu, v, hv, huv⟩
  let d : triangularHexGraph.edgeSet := ⟨e, heHex⟩
  have hdS : (triangularHexEdgeCrossed d).1 ∈ S := by
    rw [show S = ⋃ x ∈ C, triangularGraph.incidenceSet x by rfl]
    refine Set.mem_iUnion.mpr ⟨u, Set.mem_iUnion.mpr ⟨hu, ?_⟩⟩
    rw [SimpleGraph.edge_mem_incidenceSet_iff]
    rw [huv]
    simp
  exact ⟨(triangularHexEdgeCrossed d).1, hdS,
    triangularHexDualOfPrimal_edgeCrossed d⟩

theorem triangularHexBoundaryGraph_support_finite
    {C : Set SquareVertex} (hC : C.Finite) :
    (triangularHexBoundaryGraph C).support.Finite :=
  SimpleGraph.support_finite_of_edgeSet_finite
    (triangularHexBoundaryGraph_edgeSet_finite hC)

end Percolation
