import Percolation.Planar.TriangularPeierls

/-!
# Positive-ray parity for triangular Peierls contours

This file turns the finite even-degree hexagonal boundary graph into a simple cycle meeting the
positive horizontal ray an odd number of times.
-/

namespace Percolation

open SimpleGraph MeasureTheory ProbabilityTheory
open scoped Sym2 unitInterval

/-- The primal vertex at coordinate `k` on the positive horizontal ray. -/
def triangularPositiveRayPrimalVertex (k : ℕ) : SquareVertex :=
  squareVertex (k : ℤ) 0

/-- The hexagonal edge crossing the `k`th horizontal primal edge of the positive ray. -/
def triangularPositiveRayDualEdge (k : ℕ) : Sym2 TriangularHexVertex :=
  triangularHexDartEdge (triangularHexPositiveRayVertex k) 1

theorem triangularPositiveRayDualEdge_mem_edgeSet (k : ℕ) :
    triangularPositiveRayDualEdge k ∈ triangularHexGraph.edgeSet :=
  triangularHexDartEdge_mem_edgeSet _ _

theorem triangularPositiveRayDualEdge_crossed (k : ℕ) :
    triangularHexEdgeCrossed
        ⟨triangularPositiveRayDualEdge k,
          triangularPositiveRayDualEdge_mem_edgeSet k⟩ =
      triangularCubicStepEdge (triangularPositiveRayPrimalVertex k)
        ((0 : Fin 2), true) := by
  change triangularHexEdgeCrossed
      ⟨triangularHexDartEdge (triangularHexPositiveRayVertex k) 1, _⟩ = _
  rw [triangularHexEdgeCrossed_dart]
  rfl

theorem triangularPositiveRayDualEdge_injective :
    Function.Injective triangularPositiveRayDualEdge := by
  intro k l h
  simp only [triangularPositiveRayDualEdge, triangularHexDartEdge,
    triangularHexPositiveRayVertex, triangularHexNeighbor] at h
  rcases Sym2.eq_iff.mp h with hs | hs
  · have hcoord := congrArg (fun z : TriangularHexVertex ↦ z.1 0) hs.1
    simpa [squareVertex] using hcoord
  · have horient := congrArg Prod.snd hs.1
    simp at horient

/-- Embedding of positive-ray coordinates into dual edges. -/
def triangularPositiveRayDualEdgeEmbedding : ℕ ↪ Sym2 TriangularHexVertex :=
  ⟨triangularPositiveRayDualEdge, triangularPositiveRayDualEdge_injective⟩

/-- Indices before `R` at which membership in `C` changes along the positive ray. -/
noncomputable def triangularPositiveRayChangeIndices
    (C : Set SquareVertex) (R : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range R).filter fun k ↦
    ¬ (triangularPositiveRayPrimalVertex k ∈ C ↔
      triangularPositiveRayPrimalVertex (k + 1) ∈ C)

theorem odd_card_triangularPositiveRayChangeIndices
    {C : Set SquareVertex} {R : ℕ}
    (hzero : triangularPositiveRayPrimalVertex 0 ∈ C)
    (hR : triangularPositiveRayPrimalVertex R ∉ C) :
    Odd (triangularPositiveRayChangeIndices C R).card := by
  classical
  simpa [triangularPositiveRayChangeIndices] using
    odd_card_filter_nat_changes_of_true_false
      (P := fun k ↦ triangularPositiveRayPrimalVertex k ∈ C) hzero hR

/-- Positive-ray boundary edges up to the terminal coordinate `R`. -/
noncomputable def triangularPositiveRayBoundaryEdges
    (C : Set SquareVertex) (R : ℕ) : Finset (Sym2 TriangularHexVertex) :=
  (triangularPositiveRayChangeIndices C R).map
    triangularPositiveRayDualEdgeEmbedding

theorem odd_card_triangularPositiveRayBoundaryEdges
    {C : Set SquareVertex} {R : ℕ}
    (hzero : triangularPositiveRayPrimalVertex 0 ∈ C)
    (hR : triangularPositiveRayPrimalVertex R ∉ C) :
    Odd (triangularPositiveRayBoundaryEdges C R).card := by
  rw [triangularPositiveRayBoundaryEdges, Finset.card_map]
  exact odd_card_triangularPositiveRayChangeIndices hzero hR

theorem triangularPositiveRayDualEdge_mem_boundary_of_change
    {C : Set SquareVertex} {R k : ℕ}
    (hk : k ∈ triangularPositiveRayChangeIndices C R) :
    triangularPositiveRayDualEdge k ∈
      (triangularHexBoundaryGraph C).edgeSet := by
  classical
  rw [triangularPositiveRayChangeIndices, Finset.mem_filter] at hk
  rw [mem_triangularHexBoundaryGraph_edgeSet_iff]
  refine ⟨triangularPositiveRayDualEdge_mem_edgeSet k, ?_⟩
  rw [triangularPositiveRayDualEdge_crossed,
    triangularEdgeCuts_cubicStep_iff]
  have hstep : cubicStepFrom (triangularPositiveRayPrimalVertex k)
      ((0 : Fin 2), true) = triangularPositiveRayPrimalVertex (k + 1) := by
    ext i
    fin_cases i <;>
      simp [triangularPositiveRayPrimalVertex, squareVertex,
        cubicStepFrom, cubicDirectionIncrement]
  rw [hstep]
  by_cases hleft : triangularPositiveRayPrimalVertex k ∈ C <;>
    by_cases hright : triangularPositiveRayPrimalVertex (k + 1) ∈ C <;>
      simp_all

theorem triangularPositiveRayBoundaryEdges_subset_boundaryGraph
    (C : Set SquareVertex) (R : ℕ) :
    ∀ e ∈ triangularPositiveRayBoundaryEdges C R,
      e ∈ (triangularHexBoundaryGraph C).edgeSet := by
  intro e he
  rw [triangularPositiveRayBoundaryEdges, Finset.mem_map] at he
  rcases he with ⟨k, hk, rfl⟩
  exact triangularPositiveRayDualEdge_mem_boundary_of_change hk

theorem mem_triangularPositiveRayChangeIndices_of_mem_boundary
    {C : Set SquareVertex} {R k : ℕ}
    (houtside : ∀ j : ℕ, R ≤ j → triangularPositiveRayPrimalVertex j ∉ C)
    (hkBoundary : triangularPositiveRayDualEdge k ∈
      (triangularHexBoundaryGraph C).edgeSet) :
    k ∈ triangularPositiveRayChangeIndices C R := by
  classical
  have hklt : k < R := by
    by_contra hnot
    have hkout := houtside k (by omega)
    have hksout := houtside (k + 1) (by omega)
    rw [mem_triangularHexBoundaryGraph_edgeSet_iff] at hkBoundary
    rcases hkBoundary with ⟨_he, hcut⟩
    rw [triangularPositiveRayDualEdge_crossed,
      triangularEdgeCuts_cubicStep_iff] at hcut
    have hstep : cubicStepFrom (triangularPositiveRayPrimalVertex k)
        ((0 : Fin 2), true) = triangularPositiveRayPrimalVertex (k + 1) := by
      ext i
      fin_cases i <;>
        simp [triangularPositiveRayPrimalVertex, squareVertex,
          cubicStepFrom, cubicDirectionIncrement]
    rw [hstep] at hcut
    simp [hkout, hksout] at hcut
  rw [triangularPositiveRayChangeIndices, Finset.mem_filter]
  refine ⟨Finset.mem_range.mpr hklt, ?_⟩
  rw [mem_triangularHexBoundaryGraph_edgeSet_iff] at hkBoundary
  rcases hkBoundary with ⟨_he, hcut⟩
  rw [triangularPositiveRayDualEdge_crossed,
    triangularEdgeCuts_cubicStep_iff] at hcut
  have hstep : cubicStepFrom (triangularPositiveRayPrimalVertex k)
      ((0 : Fin 2), true) = triangularPositiveRayPrimalVertex (k + 1) := by
    ext i
    fin_cases i <;>
      simp [triangularPositiveRayPrimalVertex, squareVertex,
        cubicStepFrom, cubicDirectionIncrement]
  rw [hstep] at hcut
  by_cases hk : triangularPositiveRayPrimalVertex k ∈ C <;>
    by_cases hks : triangularPositiveRayPrimalVertex (k + 1) ∈ C <;>
      simp_all

/-- A finite primal set containing the origin has a terminal positive-ray coordinate beyond all
of its vertices. -/
theorem exists_triangularPositiveRay_terminal
    {C : Set SquareVertex} (hC : C.Finite)
    (hzero : triangularPositiveRayPrimalVertex 0 ∈ C) :
    ∃ R : ℕ, 0 < R ∧
      ∀ k : ℕ, R ≤ k → triangularPositiveRayPrimalVertex k ∉ C := by
  have hcoordFinite : ((fun x : SquareVertex ↦ x 0) '' C).Finite :=
    hC.image _
  rcases hcoordFinite.bddAbove with ⟨b, hb⟩
  have hbzero : (0 : ℤ) ≤ b := by
    apply hb
    exact ⟨triangularPositiveRayPrimalVertex 0, hzero, by
      simp [triangularPositiveRayPrimalVertex, squareVertex]⟩
  obtain ⟨R, hRb⟩ := exists_nat_gt b
  refine ⟨R, by omega, ?_⟩
  intro k hRk hkC
  have hkb : (k : ℤ) ≤ b := by
    apply hb
    exact ⟨triangularPositiveRayPrimalVertex k, hkC, by
      simp [triangularPositiveRayPrimalVertex, squareVertex]⟩
  exact (not_lt_of_ge hkb) (lt_of_lt_of_le hRb (by exact_mod_cast hRk))

/-- Finite even-degree boundary selection: some simple boundary cycle meets the positive ray an
odd number of times. -/
theorem exists_triangularHexBoundary_isCycle_odd_positiveRay
    {C : Set SquareVertex} (hC : C.Finite)
    (hzero : triangularPositiveRayPrimalVertex 0 ∈ C) :
    ∃ R : ℕ,
      (∀ k : ℕ, R ≤ k → triangularPositiveRayPrimalVertex k ∉ C) ∧
        ∃ u : TriangularHexVertex,
          ∃ w : (triangularHexBoundaryGraph C).Walk u u,
            w.IsCycle ∧
              Odd ((triangularPositiveRayBoundaryEdges C R).filter
                (fun e ↦ e ∈ w.edges.toFinset)).card := by
  classical
  obtain ⟨R, _hRpos, hRoutside⟩ :=
    exists_triangularPositiveRay_terminal hC hzero
  have hterminal : triangularPositiveRayPrimalVertex R ∉ C :=
    hRoutside R le_rfl
  obtain ⟨u, w, hwcycle, hwodd⟩ :=
    SimpleGraph.exists_isCycle_odd_card_filter_of_odd_edge_finset
      (triangularHexBoundaryGraph C)
      (triangularHexBoundaryGraph_support_finite hC)
      (even_degree_triangularHexBoundaryGraph C)
      (triangularPositiveRayBoundaryEdges C R)
      (triangularPositiveRayBoundaryEdges_subset_boundaryGraph C R)
      (odd_card_triangularPositiveRayBoundaryEdges hzero hterminal)
  exact ⟨R, hRoutside, u, w, hwcycle, hwodd⟩

end Percolation
