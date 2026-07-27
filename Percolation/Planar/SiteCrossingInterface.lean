import Percolation.Planar.SiteCrossingFrontier
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# The planar interface for a failed site crossing

For the rectangle `[0,m] × [-n,n]`, adjoin a permanently reachable column at horizontal
coordinate `-1`.  The right side of the frame, at coordinate `m+1`, is permanently
unreachable.  The positive square-lattice edges across which framed reachability changes form a
finite primal interface.  After applying the square-lattice crossing bijection, this becomes a
finite shifted-dual graph.

Interior dual vertices have even interface degree by the four-side cell parity lemma.  The only
possible odd-degree vertices lie immediately below or above the rectangle.  The bottom and top
boundary interface sets both have odd cardinality, so the handshaking lemma forces an interface
component meeting both boundaries.  The unreachable endpoint of every primal interface edge is
a closed site in the original rectangle; consecutive interface edges have unreachable endpoints
which are equal or star-adjacent.  This supplies the deterministic crossing alternative needed
for Grimmett's site estimate (7.70).
-/

namespace Percolation

noncomputable section

open scoped Finset

local instance : DecidableEq SquarePositiveEdge := Classical.decEq _

/-- Reachability in the rectangle, augmented by the full column immediately to its left. -/
def siteRectangleFramedReachable
    (m n : ℕ) (eta : Set SquareVertex) (x : SquareVertex) : Prop :=
  (x 0 = -1 ∧ -(n : ℤ) ≤ x 1 ∧ x 1 ≤ (n : ℤ)) ∨
    x ∈ siteRectangleLeftReachableVertices m n eta

noncomputable instance (m n : ℕ) (eta : Set SquareVertex) :
    DecidablePred (siteRectangleFramedReachable m n eta) :=
  Classical.decPred _

/-- The framed predicate agrees with ordinary left reachability inside the rectangle. -/
theorem siteRectangleFramedReachable_iff_reachable_of_mem_rectangle
    {m n : ℕ} {eta : Set SquareVertex} {x : SquareVertex}
    (hx : x ∈ squareRectangleVertices m n) :
    siteRectangleFramedReachable m n eta x ↔
      x ∈ siteRectangleLeftReachableVertices m n eta := by
  rw [siteRectangleFramedReachable]
  have hx0 := (mem_squareRectangleVertices_iff.mp hx).1
  constructor
  · rintro (hframe | hreachable)
    · exact False.elim (by omega)
    · exact hreachable
  · exact Or.inr

/-- Every vertex of the added left column is framed-reachable. -/
theorem siteRectangleFramedReachable_leftColumn
    (m n : ℕ) (eta : Set SquareVertex) (y : ℤ)
    (hyLower : -(n : ℤ) ≤ y) (hyUpper : y ≤ (n : ℤ)) :
    siteRectangleFramedReachable m n eta (squareVertex (-1) y) := by
  left
  simp [hyLower, hyUpper]

/-- The added right column is framed-unreachable. -/
theorem not_siteRectangleFramedReachable_rightColumn
    (m n : ℕ) (eta : Set SquareVertex) (y : ℤ)
    (hyLower : -(n : ℤ) ≤ y) (hyUpper : y ≤ (n : ℤ)) :
    ¬siteRectangleFramedReachable m n eta (squareVertex ((m : ℤ) + 1) y) := by
  rw [siteRectangleFramedReachable]
  rintro (hframe | hReachable)
  · have hcoord := hframe.1
    simp [squareVertex] at hcoord
    have hm : (0 : ℤ) ≤ (m : ℤ) := Int.natCast_nonneg m
    omega
  ·
    have hRect := (mem_siteRectangleLeftReachableVertices_iff
      m n eta (squareVertex ((m : ℤ) + 1) y)).mp hReachable |>.1
    rw [mem_squareRectangleVertices_iff] at hRect
    simpa [squareVertex] using hRect.2.1

/-- Shifted-dual unit cells whose interiors cover the framed rectangle. -/
noncomputable def siteRectangleInterfaceCells (m n : ℕ) : Finset DualSquareVertex :=
  Fintype.piFinset fun i : Fin 2 ↦
    if i = 0 then Finset.Icc (-1 : ℤ) (m : ℤ)
    else Finset.Icc (-(n : ℤ)) ((n : ℤ) - 1)

@[simp]
theorem mem_siteRectangleInterfaceCells_iff
    {m n : ℕ} {z : DualSquareVertex} :
    z ∈ siteRectangleInterfaceCells m n ↔
      -1 ≤ z 0 ∧ z 0 ≤ (m : ℤ) ∧
        -(n : ℤ) ≤ z 1 ∧ z 1 < (n : ℤ) := by
  classical
  simp only [siteRectangleInterfaceCells, Fintype.mem_piFinset]
  constructor
  · intro h
    have h0 : -1 ≤ z 0 ∧ z 0 ≤ (m : ℤ) := by
      simpa [Finset.mem_Icc] using h (0 : Fin 2)
    have h1 : -(n : ℤ) ≤ z 1 ∧ z 1 ≤ (n : ℤ) - 1 := by
      simpa [Finset.mem_Icc] using h (1 : Fin 2)
    omega
  · rintro ⟨hz0, hz0', hz1, hz1'⟩ i
    fin_cases i
    · simp [Finset.mem_Icc, hz0, hz0']
    · simp [Finset.mem_Icc]
      omega

/-- Positive primal edges surrounding at least one interface cell. -/
noncomputable def siteRectangleFramedPositiveEdges (m n : ℕ) : Finset SquarePositiveEdge := by
  classical
  exact (siteRectangleInterfaceCells m n).biUnion squareCellPositiveEdges

@[simp]
theorem mem_siteRectangleFramedPositiveEdges_iff
    {m n : ℕ} {e : SquarePositiveEdge} :
    e ∈ siteRectangleFramedPositiveEdges m n ↔
      ∃ z ∈ siteRectangleInterfaceCells m n, e ∈ squareCellPositiveEdges z := by
  classical
  simp [siteRectangleFramedPositiveEdges]

/-- Finite primal interface: the framed reachability predicate changes across the edge. -/
noncomputable def siteRectangleInterfacePositiveEdges
    (m n : ℕ) (eta : Set SquareVertex) : Finset SquarePositiveEdge := by
  classical
  exact (siteRectangleFramedPositiveEdges m n).filter fun e ↦
    ¬(siteRectangleFramedReachable m n eta e.base ↔
      siteRectangleFramedReachable m n eta
        (cubicStepFrom e.base (e.axis, true)))

@[simp]
theorem mem_siteRectangleInterfacePositiveEdges_iff
    {m n : ℕ} {eta : Set SquareVertex} {e : SquarePositiveEdge} :
    e ∈ siteRectangleInterfacePositiveEdges m n eta ↔
      e ∈ siteRectangleFramedPositiveEdges m n ∧
        ¬(siteRectangleFramedReachable m n eta e.base ↔
          siteRectangleFramedReachable m n eta
            (cubicStepFrom e.base (e.axis, true))) := by
  classical
  simp [siteRectangleInterfacePositiveEdges]

/-- Shifted-dual bonds crossing the framed primal interface. -/
noncomputable def siteRectangleInterfaceDualEdges
    (m n : ℕ) (eta : Set SquareVertex) : Finset DualSquareEdge :=
  (siteRectangleInterfacePositiveEdges m n eta).map
    squarePositiveEdgeDualCrossingEmbedding

/-- The finite shifted-dual interface graph. -/
noncomputable def siteRectangleInterfaceDualGraph
    (m n : ℕ) (eta : Set SquareVertex) : SimpleGraph DualSquareVertex :=
  SimpleGraph.fromEdgeSet
    (Subtype.val '' ((siteRectangleInterfaceDualEdges m n eta : Finset DualSquareEdge) :
      Set DualSquareEdge))

@[simp]
theorem mem_siteRectangleInterfaceDualEdges_iff
    {m n : ℕ} {eta : Set SquareVertex} {e : DualSquareEdge} :
    e ∈ siteRectangleInterfaceDualEdges m n eta ↔
      ∃ b : SquarePositiveEdge,
        b ∈ siteRectangleInterfacePositiveEdges m n eta ∧
          squarePositiveEdgeDualCrossingEmbedding b = e := by
  rw [siteRectangleInterfaceDualEdges, Finset.mem_map]

theorem mem_siteRectangleInterfaceDualGraph_edgeSet_iff
    {m n : ℕ} {eta : Set SquareVertex} {e : Sym2 DualSquareVertex} :
    e ∈ (siteRectangleInterfaceDualGraph m n eta).edgeSet ↔
      ∃ h : e ∈ dualSquareGraph.edgeSet,
        (⟨e, h⟩ : DualSquareEdge) ∈ siteRectangleInterfaceDualEdges m n eta := by
  rw [siteRectangleInterfaceDualGraph, SimpleGraph.edgeSet_fromEdgeSet]
  constructor
  · rintro ⟨himage, _hnotdiag⟩
    rcases himage with ⟨d, hd, rfl⟩
    exact ⟨d.property, hd⟩
  · rintro ⟨he, hinterface⟩
    exact ⟨⟨⟨e, he⟩, hinterface, rfl⟩,
      dualSquareGraph.not_isDiag_of_mem_edgeSet he⟩

theorem siteRectangleInterfaceDualGraph_edgeSet_finite
    (m n : ℕ) (eta : Set SquareVertex) :
    (siteRectangleInterfaceDualGraph m n eta).edgeSet.Finite := by
  classical
  refine ((siteRectangleInterfaceDualEdges m n eta).finite_toSet.image Subtype.val).subset ?_
  intro e he
  rw [mem_siteRectangleInterfaceDualGraph_edgeSet_iff] at he
  rcases he with ⟨hedual, hinterface⟩
  exact ⟨⟨e, hedual⟩, hinterface, rfl⟩

/-- The finite interface graph is a subgraph of the shifted-dual square lattice. -/
theorem siteRectangleInterfaceDualGraph_le_dualSquareGraph
    (m n : ℕ) (eta : Set SquareVertex) :
    siteRectangleInterfaceDualGraph m n eta ≤ dualSquareGraph := by
  intro x y hxy
  rw [siteRectangleInterfaceDualGraph, SimpleGraph.fromEdgeSet_adj] at hxy
  rcases hxy.1 with ⟨d, _hd, hdxy⟩
  have hmem : s(x, y) ∈ dualSquareGraph.edgeSet := by
    simpa [hdxy] using d.property
  simpa [SimpleGraph.mem_edgeSet] using hmem

noncomputable instance instFintypeSiteRectangleInterfaceDualGraphEdgeSet
    (m n : ℕ) (eta : Set SquareVertex) :
    Fintype (siteRectangleInterfaceDualGraph m n eta).edgeSet :=
  (siteRectangleInterfaceDualGraph_edgeSet_finite m n eta).fintype

noncomputable instance instFintypeSiteRectangleInterfaceDualGraphNeighborSet
    (m n : ℕ) (eta : Set SquareVertex) (z : DualSquareVertex) :
    Fintype ((siteRectangleInterfaceDualGraph m n eta).neighborSet z) := by
  classical
  let G := siteRectangleInterfaceDualGraph m n eta
  have hfinite : (G.incidenceSet z).Finite :=
    (siteRectangleInterfaceDualGraph_edgeSet_finite m n eta).subset
      (G.incidenceSet_subset z)
  letI : Fintype (G.incidenceSet z) := hfinite.fintype
  exact Fintype.ofEquiv (G.incidenceSet z) (G.incidenceSetEquivNeighborSet z)

/-- Explicit interface bonds incident to one shifted-dual vertex. -/
noncomputable def siteRectangleInterfaceDualEdgesIncident
    (m n : ℕ) (eta : Set SquareVertex) (z : DualSquareVertex) :
    Finset DualSquareEdge := by
  classical
  exact (siteRectangleInterfaceDualEdges m n eta).filter fun e ↦
    z ∈ (e : Sym2 DualSquareVertex)

/-- The interface graph's edge finset is the underlying endpoint set of the explicit dual
interface bonds. -/
theorem siteRectangleInterfaceDualGraph_edgeFinset_eq_map
    (m n : ℕ) (eta : Set SquareVertex) :
    (siteRectangleInterfaceDualGraph m n eta).edgeFinset =
      (siteRectangleInterfaceDualEdges m n eta).map dualSquareEdgeValEmbedding := by
  classical
  ext e
  rw [SimpleGraph.mem_edgeFinset, Finset.mem_map,
    mem_siteRectangleInterfaceDualGraph_edgeSet_iff]
  constructor
  · rintro ⟨hedual, hinterface⟩
    exact ⟨⟨e, hedual⟩, hinterface, rfl⟩
  · rintro ⟨d, hd, hde⟩
    subst hde
    exact ⟨d.property, hd⟩

theorem siteRectangleInterfaceDualGraph_incidenceFinset_eq_map
    (m n : ℕ) (eta : Set SquareVertex) (z : DualSquareVertex) :
    (siteRectangleInterfaceDualGraph m n eta).incidenceFinset z =
      (siteRectangleInterfaceDualEdgesIncident m n eta z).map
        dualSquareEdgeValEmbedding := by
  classical
  rw [SimpleGraph.incidenceFinset_eq_filter,
    siteRectangleInterfaceDualGraph_edgeFinset_eq_map]
  ext e
  rw [Finset.mem_filter, Finset.mem_map, Finset.mem_map]
  simp only [siteRectangleInterfaceDualEdgesIncident, Finset.mem_filter]
  constructor
  · rintro ⟨⟨d, hd, hde⟩, hz⟩
    subst hde
    exact ⟨d, ⟨hd, hz⟩, rfl⟩
  · rintro ⟨d, ⟨hd, hz⟩, hde⟩
    subst hde
    exact ⟨⟨d, hd, rfl⟩, hz⟩

theorem siteRectangleInterfaceDualGraph_degree_eq_card_incident
    (m n : ℕ) (eta : Set SquareVertex) (z : DualSquareVertex) :
    (siteRectangleInterfaceDualGraph m n eta).degree z =
      (siteRectangleInterfaceDualEdgesIncident m n eta z).card := by
  rw [← SimpleGraph.card_incidenceFinset_eq_degree,
    siteRectangleInterfaceDualGraph_incidenceFinset_eq_map, Finset.card_map]

/-- Incident interface dual bonds are the crossings of incident primal interface edges. -/
theorem siteRectangleInterfaceDualEdgesIncident_eq_map
    (m n : ℕ) (eta : Set SquareVertex) (z : DualSquareVertex) :
    siteRectangleInterfaceDualEdgesIncident m n eta z =
      ((siteRectangleInterfacePositiveEdges m n eta).filter fun b ↦
        b ∈ squareCellPositiveEdges z).map squarePositiveEdgeDualCrossingEmbedding := by
  classical
  ext d
  constructor
  · intro hd
    rw [siteRectangleInterfaceDualEdgesIncident, Finset.mem_filter] at hd
    rcases hd with ⟨hinterface, hz⟩
    rw [mem_siteRectangleInterfaceDualEdges_iff] at hinterface
    rcases hinterface with ⟨b, hb, hbd⟩
    rw [Finset.mem_map]
    refine ⟨b, ?_, hbd⟩
    rw [Finset.mem_filter]
    exact ⟨hb, (mem_squareCellPositiveEdges_iff_mem_crossing).mpr
      (by simpa [hbd] using hz)⟩
  · intro hd
    rw [Finset.mem_map] at hd
    rcases hd with ⟨b, hb, hbd⟩
    rw [Finset.mem_filter] at hb
    rw [siteRectangleInterfaceDualEdgesIncident, Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · rw [mem_siteRectangleInterfaceDualEdges_iff]
      exact ⟨b, hb.1, hbd⟩
    · simpa [← hbd] using (mem_squareCellPositiveEdges_iff_mem_crossing).mp hb.2

/-- At an interior cell, every cell-side bond belongs to the framed finite edge set. -/
theorem squareCellPositiveEdges_subset_siteRectangleFramedPositiveEdges
    {m n : ℕ} {z : DualSquareVertex}
    (hz : z ∈ siteRectangleInterfaceCells m n) :
    squareCellPositiveEdges z ⊆ siteRectangleFramedPositiveEdges m n := by
  intro e he
  rw [mem_siteRectangleFramedPositiveEdges_iff]
  exact ⟨z, hz, he⟩

/-- At an interior dual vertex, explicit incident interface edges are exactly the cell sides on
which framed reachability changes. -/
theorem siteRectangleInterfaceDualEdgesIncident_eq_cellBoundary
    {m n : ℕ} {eta : Set SquareVertex} {z : DualSquareVertex}
    (hz : z ∈ siteRectangleInterfaceCells m n) :
    siteRectangleInterfaceDualEdgesIncident m n eta z =
      ((squareCellPositiveEdges z).filter fun b ↦
        ¬(siteRectangleFramedReachable m n eta b.base ↔
          siteRectangleFramedReachable m n eta
            (cubicStepFrom b.base (b.axis, true)))).map
        squarePositiveEdgeDualCrossingEmbedding := by
  classical
  rw [siteRectangleInterfaceDualEdgesIncident_eq_map]
  congr 1
  ext b
  rw [Finset.mem_filter, Finset.mem_filter,
    mem_siteRectangleInterfacePositiveEdges_iff]
  constructor
  · rintro ⟨⟨_hframe, hchange⟩, hcell⟩
    exact ⟨hcell, hchange⟩
  · rintro ⟨hcell, hchange⟩
    exact ⟨⟨squareCellPositiveEdges_subset_siteRectangleFramedPositiveEdges hz hcell,
      hchange⟩, hcell⟩

/-- Every interior dual vertex has even interface degree. -/
theorem even_degree_siteRectangleInterfaceDualGraph_of_mem_cells
    {m n : ℕ} {eta : Set SquareVertex} {z : DualSquareVertex}
    (hz : z ∈ siteRectangleInterfaceCells m n) :
    Even ((siteRectangleInterfaceDualGraph m n eta).degree z) := by
  rw [siteRectangleInterfaceDualGraph_degree_eq_card_incident,
    siteRectangleInterfaceDualEdgesIncident_eq_cellBoundary hz, Finset.card_map]
  exact even_card_squareCellPositiveEdges_boundary
    (siteRectangleFramedReachable m n eta) z

/-! ### Odd bottom and top interfaces -/

/-- Indices at which a proposition changes between consecutive integers. -/
noncomputable def adjacentChangeIndices
    (P : ℤ → Prop) (a : ℤ) (k : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range k).filter fun j ↦
    ¬(P (a + (j : ℤ)) ↔ P (a + (j : ℤ) + 1))

/-- The parity of the number of adjacent changes records whether the two endpoint values differ. -/
theorem odd_card_adjacentChangeIndices_iff
    (P : ℤ → Prop) (a : ℤ) (k : ℕ) :
    Odd (adjacentChangeIndices P a k).card ↔
      ¬(P a ↔ P (a + (k : ℤ))) := by
  classical
  induction k with
  | zero => simp [adjacentChangeIndices]
  | succ k ih =>
      rw [adjacentChangeIndices, Finset.range_add_one, Finset.filter_insert]
      change
        Odd (if ¬(P (a + (k : ℤ)) ↔ P (a + (k : ℤ) + 1)) then
          insert k (adjacentChangeIndices P a k)
        else adjacentChangeIndices P a k).card ↔
          ¬(P a ↔ P (a + ((k + 1 : ℕ) : ℤ)))
      have hend : a + ((k + 1 : ℕ) : ℤ) = a + (k : ℤ) + 1 := by
        push_cast
        ring
      rw [hend]
      by_cases hlast : ¬(P (a + (k : ℤ)) ↔ P (a + (k : ℤ) + 1))
      · have hkNotMem : k ∉ adjacentChangeIndices P a k := by
          rw [adjacentChangeIndices, Finset.mem_filter]
          simp
        rw [if_pos hlast, Finset.card_insert_of_notMem hkNotMem, Nat.odd_add_one]
        rw [ih]
        tauto
      · rw [if_neg hlast]
        rw [ih]
        tauto

/-- Numbering of the horizontal positive edges from column `-1` to the right. -/
def framedHorizontalPositiveEdgeEmbedding (y : ℤ) : ℕ ↪ SquarePositiveEdge where
  toFun j := ⟨squareVertex ((j : ℤ) - 1) y, (0 : Fin 2)⟩
  inj' := by
    intro j k h
    have hbase := congrArg SquarePositiveEdge.base h
    have hcoord := congrFun hbase (0 : Fin 2)
    simp [squareVertex] at hcoord
    omega

/-- Horizontal interface edges on the bottom row of the rectangle. -/
noncomputable def siteRectangleBottomInterfacePositiveEdges
    (m n : ℕ) (eta : Set SquareVertex) : Finset SquarePositiveEdge :=
  (adjacentChangeIndices
    (fun x : ℤ ↦ siteRectangleFramedReachable m n eta
      (squareVertex x (-(n : ℤ)))) (-1) (m + 2)).map
    (framedHorizontalPositiveEdgeEmbedding (-(n : ℤ)))

/-- Horizontal interface edges on the top row of the rectangle. -/
noncomputable def siteRectangleTopInterfacePositiveEdges
    (m n : ℕ) (eta : Set SquareVertex) : Finset SquarePositiveEdge :=
  (adjacentChangeIndices
    (fun x : ℤ ↦ siteRectangleFramedReachable m n eta
      (squareVertex x (n : ℤ))) (-1) (m + 2)).map
    (framedHorizontalPositiveEdgeEmbedding (n : ℤ))

/-- A positive horizontal step increments the displayed first coordinate. -/
theorem cubicStepFrom_squareVertex_horizontal_pos (x y : ℤ) :
    cubicStepFrom (squareVertex x y) ((0 : Fin 2), true) =
      squareVertex (x + 1) y := by
  ext i
  fin_cases i <;> simp [squareVertex, cubicStepFrom, cubicDirectionIncrement]

/-- Every bottom-row change edge belongs to the finite framed interface. -/
theorem siteRectangleBottomInterfacePositiveEdges_subset_interface
    {m n : ℕ} {eta : Set SquareVertex} (hn : 0 < n) :
    siteRectangleBottomInterfacePositiveEdges m n eta ⊆
      siteRectangleInterfacePositiveEdges m n eta := by
  classical
  intro e he
  rw [siteRectangleBottomInterfacePositiveEdges, Finset.mem_map] at he
  rcases he with ⟨j, hj, rfl⟩
  rw [adjacentChangeIndices, Finset.mem_filter] at hj
  rcases hj with ⟨hjRange, hjChange⟩
  rw [mem_siteRectangleInterfacePositiveEdges_iff]
  constructor
  · rw [mem_siteRectangleFramedPositiveEdges_iff]
    let z : DualSquareVertex :=
      squareVertex ((j : ℤ) - 1) (-(n : ℤ))
    refine ⟨z, ?_, ?_⟩
    · rw [mem_siteRectangleInterfaceCells_iff]
      simp [z, squareVertex]
      have hjlt := Finset.mem_range.mp hjRange
      omega
    · change (⟨z, (0 : Fin 2)⟩ : SquarePositiveEdge) ∈ squareCellPositiveEdges z
      simp [squareCellPositiveEdges, squareCellPositiveEdgeList]
  · simpa [framedHorizontalPositiveEdgeEmbedding,
      cubicStepFrom_squareVertex_horizontal_pos] using hjChange

/-- Every top-row change edge belongs to the finite framed interface. -/
theorem siteRectangleTopInterfacePositiveEdges_subset_interface
    {m n : ℕ} {eta : Set SquareVertex} (hn : 0 < n) :
    siteRectangleTopInterfacePositiveEdges m n eta ⊆
      siteRectangleInterfacePositiveEdges m n eta := by
  classical
  intro e he
  rw [siteRectangleTopInterfacePositiveEdges, Finset.mem_map] at he
  rcases he with ⟨j, hj, rfl⟩
  rw [adjacentChangeIndices, Finset.mem_filter] at hj
  rcases hj with ⟨hjRange, hjChange⟩
  rw [mem_siteRectangleInterfacePositiveEdges_iff]
  constructor
  · rw [mem_siteRectangleFramedPositiveEdges_iff]
    let z : DualSquareVertex :=
      squareVertex ((j : ℤ) - 1) ((n : ℤ) - 1)
    refine ⟨z, ?_, ?_⟩
    · rw [mem_siteRectangleInterfaceCells_iff]
      simp [z, squareVertex]
      have hjlt := Finset.mem_range.mp hjRange
      omega
    · simp [squareCellPositiveEdges, squareCellPositiveEdgeList, z,
        framedHorizontalPositiveEdgeEmbedding, squareVertex]
  · simpa [framedHorizontalPositiveEdgeEmbedding,
      cubicStepFrom_squareVertex_horizontal_pos] using hjChange

/-- The bottom interface contains an odd number of primal bonds. -/
theorem odd_card_siteRectangleBottomInterfacePositiveEdges
    (m n : ℕ) (eta : Set SquareVertex) :
    Odd (siteRectangleBottomInterfacePositiveEdges m n eta).card := by
  rw [siteRectangleBottomInterfacePositiveEdges, Finset.card_map,
    odd_card_adjacentChangeIndices_iff]
  have hleft := siteRectangleFramedReachable_leftColumn
    m n eta (-(n : ℤ)) (by omega) (by omega)
  have hright := not_siteRectangleFramedReachable_rightColumn
    m n eta (-(n : ℤ)) (by omega) (by omega)
  intro hiff
  apply hright
  convert hiff.mp hleft using 1
  ext i
  fin_cases i <;> simp [squareVertex]
  push_cast
  ring

/-- The top interface contains an odd number of primal bonds. -/
theorem odd_card_siteRectangleTopInterfacePositiveEdges
    (m n : ℕ) (eta : Set SquareVertex) :
    Odd (siteRectangleTopInterfacePositiveEdges m n eta).card := by
  rw [siteRectangleTopInterfacePositiveEdges, Finset.card_map,
    odd_card_adjacentChangeIndices_iff]
  have hleft := siteRectangleFramedReachable_leftColumn
    m n eta (n : ℤ) (by omega) (by omega)
  have hright := not_siteRectangleFramedReachable_rightColumn
    m n eta (n : ℤ) (by omega) (by omega)
  intro hiff
  apply hright
  convert hiff.mp hleft using 1
  ext i
  fin_cases i <;> simp [squareVertex]
  push_cast
  ring

/-- A right side of an interface cell cannot lie on the permanently unreachable right wall. -/
theorem cellRight_base_lt_of_interface_change
    {m n : ℕ} {eta : Set SquareVertex} {c : DualSquareVertex}
    (hc : c ∈ siteRectangleInterfaceCells m n)
    (hchange :
      ¬(siteRectangleFramedReachable m n eta
          (squareVertex (c 0 + 1) (c 1)) ↔
        siteRectangleFramedReachable m n eta
          (cubicStepFrom (squareVertex (c 0 + 1) (c 1)) ((1 : Fin 2), true)))) :
    c 0 < (m : ℤ) := by
  rw [mem_siteRectangleInterfaceCells_iff] at hc
  by_contra hlt
  have hc0 : c 0 = (m : ℤ) := by omega
  have hbase :
      ¬siteRectangleFramedReachable m n eta (squareVertex (c 0 + 1) (c 1)) := by
    simpa [hc0] using not_siteRectangleFramedReachable_rightColumn
      m n eta (c 1) hc.2.2.1 (by omega)
  have hstep :
      ¬siteRectangleFramedReachable m n eta
        (cubicStepFrom (squareVertex (c 0 + 1) (c 1)) ((1 : Fin 2), true)) := by
    have hstepEq :
        cubicStepFrom (squareVertex (c 0 + 1) (c 1)) ((1 : Fin 2), true) =
          squareVertex ((m : ℤ) + 1) (c 1 + 1) := by
      ext i
      fin_cases i <;>
        simp [hc0, squareVertex, cubicStepFrom, cubicDirectionIncrement]
    rw [hstepEq]
    exact not_siteRectangleFramedReachable_rightColumn
      m n eta (c 1 + 1) (by omega) (by omega)
  apply hchange
  exact ⟨fun h ↦ False.elim (hbase h), fun h ↦ False.elim (hstep h)⟩

/-- A left side of an interface cell cannot lie on the permanently reachable left wall. -/
theorem neg_one_lt_cellLeft_base_of_interface_change
    {m n : ℕ} {eta : Set SquareVertex} {c : DualSquareVertex}
    (hc : c ∈ siteRectangleInterfaceCells m n)
    (hchange :
      ¬(siteRectangleFramedReachable m n eta c ↔
        siteRectangleFramedReachable m n eta
          (cubicStepFrom c ((1 : Fin 2), true)))) :
    (-1 : ℤ) < c 0 := by
  rw [mem_siteRectangleInterfaceCells_iff] at hc
  by_contra hlt
  have hc0 : c 0 = -1 := by omega
  have hcEq : c = squareVertex (-1) (c 1) := by
    ext i
    fin_cases i
    · simpa [squareVertex] using hc0
    · simp [squareVertex]
  have hbase : siteRectangleFramedReachable m n eta c := by
    rw [hcEq]
    exact siteRectangleFramedReachable_leftColumn
      m n eta (c 1) hc.2.2.1 (by omega)
  have hstep :
      siteRectangleFramedReachable m n eta (cubicStepFrom c ((1 : Fin 2), true)) := by
    have hstepEq : cubicStepFrom c ((1 : Fin 2), true) =
        squareVertex (-1) (c 1 + 1) := by
      rw [hcEq]
      ext i
      fin_cases i <;> simp [squareVertex, cubicStepFrom, cubicDirectionIncrement]
    rw [hstepEq]
    exact siteRectangleFramedReachable_leftColumn
      m n eta (c 1 + 1) (by omega) (by omega)
  apply hchange
  exact ⟨fun _ ↦ hstep, fun _ ↦ hbase⟩

/-- An endpoint cell of a dual interface bond is either an interior cell or lies immediately
below/above the rectangle.  The permanent left/right columns rule out lateral exterior cells. -/
theorem mem_cells_or_bottom_or_top_of_mem_interface_incident
    {m n : ℕ} {eta : Set SquareVertex} {b : SquarePositiveEdge}
    {z : DualSquareVertex}
    (hb : b ∈ siteRectangleInterfacePositiveEdges m n eta)
    (hz : z ∈ (squarePositiveEdgeDualCrossingEmbedding b : Sym2 DualSquareVertex)) :
    z ∈ siteRectangleInterfaceCells m n ∨
      (-1 ≤ z 0 ∧ z 0 ≤ (m : ℤ) ∧ z 1 = -(n : ℤ) - 1) ∨
        (-1 ≤ z 0 ∧ z 0 ≤ (m : ℤ) ∧ z 1 = (n : ℤ)) := by
  rw [mem_siteRectangleInterfacePositiveEdges_iff] at hb
  rcases (mem_siteRectangleFramedPositiveEdges_iff.mp hb.1) with ⟨c, hc, hbc⟩
  simp [squareCellPositiveEdges, squareCellPositiveEdgeList] at hbc
  rw [mem_siteRectangleInterfaceCells_iff] at hc
  rcases hbc with rfl | rfl | rfl | rfl
  ·
    simp [squarePositiveEdgeDualCrossingEmbedding, squareEdgeDualCrossingEquiv,
      SquarePositiveEdge.edgeEquiv_apply, squarePositiveEdgeDualCrossingEquiv,
      primalToDualCrossingPositiveEdge, SquarePositiveEdge.toEdge, squarePerp,
      cubicStepFrom, cubicDirectionIncrement] at hz
    rcases hz with hz | hz <;> subst z
    all_goals
      rw [mem_siteRectangleInterfaceCells_iff]
      try simp [squareVertex, Function.update_apply] at hc ⊢
      omega
  ·
    have hcRight : c 0 < (m : ℤ) :=
      cellRight_base_lt_of_interface_change
        (mem_siteRectangleInterfaceCells_iff.mpr hc) hb.2
    simp [squarePositiveEdgeDualCrossingEmbedding, squareEdgeDualCrossingEquiv,
      SquarePositiveEdge.edgeEquiv_apply, squarePositiveEdgeDualCrossingEquiv,
      primalToDualCrossingPositiveEdge, SquarePositiveEdge.toEdge, squarePerp,
      cubicStepFrom, cubicDirectionIncrement] at hz
    rcases hz with hz | hz <;> subst z
    all_goals
      rw [mem_siteRectangleInterfaceCells_iff]
      try simp [squareVertex, Function.update_apply] at hc ⊢
      omega
  ·
    simp [squarePositiveEdgeDualCrossingEmbedding, squareEdgeDualCrossingEquiv,
      SquarePositiveEdge.edgeEquiv_apply, squarePositiveEdgeDualCrossingEquiv,
      primalToDualCrossingPositiveEdge, SquarePositiveEdge.toEdge, squarePerp,
      cubicStepFrom, cubicDirectionIncrement] at hz
    rcases hz with hz | hz <;> subst z
    all_goals
      rw [mem_siteRectangleInterfaceCells_iff]
      try simp [squareVertex, Function.update_apply] at hc ⊢
      omega
  ·
    have hcLeft : (-1 : ℤ) < c 0 :=
      neg_one_lt_cellLeft_base_of_interface_change
        (mem_siteRectangleInterfaceCells_iff.mpr hc) hb.2
    simp [squarePositiveEdgeDualCrossingEmbedding, squareEdgeDualCrossingEquiv,
      SquarePositiveEdge.edgeEquiv_apply, squarePositiveEdgeDualCrossingEquiv,
      primalToDualCrossingPositiveEdge, SquarePositiveEdge.toEdge, squarePerp,
      cubicStepFrom, cubicDirectionIncrement] at hz
    rcases hz with hz | hz <;> subst z
    all_goals
      rw [mem_siteRectangleInterfaceCells_iff]
      try simp [squareVertex, Function.update_apply] at hc ⊢
      omega

/-- Numbering of exterior shifted-dual vertices immediately below the rectangle. -/
def bottomExteriorDualVertexEmbedding (n : ℕ) : ℕ ↪ DualSquareVertex where
  toFun j := squareVertex ((j : ℤ) - 1) (-(n : ℤ) - 1)
  inj' := by
    intro j k h
    have hcoord := congrFun h (0 : Fin 2)
    simp [squareVertex] at hcoord
    omega

/-- Numbering of exterior shifted-dual vertices immediately above the rectangle. -/
def topExteriorDualVertexEmbedding (n : ℕ) : ℕ ↪ DualSquareVertex where
  toFun j := squareVertex ((j : ℤ) - 1) (n : ℤ)
  inj' := by
    intro j k h
    have hcoord := congrFun h (0 : Fin 2)
    simp [squareVertex] at hcoord
    omega

/-- Bottom exterior vertices corresponding to bottom-row interface changes. -/
noncomputable def siteRectangleBottomInterfaceDualVertices
    (m n : ℕ) (eta : Set SquareVertex) : Finset DualSquareVertex :=
  (adjacentChangeIndices
    (fun x : ℤ ↦ siteRectangleFramedReachable m n eta
      (squareVertex x (-(n : ℤ)))) (-1) (m + 2)).map
    (bottomExteriorDualVertexEmbedding n)

/-- Top exterior vertices corresponding to top-row interface changes. -/
noncomputable def siteRectangleTopInterfaceDualVertices
    (m n : ℕ) (eta : Set SquareVertex) : Finset DualSquareVertex :=
  (adjacentChangeIndices
    (fun x : ℤ ↦ siteRectangleFramedReachable m n eta
      (squareVertex x (n : ℤ))) (-1) (m + 2)).map
    (topExteriorDualVertexEmbedding n)

theorem odd_card_siteRectangleBottomInterfaceDualVertices
    (m n : ℕ) (eta : Set SquareVertex) :
    Odd (siteRectangleBottomInterfaceDualVertices m n eta).card := by
  rw [siteRectangleBottomInterfaceDualVertices, Finset.card_map,
    odd_card_adjacentChangeIndices_iff]
  have hleft := siteRectangleFramedReachable_leftColumn
    m n eta (-(n : ℤ)) (by omega) (by omega)
  have hright := not_siteRectangleFramedReachable_rightColumn
    m n eta (-(n : ℤ)) (by omega) (by omega)
  intro hiff
  apply hright
  convert hiff.mp hleft using 1
  ext i
  fin_cases i <;> simp [squareVertex]
  push_cast
  ring

theorem odd_card_siteRectangleTopInterfaceDualVertices
    (m n : ℕ) (eta : Set SquareVertex) :
    Odd (siteRectangleTopInterfaceDualVertices m n eta).card := by
  rw [siteRectangleTopInterfaceDualVertices, Finset.card_map,
    odd_card_adjacentChangeIndices_iff]
  have hleft := siteRectangleFramedReachable_leftColumn
    m n eta (n : ℤ) (by omega) (by omega)
  have hright := not_siteRectangleFramedReachable_rightColumn
    m n eta (n : ℤ) (by omega) (by omega)
  intro hiff
  apply hright
  convert hiff.mp hleft using 1
  ext i
  fin_cases i <;> simp [squareVertex]
  push_cast
  ring

/-- A bottom exterior dual vertex is incident to at most its unique horizontal primal crossing. -/
theorem interfacePositiveEdge_eq_of_incident_bottom
    {m n : ℕ} {eta : Set SquareVertex} {b : SquarePositiveEdge}
    {z : DualSquareVertex}
    (hz0Lower : -1 ≤ z 0) (hz0Upper : z 0 ≤ (m : ℤ))
    (hz1 : z 1 = -(n : ℤ) - 1)
    (hb : b ∈ siteRectangleInterfacePositiveEdges m n eta)
    (hzb : z ∈ (squarePositiveEdgeDualCrossingEmbedding b : Sym2 DualSquareVertex)) :
    b = ⟨squareVertex (z 0) (-(n : ℤ)), (0 : Fin 2)⟩ := by
  rw [mem_siteRectangleInterfacePositiveEdges_iff] at hb
  rcases (mem_siteRectangleFramedPositiveEdges_iff.mp hb.1) with ⟨c, hc, hbc⟩
  rw [mem_siteRectangleInterfaceCells_iff] at hc
  simp [squareCellPositiveEdges, squareCellPositiveEdgeList] at hbc
  rcases hbc with rfl | rfl | rfl | rfl
  all_goals
    simp [squarePositiveEdgeDualCrossingEmbedding, squareEdgeDualCrossingEquiv,
      SquarePositiveEdge.edgeEquiv_apply, squarePositiveEdgeDualCrossingEquiv,
      primalToDualCrossingPositiveEdge, SquarePositiveEdge.toEdge, squarePerp,
      cubicStepFrom, cubicDirectionIncrement] at hzb
    rcases hzb with hzb | hzb <;> subst z
    all_goals
      simp [squareVertex, Function.update_apply] at hc hz0Lower hz0Upper hz1 ⊢
      first
      | omega
      | (ext i; fin_cases i <;> simp [squareVertex] <;> omega)

/-- A top exterior dual vertex is incident to at most its unique horizontal primal crossing. -/
theorem interfacePositiveEdge_eq_of_incident_top
    {m n : ℕ} {eta : Set SquareVertex} {b : SquarePositiveEdge}
    {z : DualSquareVertex}
    (hz0Lower : -1 ≤ z 0) (hz0Upper : z 0 ≤ (m : ℤ))
    (hz1 : z 1 = (n : ℤ))
    (hb : b ∈ siteRectangleInterfacePositiveEdges m n eta)
    (hzb : z ∈ (squarePositiveEdgeDualCrossingEmbedding b : Sym2 DualSquareVertex)) :
    b = ⟨squareVertex (z 0) (n : ℤ), (0 : Fin 2)⟩ := by
  rw [mem_siteRectangleInterfacePositiveEdges_iff] at hb
  rcases (mem_siteRectangleFramedPositiveEdges_iff.mp hb.1) with ⟨c, hc, hbc⟩
  rw [mem_siteRectangleInterfaceCells_iff] at hc
  simp [squareCellPositiveEdges, squareCellPositiveEdgeList] at hbc
  rcases hbc with rfl | rfl | rfl | rfl
  all_goals
    simp [squarePositiveEdgeDualCrossingEmbedding, squareEdgeDualCrossingEquiv,
      SquarePositiveEdge.edgeEquiv_apply, squarePositiveEdgeDualCrossingEquiv,
      primalToDualCrossingPositiveEdge, SquarePositiveEdge.toEdge, squarePerp,
      cubicStepFrom, cubicDirectionIncrement] at hzb
    rcases hzb with hzb | hzb <;> subst z
    all_goals
      simp [squareVertex, Function.update_apply] at hc hz0Lower hz0Upper hz1 ⊢
      first
      | omega
      | (ext i; fin_cases i <;> simp [squareVertex] <;> omega)

/-- Every selected bottom exterior interface vertex has degree one. -/
theorem degree_siteRectangleInterfaceDualGraph_eq_one_of_mem_bottom
    {m n : ℕ} {eta : Set SquareVertex} (hn : 0 < n) {z : DualSquareVertex}
    (hz : z ∈ siteRectangleBottomInterfaceDualVertices m n eta) :
    (siteRectangleInterfaceDualGraph m n eta).degree z = 1 := by
  classical
  rw [siteRectangleBottomInterfaceDualVertices, Finset.mem_map] at hz
  rcases hz with ⟨j, hj, rfl⟩
  let b : SquarePositiveEdge :=
    ⟨squareVertex ((j : ℤ) - 1) (-(n : ℤ)), (0 : Fin 2)⟩
  let d : DualSquareEdge := squarePositiveEdgeDualCrossingEmbedding b
  have hbBottom : b ∈ siteRectangleBottomInterfacePositiveEdges m n eta := by
    rw [siteRectangleBottomInterfacePositiveEdges, Finset.mem_map]
    exact ⟨j, hj, rfl⟩
  have hbInterface : b ∈ siteRectangleInterfacePositiveEdges m n eta :=
    siteRectangleBottomInterfacePositiveEdges_subset_interface hn hbBottom
  have hzCrossing :
      squareVertex ((j : ℤ) - 1) (-(n : ℤ) - 1) ∈
        (squarePositiveEdgeDualCrossingEmbedding b : Sym2 DualSquareVertex) := by
    apply mem_crossing_of_mem_squareCellPositiveEdges
    simp [squareCellPositiveEdges, squareCellPositiveEdgeList, b]
  rw [siteRectangleInterfaceDualGraph_degree_eq_card_incident]
  have hsingleton :
      siteRectangleInterfaceDualEdgesIncident m n eta
          (squareVertex ((j : ℤ) - 1) (-(n : ℤ) - 1)) = {d} := by
    ext e
    constructor
    · intro he
      rw [siteRectangleInterfaceDualEdgesIncident, Finset.mem_filter] at he
      rcases he with ⟨heInterface, hze⟩
      rw [mem_siteRectangleInterfaceDualEdges_iff] at heInterface
      rcases heInterface with ⟨b', hb', hb'e⟩
      have hb'eq : b' = b := by
        apply interfacePositiveEdge_eq_of_incident_bottom
          (z := squareVertex ((j : ℤ) - 1) (-(n : ℤ) - 1))
          (b := b') (m := m) (n := n) (eta := eta)
        · simp [squareVertex]
          have hjlt := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
          omega
        · simp [squareVertex]
          have hjlt := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
          omega
        · simp [squareVertex]
        · exact hb'
        · simpa [hb'e] using hze
      subst hb'eq
      simp [d, hb'e]
    · intro he
      rw [Finset.mem_singleton] at he
      subst e
      rw [siteRectangleInterfaceDualEdgesIncident, Finset.mem_filter]
      refine ⟨?_, hzCrossing⟩
      rw [mem_siteRectangleInterfaceDualEdges_iff]
      exact ⟨b, hbInterface, rfl⟩
  simpa [bottomExteriorDualVertexEmbedding] using congrArg Finset.card hsingleton

/-- Every selected top exterior interface vertex has degree one. -/
theorem degree_siteRectangleInterfaceDualGraph_eq_one_of_mem_top
    {m n : ℕ} {eta : Set SquareVertex} (hn : 0 < n) {z : DualSquareVertex}
    (hz : z ∈ siteRectangleTopInterfaceDualVertices m n eta) :
    (siteRectangleInterfaceDualGraph m n eta).degree z = 1 := by
  classical
  rw [siteRectangleTopInterfaceDualVertices, Finset.mem_map] at hz
  rcases hz with ⟨j, hj, rfl⟩
  let b : SquarePositiveEdge :=
    ⟨squareVertex ((j : ℤ) - 1) (n : ℤ), (0 : Fin 2)⟩
  let d : DualSquareEdge := squarePositiveEdgeDualCrossingEmbedding b
  have hbTop : b ∈ siteRectangleTopInterfacePositiveEdges m n eta := by
    rw [siteRectangleTopInterfacePositiveEdges, Finset.mem_map]
    exact ⟨j, hj, rfl⟩
  have hbInterface : b ∈ siteRectangleInterfacePositiveEdges m n eta :=
    siteRectangleTopInterfacePositiveEdges_subset_interface hn hbTop
  have hzCrossing :
      squareVertex ((j : ℤ) - 1) (n : ℤ) ∈
        (squarePositiveEdgeDualCrossingEmbedding b : Sym2 DualSquareVertex) := by
    apply mem_crossing_of_mem_squareCellPositiveEdges
    simp [squareCellPositiveEdges, squareCellPositiveEdgeList, b]
  rw [siteRectangleInterfaceDualGraph_degree_eq_card_incident]
  have hsingleton :
      siteRectangleInterfaceDualEdgesIncident m n eta
          (squareVertex ((j : ℤ) - 1) (n : ℤ)) = {d} := by
    ext e
    constructor
    · intro he
      rw [siteRectangleInterfaceDualEdgesIncident, Finset.mem_filter] at he
      rcases he with ⟨heInterface, hze⟩
      rw [mem_siteRectangleInterfaceDualEdges_iff] at heInterface
      rcases heInterface with ⟨b', hb', hb'e⟩
      have hb'eq : b' = b := by
        apply interfacePositiveEdge_eq_of_incident_top
          (z := squareVertex ((j : ℤ) - 1) (n : ℤ))
          (b := b') (m := m) (n := n) (eta := eta)
        · simp [squareVertex]
          have hjlt := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
          omega
        · simp [squareVertex]
          have hjlt := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
          omega
        · simp [squareVertex]
        · exact hb'
        · simpa [hb'e] using hze
      subst hb'eq
      simp [d, hb'e]
    · intro he
      rw [Finset.mem_singleton] at he
      subst e
      rw [siteRectangleInterfaceDualEdgesIncident, Finset.mem_filter]
      refine ⟨?_, hzCrossing⟩
      rw [mem_siteRectangleInterfaceDualEdges_iff]
      exact ⟨b, hbInterface, rfl⟩
  simpa [topExteriorDualVertexEmbedding] using congrArg Finset.card hsingleton

@[simp]
theorem mem_siteRectangleBottomInterfaceDualVertices_iff
    {m n : ℕ} {eta : Set SquareVertex} {z : DualSquareVertex} :
    z ∈ siteRectangleBottomInterfaceDualVertices m n eta ↔
      -1 ≤ z 0 ∧ z 0 ≤ (m : ℤ) ∧ z 1 = -(n : ℤ) - 1 ∧
        ¬(siteRectangleFramedReachable m n eta
            (squareVertex (z 0) (-(n : ℤ))) ↔
          siteRectangleFramedReachable m n eta
            (squareVertex (z 0 + 1) (-(n : ℤ)))) := by
  classical
  rw [siteRectangleBottomInterfaceDualVertices, Finset.mem_map]
  constructor
  · rintro ⟨j, hj, rfl⟩
    rw [adjacentChangeIndices, Finset.mem_filter] at hj
    rcases hj with ⟨hjRange, hjChange⟩
    have hjlt := Finset.mem_range.mp hjRange
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [bottomExteriorDualVertexEmbedding, squareVertex]
      omega
    · simp [bottomExteriorDualVertexEmbedding, squareVertex]
      omega
    · simp [bottomExteriorDualVertexEmbedding, squareVertex]
    · simpa [bottomExteriorDualVertexEmbedding, squareVertex] using hjChange
  · rintro ⟨hz0Lower, hz0Upper, hz1, hzChange⟩
    let j : ℕ := (z 0 + 1).toNat
    have hjCast : (j : ℤ) = z 0 + 1 := by
      have hnonneg : 0 ≤ z 0 + 1 := by omega
      simpa [j] using Int.toNat_of_nonneg hnonneg
    refine ⟨j, ?_, ?_⟩
    · rw [adjacentChangeIndices, Finset.mem_filter]
      constructor
      · rw [Finset.mem_range]
        omega
      · simpa [hjCast, squareVertex] using hzChange
    · ext i
      fin_cases i <;> simp [bottomExteriorDualVertexEmbedding, squareVertex, hjCast, hz1]

@[simp]
theorem mem_siteRectangleTopInterfaceDualVertices_iff
    {m n : ℕ} {eta : Set SquareVertex} {z : DualSquareVertex} :
    z ∈ siteRectangleTopInterfaceDualVertices m n eta ↔
      -1 ≤ z 0 ∧ z 0 ≤ (m : ℤ) ∧ z 1 = (n : ℤ) ∧
        ¬(siteRectangleFramedReachable m n eta
            (squareVertex (z 0) (n : ℤ)) ↔
          siteRectangleFramedReachable m n eta
            (squareVertex (z 0 + 1) (n : ℤ))) := by
  classical
  rw [siteRectangleTopInterfaceDualVertices, Finset.mem_map]
  constructor
  · rintro ⟨j, hj, rfl⟩
    rw [adjacentChangeIndices, Finset.mem_filter] at hj
    rcases hj with ⟨hjRange, hjChange⟩
    have hjlt := Finset.mem_range.mp hjRange
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [topExteriorDualVertexEmbedding, squareVertex]
      omega
    · simp [topExteriorDualVertexEmbedding, squareVertex]
      omega
    · simp [topExteriorDualVertexEmbedding, squareVertex]
    · simpa [topExteriorDualVertexEmbedding, squareVertex] using hjChange
  · rintro ⟨hz0Lower, hz0Upper, hz1, hzChange⟩
    let j : ℕ := (z 0 + 1).toNat
    have hjCast : (j : ℤ) = z 0 + 1 := by
      have hnonneg : 0 ≤ z 0 + 1 := by omega
      simpa [j] using Int.toNat_of_nonneg hnonneg
    refine ⟨j, ?_, ?_⟩
    · rw [adjacentChangeIndices, Finset.mem_filter]
      constructor
      · rw [Finset.mem_range]
        omega
      · simpa [hjCast, squareVertex] using hzChange
    · ext i
      fin_cases i <;> simp [topExteriorDualVertexEmbedding, squareVertex, hjCast, hz1]

/-- The odd-degree vertices of the finite interface graph are exactly its bottom and top
exterior change vertices. -/
theorem odd_degree_siteRectangleInterfaceDualGraph_iff
    {m n : ℕ} {eta : Set SquareVertex} (hn : 0 < n) (z : DualSquareVertex) :
    Odd ((siteRectangleInterfaceDualGraph m n eta).degree z) ↔
      z ∈ siteRectangleBottomInterfaceDualVertices m n eta ∨
        z ∈ siteRectangleTopInterfaceDualVertices m n eta := by
  constructor
  · intro hodd
    have hcardPos :
        0 < (siteRectangleInterfaceDualEdgesIncident m n eta z).card := by
      rw [← siteRectangleInterfaceDualGraph_degree_eq_card_incident]
      exact hodd.pos
    rcases Finset.card_pos.mp hcardPos with ⟨d, hd⟩
    rw [siteRectangleInterfaceDualEdgesIncident, Finset.mem_filter] at hd
    rcases hd with ⟨hdInterface, hzd⟩
    rw [mem_siteRectangleInterfaceDualEdges_iff] at hdInterface
    rcases hdInterface with ⟨b, hb, hbd⟩
    have hzb : z ∈
        (squarePositiveEdgeDualCrossingEmbedding b : Sym2 DualSquareVertex) := by
      simpa [hbd] using hzd
    rcases mem_cells_or_bottom_or_top_of_mem_interface_incident hb hzb with
      hzCell | hzBottom | hzTop
    · exact False.elim ((Nat.not_odd_iff_even.mpr
        (even_degree_siteRectangleInterfaceDualGraph_of_mem_cells hzCell)) hodd)
    · left
      rw [mem_siteRectangleBottomInterfaceDualVertices_iff]
      refine ⟨hzBottom.1, hzBottom.2.1, hzBottom.2.2, ?_⟩
      have hbEq := interfacePositiveEdge_eq_of_incident_bottom
        hzBottom.1 hzBottom.2.1 hzBottom.2.2 hb hzb
      rw [mem_siteRectangleInterfacePositiveEdges_iff] at hb
      simpa [hbEq, cubicStepFrom_squareVertex_horizontal_pos] using hb.2
    · right
      rw [mem_siteRectangleTopInterfaceDualVertices_iff]
      refine ⟨hzTop.1, hzTop.2.1, hzTop.2.2, ?_⟩
      have hbEq := interfacePositiveEdge_eq_of_incident_top
        hzTop.1 hzTop.2.1 hzTop.2.2 hb hzb
      rw [mem_siteRectangleInterfacePositiveEdges_iff] at hb
      simpa [hbEq, cubicStepFrom_squareVertex_horizontal_pos] using hb.2
  · rintro (hzBottom | hzTop)
    · rw [degree_siteRectangleInterfaceDualGraph_eq_one_of_mem_bottom hn hzBottom]
      exact odd_one
    · rw [degree_siteRectangleInterfaceDualGraph_eq_one_of_mem_top hn hzTop]
      exact odd_one

theorem disjoint_siteRectangleBottomInterfaceDualVertices_top
    (m n : ℕ) (eta : Set SquareVertex) :
    Disjoint (siteRectangleBottomInterfaceDualVertices m n eta)
      (siteRectangleTopInterfaceDualVertices m n eta) := by
  rw [Finset.disjoint_left]
  intro z hzBottom hzTop
  rw [mem_siteRectangleBottomInterfaceDualVertices_iff] at hzBottom
  rw [mem_siteRectangleTopInterfaceDualVertices_iff] at hzTop
  omega

namespace SimpleGraph

/-- In a finite-support graph, if the odd-degree vertices are partitioned into two classes and
the first class has odd cardinality, some graph component meets both classes. -/
theorem exists_reachable_between_of_odd_degree_partition
    {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]
    (hfinite : G.support.Finite) (B T : Finset V)
    (hBodd : Odd B.card)
    (hodd : ∀ v, Odd (G.degree v) ↔ v ∈ B ∨ v ∈ T) :
    ∃ b ∈ B, ∃ t ∈ T, G.Reachable b t := by
  classical
  by_contra hno
  push Not at hno
  let U : Set V := {v | ∃ b ∈ B, G.Reachable b v}
  have hUfinite : U.Finite := by
    refine (hfinite.union B.finite_toSet).subset ?_
    intro v hv
    rcases hv with ⟨b, hbB, hbv⟩
    by_cases hvb : v = b
    · exact Or.inr (by simpa [hvb] using hbB)
    · exact Or.inl (_root_.SimpleGraph.mem_support_of_reachable (G := G) hvb hbv.symm)
  letI : Fintype U := hUfinite.fintype
  let H : SimpleGraph U := G.induce U
  have hneighbor : ∀ x : U, G.neighborSet (x : V) ⊆ U := by
    intro x y hxy
    rcases x.property with ⟨b, hbB, hbx⟩
    exact ⟨b, hbB, hbx.trans hxy.reachable⟩
  have hdegree : ∀ x : U, H.degree x = G.degree (x : V) := by
    intro x
    exact _root_.SimpleGraph.degree_induce_of_neighborSet_subset_lf
      (G := G) (s := U) (v := x)
      (hneighbor x)
  let oddEquiv : {x : U // Odd (H.degree x)} ≃ {b : V // b ∈ B} :=
    { toFun := fun x ↦ ⟨x.1.1, by
          rcases (hodd x.1.1).mp (by simpa [hdegree] using x.2) with hxB | hxT
          · exact hxB
          · rcases x.1.2 with ⟨b, hbB, hbx⟩
            exact False.elim (hno b hbB x.1.1 hxT hbx)⟩
      invFun := fun b ↦
        ⟨⟨b.1, ⟨b.1, b.2,
          _root_.SimpleGraph.Reachable.refl (G := G) (u := b.1)⟩⟩, by
          rw [hdegree]
          exact (hodd b.1).mpr (Or.inl b.2)⟩
      left_inv := by intro x; ext; rfl
      right_inv := by intro b; ext; rfl }
  have hcard : #{x : U | Odd (H.degree x)} = B.card := by
    calc
      #{x : U | Odd (H.degree x)} = Fintype.card {x : U // Odd (H.degree x)} := by
        exact (Fintype.card_subtype fun x : U ↦ Odd (H.degree x)).symm
      _ = Fintype.card {b : V // b ∈ B} := Fintype.card_congr oddEquiv
      _ = B.card := Fintype.card_coe B
  have heven := H.even_card_odd_degree_vertices
  rw [hcard] at heven
  exact (Nat.not_odd_iff_even.mpr heven) hBodd

end SimpleGraph

/-- Some finite dual-interface component meets both the bottom and top of the rectangle. -/
theorem exists_interfaceDual_reachable_bottom_top
    {m n : ℕ} {eta : Set SquareVertex} (hn : 0 < n) :
    ∃ b ∈ siteRectangleBottomInterfaceDualVertices m n eta,
      ∃ t ∈ siteRectangleTopInterfaceDualVertices m n eta,
        (siteRectangleInterfaceDualGraph m n eta).Reachable b t := by
  apply SimpleGraph.exists_reachable_between_of_odd_degree_partition
    (siteRectangleInterfaceDualGraph_edgeSet_finite m n eta |>
      SimpleGraph.support_finite_of_edgeSet_finite)
    (siteRectangleBottomInterfaceDualVertices m n eta)
    (siteRectangleTopInterfaceDualVertices m n eta)
    (odd_card_siteRectangleBottomInterfaceDualVertices m n eta)
  intro z
  exact odd_degree_siteRectangleInterfaceDualGraph_iff hn z

/-! ### From a dual interface walk to a closed star walk -/

/-- The endpoint of a primal interface edge on the unreachable side of the framed predicate. -/
noncomputable def siteRectangleInterfaceUnreachableEndpoint
    (m n : ℕ) (eta : Set SquareVertex) (b : SquarePositiveEdge) : SquareVertex :=
  if siteRectangleFramedReachable m n eta b.base then
    cubicStepFrom b.base (b.axis, true)
  else b.base

/-- The endpoint of a primal interface edge on the reachable side of the framed predicate. -/
noncomputable def siteRectangleInterfaceReachableEndpoint
    (m n : ℕ) (eta : Set SquareVertex) (b : SquarePositiveEdge) : SquareVertex :=
  if siteRectangleFramedReachable m n eta b.base then b.base
  else cubicStepFrom b.base (b.axis, true)

theorem interfaceEndpoint_reachable_and_unreachable
    {m n : ℕ} {eta : Set SquareVertex} {b : SquarePositiveEdge}
    (hb : b ∈ siteRectangleInterfacePositiveEdges m n eta) :
    siteRectangleFramedReachable m n eta
        (siteRectangleInterfaceReachableEndpoint m n eta b) ∧
      ¬siteRectangleFramedReachable m n eta
        (siteRectangleInterfaceUnreachableEndpoint m n eta b) := by
  rw [mem_siteRectangleInterfacePositiveEdges_iff] at hb
  have hchange := hb.2
  by_cases hbase : siteRectangleFramedReachable m n eta b.base
  · constructor
    · simpa [siteRectangleInterfaceReachableEndpoint, hbase]
    · simp only [siteRectangleInterfaceUnreachableEndpoint, if_pos hbase]
      intro hstep
      exact hchange ⟨fun _ ↦ hstep, fun _ ↦ hbase⟩
  · constructor
    · simp only [siteRectangleInterfaceReachableEndpoint, if_neg hbase]
      by_contra hstep
      exact hchange ⟨fun h ↦ False.elim (hbase h), fun h ↦ False.elim (hstep h)⟩
    · simpa [siteRectangleInterfaceUnreachableEndpoint, hbase]

theorem interfaceEndpoint_adj
    (m n : ℕ) (eta : Set SquareVertex) (b : SquarePositiveEdge) :
    squareGraph.Adj
      (siteRectangleInterfaceReachableEndpoint m n eta b)
      (siteRectangleInterfaceUnreachableEndpoint m n eta b) := by
  by_cases hbase : siteRectangleFramedReachable m n eta b.base
  · simp [siteRectangleInterfaceReachableEndpoint,
      siteRectangleInterfaceUnreachableEndpoint, hbase]
    exact cubicGraph_adj_stepFrom b.base (b.axis, true)
  · simp [siteRectangleInterfaceReachableEndpoint,
      siteRectangleInterfaceUnreachableEndpoint, hbase]
    exact (cubicGraph_adj_stepFrom b.base (b.axis, true)).symm

/-- Both endpoints of a framed interface edge lie in the coordinate frame
`[-1,m+1] × [-n,n]`. -/
theorem interfacePositiveEdge_endpoint_mem_frame
    {m n : ℕ} {eta : Set SquareVertex} {b : SquarePositiveEdge}
    (hb : b ∈ siteRectangleInterfacePositiveEdges m n eta) :
    (-1 ≤ b.base 0 ∧ b.base 0 ≤ (m : ℤ) + 1 ∧
        -(n : ℤ) ≤ b.base 1 ∧ b.base 1 ≤ (n : ℤ)) ∧
      (-1 ≤ cubicStepFrom b.base (b.axis, true) 0 ∧
        cubicStepFrom b.base (b.axis, true) 0 ≤ (m : ℤ) + 1 ∧
        -(n : ℤ) ≤ cubicStepFrom b.base (b.axis, true) 1 ∧
        cubicStepFrom b.base (b.axis, true) 1 ≤ (n : ℤ)) := by
  rw [mem_siteRectangleInterfacePositiveEdges_iff] at hb
  rcases (mem_siteRectangleFramedPositiveEdges_iff.mp hb.1) with ⟨c, hc, hbc⟩
  rw [mem_siteRectangleInterfaceCells_iff] at hc
  simp [squareCellPositiveEdges, squareCellPositiveEdgeList] at hbc
  rcases hbc with rfl | rfl | rfl | rfl
  all_goals
    simp [squareVertex, cubicStepFrom, cubicDirectionIncrement] at hc ⊢
    omega

theorem interfaceUnreachableEndpoint_mem_frame
    {m n : ℕ} {eta : Set SquareVertex} {b : SquarePositiveEdge}
    (hb : b ∈ siteRectangleInterfacePositiveEdges m n eta) :
    -1 ≤ (siteRectangleInterfaceUnreachableEndpoint m n eta b) 0 ∧
      (siteRectangleInterfaceUnreachableEndpoint m n eta b) 0 ≤ (m : ℤ) + 1 ∧
      -(n : ℤ) ≤ (siteRectangleInterfaceUnreachableEndpoint m n eta b) 1 ∧
      (siteRectangleInterfaceUnreachableEndpoint m n eta b) 1 ≤ (n : ℤ) := by
  rcases interfacePositiveEdge_endpoint_mem_frame hb with ⟨hbase, hstep⟩
  by_cases h : siteRectangleFramedReachable m n eta b.base <;>
    simp [siteRectangleInterfaceUnreachableEndpoint, h, hbase, hstep]

theorem interfaceReachableEndpoint_mem_frame
    {m n : ℕ} {eta : Set SquareVertex} {b : SquarePositiveEdge}
    (hb : b ∈ siteRectangleInterfacePositiveEdges m n eta) :
    -1 ≤ (siteRectangleInterfaceReachableEndpoint m n eta b) 0 ∧
      (siteRectangleInterfaceReachableEndpoint m n eta b) 0 ≤ (m : ℤ) + 1 ∧
      -(n : ℤ) ≤ (siteRectangleInterfaceReachableEndpoint m n eta b) 1 ∧
      (siteRectangleInterfaceReachableEndpoint m n eta b) 1 ≤ (n : ℤ) := by
  rcases interfacePositiveEdge_endpoint_mem_frame hb with ⟨hbase, hstep⟩
  by_cases h : siteRectangleFramedReachable m n eta b.base <;>
    simp [siteRectangleInterfaceReachableEndpoint, h, hbase, hstep]

/-- Under crossing failure, the reachable endpoint of an interface edge cannot lie in the
permanently unreachable right column. -/
theorem interfaceReachableEndpoint_ne_rightColumn_of_not_crossing
    {m n : ℕ} {eta : Set SquareVertex} (hno : eta ∉ siteSquareRectangleCrossingEvent m n)
    {b : SquarePositiveEdge} (hb : b ∈ siteRectangleInterfacePositiveEdges m n eta) :
    (siteRectangleInterfaceReachableEndpoint m n eta b) 0 ≠ (m : ℤ) + 1 := by
  intro hxRight
  have hframe := interfaceReachableEndpoint_mem_frame hb
  have hreach := (interfaceEndpoint_reachable_and_unreachable hb).1
  let r := siteRectangleInterfaceReachableEndpoint m n eta b
  change siteRectangleFramedReachable m n eta r at hreach
  change -1 ≤ r 0 ∧ r 0 ≤ (m : ℤ) + 1 ∧
    -(n : ℤ) ≤ r 1 ∧ r 1 ≤ (n : ℤ) at hframe
  have hrEq : r = squareVertex ((m : ℤ) + 1) (r 1) := by
    ext i
    fin_cases i
    · simpa [r, squareVertex] using hxRight
    · simp [squareVertex]
  rw [hrEq] at hreach
  exact not_siteRectangleFramedReachable_rightColumn m n eta (r 1)
    hframe.2.2.1 hframe.2.2.2 hreach

/-- Under crossing failure, the unreachable endpoint of every interface edge is an actual
closed boundary site of the original rectangle. -/
theorem interfaceUnreachableEndpoint_mem_reachableBoundary_of_not_crossing
    {m n : ℕ} {eta : Set SquareVertex} (hno : eta ∉ siteSquareRectangleCrossingEvent m n)
    {b : SquarePositiveEdge} (hb : b ∈ siteRectangleInterfacePositiveEdges m n eta) :
    siteRectangleInterfaceUnreachableEndpoint m n eta b ∈
      siteRectangleLeftReachableBoundary m n eta := by
  let u := siteRectangleInterfaceUnreachableEndpoint m n eta b
  let r := siteRectangleInterfaceReachableEndpoint m n eta b
  have huFrame := interfaceUnreachableEndpoint_mem_frame hb
  have hrFrame := interfaceReachableEndpoint_mem_frame hb
  have hrReachable := (interfaceEndpoint_reachable_and_unreachable hb).1
  have huNotReachable := (interfaceEndpoint_reachable_and_unreachable hb).2
  change -1 ≤ u 0 ∧ u 0 ≤ (m : ℤ) + 1 ∧
    -(n : ℤ) ≤ u 1 ∧ u 1 ≤ (n : ℤ) at huFrame
  change -1 ≤ r 0 ∧ r 0 ≤ (m : ℤ) + 1 ∧
    -(n : ℤ) ≤ r 1 ∧ r 1 ≤ (n : ℤ) at hrFrame
  change siteRectangleFramedReachable m n eta r at hrReachable
  change ¬siteRectangleFramedReachable m n eta u at huNotReachable
  have hruAdj : squareGraph.Adj r u := interfaceEndpoint_adj m n eta b
  have hrRight : r 0 ≠ (m : ℤ) + 1 :=
    interfaceReachableEndpoint_ne_rightColumn_of_not_crossing hno hb
  have huNotLeft : u 0 ≠ -1 := by
    intro huLeft
    have huEq : u = squareVertex (-1) (u 1) := by
      ext i
      fin_cases i
      · simpa [squareVertex] using huLeft
      · simp [squareVertex]
    apply huNotReachable
    rw [huEq]
    exact siteRectangleFramedReachable_leftColumn m n eta (u 1)
      huFrame.2.2.1 huFrame.2.2.2
  have huLeftLower : (-1 : ℤ) < u 0 :=
    lt_of_le_of_ne huFrame.1 (Ne.symm huNotLeft)
  have hcoordDist : (u 0 - r 0).natAbs ≤ 1 := by
    have hdist : cubicL1Dist r u = 1 := by
      rcases (cubicGraph_adj_iff_exists_stepFrom r u).mp hruAdj with ⟨a, ha⟩
      rw [ha]
      exact cubicL1Dist_stepFrom r a
    exact (cubicL1Dist_coord_le r u (0 : Fin 2)).trans_eq hdist
  have hcoordDistInt : ((u 0 - r 0).natAbs : ℤ) ≤ 1 := by
    exact_mod_cast hcoordDist
  have hcoordUpper : u 0 - r 0 ≤ 1 :=
    Int.le_natAbs.trans hcoordDistInt
  have hnegLeNatAbs : -(u 0 - r 0) ≤ ((u 0 - r 0).natAbs : ℤ) := by
    have h := Int.le_natAbs (a := r 0 - u 0)
    rw [show r 0 - u 0 = -(u 0 - r 0) by ring, Int.natAbs_neg] at h
    exact h
  have hcoordLower : -(u 0 - r 0) ≤ 1 :=
    hnegLeNatAbs.trans hcoordDistInt
  have huNotRight : u 0 ≠ (m : ℤ) + 1 := by
    intro huRight
    have hrLower : (m : ℤ) ≤ r 0 := by
      omega
    have hrEq : r 0 = (m : ℤ) := by omega
    have hrRect : r ∈ squareRectangleVertices m n := by
      rw [mem_squareRectangleVertices_iff]
      exact ⟨by omega, hrEq.le, hrFrame.2.2.1, hrFrame.2.2.2⟩
    have hrOrdinary : r ∈ siteRectangleLeftReachableVertices m n eta :=
      (siteRectangleFramedReachable_iff_reachable_of_mem_rectangle hrRect).mp hrReachable
    have hrRightFace : r ∈ squareRectangleRight m n := by
      rw [mem_squareRectangleRight_iff]
      exact ⟨hrEq, hrFrame.2.2.1, hrFrame.2.2.2⟩
    exact hno ((mem_siteSquareRectangleCrossingEvent_iff_exists_mem_right_reachable
      m n eta).mpr ⟨r, hrRightFace, hrOrdinary⟩)
  have huRect : u ∈ squareRectangleVertices m n := by
    rw [mem_squareRectangleVertices_iff]
    exact ⟨by omega, by omega, huFrame.2.2.1, huFrame.2.2.2⟩
  have huOrdinary : u ∉ siteRectangleLeftReachableVertices m n eta := by
    intro huReachable
    exact huNotReachable ((siteRectangleFramedReachable_iff_reachable_of_mem_rectangle
      huRect).mpr huReachable)
  rw [mem_siteRectangleLeftReachableBoundary_iff]
  refine ⟨huRect, huOrdinary, ?_⟩
  by_cases hrLeft : r 0 = -1
  · left
    rw [mem_squareRectangleLeft_iff]
    have huZero : u 0 = 0 := by omega
    exact ⟨huZero, huFrame.2.2.1, huFrame.2.2.2⟩
  · right
    have hrRect : r ∈ squareRectangleVertices m n := by
      rw [mem_squareRectangleVertices_iff]
      exact ⟨by omega, by omega, hrFrame.2.2.1, hrFrame.2.2.2⟩
    have hrOrdinary : r ∈ siteRectangleLeftReachableVertices m n eta :=
      (siteRectangleFramedReachable_iff_reachable_of_mem_rectangle hrRect).mp hrReachable
    exact ⟨r, hrOrdinary, hruAdj⟩

theorem interfaceUnreachableEndpoint_not_mem_of_not_crossing
    {m n : ℕ} {eta : Set SquareVertex} (hno : eta ∉ siteSquareRectangleCrossingEvent m n)
    {b : SquarePositiveEdge} (hb : b ∈ siteRectangleInterfacePositiveEdges m n eta) :
    siteRectangleInterfaceUnreachableEndpoint m n eta b ∉ eta :=
  not_mem_of_mem_siteRectangleLeftReachableBoundary
    (interfaceUnreachableEndpoint_mem_reachableBoundary_of_not_crossing hno hb)

/-- A cell-side endpoint is one of the four corners of that unit cell. -/
theorem squareCell_endpoint_coordinate_bounds
    {z : DualSquareVertex} {b : SquarePositiveEdge} {x : SquareVertex}
    (hb : b ∈ squareCellPositiveEdges z)
    (hx : x = b.base ∨ x = cubicStepFrom b.base (b.axis, true)) :
    z 0 ≤ x 0 ∧ x 0 ≤ z 0 + 1 ∧ z 1 ≤ x 1 ∧ x 1 ≤ z 1 + 1 := by
  simp [squareCellPositiveEdges, squareCellPositiveEdgeList] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> rcases hx with rfl | rfl
  all_goals
    simp [squareVertex, cubicStepFrom, cubicDirectionIncrement]

theorem interfaceUnreachableEndpoint_is_cell_corner
    {m n : ℕ} {eta : Set SquareVertex} {z : DualSquareVertex}
    {b : SquarePositiveEdge}
    (hz : z ∈ (squarePositiveEdgeDualCrossingEmbedding b : Sym2 DualSquareVertex)) :
    z 0 ≤ (siteRectangleInterfaceUnreachableEndpoint m n eta b) 0 ∧
      (siteRectangleInterfaceUnreachableEndpoint m n eta b) 0 ≤ z 0 + 1 ∧
      z 1 ≤ (siteRectangleInterfaceUnreachableEndpoint m n eta b) 1 ∧
      (siteRectangleInterfaceUnreachableEndpoint m n eta b) 1 ≤ z 1 + 1 := by
  apply squareCell_endpoint_coordinate_bounds
    ((mem_squareCellPositiveEdges_iff_mem_crossing).mpr hz)
  by_cases h : siteRectangleFramedReachable m n eta b.base
  · exact Or.inr (by simp [siteRectangleInterfaceUnreachableEndpoint, h])
  · exact Or.inl (by simp [siteRectangleInterfaceUnreachableEndpoint, h])

/-- Unreachable endpoints of two interface edges incident to the same dual cell are equal or
star-adjacent. -/
theorem interfaceUnreachableEndpoint_eq_or_starAdj_of_common_incident
    {m n : ℕ} {eta : Set SquareVertex} {z : DualSquareVertex}
    {b c : SquarePositiveEdge}
    (hzb : z ∈ (squarePositiveEdgeDualCrossingEmbedding b : Sym2 DualSquareVertex))
    (hzc : z ∈ (squarePositiveEdgeDualCrossingEmbedding c : Sym2 DualSquareVertex)) :
    siteRectangleInterfaceUnreachableEndpoint m n eta b =
        siteRectangleInterfaceUnreachableEndpoint m n eta c ∨
      squareStarGraph.Adj
        (siteRectangleInterfaceUnreachableEndpoint m n eta b)
        (siteRectangleInterfaceUnreachableEndpoint m n eta c) := by
  let u := siteRectangleInterfaceUnreachableEndpoint m n eta b
  let v := siteRectangleInterfaceUnreachableEndpoint m n eta c
  by_cases huv : u = v
  · exact Or.inl huv
  · right
    rw [squareStarGraph_adj_iff]
    refine ⟨huv, ?_⟩
    have hu := interfaceUnreachableEndpoint_is_cell_corner (m := m) (n := n)
      (eta := eta) hzb
    have hv := interfaceUnreachableEndpoint_is_cell_corner (m := m) (n := n)
      (eta := eta) hzc
    change z 0 ≤ u 0 ∧ u 0 ≤ z 0 + 1 ∧ z 1 ≤ u 1 ∧ u 1 ≤ z 1 + 1 at hu
    change z 0 ≤ v 0 ∧ v 0 ≤ z 0 + 1 ∧ z 1 ≤ v 1 ∧ v 1 ≤ z 1 + 1 at hv
    rw [cubicLInfDist]
    apply Finset.sup_le
    intro i _hi
    fin_cases i
    · by_cases hnonneg : 0 ≤ v 0 - u 0
      · have hcast : ((v 0 - u 0).natAbs : ℤ) ≤ 1 := by
          rw [Int.natAbs_of_nonneg hnonneg]
          omega
        exact_mod_cast hcast
      · have hcast : ((v 0 - u 0).natAbs : ℤ) ≤ 1 := by
          rw [Int.ofNat_natAbs_of_nonpos (le_of_not_ge hnonneg)]
          omega
        exact_mod_cast hcast
    · by_cases hnonneg : 0 ≤ v 1 - u 1
      · have hcast : ((v 1 - u 1).natAbs : ℤ) ≤ 1 := by
          rw [Int.natAbs_of_nonneg hnonneg]
          omega
        exact_mod_cast hcast
      · have hcast : ((v 1 - u 1).natAbs : ℤ) ≤ 1 := by
          rw [Int.ofNat_natAbs_of_nonpos (le_of_not_ge hnonneg)]
          omega
        exact_mod_cast hcast

/-- Boundary sites viewed as vertices of the induced star graph. -/
abbrev SiteRectangleBoundaryVertex (m n : ℕ) (eta : Set SquareVertex) :=
  {x : SquareVertex // x ∈ siteRectangleLeftReachableBoundary m n eta}

/-- Star adjacency restricted to the finite closed reachable boundary. -/
abbrev siteRectangleBoundaryStarGraph
    (m n : ℕ) (eta : Set SquareVertex) :
    SimpleGraph (SiteRectangleBoundaryVertex m n eta) :=
  squareStarGraph.induce
    (siteRectangleLeftReachableBoundary m n eta : Set SquareVertex)

/-- An interface edge supplies a vertex of the induced closed-boundary star graph. -/
noncomputable def interfaceUnreachableBoundaryVertex
    {m n : ℕ} {eta : Set SquareVertex}
    (hno : eta ∉ siteSquareRectangleCrossingEvent m n)
    (b : SquarePositiveEdge)
    (hb : b ∈ siteRectangleInterfacePositiveEdges m n eta) :
    SiteRectangleBoundaryVertex m n eta :=
  ⟨siteRectangleInterfaceUnreachableEndpoint m n eta b,
    interfaceUnreachableEndpoint_mem_reachableBoundary_of_not_crossing hno hb⟩

/-- Interface edges incident to the same dual vertex give connected boundary-star vertices. -/
theorem interfaceUnreachableBoundaryVertex_reachable_of_common_incident
    {m n : ℕ} {eta : Set SquareVertex}
    (hno : eta ∉ siteSquareRectangleCrossingEvent m n)
    {z : DualSquareVertex} {b c : SquarePositiveEdge}
    (hb : b ∈ siteRectangleInterfacePositiveEdges m n eta)
    (hc : c ∈ siteRectangleInterfacePositiveEdges m n eta)
    (hzb : z ∈ (squarePositiveEdgeDualCrossingEmbedding b : Sym2 DualSquareVertex))
    (hzc : z ∈ (squarePositiveEdgeDualCrossingEmbedding c : Sym2 DualSquareVertex)) :
    (siteRectangleBoundaryStarGraph m n eta).Reachable
      (interfaceUnreachableBoundaryVertex hno b hb)
      (interfaceUnreachableBoundaryVertex hno c hc) := by
  rcases interfaceUnreachableEndpoint_eq_or_starAdj_of_common_incident hzb hzc with
    heq | hadj
  · have hsubtype : interfaceUnreachableBoundaryVertex hno b hb =
        interfaceUnreachableBoundaryVertex hno c hc := by
      apply Subtype.ext
      exact heq
    simpa [hsubtype] using
      (SimpleGraph.Reachable.refl (G := siteRectangleBoundaryStarGraph m n eta)
        (u := interfaceUnreachableBoundaryVertex hno b hb))
  · exact ((SimpleGraph.induce_adj).mpr hadj).reachable

/-- Every interface-graph edge is the crossing of a unique primal interface edge. -/
theorem exists_interfacePositiveEdge_of_interfaceDualGraph_adj
    {m n : ℕ} {eta : Set SquareVertex} {z w : DualSquareVertex}
    (hzw : (siteRectangleInterfaceDualGraph m n eta).Adj z w) :
    ∃ b ∈ siteRectangleInterfacePositiveEdges m n eta,
      squarePositiveEdgeDualCrossingEmbedding b =
        (⟨s(z, w), by
          rw [SimpleGraph.mem_edgeSet]
          exact (siteRectangleInterfaceDualGraph_le_dualSquareGraph m n eta hzw)⟩ :
          DualSquareEdge) := by
  have hedge : s(z, w) ∈ (siteRectangleInterfaceDualGraph m n eta).edgeSet := by
    rw [SimpleGraph.mem_edgeSet]
    exact hzw
  rw [mem_siteRectangleInterfaceDualGraph_edgeSet_iff] at hedge
  rcases hedge with ⟨hedual, hinterface⟩
  rw [mem_siteRectangleInterfaceDualEdges_iff] at hinterface
  rcases hinterface with ⟨b, hb, hbeq⟩
  refine ⟨b, hb, ?_⟩
  apply Subtype.ext
  exact congrArg Subtype.val hbeq

/-- A nonempty walk in the dual interface graph yields two endpoint interface edges whose
unreachable boundary sites are connected in the induced star graph. -/
theorem exists_boundaryStar_reachable_of_interfaceDualGraph_walk
    {m n : ℕ} {eta : Set SquareVertex}
    (hno : eta ∉ siteSquareRectangleCrossingEvent m n)
    {z w : DualSquareVertex}
    (p : (siteRectangleInterfaceDualGraph m n eta).Walk z w)
    (hp : 0 < p.length) :
    ∃ b : SquarePositiveEdge,
      ∃ hb : b ∈ siteRectangleInterfacePositiveEdges m n eta,
        ∃ c : SquarePositiveEdge,
          ∃ hc : c ∈ siteRectangleInterfacePositiveEdges m n eta,
            z ∈ (squarePositiveEdgeDualCrossingEmbedding b : Sym2 DualSquareVertex) ∧
              w ∈ (squarePositiveEdgeDualCrossingEmbedding c : Sym2 DualSquareVertex) ∧
                (siteRectangleBoundaryStarGraph m n eta).Reachable
                  (interfaceUnreachableBoundaryVertex hno b hb)
                  (interfaceUnreachableBoundaryVertex hno c hc) := by
  induction p with
  | nil => simp at hp
  | @cons z y w hzy q ih =>
      rcases exists_interfacePositiveEdge_of_interfaceDualGraph_adj hzy with
        ⟨b, hb, hbeq⟩
      have hzb : z ∈
          (squarePositiveEdgeDualCrossingEmbedding b : Sym2 DualSquareVertex) := by
        rw [hbeq]
        simp
      have hyb : y ∈
          (squarePositiveEdgeDualCrossingEmbedding b : Sym2 DualSquareVertex) := by
        rw [hbeq]
        simp
      cases q with
      | nil =>
          refine ⟨b, hb, b, hb, hzb, hyb, ?_⟩
          exact SimpleGraph.Reachable.refl
            (G := siteRectangleBoundaryStarGraph m n eta)
            (u := interfaceUnreachableBoundaryVertex hno b hb)
      | @cons y v w hyv r =>
          rcases ih (by simp) with ⟨c, hc, e, he, hyc, hwe, hce⟩
          refine ⟨b, hb, e, he, hzb, hwe, ?_⟩
          exact (interfaceUnreachableBoundaryVertex_reachable_of_common_incident
            hno hb hc hyb hyc).trans hce

/-- Deterministic planar crossing alternative: if the open-site left-right crossing fails, a
self-avoiding closed star path crosses the rectangle from bottom to top. -/
theorem exists_closed_squareStar_path_bottom_top_of_not_crossing
    {m n : ℕ} {eta : Set SquareVertex} (hn : 0 < n)
    (hno : eta ∉ siteSquareRectangleCrossingEvent m n) :
    ∃ x y : SquareVertex,
      x ∈ squareRectangleVertices m n ∧ x 1 = -(n : ℤ) ∧
        y ∈ squareRectangleVertices m n ∧ y 1 = (n : ℤ) ∧
          ∃ w : squareStarGraph.Walk x y,
            w.IsPath ∧
              (∀ z ∈ w.support,
                z ∈ siteRectangleLeftReachableBoundary m n eta) ∧
              ∀ z ∈ w.support, z ∉ eta := by
  rcases exists_interfaceDual_reachable_bottom_top (eta := eta) hn with
    ⟨zBottom, hzBottom, zTop, hzTop, hdualReachable⟩
  have hztNe : zBottom ≠ zTop := by
    intro hzt
    subst zTop
    exact (Finset.disjoint_left.mp
      (disjoint_siteRectangleBottomInterfaceDualVertices_top m n eta))
      hzBottom hzTop
  let p := Classical.choice hdualReachable
  have hp : 0 < p.length := by
    apply Nat.pos_of_ne_zero
    intro hp0
    exact hztNe (SimpleGraph.Walk.eq_of_length_eq_zero hp0)
  rcases exists_boundaryStar_reachable_of_interfaceDualGraph_walk hno p hp with
    ⟨b, hb, c, hc, hzb, hzc, hstarReachable⟩
  let x := siteRectangleInterfaceUnreachableEndpoint m n eta b
  let y := siteRectangleInterfaceUnreachableEndpoint m n eta c
  have hxBoundary :=
    interfaceUnreachableEndpoint_mem_reachableBoundary_of_not_crossing hno hb
  have hyBoundary :=
    interfaceUnreachableEndpoint_mem_reachableBoundary_of_not_crossing hno hc
  have hzBottomData :=
    (mem_siteRectangleBottomInterfaceDualVertices_iff.mp hzBottom)
  have hzTopData :=
    (mem_siteRectangleTopInterfaceDualVertices_iff.mp hzTop)
  have hbEq := interfacePositiveEdge_eq_of_incident_bottom
    hzBottomData.1 hzBottomData.2.1 hzBottomData.2.2.1 hb hzb
  have hcEq := interfacePositiveEdge_eq_of_incident_top
    hzTopData.1 hzTopData.2.1 hzTopData.2.2.1 hc hzc
  subst b
  subst c
  have hxRow : x 1 = -(n : ℤ) := by
    by_cases hbase : siteRectangleFramedReachable m n eta
        (squareVertex (zBottom 0) (-(n : ℤ))) <;>
      simp [x, siteRectangleInterfaceUnreachableEndpoint, hbase,
        squareVertex, cubicStepFrom, cubicDirectionIncrement]
  have hyRow : y 1 = (n : ℤ) := by
    by_cases hbase : siteRectangleFramedReachable m n eta
        (squareVertex (zTop 0) (n : ℤ)) <;>
      simp [y, siteRectangleInterfaceUnreachableEndpoint, hbase,
        squareVertex, cubicStepFrom, cubicDirectionIncrement]
  have hxRect :=
    (mem_siteRectangleLeftReachableBoundary_iff m n eta x).mp hxBoundary |>.1
  have hyRect :=
    (mem_siteRectangleLeftReachableBoundary_iff m n eta y).mp hyBoundary |>.1
  let q := Classical.choice hstarReachable
  let qAmbient : squareStarGraph.Walk x y :=
    q.map (SimpleGraph.Embedding.induce
      (siteRectangleLeftReachableBoundary m n eta : Set SquareVertex)).toHom
  let w : squareStarGraph.Walk x y := qAmbient.toPath
  refine ⟨x, y, hxRect, hxRow, hyRect, hyRow, w, qAmbient.toPath.property, ?_, ?_⟩
  · intro v hv
    have hvAmbient : v ∈ qAmbient.support := qAmbient.support_toPath_subset hv
    change v ∈ (q.map (SimpleGraph.Embedding.induce
      (siteRectangleLeftReachableBoundary m n eta : Set SquareVertex)).toHom).support at hvAmbient
    rw [SimpleGraph.Walk.support_map] at hvAmbient
    rcases List.mem_map.mp hvAmbient with ⟨v', _hv', hv'⟩
    rw [← hv']
    exact v'.property
  · intro v hv
    apply not_mem_of_mem_siteRectangleLeftReachableBoundary
    have hvAmbient : v ∈ qAmbient.support := qAmbient.support_toPath_subset hv
    change v ∈ (q.map (SimpleGraph.Embedding.induce
      (siteRectangleLeftReachableBoundary m n eta : Set SquareVertex)).toHom).support at hvAmbient
    rw [SimpleGraph.Walk.support_map] at hvAmbient
    rcases List.mem_map.mp hvAmbient with ⟨v', _hv', hv'⟩
    rw [← hv']
    exact v'.property

end

end Percolation
