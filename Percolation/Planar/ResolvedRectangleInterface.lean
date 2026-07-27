import Percolation.Planar.SiteCrossingInterface

/-!
# Resolved rectangle interfaces

At a checkerboard cell, the ordinary dual-interface graph has degree four and forgets which
two boundary strands should be paired. This file splits those four incidences according to the
reachable corner while leaving an ordinary degree-two cell unsplit.
-/

namespace Percolation

noncomputable section

/-- Cell sides across which a vertex predicate changes value. -/
def squareCellBoundaryPositiveEdges
    (P : SquareVertex → Prop) [DecidablePred P] (z : DualSquareVertex) :
    Finset SquarePositiveEdge :=
  (squareCellPositiveEdges z).filter fun b ↦
    ¬(P b.base ↔ P (cubicStepFrom b.base (b.axis, true)))

/-- The endpoint satisfying `P` on a cell side where `P` changes value. -/
def squareCellBoundaryTrueEndpoint
    (P : SquareVertex → Prop) [DecidablePred P] (b : SquarePositiveEdge) : SquareVertex :=
  if P b.base then b.base else cubicStepFrom b.base (b.axis, true)

/-- Degree-four cell boundaries are split by their `P`-true corner; degree-two boundaries are
left as one strand. -/
def squareCellBoundarySplitTag
    (P : SquareVertex → Prop) [DecidablePred P] (z : DualSquareVertex)
    (b : SquarePositiveEdge) : Option SquareVertex :=
  if (squareCellBoundaryPositiveEdges P z).card = 4 then
    some (squareCellBoundaryTrueEndpoint P b)
  else none

/-- A square cell has exactly four positively oriented boundary edges. -/
theorem card_squareCellPositiveEdges_eq_four (z : DualSquareVertex) :
    (squareCellPositiveEdges z).card = 4 := by
  classical
  simpa [squareCellPositiveEdges, squareCellPositiveEdgeList] using
    (List.toFinset_card_of_nodup (squareCellPositiveEdgeList_nodup z))

/-- A nonempty cell boundary that is not the degree-four checkerboard case has degree two. -/
theorem card_squareCellBoundaryPositiveEdges_eq_two_of_mem_of_ne_four
    (P : SquareVertex → Prop) [DecidablePred P] (z : DualSquareVertex)
    {b : SquarePositiveEdge} (hb : b ∈ squareCellBoundaryPositiveEdges P z)
    (hfour : (squareCellBoundaryPositiveEdges P z).card ≠ 4) :
    (squareCellBoundaryPositiveEdges P z).card = 2 := by
  have heven : Even (squareCellBoundaryPositiveEdges P z).card := by
    simpa [squareCellBoundaryPositiveEdges] using
      (even_card_squareCellPositiveEdges_boundary P z)
  have hpos : 0 < (squareCellBoundaryPositiveEdges P z).card :=
    Finset.card_pos.mpr ⟨b, hb⟩
  have hsubset : squareCellBoundaryPositiveEdges P z ⊆ squareCellPositiveEdges z := by
    intro c hc
    simpa [squareCellBoundaryPositiveEdges] using (Finset.mem_of_mem_filter c hc)
  have hle : (squareCellBoundaryPositiveEdges P z).card ≤ 4 := by
    calc
      (squareCellBoundaryPositiveEdges P z).card ≤ (squareCellPositiveEdges z).card :=
        Finset.card_le_card hsubset
      _ = 4 := card_squareCellPositiveEdges_eq_four z
  rcases heven with ⟨k, hk⟩
  omega

/-- In the degree-four checkerboard case, the split tags give one of the two noncrossing
pairings of the four cyclically ordered sides. -/
theorem squareCellBoundarySplitTag_pairing_of_card_eq_four
    (P : SquareVertex → Prop) [DecidablePred P] (z : DualSquareVertex)
    (hfour : (squareCellBoundaryPositiveEdges P z).card = 4) :
    let se : SquareVertex := squareVertex (z 0 + 1) (z 1)
    let nw : SquareVertex := squareVertex (z 0) (z 1 + 1)
    let bottom : SquarePositiveEdge := ⟨z, (0 : Fin 2)⟩
    let right : SquarePositiveEdge := ⟨se, (1 : Fin 2)⟩
    let top : SquarePositiveEdge := ⟨nw, (0 : Fin 2)⟩
    let left : SquarePositiveEdge := ⟨z, (1 : Fin 2)⟩
    (squareCellBoundarySplitTag P z bottom = squareCellBoundarySplitTag P z left ∧
        squareCellBoundarySplitTag P z right = squareCellBoundarySplitTag P z top ∧
        squareCellBoundarySplitTag P z bottom ≠ squareCellBoundarySplitTag P z right) ∨
      (squareCellBoundarySplitTag P z bottom = squareCellBoundarySplitTag P z right ∧
        squareCellBoundarySplitTag P z top = squareCellBoundarySplitTag P z left ∧
        squareCellBoundarySplitTag P z bottom ≠ squareCellBoundarySplitTag P z top) := by
  dsimp only
  let se : SquareVertex := squareVertex (z 0 + 1) (z 1)
  let nw : SquareVertex := squareVertex (z 0) (z 1 + 1)
  let ne : SquareVertex := squareVertex (z 0 + 1) (z 1 + 1)
  have hbottom : cubicStepFrom z ((0 : Fin 2), true) = se := by
    ext i
    fin_cases i <;> simp [se, cubicStepFrom, cubicDirectionIncrement]
  have hright : cubicStepFrom se ((1 : Fin 2), true) = ne := by
    ext i
    fin_cases i <;> simp [se, ne, cubicStepFrom, cubicDirectionIncrement]
  have htop : cubicStepFrom nw ((0 : Fin 2), true) = ne := by
    ext i
    fin_cases i <;> simp [nw, ne, cubicStepFrom, cubicDirectionIncrement]
  have hleft : cubicStepFrom z ((1 : Fin 2), true) = nw := by
    ext i
    fin_cases i <;> simp [nw, cubicStepFrom, cubicDirectionIncrement]
  have hz_ne : z ≠ ne := by
    intro h
    have hcoord := congrFun h (0 : Fin 2)
    simp [ne] at hcoord
  have hse_nw : se ≠ nw := by
    intro h
    have hcoord := congrFun h (0 : Fin 2)
    simp [se, nw] at hcoord
  have hsubset : squareCellBoundaryPositiveEdges P z ⊆ squareCellPositiveEdges z := by
    intro c hc
    simpa [squareCellBoundaryPositiveEdges] using (Finset.mem_of_mem_filter c hc)
  have hboundary_eq :
      squareCellBoundaryPositiveEdges P z = squareCellPositiveEdges z := by
    apply Finset.eq_of_subset_of_card_le hsubset
    rw [card_squareCellPositiveEdges_eq_four, hfour]
  have hallchange {c : SquarePositiveEdge} (hc : c ∈ squareCellPositiveEdges z) :
      ¬(P c.base ↔ P (cubicStepFrom c.base (c.axis, true))) := by
    have hc' : c ∈ squareCellBoundaryPositiveEdges P z := by
      rw [hboundary_eq]
      exact hc
    rw [squareCellBoundaryPositiveEdges, Finset.mem_filter] at hc'
    exact hc'.2
  have hbottomChange : ¬(P z ↔ P se) := by
    have h := hallchange (c := (⟨z, (0 : Fin 2)⟩ : SquarePositiveEdge)) (by
      simp [squareCellPositiveEdges, squareCellPositiveEdgeList])
    simpa [hbottom] using h
  have hrightChange : ¬(P se ↔ P ne) := by
    have h := hallchange (c := (⟨se, (1 : Fin 2)⟩ : SquarePositiveEdge)) (by
      simp [squareCellPositiveEdges, squareCellPositiveEdgeList, se])
    simpa [hright] using h
  have hleftChange : ¬(P z ↔ P nw) := by
    have h := hallchange (c := (⟨z, (1 : Fin 2)⟩ : SquarePositiveEdge)) (by
      simp [squareCellPositiveEdges, squareCellPositiveEdgeList])
    simpa [hleft] using h
  by_cases hz : P z
  · have hse : ¬P se := by simpa [hz] using hbottomChange
    have hnw : ¬P nw := by simpa [hz] using hleftChange
    have hne : P ne := by simpa [hse] using hrightChange
    left
    simp [squareCellBoundarySplitTag, squareCellBoundaryTrueEndpoint, hfour,
      se, nw, ne, hright, htop, hz_ne, hz, hse, hnw]
  · have hse : P se := by simpa [hz] using hbottomChange
    have hnw : P nw := by simpa [hz] using hleftChange
    have hne : ¬P ne := by simpa [hse] using hrightChange
    right
    simp [squareCellBoundarySplitTag, squareCellBoundaryTrueEndpoint, hfour,
      se, nw, hbottom, hleft, hse_nw, hz, hse, hnw]

end

end Percolation
