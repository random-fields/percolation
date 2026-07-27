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

private theorem card_filter_eq_two_of_nodup_four_pairing
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (a b c d : α) (f : α → β) (hnodup : [a, b, c, d].Nodup)
    (hpair :
      (f a = f d ∧ f b = f c ∧ f a ≠ f b) ∨
        (f a = f b ∧ f c = f d ∧ f a ≠ f c))
    {x : α} (hx : x ∈ [a, b, c, d]) :
    (([a, b, c, d].toFinset).filter fun y ↦ f y = f x).card = 2 := by
  simp at hx
  rcases hpair with ⟨had, hbc, hab⟩ | ⟨hab, hcd, hac⟩
  · rcases hx with rfl | rfl | rfl | rfl
    · apply Finset.card_eq_two.mpr
      refine ⟨x, d, ?_, ?_⟩
      · simp_all
      · ext y
        simp_all [eq_comm]
        grind
    · apply Finset.card_eq_two.mpr
      refine ⟨x, c, ?_, ?_⟩
      · simp_all
      · ext y
        simp_all [eq_comm]
        grind
    · apply Finset.card_eq_two.mpr
      refine ⟨b, x, ?_, ?_⟩
      · simp_all
      · ext y
        simp_all [eq_comm]
        grind
    · apply Finset.card_eq_two.mpr
      refine ⟨a, x, ?_, ?_⟩
      · simp_all
      · ext y
        simp_all [eq_comm]
        grind
  · rcases hx with rfl | rfl | rfl | rfl
    · apply Finset.card_eq_two.mpr
      refine ⟨x, b, ?_, ?_⟩
      · simp_all
      · ext y
        simp_all [eq_comm]
        grind
    · apply Finset.card_eq_two.mpr
      refine ⟨a, x, ?_, ?_⟩
      · simp_all
      · ext y
        simp_all [eq_comm]
        grind
    · apply Finset.card_eq_two.mpr
      refine ⟨x, d, ?_, ?_⟩
      · simp_all
      · ext y
        simp_all [eq_comm]
        grind
    · apply Finset.card_eq_two.mpr
      refine ⟨c, x, ?_, ?_⟩
      · simp_all
      · ext y
        simp_all [eq_comm]
        grind

/-- Every boundary edge belongs to a split-tag fiber of cardinality two. -/
theorem card_squareCellBoundaryPositiveEdges_filter_splitTag_eq_two
    (P : SquareVertex → Prop) [DecidablePred P] (z : DualSquareVertex)
    {b : SquarePositiveEdge} (hb : b ∈ squareCellBoundaryPositiveEdges P z) :
    ((squareCellBoundaryPositiveEdges P z).filter fun c ↦
      squareCellBoundarySplitTag P z c = squareCellBoundarySplitTag P z b).card = 2 := by
  classical
  by_cases hfour : (squareCellBoundaryPositiveEdges P z).card = 4
  · let se : SquareVertex := squareVertex (z 0 + 1) (z 1)
    let nw : SquareVertex := squareVertex (z 0) (z 1 + 1)
    let bottom : SquarePositiveEdge := ⟨z, (0 : Fin 2)⟩
    let right : SquarePositiveEdge := ⟨se, (1 : Fin 2)⟩
    let top : SquarePositiveEdge := ⟨nw, (0 : Fin 2)⟩
    let left : SquarePositiveEdge := ⟨z, (1 : Fin 2)⟩
    have hsubset : squareCellBoundaryPositiveEdges P z ⊆ squareCellPositiveEdges z := by
      intro c hc
      simpa [squareCellBoundaryPositiveEdges] using (Finset.mem_of_mem_filter c hc)
    have hboundary_eq :
        squareCellBoundaryPositiveEdges P z = squareCellPositiveEdges z := by
      apply Finset.eq_of_subset_of_card_le hsubset
      rw [card_squareCellPositiveEdges_eq_four, hfour]
    have hnodup : [bottom, right, top, left].Nodup := by
      simpa [bottom, right, top, left, se, nw, squareCellPositiveEdgeList] using
        (squareCellPositiveEdgeList_nodup z)
    have hpair :
        (squareCellBoundarySplitTag P z bottom = squareCellBoundarySplitTag P z left ∧
            squareCellBoundarySplitTag P z right = squareCellBoundarySplitTag P z top ∧
            squareCellBoundarySplitTag P z bottom ≠
              squareCellBoundarySplitTag P z right) ∨
          (squareCellBoundarySplitTag P z bottom = squareCellBoundarySplitTag P z right ∧
            squareCellBoundarySplitTag P z top = squareCellBoundarySplitTag P z left ∧
            squareCellBoundarySplitTag P z bottom ≠
              squareCellBoundarySplitTag P z top) := by
      simpa [bottom, right, top, left, se, nw] using
        (squareCellBoundarySplitTag_pairing_of_card_eq_four P z hfour)
    have hbcell : b ∈ squareCellPositiveEdges z := hsubset hb
    have hblist : b ∈ [bottom, right, top, left] := by
      simpa [squareCellPositiveEdges, squareCellPositiveEdgeList,
        bottom, right, top, left, se, nw] using hbcell
    have hfiber := card_filter_eq_two_of_nodup_four_pairing
      bottom right top left (squareCellBoundarySplitTag P z) hnodup hpair hblist
    rw [hboundary_eq]
    simpa only [squareCellPositiveEdges, squareCellPositiveEdgeList,
      bottom, right, top, left, se, nw] using hfiber
  · have hcard :=
      card_squareCellBoundaryPositiveEdges_eq_two_of_mem_of_ne_four P z hb hfour
    simpa [squareCellBoundarySplitTag, hfour] using hcard

private theorem existsUnique_mem_ne_of_card_eq_two
    {α : Type*} [DecidableEq α] {s : Finset α} {b : α}
    (hb : b ∈ s) (hcard : s.card = 2) :
    ∃! c, c ∈ s ∧ c ≠ b := by
  rcases Finset.card_eq_two.mp hcard with ⟨x, y, hxy, rfl⟩
  have hb' : b = x ∨ b = y := by simpa using hb
  rcases hb' with hbx | hby
  · refine ⟨y, ⟨by simp, ?_⟩, ?_⟩
    · intro hyb
      exact hxy (hbx.symm.trans hyb.symm)
    intro c hc
    have hc' : c = x ∨ c = y := by simpa using hc.1
    rcases hc' with hcx | hcy
    · exact (hc.2 (hcx.trans hbx.symm)).elim
    · exact hcy
  · refine ⟨x, ⟨by simp, ?_⟩, ?_⟩
    · intro hxb
      exact hxy (hxb.trans hby)
    intro c hc
    have hc' : c = x ∨ c = y := by simpa using hc.1
    rcases hc' with hcx | hcy
    · exact hcx
    · exact (hc.2 (hcy.trans hby.symm)).elim

/-- Every cell-boundary edge has a unique distinct partner with the same split tag. This is the
local successor relation used by a resolved interface graph on interface bonds. -/
theorem existsUnique_squareCellBoundaryPositiveEdge_partner
    (P : SquareVertex → Prop) [DecidablePred P] (z : DualSquareVertex)
    {b : SquarePositiveEdge} (hb : b ∈ squareCellBoundaryPositiveEdges P z) :
    ∃! c : SquarePositiveEdge,
      c ∈ squareCellBoundaryPositiveEdges P z ∧ c ≠ b ∧
        squareCellBoundarySplitTag P z c = squareCellBoundarySplitTag P z b := by
  classical
  let fiber := (squareCellBoundaryPositiveEdges P z).filter fun c ↦
    squareCellBoundarySplitTag P z c = squareCellBoundarySplitTag P z b
  have hbFiber : b ∈ fiber := by
    simp [fiber, hb]
  have hcard : fiber.card = 2 := by
    simpa [fiber] using
      (card_squareCellBoundaryPositiveEdges_filter_splitTag_eq_two P z hb)
  rcases existsUnique_mem_ne_of_card_eq_two hbFiber hcard with ⟨c, hc, hunique⟩
  refine ⟨c, ?_, ?_⟩
  · have hcmem := Finset.mem_filter.mp hc.1
    exact ⟨hcmem.1, hc.2, hcmem.2⟩
  · intro d hd
    apply hunique d
    exact ⟨Finset.mem_filter.mpr ⟨hd.1, hd.2.2⟩, hd.2.1⟩

end

end Percolation
