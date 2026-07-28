import Percolation.Planar.BRTruncatedPorts

namespace Percolation

noncomputable section

theorem brTruncatedResolvedIncidentCells_eq_horizontal_pair
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (d : BRTruncatedInterfaceEdge n R)
    (haxis : d.1.axis = (0 : Fin 2)) :
    brTruncatedResolvedIncidentCells d =
      ({squareVertex (d.1.base 0) (d.1.base 1 - 1), d.1.base} :
        Finset DualSquareVertex).filter (fun z ↦ z ∈ brTruncatedBoundaryCells n) := by
  classical
  rcases d with ⟨⟨base, axis⟩, hd⟩
  change axis = 0 at haxis
  subst axis
  ext z
  rw [mem_brTruncatedResolvedIncidentCells_iff]
  simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hz, hzcell⟩
    refine ⟨?_, hzcell⟩
    rw [brStoppedInterfaceIncidentAt, squareCellBoundaryPositiveEdges,
      Finset.mem_filter] at hz
    have hz' : ({ base := base, axis := (0 : Fin 2) } : SquarePositiveEdge) ∈
        squareCellPositiveEdges z := by
      simpa using hz.1
    have hz'' : base = z ∨ base = squareVertex (z 0) (z 1 + 1) := by
      simpa [squareCellPositiveEdges, squareCellPositiveEdgeList, squareVertex] using hz'
    rcases hz'' with h | h
    · exact Or.inr h.symm
    · left
      have h0 := congrFun h (0 : Fin 2)
      have h1 := congrFun h (1 : Fin 2)
      ext i
      fin_cases i <;> simp [squareVertex] at h0 h1 ⊢ <;> omega
  · rintro ⟨hz, hzcell⟩
    refine ⟨?_, hzcell⟩
    rw [brStoppedInterfaceIncidentAt, squareCellBoundaryPositiveEdges,
      Finset.mem_filter]
    refine ⟨?_, (mem_brTruncatedDualBoundaryPositiveEdges_iff.mp hd).1⟩
    rcases hz with hz | hz
    · subst z
      change ({ base := base, axis := (0 : Fin 2) } : SquarePositiveEdge) ∈
        squareCellPositiveEdges (squareVertex (base 0) (base 1 - 1))
      simp [squareCellPositiveEdges, squareCellPositiveEdgeList]
    · subst z
      change ({ base := base, axis := (0 : Fin 2) } : SquarePositiveEdge) ∈
        squareCellPositiveEdges base
      simp [squareCellPositiveEdges, squareCellPositiveEdgeList]

theorem brTruncatedResolvedIncidentCells_eq_vertical_pair
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (d : BRTruncatedInterfaceEdge n R)
    (haxis : d.1.axis = (1 : Fin 2)) :
    brTruncatedResolvedIncidentCells d =
      ({squareVertex (d.1.base 0 - 1) (d.1.base 1), d.1.base} :
        Finset DualSquareVertex).filter (fun z ↦ z ∈ brTruncatedBoundaryCells n) := by
  classical
  rcases d with ⟨⟨base, axis⟩, hd⟩
  change axis = 1 at haxis
  subst axis
  ext z
  rw [mem_brTruncatedResolvedIncidentCells_iff]
  simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hz, hzcell⟩
    refine ⟨?_, hzcell⟩
    rw [brStoppedInterfaceIncidentAt, squareCellBoundaryPositiveEdges,
      Finset.mem_filter] at hz
    have hz' : ({ base := base, axis := (1 : Fin 2) } : SquarePositiveEdge) ∈
        squareCellPositiveEdges z := by
      simpa using hz.1
    have hz'' : base = squareVertex (z 0 + 1) (z 1) ∨ base = z := by
      simpa [squareCellPositiveEdges, squareCellPositiveEdgeList, squareVertex] using hz'
    rcases hz'' with h | h
    · left
      have h0 := congrFun h (0 : Fin 2)
      have h1 := congrFun h (1 : Fin 2)
      ext i
      fin_cases i <;> simp [squareVertex] at h0 h1 ⊢ <;> omega
    · exact Or.inr h.symm
  · rintro ⟨hz, hzcell⟩
    refine ⟨?_, hzcell⟩
    rw [brStoppedInterfaceIncidentAt, squareCellBoundaryPositiveEdges,
      Finset.mem_filter]
    refine ⟨?_, (mem_brTruncatedDualBoundaryPositiveEdges_iff.mp hd).1⟩
    rcases hz with hz | hz
    · subst z
      change ({ base := base, axis := (1 : Fin 2) } : SquarePositiveEdge) ∈
        squareCellPositiveEdges (squareVertex (base 0 - 1) (base 1))
      simp [squareCellPositiveEdges, squareCellPositiveEdgeList]
    · subst z
      change ({ base := base, axis := (1 : Fin 2) } : SquarePositiveEdge) ∈
        squareCellPositiveEdges base
      simp [squareCellPositiveEdges, squareCellPositiveEdgeList]

theorem card_brTruncatedResolvedIncidentCells_horizontal
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)} (hn : 0 < n)
    (d : BRTruncatedInterfaceEdge n R) (haxis : d.1.axis = (0 : Fin 2)) :
    (brTruncatedResolvedIncidentCells d).card =
      if d.1.base 1 = -(n : ℤ) ∨ d.1.base 1 = (n : ℤ) - 1 then 1 else 2 := by
  classical
  rw [brTruncatedResolvedIncidentCells_eq_horizontal_pair d haxis]
  have htrunc := mem_brTruncatedDualBoundaryPositiveEdges_iff.mp d.2
  have hbase := mem_brLeftmostDualFaces_iff.mp htrunc.2.1
  have hstep := mem_brLeftmostDualFaces_iff.mp htrunc.2.2.1
  rw [haxis] at hstep
  simp [cubicStepFrom, cubicDirectionIncrement] at hstep
  have hlower :
      squareVertex (d.1.base 0) (d.1.base 1 - 1) ∈ brTruncatedBoundaryCells n ↔
        -(n : ℤ) < d.1.base 1 := by
    rw [mem_brTruncatedBoundaryCells_iff]
    simp [squareVertex]
    omega
  have hupper : d.1.base ∈ brTruncatedBoundaryCells n ↔
      d.1.base 1 < (n : ℤ) - 1 := by
    rw [mem_brTruncatedBoundaryCells_iff]
    omega
  have hne : squareVertex (d.1.base 0) (d.1.base 1 - 1) ≠ d.1.base := by
    intro h
    have h1 := congrFun h (1 : Fin 2)
    simp [squareVertex] at h1
  simp only [Finset.filter_insert, Finset.filter_singleton]
  simp [hlower, hupper]
  split_ifs <;> simp [hne] <;> omega

theorem card_brTruncatedResolvedIncidentCells_vertical
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (d : BRTruncatedInterfaceEdge n R) (haxis : d.1.axis = (1 : Fin 2)) :
    (brTruncatedResolvedIncidentCells d).card =
      if d.1.base 0 = -1 ∨ d.1.base 0 = 2 * (n : ℤ) then 1 else 2 := by
  classical
  rw [brTruncatedResolvedIncidentCells_eq_vertical_pair d haxis]
  have htrunc := mem_brTruncatedDualBoundaryPositiveEdges_iff.mp d.2
  have hbase := mem_brLeftmostDualFaces_iff.mp htrunc.2.1
  have hstep := mem_brLeftmostDualFaces_iff.mp htrunc.2.2.1
  rw [haxis] at hstep
  simp [cubicStepFrom, cubicDirectionIncrement] at hstep
  have hleft :
      squareVertex (d.1.base 0 - 1) (d.1.base 1) ∈ brTruncatedBoundaryCells n ↔
        -1 < d.1.base 0 := by
    rw [mem_brTruncatedBoundaryCells_iff]
    simp [squareVertex]
    omega
  have hright : d.1.base ∈ brTruncatedBoundaryCells n ↔
      d.1.base 0 < 2 * (n : ℤ) := by
    rw [mem_brTruncatedBoundaryCells_iff]
    omega
  have hne : squareVertex (d.1.base 0 - 1) (d.1.base 1) ≠ d.1.base := by
    intro h
    have h0 := congrFun h (0 : Fin 2)
    simp [squareVertex] at h0
  simp only [Finset.filter_insert, Finset.filter_singleton]
  simp [hleft, hright]
  split_ifs <;> simp [hne] <;> omega

/-- Exactly one of the two incident cells survives precisely at one of the four frame ports. -/
theorem card_brTruncatedResolvedIncidentCells_eq_one_iff_ports
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)} (hn : 0 < n)
    (d : BRTruncatedInterfaceEdge n R) :
    (brTruncatedResolvedIncidentCells d).card = 1 ↔
      d.1 ∈ brTruncatedBottomBoundaryEdges n R ∨
        d.1 ∈ brTruncatedTopBoundaryEdges n R ∨
          d.1 ∈ brTruncatedLeftBoundaryEdges n R ∨
            d.1 ∈ brTruncatedRightBoundaryEdges n R := by
  by_cases haxis : d.1.axis = (0 : Fin 2)
  · rw [card_brTruncatedResolvedIncidentCells_horizontal hn d haxis]
    simp [haxis, d.2]
    tauto
  · have haxis' : d.1.axis = (1 : Fin 2) := by
      omega
    rw [card_brTruncatedResolvedIncidentCells_vertical d haxis']
    simp [haxis', d.2]
    tauto

/-- Every retained edge has either one or two incident cells after truncation. -/
theorem card_brTruncatedResolvedIncidentCells_eq_one_or_two
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)} (hn : 0 < n)
    (d : BRTruncatedInterfaceEdge n R) :
    (brTruncatedResolvedIncidentCells d).card = 1 ∨
      (brTruncatedResolvedIncidentCells d).card = 2 := by
  by_cases haxis : d.1.axis = (0 : Fin 2)
  · rw [card_brTruncatedResolvedIncidentCells_horizontal hn d haxis]
    split_ifs <;> simp
  · have haxis' : d.1.axis = (1 : Fin 2) := by omega
    rw [card_brTruncatedResolvedIncidentCells_vertical d haxis']
    split_ifs <;> simp

/-- Away from the four frame ports, both incident cells survive the truncation. -/
theorem card_brTruncatedResolvedIncidentCells_eq_two_iff_not_ports
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)} (hn : 0 < n)
    (d : BRTruncatedInterfaceEdge n R) :
    (brTruncatedResolvedIncidentCells d).card = 2 ↔
      ¬(d.1 ∈ brTruncatedBottomBoundaryEdges n R ∨
        d.1 ∈ brTruncatedTopBoundaryEdges n R ∨
          d.1 ∈ brTruncatedLeftBoundaryEdges n R ∨
            d.1 ∈ brTruncatedRightBoundaryEdges n R) := by
  constructor
  · intro htwo hport
    have hone := (card_brTruncatedResolvedIncidentCells_eq_one_iff_ports hn d).mpr hport
    omega
  · intro hnot
    rcases card_brTruncatedResolvedIncidentCells_eq_one_or_two hn d with hone | htwo
    · exact False.elim (hnot
        ((card_brTruncatedResolvedIncidentCells_eq_one_iff_ports hn d).mp hone))
    · exact htwo

/-! ### Degrees on an admissible separating fiber -/

/-- In the separating case, the degree-one vertices are exactly the bottom and top ports. -/
theorem degree_brTruncatedResolvedBoundaryGraph_eq_one_iff
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)} (hn : 0 < n)
    (hR : BRAdmissibleSeparatingFiber n R) (d : BRTruncatedInterfaceEdge n R) :
    (brTruncatedResolvedBoundaryGraph n R).degree d = 1 ↔
      d ∈ brTruncatedBottomBoundaryVertices n R ∨
        d ∈ brTruncatedTopBoundaryVertices n R := by
  rw [degree_brTruncatedResolvedBoundaryGraph hR.1 d,
    card_brTruncatedResolvedIncidentCells_eq_one_iff_ports hn d]
  rw [brTruncatedLeftBoundaryEdges_eq_empty_of_separating hR.separatingReachedSet,
    brTruncatedRightBoundaryEdges_eq_empty_of_separating hR.separatingReachedSet]
  simp

/-- Every truncated resolved-boundary vertex has degree one or degree two. -/
theorem degree_brTruncatedResolvedBoundaryGraph_eq_one_or_two
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)} (hn : 0 < n)
    (hR : BRAdmissibleSeparatingFiber n R) (d : BRTruncatedInterfaceEdge n R) :
    (brTruncatedResolvedBoundaryGraph n R).degree d = 1 ∨
      (brTruncatedResolvedBoundaryGraph n R).degree d = 2 := by
  rw [degree_brTruncatedResolvedBoundaryGraph hR.1 d]
  exact card_brTruncatedResolvedIncidentCells_eq_one_or_two hn d

/-- The non-port vertices of a separating truncated boundary have degree two. -/
theorem degree_brTruncatedResolvedBoundaryGraph_eq_two_iff
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)} (hn : 0 < n)
    (hR : BRAdmissibleSeparatingFiber n R) (d : BRTruncatedInterfaceEdge n R) :
    (brTruncatedResolvedBoundaryGraph n R).degree d = 2 ↔
      d ∉ brTruncatedBottomBoundaryVertices n R ∧
        d ∉ brTruncatedTopBoundaryVertices n R := by
  rw [degree_brTruncatedResolvedBoundaryGraph hR.1 d,
    card_brTruncatedResolvedIncidentCells_eq_two_iff_not_ports hn d]
  rw [brTruncatedLeftBoundaryEdges_eq_empty_of_separating hR.separatingReachedSet,
    brTruncatedRightBoundaryEdges_eq_empty_of_separating hR.separatingReachedSet]
  simp

/-- Odd degree is equivalent to belonging to one of the two horizontal port sets. -/
theorem odd_degree_brTruncatedResolvedBoundaryGraph_iff
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)} (hn : 0 < n)
    (hR : BRAdmissibleSeparatingFiber n R) (d : BRTruncatedInterfaceEdge n R) :
    Odd ((brTruncatedResolvedBoundaryGraph n R).degree d) ↔
      d ∈ brTruncatedBottomBoundaryVertices n R ∨
        d ∈ brTruncatedTopBoundaryVertices n R := by
  constructor
  · intro hodd
    rcases degree_brTruncatedResolvedBoundaryGraph_eq_one_or_two hn hR d with hone | htwo
    · exact (degree_brTruncatedResolvedBoundaryGraph_eq_one_iff hn hR d).mp hone
    · rw [htwo] at hodd
      norm_num at hodd
  · intro hport
    rw [(degree_brTruncatedResolvedBoundaryGraph_eq_one_iff hn hR d).mpr hport]
    exact odd_one

/-- Some component of the finite truncated boundary meets both horizontal port sets. -/
theorem exists_brTruncatedResolvedBoundaryGraph_reachable_bottom_top
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)} (hn : 0 < n)
    (hR : BRAdmissibleSeparatingFiber n R) :
    ∃ b ∈ brTruncatedBottomBoundaryVertices n R,
      ∃ t ∈ brTruncatedTopBoundaryVertices n R,
        (brTruncatedResolvedBoundaryGraph n R).Reachable b t := by
  apply SimpleGraph.exists_reachable_between_of_odd_degree_partition
    (Set.toFinite (brTruncatedResolvedBoundaryGraph n R).support)
    (brTruncatedBottomBoundaryVertices n R)
    (brTruncatedTopBoundaryVertices n R)
    (odd_card_brTruncatedBottomBoundaryVertices hn hR)
  intro d
  exact odd_degree_brTruncatedResolvedBoundaryGraph_iff hn hR d

end

end Percolation
