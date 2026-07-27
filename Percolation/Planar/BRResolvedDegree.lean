import Percolation.Planar.BRResolvedBoundary

/-!
# Degree of the locally resolved stopped boundary

This module identifies the two dual-coordinate cells incident to a stopped-interface edge and
uses the unique local split-tag partner in each cell to compute the degree of the full resolved
boundary graph.
-/

namespace Percolation

open SimpleGraph
open scoped Sym2

noncomputable section

/-- The two dual-coordinate unit cells incident to a stopped-interface positive edge. -/
def brResolvedIncidentCells
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (d : BRStoppedInterfaceEdge n R) : Finset DualSquareVertex :=
  (squarePositiveEdgeDualCrossingEmbedding d.1 : Sym2 DualSquareVertex).toFinset

@[simp]
theorem mem_brResolvedIncidentCells_iff
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    {d : BRStoppedInterfaceEdge n R} {z : DualSquareVertex} :
    z ∈ brResolvedIncidentCells d ↔ brStoppedInterfaceIncidentAt z d := by
  classical
  rw [brResolvedIncidentCells, Sym2.mem_toFinset,
    ← mem_squareCellPositiveEdges_iff_mem_crossing]
  simp only [brStoppedInterfaceIncidentAt, squareCellBoundaryPositiveEdges,
    Finset.mem_filter]
  exact (and_iff_left d.2).symm

/-- A stopped-interface positive edge is incident to exactly two dual-coordinate cells. -/
theorem card_brResolvedIncidentCells_eq_two
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (d : BRStoppedInterfaceEdge n R) :
    (brResolvedIncidentCells d).card = 2 := by
  classical
  apply Sym2.card_toFinset_of_not_isDiag
  exact dualSquareGraph.not_isDiag_of_mem_edgeSet
    (squarePositiveEdgeDualCrossingEmbedding d.1).2

/-- Each of the two incident cells supplies a unique resolved partner. -/
theorem existsUnique_brResolvedBoundaryPartnerAt_of_mem_incidentCells
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (d : BRStoppedInterfaceEdge n R) {z : DualSquareVertex}
    (hz : z ∈ brResolvedIncidentCells d) :
    ∃! e : BRStoppedInterfaceEdge n R, brResolvedBoundaryPairedAt z d e :=
  existsUnique_brResolvedBoundaryPartnerAt z d
    (mem_brResolvedIncidentCells_iff.mp hz)

/-- Two distinct cells incident to `d` have no common cell-side positive edge other than `d`.
This is the local square-grid geometry needed to distinguish the two resolved partners. -/
theorem squarePositiveEdge_eq_of_mem_two_brResolvedIncidentCells
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    {d : BRStoppedInterfaceEdge n R} {e : SquarePositiveEdge}
    {z w : DualSquareVertex}
    (hz : z ∈ brResolvedIncidentCells d)
    (hw : w ∈ brResolvedIncidentCells d) (hzw : z ≠ w)
    (hez : e ∈ squareCellPositiveEdges z)
    (hew : e ∈ squareCellPositiveEdges w) :
    e = d.1 := by
  classical
  let Cd := brResolvedIncidentCells d
  let Ce := (squarePositiveEdgeDualCrossingEmbedding e :
    Sym2 DualSquareVertex).toFinset
  have hCdCard : Cd.card = 2 := by
    simpa [Cd] using card_brResolvedIncidentCells_eq_two d
  have hCeCard : Ce.card = 2 := by
    dsimp only [Ce]
    apply Sym2.card_toFinset_of_not_isDiag
    exact dualSquareGraph.not_isDiag_of_mem_edgeSet
      (squarePositiveEdgeDualCrossingEmbedding e).2
  have hzE : z ∈ Ce := by
    change z ∈ (squarePositiveEdgeDualCrossingEmbedding e :
      Sym2 DualSquareVertex).toFinset
    rw [Sym2.mem_toFinset]
    exact (mem_squareCellPositiveEdges_iff_mem_crossing.mp hez)
  have hwE : w ∈ Ce := by
    change w ∈ (squarePositiveEdgeDualCrossingEmbedding e :
      Sym2 DualSquareVertex).toFinset
    rw [Sym2.mem_toFinset]
    exact (mem_squareCellPositiveEdges_iff_mem_crossing.mp hew)
  have hpairCd : ({z, w} : Finset DualSquareVertex) = Cd := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hz
      · exact hw
    · simp [hzw, hCdCard]
  have hpairCe : ({z, w} : Finset DualSquareVertex) = Ce := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hzE
      · exact hwE
    · simp [hzw, hCeCard]
  have hcrossing :
      (squarePositiveEdgeDualCrossingEmbedding e : Sym2 DualSquareVertex) =
        (squarePositiveEdgeDualCrossingEmbedding d.1 : Sym2 DualSquareVertex) := by
    apply Sym2.ext
    intro x
    rw [← Sym2.mem_toFinset, ← Sym2.mem_toFinset]
    change x ∈ Ce ↔ x ∈ Cd
    rw [← hpairCe, ← hpairCd]
  apply squarePositiveEdgeDualCrossingEmbedding.injective
  exact Subtype.ext hcrossing

/-- An incident cell together with its membership proof. -/
abbrev BRResolvedIncidentCell
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (d : BRStoppedInterfaceEdge n R) :=
  {z : DualSquareVertex // z ∈ brResolvedIncidentCells d}

/-- The unique split-tag partner supplied by one incident cell. -/
noncomputable def brResolvedBoundaryPartner
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (d : BRStoppedInterfaceEdge n R) (z : BRResolvedIncidentCell d) :
    BRStoppedInterfaceEdge n R :=
  (existsUnique_brResolvedBoundaryPartnerAt_of_mem_incidentCells d z.2).choose

/-- The selected partner satisfies the resolved pairing relation at its incident cell. -/
theorem brResolvedBoundaryPartner_pairedAt
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (d : BRStoppedInterfaceEdge n R) (z : BRResolvedIncidentCell d) :
    brResolvedBoundaryPairedAt z.1 d (brResolvedBoundaryPartner d z) :=
  (existsUnique_brResolvedBoundaryPartnerAt_of_mem_incidentCells d z.2).choose_spec.1

/-- The two incident cells select distinct resolved partners. -/
theorem brResolvedBoundaryPartner_injective
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (d : BRStoppedInterfaceEdge n R) :
    Function.Injective (brResolvedBoundaryPartner d) := by
  classical
  intro z w hpartner
  apply Subtype.ext
  by_contra hzw
  have hzPair := brResolvedBoundaryPartner_pairedAt d z
  have hwPair := brResolvedBoundaryPartner_pairedAt d w
  have hwPair' :
      brResolvedBoundaryPairedAt w.1 d (brResolvedBoundaryPartner d z) := by
    simpa only [hpartner] using hwPair
  have hez := hzPair.2.1
  have hew := hwPair'.2.1
  rw [brStoppedInterfaceIncidentAt, squareCellBoundaryPositiveEdges,
    Finset.mem_filter] at hez hew
  have heq : (brResolvedBoundaryPartner d z).1 = d.1 :=
    squarePositiveEdge_eq_of_mem_two_brResolvedIncidentCells z.2 w.2 hzw hez.1 hew.1
  exact hzPair.2.2.1 (Subtype.ext heq)

/-- Map each incident cell to the corresponding neighbor in the resolved graph. -/
def brResolvedIncidentCellToNeighbor
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (d : BRStoppedInterfaceEdge n R) :
    BRResolvedIncidentCell d → (brResolvedBoundaryGraph n R).neighborSet d :=
  fun z ↦ ⟨brResolvedBoundaryPartner d z,
    brResolvedBoundaryGraph_adj_iff.mpr
      ⟨z.1, brResolvedBoundaryPartner_pairedAt d z⟩⟩

theorem brResolvedIncidentCellToNeighbor_injective
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (d : BRStoppedInterfaceEdge n R) :
    Function.Injective (brResolvedIncidentCellToNeighbor d) := by
  intro z w hzw
  apply brResolvedBoundaryPartner_injective d
  exact congrArg Subtype.val hzw

theorem brResolvedIncidentCellToNeighbor_surjective
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (d : BRStoppedInterfaceEdge n R) :
    Function.Surjective (brResolvedIncidentCellToNeighbor d) := by
  rintro ⟨e, he⟩
  rcases brResolvedBoundaryGraph_adj_iff.mp he with ⟨z, hpair⟩
  have hz : z ∈ brResolvedIncidentCells d :=
    mem_brResolvedIncidentCells_iff.mpr hpair.1
  let z' : BRResolvedIncidentCell d := ⟨z, hz⟩
  refine ⟨z', ?_⟩
  apply Subtype.ext
  exact brResolvedBoundaryPairedAt_right_unique
    (brResolvedBoundaryPartner_pairedAt d z') hpair

/-- The two incident cells are canonically equivalent to the resolved neighbors. -/
noncomputable def brResolvedIncidentCellEquivNeighborSet
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (d : BRStoppedInterfaceEdge n R) :
    BRResolvedIncidentCell d ≃ (brResolvedBoundaryGraph n R).neighborSet d :=
  Equiv.ofBijective (brResolvedIncidentCellToNeighbor d)
    ⟨brResolvedIncidentCellToNeighbor_injective d,
      brResolvedIncidentCellToNeighbor_surjective d⟩

noncomputable instance instFintypeBRResolvedBoundaryGraphNeighborSet
    (n : ℕ) (R : Finset (BRLeftmostDualVertex n))
    (d : BRStoppedInterfaceEdge n R) :
    Fintype ((brResolvedBoundaryGraph n R).neighborSet d) :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

/-- Every vertex of the full resolved stopped-boundary graph has degree two. -/
theorem brResolvedBoundaryGraph_degree_eq_two
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (d : BRStoppedInterfaceEdge n R) :
    (brResolvedBoundaryGraph n R).degree d = 2 := by
  rw [← SimpleGraph.card_neighborSet_eq_degree]
  calc
    Fintype.card ((brResolvedBoundaryGraph n R).neighborSet d) =
        Fintype.card (BRResolvedIncidentCell d) :=
      Fintype.card_congr (brResolvedIncidentCellEquivNeighborSet d).symm
    _ = (brResolvedIncidentCells d).card := Fintype.card_coe _
    _ = 2 := card_brResolvedIncidentCells_eq_two d

end

end Percolation
