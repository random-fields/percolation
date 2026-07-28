import Percolation.Planar.BRFiberGeometry
import Percolation.Planar.BRResolvedDegree

/-!
# Truncated resolved boundary of the stopped dual exploration

This module removes the artificial exterior part of the stopped boundary.  A retained dual bond
has both endpoints in the finite exploration frame and crosses an allowed bond of the
boundary-free RSW square.  Local resolved pairings are then restricted to cells strictly between
the bottom and top sides of the square.
-/

namespace Percolation

open SimpleGraph

noncomputable section

/-- Dual-coordinate cells whose corresponding primal vertices are strictly between the bottom
and top sides of `[0,2n] × [-n,n]`. -/
def brTruncatedBoundaryCells (n : ℕ) : Finset DualSquareVertex :=
  Fintype.piFinset fun i : Fin 2 ↦
    if i = 0 then Finset.Ico (-1 : ℤ) (2 * (n : ℤ))
    else Finset.Ico (-(n : ℤ)) ((n : ℤ) - 1)

@[simp]
theorem mem_brTruncatedBoundaryCells_iff
    {n : ℕ} {z : DualSquareVertex} :
    z ∈ brTruncatedBoundaryCells n ↔
      -1 ≤ z 0 ∧ z 0 < 2 * (n : ℤ) ∧
        -(n : ℤ) ≤ z 1 ∧ z 1 < (n : ℤ) - 1 := by
  classical
  simp only [brTruncatedBoundaryCells, Fintype.mem_piFinset]
  constructor
  · intro h
    have h0 : -1 ≤ z 0 ∧ z 0 < 2 * (n : ℤ) := by
      simpa [Finset.mem_Ico] using h (0 : Fin 2)
    have h1 : -(n : ℤ) ≤ z 1 ∧ z 1 < (n : ℤ) - 1 := by
      simpa [Finset.mem_Ico] using h (1 : Fin 2)
    exact ⟨h0.1, h0.2, h1.1, h1.2⟩
  · rintro ⟨hz0, hz0', hz1, hz1'⟩ i
    fin_cases i
    · simp [Finset.mem_Ico, hz0, hz0']
    · simp [Finset.mem_Ico, hz1, hz1']

/-- Stopped-boundary positive dual bonds retained by the finite truncation. -/
def brTruncatedDualBoundaryPositiveEdges
    (n : ℕ) (R : Finset (BRLeftmostDualVertex n)) :
    Finset DualSquarePositiveEdge := by
  classical
  exact (brStoppedDualBoundaryBoundingPositiveEdges n).filter fun d ↦
    brStoppedDualBoundaryEdge n R d ∧
      d.base ∈ brLeftmostDualFaces n ∧
      cubicStepFrom d.base (d.axis, true) ∈ brLeftmostDualFaces n ∧
      (dualToPrimalCrossingPositiveEdge d).toEdge ∈
        squareBoundaryFreeRectangleEdges (2 * n) n

@[simp]
theorem mem_brTruncatedDualBoundaryPositiveEdges_iff
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    {d : DualSquarePositiveEdge} :
    d ∈ brTruncatedDualBoundaryPositiveEdges n R ↔
      brStoppedDualBoundaryEdge n R d ∧
        d.base ∈ brLeftmostDualFaces n ∧
        cubicStepFrom d.base (d.axis, true) ∈ brLeftmostDualFaces n ∧
        (dualToPrimalCrossingPositiveEdge d).toEdge ∈
          squareBoundaryFreeRectangleEdges (2 * n) n := by
  classical
  rw [brTruncatedDualBoundaryPositiveEdges, Finset.mem_filter]
  constructor
  · exact fun h ↦ h.2
  · intro h
    exact ⟨brStoppedDualBoundaryEdge_mem_boundingPositiveEdges h.1, h⟩

/-- A retained boundary bond, represented as a finite subtype of raw positive dual bonds. -/
abbrev BRTruncatedInterfaceEdge
    (n : ℕ) (R : Finset (BRLeftmostDualVertex n)) :=
  {d : DualSquarePositiveEdge // d ∈ brTruncatedDualBoundaryPositiveEdges n R}

noncomputable instance instFintypeBRTruncatedInterfaceEdge
    (n : ℕ) (R : Finset (BRLeftmostDualVertex n)) :
    Fintype (BRTruncatedInterfaceEdge n R) :=
  Fintype.ofFinite _

/-- Regard a retained boundary bond as a stopped-interface bond. -/
def brTruncatedInterfaceEdgeToStoppedEmbedding
    (n : ℕ) (R : Finset (BRLeftmostDualVertex n)) :
    BRTruncatedInterfaceEdge n R ↪ BRStoppedInterfaceEdge n R where
  toFun d := ⟨d.1, (mem_brTruncatedDualBoundaryPositiveEdges_iff.mp d.2).1⟩
  inj' := by
    intro d e hde
    apply Subtype.ext
    exact congrArg (fun x : BRStoppedInterfaceEdge n R ↦ x.1) hde

/-- The stopped-interface value of a retained boundary bond. -/
abbrev BRTruncatedInterfaceEdge.toStopped
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (d : BRTruncatedInterfaceEdge n R) : BRStoppedInterfaceEdge n R :=
  brTruncatedInterfaceEdgeToStoppedEmbedding n R d

/-- The truncated resolved boundary graph.  Its adjacency witness is explicitly required to lie
in the retained cell set, so no pairing through an exterior cell is silently admitted. -/
def brTruncatedResolvedBoundaryGraph
    (n : ℕ) (R : Finset (BRLeftmostDualVertex n)) :
    SimpleGraph (BRTruncatedInterfaceEdge n R) where
  Adj d e := ∃ z ∈ brTruncatedBoundaryCells n,
    brResolvedBoundaryPairedAt z d.toStopped e.toStopped
  symm := by
    rintro d e ⟨z, hz, hde⟩
    exact ⟨z, hz, brResolvedBoundaryPairedAt_comm.mp hde⟩
  loopless := ⟨by
    intro d hdd
    rcases hdd with ⟨z, _hz, hdd⟩
    exact not_brResolvedBoundaryPairedAt_self z d.toStopped hdd⟩

@[simp]
theorem brTruncatedResolvedBoundaryGraph_adj_iff
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    {d e : BRTruncatedInterfaceEdge n R} :
    (brTruncatedResolvedBoundaryGraph n R).Adj d e ↔
      ∃ z ∈ brTruncatedBoundaryCells n,
        brResolvedBoundaryPairedAt z d.toStopped e.toStopped :=
  Iff.rfl

/-- Incident cells of a retained edge that survive the geometric cell truncation. -/
def brTruncatedResolvedIncidentCells
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (d : BRTruncatedInterfaceEdge n R) : Finset DualSquareVertex :=
  (brResolvedIncidentCells d.toStopped).filter fun z ↦
    z ∈ brTruncatedBoundaryCells n

@[simp]
theorem mem_brTruncatedResolvedIncidentCells_iff
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    {d : BRTruncatedInterfaceEdge n R} {z : DualSquareVertex} :
    z ∈ brTruncatedResolvedIncidentCells d ↔
      brStoppedInterfaceIncidentAt z d.toStopped ∧
        z ∈ brTruncatedBoundaryCells n := by
  simp [brTruncatedResolvedIncidentCells, mem_brResolvedIncidentCells_iff]

/-! ### Neighbors selected by retained incident cells -/

/-- An incident cell retained by the truncation whose canonical resolved partner is also a
retained boundary edge.  These are exactly the incident-cell witnesses which give neighbors in
`brTruncatedResolvedBoundaryGraph`. -/
abbrev BRTruncatedPartnerIncidentCell
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (d : BRTruncatedInterfaceEdge n R) :=
  {z : BRResolvedIncidentCell d.toStopped //
    z.1 ∈ brTruncatedBoundaryCells n ∧
      (brResolvedBoundaryPartner d.toStopped z).1 ∈
        brTruncatedDualBoundaryPositiveEdges n R}

/-- Send a retained incident cell to the truncated neighbor selected by its canonical resolved
partner. -/
def brTruncatedPartnerIncidentCellToNeighbor
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (d : BRTruncatedInterfaceEdge n R) :
    BRTruncatedPartnerIncidentCell d →
      (brTruncatedResolvedBoundaryGraph n R).neighborSet d :=
  fun z ↦
    let e : BRTruncatedInterfaceEdge n R :=
      ⟨(brResolvedBoundaryPartner d.toStopped z.1).1, z.2.2⟩
    ⟨e, brTruncatedResolvedBoundaryGraph_adj_iff.mpr
      ⟨z.1.1, z.2.1, by
        simpa [e] using brResolvedBoundaryPartner_pairedAt d.toStopped z.1⟩⟩

theorem brTruncatedPartnerIncidentCellToNeighbor_injective
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (d : BRTruncatedInterfaceEdge n R) :
    Function.Injective (brTruncatedPartnerIncidentCellToNeighbor d) := by
  intro z w hzw
  apply Subtype.ext
  apply brResolvedBoundaryPartner_injective d.toStopped
  apply Subtype.ext
  exact congrArg
    (fun e : (brTruncatedResolvedBoundaryGraph n R).neighborSet d ↦ e.1.1) hzw

theorem brTruncatedPartnerIncidentCellToNeighbor_surjective
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (d : BRTruncatedInterfaceEdge n R) :
    Function.Surjective (brTruncatedPartnerIncidentCellToNeighbor d) := by
  rintro ⟨e, he⟩
  rcases brTruncatedResolvedBoundaryGraph_adj_iff.mp he with ⟨z, hz, hpair⟩
  have hzIncident : z ∈ brResolvedIncidentCells d.toStopped :=
    mem_brResolvedIncidentCells_iff.mpr hpair.1
  let z' : BRResolvedIncidentCell d.toStopped := ⟨z, hzIncident⟩
  have hpartner : brResolvedBoundaryPartner d.toStopped z' = e.toStopped :=
    brResolvedBoundaryPairedAt_right_unique
      (brResolvedBoundaryPartner_pairedAt d.toStopped z') hpair
  have hpartnerMem :
      (brResolvedBoundaryPartner d.toStopped z').1 ∈
        brTruncatedDualBoundaryPositiveEdges n R := by
    rw [hpartner]
    exact e.2
  let z'' : BRTruncatedPartnerIncidentCell d := ⟨z', hz, hpartnerMem⟩
  refine ⟨z'', ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun x : BRStoppedInterfaceEdge n R ↦ x.1) hpartner

/-- Retained partner cells are canonically equivalent to neighbors in the truncated resolved
boundary graph. -/
noncomputable def brTruncatedPartnerIncidentCellEquivNeighborSet
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (d : BRTruncatedInterfaceEdge n R) :
    BRTruncatedPartnerIncidentCell d ≃
      (brTruncatedResolvedBoundaryGraph n R).neighborSet d :=
  Equiv.ofBijective (brTruncatedPartnerIncidentCellToNeighbor d)
    ⟨brTruncatedPartnerIncidentCellToNeighbor_injective d,
      brTruncatedPartnerIncidentCellToNeighbor_surjective d⟩

noncomputable instance instFintypeBRTruncatedResolvedBoundaryGraphNeighborSet
    (n : ℕ) (R : Finset (BRLeftmostDualVertex n))
    (d : BRTruncatedInterfaceEdge n R) :
    Fintype ((brTruncatedResolvedBoundaryGraph n R).neighborSet d) :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

/-- The degree of a truncated boundary edge is the number of retained incident cells whose
canonical resolved partners are retained. -/
theorem degree_brTruncatedResolvedBoundaryGraph_eq_card_partner_cells
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (d : BRTruncatedInterfaceEdge n R) :
    (brTruncatedResolvedBoundaryGraph n R).degree d =
      Fintype.card (BRTruncatedPartnerIncidentCell d) := by
  rw [← SimpleGraph.card_neighborSet_eq_degree]
  exact (Fintype.card_congr
    (brTruncatedPartnerIncidentCellEquivNeighborSet d)).symm

/-! ### Realizable fibers retain every partner from a retained cell -/

private theorem brReachedDualFace_iff_mem
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    {z : BRLeftmostDualVertex n} :
    brReachedDualFace n R z.1 ↔ z ∈ R := by
  rw [brReachedDualFace, brReachedFaceCoordinates, Finset.mem_map]
  constructor
  · rintro ⟨w, hw, hwz⟩
    have : w = z := Subtype.ext hwz
    simpa only [this] using hw
  · intro hz
    exact ⟨z, hz, rfl⟩

/-- Every side of a retained dual-coordinate cell has both endpoints in the exploration frame. -/
theorem squareCellPositiveEdge_endpoints_mem_brLeftmostDualFaces
    {n : ℕ} {z : DualSquareVertex} {e : DualSquarePositiveEdge}
    (hz : z ∈ brTruncatedBoundaryCells n)
    (he : e ∈ squareCellPositiveEdges z) :
    e.base ∈ brLeftmostDualFaces n ∧
      cubicStepFrom e.base (e.axis, true) ∈ brLeftmostDualFaces n := by
  rw [mem_brTruncatedBoundaryCells_iff] at hz
  simp [squareCellPositiveEdges, squareCellPositiveEdgeList] at he
  rcases he with rfl | rfl | rfl | rfl
  all_goals
    constructor <;>
      rw [mem_brLeftmostDualFaces_iff] <;>
      simp [squareVertex, cubicStepFrom, cubicDirectionIncrement] <;>
      omega

private theorem squareEdgeDualCrossingEquiv_symm_dualPositiveEdge_toEdge
    (e : DualSquarePositiveEdge) :
    squareEdgeDualCrossingEquiv.symm e.toEdge =
      (dualToPrimalCrossingPositiveEdge e).toEdge := by
  have horient : SquarePositiveEdge.edgeEquiv.symm e.toEdge = e := by
    apply SquarePositiveEdge.edgeEquiv.injective
    simp [SquarePositiveEdge.edgeEquiv_apply]
  simp [squareEdgeDualCrossingEquiv, squarePositiveEdgeDualCrossingEquiv,
    SquarePositiveEdge.edgeEquiv_apply, horient]

/-- A stopped boundary edge whose endpoints lie in the frame crosses an allowed boundary-free
bond whenever its reached-face set is realized by an exploration fiber. -/
theorem dualToPrimalCrossingPositiveEdge_mem_boundaryFree_of_mem_fiber
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    {omega : EdgeConfiguration 2} (homega : omega ∈ brReachableFaceFiber n R)
    (e : BRStoppedInterfaceEdge n R)
    (hbase : e.1.base ∈ brLeftmostDualFaces n)
    (hstep : cubicStepFrom e.1.base (e.1.axis, true) ∈ brLeftmostDualFaces n) :
    (dualToPrimalCrossingPositiveEdge e.1).toEdge ∈
      squareBoundaryFreeRectangleEdges (2 * n) n := by
  let x : BRLeftmostDualVertex n := ⟨e.1.base, hbase⟩
  let y : BRLeftmostDualVertex n :=
    ⟨cubicStepFrom e.1.base (e.1.axis, true), hstep⟩
  have hxy : (brLeftmostDualGraph n).Adj x y := by
    rw [brLeftmostDualGraph_adj_iff]
    exact cubicGraph_adj_stepFrom e.1.base (e.1.axis, true)
  have hdual :
      brLeftmostDualEdgeEmbedding n
          ⟨s(x, y), (brLeftmostDualGraph n).mem_edgeSet.mpr hxy⟩ = e.1.toEdge := by
    apply Subtype.ext
    rfl
  by_contra hallowed
  have hcrossed :
      squareEdgeDualCrossingEquiv.symm
          (brLeftmostDualEdgeEmbedding n
            ⟨s(x, y), (brLeftmostDualGraph n).mem_edgeSet.mpr hxy⟩) ∉
        squareBoundaryFreeRectangleEdges (2 * n) n := by
    rw [hdual, squareEdgeDualCrossingEquiv_symm_dualPositiveEdge_toEdge]
    exact hallowed
  have hsame := mem_brLeftReachableFaces_iff_of_adj_of_crossed_not_mem
    (omega := omega) hxy hcrossed
  change brLeftReachableFaces n omega = R at homega
  rw [homega] at hsame
  have hsameFace :
      brReachedDualFace n R e.1.base ↔
        brReachedDualFace n R (cubicStepFrom e.1.base (e.1.axis, true)) := by
    exact brReachedDualFace_iff_mem.trans
      (hsame.trans brReachedDualFace_iff_mem.symm)
  exact e.2 hsameFace

/-- In a realized fiber, the canonical partner selected at a retained incident cell is itself a
retained boundary edge. -/
theorem brResolvedBoundaryPartner_mem_truncated_of_mem_fiber
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    {omega : EdgeConfiguration 2} (homega : omega ∈ brReachableFaceFiber n R)
    (d : BRTruncatedInterfaceEdge n R) (z : BRResolvedIncidentCell d.toStopped)
    (hz : z.1 ∈ brTruncatedBoundaryCells n) :
    (brResolvedBoundaryPartner d.toStopped z).1 ∈
      brTruncatedDualBoundaryPositiveEdges n R := by
  classical
  have hpair := brResolvedBoundaryPartner_pairedAt d.toStopped z
  have hpartnerCell :
      (brResolvedBoundaryPartner d.toStopped z).1 ∈ squareCellPositiveEdges z.1 := by
    have hincident := hpair.2.1
    rw [brStoppedInterfaceIncidentAt, squareCellBoundaryPositiveEdges,
      Finset.mem_filter] at hincident
    exact hincident.1
  have hendpoints :=
    squareCellPositiveEdge_endpoints_mem_brLeftmostDualFaces hz hpartnerCell
  rw [mem_brTruncatedDualBoundaryPositiveEdges_iff]
  exact ⟨(brResolvedBoundaryPartner d.toStopped z).2, hendpoints.1, hendpoints.2,
    dualToPrimalCrossingPositiveEdge_mem_boundaryFree_of_mem_fiber homega
      (brResolvedBoundaryPartner d.toStopped z) hendpoints.1 hendpoints.2⟩

/-- On a realized fiber, retained partner cells are equivalent to the geometrically retained
incident-cell finset. -/
noncomputable def brTruncatedPartnerIncidentCellEquivResolvedIncidentCells
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    {omega : EdgeConfiguration 2} (homega : omega ∈ brReachableFaceFiber n R)
    (d : BRTruncatedInterfaceEdge n R) :
    BRTruncatedPartnerIncidentCell d ≃
      {z : DualSquareVertex // z ∈ brTruncatedResolvedIncidentCells d} where
  toFun z := ⟨z.1.1, by
    rw [brTruncatedResolvedIncidentCells, Finset.mem_filter]
    exact ⟨z.1.2, z.2.1⟩⟩
  invFun z := by
    have hz := mem_brTruncatedResolvedIncidentCells_iff.mp z.2
    let z' : BRResolvedIncidentCell d.toStopped :=
      ⟨z.1, mem_brResolvedIncidentCells_iff.mpr hz.1⟩
    exact ⟨z', hz.2,
      brResolvedBoundaryPartner_mem_truncated_of_mem_fiber homega d z' hz.2⟩
  left_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv z := by
    apply Subtype.ext
    rfl

/-- For a realizable stopped fiber, truncated degree is the number of geometrically retained
incident cells. -/
theorem degree_brTruncatedResolvedBoundaryGraph
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hreal : ∃ omega, omega ∈ brReachableFaceFiber n R)
    (d : BRTruncatedInterfaceEdge n R) :
    (brTruncatedResolvedBoundaryGraph n R).degree d =
      (brTruncatedResolvedIncidentCells d).card := by
  rcases hreal with ⟨omega, homega⟩
  rw [degree_brTruncatedResolvedBoundaryGraph_eq_card_partner_cells]
  calc
    Fintype.card (BRTruncatedPartnerIncidentCell d) =
        Fintype.card {z : DualSquareVertex // z ∈ brTruncatedResolvedIncidentCells d} :=
      Fintype.card_congr
        (brTruncatedPartnerIncidentCellEquivResolvedIncidentCells homega d)
    _ = (brTruncatedResolvedIncidentCells d).card := Fintype.card_coe _

end

end Percolation
