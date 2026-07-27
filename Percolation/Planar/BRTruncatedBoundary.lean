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

end

end Percolation
