import Percolation.Planar.BRDualExploration
import Percolation.Planar.ResolvedRectangleInterface

/-!
# The locally resolved boundary of the stopped dual exploration

This file supplies the local graph used to trace the boundary of a fixed reached-face fiber in
the Bollobás--Riordan exploration.  A vertex is a positive dual bond on which membership in the
fixed reached set changes.  Such a bond canonically represents the positive primal bond that it
crosses, via `dualToPrimalCrossingPositiveEdge`.

Two boundary bonds are adjacent when they lie on a common unit cell of the dual-coordinate
lattice, are distinct, and have the same `squareCellBoundarySplitTag`.  The split tag resolves
the degree-four checkerboard ambiguity.  The local pairing theorem from
`ResolvedRectangleInterface` gives a unique partner at each fixed incident cell.

No global path, cycle, endpoint, or partition assertion is made here.  In particular, local
uniqueness at a fixed cell does not by itself identify the boundary component selected by the
stopping argument.
-/

namespace Percolation

open SimpleGraph

noncomputable section

/-- Forget the finite-frame proof carried by a vertex of the stopped dual exploration. -/
def brLeftmostDualVertexValEmbedding (n : ℕ) :
    BRLeftmostDualVertex n ↪ DualSquareVertex where
  toFun := Subtype.val
  inj' := Subtype.val_injective

/-- The reached dual faces of a fixed stopping fiber, in ambient integer coordinates. -/
def brReachedFaceCoordinates
    (n : ℕ) (R : Finset (BRLeftmostDualVertex n)) : Finset DualSquareVertex :=
  R.map (brLeftmostDualVertexValEmbedding n)

/-- Membership in the fixed reached-face set, viewed as a predicate on the encoded dual
lattice.  `SquareVertex` and `DualSquareVertex` have the same integer-coordinate model. -/
def brReachedDualFace
    (n : ℕ) (R : Finset (BRLeftmostDualVertex n)) (z : SquareVertex) : Prop :=
  z ∈ brReachedFaceCoordinates n R

local instance instDecidablePredBRReachedDualFace
    (n : ℕ) (R : Finset (BRLeftmostDualVertex n)) :
    DecidablePred (brReachedDualFace n R) :=
  Classical.decPred _

/-- A positive dual bond lies on the stopped interface when exactly one endpoint belongs to the
fixed reached-face set.  Faces outside the finite exploration frame are treated as unreached. -/
def brStoppedDualBoundaryEdge
    (n : ℕ) (R : Finset (BRLeftmostDualVertex n))
    (d : DualSquarePositiveEdge) : Prop :=
  ¬(brReachedDualFace n R d.base ↔
    brReachedDualFace n R (cubicStepFrom d.base (d.axis, true)))

/-! ### A finite enclosure of the stopped boundary -/

/-- Possible base vertices of stopped-boundary positive dual bonds.

The reached frame has coordinate bounds `[-1, 2n] × [-n, n-1]`.  If the reached endpoint is
the positive edge's terminal endpoint, the base is at most one coordinate step away.  We use the
slightly non-sharp but uniform enclosure `[-2, 2n+1] × [-n-1, n]`. -/
def brStoppedDualBoundaryBaseBox (n : ℕ) : Finset DualSquareVertex :=
  Fintype.piFinset fun i : Fin 2 ↦
    if i = 0 then Finset.Icc (-2 : ℤ) (2 * (n : ℤ) + 1)
    else Finset.Icc (-(n : ℤ) - 1) (n : ℤ)

@[simp]
theorem mem_brStoppedDualBoundaryBaseBox_iff
    {n : ℕ} {z : DualSquareVertex} :
    z ∈ brStoppedDualBoundaryBaseBox n ↔
      -2 ≤ z 0 ∧ z 0 ≤ 2 * (n : ℤ) + 1 ∧
        -(n : ℤ) - 1 ≤ z 1 ∧ z 1 ≤ (n : ℤ) := by
  classical
  simp only [brStoppedDualBoundaryBaseBox, Fintype.mem_piFinset]
  constructor
  · intro h
    have h0 : -2 ≤ z 0 ∧ z 0 ≤ 2 * (n : ℤ) + 1 := by
      simpa [Finset.mem_Icc] using h (0 : Fin 2)
    have h1 : -(n : ℤ) - 1 ≤ z 1 ∧ z 1 ≤ (n : ℤ) := by
      simpa [Finset.mem_Icc] using h (1 : Fin 2)
    exact ⟨h0.1, h0.2, h1.1, h1.2⟩
  · rintro ⟨hz0, hz0', hz1, hz1'⟩ i
    fin_cases i
    · simp [Finset.mem_Icc, hz0, hz0']
    · simp [Finset.mem_Icc, hz1, hz1']

/-- Assemble a positive dual bond from its base vertex and coordinate axis. -/
def brDualPositiveEdgeOfProdEmbedding :
    DualSquareVertex × Fin 2 ↪ DualSquarePositiveEdge where
  toFun := fun p ↦ ⟨p.1, p.2⟩
  inj' := by
    intro p q hpq
    apply Prod.ext
    · exact congrArg SquarePositiveEdge.base hpq
    · exact congrArg SquarePositiveEdge.axis hpq

/-- A finite set of positive dual bonds containing every stopped-boundary bond. -/
def brStoppedDualBoundaryBoundingPositiveEdges (n : ℕ) :
    Finset DualSquarePositiveEdge :=
  ((brStoppedDualBoundaryBaseBox n).product (Finset.univ : Finset (Fin 2))).map
    brDualPositiveEdgeOfProdEmbedding

@[simp]
theorem mem_brStoppedDualBoundaryBoundingPositiveEdges_iff
    {n : ℕ} {d : DualSquarePositiveEdge} :
    d ∈ brStoppedDualBoundaryBoundingPositiveEdges n ↔
      d.base ∈ brStoppedDualBoundaryBaseBox n := by
  rcases d with ⟨base, axis⟩
  constructor
  · intro h
    rw [brStoppedDualBoundaryBoundingPositiveEdges, Finset.mem_map] at h
    rcases h with ⟨p, hp, hp_eq⟩
    rcases p with ⟨pbase, paxis⟩
    cases hp_eq
    simpa [Finset.mem_product] using hp
  · intro h
    rw [brStoppedDualBoundaryBoundingPositiveEdges, Finset.mem_map]
    exact ⟨(base, axis), by simpa [Finset.mem_product] using h, rfl⟩

/-- Every reached face belongs to the finite exploration frame. -/
theorem brReachedFaceCoordinates_subset_brLeftmostDualFaces
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)} :
    brReachedFaceCoordinates n R ⊆ brLeftmostDualFaces n := by
  intro z hz
  rw [brReachedFaceCoordinates, Finset.mem_map] at hz
  rcases hz with ⟨w, _hwR, rfl⟩
  exact w.2

/-- Every stopped-boundary positive dual bond lies in the explicit finite coordinate
enclosure. -/
theorem brStoppedDualBoundaryEdge_mem_boundingPositiveEdges
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)} {d : DualSquarePositiveEdge}
    (hd : brStoppedDualBoundaryEdge n R d) :
    d ∈ brStoppedDualBoundaryBoundingPositiveEdges n := by
  classical
  rw [mem_brStoppedDualBoundaryBoundingPositiveEdges_iff,
    mem_brStoppedDualBoundaryBaseBox_iff]
  have hReachedEndpoint :
      brReachedDualFace n R d.base ∨
        brReachedDualFace n R (cubicStepFrom d.base (d.axis, true)) := by
    by_contra hnone
    have hnone' := not_or.mp hnone
    exact hd (iff_of_false hnone'.1 hnone'.2)
  rcases hReachedEndpoint with hbase | hstep
  · have hbaseFrame : d.base ∈ brLeftmostDualFaces n :=
      brReachedFaceCoordinates_subset_brLeftmostDualFaces hbase
    rw [mem_brLeftmostDualFaces_iff] at hbaseFrame
    omega
  · have hstepFrame :
        cubicStepFrom d.base (d.axis, true) ∈ brLeftmostDualFaces n :=
      brReachedFaceCoordinates_subset_brLeftmostDualFaces hstep
    rw [mem_brLeftmostDualFaces_iff] at hstepFrame
    have hstep0Upper :=
      cubicStepFrom_coord_le_add_one d.base (d.axis, true) (0 : Fin 2)
    have hbase0Upper :=
      cubicStepFrom_coord_sub_one_le d.base (d.axis, true) (0 : Fin 2)
    have hstep1Upper :=
      cubicStepFrom_coord_le_add_one d.base (d.axis, true) (1 : Fin 2)
    have hbase1Upper :=
      cubicStepFrom_coord_sub_one_le d.base (d.axis, true) (1 : Fin 2)
    omega

/-- The ambient set of stopped-boundary positive dual bonds is finite. -/
theorem finite_setOf_brStoppedDualBoundaryEdge
    (n : ℕ) (R : Finset (BRLeftmostDualVertex n)) :
    Set.Finite {d : DualSquarePositiveEdge | brStoppedDualBoundaryEdge n R d} :=
  (brStoppedDualBoundaryBoundingPositiveEdges n).finite_toSet.subset
    (fun _d hd ↦ brStoppedDualBoundaryEdge_mem_boundingPositiveEdges hd)

/-- Boundary bonds of a stopped exploration fiber.

The stored coordinate is the positive dual bond.  Its canonical crossed primal bond is
`brStoppedInterfacePrimalPositiveEdge`; using the dual coordinate makes the local cell pairing
definitionally compatible with `existsUnique_squareCellBoundaryPositiveEdge_partner`. -/
abbrev BRStoppedInterfaceEdge
    (n : ℕ) (R : Finset (BRLeftmostDualVertex n)) :=
  {d : DualSquarePositiveEdge // brStoppedDualBoundaryEdge n R d}

noncomputable instance instFintypeBRStoppedInterfaceEdge
    (n : ℕ) (R : Finset (BRLeftmostDualVertex n)) :
    Fintype (BRStoppedInterfaceEdge n R) :=
  (finite_setOf_brStoppedDualBoundaryEdge n R).fintype

/-- The positive primal bond represented by a stopped-interface boundary bond. -/
def brStoppedInterfacePrimalPositiveEdge
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (d : BRStoppedInterfaceEdge n R) : SquarePositiveEdge :=
  dualToPrimalCrossingPositiveEdge d.1

/-- Distinct stopped-interface vertices represent distinct crossed primal bonds. -/
theorem brStoppedInterfacePrimalPositiveEdge_injective
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)} :
    Function.Injective
      (brStoppedInterfacePrimalPositiveEdge (n := n) (R := R)) := by
  intro d e hde
  apply Subtype.ext
  have hdual := congrArg primalToDualCrossingPositiveEdge hde
  simpa [brStoppedInterfacePrimalPositiveEdge] using hdual

/-- A stopped-interface bond is incident to the dual-coordinate unit cell `z`. -/
def brStoppedInterfaceIncidentAt
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (z : DualSquareVertex) (d : BRStoppedInterfaceEdge n R) : Prop :=
  d.1 ∈ squareCellBoundaryPositiveEdges (brReachedDualFace n R) z

/-- The resolved local pairing relation at one dual-coordinate unit cell. -/
def brResolvedBoundaryPairedAt
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (z : DualSquareVertex)
    (d e : BRStoppedInterfaceEdge n R) : Prop :=
  brStoppedInterfaceIncidentAt z d ∧
    brStoppedInterfaceIncidentAt z e ∧ e ≠ d ∧
      squareCellBoundarySplitTag (brReachedDualFace n R) z e.1 =
        squareCellBoundarySplitTag (brReachedDualFace n R) z d.1

/-- Pairing at a fixed cell is symmetric. -/
theorem brResolvedBoundaryPairedAt_comm
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)} {z : DualSquareVertex}
    {d e : BRStoppedInterfaceEdge n R} :
    brResolvedBoundaryPairedAt z d e ↔ brResolvedBoundaryPairedAt z e d := by
  constructor
  · rintro ⟨hd, he, hne, htag⟩
    exact ⟨he, hd, hne.symm, htag.symm⟩
  · rintro ⟨he, hd, hne, htag⟩
    exact ⟨hd, he, hne.symm, htag.symm⟩

/-- The local resolved pairing never pairs a boundary bond with itself. -/
theorem not_brResolvedBoundaryPairedAt_self
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (z : DualSquareVertex) (d : BRStoppedInterfaceEdge n R) :
    ¬brResolvedBoundaryPairedAt z d d := by
  rintro ⟨_hd, _hd, hne, _htag⟩
  exact hne rfl

/-- At a fixed incident cell, a stopped-interface bond has a unique resolved partner. -/
theorem existsUnique_brResolvedBoundaryPartnerAt
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (z : DualSquareVertex) (d : BRStoppedInterfaceEdge n R)
    (hd : brStoppedInterfaceIncidentAt z d) :
    ∃! e : BRStoppedInterfaceEdge n R, brResolvedBoundaryPairedAt z d e := by
  classical
  rcases existsUnique_squareCellBoundaryPositiveEdge_partner
      (brReachedDualFace n R) z hd with ⟨e, he, hunique⟩
  have heBoundary : brStoppedDualBoundaryEdge n R e := by
    have heMem := he.1
    rw [squareCellBoundaryPositiveEdges, Finset.mem_filter] at heMem
    exact heMem.2
  let e' : BRStoppedInterfaceEdge n R := ⟨e, heBoundary⟩
  refine ⟨e', ?_, ?_⟩
  · refine ⟨hd, he.1, ?_, he.2.2⟩
    intro hed
    exact he.2.1 (congrArg Subtype.val hed)
  · intro f hf
    apply Subtype.ext
    apply hunique f.1
    refine ⟨hf.2.1, ?_, hf.2.2.2⟩
    intro hfd
    apply hf.2.2.1
    exact Subtype.ext hfd

/-- The right argument of the fixed-cell pairing relation is unique. -/
theorem brResolvedBoundaryPairedAt_right_unique
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    {z : DualSquareVertex} {d e f : BRStoppedInterfaceEdge n R}
    (hde : brResolvedBoundaryPairedAt z d e)
    (hdf : brResolvedBoundaryPairedAt z d f) :
    e = f := by
  rcases existsUnique_brResolvedBoundaryPartnerAt z d hde.1 with ⟨g, _hg, hunique⟩
  exact (hunique e hde).trans (hunique f hdf).symm

/-- The locally resolved stopped-interface graph.  An edge records a resolved pairing at some
common dual-coordinate unit cell. -/
def brResolvedBoundaryGraph
    (n : ℕ) (R : Finset (BRLeftmostDualVertex n)) :
    SimpleGraph (BRStoppedInterfaceEdge n R) where
  Adj d e := ∃ z : DualSquareVertex, brResolvedBoundaryPairedAt z d e
  symm := by
    rintro d e ⟨z, hde⟩
    exact ⟨z, brResolvedBoundaryPairedAt_comm.mp hde⟩
  loopless := ⟨by
    intro d hdd
    rcases hdd with ⟨z, hdd⟩
    exact not_brResolvedBoundaryPairedAt_self z d hdd⟩

@[simp]
theorem brResolvedBoundaryGraph_adj_iff
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    {d e : BRStoppedInterfaceEdge n R} :
    (brResolvedBoundaryGraph n R).Adj d e ↔
      ∃ z : DualSquareVertex, brResolvedBoundaryPairedAt z d e :=
  Iff.rfl

/-- The resolved graph has only finitely many edges. -/
theorem brResolvedBoundaryGraph_edgeSet_finite
    (n : ℕ) (R : Finset (BRLeftmostDualVertex n)) :
    (brResolvedBoundaryGraph n R).edgeSet.Finite :=
  Set.toFinite _

/-- The support of the resolved graph is finite. -/
theorem brResolvedBoundaryGraph_support_finite
    (n : ℕ) (R : Finset (BRLeftmostDualVertex n)) :
    (brResolvedBoundaryGraph n R).support.Finite :=
  Set.toFinite _

/-- Incidence at a fixed cell supplies an edge of the resolved graph.  This is only an
existence statement: another cell incident to the same boundary bond may supply another graph
neighbor. -/
theorem exists_brResolvedBoundaryGraph_adj_of_incidentAt
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (z : DualSquareVertex) (d : BRStoppedInterfaceEdge n R)
    (hd : brStoppedInterfaceIncidentAt z d) :
    ∃ e : BRStoppedInterfaceEdge n R,
      (brResolvedBoundaryGraph n R).Adj d e ∧ brResolvedBoundaryPairedAt z d e := by
  rcases existsUnique_brResolvedBoundaryPartnerAt z d hd with ⟨e, he, _hunique⟩
  exact ⟨e, ⟨z, he⟩, he⟩

end

end Percolation
