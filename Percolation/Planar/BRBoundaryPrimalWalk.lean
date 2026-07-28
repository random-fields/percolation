import Percolation.Planar.BRFiberGeometry
import Percolation.Planar.BRTruncatedBoundary
import Percolation.Planar.BRTruncatedPorts
import Mathlib.Combinatorics.SimpleGraph.LineGraph

/-!
# Primal walks carried by the truncated resolved boundary

The vertices of the truncated resolved boundary graph are dual interface bonds.  Each such
bond crosses a canonical primal bond.  This file records the local geometry needed to turn a
resolved-boundary walk into a primal square-lattice connection.
-/

namespace Percolation

open SimpleGraph
open scoped Sym2

noncomputable section

/-- The primal corner shared by the bonds crossing any two sides paired at the dual cell `z`. -/
def brPairingPrimalVertex (z : DualSquareVertex) : SquareVertex :=
  squareVertex (z 0 + 1) (z 1 + 1)

/-- The primal bond crossing a stopped-interface side incident to `z` contains the northeast
corner of that dual-coordinate cell. -/
theorem brPairingPrimalVertex_mem_crossedPrimalEdge_of_incidentAt
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    {z : DualSquareVertex} {d : BRStoppedInterfaceEdge n R}
    (hd : brStoppedInterfaceIncidentAt z d) :
    brPairingPrimalVertex z ∈
      ((brStoppedInterfacePrimalPositiveEdge d).toEdge : Sym2 SquareVertex) := by
  classical
  rcases d with ⟨d, hdBoundary⟩
  change d ∈ squareCellBoundaryPositiveEdges (brReachedDualFace n R) z at hd
  have hdCell : d ∈ squareCellPositiveEdges z :=
    (Finset.mem_filter.mp hd).1
  simp [squareCellPositiveEdges, squareCellPositiveEdgeList] at hdCell
  rcases hdCell with rfl | rfl | rfl | rfl
  · simp [brPairingPrimalVertex, brStoppedInterfacePrimalPositiveEdge,
      dualToPrimalCrossingPositiveEdge, SquarePositiveEdge.toEdge,
      squarePerp, cubicStepFrom, cubicDirectionIncrement, Sym2.mem_iff]
    right
    ext i
    fin_cases i <;> simp [squareVertex]
  · simp [brPairingPrimalVertex, brStoppedInterfacePrimalPositiveEdge,
      dualToPrimalCrossingPositiveEdge, SquarePositiveEdge.toEdge,
      squarePerp, cubicStepFrom, cubicDirectionIncrement, Sym2.mem_iff]
    left
    ext i
    fin_cases i <;> simp [squareVertex]
  · simp [brPairingPrimalVertex, brStoppedInterfacePrimalPositiveEdge,
      dualToPrimalCrossingPositiveEdge, SquarePositiveEdge.toEdge,
      squarePerp, cubicStepFrom, cubicDirectionIncrement, squareVertex, Sym2.mem_iff]
    left
    ext i
    fin_cases i <;> simp [squareVertex]
  · simp [brPairingPrimalVertex, brStoppedInterfacePrimalPositiveEdge,
      dualToPrimalCrossingPositiveEdge, SquarePositiveEdge.toEdge,
      squarePerp, cubicStepFrom, cubicDirectionIncrement, Sym2.mem_iff]
    right
    ext i
    fin_cases i <;> simp [squareVertex]

/-- Locally resolved paired dual sides cross primal bonds with a common endpoint.  This statement
also covers the degree-four split case: the split tag selects the pair, while incidence alone
identifies the common primal corner. -/
theorem brResolvedBoundaryPairedAt_crossedPrimalEdges_share_vertex
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    {z : DualSquareVertex} {d e : BRStoppedInterfaceEdge n R}
    (hde : brResolvedBoundaryPairedAt z d e) :
    brPairingPrimalVertex z ∈
        ((brStoppedInterfacePrimalPositiveEdge d).toEdge : Sym2 SquareVertex) ∧
      brPairingPrimalVertex z ∈
        ((brStoppedInterfacePrimalPositiveEdge e).toEdge : Sym2 SquareVertex) :=
  ⟨brPairingPrimalVertex_mem_crossedPrimalEdge_of_incidentAt hde.1,
    brPairingPrimalVertex_mem_crossedPrimalEdge_of_incidentAt hde.2.1⟩

/-- The canonical primal bond crossed by a retained truncated-interface bond. -/
def brTruncatedInterfacePrimalEdge
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (d : BRTruncatedInterfaceEdge n R) : SquareEdge :=
  (brStoppedInterfacePrimalPositiveEdge d.toStopped).toEdge

/-! ### Primal endpoints selected by the horizontal ports -/

/-- The lower endpoint of the vertical primal bond crossed by a bottom horizontal dual port. -/
def brBottomPortPrimalVertex (d : DualSquarePositiveEdge) : SquareVertex :=
  (dualToPrimalCrossingPositiveEdge d).base

/-- The upper endpoint of the vertical primal bond crossed by a top horizontal dual port. -/
def brTopPortPrimalVertex (d : DualSquarePositiveEdge) : SquareVertex :=
  cubicStepFrom (dualToPrimalCrossingPositiveEdge d).base
    ((dualToPrimalCrossingPositiveEdge d).axis, true)

/-- The selected bottom-port vertex is an endpoint of the crossed primal bond. -/
theorem brBottomPortPrimalVertex_mem_crossedPrimalEdge
    (d : DualSquarePositiveEdge) :
    brBottomPortPrimalVertex d ∈
      ((dualToPrimalCrossingPositiveEdge d).toEdge : Sym2 SquareVertex) := by
  simp [brBottomPortPrimalVertex, SquarePositiveEdge.toEdge, Sym2.mem_iff]

/-- The selected top-port vertex is an endpoint of the crossed primal bond. -/
theorem brTopPortPrimalVertex_mem_crossedPrimalEdge
    (d : DualSquarePositiveEdge) :
    brTopPortPrimalVertex d ∈
      ((dualToPrimalCrossingPositiveEdge d).toEdge : Sym2 SquareVertex) := by
  simp [brTopPortPrimalVertex, SquarePositiveEdge.toEdge, Sym2.mem_iff]

/-- The raw coordinate data of a bottom horizontal dual port select a primal endpoint on the
bottom side of the centered square. -/
theorem brBottomPortPrimalVertex_coordinates
    {n : ℕ} {d : DualSquarePositiveEdge}
    (haxis : d.axis = (0 : Fin 2)) (hbottom : d.base 1 = -(n : ℤ))
    (hleft : -1 ≤ d.base 0) (hright : d.base 0 < 2 * (n : ℤ)) :
    0 ≤ brBottomPortPrimalVertex d 0 ∧
      brBottomPortPrimalVertex d 0 ≤ 2 * (n : ℤ) ∧
        brBottomPortPrimalVertex d 1 = -(n : ℤ) := by
  rcases d with ⟨base, axis⟩
  change axis = 0 at haxis
  subst axis
  change base 1 = -(n : ℤ) at hbottom
  change -1 ≤ base 0 at hleft
  change base 0 < 2 * (n : ℤ) at hright
  simp [brBottomPortPrimalVertex, dualToPrimalCrossingPositiveEdge,
    cubicStepFrom, cubicDirectionIncrement, squarePerp]
  omega

/-- The raw coordinate data of a top horizontal dual port select a primal endpoint on the top
side of the centered square. -/
theorem brTopPortPrimalVertex_coordinates
    {n : ℕ} {d : DualSquarePositiveEdge}
    (haxis : d.axis = (0 : Fin 2)) (htop : d.base 1 = (n : ℤ) - 1)
    (hleft : -1 ≤ d.base 0) (hright : d.base 0 < 2 * (n : ℤ)) :
    0 ≤ brTopPortPrimalVertex d 0 ∧
      brTopPortPrimalVertex d 0 ≤ 2 * (n : ℤ) ∧
        brTopPortPrimalVertex d 1 = (n : ℤ) := by
  rcases d with ⟨base, axis⟩
  change axis = 0 at haxis
  subst axis
  change base 1 = (n : ℤ) - 1 at htop
  change -1 ≤ base 0 at hleft
  change base 0 < 2 * (n : ℤ) at hright
  simp [brTopPortPrimalVertex, dualToPrimalCrossingPositiveEdge,
    cubicStepFrom, cubicDirectionIncrement, squarePerp]
  omega

/-- Coordinate form specialized to raw membership in the retained bottom-port finset. -/
theorem brBottomPortPrimalVertex_coordinates_of_mem
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    {d : DualSquarePositiveEdge}
    (hd : d ∈ brTruncatedBottomBoundaryEdges n R) :
    0 ≤ brBottomPortPrimalVertex d 0 ∧
      brBottomPortPrimalVertex d 0 ≤ 2 * (n : ℤ) ∧
        brBottomPortPrimalVertex d 1 = -(n : ℤ) := by
  have hport := mem_brTruncatedBottomBoundaryEdges_iff.mp hd
  have hbounds := brTruncatedBottomBoundaryEdges_base_bounds hd
  exact brBottomPortPrimalVertex_coordinates
    hport.2.1 hport.2.2 hbounds.1 hbounds.2

/-- Coordinate form specialized to raw membership in the retained top-port finset. -/
theorem brTopPortPrimalVertex_coordinates_of_mem
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    {d : DualSquarePositiveEdge}
    (hd : d ∈ brTruncatedTopBoundaryEdges n R) :
    0 ≤ brTopPortPrimalVertex d 0 ∧
      brTopPortPrimalVertex d 0 ≤ 2 * (n : ℤ) ∧
        brTopPortPrimalVertex d 1 = (n : ℤ) := by
  have hport := mem_brTruncatedTopBoundaryEdges_iff.mp hd
  have hbounds := brTruncatedTopBoundaryEdges_base_bounds hd
  exact brTopPortPrimalVertex_coordinates
    hport.2.1 hport.2.2 hbounds.1 hbounds.2

/-- The bottom endpoint selected from a retained interface subtype lies on its canonical crossed
primal bond. -/
theorem brBottomPortPrimalVertex_mem_truncatedInterfacePrimalEdge
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (d : BRTruncatedInterfaceEdge n R) :
    brBottomPortPrimalVertex d.1 ∈
      (brTruncatedInterfacePrimalEdge d : Sym2 SquareVertex) :=
  brBottomPortPrimalVertex_mem_crossedPrimalEdge d.1

/-- The top endpoint selected from a retained interface subtype lies on its canonical crossed
primal bond. -/
theorem brTopPortPrimalVertex_mem_truncatedInterfacePrimalEdge
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (d : BRTruncatedInterfaceEdge n R) :
    brTopPortPrimalVertex d.1 ∈
      (brTruncatedInterfacePrimalEdge d : Sym2 SquareVertex) :=
  brTopPortPrimalVertex_mem_crossedPrimalEdge d.1

/-- A bottom-port vertex of the truncated graph supplies both the endpoint proof needed by the
primal-walk conversion and the three coordinates needed for bottom-side membership. -/
theorem brTruncatedBottomBoundaryVertex_primalEndpoint
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    {d : BRTruncatedInterfaceEdge n R}
    (hd : d ∈ brTruncatedBottomBoundaryVertices n R) :
    brBottomPortPrimalVertex d.1 ∈
        (brTruncatedInterfacePrimalEdge d : Sym2 SquareVertex) ∧
      0 ≤ brBottomPortPrimalVertex d.1 0 ∧
      brBottomPortPrimalVertex d.1 0 ≤ 2 * (n : ℤ) ∧
        brBottomPortPrimalVertex d.1 1 = -(n : ℤ) := by
  refine ⟨brBottomPortPrimalVertex_mem_truncatedInterfacePrimalEdge d, ?_⟩
  exact brBottomPortPrimalVertex_coordinates_of_mem
    (mem_brTruncatedBottomBoundaryVertices_iff.mp hd)

/-- A top-port vertex of the truncated graph supplies both the endpoint proof needed by the
primal-walk conversion and the three coordinates needed for top-side membership. -/
theorem brTruncatedTopBoundaryVertex_primalEndpoint
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    {d : BRTruncatedInterfaceEdge n R}
    (hd : d ∈ brTruncatedTopBoundaryVertices n R) :
    brTopPortPrimalVertex d.1 ∈
        (brTruncatedInterfacePrimalEdge d : Sym2 SquareVertex) ∧
      0 ≤ brTopPortPrimalVertex d.1 0 ∧
      brTopPortPrimalVertex d.1 0 ≤ 2 * (n : ℤ) ∧
        brTopPortPrimalVertex d.1 1 = (n : ℤ) := by
  refine ⟨brTopPortPrimalVertex_mem_truncatedInterfacePrimalEdge d, ?_⟩
  exact brTopPortPrimalVertex_coordinates_of_mem
    (mem_brTruncatedTopBoundaryVertices_iff.mp hd)

@[simp]
theorem brReachedDualFace_subtype_val_iff
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    {z : BRLeftmostDualVertex n} :
    brReachedDualFace n R z.1 ↔ z ∈ R := by
  simp [brReachedDualFace, brReachedFaceCoordinates,
    brLeftmostDualVertexValEmbedding]

/-- Crossing the canonical primal bond recovers the retained positive dual bond. -/
theorem squarePositiveEdgeDualCrossingEmbedding_brTruncatedInterfacePrimalEdge
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (d : BRTruncatedInterfaceEdge n R) :
    squarePositiveEdgeDualCrossingEmbedding
        (brStoppedInterfacePrimalPositiveEdge d.toStopped) = d.1.toEdge := by
  unfold squarePositiveEdgeDualCrossingEmbedding squareEdgeDualCrossingEquiv
  simp only [Function.Embedding.trans_apply, Equiv.toEmbedding_apply,
    Equiv.trans_apply]
  rw [SquarePositiveEdge.edgeEquiv_symm_squarePositiveEdgeEmbedding]
  change (primalToDualCrossingPositiveEdge
    (dualToPrimalCrossingPositiveEdge d.1)).toEdge = d.1.toEdge
  rw [primalToDual_dualToPrimalCrossingPositiveEdge]

/-- Adjacent retained boundary bonds cross distinct primal bonds with a common endpoint. -/
theorem brTruncatedInterfacePrimalEdge_adj
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    {d e : BRTruncatedInterfaceEdge n R}
    (hde : (brTruncatedResolvedBoundaryGraph n R).Adj d e) :
    brTruncatedInterfacePrimalEdge d ≠ brTruncatedInterfacePrimalEdge e ∧
      ∃ v : SquareVertex,
        v ∈ (brTruncatedInterfacePrimalEdge d : Sym2 SquareVertex) ∧
          v ∈ (brTruncatedInterfacePrimalEdge e : Sym2 SquareVertex) := by
  rcases brTruncatedResolvedBoundaryGraph_adj_iff.mp hde with ⟨z, _hz, hpair⟩
  refine ⟨?_, brPairingPrimalVertex z, ?_⟩
  · intro hedges
    have hpositive :
        brStoppedInterfacePrimalPositiveEdge d.toStopped =
          brStoppedInterfacePrimalPositiveEdge e.toStopped :=
      SquarePositiveEdge.toEdge_injective hedges
    have hstopped : d.toStopped = e.toStopped :=
      brStoppedInterfacePrimalPositiveEdge_injective hpositive
    exact hpair.2.2.1 hstopped.symm
  · exact brResolvedBoundaryPairedAt_crossedPrimalEdges_share_vertex hpair

/-- Crossing retained interface bonds defines a homomorphism from the resolved boundary into
the line graph of the primal square lattice. -/
def brTruncatedBoundaryToPrimalLineGraphHom
    (n : ℕ) (R : Finset (BRLeftmostDualVertex n)) :
    brTruncatedResolvedBoundaryGraph n R →g squareGraph.lineGraph where
  toFun := brTruncatedInterfacePrimalEdge
  map_rel' := by
    intro d e hde
    rw [SimpleGraph.lineGraph_adj_iff_exists]
    exact brTruncatedInterfacePrimalEdge_adj hde

/-- The canonical primal line-graph walk carried by a walk in the truncated resolved boundary. -/
def brTruncatedBoundaryWalkToPrimalLineGraphWalk
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    {d e : BRTruncatedInterfaceEdge n R}
    (w : (brTruncatedResolvedBoundaryGraph n R).Walk d e) :
    squareGraph.lineGraph.Walk
      (brTruncatedInterfacePrimalEdge d) (brTruncatedInterfacePrimalEdge e) :=
  w.map (brTruncatedBoundaryToPrimalLineGraphHom n R)

/-- Every retained interface bond crosses an allowed primal bond which is open on the realized
reached-face fiber. -/
theorem brTruncatedInterfacePrimalEdge_mem_boundaryFree_and_configuration
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    {omega : EdgeConfiguration 2}
    (homega : omega ∈ brReachableFaceFiber n R)
    (d : BRTruncatedInterfaceEdge n R) :
    brTruncatedInterfacePrimalEdge d ∈
        squareBoundaryFreeRectangleEdges (2 * n) n ∧
      brTruncatedInterfacePrimalEdge d ∈ omega := by
  have hd := mem_brTruncatedDualBoundaryPositiveEdges_iff.mp d.2
  let x : BRLeftmostDualVertex n := ⟨d.1.base, hd.2.1⟩
  let y : BRLeftmostDualVertex n :=
    ⟨cubicStepFrom d.1.base (d.1.axis, true), hd.2.2.1⟩
  have hxy : (brLeftmostDualGraph n).Adj x y := by
    rw [brLeftmostDualGraph_adj_iff]
    exact cubicGraph_adj_stepFrom d.1.base (d.1.axis, true)
  have hchange : ¬(x ∈ R ↔ y ∈ R) := by
    have hchangeFaces := hd.1
    change ¬(brReachedDualFace n R x.1 ↔ brReachedDualFace n R y.1) at hchangeFaces
    simpa only [brReachedDualFace_subtype_val_iff] using hchangeFaces
  have hforward :
      squareEdgeDualCrossingEquiv.symm
          (brLeftmostDualEdgeEmbedding n
            ⟨s(x, y), (brLeftmostDualGraph n).mem_edgeSet.mpr hxy⟩) =
        brTruncatedInterfacePrimalEdge d := by
    calc
      squareEdgeDualCrossingEquiv.symm
          (brLeftmostDualEdgeEmbedding n
            ⟨s(x, y), (brLeftmostDualGraph n).mem_edgeSet.mpr hxy⟩) =
          squareEdgeDualCrossingEquiv.symm
            (squarePositiveEdgeDualCrossingEmbedding
              (brStoppedInterfacePrimalPositiveEdge d.toStopped)) := by
                apply congrArg squareEdgeDualCrossingEquiv.symm
                rw [squarePositiveEdgeDualCrossingEmbedding_brTruncatedInterfacePrimalEdge]
                apply Subtype.ext
                rfl
      _ = brTruncatedInterfacePrimalEdge d :=
        squareEdgeDualCrossingEquiv_symm_squarePositiveEdgeDualCrossingEmbedding _
  have hreverse :
      squareEdgeDualCrossingEquiv.symm
          (brLeftmostDualEdgeEmbedding n
            ⟨s(y, x), (brLeftmostDualGraph n).mem_edgeSet.mpr hxy.symm⟩) =
        brTruncatedInterfacePrimalEdge d := by
    calc
      squareEdgeDualCrossingEquiv.symm
          (brLeftmostDualEdgeEmbedding n
            ⟨s(y, x), (brLeftmostDualGraph n).mem_edgeSet.mpr hxy.symm⟩) =
          squareEdgeDualCrossingEquiv.symm
            (squarePositiveEdgeDualCrossingEmbedding
              (brStoppedInterfacePrimalPositiveEdge d.toStopped)) := by
                apply congrArg squareEdgeDualCrossingEquiv.symm
                rw [squarePositiveEdgeDualCrossingEmbedding_brTruncatedInterfacePrimalEdge]
                apply Subtype.ext
                exact Sym2.eq_swap
      _ = brTruncatedInterfacePrimalEdge d :=
        squareEdgeDualCrossingEquiv_symm_squarePositiveEdgeDualCrossingEmbedding _
  change brLeftReachableFaces n omega = R at homega
  by_cases hxR : x ∈ R
  · have hyR : y ∉ R := by
      intro hyR
      exact hchange (iff_of_true hxR hyR)
    have hx : x ∈ brLeftReachableFaces n omega := by
      rw [homega]
      exact hxR
    have hy : y ∉ brLeftReachableFaces n omega := by
      rw [homega]
      exact hyR
    simpa [hforward] using
      (brCutCrossedPrimalEdge_mem_boundaryFree_and_configuration hx hy hxy)
  · have hyR : y ∈ R := by
      by_contra hyR
      exact hchange (iff_of_false hxR hyR)
    have hy : y ∈ brLeftReachableFaces n omega := by
      rw [homega]
      exact hyR
    have hx : x ∉ brLeftReachableFaces n omega := by
      rw [homega]
      exact hxR
    simpa [hreverse] using
      (brCutCrossedPrimalEdge_mem_boundaryFree_and_configuration hy hx hxy.symm)

/-- Two endpoints of one open square-lattice bond are joined by an open primal walk. -/
private theorem exists_open_primalWalk_of_mem_edge
    {omega : EdgeConfiguration 2} {e : SquareEdge} {x y : SquareVertex}
    (heOpen : e ∈ omega) (hx : x ∈ (e : Sym2 SquareVertex))
    (hy : y ∈ (e : Sym2 SquareVertex)) :
    ∃ p : squareGraph.Walk x y, walkIsOpen omega p := by
  by_cases hxy : x = y
  · subst y
    exact ⟨SimpleGraph.Walk.nil, by simp [walkIsOpen]⟩
  · have hedge : s(x, y) = (e : Sym2 SquareVertex) := by
      rw [← e.1.out_eq, Sym2.mem_iff] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact (hxy rfl).elim
      · exact e.1.out_eq
      · exact Sym2.eq_swap.trans e.1.out_eq
      · exact (hxy rfl).elim
    have hadj : squareGraph.Adj x y := by
      rw [← squareGraph.mem_edgeSet, hedge]
      exact e.2
    let step : squareGraph.Walk x y :=
      SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil
    refine ⟨step, ?_⟩
    intro f hf
    have hfe :
        (⟨f, step.edges_subset_edgeSet hf⟩ : SquareEdge) = e := by
      apply Subtype.ext
      have hfxy : f = s(x, y) := by simpa [step] using hf
      exact hfxy.trans hedge
    simpa [hfe] using heOpen

/-- Two endpoints of one open allowed square-lattice bond are joined by an open walk using only
allowed bonds. -/
private theorem exists_open_primalWalkIn_of_mem_edge
    {omega : EdgeConfiguration 2} {allowed : Finset SquareEdge}
    {e : SquareEdge} {x y : SquareVertex}
    (heOpen : e ∈ omega) (heAllowed : e ∈ allowed)
    (hx : x ∈ (e : Sym2 SquareVertex))
    (hy : y ∈ (e : Sym2 SquareVertex)) :
    ∃ p : squareGraph.Walk x y,
      walkIsOpen omega p ∧ walkEdgeFinset p ⊆ allowed := by
  by_cases hxy : x = y
  · subst y
    refine ⟨SimpleGraph.Walk.nil, by simp [walkIsOpen], ?_⟩
    intro f hf
    rw [mem_walkEdgeFinset_iff] at hf
    simp at hf
  · have hedge : s(x, y) = (e : Sym2 SquareVertex) := by
      rw [← e.1.out_eq, Sym2.mem_iff] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact (hxy rfl).elim
      · exact e.1.out_eq
      · exact Sym2.eq_swap.trans e.1.out_eq
      · exact (hxy rfl).elim
    have hadj : squareGraph.Adj x y := by
      rw [← squareGraph.mem_edgeSet, hedge]
      exact e.2
    let step : squareGraph.Walk x y :=
      SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil
    refine ⟨step, ?_, ?_⟩
    · intro f hf
      have hfe :
          (⟨f, step.edges_subset_edgeSet hf⟩ : SquareEdge) = e := by
        apply Subtype.ext
        have hfxy : f = s(x, y) := by simpa [step] using hf
        exact hfxy.trans hedge
      simpa [hfe] using heOpen
    · intro f hf
      have hfEdges : (f : Sym2 SquareVertex) ∈ step.edges :=
        (mem_walkEdgeFinset_iff step f).mp hf
      have hfe : f = e := by
        apply Subtype.ext
        have hfxy : (f : Sym2 SquareVertex) = s(x, y) := by
          simpa [step] using hfEdges
        exact hfxy.trans hedge
      simpa [hfe] using heAllowed

/-- A resolved-boundary walk produces an open primal square-lattice walk between arbitrary
endpoints of its first and last crossed bonds.  This avoids any orientation choice: at each
boundary step, the local pairing supplies the common primal vertex used for concatenation. -/
theorem brTruncatedBoundaryWalk_exists_open_primalWalk
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    {omega : EdgeConfiguration 2}
    (homega : omega ∈ brReachableFaceFiber n R)
    {d e : BRTruncatedInterfaceEdge n R}
    (w : (brTruncatedResolvedBoundaryGraph n R).Walk d e)
    {x y : SquareVertex}
    (hx : x ∈ (brTruncatedInterfacePrimalEdge d : Sym2 SquareVertex))
    (hy : y ∈ (brTruncatedInterfacePrimalEdge e : Sym2 SquareVertex)) :
    ∃ p : squareGraph.Walk x y, walkIsOpen omega p := by
  induction w generalizing x with
  | nil =>
      exact exists_open_primalWalk_of_mem_edge
        (brTruncatedInterfacePrimalEdge_mem_boundaryFree_and_configuration homega _).2 hx hy
  | @cons u v z huv tail ih =>
      rcases brTruncatedInterfacePrimalEdge_adj huv with
        ⟨_hne, common, hcommonU, hcommonV⟩
      obtain ⟨p, hp⟩ := exists_open_primalWalk_of_mem_edge
        (brTruncatedInterfacePrimalEdge_mem_boundaryFree_and_configuration homega u).2
        hx hcommonU
      obtain ⟨q, hq⟩ := ih hcommonV hy
      exact ⟨p.append q, walkIsOpen_append hp hq⟩

/-- Boundary-free strengthening of `brTruncatedBoundaryWalk_exists_open_primalWalk`, in exactly
the witness shape required by `connectionEventIn`. -/
theorem brTruncatedBoundaryWalk_exists_open_primalWalkIn
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    {omega : EdgeConfiguration 2}
    (homega : omega ∈ brReachableFaceFiber n R)
    {d e : BRTruncatedInterfaceEdge n R}
    (w : (brTruncatedResolvedBoundaryGraph n R).Walk d e)
    {x y : SquareVertex}
    (hx : x ∈ (brTruncatedInterfacePrimalEdge d : Sym2 SquareVertex))
    (hy : y ∈ (brTruncatedInterfacePrimalEdge e : Sym2 SquareVertex)) :
    ∃ p : squareGraph.Walk x y,
      walkIsOpen omega p ∧
        walkEdgeFinset p ⊆ squareBoundaryFreeRectangleEdges (2 * n) n := by
  induction w generalizing x with
  | @nil u =>
      have hedge :=
        brTruncatedInterfacePrimalEdge_mem_boundaryFree_and_configuration homega u
      exact exists_open_primalWalkIn_of_mem_edge hedge.2 hedge.1 hx hy
  | @cons u v z huv tail ih =>
      rcases brTruncatedInterfacePrimalEdge_adj huv with
        ⟨_hne, common, hcommonU, hcommonV⟩
      have huEdge :=
        brTruncatedInterfacePrimalEdge_mem_boundaryFree_and_configuration homega u
      obtain ⟨p, hpOpen, hpAllowed⟩ := exists_open_primalWalkIn_of_mem_edge
        huEdge.2 huEdge.1 hx hcommonU
      obtain ⟨q, hqOpen, hqAllowed⟩ := ih hcommonV hy
      refine ⟨p.append q, walkIsOpen_append hpOpen hqOpen, ?_⟩
      intro f hf
      rw [mem_walkEdgeFinset_iff, SimpleGraph.Walk.edges_append,
        List.mem_append] at hf
      rcases hf with hf | hf
      · exact hpAllowed ((mem_walkEdgeFinset_iff p f).mpr hf)
      · exact hqAllowed ((mem_walkEdgeFinset_iff q f).mpr hf)

end

end Percolation
