import Percolation.Planar.BRFilledHull
import Percolation.Planar.BRFirstContact
import Percolation.Planar.BRExplorationAlternative

/-!
# The outer interface of the filled BR exploration

The filled reached set and its right complement are connected.  This file uses the mod-two
face-index API to show that its selected bottom--top interface is the whole cut between those
two regions.  This is the finite, deterministic outermost property needed by the fresh-contact
argument: no queried reached-face coordinate can lie strictly to the right of the selected
interface.
-/

namespace Percolation

open SimpleGraph
open scoped Sym2

noncomputable section

local instance instDecidableRelBROuterInterface (n : ℕ) :
    DecidableRel (brLeftmostDualGraph n).Adj :=
  Classical.decRel _

/-- Horizontal coordinate of the selected lower endpoint, as a natural number. -/
private def brFilledHullSelectedBottomNat
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) : ℕ :=
  Int.toNat ((brSelectedBottomPrimalVertex hn hR.filledHull) 0)

/-- Horizontal coordinate of the selected upper endpoint, as a natural number. -/
private def brFilledHullSelectedTopNat
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) : ℕ :=
  Int.toNat ((brSelectedTopPrimalVertex hn hR.filledHull) 0)

private theorem brFilledHullSelectedBottomNat_cast
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    (brFilledHullSelectedBottomNat hn hR : ℤ) =
      (brSelectedBottomPrimalVertex hn hR.filledHull) 0 := by
  have hb := mem_brSquareBottomSide_iff.mp
    (brSelectedBottomPrimalVertex_mem_bottomSide hn hR.filledHull)
  exact Int.toNat_of_nonneg hb.1

private theorem brFilledHullSelectedTopNat_cast
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    (brFilledHullSelectedTopNat hn hR : ℤ) =
      (brSelectedTopPrimalVertex hn hR.filledHull) 0 := by
  have ht := mem_brSquareTopSide_iff.mp
    (brSelectedTopPrimalVertex_mem_topSide hn hR.filledHull)
  exact Int.toNat_of_nonneg ht.1

/-- The selected filled-hull crossing with endpoints normalized to explicit integer-coordinate
vertices, as required by the exterior-closure parity API. -/
private def brFilledHullSelectedPrimalWalkNormalized
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    squareGraph.Walk
      (squareVertex (brFilledHullSelectedBottomNat hn hR : ℤ) (-(n : ℤ)))
      (squareVertex (brFilledHullSelectedTopNat hn hR : ℤ) (n : ℤ)) :=
  (brSelectedPrimalWalk hn hR.filledHull).copy
    (by
      ext i
      fin_cases i
      · exact (brFilledHullSelectedBottomNat_cast hn hR).symm
      · have hb := mem_brSquareBottomSide_iff.mp
          (brSelectedBottomPrimalVertex_mem_bottomSide hn hR.filledHull)
        simpa [squareVertex] using hb.2.2)
    (by
      ext i
      fin_cases i
      · exact (brFilledHullSelectedTopNat_cast hn hR).symm
      · have ht := mem_brSquareTopSide_iff.mp
          (brSelectedTopPrimalVertex_mem_topSide hn hR.filledHull)
        simpa [squareVertex] using ht.2.2)

/-- Close the selected bottom--top crossing along the deterministic left exterior. -/
private def brFilledHullSelectedClosedWalk
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    squareGraph.Walk
      (squareVertex (brFilledHullSelectedBottomNat hn hR : ℤ) (-(n : ℤ)))
      (squareVertex (brFilledHullSelectedBottomNat hn hR : ℤ) (-(n : ℤ))) :=
  (brFilledHullSelectedPrimalWalkNormalized hn hR).append
    (brLeftExteriorClosureWalk n
      (brFilledHullSelectedBottomNat hn hR)
      (brFilledHullSelectedTopNat hn hR))

private theorem brFilledHullSelectedPrimalWalkNormalized_support_coordinates
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R)
    {z : SquareVertex}
    (hz : z ∈ (brFilledHullSelectedPrimalWalkNormalized hn hR).support) :
    0 ≤ z 0 ∧ z 0 ≤ 2 * (n : ℤ) ∧
      -(n : ℤ) ≤ z 1 ∧ z 1 ≤ (n : ℤ) := by
  apply brSelectedPrimalWalk_support_coordinates hn hR.filledHull
  simpa [brFilledHullSelectedPrimalWalkNormalized] using hz

private theorem brFilledHullSelectedPrimalWalkNormalized_edges_iff
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R)
    (e : SquareEdge) :
    e ∈ walkEdgeFinset (brFilledHullSelectedPrimalWalkNormalized hn hR) ↔
      e ∈ walkEdgeFinset (brSelectedPrimalWalk hn hR.filledHull) := by
  simp [mem_walkEdgeFinset_iff, brFilledHullSelectedPrimalWalkNormalized,
    SimpleGraph.Walk.edges_copy]

private theorem brFilledHullSelectedClosedWalk_parity_ne_source_target
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R)
    {a r : BRLeftmostDualVertex n}
    (ha : a ∈ brLeftmostDualSources n)
    (hr : r ∈ brRightmostDualTargets n) :
    closedSquareWalkFaceParity (brFilledHullSelectedClosedWalk hn hR) a.1 ≠
      closedSquareWalkFaceParity (brFilledHullSelectedClosedWalk hn hR) r.1 := by
  have haFrame := mem_brLeftmostDualFaces_iff.mp a.2
  apply brClosedBottomTopWalk_faceParity_ne
    (brFilledHullSelectedPrimalWalkNormalized hn hR)
    (fun z hz ↦ brFilledHullSelectedPrimalWalkNormalized_support_coordinates hn hR hz)
  · exact mem_brLeftmostDualSources_iff.mp ha
  · exact haFrame.2.2.1
  · exact haFrame.2.2.2
  · exact mem_brRightmostDualTargets_iff.mp hr

/-- Face parity is constant along a frame walk which stays wholly on one side of the filled-hull
cut.  If parity changed, the crossing-parity theorem would find a selected-interface bond
crossing an edge of that walk, contradicting constancy of hull membership at its endpoints. -/
private theorem brFilledHullSelectedClosedWalk_parity_eq_of_frameWalk_constant
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R)
    {u v : BRLeftmostDualVertex n}
    (w : (brLeftmostDualGraph n).Walk u v)
    (hsame : ∀ z ∈ w.support,
      (z ∈ brFilledReachableHull n R ↔ u ∈ brFilledReachableHull n R)) :
    closedSquareWalkFaceParity (brFilledHullSelectedClosedWalk hn hR) u.1 =
      closedSquareWalkFaceParity (brFilledHullSelectedClosedWalk hn hR) v.1 := by
  let q := w.map (brLeftmostDualToAmbientHom n)
  have hqFrame : ∀ z ∈ q.support, z ∈ brLeftmostDualFaces n := by
    intro z hz
    simp only [q, SimpleGraph.Walk.support_map, List.mem_map] at hz
    rcases hz with ⟨zFrame, _hzFrame, rfl⟩
    exact zFrame.2
  have hqSame : ∀ z ∈ q.support,
      (brReachedDualFace n (brFilledReachableHull n R) z ↔
        u ∈ brFilledReachableHull n R) := by
    intro z hz
    simp only [q, SimpleGraph.Walk.support_map, List.mem_map] at hz
    rcases hz with ⟨zFrame, hzFrame, rfl⟩
    exact brReachedDualFace_subtype_iff.trans (hsame zFrame hzFrame)
  by_contra hparity
  obtain ⟨ed, hedq, hedc⟩ :=
    exists_dualWalk_edge_crossing_closedWalk_of_faceParity_ne
      (brFilledHullSelectedClosedWalk hn hR) q hparity
  have hedRaw : (ed : Sym2 DualSquareVertex) ∈ q.edges :=
    (mem_walkEdgeFinset_iff q ed).mp hedq
  have hedEndpoints : ∀ z ∈ (ed : Sym2 DualSquareVertex),
      z ∈ brLeftmostDualFaces n := by
    intro z hz
    exact hqFrame z (q.mem_support_of_mem_edges hedRaw hz)
  have hedNotClosure : squareEdgeDualCrossingEquiv.symm ed ∉
      walkEdgeFinset (brLeftExteriorClosureWalk n
        (brFilledHullSelectedBottomNat hn hR)
        (brFilledHullSelectedTopNat hn hR)) :=
    squareEdgeDualCrossingEquiv_symm_not_mem_brLeftExteriorClosureWalk
      ed hedEndpoints
  have hedPrimalNormalized : squareEdgeDualCrossingEquiv.symm ed ∈
      walkEdgeFinset (brFilledHullSelectedPrimalWalkNormalized hn hR) := by
    have hedc' : squareEdgeDualCrossingEquiv.symm ed ∈
        walkEdgeFinset
          ((brFilledHullSelectedPrimalWalkNormalized hn hR).append
            (brLeftExteriorClosureWalk n
              (brFilledHullSelectedBottomNat hn hR)
              (brFilledHullSelectedTopNat hn hR))) := by
      simpa only [brFilledHullSelectedClosedWalk] using hedc
    rw [mem_walkEdgeFinset_iff, SimpleGraph.Walk.edges_append,
      List.mem_append] at hedc'
    rcases hedc' with hp | hclosure
    · exact (mem_walkEdgeFinset_iff _ _).mpr hp
    · exact (hedNotClosure ((mem_walkEdgeFinset_iff _ _).mpr hclosure)).elim
  have hedPrimal : squareEdgeDualCrossingEquiv.symm ed ∈
      walkEdgeFinset (brSelectedPrimalWalk hn hR.filledHull) :=
    (brFilledHullSelectedPrimalWalkNormalized_edges_iff hn hR _).mp
      hedPrimalNormalized
  have hedInterface : squareEdgeDualCrossingEquiv.symm ed ∈
      brTruncatedInterfacePrimalEdges n (brFilledReachableHull n R) :=
    walkEdgeFinset_brSelectedPrimalWalk_subset_interface hn hR.filledHull hedPrimal
  rcases mem_brTruncatedInterfacePrimalEdges_iff.mp hedInterface with ⟨d, hdEq⟩
  have hcrossD : squareEdgeDualCrossingEquiv
      (brTruncatedInterfacePrimalEdge d) = d.1.toEdge := by
    simpa [squarePositiveEdgeDualCrossingEmbedding,
      brTruncatedInterfacePrimalEdge] using
      (squarePositiveEdgeDualCrossingEmbedding_brTruncatedInterfacePrimalEdge d)
  have hedDualEq : ed = d.1.toEdge := by
    calc
      ed = squareEdgeDualCrossingEquiv
          (squareEdgeDualCrossingEquiv.symm ed) :=
        (squareEdgeDualCrossingEquiv.apply_symm_apply ed).symm
      _ = squareEdgeDualCrossingEquiv (brTruncatedInterfacePrimalEdge d) := by
        exact congrArg squareEdgeDualCrossingEquiv hdEq.symm
      _ = d.1.toEdge := hcrossD
  have hbaseSupport : d.1.base ∈ q.support := by
    apply q.mem_support_of_mem_edges hedRaw
    rw [hedDualEq]
    simp [SquarePositiveEdge.toEdge, Sym2.mem_iff]
  have hstepSupport : cubicStepFrom d.1.base (d.1.axis, true) ∈ q.support := by
    apply q.mem_support_of_mem_edges hedRaw
    rw [hedDualEq]
    simp [SquarePositiveEdge.toEdge, Sym2.mem_iff]
  have hbaseStatus := hqSame d.1.base hbaseSupport
  have hstepStatus := hqSame
    (cubicStepFrom d.1.base (d.1.axis, true)) hstepSupport
  have hdBoundary := (mem_brTruncatedDualBoundaryPositiveEdges_iff.mp d.2).1
  exact hdBoundary (hbaseStatus.trans hstepStatus.symm)

private theorem brFilledHullSelectedClosedWalk_parity_eq_source_of_mem
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R)
    {x : BRLeftmostDualVertex n}
    (hx : x ∈ brFilledReachableHull n R) :
    ∃ a ∈ brLeftmostDualSources n,
      closedSquareWalkFaceParity (brFilledHullSelectedClosedWalk hn hR) a.1 =
        closedSquareWalkFaceParity (brFilledHullSelectedClosedWalk hn hR) x.1 := by
  rcases exists_brHullInternalWalk_from_source hR hx with ⟨a, ha, w, hw⟩
  have haHull : a ∈ brFilledReachableHull n R :=
    hR.filledHull.separatingReachedSet.1 ha
  refine ⟨a, ha,
    brFilledHullSelectedClosedWalk_parity_eq_of_frameWalk_constant
      hn hR w ?_⟩
  intro z hz
  have hzHull : z ∈ brFilledReachableHull n R := by
    rw [SimpleGraph.Walk.mem_support_iff_exists_mem_edges] at hz
    rcases hz with rfl | ⟨e, he, hze⟩
    · exact hx
    · exact hw e he z hze
  exact iff_of_true hzHull haHull

private theorem brFilledHullSelectedClosedWalk_parity_eq_target_of_not_mem
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R)
    {x : BRLeftmostDualVertex n}
    (hx : x ∉ brFilledReachableHull n R) :
    ∃ r ∈ brRightmostDualTargets n,
      closedSquareWalkFaceParity (brFilledHullSelectedClosedWalk hn hR) r.1 =
        closedSquareWalkFaceParity (brFilledHullSelectedClosedWalk hn hR) x.1 := by
  rcases exists_brRightComplementWalk_from_target hx with ⟨r, hr, w, hw⟩
  have hrOutside : r ∉ brFilledReachableHull n R := by
    intro hrHull
    exact Finset.disjoint_left.mp
      (disjoint_brFilledReachableHull_rightTargets hR.2) hrHull hr
  refine ⟨r, hr,
    brFilledHullSelectedClosedWalk_parity_eq_of_frameWalk_constant
      hn hR w ?_⟩
  intro z hz
  exact iff_of_false (hw z hz) hrOutside

/-- Every frame cut bond between the filled hull and its right complement belongs to the
selected bottom--top primal interface.  In particular the selector contains the entire outer
cut, not merely an arbitrary parity component. -/
theorem brFilledHullCutCrossedPrimalEdge_mem_selectedWalk
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R)
    {x y : BRLeftmostDualVertex n}
    (hx : x ∈ brFilledReachableHull n R)
    (hy : y ∉ brFilledReachableHull n R)
    (hxy : (brLeftmostDualGraph n).Adj x y) :
    let d : (brLeftmostDualGraph n).edgeSet :=
      ⟨s(x, y), (brLeftmostDualGraph n).mem_edgeSet.mpr hxy⟩
    squareEdgeDualCrossingEquiv.symm (brLeftmostDualEdgeEmbedding n d) ∈
      walkEdgeFinset (brSelectedPrimalWalk hn hR.filledHull) := by
  let d : (brLeftmostDualGraph n).edgeSet :=
    ⟨s(x, y), (brLeftmostDualGraph n).mem_edgeSet.mpr hxy⟩
  let ed : DualSquareEdge := brLeftmostDualEdgeEmbedding n d
  rcases brFilledHullSelectedClosedWalk_parity_eq_source_of_mem
      hn hR hx with ⟨a, ha, hax⟩
  rcases brFilledHullSelectedClosedWalk_parity_eq_target_of_not_mem
      hn hR hy with ⟨r, hr, hry⟩
  have hxyParity :
      closedSquareWalkFaceParity (brFilledHullSelectedClosedWalk hn hR) x.1 ≠
        closedSquareWalkFaceParity (brFilledHullSelectedClosedWalk hn hR) y.1 := by
    intro hxyParity
    exact brFilledHullSelectedClosedWalk_parity_ne_source_target hn hR ha hr
      (hax.trans (hxyParity.trans hry.symm))
  have hxyAmbient : dualSquareGraph.Adj x.1 y.1 := hxy
  have hedUnderlying : (ed : Sym2 DualSquareVertex) = s(x.1, y.1) := by
    simp [ed, d, brLeftmostDualEdgeEmbedding, brLeftmostDualToAmbientHom]
  have hedClosed : squareEdgeDualCrossingEquiv.symm ed ∈
      walkEdgeFinset (brFilledHullSelectedClosedWalk hn hR) := by
    by_contra hnot
    exact hxyParity
      (closedSquareWalkFaceParity_eq_of_dualAdj_of_crossed_not_mem
        (brFilledHullSelectedClosedWalk hn hR) hxyAmbient hnot)
  have hedEndpoints : ∀ z ∈ (ed : Sym2 DualSquareVertex),
      z ∈ brLeftmostDualFaces n := by
    intro z hz
    rw [hedUnderlying, Sym2.mem_iff] at hz
    exact hz.elim (fun h ↦ h ▸ x.2) (fun h ↦ h ▸ y.2)
  have hedNotClosure : squareEdgeDualCrossingEquiv.symm ed ∉
      walkEdgeFinset (brLeftExteriorClosureWalk n
        (brFilledHullSelectedBottomNat hn hR)
        (brFilledHullSelectedTopNat hn hR)) :=
    squareEdgeDualCrossingEquiv_symm_not_mem_brLeftExteriorClosureWalk
      ed hedEndpoints
  have hedNormalized : squareEdgeDualCrossingEquiv.symm ed ∈
      walkEdgeFinset (brFilledHullSelectedPrimalWalkNormalized hn hR) := by
    have hedClosed' : squareEdgeDualCrossingEquiv.symm ed ∈
        walkEdgeFinset
          ((brFilledHullSelectedPrimalWalkNormalized hn hR).append
            (brLeftExteriorClosureWalk n
              (brFilledHullSelectedBottomNat hn hR)
              (brFilledHullSelectedTopNat hn hR))) := by
      simpa only [brFilledHullSelectedClosedWalk] using hedClosed
    rw [mem_walkEdgeFinset_iff, SimpleGraph.Walk.edges_append,
      List.mem_append] at hedClosed'
    rcases hedClosed' with hp | hc
    · exact (mem_walkEdgeFinset_iff _ _).mpr hp
    · exact (hedNotClosure ((mem_walkEdgeFinset_iff _ _).mpr hc)).elim
  exact (brFilledHullSelectedPrimalWalkNormalized_edges_iff hn hR _).mp
    hedNormalized

/-- Along a primal step avoiding a closed primal walk at both endpoints, the face parity based
at the two endpoint coordinates is unchanged.  The dual bond between those two face coordinates
crosses a perpendicular primal bond incident to one of the endpoints. -/
private theorem closedSquareWalkFaceParity_eq_of_primalAdj_of_endpoints_not_mem
    {o u v : SquareVertex} (c : squareGraph.Walk o o)
    (huv : squareGraph.Adj u v)
    (hu : u ∉ c.support) (hv : v ∉ c.support) :
    closedSquareWalkFaceParity c u = closedSquareWalkFaceParity c v := by
  rcases (cubicGraph_adj_iff_exists_stepFrom u v).mp huv with ⟨⟨i, b⟩, rfl⟩
  fin_cases i <;> cases b
  · have h := closedSquareWalkFaceParity_eq_of_positiveDualStep_of_crossed_not_mem c
        (⟨cubicStepFrom u ((0 : Fin 2), false), (0 : Fin 2)⟩ :
          DualSquarePositiveEdge) (by
            intro he
            apply hu
            have heRaw := (mem_walkEdgeFinset_iff c _).mp he
            apply c.mem_support_of_mem_edges heRaw
            simpa [dualToPrimalCrossingPositiveEdge, SquarePositiveEdge.toEdge,
              squarePerp, Sym2.mem_iff] using
                (Or.inl (cubicStepFrom_neg_pos u (0 : Fin 2)).symm))
    simpa [cubicStepFrom_neg_pos] using h.symm
  · apply closedSquareWalkFaceParity_eq_of_positiveDualStep_of_crossed_not_mem c
      (⟨u, (0 : Fin 2)⟩ : DualSquarePositiveEdge)
    intro he
    apply hv
    have heRaw := (mem_walkEdgeFinset_iff c _).mp he
    apply c.mem_support_of_mem_edges heRaw
    simp [dualToPrimalCrossingPositiveEdge, SquarePositiveEdge.toEdge,
      squarePerp, Sym2.mem_iff]
  · have h := closedSquareWalkFaceParity_eq_of_positiveDualStep_of_crossed_not_mem c
        (⟨cubicStepFrom u ((1 : Fin 2), false), (1 : Fin 2)⟩ :
          DualSquarePositiveEdge) (by
            intro he
            apply hu
            have heRaw := (mem_walkEdgeFinset_iff c _).mp he
            apply c.mem_support_of_mem_edges heRaw
            simpa [dualToPrimalCrossingPositiveEdge, SquarePositiveEdge.toEdge,
              squarePerp, Sym2.mem_iff] using
                (Or.inl (cubicStepFrom_neg_pos u (1 : Fin 2)).symm))
    simpa [cubicStepFrom_neg_pos] using h.symm
  · apply closedSquareWalkFaceParity_eq_of_positiveDualStep_of_crossed_not_mem c
      (⟨u, (1 : Fin 2)⟩ : DualSquarePositiveEdge)
    intro he
    apply hv
    have heRaw := (mem_walkEdgeFinset_iff c _).mp he
    apply c.mem_support_of_mem_edges heRaw
    simp [dualToPrimalCrossingPositiveEdge, SquarePositiveEdge.toEdge,
      squarePerp, Sym2.mem_iff]

/-! ### A closed doubled outer interface -/

private def brFilledHullDoubledTopConnector
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    squareGraph.Walk
      (brPrimalTopReflectionIso n
        (brSelectedBottomPrimalVertex hn hR.filledHull))
      (cubicStepFrom
        (brPrimalTopReflectionIso n
          (brSelectedBottomPrimalVertex hn hR.filledHull))
        ((1 : Fin 2), true)) :=
  SimpleGraph.Walk.cons
    (cubicGraph_adj_stepFrom _ ((1 : Fin 2), true)) .nil

private def brFilledHullDoubledBottomConnector
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    squareGraph.Walk
      (cubicStepFrom (brSelectedBottomPrimalVertex hn hR.filledHull)
        ((1 : Fin 2), false))
      (brSelectedBottomPrimalVertex hn hR.filledHull) :=
  (SimpleGraph.Walk.cons
    (cubicGraph_adj_stepFrom _ ((1 : Fin 2), true)) .nil).copy rfl
      (cubicStepFrom_neg_pos _ (1 : Fin 2))

private def brFilledHullDoubledMiddleClosure
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    squareGraph.Walk
      (cubicStepFrom
        (brPrimalTopReflectionIso n
          (brSelectedBottomPrimalVertex hn hR.filledHull))
        ((1 : Fin 2), true))
      (cubicStepFrom (brSelectedBottomPrimalVertex hn hR.filledHull)
        ((1 : Fin 2), false)) := by
  let a := brFilledHullSelectedBottomNat hn hR
  let F := brExtensionRectangleTranslateIso n
  let middleRaw :=
    (brLeftExteriorClosureWalk (2 * n + 1) a a).map F.toHom
  have hb0 : (brSelectedBottomPrimalVertex hn hR.filledHull) 0 = (a : ℤ) :=
    (brFilledHullSelectedBottomNat_cast hn hR).symm
  have hb1 : (brSelectedBottomPrimalVertex hn hR.filledHull) 1 = -(n : ℤ) :=
    (mem_brSquareBottomSide_iff.mp
      (brSelectedBottomPrimalVertex_mem_bottomSide hn hR.filledHull)).2.2
  have htop : cubicStepFrom
      (brPrimalTopReflectionIso n
        (brSelectedBottomPrimalVertex hn hR.filledHull))
      ((1 : Fin 2), true) =
      F (squareVertex (a : ℤ) ((2 * n + 1 : ℕ) : ℤ)) := by
    ext i
    fin_cases i
    · simp [F, cubicStepFrom, cubicDirectionIncrement, hb0]
    · simp [F, cubicStepFrom, cubicDirectionIncrement, hb1]
      omega
  have hbottom : F (squareVertex (a : ℤ) (-((2 * n + 1 : ℕ) : ℤ))) =
      cubicStepFrom (brSelectedBottomPrimalVertex hn hR.filledHull)
        ((1 : Fin 2), false) := by
    ext i
    fin_cases i
    · simp [F, cubicStepFrom, cubicDirectionIncrement, hb0]
    · simp [F, cubicStepFrom, cubicDirectionIncrement, hb1]
      omega
  let middle := middleRaw.copy htop.symm hbottom
  exact middle

/-- The deterministic closure of the doubled interface runs one layer outside the extension
rectangle.  Hence its only vertices in the rectangle are the two doubled-interface endpoints. -/
private def brFilledHullDoubledOuterClosure
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    squareGraph.Walk
      (brPrimalTopReflectionIso n
        (brSelectedBottomPrimalVertex hn hR.filledHull))
      (brSelectedBottomPrimalVertex hn hR.filledHull) :=
  (brFilledHullDoubledTopConnector hn hR).append
    ((brFilledHullDoubledMiddleClosure hn hR).append
      (brFilledHullDoubledBottomConnector hn hR))

/-- The doubled filled-hull interface closed through the exterior layer. -/
private def brFilledHullDoubledClosedWalk
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    squareGraph.Walk
      (brSelectedBottomPrimalVertex hn hR.filledHull)
      (brSelectedBottomPrimalVertex hn hR.filledHull) :=
  (brDoubledSelectedPrimalWalk hn hR.filledHull).append
    (brFilledHullDoubledOuterClosure hn hR)

private theorem brFilledHullDoubledOuterClosure_support
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R)
    {z : SquareVertex}
    (hz : z ∈ (brFilledHullDoubledOuterClosure hn hR).support) :
    z = brPrimalTopReflectionIso n
        (brSelectedBottomPrimalVertex hn hR.filledHull) ∨
      z = brSelectedBottomPrimalVertex hn hR.filledHull ∨
      z 0 = -1 ∨ z 1 = 3 * (n : ℤ) + 1 ∨
        z 1 = -(n : ℤ) - 1 := by
  change z ∈ ((brFilledHullDoubledTopConnector hn hR).append
    ((brFilledHullDoubledMiddleClosure hn hR).append
      (brFilledHullDoubledBottomConnector hn hR))).support at hz
  rw [SimpleGraph.Walk.mem_support_append_iff,
    SimpleGraph.Walk.mem_support_append_iff] at hz
  rcases hz with hzTop | hzMiddle | hzBottom
  · simp [brFilledHullDoubledTopConnector] at hzTop
    rcases hzTop with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (Or.inr (Or.inl (by
        have hb := mem_brSquareBottomSide_iff.mp
          (brSelectedBottomPrimalVertex_mem_bottomSide hn hR.filledHull)
        simp [cubicStepFrom, cubicDirectionIncrement,
          brPrimalTopReflectionIso_one]
        omega))))
  · simp only [brFilledHullDoubledMiddleClosure,
      SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map,
      List.mem_map] at hzMiddle
    rcases hzMiddle with ⟨q, hq, rfl⟩
    rcases mem_brLeftExteriorClosureWalk_support hq with hq0 | hq1 | hq1
    · exact Or.inr (Or.inr (Or.inl (by simpa using hq0)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (by
        change brExtensionRectangleTranslateIso n q 1 = 3 * (n : ℤ) + 1
        rw [brExtensionRectangleTranslateIso_one]
        omega))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (by
        change brExtensionRectangleTranslateIso n q 1 = -(n : ℤ) - 1
        rw [brExtensionRectangleTranslateIso_one]
        omega))))
  · simp [brFilledHullDoubledBottomConnector] at hzBottom
    rcases hzBottom with rfl | rfl
    · exact Or.inr (Or.inr (Or.inr (Or.inr (by
        have hb := mem_brSquareBottomSide_iff.mp
          (brSelectedBottomPrimalVertex_mem_bottomSide hn hR.filledHull)
        simp [cubicStepFrom, cubicDirectionIncrement]
        omega))))
    · exact Or.inr (Or.inl
        (cubicStepFrom_neg_pos
          (brSelectedBottomPrimalVertex hn hR.filledHull) (1 : Fin 2)))

private theorem brFilledHullDoubledMiddleClosure_horizontalRayCount_eq_zero
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R)
    (f : DualSquareVertex) (hf : -1 ≤ f 0) :
    (brFilledHullDoubledMiddleClosure hn hR).edges.countP
      (squareEdgeCrossesFaceHorizontalRayBool f) = 0 := by
  let a := brFilledHullSelectedBottomNat hn hR
  let f' := squareVertex (f 0) (f 1 - (n : ℤ))
  have hraw := brLeftExteriorClosureWalk_horizontalRayCount_eq_zero
    (n := 2 * n + 1) (a := a) (b := a) f' (by simpa [f', squareVertex] using hf)
  rw [List.countP_eq_zero] at hraw ⊢
  intro e he
  simp only [brFilledHullDoubledMiddleClosure,
    SimpleGraph.Walk.edges_copy, SimpleGraph.Walk.edges_map,
    List.mem_map] at he
  rcases he with ⟨q, hq, rfl⟩
  have hqZero := hraw q hq
  induction q using Sym2.ind with
  | _ u v =>
      simp [squareEdgeCrossesFaceHorizontalRayBool,
        squareEdgeCrossesFaceHorizontalRay, f', squareVertex,
        brExtensionRectangleTranslateIso_zero,
        brExtensionRectangleTranslateIso_one] at hqZero ⊢
      intro h0 h1
      apply hqZero h0
      omega

private theorem brFilledHullDoubledOuterClosure_horizontalRayCount_eq_zero
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R)
    (f : DualSquareVertex) (hf0 : -1 ≤ f 0)
    (hside : (-(n : ℤ) ≤ f 1 ∧ f 1 < (n : ℤ)) ∨
      2 * (n : ℤ) ≤ f 0) :
    (brFilledHullDoubledOuterClosure hn hR).edges.countP
      (squareEdgeCrossesFaceHorizontalRayBool f) = 0 := by
  let top := brFilledHullDoubledTopConnector hn hR
  let middle := brFilledHullDoubledMiddleClosure hn hR
  let bottom := brFilledHullDoubledBottomConnector hn hR
  have hb := mem_brSquareBottomSide_iff.mp
    (brSelectedBottomPrimalVertex_mem_bottomSide hn hR.filledHull)
  have htop : top.edges.countP
      (squareEdgeCrossesFaceHorizontalRayBool f) = 0 := by
    simp only [top, brFilledHullDoubledTopConnector,
      SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil,
      List.countP_cons, List.countP_nil, add_zero]
    simp [squareEdgeCrossesFaceHorizontalRayBool,
      squareEdgeCrossesFaceHorizontalRay, cubicStepFrom,
      cubicDirectionIncrement, brPrimalTopReflectionIso_zero,
      brPrimalTopReflectionIso_one]
    rcases hside with hheight | hright <;> omega
  have hmiddle : middle.edges.countP
      (squareEdgeCrossesFaceHorizontalRayBool f) = 0 :=
    brFilledHullDoubledMiddleClosure_horizontalRayCount_eq_zero hn hR f hf0
  have hbottom : bottom.edges.countP
      (squareEdgeCrossesFaceHorizontalRayBool f) = 0 := by
    simp only [bottom, brFilledHullDoubledBottomConnector,
      SimpleGraph.Walk.edges_copy, SimpleGraph.Walk.edges_cons,
      SimpleGraph.Walk.edges_nil, List.countP_cons, List.countP_nil,
      add_zero]
    simp [squareEdgeCrossesFaceHorizontalRayBool,
      squareEdgeCrossesFaceHorizontalRay, cubicStepFrom,
      cubicDirectionIncrement]
    rcases hside with hheight | hright <;> omega
  simp only [brFilledHullDoubledOuterClosure,
    SimpleGraph.Walk.edges_append, List.countP_append]
  simpa [top, middle, bottom, htop, hmiddle, hbottom]

private theorem walk_horizontalRayCount_eq_zero_of_support_above
    {u v : SquareVertex} (p : squareGraph.Walk u v)
    (f : DualSquareVertex)
    (habove : ∀ z ∈ p.support, f 1 < z 1) :
    p.edges.countP (squareEdgeCrossesFaceHorizontalRayBool f) = 0 := by
  rw [List.countP_eq_zero]
  intro e he
  induction e using Sym2.ind with
  | _ x y =>
      have hx := habove x (p.fst_mem_support_of_mem_edges he)
      have hy := habove y (p.snd_mem_support_of_mem_edges he)
      simp [squareEdgeCrossesFaceHorizontalRayBool,
        squareEdgeCrossesFaceHorizontalRay]
      omega

private theorem walk_horizontalRayCount_eq_zero_of_support_left
    {u v : SquareVertex} (p : squareGraph.Walk u v)
    (f : DualSquareVertex)
    (hleft : ∀ z ∈ p.support, z 0 ≤ f 0) :
    p.edges.countP (squareEdgeCrossesFaceHorizontalRayBool f) = 0 := by
  rw [List.countP_eq_zero]
  intro e he
  induction e using Sym2.ind with
  | _ x y =>
      have hx := hleft x (p.fst_mem_support_of_mem_edges he)
      have hy := hleft y (p.snd_mem_support_of_mem_edges he)
      simp [squareEdgeCrossesFaceHorizontalRayBool,
        squareEdgeCrossesFaceHorizontalRay]
      omega

private theorem brFilledHullReflected_horizontalRayCount_eq_zero_lowerFrame
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R)
    (f : DualSquareVertex) (hf : f 1 < (n : ℤ)) :
    (brReflectedSelectedPrimalWalk hn hR.filledHull).edges.countP
      (squareEdgeCrossesFaceHorizontalRayBool f) = 0 := by
  apply walk_horizontalRayCount_eq_zero_of_support_above _ f
  intro z hz
  have hzCoords :=
    brReflectedSelectedPrimalWalk_support_coordinates hn hR.filledHull hz
  omega

private theorem brFilledHullDoubledClosedWalk_parity_eq_lowerClosedWalk
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R)
    (f : BRLeftmostDualVertex n) :
    closedSquareWalkFaceParity (brFilledHullDoubledClosedWalk hn hR) f.1 =
      closedSquareWalkFaceParity (brFilledHullSelectedClosedWalk hn hR) f.1 := by
  have hfCoords := mem_brLeftmostDualFaces_iff.mp f.2
  have hreflect :=
    brFilledHullReflected_horizontalRayCount_eq_zero_lowerFrame
      hn hR f.1 hfCoords.2.2.2
  have houter := brFilledHullDoubledOuterClosure_horizontalRayCount_eq_zero
    hn hR f.1 hfCoords.1 (Or.inl ⟨hfCoords.2.2.1, hfCoords.2.2.2⟩)
  have hold := brLeftExteriorClosureWalk_horizontalRayCount_eq_zero
    (n := n) (a := brFilledHullSelectedBottomNat hn hR)
    (b := brFilledHullSelectedTopNat hn hR) f.1 hfCoords.1
  unfold closedSquareWalkFaceParity
  simp only [brFilledHullDoubledClosedWalk,
    brDoubledSelectedPrimalWalk, brFilledHullSelectedClosedWalk,
    SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_copy,
    List.countP_append]
  rw [hreflect, houter, hold]
  simp [brFilledHullSelectedPrimalWalkNormalized,
    SimpleGraph.Walk.edges_copy]

private theorem brFilledHullDoubledClosedWalk_parity_eq_zero_of_right
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R)
    (f : DualSquareVertex) (hf : 2 * (n : ℤ) ≤ f 0) :
    closedSquareWalkFaceParity (brFilledHullDoubledClosedWalk hn hR) f = 0 := by
  have hdoubled : (brDoubledSelectedPrimalWalk hn hR.filledHull).edges.countP
      (squareEdgeCrossesFaceHorizontalRayBool f) = 0 := by
    apply walk_horizontalRayCount_eq_zero_of_support_left _ f
    intro z hz
    have hzCoords := brDoubledSelectedPrimalWalk_support_coordinates
      hn hR.filledHull hz
    omega
  have houter := brFilledHullDoubledOuterClosure_horizontalRayCount_eq_zero
    hn hR f (by omega) (Or.inr hf)
  unfold closedSquareWalkFaceParity
  simp only [brFilledHullDoubledClosedWalk, SimpleGraph.Walk.edges_append,
    List.countP_append]
  rw [hdoubled, houter]

private theorem brFilledHullDoubledClosedWalk_parity_ne_zero_of_mem
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R)
    {x : BRLeftmostDualVertex n}
    (hx : x ∈ brFilledReachableHull n R) :
    closedSquareWalkFaceParity (brFilledHullDoubledClosedWalk hn hR) x.1 ≠ 0 := by
  rcases brFilledHullSelectedClosedWalk_parity_eq_source_of_mem
      hn hR hx with ⟨a, ha, hax⟩
  let r := brRightTargetAtSameHeight n x
  have hr : r ∈ brRightmostDualTargets n :=
    brRightTargetAtSameHeight_mem_targets n x
  have hne := brFilledHullSelectedClosedWalk_parity_ne_source_target
    hn hR ha hr
  have haDouble := brFilledHullDoubledClosedWalk_parity_eq_lowerClosedWalk hn hR a
  have hxDouble := brFilledHullDoubledClosedWalk_parity_eq_lowerClosedWalk hn hR x
  have hrDouble := brFilledHullDoubledClosedWalk_parity_eq_lowerClosedWalk hn hR r
  have hrZero := brFilledHullDoubledClosedWalk_parity_eq_zero_of_right
    hn hR r.1 (by rw [mem_brRightmostDualTargets_iff] at hr; omega)
  intro hxZero
  apply hne
  calc
    closedSquareWalkFaceParity (brFilledHullSelectedClosedWalk hn hR) a.1 =
        closedSquareWalkFaceParity (brFilledHullDoubledClosedWalk hn hR) a.1 :=
      haDouble.symm
    _ = closedSquareWalkFaceParity (brFilledHullDoubledClosedWalk hn hR) x.1 :=
      (haDouble.trans hax).trans hxDouble.symm
    _ = 0 := hxZero
    _ = closedSquareWalkFaceParity (brFilledHullDoubledClosedWalk hn hR) r.1 :=
      hrZero.symm
    _ = closedSquareWalkFaceParity (brFilledHullSelectedClosedWalk hn hR) r.1 :=
      hrDouble

private theorem endpoint_coordinates_of_mem_brExtensionRectangleEdges_outer
    {m n : ℕ} {e : SquareEdge} (he : e ∈ brExtensionRectangleEdges m n)
    {x : SquareVertex} (hx : x ∈ (e : Sym2 SquareVertex)) :
    0 ≤ x 0 ∧ x 0 ≤ (m : ℤ) ∧
      -(n : ℤ) ≤ x 1 ∧ x 1 ≤ 3 * (n : ℤ) := by
  rw [brExtensionRectangleEdges, Finset.mem_map] at he
  obtain ⟨f, hf, rfl⟩ := he
  change x ∈ Sym2.map (brExtensionRectangleTranslateIso n)
    (f : Sym2 SquareVertex) at hx
  rw [Sym2.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  rw [squareBoundaryFreeRectangleEdges, Finset.mem_filter] at hf
  have hy' := mem_squareRectangleVertices_iff.mp
    (endpoint_mem_squareRectangle_of_edge_mem hf.1 hy)
  simp only [brExtensionRectangleTranslateIso_zero,
    brExtensionRectangleTranslateIso_one]
  omega

private theorem brFirstContactArm_support_coordinates
    (m : ℕ) {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hm : 2 * n ≤ m) (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R)
    {r z : SquareVertex}
    (hz : z ∈ (brDoubledSelectedPrimalWalk hn hR.filledHull).support)
    (arm : squareGraph.Walk r z)
    (harm : walkEdgeFinset arm ⊆ brExtensionRectangleEdges m n) :
    ∀ t ∈ arm.support,
      0 ≤ t 0 ∧ t 0 ≤ (m : ℤ) ∧
        -(n : ℤ) ≤ t 1 ∧ t 1 ≤ 3 * (n : ℤ) := by
  intro t ht
  rw [SimpleGraph.Walk.mem_support_iff_exists_mem_edges] at ht
  rcases ht with rfl | ⟨e, he, hte⟩
  · have hzCoords := brDoubledSelectedPrimalWalk_support_coordinates
      hn hR.filledHull hz
    omega
  · let ee : SquareEdge := ⟨e, arm.edges_subset_edgeSet he⟩
    apply endpoint_coordinates_of_mem_brExtensionRectangleEdges_outer
      (harm ((mem_walkEdgeFinset_iff arm ee).mpr he)) hte

private theorem brFirstContactArm_not_mem_doubledClosed_of_ne_contact
    (m : ℕ) {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hm : 2 * n ≤ m) (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R)
    {r z : SquareVertex}
    (hz : z ∈ (brDoubledSelectedPrimalWalk hn hR.filledHull).support)
    (arm : squareGraph.Walk r z)
    (harm : walkEdgeFinset arm ⊆ brExtensionRectangleEdges m n)
    (hfirst : ∀ t ∈ (brDoubledSelectedPrimalWalk hn hR.filledHull).support,
      t ∈ arm.support → t = z)
    {t : SquareVertex} (ht : t ∈ arm.support) (htz : t ≠ z) :
    t ∉ (brFilledHullDoubledClosedWalk hn hR).support := by
  intro htClosed
  rw [brFilledHullDoubledClosedWalk,
    SimpleGraph.Walk.mem_support_append_iff] at htClosed
  rcases htClosed with htDoubled | htClosure
  · exact htz (hfirst t htDoubled ht)
  · rcases brFilledHullDoubledOuterClosure_support hn hR htClosure with
      htTop | htBottom | htLeft | htAbove | htBelow
    · apply htz
      apply hfirst t
      · rw [htTop, brDoubledSelectedPrimalWalk_support_iff]
        exact Or.inr (by simp [brReflectedSelectedPrimalWalk])
      · exact ht
    · apply htz
      apply hfirst t
      · rw [htBottom, brDoubledSelectedPrimalWalk_support_iff]
        exact Or.inl (brSelectedPrimalWalk hn hR.filledHull).start_mem_support
      · exact ht
    · have htCoords := brFirstContactArm_support_coordinates
        m hm hn hR hz arm harm t ht
      omega
    · have htCoords := brFirstContactArm_support_coordinates
        m hm hn hR hz arm harm t ht
      omega
    · have htCoords := brFirstContactArm_support_coordinates
        m hm hn hR hz arm harm t ht
      omega

private theorem exists_filledHull_face_crossing_of_mem_fiberSupport
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    {e : SquareEdge}
    (he : e ∈ brReachableFaceFiberSupport n (brFilledReachableHull n R)) :
    ∃ x : BRLeftmostDualVertex n,
      x ∈ brFilledReachableHull n R ∧
        x.1 ∈ (squareEdgeDualCrossingEquiv e : Sym2 DualSquareVertex) := by
  rw [brReachableFaceFiberSupport, Finset.mem_filter] at he
  rcases Finset.mem_image.mp he.1 with ⟨d, _hdAttach, hde⟩
  have hdIncident : d.1 ∈ finiteGraphIncidentEdges (brLeftmostDualGraph n)
      (brFilledReachableHull n R) := d.2
  unfold finiteGraphIncidentEdges at hdIncident
  rw [Finset.mem_biUnion] at hdIncident
  rcases hdIncident with ⟨x, hxHull, hdx⟩
  rw [SimpleGraph.mem_incidenceFinset] at hdx
  refine ⟨x, hxHull, ?_⟩
  let dg : (brLeftmostDualGraph n).edgeSet :=
    ⟨d.1, (brLeftmostDualGraph n).incidenceSet_subset x hdx⟩
  have hxEdge : x ∈ d.1 := by
    exact (brLeftmostDualGraph n).edge_mem_incidenceSet_iff.mp
      (show (dg : Sym2 (BRLeftmostDualVertex n)) ∈
        (brLeftmostDualGraph n).incidenceSet x from hdx)
  have hxD : x.1 ∈ (brIncidentDualEdge n (brFilledReachableHull n R) d :
      Sym2 DualSquareVertex) := by
    change x.1 ∈ Sym2.map (brLeftmostDualToAmbientHom n) d.1
    rw [Sym2.mem_map]
    exact ⟨x, hxEdge, rfl⟩
  have hdual : brIncidentDualEdge n (brFilledReachableHull n R) d =
      squareEdgeDualCrossingEquiv e := by
    apply squareEdgeDualCrossingEquiv.symm.injective
    simpa [brIncidentCrossedPrimalEdge] using hde
  simpa [hdual] using hxD

/-- If a primal bond is incident to a vertex outside a closed walk, both shifted-dual faces
crossed by that bond have the same face parity as the coordinate face based at that vertex. -/
private theorem crossedDualFace_parity_eq_of_endpoint_not_mem_closed
    {o : SquareVertex} (c : squareGraph.Walk o o)
    {e : SquareEdge} {u f : SquareVertex}
    (huE : u ∈ (e : Sym2 SquareVertex)) (hu : u ∉ c.support)
    (hf : f ∈ (squareEdgeDualCrossingEquiv e : Sym2 DualSquareVertex)) :
    closedSquareWalkFaceParity c f = closedSquareWalkFaceParity c u := by
  let pe : SquarePositiveEdge := SquarePositiveEdge.edgeEquiv.symm e
  have hePe : pe.toEdge = e := by
    change SquarePositiveEdge.edgeEquiv pe = e
    simp [pe]
  have huPe : u ∈ (pe.toEdge : Sym2 SquareVertex) := by
    simpa [hePe] using huE
  have hpeNot : pe.toEdge ∉ walkEdgeFinset c := by
    intro he
    apply hu
    have heRaw := (mem_walkEdgeFinset_iff c pe.toEdge).mp he
    exact c.mem_support_of_mem_edges heRaw huPe
  have hsideBase : closedSquareWalkFaceParity c
      (primalToDualCrossingPositiveEdge pe).base =
      closedSquareWalkFaceParity c pe.base := by
    have h := closedSquareWalkFaceParity_eq_of_positiveDualStep_of_crossed_not_mem
      c (primalToDualCrossingPositiveEdge pe) (by
        simpa using hpeNot)
    simpa [primalToDualCrossingPositiveEdge, squarePerp,
      cubicStepFrom_neg_pos] using h
  have hbaseU : closedSquareWalkFaceParity c pe.base =
      closedSquareWalkFaceParity c u := by
    simp only [SquarePositiveEdge.toEdge, Sym2.mem_iff] at huPe
    rcases huPe with huBase | huStep
    · exact congrArg _ huBase.symm
    · let tangent : DualSquarePositiveEdge := ⟨pe.base, pe.axis⟩
      have htangentNot : (dualToPrimalCrossingPositiveEdge tangent).toEdge ∉
          walkEdgeFinset c := by
        intro he
        apply hu
        have heRaw := (mem_walkEdgeFinset_iff c _).mp he
        apply c.mem_support_of_mem_edges heRaw
        have hu' : u = cubicStepFrom pe.base (pe.axis, true) := huStep
        subst u
        simp [tangent, dualToPrimalCrossingPositiveEdge,
          SquarePositiveEdge.toEdge, Sym2.mem_iff]
      have h := closedSquareWalkFaceParity_eq_of_positiveDualStep_of_crossed_not_mem
        c tangent htangentNot
      simpa [tangent, huStep] using h
  have hdual : (squareEdgeDualCrossingEquiv e : Sym2 DualSquareVertex) =
      ((primalToDualCrossingPositiveEdge pe).toEdge : Sym2 DualSquareVertex) := by
    have hcross : squareEdgeDualCrossingEquiv pe.toEdge =
        (primalToDualCrossingPositiveEdge pe).toEdge := by
      unfold squareEdgeDualCrossingEquiv
      simp only [Equiv.trans_apply]
      have hpeInv : SquarePositiveEdge.edgeEquiv.symm pe.toEdge = pe := by
        simpa [squarePositiveEdgeEmbedding] using
          (SquarePositiveEdge.edgeEquiv_symm_squarePositiveEdgeEmbedding pe)
      rw [hpeInv]
      exact SquarePositiveEdge.edgeEquiv_apply _
    exact congrArg Subtype.val (by simpa [hePe] using hcross)
  rw [hdual] at hf
  simp only [SquarePositiveEdge.toEdge, Sym2.mem_iff] at hf
  rcases hf with rfl | rfl
  · exact hsideBase.trans hbaseU
  · simpa [primalToDualCrossingPositiveEdge,
      cubicStepFrom_neg_pos] using hbaseU

private theorem crossedDualFace_parity_eq_zero_of_mem_path_edges
    {o r z : SquareVertex} (c : squareGraph.Walk o o)
    (p : squareGraph.Walk r z) (hp : p.IsPath)
    (havoid : ∀ t ∈ p.support, t ≠ z → t ∉ c.support)
    (hr : closedSquareWalkFaceParity c r = 0)
    {e : SquareEdge} (he : (e : Sym2 SquareVertex) ∈ p.edges)
    {f : DualSquareVertex}
    (hf : f ∈ (squareEdgeDualCrossingEquiv e : Sym2 DualSquareVertex)) :
    closedSquareWalkFaceParity c f = 0 := by
  induction p with
  | nil => simp at he
  | @cons u v z huv q ih =>
      have hqPath : q.IsPath := hp.of_cons
      have huNotQ : u ∉ q.support :=
        (SimpleGraph.Walk.cons_isPath_iff huv q).mp hp |>.2
      have huz : u ≠ z := by
        intro huz
        apply huNotQ
        rw [huz]
        exact q.end_mem_support
      have huClosed : u ∉ c.support := havoid u (by simp) huz
      rw [SimpleGraph.Walk.edges_cons, List.mem_cons] at he
      rcases he with heHead | heTail
      · let eHead : SquareEdge :=
          ⟨s(u, v), squareGraph.mem_edgeSet.mpr huv⟩
        have heEq : e = eHead := Subtype.ext heHead
        subst e
        have huHead : u ∈ (eHead : Sym2 SquareVertex) := by
          simp [eHead, Sym2.mem_iff]
        exact (crossedDualFace_parity_eq_of_endpoint_not_mem_closed
          c huHead huClosed hf).trans hr
      · by_cases hvz : v = z
        · subst v
          have hqNil : q = .nil :=
            q.isPath_iff_eq_nil.mp hqPath
          subst q
          simp at heTail
        · have hvClosed : v ∉ c.support := havoid v (by simp) hvz
          have hvParity : closedSquareWalkFaceParity c v = 0 :=
            (closedSquareWalkFaceParity_eq_of_primalAdj_of_endpoints_not_mem
              c huv huClosed hvClosed).symm.trans hr
          apply ih hqPath
          · intro t ht htz
            exact havoid t (by simp [ht]) htz
          · exact hvParity
          · exact heTail

private theorem brFirstContactPath_edges_disjoint_filledHullSupport
    (m : ℕ) {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hm : 2 * n ≤ m) (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R)
    {r z : SquareVertex}
    (hr : r ∈ brExtensionRectangleRightSide m n)
    (hz : z ∈ (brDoubledSelectedPrimalWalk hn hR.filledHull).support)
    (arm : squareGraph.Walk r z)
    (hpath : arm.IsPath)
    (harm : walkEdgeFinset arm ⊆ brExtensionRectangleEdges m n)
    (hfirst : ∀ t ∈ (brDoubledSelectedPrimalWalk hn hR.filledHull).support,
      t ∈ arm.support → t = z) :
    Disjoint (walkEdgeFinset arm)
      (brReachableFaceFiberSupport n (brFilledReachableHull n R)) := by
  rw [Finset.disjoint_left]
  intro e hePath heSupport
  have heRaw : (e : Sym2 SquareVertex) ∈ arm.edges :=
    (mem_walkEdgeFinset_iff _ e).mp hePath
  rcases exists_filledHull_face_crossing_of_mem_fiberSupport heSupport with
    ⟨x, hxHull, hxCross⟩
  have hrCoords := mem_brExtensionRectangleRightSide_iff.mp hr
  have hrParity := brFilledHullDoubledClosedWalk_parity_eq_zero_of_right
    hn hR r (by omega)
  have havoidPath : ∀ t ∈ arm.support,
      t ≠ z → t ∉ (brFilledHullDoubledClosedWalk hn hR).support := by
    intro t ht htz
    apply brFirstContactArm_not_mem_doubledClosed_of_ne_contact
      m hm hn hR hz arm harm hfirst
    · exact ht
    · exact htz
  have hxZero := crossedDualFace_parity_eq_zero_of_mem_path_edges
    (brFilledHullDoubledClosedWalk hn hR)
    arm hpath
    havoidPath hrParity heRaw hxCross
  exact (brFilledHullDoubledClosedWalk_parity_ne_zero_of_mem
    hn hR hxHull) hxZero

private theorem brPrimalTopReflectionIso_mem_filledHullDoubled_support_iff
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R)
    {z : SquareVertex} :
    brPrimalTopReflectionIso n z ∈
        (brDoubledSelectedPrimalWalk hn hR.filledHull).support ↔
      z ∈ (brDoubledSelectedPrimalWalk hn hR.filledHull).support := by
  have forward : ∀ t ∈ (brDoubledSelectedPrimalWalk hn hR.filledHull).support,
      brPrimalTopReflectionIso n t ∈
        (brDoubledSelectedPrimalWalk hn hR.filledHull).support := by
    intro t ht
    rw [brDoubledSelectedPrimalWalk_support_iff] at ht ⊢
    rcases ht with htLower | htUpper
    · exact Or.inr ((brReflectedSelectedPrimalWalk_support_iff
        hn hR.filledHull).2 (by
          simpa only [brPrimalTopReflectionIso_involutive] using htLower))
    · exact Or.inl ((brReflectedSelectedPrimalWalk_support_iff
        hn hR.filledHull).1 htUpper)
  constructor
  · intro hz
    have := forward (brPrimalTopReflectionIso n z) hz
    simpa only [brPrimalTopReflectionIso_involutive] using this
  · exact forward z

theorem brFirstContactPath_edges_disjoint_symmetricFilledHullSupport
    (m : ℕ) {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hm : 2 * n ≤ m) (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R)
    {r z : SquareVertex}
    (hr : r ∈ brExtensionRectangleRightSide m n)
    (hz : z ∈ (brDoubledSelectedPrimalWalk hn hR.filledHull).support)
    (arm : squareGraph.Walk r z)
    (hpath : arm.IsPath)
    (harm : walkEdgeFinset arm ⊆ brExtensionRectangleEdges m n)
    (hfirst : ∀ t ∈ (brDoubledSelectedPrimalWalk hn hR.filledHull).support,
      t ∈ arm.support → t = z) :
    Disjoint (walkEdgeFinset arm)
      (brSymmetricReachableFaceFiberSupport n (brFilledReachableHull n R)) := by
  let F := brPrimalTopReflectionIso n
  let armR := arm.map F.toHom
  have hdisjoint := brFirstContactPath_edges_disjoint_filledHullSupport
    m hm hn hR hr hz arm hpath harm hfirst
  have hrR : F r ∈ brExtensionRectangleRightSide m n := by
    rw [mem_brExtensionRectangleRightSide_iff]
    have h := mem_brExtensionRectangleRightSide_iff.mp hr
    simp only [F, brPrimalTopReflectionIso_zero, brPrimalTopReflectionIso_one]
    omega
  have hzR : F z ∈
      (brDoubledSelectedPrimalWalk hn hR.filledHull).support :=
    (brPrimalTopReflectionIso_mem_filledHullDoubled_support_iff hn hR).2 hz
  have hpathR : armR.IsPath :=
    SimpleGraph.Walk.map_isPath_of_injective F.injective hpath
  have harmR : walkEdgeFinset armR ⊆ brExtensionRectangleEdges m n := by
    intro e he
    have heRaw : (e : Sym2 SquareVertex) ∈ armR.edges :=
      (mem_walkEdgeFinset_iff armR e).mp he
    simp only [armR, SimpleGraph.Walk.edges_map, List.mem_map] at heRaw
    rcases heRaw with ⟨q, hq, hqe⟩
    let qE : SquareEdge := ⟨q, arm.edges_subset_edgeSet hq⟩
    have hqAllowed : qE ∈ brExtensionRectangleEdges m n :=
      harm ((mem_walkEdgeFinset_iff arm qE).mpr hq)
    have hmapAllowed : F.mapEdgeSet qE ∈ brExtensionRectangleEdges m n := by
      rw [← brPrimalTopReflectionIso_image_extensionRectangleEdges m n]
      exact Finset.mem_image.mpr ⟨qE, hqAllowed, rfl⟩
    have heq : e = F.mapEdgeSet qE := by
      apply Subtype.ext
      exact hqe.symm
    simpa [heq] using hmapAllowed
  have hfirstR : ∀ t ∈
      (brDoubledSelectedPrimalWalk hn hR.filledHull).support,
      t ∈ armR.support → t = F z := by
    intro t htDoubled htArm
    simp only [armR, SimpleGraph.Walk.support_map, List.mem_map] at htArm
    rcases htArm with ⟨s, hsArm, hst⟩
    have hsDoubled : s ∈
        (brDoubledSelectedPrimalWalk hn hR.filledHull).support := by
      apply (brPrimalTopReflectionIso_mem_filledHullDoubled_support_iff hn hR).1
      simpa [← hst] using htDoubled
    have hsz := hfirst s hsDoubled hsArm
    calc
      t = F s := hst.symm
      _ = F z := congrArg F hsz
  have hdisjointR := brFirstContactPath_edges_disjoint_filledHullSupport
    m hm hn hR hrR hzR armR hpathR harmR hfirstR
  rw [Finset.disjoint_left]
  intro e heArm heSymmetric
  rw [brSymmetricReachableFaceFiberSupport, Finset.mem_union] at heSymmetric
  rcases heSymmetric with heLower | heReflected
  · exact Finset.disjoint_left.mp hdisjoint heArm heLower
  · let eR : SquareEdge := F.mapEdgeSet e
    have heRSupport : eR ∈
        brReachableFaceFiberSupport n (brFilledReachableHull n R) := by
      exact (mem_brReflectedReachableFaceFiberSupport_iff).1 heReflected
    have heRaw : (e : Sym2 SquareVertex) ∈ arm.edges :=
      (mem_walkEdgeFinset_iff arm e).mp heArm
    have heRArm : eR ∈ walkEdgeFinset armR := by
      change eR ∈ walkEdgeFinset (arm.map F.toHom)
      rw [mem_walkEdgeFinset_iff, SimpleGraph.Walk.edges_map, List.mem_map]
      exact ⟨(e : Sym2 SquareVertex), heRaw, rfl⟩
    exact Finset.disjoint_left.mp hdisjointR heRArm heRSupport

/-- The filled outer interface supplies the direct fresh cover needed by the
Bollobas--Riordan fiber estimate.  The first-contact arm is simplified to a path; every edge of
that path lies in the doubled rectangle and, by the outer-interface parity argument above, avoids
all coordinates queried by the filled hull and by its reflection. -/
theorem brExtensionRectangleCrossingEvent_subset_filledHull_fresh_union
    (m : ℕ) {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hm : 2 * n ≤ m) (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    brExtensionRectangleCrossingEvent m n ⊆
      brLowerFreshExtensionEvent m (brFilledReachableHull n R) hn hR.filledHull ∪
        brUpperFreshExtensionEvent m (brFilledReachableHull n R) hn hR.filledHull := by
  intro omega hcross
  obtain ⟨z, hzDoubled, r, hr, arm, harmOpen, harmEdges, hfirst⟩ :=
    exists_brFirstContactWalk m hm hn hR.filledHull hcross
  let path : squareGraph.Walk r z := arm.toPath
  have hpathOpen : walkIsOpen omega path :=
    walkIsOpen_toPath arm harmOpen
  have hpathEdges : walkEdgeFinset path ⊆ brExtensionRectangleEdges m n := by
    intro e he
    rw [mem_walkEdgeFinset_iff] at he
    exact harmEdges ((mem_walkEdgeFinset_iff arm e).mpr
      (arm.edges_toPath_subset he))
  have hfirstPath : ∀ t ∈
      (brDoubledSelectedPrimalWalk hn hR.filledHull).support,
      t ∈ path.support → t = z := by
    intro t htDoubled htPath
    exact hfirst t htDoubled (arm.support_toPath_subset htPath)
  have hdisjoint : Disjoint (walkEdgeFinset path)
      (brSymmetricReachableFaceFiberSupport n (brFilledReachableHull n R)) :=
    brFirstContactPath_edges_disjoint_symmetricFilledHullSupport
      m hm hn hR hr hzDoubled path arm.toPath.property hpathEdges hfirstPath
  have hpathFresh : walkEdgeFinset path ⊆
      brFreshExtensionEdges m n (brFilledReachableHull n R) := by
    intro e he
    rw [brFreshExtensionEdges, Finset.mem_sdiff]
    exact ⟨hpathEdges he, fun heQueried ↦
      Finset.disjoint_left.mp hdisjoint he heQueried⟩
  have hreverseFresh : walkEdgeFinset path.reverse ⊆
      brFreshExtensionEdges m n (brFilledReachableHull n R) := by
    intro e he
    rw [mem_walkEdgeFinset_iff, SimpleGraph.Walk.edges_reverse,
      List.mem_reverse] at he
    exact hpathFresh ((mem_walkEdgeFinset_iff path e).mpr he)
  have hzr : omega ∈ connectionEventIn 2
      (brFreshExtensionEdges m n (brFilledReachableHull n R)) z r :=
    ⟨path.reverse, walkIsOpen_reverse hpathOpen, hreverseFresh⟩
  rw [brDoubledSelectedPrimalWalk_support_iff hn hR.filledHull] at hzDoubled
  rcases hzDoubled with hzLower | hzUpper
  · exact Or.inl ⟨z, hzLower, r, hr, hzr⟩
  · right
    change cubicGraphIsoConfigurationPullback
        (brPrimalTopReflectionIso n) omega ∈
      brLowerFreshExtensionEvent m (brFilledReachableHull n R) hn hR.filledHull
    refine ⟨brPrimalTopReflectionIso n z,
      (brReflectedSelectedPrimalWalk_support_iff hn hR.filledHull).mp hzUpper,
      brPrimalTopReflectionIso n r, ?_, ?_⟩
    · rw [mem_brExtensionRectangleRightSide_iff]
      have hrCoords := mem_brExtensionRectangleRightSide_iff.mp hr
      simp only [brPrimalTopReflectionIso_zero, brPrimalTopReflectionIso_one]
      omega
    · rw [cubicGraphIsoConfigurationPullback_mem_connectionEventIn_iff,
        brPrimalTopReflectionIso_image_freshExtensionEdges,
        brPrimalTopReflectionIso_involutive,
        brPrimalTopReflectionIso_involutive]
      exact hzr

/-- On the original stopped fiber, a fresh arm to the selected outer boundary of the filled
hull gives the same three-arm source event as an arm to the unfilled selector.  Openness of the
filled-hull interface in the original fiber is the deterministic stopping property proved in
`BRFilledHull`. -/
theorem inter_fiber_brLowerFreshExtensionEvent_filledHull_subset_brSourceXEvent
    (m : ℕ) {n : ℕ} (R : Finset (BRLeftmostDualVertex n))
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    brReachableFaceFiber n R ∩
        brLowerFreshExtensionEvent m (brFilledReachableHull n R) hn hR.filledHull ⊆
      brSourceXEvent m n := by
  rintro omega ⟨homega, z, hz, r, hr, wr, hwrOpen, hwrFresh⟩
  let p := brSelectedPrimalWalk hn hR.filledHull
  have hpOpen : walkIsOpen omega p :=
    walkIsOpen_brSelectedPrimalWalk_filledHull_of_mem_fiber hn hR homega
  have hpEdges : walkEdgeFinset p ⊆ brSourceSquareEdges n := by
    simpa [p, brSourceSquareEdges] using
      walkEdgeFinset_brSelectedPrimalWalk_subset_boundaryFree hn hR.filledHull
  have htRect : brSelectedTopPrimalVertex hn hR.filledHull ∈
      squareRectangleVertices (2 * n) n := by
    have ht := mem_brSquareTopSide_iff.mp
      (brSelectedTopPrimalVertex_mem_topSide hn hR.filledHull)
    rw [mem_squareRectangleVertices_iff]
    omega
  have hzRect : z ∈ brSourceSquareVertices n := by
    exact walk_support_mem_rectangle_of_boundaryFree_edges p htRect
      (by simpa [p] using
        walkEdgeFinset_brSelectedPrimalWalk_subset_boundaryFree hn hR.filledHull) z hz
  let wb := (p.takeUntil z hz).reverse
  let wt := p.dropUntil z hz
  have hwbOpen : walkIsOpen omega wb :=
    walkIsOpen_reverse
      (walkIsOpen_of_edges_subset hpOpen (p.edges_takeUntil_subset hz))
  have hwtOpen : walkIsOpen omega wt :=
    walkIsOpen_of_edges_subset hpOpen (p.edges_dropUntil_subset hz)
  have hwbSupport : walkEdgeFinset wb ⊆ brSourceSquareEdges n :=
    (walkEdgeFinset_reverse_subset (p.takeUntil z hz)).trans
      ((walkEdgeFinset_takeUntil_subset p hz).trans hpEdges)
  have hwtSupport : walkEdgeFinset wt ⊆ brSourceSquareEdges n :=
    (walkEdgeFinset_dropUntil_subset p hz).trans hpEdges
  apply mem_brSourceXEvent_of_walks hzRect
    (brSelectedBottomPrimalVertex_mem_bottomSide hn hR.filledHull)
    (brSelectedTopPrimalVertex_mem_topSide hn hR.filledHull) hr
    wb hwbOpen hwbSupport wt hwtOpen hwtSupport wr hwrOpen
  exact hwrFresh.trans
    (brFreshExtensionEdges_subset_extensionRectangleEdges m n
      (brFilledReachableHull n R))

end

end Percolation
