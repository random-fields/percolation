import Percolation.Planar.FullVerticalCrossing
import Percolation.Planar.BRExplorationAlternative

/-!
# Full primal crossings exclude strict dual crossings

This module packages the deterministic mod-two separation step for the full bottom-to-top
crossing of `[0, 2n] x [-n, n]`.  A shifted-dual open walk across the surrounding face frame
must cross the primal walk, so the crossed primal bond would be both open and closed.
-/

namespace Percolation

open SimpleGraph
open scoped Sym2

noncomputable section

/-- A strict shifted-dual left-to-right crossing of the face frame excludes a full primal
bottom-to-top crossing of the corresponding square. -/
theorem dualWalkIsOpen_not_mem_fullVerticalCrossingEvent
    {n : ℕ} {x y : DualSquareVertex}
    (q : dualSquareGraph.Walk x y)
    (hx₀ : x 0 = -1) (hy₀ : y 0 = 2 * (n : ℤ))
    (hqSupport : ∀ z ∈ q.support, z ∈ brLeftmostDualFaces n)
    {ω : EdgeConfiguration 2} (hqOpen : dualWalkIsOpen ω q) :
    ω ∉ fullVerticalCrossingEvent n := by
  classical
  intro hvertical
  change cubicGraphIsoConfigurationPullback (fullVerticalCrossingPlacementIso n) ω ∈
    leftRightCrossingEvent 2 n (1 : Fin 2) at hvertical
  obtain ⟨u, huFace, v, hvFace, huv⟩ :=
    mem_leftRightCrossingEvent_iff.mp hvertical
  obtain ⟨w, hwOpen, hwEdges⟩ := huv
  let F := fullVerticalCrossingPlacementIso n
  let p : squareGraph.Walk (F u) (F v) := w.map F.toHom
  have hpOpen : walkIsOpen ω p := by
    exact walkIsOpen_map_cubicGraphIso F w hwOpen
  have huData := mem_cubicBoxFace.mp huFace
  have hvData := mem_cubicBoxFace.mp hvFace
  have huOther := huData.2 (0 : Fin 2) (by decide)
  have hvOther := hvData.2 (0 : Fin 2) (by decide)
  have huNonneg : 0 ≤ (F u) 0 := by
    simp only [F, fullVerticalCrossingPlacementIso_zero]
    simp only [cubicOrigin] at huOther
    omega
  have hvNonneg : 0 ≤ (F v) 0 := by
    simp only [F, fullVerticalCrossingPlacementIso_zero]
    simp only [cubicOrigin] at hvOther
    omega
  let a := ((F u) 0).toNat
  let b := ((F v) 0).toNat
  have haCast : (a : ℤ) = (F u) 0 := by
    simp [a, Int.toNat_of_nonneg huNonneg]
  have hbCast : (b : ℤ) = (F v) 0 := by
    simp [b, Int.toNat_of_nonneg hvNonneg]
  have huMapOne : (F u) 1 = u 1 := by
    change (fullVerticalCrossingPlacementIso n u) 1 = u 1
    exact fullVerticalCrossingPlacementIso_one n u
  have hvMapOne : (F v) 1 = v 1 := by
    change (fullVerticalCrossingPlacementIso n v) 1 = v 1
    exact fullVerticalCrossingPlacementIso_one n v
  have huOne : u 1 = -(n : ℤ) := by
    simpa [cubicOrigin] using huData.1
  have hvOne : v 1 = (n : ℤ) := by
    simpa [cubicOrigin] using hvData.1
  have huEq : F u = squareVertex (a : ℤ) (-(n : ℤ)) := by
    calc
      F u = squareVertex ((F u) 0) ((F u) 1) := (squareVertex_eta (F u)).symm
      _ = squareVertex (a : ℤ) (-(n : ℤ)) := by
        rw [← haCast, huMapOne, huOne]
  have hvEq : F v = squareVertex (b : ℤ) (n : ℤ) := by
    calc
      F v = squareVertex ((F v) 0) ((F v) 1) := (squareVertex_eta (F v)).symm
      _ = squareVertex (b : ℤ) (n : ℤ) := by
        rw [← hbCast, hvMapOne, hvOne]
  let p' : squareGraph.Walk (squareVertex (a : ℤ) (-(n : ℤ)))
      (squareVertex (b : ℤ) (n : ℤ)) := p.copy huEq hvEq
  have huBox : u ∈ cubicMetricBox 2 cubicOrigin n := by
    apply mem_cubicMetricBox_iff_lInfDist_le.mpr
    exact (mem_cubicBoxSurface.mp
      (cubicBoxFace_subset_surface cubicOrigin (1 : Fin 2) false huFace)).le
  have hwBox := walk_support_subset_cubicMetricBox_of_edges huBox w hwEdges
  have hpBox : ∀ z ∈ p'.support,
      0 ≤ z 0 ∧ z 0 ≤ 2 * (n : ℤ) ∧
        -(n : ℤ) ≤ z 1 ∧ z 1 ≤ (n : ℤ) := by
    intro z hz
    have hzP : z ∈ p.support := by
      simpa [p', SimpleGraph.Walk.support_copy] using hz
    simp only [p, SimpleGraph.Walk.support_map, List.mem_map] at hzP
    obtain ⟨z₀, hz₀, rfl⟩ := hzP
    have hzBox := mem_cubicMetricBox.mp (hwBox z₀ hz₀)
    have hzZero := hzBox (0 : Fin 2)
    have hzOne := hzBox (1 : Fin 2)
    have hzMapZero : (F.toHom z₀) 0 = z₀ 0 + n := by
      change (fullVerticalCrossingPlacementIso n z₀) 0 = z₀ 0 + n
      exact fullVerticalCrossingPlacementIso_zero n z₀
    have hzMapOne : (F.toHom z₀) 1 = z₀ 1 := by
      change (fullVerticalCrossingPlacementIso n z₀) 1 = z₀ 1
      exact fullVerticalCrossingPlacementIso_one n z₀
    rw [hzMapZero, hzMapOne]
    simp only [cubicOrigin] at hzZero hzOne
    omega
  have hpOpen' : walkIsOpen ω p' := by
    simpa [p'] using (walkIsOpen_copy p huEq hvEq).mpr hpOpen
  have hxFrame := mem_brLeftmostDualFaces_iff.mp
    (hqSupport x q.start_mem_support)
  let c := p'.append (brLeftExteriorClosureWalk n a b)
  have hparity : closedSquareWalkFaceParity c x ≠
      closedSquareWalkFaceParity c y := by
    exact brClosedBottomTopWalk_faceParity_ne p' hpBox hx₀ hxFrame.2.2.1
      hxFrame.2.2.2 hy₀
  obtain ⟨ed, hedq, hedc⟩ :=
    exists_dualWalk_edge_crossing_closedWalk_of_faceParity_ne c q hparity
  have hedRaw : (ed : Sym2 DualSquareVertex) ∈ q.edges :=
    (mem_walkEdgeFinset_iff q ed).mp hedq
  have hedEndpoints : ∀ z ∈ (ed : Sym2 DualSquareVertex),
      z ∈ brLeftmostDualFaces n := by
    intro z hz
    exact hqSupport z (q.mem_support_of_mem_edges hedRaw hz)
  have hedNotClosure : squareEdgeDualCrossingEquiv.symm ed ∉
      walkEdgeFinset (brLeftExteriorClosureWalk n a b) :=
    squareEdgeDualCrossingEquiv_symm_not_mem_brLeftExteriorClosureWalk
      ed hedEndpoints
  have hedPrimal : squareEdgeDualCrossingEquiv.symm ed ∈ walkEdgeFinset p' := by
    have hedc' : squareEdgeDualCrossingEquiv.symm ed ∈
        walkEdgeFinset (p'.append (brLeftExteriorClosureWalk n a b)) := by
      simpa only [c] using hedc
    rw [mem_walkEdgeFinset_iff, SimpleGraph.Walk.edges_append,
      List.mem_append] at hedc'
    rcases hedc' with hp | hclosure
    · exact (mem_walkEdgeFinset_iff p' _).mpr hp
    · exact (hedNotClosure ((mem_walkEdgeFinset_iff _ _).mpr hclosure)).elim
  have hedOpen : squareEdgeDualCrossingEquiv.symm ed ∈ ω := by
    have hraw := (mem_walkEdgeFinset_iff p' _).mp hedPrimal
    have hopen := hpOpen' _ hraw
    simpa only [Subtype.ext_iff] using hopen
  have hedClosed : squareEdgeDualCrossingEquiv.symm ed ∉ ω := by
    apply (dualSquareConfiguration_open_iff ω ed).mp
    have hopen := hqOpen _ hedRaw
    simpa only [Subtype.ext_iff] using hopen
  exact hedClosed hedOpen

end

end Percolation
