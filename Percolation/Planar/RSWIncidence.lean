import Percolation.Planar.RectangleIntersection
import Percolation.Planar.RSWPlacements

/-!
# Deterministic RSW incidence

The RSW placement events carry explicit finite crossing walks.  This file proves that the
crossings in Figures 11.25 and 11.26 glue by reducing both overlap claims to the discrete
left-right/bottom-top intersection theorem.  No planar-topology axiom is used.
-/

namespace Percolation

/-- A boundary-free crossing event supplies an ordinary open rectangle crossing witness. -/
theorem exists_openSquareRectangleCrossing_of_mem_boundaryFree
    {m n : ℕ} {omega : EdgeConfiguration 2}
    (h : omega ∈ squareBoundaryFreeRectangleCrossingEvent m n) :
    ∃ C : OpenSquareRectangleCrossing m n omega,
      walkEdgeFinset C.walk ⊆ squareBoundaryFreeRectangleEdges m n := by
  simp only [squareBoundaryFreeRectangleCrossingEvent, Set.mem_iUnion] at h
  rcases h with ⟨x, hx, y, hy, w, hwOpen, hwEdges⟩
  let C : OpenSquareRectangleCrossing m n omega := {
    start := x
    finish := y
    walk := w
    start_mem := hx
    finish_mem := hy
    isOpen := hwOpen
    edges_subset := fun e he ↦ (Finset.mem_filter.mp (hwEdges he)).1 }
  exact ⟨C, by simpa [C] using hwEdges⟩

/-- Every vertex of an explicit rectangle-crossing witness lies in its rectangle. -/
theorem OpenSquareRectangleCrossing.support_mem_rectangle
    {m n : ℕ} {omega : EdgeConfiguration 2}
    (C : OpenSquareRectangleCrossing m n omega) {z : SquareVertex}
    (hz : z ∈ C.walk.support) : z ∈ squareRectangleVertices m n := by
  rw [SimpleGraph.Walk.mem_support_iff_exists_mem_edges] at hz
  rcases hz with rfl | ⟨e, he, hze⟩
  · exact (Finset.mem_filter.mp C.finish_mem).1
  · let ee : SquareEdge := ⟨e, C.walk.edges_subset_edgeSet he⟩
    exact endpoint_mem_squareRectangle_of_edge_mem
      (C.edges_subset ((mem_walkEdgeFinset_iff C.walk ee).mpr he)) hze

/-- Boundary-freeness transports through a graph embedding whenever target-boundary vertices
pull back to source-boundary vertices. -/
private theorem mappedCrossing_edge_not_both_boundary
    {ms ns mt nt : ℕ} {omega : EdgeConfiguration 2}
    (C : OpenSquareRectangleCrossing ms ns omega)
    (hfree : walkEdgeFinset C.walk ⊆ squareBoundaryFreeRectangleEdges ms ns)
    (F : squareGraph ≃g squareGraph)
    (hboundary : ∀ x, x ∈ squareRectangleVertices ms ns →
      squareRectangleBoundaryVertex mt nt (F x) →
      squareRectangleBoundaryVertex ms ns x)
    {e : Sym2 SquareVertex} (he : e ∈ (C.walk.map F.toHom).edges) :
    ¬ (squareRectangleBoundaryVertex mt nt e.out.1 ∧
      squareRectangleBoundaryVertex mt nt e.out.2) := by
  rw [SimpleGraph.Walk.edges_map] at he
  rcases List.mem_map.mp he with ⟨f, hf, rfl⟩
  induction f using Sym2.ind with
  | _ u v =>
      intro hb
      let mapped : Sym2 SquareVertex := Sym2.map F s(u, v)
      have hbmem : ∀ x ∈ mapped, squareRectangleBoundaryVertex mt nt x := by
        intro x hx
        rw [← mapped.out_eq, Sym2.mem_iff] at hx
        rcases hx with rfl | rfl
        · exact hb.1
        · exact hb.2
      let ee : SquareEdge := ⟨s(u, v), C.walk.edges_subset_edgeSet hf⟩
      have hee : ee ∈ walkEdgeFinset C.walk := (mem_walkEdgeFinset_iff C.walk ee).mpr hf
      have huRect : u ∈ squareRectangleVertices ms ns :=
        endpoint_mem_squareRectangle_of_edge_mem (C.edges_subset hee) (by simp [ee])
      have hvRect : v ∈ squareRectangleVertices ms ns :=
        endpoint_mem_squareRectangle_of_edge_mem (C.edges_subset hee) (by simp [ee])
      have hnot := (Finset.mem_filter.mp (hfree hee)).2
      apply hnot
      have hsource : ∀ x ∈ s(u, v), squareRectangleBoundaryVertex ms ns x := by
        intro x hx
        exact (Sym2.mem_iff.mp hx).elim
          (fun hxu ↦ hxu ▸ hboundary u huRect (hbmem (F u) (by simp [mapped])))
          (fun hxv ↦ hxv ▸ hboundary v hvRect (hbmem (F v) (by simp [mapped])))
      exact ⟨hsource ee.1.out.1 (by exact Sym2.out_fst_mem ee.1),
        hsource ee.1.out.2 (by exact Sym2.out_snd_mem ee.1)⟩

/-- Shift the vertical coordinate of the RSW rectangles from `[-l,l]` to `[0,2l]`. -/
def rswNormalizeIso (l : ℕ) : squareGraph ≃g squareGraph :=
  cubicTranslationIso (squareVertex 0 (-(l : ℤ))) cubicOrigin

@[simp]
theorem rswNormalizeIso_zero (l : ℕ) (x : SquareVertex) :
    rswNormalizeIso l x 0 = x 0 := by
  simp [rswNormalizeIso, cubicTranslationIso_apply, cubicTranslate, squareVertex, cubicOrigin]

@[simp]
theorem rswNormalizeIso_one (l : ℕ) (x : SquareVertex) :
    rswNormalizeIso l x 1 = x 1 + l := by
  simp [rswNormalizeIso, cubicTranslationIso_apply, cubicTranslate, squareVertex, cubicOrigin]

/-- Normalize the translate of the right crossing in Figure 11.25. -/
def rswRightNormalizeIso (l : ℕ) : squareGraph ≃g squareGraph :=
  (squareCrossingTranslateIso cubicOrigin (squareVertex (l : ℕ) 0)).trans
    (rswNormalizeIso l)

@[simp]
theorem rswRightNormalizeIso_zero (l : ℕ) (x : SquareVertex) :
    rswRightNormalizeIso l x 0 = x 0 + l := by
  simp [rswRightNormalizeIso, squareCrossingTranslateIso, cubicTranslationIso_apply,
    cubicTranslate, squareVertex, cubicOrigin]

@[simp]
theorem rswRightNormalizeIso_one (l : ℕ) (x : SquareVertex) :
    rswRightNormalizeIso l x 1 = x 1 + l := by
  simp [rswRightNormalizeIso, squareCrossingTranslateIso, cubicTranslationIso_apply,
    cubicTranslate, squareVertex, cubicOrigin]

/-- Normalize the quarter-turned vertical square crossing in Figure 11.25. -/
def rswVerticalNormalizeIso (l : ℕ) : squareGraph ≃g squareGraph :=
  (squareCrossingQuarterTurnIso (rswRectangleCenter 1 l)
      (squareVertex (2 * l : ℕ) 0)).trans (rswNormalizeIso l)

@[simp]
theorem rswVerticalNormalizeIso_zero (l : ℕ) (x : SquareVertex) :
    rswVerticalNormalizeIso l x 0 = x 1 + 2 * l := by
  simp [rswVerticalNormalizeIso, squareCrossingQuarterTurnIso, rswRectangleCenter,
    squareCoordinateSwap, cubicTranslationIso_apply, cubicTranslate,
    cubicCoordinatePermutationIso, cubicCoordinatePermutationEquiv, squareVertex, cubicOrigin]

@[simp]
theorem rswVerticalNormalizeIso_one (l : ℕ) (x : SquareVertex) :
    rswVerticalNormalizeIso l x 1 = x 0 := by
  simp [rswVerticalNormalizeIso, squareCrossingQuarterTurnIso, rswRectangleCenter,
    squareCoordinateSwap, cubicTranslationIso_apply, cubicTranslate,
    cubicCoordinatePermutationIso, cubicCoordinatePermutationEquiv, squareVertex, cubicOrigin]

/-- Common frame for the right horizontal crossing and the vertical crossing. -/
def rswRightFrameIso (l : ℕ) : squareGraph ≃g squareGraph :=
  cubicTranslationIso (squareVertex (l : ℕ) (-(l : ℤ))) cubicOrigin

@[simp]
theorem rswRightFrameIso_zero (l : ℕ) (x : SquareVertex) :
    rswRightFrameIso l x 0 = x 0 - l := by
  simp [rswRightFrameIso, cubicTranslationIso_apply, cubicTranslate, squareVertex, cubicOrigin]
  ring

@[simp]
theorem rswRightFrameIso_one (l : ℕ) (x : SquareVertex) :
    rswRightFrameIso l x 1 = x 1 + l := by
  simp [rswRightFrameIso, cubicTranslationIso_apply, cubicTranslate, squareVertex, cubicOrigin]

/-- The vertical crossing normalized in the right crossing's frame. -/
def rswVerticalRightNormalizeIso (l : ℕ) : squareGraph ≃g squareGraph :=
  (squareCrossingQuarterTurnIso (rswRectangleCenter 1 l)
      (squareVertex (2 * l : ℕ) 0)).trans (rswRightFrameIso l)

@[simp]
theorem rswVerticalRightNormalizeIso_zero (l : ℕ) (x : SquareVertex) :
    rswVerticalRightNormalizeIso l x 0 = x 1 + l := by
  simp [rswVerticalRightNormalizeIso, rswRightFrameIso,
    squareCrossingQuarterTurnIso, rswRectangleCenter, squareCoordinateSwap,
    cubicTranslationIso_apply, cubicTranslate, cubicCoordinatePermutationIso,
    cubicCoordinatePermutationEquiv, squareVertex, cubicOrigin]
  ring

@[simp]
theorem rswVerticalRightNormalizeIso_one (l : ℕ) (x : SquareVertex) :
    rswVerticalRightNormalizeIso l x 1 = x 0 := by
  simp [rswVerticalRightNormalizeIso, rswRightFrameIso,
    squareCrossingQuarterTurnIso, rswRectangleCenter, squareCoordinateSwap,
    cubicTranslationIso_apply, cubicTranslate, cubicCoordinatePermutationIso,
    cubicCoordinatePermutationEquiv, squareVertex, cubicOrigin]

private theorem normalized_left_meets_vertical
    (l : ℕ) {omega : EdgeConfiguration 2}
    (L : OpenSquareRectangleCrossing (3 * l) l omega)
    (V : OpenSquareRectangleCrossing (2 * l) l
      (cubicGraphIsoConfigurationPullback
        (squareCrossingQuarterTurnIso (rswRectangleCenter 1 l)
          (squareVertex (2 * l : ℕ) 0)) omega)) :
    ∃ z, z ∈ L.walk.support ∧
      z ∈ (V.walk.map
        (squareCrossingQuarterTurnIso (rswRectangleCenter 1 l)
          (squareVertex (2 * l : ℕ) 0)).toHom).support := by
  let F := rswNormalizeIso l
  let P : squareGraph.Walk (squareVertex 0 (L.start 1 + l))
      (squareVertex (3 * l : ℕ) (L.finish 1 + l)) :=
    (L.walk.map F.toHom).copy (by
      ext i
      fin_cases i
      · simp [F]
        simpa using (mem_squareRectangleLeft_iff.mp L.start_mem).1
      · simp [F, squareVertex]) (by
      ext i
      fin_cases i
      · simp [F, squareVertex]
        simpa using (mem_squareRectangleRight_iff.mp L.finish_mem).1
      · simp [F, squareVertex])
  let Qraw := V.walk.map
    (squareCrossingQuarterTurnIso (rswRectangleCenter 1 l)
      (squareVertex (2 * l : ℕ) 0)).toHom
  let Q : squareGraph.Walk (squareVertex (V.start 1 + 2 * l) 0)
      (squareVertex (V.finish 1 + 2 * l) (2 * l : ℕ)) :=
    (V.walk.map (rswVerticalNormalizeIso l).toHom).copy (by
      ext i
      fin_cases i
      · simp [squareVertex]
      · simp [squareVertex]
        simpa using (mem_squareRectangleLeft_iff.mp V.start_mem).1) (by
      ext i
      fin_cases i
      · simp [squareVertex]
      · simp [squareVertex]
        simpa using (mem_squareRectangleRight_iff.mp V.finish_mem).1)
  have hpbox : ∀ z ∈ P.support,
      0 ≤ z 0 ∧ z 0 ≤ 3 * l ∧ 0 ≤ z 1 ∧ z 1 ≤ 2 * l := by
    intro z hz
    simp only [P, SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map,
      List.mem_map] at hz
    rcases hz with ⟨x, hx, rfl⟩
    have h := mem_squareRectangleVertices_iff.mp (L.support_mem_rectangle hx)
    simp [F]
    omega
  have hqbox : ∀ z ∈ Q.support,
      0 ≤ z 0 ∧ z 0 ≤ 3 * l ∧ 0 ≤ z 1 ∧ z 1 ≤ 2 * l := by
    intro z hz
    simp only [Q, SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map,
      List.mem_map] at hz
    rcases hz with ⟨x, hx, rfl⟩
    have h := mem_squareRectangleVertices_iff.mp (V.support_mem_rectangle hx)
    simp
    omega
  obtain ⟨z, hzP, hzQ⟩ :=
    squareWalk_support_inter_of_left_right_and_bottom_top_of_le_int
      (by omega : 2 * l ≤ 3 * l)
      (by have := (mem_squareRectangleLeft_iff.mp L.start_mem).2.1; omega)
      (by have := (mem_squareRectangleLeft_iff.mp L.start_mem).2.2; omega)
      (by have := (mem_squareRectangleRight_iff.mp L.finish_mem).2.1; omega)
      (by have := (mem_squareRectangleRight_iff.mp L.finish_mem).2.2; omega)
      (by have := (mem_squareRectangleLeft_iff.mp V.start_mem).2.1; omega)
      (by have := (mem_squareRectangleLeft_iff.mp V.start_mem).2.2; omega)
      (by have := (mem_squareRectangleRight_iff.mp V.finish_mem).2.1; omega)
      (by have := (mem_squareRectangleRight_iff.mp V.finish_mem).2.2; omega)
      P Q hpbox hqbox
  have hinter : ∃ z, z ∈ (L.walk.map F.toHom).support ∧
      z ∈ (Qraw.map F.toHom).support := by
    refine ⟨z, ?_, ?_⟩
    · simpa [P] using hzP
    · simpa [Q, Qraw, F, rswVerticalNormalizeIso, SimpleGraph.Walk.map_map] using hzQ
  exact walk_support_inter_of_map_support_inter F.toHom F.injective L.walk Qraw hinter

private theorem normalized_right_meets_vertical
    (l : ℕ) {omega : EdgeConfiguration 2}
    (R : OpenSquareRectangleCrossing (3 * l) l
      (cubicGraphIsoConfigurationPullback
        (squareCrossingTranslateIso cubicOrigin (squareVertex (l : ℕ) 0)) omega))
    (V : OpenSquareRectangleCrossing (2 * l) l
      (cubicGraphIsoConfigurationPullback
        (squareCrossingQuarterTurnIso (rswRectangleCenter 1 l)
          (squareVertex (2 * l : ℕ) 0)) omega)) :
    ∃ z,
      z ∈ (R.walk.map
        (squareCrossingTranslateIso cubicOrigin (squareVertex (l : ℕ) 0)).toHom).support ∧
      z ∈ (V.walk.map
        (squareCrossingQuarterTurnIso (rswRectangleCenter 1 l)
          (squareVertex (2 * l : ℕ) 0)).toHom).support := by
  let F := rswRightFrameIso l
  let Rraw := R.walk.map
    (squareCrossingTranslateIso cubicOrigin (squareVertex (l : ℕ) 0)).toHom
  let Vraw := V.walk.map
    (squareCrossingQuarterTurnIso (rswRectangleCenter 1 l)
      (squareVertex (2 * l : ℕ) 0)).toHom
  let P : squareGraph.Walk (squareVertex 0 (R.start 1 + l))
      (squareVertex (3 * l : ℕ) (R.finish 1 + l)) :=
    (R.walk.map (rswNormalizeIso l).toHom).copy (by
      ext i
      fin_cases i
      · simpa using (mem_squareRectangleLeft_iff.mp R.start_mem).1
      · simp [squareVertex]) (by
      ext i
      fin_cases i
      · simpa using (mem_squareRectangleRight_iff.mp R.finish_mem).1
      · simp [squareVertex])
  let Q : squareGraph.Walk (squareVertex (V.start 1 + l) 0)
      (squareVertex (V.finish 1 + l) (2 * l : ℕ)) :=
    (V.walk.map (rswVerticalRightNormalizeIso l).toHom).copy (by
      ext i
      fin_cases i
      · simp [squareVertex]
      · simp [squareVertex]
        simpa using (mem_squareRectangleLeft_iff.mp V.start_mem).1) (by
      ext i
      fin_cases i
      · simp [squareVertex]
      · simp [squareVertex]
        simpa using (mem_squareRectangleRight_iff.mp V.finish_mem).1)
  have hpbox : ∀ z ∈ P.support,
      0 ≤ z 0 ∧ z 0 ≤ 3 * l ∧ 0 ≤ z 1 ∧ z 1 ≤ 2 * l := by
    intro z hz
    simp only [P, SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map,
      List.mem_map] at hz
    rcases hz with ⟨x, hx, rfl⟩
    have h := mem_squareRectangleVertices_iff.mp (R.support_mem_rectangle hx)
    simp
    omega
  have hqbox : ∀ z ∈ Q.support,
      0 ≤ z 0 ∧ z 0 ≤ 3 * l ∧ 0 ≤ z 1 ∧ z 1 ≤ 2 * l := by
    intro z hz
    simp only [Q, SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map,
      List.mem_map] at hz
    rcases hz with ⟨x, hx, rfl⟩
    have h := mem_squareRectangleVertices_iff.mp (V.support_mem_rectangle hx)
    simp
    omega
  obtain ⟨z, hzP, hzQ⟩ :=
    squareWalk_support_inter_of_left_right_and_bottom_top_of_le_int
      (by omega : 2 * l ≤ 3 * l)
      (by have := (mem_squareRectangleLeft_iff.mp R.start_mem).2.1; omega)
      (by have := (mem_squareRectangleLeft_iff.mp R.start_mem).2.2; omega)
      (by have := (mem_squareRectangleRight_iff.mp R.finish_mem).2.1; omega)
      (by have := (mem_squareRectangleRight_iff.mp R.finish_mem).2.2; omega)
      (by have := (mem_squareRectangleLeft_iff.mp V.start_mem).2.1; omega)
      (by have := (mem_squareRectangleLeft_iff.mp V.start_mem).2.2; omega)
      (by have := (mem_squareRectangleRight_iff.mp V.finish_mem).2.1; omega)
      (by have := (mem_squareRectangleRight_iff.mp V.finish_mem).2.2; omega)
      P Q hpbox hqbox
  have hinter : ∃ z, z ∈ (Rraw.map F.toHom).support ∧
      z ∈ (Vraw.map F.toHom).support := by
    refine ⟨z, ?_, ?_⟩
    · simp only [P, SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map,
        List.mem_map] at hzP
      rcases hzP with ⟨x, hx, hxz⟩
      simp only [Rraw, SimpleGraph.Walk.support_map, List.mem_map]
      refine ⟨squareCrossingTranslateIso cubicOrigin (squareVertex (l : ℕ) 0) x, ?_, ?_⟩
      · exact ⟨x, hx, rfl⟩
      · rw [← hxz]
        ext i
        fin_cases i
        · simp [F, rswRightFrameIso, squareCrossingTranslateIso,
            cubicTranslationIso_apply, cubicTranslate, squareVertex, cubicOrigin]
        · simp [F, rswRightFrameIso, squareCrossingTranslateIso,
            cubicTranslationIso_apply, cubicTranslate, squareVertex, cubicOrigin]
    · simpa [Q, Vraw, F, rswVerticalRightNormalizeIso,
        SimpleGraph.Walk.map_map] using hzQ
  exact walk_support_inter_of_map_support_inter F.toHom F.injective Rraw Vraw hinter

/-- The crossings in Figure 11.25 glue to a crossing of the enclosing rectangle. -/
theorem rswGluingTwoIntersection_subset (l : ℕ) (_hl : 1 ≤ l) :
    rswGluingTwoIntersection l ⊆ rswRectangleCrossingEvent 2 l := by
  intro omega h
  rcases h with ⟨⟨hL, hR⟩, hV⟩
  let FRight := squareCrossingTranslateIso cubicOrigin (squareVertex (l : ℕ) 0)
  let FVert := squareCrossingQuarterTurnIso (rswRectangleCenter 1 l)
    (squareVertex (2 * l : ℕ) 0)
  change omega ∈ squareBoundaryFreeRectangleCrossingEvent (3 * l) l at hL
  change cubicGraphIsoConfigurationPullback FRight omega ∈
    squareBoundaryFreeRectangleCrossingEvent (3 * l) l at hR
  change cubicGraphIsoConfigurationPullback FVert omega ∈
    squareBoundaryFreeRectangleCrossingEvent (2 * l) l at hV
  obtain ⟨L, hLEdges⟩ := exists_openSquareRectangleCrossing_of_mem_boundaryFree hL
  obtain ⟨R0, hR0Edges⟩ := exists_openSquareRectangleCrossing_of_mem_boundaryFree hR
  obtain ⟨V0, hV0Edges⟩ := exists_openSquareRectangleCrossing_of_mem_boundaryFree hV
  let Rwalk := R0.walk.map FRight.toHom
  let Vwalk := V0.walk.map FVert.toHom
  obtain ⟨zL, hzLL, hzLV⟩ := normalized_left_meets_vertical l L V0
  have hRV : ∃ z, z ∈ Rwalk.support ∧ z ∈ Vwalk.support := by
    simpa [Rwalk, Vwalk, FRight, FVert] using normalized_right_meets_vertical l R0 V0
  obtain ⟨zR, hzRR, hzRV⟩ := hRV
  have hRopen : walkIsOpen omega Rwalk := by
    exact walkIsOpen_map_cubicGraphIso FRight R0.walk R0.isOpen
  have hVopen : walkIsOpen omega Vwalk := by
    exact walkIsOpen_map_cubicGraphIso FVert V0.walk V0.isOpen
  let pL := L.walk.takeUntil zL hzLL
  let vL := Vwalk.takeUntil zL hzLV
  let vR := Vwalk.takeUntil zR hzRV
  let pR := Rwalk.dropUntil zR hzRR
  let W := pL.append (vL.reverse.append (vR.append pR))
  have hpLOpen : walkIsOpen omega pL :=
    walkIsOpen_of_edges_subset L.isOpen (L.walk.edges_takeUntil_subset hzLL)
  have hvLOpen : walkIsOpen omega vL :=
    walkIsOpen_of_edges_subset hVopen (Vwalk.edges_takeUntil_subset hzLV)
  have hvROpen : walkIsOpen omega vR :=
    walkIsOpen_of_edges_subset hVopen (Vwalk.edges_takeUntil_subset hzRV)
  have hpROpen : walkIsOpen omega pR :=
    walkIsOpen_of_edges_subset hRopen (Rwalk.edges_dropUntil_subset hzRR)
  have hWOpen : walkIsOpen omega W := by
    exact walkIsOpen_append hpLOpen
      (walkIsOpen_append (walkIsOpen_reverse hvLOpen)
        (walkIsOpen_append hvROpen hpROpen))
  have hLsupport : ∀ z ∈ L.walk.support, z ∈ squareRectangleVertices (4 * l) l := by
    intro z hz
    have h := mem_squareRectangleVertices_iff.mp (L.support_mem_rectangle hz)
    rw [mem_squareRectangleVertices_iff]
    omega
  have hRsupport : ∀ z ∈ Rwalk.support, z ∈ squareRectangleVertices (4 * l) l := by
    intro z hz
    simp only [Rwalk, SimpleGraph.Walk.support_map, List.mem_map] at hz
    rcases hz with ⟨x, hx, rfl⟩
    have h := mem_squareRectangleVertices_iff.mp (R0.support_mem_rectangle hx)
    rw [mem_squareRectangleVertices_iff]
    simp [FRight, squareCrossingTranslateIso, cubicTranslationIso_apply,
      cubicTranslate, squareVertex, cubicOrigin]
    omega
  have hVsupport : ∀ z ∈ Vwalk.support, z ∈ squareRectangleVertices (4 * l) l := by
    intro z hz
    simp only [Vwalk, SimpleGraph.Walk.support_map, List.mem_map] at hz
    rcases hz with ⟨x, hx, rfl⟩
    have h := mem_squareRectangleVertices_iff.mp (V0.support_mem_rectangle hx)
    rw [mem_squareRectangleVertices_iff]
    simp [FVert, squareCrossingQuarterTurnIso, rswRectangleCenter,
      squareCoordinateSwap, cubicTranslationIso_apply, cubicTranslate,
      cubicCoordinatePermutationIso, cubicCoordinatePermutationEquiv,
      squareVertex, cubicOrigin]
    omega
  have hWsupport : ∀ z ∈ W.support, z ∈ squareRectangleVertices (4 * l) l := by
    intro z hz
    simp only [W, SimpleGraph.Walk.mem_support_append_iff,
      SimpleGraph.Walk.support_reverse] at hz
    rcases hz with hz | hz | hz | hz
    · exact hLsupport z (L.walk.support_takeUntil_subset_support hzLL hz)
    · have hz' : z ∈ vL.support := by simpa using hz
      exact hVsupport z (Vwalk.support_takeUntil_subset_support hzLV hz')
    · exact hVsupport z (Vwalk.support_takeUntil_subset_support hzRV hz)
    · exact hRsupport z (Rwalk.support_dropUntil_subset hzRR hz)
  have hLboundary : ∀ e ∈ L.walk.edges,
      ¬ (squareRectangleBoundaryVertex (4 * l) l e.out.1 ∧
        squareRectangleBoundaryVertex (4 * l) l e.out.2) := by
    intro e he hb
    let ee : SquareEdge := ⟨e, L.walk.edges_subset_edgeSet he⟩
    have hee : ee ∈ walkEdgeFinset L.walk := (mem_walkEdgeFinset_iff L.walk ee).mpr he
    have hnot := (Finset.mem_filter.mp (hLEdges hee)).2
    apply hnot
    have hmem : ∀ x ∈ e, x ∈ squareRectangleVertices (3 * l) l := by
      intro x hx
      exact L.support_mem_rectangle (L.walk.mem_support_of_mem_edges he hx)
    have pull (x : SquareVertex) (hx : x ∈ e)
        (hb : squareRectangleBoundaryVertex (4 * l) l x) :
        squareRectangleBoundaryVertex (3 * l) l x := by
      have hr := mem_squareRectangleVertices_iff.mp (hmem x hx)
      unfold squareRectangleBoundaryVertex at hb ⊢
      omega
    exact ⟨pull ee.1.out.1 (Sym2.out_fst_mem ee.1) hb.1,
      pull ee.1.out.2 (Sym2.out_snd_mem ee.1) hb.2⟩
  have hRboundary : ∀ e ∈ Rwalk.edges,
      ¬ (squareRectangleBoundaryVertex (4 * l) l e.out.1 ∧
        squareRectangleBoundaryVertex (4 * l) l e.out.2) := by
    intro e he
    apply mappedCrossing_edge_not_both_boundary R0 hR0Edges FRight
    intro x hxRect hb
    have hx := mem_squareRectangleVertices_iff.mp hxRect
    unfold squareRectangleBoundaryVertex at hb ⊢
    simp [FRight, squareCrossingTranslateIso, cubicTranslationIso_apply,
      cubicTranslate, squareVertex, cubicOrigin] at hb
    omega
    simpa [Rwalk] using he
  have hVboundary : ∀ e ∈ Vwalk.edges,
      ¬ (squareRectangleBoundaryVertex (4 * l) l e.out.1 ∧
        squareRectangleBoundaryVertex (4 * l) l e.out.2) := by
    intro e he
    apply mappedCrossing_edge_not_both_boundary V0 hV0Edges FVert
    intro x hxRect hb
    have hx := mem_squareRectangleVertices_iff.mp hxRect
    unfold squareRectangleBoundaryVertex at hb ⊢
    simp [FVert, squareCrossingQuarterTurnIso, rswRectangleCenter,
      squareCoordinateSwap, cubicTranslationIso_apply, cubicTranslate,
      cubicCoordinatePermutationIso, cubicCoordinatePermutationEquiv,
      squareVertex, cubicOrigin] at hb
    omega
    simpa [Vwalk] using he
  have hWboundary : ∀ e ∈ W.edges,
      ¬ (squareRectangleBoundaryVertex (4 * l) l e.out.1 ∧
        squareRectangleBoundaryVertex (4 * l) l e.out.2) := by
    intro e he
    simp only [W, SimpleGraph.Walk.edges_append, List.mem_append,
      SimpleGraph.Walk.edges_reverse, List.mem_reverse] at he
    rcases he with he | he | he | he
    · exact hLboundary e (L.walk.edges_takeUntil_subset hzLL he)
    · exact hVboundary e (Vwalk.edges_takeUntil_subset hzLV he)
    · exact hVboundary e (Vwalk.edges_takeUntil_subset hzRV he)
    · exact hRboundary e (Rwalk.edges_dropUntil_subset hzRR he)
  have hWEdges : walkEdgeFinset W ⊆ squareBoundaryFreeRectangleEdges (4 * l) l := by
    intro e he
    rw [squareBoundaryFreeRectangleEdges, Finset.mem_filter]
    refine ⟨walkEdgeFinset_subset_squareRectangleEdges_of_support W hWsupport he, ?_⟩
    exact hWboundary e.1 ((mem_walkEdgeFinset_iff W e).mp he)
  have hStart : L.start ∈ squareRectangleLeft (4 * l) l := by
    rw [mem_squareRectangleLeft_iff]
    have h := mem_squareRectangleLeft_iff.mp L.start_mem
    exact ⟨h.1, h.2.1, h.2.2⟩
  have hFinish : FRight R0.finish ∈ squareRectangleRight (4 * l) l := by
    rw [mem_squareRectangleRight_iff]
    have h := mem_squareRectangleRight_iff.mp R0.finish_mem
    simp [Rwalk, FRight, squareCrossingTranslateIso, cubicTranslationIso_apply,
      cubicTranslate, squareVertex, cubicOrigin]
    omega
  simp only [rswRectangleCrossingEvent, squareBoundaryFreeRectangleCrossingEvent,
    Set.mem_iUnion]
  exact ⟨L.start, hStart, FRight R0.finish, hFinish, W, hWOpen, hWEdges⟩

/-! ### Figure 11.26 -/

/-- Normalize the quarter-turned vertical square crossing in Figure 11.26. -/
def rswThreeVerticalNormalizeIso (l : ℕ) : squareGraph ≃g squareGraph :=
  (squareCrossingQuarterTurnIso (rswRectangleCenter 1 l)
      (squareVertex (3 * l : ℕ) 0)).trans (rswNormalizeIso l)

@[simp]
theorem rswThreeVerticalNormalizeIso_zero (l : ℕ) (x : SquareVertex) :
    rswThreeVerticalNormalizeIso l x 0 = x 1 + 3 * l := by
  simp [rswThreeVerticalNormalizeIso, squareCrossingQuarterTurnIso, rswRectangleCenter,
    squareCoordinateSwap, cubicTranslationIso_apply, cubicTranslate,
    cubicCoordinatePermutationIso, cubicCoordinatePermutationEquiv, squareVertex, cubicOrigin]

@[simp]
theorem rswThreeVerticalNormalizeIso_one (l : ℕ) (x : SquareVertex) :
    rswThreeVerticalNormalizeIso l x 1 = x 0 := by
  simp [rswThreeVerticalNormalizeIso, squareCrossingQuarterTurnIso, rswRectangleCenter,
    squareCoordinateSwap, cubicTranslationIso_apply, cubicTranslate,
    cubicCoordinatePermutationIso, cubicCoordinatePermutationEquiv, squareVertex, cubicOrigin]

/-- Common frame for the right horizontal crossing and vertical crossing in Figure 11.26. -/
def rswThreeRightFrameIso (l : ℕ) : squareGraph ≃g squareGraph :=
  cubicTranslationIso (squareVertex (2 * l : ℕ) (-(l : ℤ))) cubicOrigin

@[simp]
theorem rswThreeRightFrameIso_zero (l : ℕ) (x : SquareVertex) :
    rswThreeRightFrameIso l x 0 = x 0 - 2 * l := by
  simp [rswThreeRightFrameIso, cubicTranslationIso_apply, cubicTranslate, squareVertex,
    cubicOrigin]
  ring

@[simp]
theorem rswThreeRightFrameIso_one (l : ℕ) (x : SquareVertex) :
    rswThreeRightFrameIso l x 1 = x 1 + l := by
  simp [rswThreeRightFrameIso, cubicTranslationIso_apply, cubicTranslate, squareVertex,
    cubicOrigin]

/-- The Figure 11.26 vertical crossing normalized in the right crossing's frame. -/
def rswThreeVerticalRightNormalizeIso (l : ℕ) : squareGraph ≃g squareGraph :=
  (squareCrossingQuarterTurnIso (rswRectangleCenter 1 l)
      (squareVertex (3 * l : ℕ) 0)).trans (rswThreeRightFrameIso l)

@[simp]
theorem rswThreeVerticalRightNormalizeIso_zero (l : ℕ) (x : SquareVertex) :
    rswThreeVerticalRightNormalizeIso l x 0 = x 1 + l := by
  simp [rswThreeVerticalRightNormalizeIso, rswThreeRightFrameIso,
    squareCrossingQuarterTurnIso, rswRectangleCenter, squareCoordinateSwap,
    cubicTranslationIso_apply, cubicTranslate, cubicCoordinatePermutationIso,
    cubicCoordinatePermutationEquiv, squareVertex, cubicOrigin]
  ring

@[simp]
theorem rswThreeVerticalRightNormalizeIso_one (l : ℕ) (x : SquareVertex) :
    rswThreeVerticalRightNormalizeIso l x 1 = x 0 := by
  simp [rswThreeVerticalRightNormalizeIso, rswThreeRightFrameIso,
    squareCrossingQuarterTurnIso, rswRectangleCenter, squareCoordinateSwap,
    cubicTranslationIso_apply, cubicTranslate, cubicCoordinatePermutationIso,
    cubicCoordinatePermutationEquiv, squareVertex, cubicOrigin]

private theorem normalized_three_left_meets_vertical
    (l : ℕ) {omega : EdgeConfiguration 2}
    (L : OpenSquareRectangleCrossing (4 * l) l omega)
    (V : OpenSquareRectangleCrossing (2 * l) l
      (cubicGraphIsoConfigurationPullback
        (squareCrossingQuarterTurnIso (rswRectangleCenter 1 l)
          (squareVertex (3 * l : ℕ) 0)) omega)) :
    ∃ z, z ∈ L.walk.support ∧
      z ∈ (V.walk.map
        (squareCrossingQuarterTurnIso (rswRectangleCenter 1 l)
          (squareVertex (3 * l : ℕ) 0)).toHom).support := by
  let F := rswNormalizeIso l
  let P : squareGraph.Walk (squareVertex 0 (L.start 1 + l))
      (squareVertex (4 * l : ℕ) (L.finish 1 + l)) :=
    (L.walk.map F.toHom).copy (by
      ext i
      fin_cases i
      · simp [F]
        simpa using (mem_squareRectangleLeft_iff.mp L.start_mem).1
      · simp [F, squareVertex]) (by
      ext i
      fin_cases i
      · simp [F, squareVertex]
        simpa using (mem_squareRectangleRight_iff.mp L.finish_mem).1
      · simp [F, squareVertex])
  let Qraw := V.walk.map
    (squareCrossingQuarterTurnIso (rswRectangleCenter 1 l)
      (squareVertex (3 * l : ℕ) 0)).toHom
  let Q : squareGraph.Walk (squareVertex (V.start 1 + 3 * l) 0)
      (squareVertex (V.finish 1 + 3 * l) (2 * l : ℕ)) :=
    (V.walk.map (rswThreeVerticalNormalizeIso l).toHom).copy (by
      ext i
      fin_cases i
      · simp [squareVertex]
      · simp [squareVertex]
        simpa using (mem_squareRectangleLeft_iff.mp V.start_mem).1) (by
      ext i
      fin_cases i
      · simp [squareVertex]
      · simp [squareVertex]
        simpa using (mem_squareRectangleRight_iff.mp V.finish_mem).1)
  have hpbox : ∀ z ∈ P.support,
      0 ≤ z 0 ∧ z 0 ≤ 4 * l ∧ 0 ≤ z 1 ∧ z 1 ≤ 2 * l := by
    intro z hz
    simp only [P, SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map,
      List.mem_map] at hz
    rcases hz with ⟨x, hx, rfl⟩
    have h := mem_squareRectangleVertices_iff.mp (L.support_mem_rectangle hx)
    simp [F]
    omega
  have hqbox : ∀ z ∈ Q.support,
      0 ≤ z 0 ∧ z 0 ≤ 4 * l ∧ 0 ≤ z 1 ∧ z 1 ≤ 2 * l := by
    intro z hz
    simp only [Q, SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map,
      List.mem_map] at hz
    rcases hz with ⟨x, hx, rfl⟩
    have h := mem_squareRectangleVertices_iff.mp (V.support_mem_rectangle hx)
    simp
    omega
  obtain ⟨z, hzP, hzQ⟩ :=
    squareWalk_support_inter_of_left_right_and_bottom_top_of_le_int
      (by omega : 2 * l ≤ 4 * l)
      (by have := (mem_squareRectangleLeft_iff.mp L.start_mem).2.1; omega)
      (by have := (mem_squareRectangleLeft_iff.mp L.start_mem).2.2; omega)
      (by have := (mem_squareRectangleRight_iff.mp L.finish_mem).2.1; omega)
      (by have := (mem_squareRectangleRight_iff.mp L.finish_mem).2.2; omega)
      (by have := (mem_squareRectangleLeft_iff.mp V.start_mem).2.1; omega)
      (by have := (mem_squareRectangleLeft_iff.mp V.start_mem).2.2; omega)
      (by have := (mem_squareRectangleRight_iff.mp V.finish_mem).2.1; omega)
      (by have := (mem_squareRectangleRight_iff.mp V.finish_mem).2.2; omega)
      P Q hpbox hqbox
  have hinter : ∃ z, z ∈ (L.walk.map F.toHom).support ∧
      z ∈ (Qraw.map F.toHom).support := by
    refine ⟨z, ?_, ?_⟩
    · simpa [P] using hzP
    · simpa [Q, Qraw, F, rswThreeVerticalNormalizeIso,
        SimpleGraph.Walk.map_map] using hzQ
  exact walk_support_inter_of_map_support_inter F.toHom F.injective L.walk Qraw hinter

private theorem normalized_three_right_meets_vertical
    (l : ℕ) {omega : EdgeConfiguration 2}
    (R : OpenSquareRectangleCrossing (4 * l) l
      (cubicGraphIsoConfigurationPullback
        (squareCrossingTranslateIso cubicOrigin (squareVertex (2 * l : ℕ) 0)) omega))
    (V : OpenSquareRectangleCrossing (2 * l) l
      (cubicGraphIsoConfigurationPullback
        (squareCrossingQuarterTurnIso (rswRectangleCenter 1 l)
          (squareVertex (3 * l : ℕ) 0)) omega)) :
    ∃ z,
      z ∈ (R.walk.map
        (squareCrossingTranslateIso cubicOrigin (squareVertex (2 * l : ℕ) 0)).toHom).support ∧
      z ∈ (V.walk.map
        (squareCrossingQuarterTurnIso (rswRectangleCenter 1 l)
          (squareVertex (3 * l : ℕ) 0)).toHom).support := by
  let F := rswThreeRightFrameIso l
  let Rraw := R.walk.map
    (squareCrossingTranslateIso cubicOrigin (squareVertex (2 * l : ℕ) 0)).toHom
  let Vraw := V.walk.map
    (squareCrossingQuarterTurnIso (rswRectangleCenter 1 l)
      (squareVertex (3 * l : ℕ) 0)).toHom
  let P : squareGraph.Walk (squareVertex 0 (R.start 1 + l))
      (squareVertex (4 * l : ℕ) (R.finish 1 + l)) :=
    (R.walk.map (rswNormalizeIso l).toHom).copy (by
      ext i
      fin_cases i
      · simpa using (mem_squareRectangleLeft_iff.mp R.start_mem).1
      · simp [squareVertex]) (by
      ext i
      fin_cases i
      · simpa using (mem_squareRectangleRight_iff.mp R.finish_mem).1
      · simp [squareVertex])
  let Q : squareGraph.Walk (squareVertex (V.start 1 + l) 0)
      (squareVertex (V.finish 1 + l) (2 * l : ℕ)) :=
    (V.walk.map (rswThreeVerticalRightNormalizeIso l).toHom).copy (by
      ext i
      fin_cases i
      · simp [squareVertex]
      · simp [squareVertex]
        simpa using (mem_squareRectangleLeft_iff.mp V.start_mem).1) (by
      ext i
      fin_cases i
      · simp [squareVertex]
      · simp [squareVertex]
        simpa using (mem_squareRectangleRight_iff.mp V.finish_mem).1)
  have hpbox : ∀ z ∈ P.support,
      0 ≤ z 0 ∧ z 0 ≤ 4 * l ∧ 0 ≤ z 1 ∧ z 1 ≤ 2 * l := by
    intro z hz
    simp only [P, SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map,
      List.mem_map] at hz
    rcases hz with ⟨x, hx, rfl⟩
    have h := mem_squareRectangleVertices_iff.mp (R.support_mem_rectangle hx)
    simp
    omega
  have hqbox : ∀ z ∈ Q.support,
      0 ≤ z 0 ∧ z 0 ≤ 4 * l ∧ 0 ≤ z 1 ∧ z 1 ≤ 2 * l := by
    intro z hz
    simp only [Q, SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map,
      List.mem_map] at hz
    rcases hz with ⟨x, hx, rfl⟩
    have h := mem_squareRectangleVertices_iff.mp (V.support_mem_rectangle hx)
    simp
    omega
  obtain ⟨z, hzP, hzQ⟩ :=
    squareWalk_support_inter_of_left_right_and_bottom_top_of_le_int
      (by omega : 2 * l ≤ 4 * l)
      (by have := (mem_squareRectangleLeft_iff.mp R.start_mem).2.1; omega)
      (by have := (mem_squareRectangleLeft_iff.mp R.start_mem).2.2; omega)
      (by have := (mem_squareRectangleRight_iff.mp R.finish_mem).2.1; omega)
      (by have := (mem_squareRectangleRight_iff.mp R.finish_mem).2.2; omega)
      (by have := (mem_squareRectangleLeft_iff.mp V.start_mem).2.1; omega)
      (by have := (mem_squareRectangleLeft_iff.mp V.start_mem).2.2; omega)
      (by have := (mem_squareRectangleRight_iff.mp V.finish_mem).2.1; omega)
      (by have := (mem_squareRectangleRight_iff.mp V.finish_mem).2.2; omega)
      P Q hpbox hqbox
  have hinter : ∃ z, z ∈ (Rraw.map F.toHom).support ∧
      z ∈ (Vraw.map F.toHom).support := by
    refine ⟨z, ?_, ?_⟩
    · simp only [P, SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map,
        List.mem_map] at hzP
      rcases hzP with ⟨x, hx, hxz⟩
      simp only [Rraw, SimpleGraph.Walk.support_map, List.mem_map]
      refine ⟨squareCrossingTranslateIso cubicOrigin (squareVertex (2 * l : ℕ) 0) x, ?_, ?_⟩
      · exact ⟨x, hx, rfl⟩
      · rw [← hxz]
        ext i
        fin_cases i
        · simp [F, rswThreeRightFrameIso, squareCrossingTranslateIso,
            cubicTranslationIso_apply, cubicTranslate, squareVertex, cubicOrigin]
        · simp [F, rswThreeRightFrameIso, squareCrossingTranslateIso,
            cubicTranslationIso_apply, cubicTranslate, squareVertex, cubicOrigin]
    · simpa [Q, Vraw, F, rswThreeVerticalRightNormalizeIso,
        SimpleGraph.Walk.map_map] using hzQ
  exact walk_support_inter_of_map_support_inter F.toHom F.injective Rraw Vraw hinter

/-- The crossings in Figure 11.26 glue to a crossing of the enclosing rectangle. -/
theorem rswGluingThreeIntersection_subset (l : ℕ) (_hl : 1 ≤ l) :
    rswGluingThreeIntersection l ⊆ rswRectangleCrossingEvent 3 l := by
  intro omega h
  rcases h with ⟨⟨hL, hR⟩, hV⟩
  let FRight := squareCrossingTranslateIso cubicOrigin (squareVertex (2 * l : ℕ) 0)
  let FVert := squareCrossingQuarterTurnIso (rswRectangleCenter 1 l)
    (squareVertex (3 * l : ℕ) 0)
  change omega ∈ squareBoundaryFreeRectangleCrossingEvent (4 * l) l at hL
  change cubicGraphIsoConfigurationPullback FRight omega ∈
    squareBoundaryFreeRectangleCrossingEvent (4 * l) l at hR
  change cubicGraphIsoConfigurationPullback FVert omega ∈
    squareBoundaryFreeRectangleCrossingEvent (2 * l) l at hV
  obtain ⟨L, hLEdges⟩ := exists_openSquareRectangleCrossing_of_mem_boundaryFree hL
  obtain ⟨R0, hR0Edges⟩ := exists_openSquareRectangleCrossing_of_mem_boundaryFree hR
  obtain ⟨V0, hV0Edges⟩ := exists_openSquareRectangleCrossing_of_mem_boundaryFree hV
  let Rwalk := R0.walk.map FRight.toHom
  let Vwalk := V0.walk.map FVert.toHom
  obtain ⟨zL, hzLL, hzLV⟩ := normalized_three_left_meets_vertical l L V0
  have hRV : ∃ z, z ∈ Rwalk.support ∧ z ∈ Vwalk.support := by
    simpa [Rwalk, Vwalk, FRight, FVert] using
      normalized_three_right_meets_vertical l R0 V0
  obtain ⟨zR, hzRR, hzRV⟩ := hRV
  have hRopen : walkIsOpen omega Rwalk := by
    exact walkIsOpen_map_cubicGraphIso FRight R0.walk R0.isOpen
  have hVopen : walkIsOpen omega Vwalk := by
    exact walkIsOpen_map_cubicGraphIso FVert V0.walk V0.isOpen
  let pL := L.walk.takeUntil zL hzLL
  let vL := Vwalk.takeUntil zL hzLV
  let vR := Vwalk.takeUntil zR hzRV
  let pR := Rwalk.dropUntil zR hzRR
  let W := pL.append (vL.reverse.append (vR.append pR))
  have hpLOpen : walkIsOpen omega pL :=
    walkIsOpen_of_edges_subset L.isOpen (L.walk.edges_takeUntil_subset hzLL)
  have hvLOpen : walkIsOpen omega vL :=
    walkIsOpen_of_edges_subset hVopen (Vwalk.edges_takeUntil_subset hzLV)
  have hvROpen : walkIsOpen omega vR :=
    walkIsOpen_of_edges_subset hVopen (Vwalk.edges_takeUntil_subset hzRV)
  have hpROpen : walkIsOpen omega pR :=
    walkIsOpen_of_edges_subset hRopen (Rwalk.edges_dropUntil_subset hzRR)
  have hWOpen : walkIsOpen omega W := by
    exact walkIsOpen_append hpLOpen
      (walkIsOpen_append (walkIsOpen_reverse hvLOpen)
        (walkIsOpen_append hvROpen hpROpen))
  have hLsupport : ∀ z ∈ L.walk.support, z ∈ squareRectangleVertices (6 * l) l := by
    intro z hz
    have h := mem_squareRectangleVertices_iff.mp (L.support_mem_rectangle hz)
    rw [mem_squareRectangleVertices_iff]
    omega
  have hRsupport : ∀ z ∈ Rwalk.support, z ∈ squareRectangleVertices (6 * l) l := by
    intro z hz
    simp only [Rwalk, SimpleGraph.Walk.support_map, List.mem_map] at hz
    rcases hz with ⟨x, hx, rfl⟩
    have h := mem_squareRectangleVertices_iff.mp (R0.support_mem_rectangle hx)
    rw [mem_squareRectangleVertices_iff]
    simp [FRight, squareCrossingTranslateIso, cubicTranslationIso_apply,
      cubicTranslate, squareVertex, cubicOrigin]
    omega
  have hVsupport : ∀ z ∈ Vwalk.support, z ∈ squareRectangleVertices (6 * l) l := by
    intro z hz
    simp only [Vwalk, SimpleGraph.Walk.support_map, List.mem_map] at hz
    rcases hz with ⟨x, hx, rfl⟩
    have h := mem_squareRectangleVertices_iff.mp (V0.support_mem_rectangle hx)
    rw [mem_squareRectangleVertices_iff]
    simp [FVert, squareCrossingQuarterTurnIso, rswRectangleCenter,
      squareCoordinateSwap, cubicTranslationIso_apply, cubicTranslate,
      cubicCoordinatePermutationIso, cubicCoordinatePermutationEquiv,
      squareVertex, cubicOrigin]
    omega
  have hWsupport : ∀ z ∈ W.support, z ∈ squareRectangleVertices (6 * l) l := by
    intro z hz
    simp only [W, SimpleGraph.Walk.mem_support_append_iff,
      SimpleGraph.Walk.support_reverse] at hz
    rcases hz with hz | hz | hz | hz
    · exact hLsupport z (L.walk.support_takeUntil_subset_support hzLL hz)
    · have hz' : z ∈ vL.support := by simpa using hz
      exact hVsupport z (Vwalk.support_takeUntil_subset_support hzLV hz')
    · exact hVsupport z (Vwalk.support_takeUntil_subset_support hzRV hz)
    · exact hRsupport z (Rwalk.support_dropUntil_subset hzRR hz)
  have hLboundary : ∀ e ∈ L.walk.edges,
      ¬ (squareRectangleBoundaryVertex (6 * l) l e.out.1 ∧
        squareRectangleBoundaryVertex (6 * l) l e.out.2) := by
    intro e he hb
    let ee : SquareEdge := ⟨e, L.walk.edges_subset_edgeSet he⟩
    have hee : ee ∈ walkEdgeFinset L.walk := (mem_walkEdgeFinset_iff L.walk ee).mpr he
    have hnot := (Finset.mem_filter.mp (hLEdges hee)).2
    apply hnot
    have hmem : ∀ x ∈ e, x ∈ squareRectangleVertices (4 * l) l := by
      intro x hx
      exact L.support_mem_rectangle (L.walk.mem_support_of_mem_edges he hx)
    have pull (x : SquareVertex) (hx : x ∈ e)
        (hb : squareRectangleBoundaryVertex (6 * l) l x) :
        squareRectangleBoundaryVertex (4 * l) l x := by
      have hr := mem_squareRectangleVertices_iff.mp (hmem x hx)
      unfold squareRectangleBoundaryVertex at hb ⊢
      omega
    exact ⟨pull ee.1.out.1 (Sym2.out_fst_mem ee.1) hb.1,
      pull ee.1.out.2 (Sym2.out_snd_mem ee.1) hb.2⟩
  have hRboundary : ∀ e ∈ Rwalk.edges,
      ¬ (squareRectangleBoundaryVertex (6 * l) l e.out.1 ∧
        squareRectangleBoundaryVertex (6 * l) l e.out.2) := by
    intro e he
    apply mappedCrossing_edge_not_both_boundary R0 hR0Edges FRight
    intro x hxRect hb
    have hx := mem_squareRectangleVertices_iff.mp hxRect
    unfold squareRectangleBoundaryVertex at hb ⊢
    simp [FRight, squareCrossingTranslateIso, cubicTranslationIso_apply,
      cubicTranslate, squareVertex, cubicOrigin] at hb
    omega
    simpa [Rwalk] using he
  have hVboundary : ∀ e ∈ Vwalk.edges,
      ¬ (squareRectangleBoundaryVertex (6 * l) l e.out.1 ∧
        squareRectangleBoundaryVertex (6 * l) l e.out.2) := by
    intro e he
    apply mappedCrossing_edge_not_both_boundary V0 hV0Edges FVert
    intro x hxRect hb
    have hx := mem_squareRectangleVertices_iff.mp hxRect
    unfold squareRectangleBoundaryVertex at hb ⊢
    simp [FVert, squareCrossingQuarterTurnIso, rswRectangleCenter,
      squareCoordinateSwap, cubicTranslationIso_apply, cubicTranslate,
      cubicCoordinatePermutationIso, cubicCoordinatePermutationEquiv,
      squareVertex, cubicOrigin] at hb
    omega
    simpa [Vwalk] using he
  have hWboundary : ∀ e ∈ W.edges,
      ¬ (squareRectangleBoundaryVertex (6 * l) l e.out.1 ∧
        squareRectangleBoundaryVertex (6 * l) l e.out.2) := by
    intro e he
    simp only [W, SimpleGraph.Walk.edges_append, List.mem_append,
      SimpleGraph.Walk.edges_reverse, List.mem_reverse] at he
    rcases he with he | he | he | he
    · exact hLboundary e (L.walk.edges_takeUntil_subset hzLL he)
    · exact hVboundary e (Vwalk.edges_takeUntil_subset hzLV he)
    · exact hVboundary e (Vwalk.edges_takeUntil_subset hzRV he)
    · exact hRboundary e (Rwalk.edges_dropUntil_subset hzRR he)
  have hWEdges : walkEdgeFinset W ⊆ squareBoundaryFreeRectangleEdges (6 * l) l := by
    intro e he
    rw [squareBoundaryFreeRectangleEdges, Finset.mem_filter]
    refine ⟨walkEdgeFinset_subset_squareRectangleEdges_of_support W hWsupport he, ?_⟩
    exact hWboundary e.1 ((mem_walkEdgeFinset_iff W e).mp he)
  have hStart : L.start ∈ squareRectangleLeft (6 * l) l := by
    rw [mem_squareRectangleLeft_iff]
    have h := mem_squareRectangleLeft_iff.mp L.start_mem
    exact ⟨h.1, h.2.1, h.2.2⟩
  have hFinish : FRight R0.finish ∈ squareRectangleRight (6 * l) l := by
    rw [mem_squareRectangleRight_iff]
    have h := mem_squareRectangleRight_iff.mp R0.finish_mem
    simp [Rwalk, FRight, squareCrossingTranslateIso, cubicTranslationIso_apply,
      cubicTranslate, squareVertex, cubicOrigin]
    omega
  simp only [rswRectangleCrossingEvent, squareBoundaryFreeRectangleCrossingEvent,
    Set.mem_iUnion]
  exact ⟨L.start, hStart, FRight R0.finish, hFinish, W, hWOpen, hWEdges⟩

end Percolation
