import Percolation.Planar.OddCycleExtraction
import Percolation.Planar.RSWIncidence

/-!
# Deterministic RSW circuit gluing

This file supplies the deterministic content of Grimmett's Figure 11.27.  Four explicit
boundary-free crossings are first converted to paths.  A common translation identifies their
ambient square with `[0,6l]²`, where the discrete rectangle-intersection theorem gives all four
corner incidences.  The resulting closed walk is reduced mod two to a simple odd-index cycle.
-/

namespace Percolation

/-- Translate the ambient square `[-3l,3l]²` of Figure 11.27 to `[0,6l]²`. -/
def rswCircuitFrameIso (l : ℕ) : squareGraph ≃g squareGraph :=
  cubicTranslationIso (squareVertex (-(3 * l : ℕ) : ℤ) (-(3 * l : ℕ) : ℤ)) cubicOrigin

@[simp]
theorem rswCircuitFrameIso_zero (l : ℕ) (x : SquareVertex) :
    rswCircuitFrameIso l x 0 = x 0 + 3 * l := by
  simp [rswCircuitFrameIso, cubicTranslationIso_apply, cubicTranslate, squareVertex, cubicOrigin]

@[simp]
theorem rswCircuitFrameIso_one (l : ℕ) (x : SquareVertex) :
    rswCircuitFrameIso l x 1 = x 1 + 3 * l := by
  simp [rswCircuitFrameIso, cubicTranslationIso_apply, cubicTranslate, squareVertex, cubicOrigin]

/-- Source-to-normalized placement of the top horizontal crossing. -/
def rswCircuitTopNormalizeIso (l : ℕ) : squareGraph ≃g squareGraph :=
  (squareCrossingTranslateIso (rswRectangleCenter 3 l)
      (squareVertex 0 (2 * l : ℕ))).trans (rswCircuitFrameIso l)

/-- Source-to-normalized placement of the bottom horizontal crossing. -/
def rswCircuitBottomNormalizeIso (l : ℕ) : squareGraph ≃g squareGraph :=
  (squareCrossingTranslateIso (rswRectangleCenter 3 l)
      (squareVertex 0 (-(2 * l : ℕ) : ℤ))).trans (rswCircuitFrameIso l)

/-- Source-to-normalized placement of the right vertical crossing. -/
def rswCircuitRightNormalizeIso (l : ℕ) : squareGraph ≃g squareGraph :=
  (squareCrossingQuarterTurnIso (rswRectangleCenter 3 l)
      (squareVertex (2 * l : ℕ) 0)).trans (rswCircuitFrameIso l)

/-- Source-to-normalized placement of the left vertical crossing. -/
def rswCircuitLeftNormalizeIso (l : ℕ) : squareGraph ≃g squareGraph :=
  (squareCrossingQuarterTurnIso (rswRectangleCenter 3 l)
      (squareVertex (-(2 * l : ℕ) : ℤ) 0)).trans (rswCircuitFrameIso l)

@[simp]
theorem rswCircuitTopNormalizeIso_zero (l : ℕ) (x : SquareVertex) :
    rswCircuitTopNormalizeIso l x 0 = x 0 := by
  simp [rswCircuitTopNormalizeIso, squareCrossingTranslateIso, rswRectangleCenter,
    cubicTranslationIso_apply, cubicTranslate, squareVertex, cubicOrigin]

@[simp]
theorem rswCircuitTopNormalizeIso_one (l : ℕ) (x : SquareVertex) :
    rswCircuitTopNormalizeIso l x 1 = x 1 + 5 * l := by
  simp [rswCircuitTopNormalizeIso, squareCrossingTranslateIso, rswRectangleCenter,
    cubicTranslationIso_apply, cubicTranslate, squareVertex, cubicOrigin]
  ring

@[simp]
theorem rswCircuitBottomNormalizeIso_zero (l : ℕ) (x : SquareVertex) :
    rswCircuitBottomNormalizeIso l x 0 = x 0 := by
  simp [rswCircuitBottomNormalizeIso, squareCrossingTranslateIso, rswRectangleCenter,
    cubicTranslationIso_apply, cubicTranslate, squareVertex, cubicOrigin]

@[simp]
theorem rswCircuitBottomNormalizeIso_one (l : ℕ) (x : SquareVertex) :
    rswCircuitBottomNormalizeIso l x 1 = x 1 + l := by
  simp [rswCircuitBottomNormalizeIso, squareCrossingTranslateIso, rswRectangleCenter,
    cubicTranslationIso_apply, cubicTranslate, squareVertex, cubicOrigin]
  ring

@[simp]
theorem rswCircuitRightNormalizeIso_zero (l : ℕ) (x : SquareVertex) :
    rswCircuitRightNormalizeIso l x 0 = x 1 + 5 * l := by
  simp [rswCircuitRightNormalizeIso, squareCrossingQuarterTurnIso, rswRectangleCenter,
    squareCoordinateSwap, cubicTranslationIso_apply, cubicTranslate,
    cubicCoordinatePermutationIso, cubicCoordinatePermutationEquiv, squareVertex, cubicOrigin]
  ring

@[simp]
theorem rswCircuitRightNormalizeIso_one (l : ℕ) (x : SquareVertex) :
    rswCircuitRightNormalizeIso l x 1 = x 0 := by
  simp [rswCircuitRightNormalizeIso, squareCrossingQuarterTurnIso, rswRectangleCenter,
    squareCoordinateSwap, cubicTranslationIso_apply, cubicTranslate,
    cubicCoordinatePermutationIso, cubicCoordinatePermutationEquiv, squareVertex, cubicOrigin]

@[simp]
theorem rswCircuitLeftNormalizeIso_zero (l : ℕ) (x : SquareVertex) :
    rswCircuitLeftNormalizeIso l x 0 = x 1 + l := by
  simp [rswCircuitLeftNormalizeIso, squareCrossingQuarterTurnIso, rswRectangleCenter,
    squareCoordinateSwap, cubicTranslationIso_apply, cubicTranslate,
    cubicCoordinatePermutationIso, cubicCoordinatePermutationEquiv, squareVertex, cubicOrigin]
  ring

@[simp]
theorem rswCircuitLeftNormalizeIso_one (l : ℕ) (x : SquareVertex) :
    rswCircuitLeftNormalizeIso l x 1 = x 0 := by
  simp [rswCircuitLeftNormalizeIso, squareCrossingQuarterTurnIso, rswRectangleCenter,
    squareCoordinateSwap, cubicTranslationIso_apply, cubicTranslate,
    cubicCoordinatePermutationIso, cubicCoordinatePermutationEquiv, squareVertex, cubicOrigin]

/-- Join two visited vertices of a walk through its starting point.  This ordering-free
construction is convenient when the planar intersection theorem supplies no order along the
crossing. -/
def squareWalkBetweenViaStart {u v a b : SquareVertex} (p : squareGraph.Walk u v)
    (ha : a ∈ p.support) (hb : b ∈ p.support) : squareGraph.Walk a b :=
  (p.takeUntil a ha).reverse.append (p.takeUntil b hb)

theorem squareWalkBetweenViaStart_support_subset {u v a b : SquareVertex}
    (p : squareGraph.Walk u v) (ha : a ∈ p.support) (hb : b ∈ p.support) :
    (squareWalkBetweenViaStart p ha hb).support ⊆ p.support := by
  intro z hz
  simp only [squareWalkBetweenViaStart, SimpleGraph.Walk.mem_support_append_iff,
    SimpleGraph.Walk.support_reverse] at hz
  rcases hz with hz | hz
  · exact p.support_takeUntil_subset_support ha (by simpa using hz)
  · exact p.support_takeUntil_subset_support hb hz

theorem squareWalkBetweenViaStart_edges_subset {u v a b : SquareVertex}
    (p : squareGraph.Walk u v) (ha : a ∈ p.support) (hb : b ∈ p.support) :
    (squareWalkBetweenViaStart p ha hb).edges ⊆ p.edges := by
  intro e he
  simp only [squareWalkBetweenViaStart, SimpleGraph.Walk.edges_append,
    List.mem_append, SimpleGraph.Walk.edges_reverse, List.mem_reverse] at he
  exact he.elim (fun h ↦ p.edges_takeUntil_subset ha h)
    (fun h ↦ p.edges_takeUntil_subset hb h)

private theorem horizontalRayCount_eq_zero_of_support_above
    {u v : SquareVertex} (p : squareGraph.Walk u v)
    (hpos : ∀ z ∈ p.support, 0 < z 1) :
    p.edges.countP (squareEdgeCrossesFaceHorizontalRayBool cubicOrigin) = 0 := by
  rw [List.countP_eq_zero]
  intro e he
  induction e using Sym2.ind with
  | _ x y =>
      have hx := hpos x (p.fst_mem_support_of_mem_edges he)
      have hy := hpos y (p.snd_mem_support_of_mem_edges he)
      simp [squareEdgeCrossesFaceHorizontalRayBool, squareEdgeCrossesFaceHorizontalRay,
        cubicOrigin]
      omega

private theorem horizontalRayCount_eq_zero_of_support_below
    {u v : SquareVertex} (p : squareGraph.Walk u v)
    (hneg : ∀ z ∈ p.support, z 1 < 0) :
    p.edges.countP (squareEdgeCrossesFaceHorizontalRayBool cubicOrigin) = 0 := by
  rw [List.countP_eq_zero]
  intro e he
  induction e using Sym2.ind with
  | _ x y =>
      have hx := hneg x (p.fst_mem_support_of_mem_edges he)
      have hy := hneg y (p.snd_mem_support_of_mem_edges he)
      simp [squareEdgeCrossesFaceHorizontalRayBool, squareEdgeCrossesFaceHorizontalRay,
        cubicOrigin]
      omega

private theorem horizontalRayCount_eq_zero_of_support_left
    {u v : SquareVertex} (p : squareGraph.Walk u v)
    (hleft : ∀ z ∈ p.support, z 0 < 0) :
    p.edges.countP (squareEdgeCrossesFaceHorizontalRayBool cubicOrigin) = 0 := by
  rw [List.countP_eq_zero]
  intro e he
  induction e using Sym2.ind with
  | _ x y =>
      have hx := hleft x (p.fst_mem_support_of_mem_edges he)
      have hy := hleft y (p.snd_mem_support_of_mem_edges he)
      simp [squareEdgeCrossesFaceHorizontalRayBool, squareEdgeCrossesFaceHorizontalRay,
        cubicOrigin]
      omega

private theorem verticalRayCount_eq_zero_of_support_right
    {u v : SquareVertex} (p : squareGraph.Walk u v)
    (hright : ∀ z ∈ p.support, 0 < z 0) :
    p.edges.countP (squareEdgeCrossesFaceVerticalRayBool cubicOrigin) = 0 := by
  rw [List.countP_eq_zero]
  intro e he
  induction e using Sym2.ind with
  | _ x y =>
      have hx := hright x (p.fst_mem_support_of_mem_edges he)
      have hy := hright y (p.snd_mem_support_of_mem_edges he)
      simp [squareEdgeCrossesFaceVerticalRayBool, squareEdgeCrossesFaceVerticalRay,
        cubicOrigin]
      omega

private theorem odd_horizontalRayCount_of_support_right
    {u v : SquareVertex} (p : squareGraph.Walk u v)
    (hright : ∀ z ∈ p.support, 0 < z 0)
    (hu : 0 < u 1) (hv : v 1 < 0) :
    Odd (p.edges.countP (squareEdgeCrossesFaceHorizontalRayBool cubicOrigin)) := by
  have hcutOdd : Odd (p.edges.countP
      (SimpleGraph.Walk.edgeCrossesSetBool (squareFaceNorthEast cubicOrigin))) := by
    apply (SimpleGraph.Walk.odd_countP_edges_edgeCrossesSet_iff
      (squareFaceNorthEast cubicOrigin) p).mpr
    refine Or.inl ⟨?_, ?_⟩
    · exact ⟨by simpa [squareFaceNorthEast, cubicOrigin] using hright u p.start_mem_support,
        by simpa [squareFaceNorthEast, cubicOrigin] using hu⟩
    · intro hvNE
      have hvPos : 0 < v 1 := by simpa [squareFaceNorthEast, cubicOrigin] using hvNE.2
      omega
  have hsum := walk_northEastCut_count_eq_add_faceRays p cubicOrigin
  have hvertical := verticalRayCount_eq_zero_of_support_right p hright
  rw [hsum, hvertical, add_zero] at hcutOdd
  exact hcutOdd

private theorem crossingPath_avoids_horizontal_boundary_interior
    {m n : ℕ} (hm : 0 < m) {eta : EdgeConfiguration 2}
    (C : OpenSquareRectangleCrossing m n eta)
    (hfree : walkEdgeFinset C.walk ⊆ squareBoundaryFreeRectangleEdges m n)
    {z : SquareVertex}
    (hz : z ∈ (C.walk.toPath : squareGraph.Walk C.start C.finish).support)
    (hz0 : 0 < z 0) (hzm : z 0 < m) :
    -(n : ℤ) < z 1 ∧ z 1 < n := by
  let p : squareGraph.Walk C.start C.finish := C.walk.toPath
  have hzRaw : z ∈ C.walk.support := C.walk.support_toPath_subset hz
  have hzRect := mem_squareRectangleVertices_iff.mp (C.support_mem_rectangle hzRaw)
  have hstart0 := (mem_squareRectangleLeft_iff.mp C.start_mem).1
  have hfinish0 := (mem_squareRectangleRight_iff.mp C.finish_mem).1
  have hne : C.start ≠ C.finish := by
    intro h
    have := congrFun h 0
    omega
  have hpNotNil : ¬ p.Nil := SimpleGraph.Walk.not_nil_of_ne hne
  have hzStart : z ≠ C.start := by
    intro h
    have := congrFun h 0
    omega
  have hzFinish : z ≠ C.finish := by
    intro h
    have := congrFun h 0
    omega
  have hEven : Even (p.edges.countP fun e ↦ z ∈ e) := by
    exact ((C.walk.toPath.property.isTrail.even_countP_edges_iff z).mpr
      (fun _ ↦ ⟨hzStart, hzFinish⟩))
  have hincident : ∃ e ∈ p.edges, z ∈ e :=
    (SimpleGraph.Walk.mem_support_iff_exists_mem_edges_of_not_nil hpNotNil).mp hz
  rcases hincident with ⟨e0, he0, hze0⟩
  have uniqueTop (heq : z 1 = n) :
      ∀ e ∈ p.edges, z ∈ e →
        e = s(z, cubicStepFrom z (⟨1, by decide⟩, false)) := by
    intro e he hze
    rcases Sym2.mem_iff_exists.mp hze with ⟨q, hqe⟩
    have heRaw : e ∈ C.walk.edges := C.walk.edges_toPath_subset he
    have hzqAdj : squareGraph.Adj z q := by
      have he' : s(z, q) ∈ p.edges := hqe ▸ he
      exact p.adj_of_mem_edges he'
    rcases (cubicGraph_adj_iff_exists_stepFrom z q).mp hzqAdj with ⟨i, rfl⟩
    have hqSupport : cubicStepFrom z i ∈ C.walk.support := by
      exact C.walk.support_toPath_subset
        (p.mem_support_of_mem_edges he (by simpa [hqe]))
    have hqRect := mem_squareRectangleVertices_iff.mp (C.support_mem_rectangle hqSupport)
    let ee : SquareEdge := ⟨e, C.walk.edges_subset_edgeSet heRaw⟩
    have heFin : ee ∈ walkEdgeFinset C.walk := (mem_walkEdgeFinset_iff C.walk ee).mpr heRaw
    have hnot := (Finset.mem_filter.mp (hfree heFin)).2
    rcases i with ⟨i, b⟩
    fin_cases i <;> cases b
    · exfalso
      apply hnot
      have allBoundary : ∀ x ∈ (e : Sym2 SquareVertex),
          squareRectangleBoundaryVertex m n x := by
        intro x hx
        rw [hqe, Sym2.mem_iff] at hx
        rcases hx with rfl | rfl
        · simp [squareRectangleBoundaryVertex, heq]
        · simp [squareRectangleBoundaryVertex, heq, cubicStepFrom,
            cubicDirectionIncrement]
      exact ⟨allBoundary ee.1.out.1 (Sym2.out_fst_mem ee.1),
        allBoundary ee.1.out.2 (Sym2.out_snd_mem ee.1)⟩
    · exfalso
      apply hnot
      have allBoundary : ∀ x ∈ (e : Sym2 SquareVertex),
          squareRectangleBoundaryVertex m n x := by
        intro x hx
        rw [hqe, Sym2.mem_iff] at hx
        rcases hx with rfl | rfl
        · simp [squareRectangleBoundaryVertex, heq]
        · simp [squareRectangleBoundaryVertex, heq, cubicStepFrom,
            cubicDirectionIncrement]
      exact ⟨allBoundary ee.1.out.1 (Sym2.out_fst_mem ee.1),
        allBoundary ee.1.out.2 (Sym2.out_snd_mem ee.1)⟩
    · simp [hqe]
    · exfalso
      simp [cubicStepFrom, cubicDirectionIncrement, heq] at hqRect
  have uniqueBottom (heq : z 1 = -(n : ℤ)) :
      ∀ e ∈ p.edges, z ∈ e →
        e = s(z, cubicStepFrom z (⟨1, by decide⟩, true)) := by
    intro e he hze
    rcases Sym2.mem_iff_exists.mp hze with ⟨q, hqe⟩
    have heRaw : e ∈ C.walk.edges := C.walk.edges_toPath_subset he
    have hzqAdj : squareGraph.Adj z q := by
      have he' : s(z, q) ∈ p.edges := hqe ▸ he
      exact p.adj_of_mem_edges he'
    rcases (cubicGraph_adj_iff_exists_stepFrom z q).mp hzqAdj with ⟨i, rfl⟩
    have hqSupport : cubicStepFrom z i ∈ C.walk.support := by
      exact C.walk.support_toPath_subset
        (p.mem_support_of_mem_edges he (by simpa [hqe]))
    have hqRect := mem_squareRectangleVertices_iff.mp (C.support_mem_rectangle hqSupport)
    let ee : SquareEdge := ⟨e, C.walk.edges_subset_edgeSet heRaw⟩
    have heFin : ee ∈ walkEdgeFinset C.walk := (mem_walkEdgeFinset_iff C.walk ee).mpr heRaw
    have hnot := (Finset.mem_filter.mp (hfree heFin)).2
    rcases i with ⟨i, b⟩
    fin_cases i <;> cases b
    · exfalso
      apply hnot
      have allBoundary : ∀ x ∈ (e : Sym2 SquareVertex),
          squareRectangleBoundaryVertex m n x := by
        intro x hx
        rw [hqe, Sym2.mem_iff] at hx
        rcases hx with rfl | rfl
        · simp [squareRectangleBoundaryVertex, heq]
        · simp [squareRectangleBoundaryVertex, heq, cubicStepFrom,
            cubicDirectionIncrement]
      exact ⟨allBoundary ee.1.out.1 (Sym2.out_fst_mem ee.1),
        allBoundary ee.1.out.2 (Sym2.out_snd_mem ee.1)⟩
    · exfalso
      apply hnot
      have allBoundary : ∀ x ∈ (e : Sym2 SquareVertex),
          squareRectangleBoundaryVertex m n x := by
        intro x hx
        rw [hqe, Sym2.mem_iff] at hx
        rcases hx with rfl | rfl
        · simp [squareRectangleBoundaryVertex, heq]
        · simp [squareRectangleBoundaryVertex, heq, cubicStepFrom,
            cubicDirectionIncrement]
      exact ⟨allBoundary ee.1.out.1 (Sym2.out_fst_mem ee.1),
        allBoundary ee.1.out.2 (Sym2.out_snd_mem ee.1)⟩
    · exfalso
      simp [cubicStepFrom, cubicDirectionIncrement, heq] at hqRect
    · simp [hqe]
  have notTop : z 1 ≠ n := by
    intro heq
    have hpred : ∀ e ∈ p.edges, (z ∈ e) ↔ e = e0 := by
      intro e he
      constructor
      · intro hze
        exact (uniqueTop heq e he hze).trans (uniqueTop heq e0 he0 hze0).symm
      · intro h
        simpa [h] using hze0
    have hcount : p.edges.countP (fun e ↦ z ∈ e) = p.edges.count e0 := by
      apply List.countP_congr
      intro e he
      simpa only [decide_eq_true_eq, beq_iff_eq] using hpred e he
    have hcountOne : p.edges.countP (fun e ↦ z ∈ e) = 1 := by
      rw [hcount]
      exact List.count_eq_one_of_mem C.walk.toPath.property.isTrail.edges_nodup he0
    rw [hcountOne] at hEven
    exact (Nat.not_even_one hEven)
  have notBottom : z 1 ≠ -(n : ℤ) := by
    intro heq
    have hpred : ∀ e ∈ p.edges, (z ∈ e) ↔ e = e0 := by
      intro e he
      constructor
      · intro hze
        exact (uniqueBottom heq e he hze).trans (uniqueBottom heq e0 he0 hze0).symm
      · intro h
        simpa [h] using hze0
    have hcount : p.edges.countP (fun e ↦ z ∈ e) = p.edges.count e0 := by
      apply List.countP_congr
      intro e he
      simpa only [decide_eq_true_eq, beq_iff_eq] using hpred e he
    have hcountOne : p.edges.countP (fun e ↦ z ∈ e) = 1 := by
      rw [hcount]
      exact List.count_eq_one_of_mem C.walk.toPath.property.isTrail.edges_nodup he0
    rw [hcountOne] at hEven
    exact (Nat.not_even_one hEven)
  omega

/-- The top crossing path in the ambient coordinates of Figure 11.27. -/
def rswCircuitTopPath (l : ℕ) {omega : EdgeConfiguration 2}
    (T0 : OpenSquareRectangleCrossing (6 * l) l
      (cubicGraphIsoConfigurationPullback
        (squareCrossingTranslateIso (rswRectangleCenter 3 l)
          (squareVertex 0 (2 * l : ℕ))) omega)) :
    squareGraph.Walk
      (squareCrossingTranslateIso (rswRectangleCenter 3 l)
        (squareVertex 0 (2 * l : ℕ)) T0.start)
      (squareCrossingTranslateIso (rswRectangleCenter 3 l)
        (squareVertex 0 (2 * l : ℕ)) T0.finish) :=
  (T0.walk.toPath : squareGraph.Walk T0.start T0.finish).map
    (squareCrossingTranslateIso (rswRectangleCenter 3 l)
      (squareVertex 0 (2 * l : ℕ))).toHom

/-- The bottom crossing path in the ambient coordinates of Figure 11.27. -/
def rswCircuitBottomPath (l : ℕ) {omega : EdgeConfiguration 2}
    (B0 : OpenSquareRectangleCrossing (6 * l) l
      (cubicGraphIsoConfigurationPullback
        (squareCrossingTranslateIso (rswRectangleCenter 3 l)
          (squareVertex 0 (-(2 * l : ℕ) : ℤ))) omega)) :
    squareGraph.Walk
      (squareCrossingTranslateIso (rswRectangleCenter 3 l)
        (squareVertex 0 (-(2 * l : ℕ) : ℤ)) B0.start)
      (squareCrossingTranslateIso (rswRectangleCenter 3 l)
        (squareVertex 0 (-(2 * l : ℕ) : ℤ)) B0.finish) :=
  (B0.walk.toPath : squareGraph.Walk B0.start B0.finish).map
    (squareCrossingTranslateIso (rswRectangleCenter 3 l)
      (squareVertex 0 (-(2 * l : ℕ) : ℤ))).toHom

/-- The right crossing path in the ambient coordinates of Figure 11.27. -/
def rswCircuitRightPath (l : ℕ) {omega : EdgeConfiguration 2}
    (R0 : OpenSquareRectangleCrossing (6 * l) l
      (cubicGraphIsoConfigurationPullback
        (squareCrossingQuarterTurnIso (rswRectangleCenter 3 l)
          (squareVertex (2 * l : ℕ) 0)) omega)) :
    squareGraph.Walk
      (squareCrossingQuarterTurnIso (rswRectangleCenter 3 l)
        (squareVertex (2 * l : ℕ) 0) R0.start)
      (squareCrossingQuarterTurnIso (rswRectangleCenter 3 l)
        (squareVertex (2 * l : ℕ) 0) R0.finish) :=
  (R0.walk.toPath : squareGraph.Walk R0.start R0.finish).map
    (squareCrossingQuarterTurnIso (rswRectangleCenter 3 l)
      (squareVertex (2 * l : ℕ) 0)).toHom

/-- The left crossing path in the ambient coordinates of Figure 11.27. -/
def rswCircuitLeftPath (l : ℕ) {omega : EdgeConfiguration 2}
    (L0 : OpenSquareRectangleCrossing (6 * l) l
      (cubicGraphIsoConfigurationPullback
        (squareCrossingQuarterTurnIso (rswRectangleCenter 3 l)
          (squareVertex (-(2 * l : ℕ) : ℤ) 0)) omega)) :
    squareGraph.Walk
      (squareCrossingQuarterTurnIso (rswRectangleCenter 3 l)
        (squareVertex (-(2 * l : ℕ) : ℤ) 0) L0.start)
      (squareCrossingQuarterTurnIso (rswRectangleCenter 3 l)
        (squareVertex (-(2 * l : ℕ) : ℤ) 0) L0.finish) :=
  (L0.walk.toPath : squareGraph.Walk L0.start L0.finish).map
    (squareCrossingQuarterTurnIso (rswRectangleCenter 3 l)
      (squareVertex (-(2 * l : ℕ) : ℤ) 0)).toHom

private theorem rswCircuitTopPath_geometry
    (l : ℕ) (hl : 1 ≤ l) {omega : EdgeConfiguration 2}
    (T0 : OpenSquareRectangleCrossing (6 * l) l
      (cubicGraphIsoConfigurationPullback
        (squareCrossingTranslateIso (rswRectangleCenter 3 l)
          (squareVertex 0 (2 * l : ℕ))) omega))
    (hfree : walkEdgeFinset T0.walk ⊆ squareBoundaryFreeRectangleEdges (6 * l) l) :
    ∀ z ∈ (rswCircuitTopPath l T0).support,
      (-(3 * l : ℕ) : ℤ) ≤ z 0 ∧ z 0 ≤ 3 * l ∧
        l ≤ z 1 ∧ z 1 ≤ 3 * l ∧
        l < cubicLInfDist cubicOrigin z := by
  intro z hz
  simp only [rswCircuitTopPath, SimpleGraph.Walk.support_map, List.mem_map] at hz
  rcases hz with ⟨x, hx, rfl⟩
  have hxRaw := T0.walk.support_toPath_subset hx
  have hrect := mem_squareRectangleVertices_iff.mp (T0.support_mem_rectangle hxRaw)
  have hcoords :
      (-(3 * l : ℕ) : ℤ) ≤
          squareCrossingTranslateIso (rswRectangleCenter 3 l)
            (squareVertex 0 (2 * l : ℕ)) x 0 ∧
        squareCrossingTranslateIso (rswRectangleCenter 3 l)
            (squareVertex 0 (2 * l : ℕ)) x 0 ≤ 3 * l ∧
        l ≤ squareCrossingTranslateIso (rswRectangleCenter 3 l)
            (squareVertex 0 (2 * l : ℕ)) x 1 ∧
        squareCrossingTranslateIso (rswRectangleCenter 3 l)
            (squareVertex 0 (2 * l : ℕ)) x 1 ≤ 3 * l := by
    simp [squareCrossingTranslateIso, rswRectangleCenter, cubicTranslationIso_apply,
      cubicTranslate, squareVertex, cubicOrigin]
    omega
  refine ⟨hcoords.1, hcoords.2.1, hcoords.2.2.1, hcoords.2.2.2, ?_⟩
  by_contra hnot
  have hle : cubicLInfDist cubicOrigin
      (squareCrossingTranslateIso (rswRectangleCenter 3 l)
        (squareVertex 0 (2 * l : ℕ)) x) ≤ l := Nat.le_of_not_gt hnot
  have hbox := mem_cubicMetricBox_iff_lInfDist_le.mpr hle
  have hxBox := mem_cubicMetricBox.mp hbox (0 : Fin 2)
  have hyBox := mem_cubicMetricBox.mp hbox (1 : Fin 2)
  simp [squareCrossingTranslateIso, rswRectangleCenter, cubicTranslationIso_apply,
    cubicTranslate, squareVertex, cubicOrigin] at hxBox hyBox
  by_cases hx0 : x 0 = 0
  · omega
  by_cases hx6 : x 0 = 6 * l
  · omega
  have hinside := crossingPath_avoids_horizontal_boundary_interior
    (by omega : 0 < 6 * l) T0 hfree hx (by omega) (by omega)
  omega

private theorem rswCircuitBottomPath_geometry
    (l : ℕ) (hl : 1 ≤ l) {omega : EdgeConfiguration 2}
    (B0 : OpenSquareRectangleCrossing (6 * l) l
      (cubicGraphIsoConfigurationPullback
        (squareCrossingTranslateIso (rswRectangleCenter 3 l)
          (squareVertex 0 (-(2 * l : ℕ) : ℤ))) omega))
    (hfree : walkEdgeFinset B0.walk ⊆ squareBoundaryFreeRectangleEdges (6 * l) l) :
    ∀ z ∈ (rswCircuitBottomPath l B0).support,
      (-(3 * l : ℕ) : ℤ) ≤ z 0 ∧ z 0 ≤ 3 * l ∧
        (-(3 * l : ℕ) : ℤ) ≤ z 1 ∧ z 1 ≤ -(l : ℤ) ∧
        l < cubicLInfDist cubicOrigin z := by
  intro z hz
  simp only [rswCircuitBottomPath, SimpleGraph.Walk.support_map, List.mem_map] at hz
  rcases hz with ⟨x, hx, rfl⟩
  have hxRaw := B0.walk.support_toPath_subset hx
  have hrect := mem_squareRectangleVertices_iff.mp (B0.support_mem_rectangle hxRaw)
  have hcoords :
      (-(3 * l : ℕ) : ℤ) ≤
          squareCrossingTranslateIso (rswRectangleCenter 3 l)
            (squareVertex 0 (-(2 * l : ℕ) : ℤ)) x 0 ∧
        squareCrossingTranslateIso (rswRectangleCenter 3 l)
            (squareVertex 0 (-(2 * l : ℕ) : ℤ)) x 0 ≤ 3 * l ∧
        (-(3 * l : ℕ) : ℤ) ≤
          squareCrossingTranslateIso (rswRectangleCenter 3 l)
            (squareVertex 0 (-(2 * l : ℕ) : ℤ)) x 1 ∧
        squareCrossingTranslateIso (rswRectangleCenter 3 l)
            (squareVertex 0 (-(2 * l : ℕ) : ℤ)) x 1 ≤ -(l : ℤ) := by
    simp [squareCrossingTranslateIso, rswRectangleCenter, cubicTranslationIso_apply,
      cubicTranslate, squareVertex]
    omega
  refine ⟨hcoords.1, hcoords.2.1, hcoords.2.2.1, hcoords.2.2.2, ?_⟩
  by_contra hnot
  have hle : cubicLInfDist cubicOrigin
      (squareCrossingTranslateIso (rswRectangleCenter 3 l)
        (squareVertex 0 (-(2 * l : ℕ) : ℤ)) x) ≤ l := Nat.le_of_not_gt hnot
  have hbox := mem_cubicMetricBox_iff_lInfDist_le.mpr hle
  have hxBox := mem_cubicMetricBox.mp hbox (0 : Fin 2)
  have hyBox := mem_cubicMetricBox.mp hbox (1 : Fin 2)
  simp [squareCrossingTranslateIso, rswRectangleCenter, cubicTranslationIso_apply,
    cubicTranslate, squareVertex, cubicOrigin] at hxBox hyBox
  by_cases hx0 : x 0 = 0
  · omega
  by_cases hx6 : x 0 = 6 * l
  · omega
  have hinside := crossingPath_avoids_horizontal_boundary_interior
    (by omega : 0 < 6 * l) B0 hfree hx (by omega) (by omega)
  omega

private theorem rswCircuitRightPath_geometry
    (l : ℕ) (hl : 1 ≤ l) {omega : EdgeConfiguration 2}
    (R0 : OpenSquareRectangleCrossing (6 * l) l
      (cubicGraphIsoConfigurationPullback
        (squareCrossingQuarterTurnIso (rswRectangleCenter 3 l)
          (squareVertex (2 * l : ℕ) 0)) omega))
    (hfree : walkEdgeFinset R0.walk ⊆ squareBoundaryFreeRectangleEdges (6 * l) l) :
    ∀ z ∈ (rswCircuitRightPath l R0).support,
      l ≤ z 0 ∧ z 0 ≤ 3 * l ∧
        (-(3 * l : ℕ) : ℤ) ≤ z 1 ∧ z 1 ≤ 3 * l ∧
        l < cubicLInfDist cubicOrigin z := by
  intro z hz
  simp only [rswCircuitRightPath, SimpleGraph.Walk.support_map, List.mem_map] at hz
  rcases hz with ⟨x, hx, rfl⟩
  have hxRaw := R0.walk.support_toPath_subset hx
  have hrect := mem_squareRectangleVertices_iff.mp (R0.support_mem_rectangle hxRaw)
  have hcoords :
      l ≤ squareCrossingQuarterTurnIso (rswRectangleCenter 3 l)
          (squareVertex (2 * l : ℕ) 0) x 0 ∧
        squareCrossingQuarterTurnIso (rswRectangleCenter 3 l)
            (squareVertex (2 * l : ℕ) 0) x 0 ≤ 3 * l ∧
        (-(3 * l : ℕ) : ℤ) ≤
          squareCrossingQuarterTurnIso (rswRectangleCenter 3 l)
            (squareVertex (2 * l : ℕ) 0) x 1 ∧
        squareCrossingQuarterTurnIso (rswRectangleCenter 3 l)
            (squareVertex (2 * l : ℕ) 0) x 1 ≤ 3 * l := by
    simp [squareCrossingQuarterTurnIso, rswRectangleCenter, squareCoordinateSwap,
      cubicTranslationIso_apply, cubicTranslate, cubicCoordinatePermutationIso,
      cubicCoordinatePermutationEquiv, squareVertex, cubicOrigin]
    omega
  refine ⟨hcoords.1, hcoords.2.1, hcoords.2.2.1, hcoords.2.2.2, ?_⟩
  by_contra hnot
  have hle : cubicLInfDist cubicOrigin
      (squareCrossingQuarterTurnIso (rswRectangleCenter 3 l)
        (squareVertex (2 * l : ℕ) 0) x) ≤ l := Nat.le_of_not_gt hnot
  have hbox := mem_cubicMetricBox_iff_lInfDist_le.mpr hle
  have hxBox := mem_cubicMetricBox.mp hbox (0 : Fin 2)
  have hyBox := mem_cubicMetricBox.mp hbox (1 : Fin 2)
  simp [squareCrossingQuarterTurnIso, rswRectangleCenter, squareCoordinateSwap,
    cubicTranslationIso_apply, cubicTranslate, cubicCoordinatePermutationIso,
    cubicCoordinatePermutationEquiv, squareVertex, cubicOrigin] at hxBox hyBox
  by_cases hx0 : x 0 = 0
  · omega
  by_cases hx6 : x 0 = 6 * l
  · omega
  have hinside := crossingPath_avoids_horizontal_boundary_interior
    (by omega : 0 < 6 * l) R0 hfree hx (by omega) (by omega)
  omega

private theorem rswCircuitLeftPath_geometry
    (l : ℕ) (hl : 1 ≤ l) {omega : EdgeConfiguration 2}
    (L0 : OpenSquareRectangleCrossing (6 * l) l
      (cubicGraphIsoConfigurationPullback
        (squareCrossingQuarterTurnIso (rswRectangleCenter 3 l)
          (squareVertex (-(2 * l : ℕ) : ℤ) 0)) omega))
    (hfree : walkEdgeFinset L0.walk ⊆ squareBoundaryFreeRectangleEdges (6 * l) l) :
    ∀ z ∈ (rswCircuitLeftPath l L0).support,
      (-(3 * l : ℕ) : ℤ) ≤ z 0 ∧ z 0 ≤ -(l : ℤ) ∧
        (-(3 * l : ℕ) : ℤ) ≤ z 1 ∧ z 1 ≤ 3 * l ∧
        l < cubicLInfDist cubicOrigin z := by
  intro z hz
  simp only [rswCircuitLeftPath, SimpleGraph.Walk.support_map, List.mem_map] at hz
  rcases hz with ⟨x, hx, rfl⟩
  have hxRaw := L0.walk.support_toPath_subset hx
  have hrect := mem_squareRectangleVertices_iff.mp (L0.support_mem_rectangle hxRaw)
  have hcoords :
      (-(3 * l : ℕ) : ℤ) ≤
          squareCrossingQuarterTurnIso (rswRectangleCenter 3 l)
            (squareVertex (-(2 * l : ℕ) : ℤ) 0) x 0 ∧
        squareCrossingQuarterTurnIso (rswRectangleCenter 3 l)
            (squareVertex (-(2 * l : ℕ) : ℤ) 0) x 0 ≤ -(l : ℤ) ∧
        (-(3 * l : ℕ) : ℤ) ≤
          squareCrossingQuarterTurnIso (rswRectangleCenter 3 l)
            (squareVertex (-(2 * l : ℕ) : ℤ) 0) x 1 ∧
        squareCrossingQuarterTurnIso (rswRectangleCenter 3 l)
            (squareVertex (-(2 * l : ℕ) : ℤ) 0) x 1 ≤ 3 * l := by
    simp [squareCrossingQuarterTurnIso, rswRectangleCenter, squareCoordinateSwap,
      cubicTranslationIso_apply, cubicTranslate, cubicCoordinatePermutationIso,
      cubicCoordinatePermutationEquiv, squareVertex, cubicOrigin]
    omega
  refine ⟨hcoords.1, hcoords.2.1, hcoords.2.2.1, hcoords.2.2.2, ?_⟩
  by_contra hnot
  have hle : cubicLInfDist cubicOrigin
      (squareCrossingQuarterTurnIso (rswRectangleCenter 3 l)
        (squareVertex (-(2 * l : ℕ) : ℤ) 0) x) ≤ l := Nat.le_of_not_gt hnot
  have hbox := mem_cubicMetricBox_iff_lInfDist_le.mpr hle
  have hxBox := mem_cubicMetricBox.mp hbox (0 : Fin 2)
  have hyBox := mem_cubicMetricBox.mp hbox (1 : Fin 2)
  simp [squareCrossingQuarterTurnIso, rswRectangleCenter, squareCoordinateSwap,
    cubicTranslationIso_apply, cubicTranslate, cubicCoordinatePermutationIso,
    cubicCoordinatePermutationEquiv, squareVertex, cubicOrigin] at hxBox hyBox
  by_cases hx0 : x 0 = 0
  · omega
  by_cases hx6 : x 0 = 6 * l
  · omega
  have hinside := crossingPath_avoids_horizontal_boundary_interior
    (by omega : 0 < 6 * l) L0 hfree hx (by omega) (by omega)
  omega

private theorem rswCircuit_pairwise_intersections
    (l : ℕ) {omega : EdgeConfiguration 2}
    (T0 : OpenSquareRectangleCrossing (6 * l) l
      (cubicGraphIsoConfigurationPullback
        (squareCrossingTranslateIso (rswRectangleCenter 3 l)
          (squareVertex 0 (2 * l : ℕ))) omega))
    (B0 : OpenSquareRectangleCrossing (6 * l) l
      (cubicGraphIsoConfigurationPullback
        (squareCrossingTranslateIso (rswRectangleCenter 3 l)
          (squareVertex 0 (-(2 * l : ℕ) : ℤ))) omega))
    (R0 : OpenSquareRectangleCrossing (6 * l) l
      (cubicGraphIsoConfigurationPullback
        (squareCrossingQuarterTurnIso (rswRectangleCenter 3 l)
          (squareVertex (2 * l : ℕ) 0)) omega))
    (L0 : OpenSquareRectangleCrossing (6 * l) l
      (cubicGraphIsoConfigurationPullback
        (squareCrossingQuarterTurnIso (rswRectangleCenter 3 l)
          (squareVertex (-(2 * l : ℕ) : ℤ) 0)) omega)) :
    ∃ zTR zBR zBL zTL : SquareVertex,
      zTR ∈ (rswCircuitTopPath l T0).support ∧
      zTR ∈ (rswCircuitRightPath l R0).support ∧
      zBR ∈ (rswCircuitBottomPath l B0).support ∧
      zBR ∈ (rswCircuitRightPath l R0).support ∧
      zBL ∈ (rswCircuitBottomPath l B0).support ∧
      zBL ∈ (rswCircuitLeftPath l L0).support ∧
      zTL ∈ (rswCircuitTopPath l T0).support ∧
      zTL ∈ (rswCircuitLeftPath l L0).support := by
  let TN : squareGraph.Walk (squareVertex 0 (T0.start 1 + 5 * l))
      (squareVertex (6 * l : ℕ) (T0.finish 1 + 5 * l)) :=
    ((T0.walk.toPath : squareGraph.Walk T0.start T0.finish).map
      (rswCircuitTopNormalizeIso l).toHom).copy (by
        ext i
        fin_cases i
        · simpa using (mem_squareRectangleLeft_iff.mp T0.start_mem).1
        · simp [squareVertex]) (by
        ext i
        fin_cases i
        · simpa using (mem_squareRectangleRight_iff.mp T0.finish_mem).1
        · simp [squareVertex])
  let BN : squareGraph.Walk (squareVertex 0 (B0.start 1 + l))
      (squareVertex (6 * l : ℕ) (B0.finish 1 + l)) :=
    ((B0.walk.toPath : squareGraph.Walk B0.start B0.finish).map
      (rswCircuitBottomNormalizeIso l).toHom).copy (by
        ext i
        fin_cases i
        · simpa using (mem_squareRectangleLeft_iff.mp B0.start_mem).1
        · simp [squareVertex]) (by
        ext i
        fin_cases i
        · simpa using (mem_squareRectangleRight_iff.mp B0.finish_mem).1
        · simp [squareVertex])
  let RN : squareGraph.Walk (squareVertex (R0.start 1 + 5 * l) 0)
      (squareVertex (R0.finish 1 + 5 * l) (6 * l : ℕ)) :=
    ((R0.walk.toPath : squareGraph.Walk R0.start R0.finish).map
      (rswCircuitRightNormalizeIso l).toHom).copy (by
        ext i
        fin_cases i
        · simp [squareVertex]
        · simpa using (mem_squareRectangleLeft_iff.mp R0.start_mem).1) (by
        ext i
        fin_cases i
        · simp [squareVertex]
        · simpa using (mem_squareRectangleRight_iff.mp R0.finish_mem).1)
  let LN : squareGraph.Walk (squareVertex (L0.start 1 + l) 0)
      (squareVertex (L0.finish 1 + l) (6 * l : ℕ)) :=
    ((L0.walk.toPath : squareGraph.Walk L0.start L0.finish).map
      (rswCircuitLeftNormalizeIso l).toHom).copy (by
        ext i
        fin_cases i
        · simp [squareVertex]
        · simpa using (mem_squareRectangleLeft_iff.mp L0.start_mem).1) (by
        ext i
        fin_cases i
        · simp [squareVertex]
        · simpa using (mem_squareRectangleRight_iff.mp L0.finish_mem).1)
  have hTN : ∀ z ∈ TN.support,
      0 ≤ z 0 ∧ z 0 ≤ 6 * l ∧ 0 ≤ z 1 ∧ z 1 ≤ 6 * l := by
    intro z hz
    simp only [TN, SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map,
      List.mem_map] at hz
    rcases hz with ⟨x, hx, rfl⟩
    have hx' := T0.walk.support_toPath_subset hx
    have h := mem_squareRectangleVertices_iff.mp (T0.support_mem_rectangle hx')
    simp
    omega
  have hBN : ∀ z ∈ BN.support,
      0 ≤ z 0 ∧ z 0 ≤ 6 * l ∧ 0 ≤ z 1 ∧ z 1 ≤ 6 * l := by
    intro z hz
    simp only [BN, SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map,
      List.mem_map] at hz
    rcases hz with ⟨x, hx, rfl⟩
    have hx' := B0.walk.support_toPath_subset hx
    have h := mem_squareRectangleVertices_iff.mp (B0.support_mem_rectangle hx')
    simp
    omega
  have hRN : ∀ z ∈ RN.support,
      0 ≤ z 0 ∧ z 0 ≤ 6 * l ∧ 0 ≤ z 1 ∧ z 1 ≤ 6 * l := by
    intro z hz
    simp only [RN, SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map,
      List.mem_map] at hz
    rcases hz with ⟨x, hx, rfl⟩
    have hx' := R0.walk.support_toPath_subset hx
    have h := mem_squareRectangleVertices_iff.mp (R0.support_mem_rectangle hx')
    simp
    omega
  have hLN : ∀ z ∈ LN.support,
      0 ≤ z 0 ∧ z 0 ≤ 6 * l ∧ 0 ≤ z 1 ∧ z 1 ≤ 6 * l := by
    intro z hz
    simp only [LN, SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map,
      List.mem_map] at hz
    rcases hz with ⟨x, hx, rfl⟩
    have hx' := L0.walk.support_toPath_subset hx
    have h := mem_squareRectangleVertices_iff.mp (L0.support_mem_rectangle hx')
    simp
    omega
  obtain ⟨zTRn, hzTRTn, hzTRRn⟩ :=
    squareWalk_support_inter_of_left_right_and_bottom_top_of_le_int
      (by omega : 6 * l ≤ 6 * l)
      (by have := (mem_squareRectangleLeft_iff.mp T0.start_mem).2.1; omega)
      (by have := (mem_squareRectangleLeft_iff.mp T0.start_mem).2.2; omega)
      (by have := (mem_squareRectangleRight_iff.mp T0.finish_mem).2.1; omega)
      (by have := (mem_squareRectangleRight_iff.mp T0.finish_mem).2.2; omega)
      (by have := (mem_squareRectangleLeft_iff.mp R0.start_mem).2.1; omega)
      (by have := (mem_squareRectangleLeft_iff.mp R0.start_mem).2.2; omega)
      (by have := (mem_squareRectangleRight_iff.mp R0.finish_mem).2.1; omega)
      (by have := (mem_squareRectangleRight_iff.mp R0.finish_mem).2.2; omega)
      TN RN hTN hRN
  have hTRmap : ∃ z,
      z ∈ ((rswCircuitTopPath l T0).map (rswCircuitFrameIso l).toHom).support ∧
      z ∈ ((rswCircuitRightPath l R0).map (rswCircuitFrameIso l).toHom).support := by
    refine ⟨zTRn, ?_, ?_⟩
    · simpa [TN, rswCircuitTopPath, rswCircuitTopNormalizeIso,
        SimpleGraph.Walk.map_map] using hzTRTn
    · simpa [RN, rswCircuitRightPath, rswCircuitRightNormalizeIso,
        SimpleGraph.Walk.map_map] using hzTRRn
  obtain ⟨zTR, hzTRT, hzTRR⟩ := walk_support_inter_of_map_support_inter
    (rswCircuitFrameIso l).toHom (rswCircuitFrameIso l).injective
      (rswCircuitTopPath l T0) (rswCircuitRightPath l R0) hTRmap
  obtain ⟨zBRn, hzBRBn, hzBRRn⟩ :=
    squareWalk_support_inter_of_left_right_and_bottom_top_of_le_int
      (by omega : 6 * l ≤ 6 * l)
      (by have := (mem_squareRectangleLeft_iff.mp B0.start_mem).2.1; omega)
      (by have := (mem_squareRectangleLeft_iff.mp B0.start_mem).2.2; omega)
      (by have := (mem_squareRectangleRight_iff.mp B0.finish_mem).2.1; omega)
      (by have := (mem_squareRectangleRight_iff.mp B0.finish_mem).2.2; omega)
      (by have := (mem_squareRectangleLeft_iff.mp R0.start_mem).2.1; omega)
      (by have := (mem_squareRectangleLeft_iff.mp R0.start_mem).2.2; omega)
      (by have := (mem_squareRectangleRight_iff.mp R0.finish_mem).2.1; omega)
      (by have := (mem_squareRectangleRight_iff.mp R0.finish_mem).2.2; omega)
      BN RN hBN hRN
  have hBRmap : ∃ z,
      z ∈ ((rswCircuitBottomPath l B0).map (rswCircuitFrameIso l).toHom).support ∧
      z ∈ ((rswCircuitRightPath l R0).map (rswCircuitFrameIso l).toHom).support := by
    refine ⟨zBRn, ?_, ?_⟩
    · simpa [BN, rswCircuitBottomPath, rswCircuitBottomNormalizeIso,
        SimpleGraph.Walk.map_map] using hzBRBn
    · simpa [RN, rswCircuitRightPath, rswCircuitRightNormalizeIso,
        SimpleGraph.Walk.map_map] using hzBRRn
  obtain ⟨zBR, hzBRB, hzBRR⟩ := walk_support_inter_of_map_support_inter
    (rswCircuitFrameIso l).toHom (rswCircuitFrameIso l).injective
      (rswCircuitBottomPath l B0) (rswCircuitRightPath l R0) hBRmap
  obtain ⟨zBLn, hzBLBn, hzBLLn⟩ :=
    squareWalk_support_inter_of_left_right_and_bottom_top_of_le_int
      (by omega : 6 * l ≤ 6 * l)
      (by have := (mem_squareRectangleLeft_iff.mp B0.start_mem).2.1; omega)
      (by have := (mem_squareRectangleLeft_iff.mp B0.start_mem).2.2; omega)
      (by have := (mem_squareRectangleRight_iff.mp B0.finish_mem).2.1; omega)
      (by have := (mem_squareRectangleRight_iff.mp B0.finish_mem).2.2; omega)
      (by have := (mem_squareRectangleLeft_iff.mp L0.start_mem).2.1; omega)
      (by have := (mem_squareRectangleLeft_iff.mp L0.start_mem).2.2; omega)
      (by have := (mem_squareRectangleRight_iff.mp L0.finish_mem).2.1; omega)
      (by have := (mem_squareRectangleRight_iff.mp L0.finish_mem).2.2; omega)
      BN LN hBN hLN
  have hBLmap : ∃ z,
      z ∈ ((rswCircuitBottomPath l B0).map (rswCircuitFrameIso l).toHom).support ∧
      z ∈ ((rswCircuitLeftPath l L0).map (rswCircuitFrameIso l).toHom).support := by
    refine ⟨zBLn, ?_, ?_⟩
    · simpa [BN, rswCircuitBottomPath, rswCircuitBottomNormalizeIso,
        SimpleGraph.Walk.map_map] using hzBLBn
    · simpa [LN, rswCircuitLeftPath, rswCircuitLeftNormalizeIso,
        SimpleGraph.Walk.map_map] using hzBLLn
  obtain ⟨zBL, hzBLB, hzBLL⟩ := walk_support_inter_of_map_support_inter
    (rswCircuitFrameIso l).toHom (rswCircuitFrameIso l).injective
      (rswCircuitBottomPath l B0) (rswCircuitLeftPath l L0) hBLmap
  obtain ⟨zTLn, hzTLTn, hzTLLn⟩ :=
    squareWalk_support_inter_of_left_right_and_bottom_top_of_le_int
      (by omega : 6 * l ≤ 6 * l)
      (by have := (mem_squareRectangleLeft_iff.mp T0.start_mem).2.1; omega)
      (by have := (mem_squareRectangleLeft_iff.mp T0.start_mem).2.2; omega)
      (by have := (mem_squareRectangleRight_iff.mp T0.finish_mem).2.1; omega)
      (by have := (mem_squareRectangleRight_iff.mp T0.finish_mem).2.2; omega)
      (by have := (mem_squareRectangleLeft_iff.mp L0.start_mem).2.1; omega)
      (by have := (mem_squareRectangleLeft_iff.mp L0.start_mem).2.2; omega)
      (by have := (mem_squareRectangleRight_iff.mp L0.finish_mem).2.1; omega)
      (by have := (mem_squareRectangleRight_iff.mp L0.finish_mem).2.2; omega)
      TN LN hTN hLN
  have hTLmap : ∃ z,
      z ∈ ((rswCircuitTopPath l T0).map (rswCircuitFrameIso l).toHom).support ∧
      z ∈ ((rswCircuitLeftPath l L0).map (rswCircuitFrameIso l).toHom).support := by
    refine ⟨zTLn, ?_, ?_⟩
    · simpa [TN, rswCircuitTopPath, rswCircuitTopNormalizeIso,
        SimpleGraph.Walk.map_map] using hzTLTn
    · simpa [LN, rswCircuitLeftPath, rswCircuitLeftNormalizeIso,
        SimpleGraph.Walk.map_map] using hzTLLn
  obtain ⟨zTL, hzTLT, hzTLL⟩ := walk_support_inter_of_map_support_inter
    (rswCircuitFrameIso l).toHom (rswCircuitFrameIso l).injective
      (rswCircuitTopPath l T0) (rswCircuitLeftPath l L0) hTLmap
  exact ⟨zTR, zBR, zBL, zTL, hzTRT, hzTRR, hzBRB, hzBRR,
    hzBLB, hzBLL, hzTLT, hzTLL⟩

private theorem cubicLInfDist_origin_le_of_square_bounds {n : ℕ} {z : SquareVertex}
    (hxLower : -(n : ℤ) ≤ z 0) (hxUpper : z 0 ≤ n)
    (hyLower : -(n : ℤ) ≤ z 1) (hyUpper : z 1 ≤ n) :
    cubicLInfDist cubicOrigin z ≤ n := by
  apply mem_cubicMetricBox_iff_lInfDist_le.mp
  rw [mem_cubicMetricBox]
  intro i
  fin_cases i
  · simpa [cubicOrigin] using And.intro hxLower hxUpper
  · simpa [cubicOrigin] using And.intro hyLower hyUpper

/-- The four boundary-free crossings in Grimmett's Figure 11.27 contain an open simple circuit
in `B(3l) \ B(l)` with odd face index about the origin. -/
theorem rswCircuitGluingIntersection_subset (l : ℕ) (hl : 1 ≤ l) :
    rswCircuitGluingIntersection l ⊆ rswAnnulusOpenCircuitEvent l := by
  intro omega homega
  rcases homega with ⟨⟨⟨hT, hR⟩, hB⟩, hL⟩
  have hT' : cubicGraphIsoConfigurationPullback
      (squareCrossingTranslateIso (rswRectangleCenter 3 l)
        (squareVertex 0 (2 * l : ℕ))) omega ∈
        squareBoundaryFreeRectangleCrossingEvent (6 * l) l := by
    simpa [rswCircuitTopEvent, rswHorizontalPlacementEvent, cubicGraphIsoEvent,
      rswRectangleCrossingEvent, Nat.mul_assoc] using hT
  have hB' : cubicGraphIsoConfigurationPullback
      (squareCrossingTranslateIso (rswRectangleCenter 3 l)
        (squareVertex 0 (-(2 * l : ℕ) : ℤ))) omega ∈
        squareBoundaryFreeRectangleCrossingEvent (6 * l) l := by
    simpa [rswCircuitBottomEvent, rswHorizontalPlacementEvent, cubicGraphIsoEvent,
      rswRectangleCrossingEvent, Nat.mul_assoc] using hB
  have hR' : cubicGraphIsoConfigurationPullback
      (squareCrossingQuarterTurnIso (rswRectangleCenter 3 l)
        (squareVertex (2 * l : ℕ) 0)) omega ∈
        squareBoundaryFreeRectangleCrossingEvent (6 * l) l := by
    simpa [rswCircuitRightEvent, rswVerticalPlacementEvent, cubicGraphIsoEvent,
      rswRectangleCrossingEvent, Nat.mul_assoc] using hR
  have hL' : cubicGraphIsoConfigurationPullback
      (squareCrossingQuarterTurnIso (rswRectangleCenter 3 l)
        (squareVertex (-(2 * l : ℕ) : ℤ) 0)) omega ∈
        squareBoundaryFreeRectangleCrossingEvent (6 * l) l := by
    simpa [rswCircuitLeftEvent, rswVerticalPlacementEvent, cubicGraphIsoEvent,
      rswRectangleCrossingEvent, Nat.mul_assoc] using hL
  obtain ⟨T0, hTfree⟩ := exists_openSquareRectangleCrossing_of_mem_boundaryFree hT'
  obtain ⟨B0, hBfree⟩ := exists_openSquareRectangleCrossing_of_mem_boundaryFree hB'
  obtain ⟨R0, hRfree⟩ := exists_openSquareRectangleCrossing_of_mem_boundaryFree hR'
  obtain ⟨L0, hLfree⟩ := exists_openSquareRectangleCrossing_of_mem_boundaryFree hL'
  obtain ⟨zTR, zBR, zBL, zTL, hzTRT, hzTRR, hzBRB, hzBRR,
      hzBLB, hzBLL, hzTLT, hzTLL⟩ :=
    rswCircuit_pairwise_intersections l T0 B0 R0 L0
  let T := rswCircuitTopPath l T0
  let B := rswCircuitBottomPath l B0
  let R := rswCircuitRightPath l R0
  let L := rswCircuitLeftPath l L0
  let tSeg := squareWalkBetweenViaStart T hzTLT hzTRT
  let rSeg := squareWalkBetweenViaStart R hzTRR hzBRR
  let bSeg := squareWalkBetweenViaStart B hzBRB hzBLB
  let lSeg := squareWalkBetweenViaStart L hzBLL hzTLL
  let W := tSeg.append (rSeg.append (bSeg.append lSeg))
  have hTgeometry : ∀ z ∈ T.support,
      (-(3 * l : ℕ) : ℤ) ≤ z 0 ∧ z 0 ≤ 3 * l ∧
        l ≤ z 1 ∧ z 1 ≤ 3 * l ∧
        l < cubicLInfDist cubicOrigin z := by
    simpa [T] using rswCircuitTopPath_geometry l hl T0 hTfree
  have hBgeometry : ∀ z ∈ B.support,
      (-(3 * l : ℕ) : ℤ) ≤ z 0 ∧ z 0 ≤ 3 * l ∧
        (-(3 * l : ℕ) : ℤ) ≤ z 1 ∧ z 1 ≤ -(l : ℤ) ∧
        l < cubicLInfDist cubicOrigin z := by
    simpa [B] using rswCircuitBottomPath_geometry l hl B0 hBfree
  have hRgeometry : ∀ z ∈ R.support,
      l ≤ z 0 ∧ z 0 ≤ 3 * l ∧
        (-(3 * l : ℕ) : ℤ) ≤ z 1 ∧ z 1 ≤ 3 * l ∧
        l < cubicLInfDist cubicOrigin z := by
    simpa [R] using rswCircuitRightPath_geometry l hl R0 hRfree
  have hLgeometry : ∀ z ∈ L.support,
      (-(3 * l : ℕ) : ℤ) ≤ z 0 ∧ z 0 ≤ -(l : ℤ) ∧
        (-(3 * l : ℕ) : ℤ) ≤ z 1 ∧ z 1 ≤ 3 * l ∧
        l < cubicLInfDist cubicOrigin z := by
    simpa [L] using rswCircuitLeftPath_geometry l hl L0 hLfree
  have hopenT : walkIsOpen omega T := by
    simpa [T, rswCircuitTopPath] using walkIsOpen_map_cubicGraphIso (ω := omega)
      (squareCrossingTranslateIso (rswRectangleCenter 3 l)
        (squareVertex 0 (2 * l : ℕ)))
      (T0.walk.toPath : squareGraph.Walk T0.start T0.finish)
      (walkIsOpen_toPath T0.walk T0.isOpen)
  have hopenB : walkIsOpen omega B := by
    simpa [B, rswCircuitBottomPath] using walkIsOpen_map_cubicGraphIso (ω := omega)
      (squareCrossingTranslateIso (rswRectangleCenter 3 l)
        (squareVertex 0 (-(2 * l : ℕ) : ℤ)))
      (B0.walk.toPath : squareGraph.Walk B0.start B0.finish)
      (walkIsOpen_toPath B0.walk B0.isOpen)
  have hopenR : walkIsOpen omega R := by
    simpa [R, rswCircuitRightPath] using walkIsOpen_map_cubicGraphIso (ω := omega)
      (squareCrossingQuarterTurnIso (rswRectangleCenter 3 l)
        (squareVertex (2 * l : ℕ) 0))
      (R0.walk.toPath : squareGraph.Walk R0.start R0.finish)
      (walkIsOpen_toPath R0.walk R0.isOpen)
  have hopenL : walkIsOpen omega L := by
    simpa [L, rswCircuitLeftPath] using walkIsOpen_map_cubicGraphIso (ω := omega)
      (squareCrossingQuarterTurnIso (rswRectangleCenter 3 l)
        (squareVertex (-(2 * l : ℕ) : ℤ) 0))
      (L0.walk.toPath : squareGraph.Walk L0.start L0.finish)
      (walkIsOpen_toPath L0.walk L0.isOpen)
  have hopenTSeg : walkIsOpen omega tSeg := walkIsOpen_of_edges_subset hopenT
    (squareWalkBetweenViaStart_edges_subset T hzTLT hzTRT)
  have hopenRSeg : walkIsOpen omega rSeg := walkIsOpen_of_edges_subset hopenR
    (squareWalkBetweenViaStart_edges_subset R hzTRR hzBRR)
  have hopenBSeg : walkIsOpen omega bSeg := walkIsOpen_of_edges_subset hopenB
    (squareWalkBetweenViaStart_edges_subset B hzBRB hzBLB)
  have hopenLSeg : walkIsOpen omega lSeg := walkIsOpen_of_edges_subset hopenL
    (squareWalkBetweenViaStart_edges_subset L hzBLL hzTLL)
  have hopenW : walkIsOpen omega W := by
    exact walkIsOpen_append hopenTSeg
      (walkIsOpen_append hopenRSeg (walkIsOpen_append hopenBSeg hopenLSeg))
  have hWgeometry : ∀ z ∈ W.support,
      l < cubicLInfDist cubicOrigin z ∧ cubicLInfDist cubicOrigin z ≤ 3 * l := by
    intro z hz
    simp only [W, SimpleGraph.Walk.mem_support_append_iff] at hz
    rcases hz with hz | hz | hz | hz
    · have hzt := squareWalkBetweenViaStart_support_subset T hzTLT hzTRT hz
      have hg := hTgeometry z hzt
      exact ⟨hg.2.2.2.2, cubicLInfDist_origin_le_of_square_bounds
        hg.1 hg.2.1 (by omega) hg.2.2.2.1⟩
    · have hzr := squareWalkBetweenViaStart_support_subset R hzTRR hzBRR hz
      have hg := hRgeometry z hzr
      exact ⟨hg.2.2.2.2, cubicLInfDist_origin_le_of_square_bounds
        (by omega) hg.2.1 hg.2.2.1 hg.2.2.2.1⟩
    · have hzb := squareWalkBetweenViaStart_support_subset B hzBRB hzBLB hz
      have hg := hBgeometry z hzb
      exact ⟨hg.2.2.2.2, cubicLInfDist_origin_le_of_square_bounds
        hg.1 hg.2.1 hg.2.2.1 (by omega)⟩
    · have hzl := squareWalkBetweenViaStart_support_subset L hzBLL hzTLL hz
      have hg := hLgeometry z hzl
      exact ⟨hg.2.2.2.2, cubicLInfDist_origin_le_of_square_bounds
        hg.1 (by omega) hg.2.2.1 hg.2.2.2.1⟩
  have htPos : ∀ z ∈ tSeg.support, 0 < z 1 := by
    intro z hz
    have hg := hTgeometry z (squareWalkBetweenViaStart_support_subset T hzTLT hzTRT hz)
    omega
  have hbNeg : ∀ z ∈ bSeg.support, z 1 < 0 := by
    intro z hz
    have hg := hBgeometry z (squareWalkBetweenViaStart_support_subset B hzBRB hzBLB hz)
    omega
  have hlNeg : ∀ z ∈ lSeg.support, z 0 < 0 := by
    intro z hz
    have hg := hLgeometry z (squareWalkBetweenViaStart_support_subset L hzBLL hzTLL hz)
    omega
  have hrPos : ∀ z ∈ rSeg.support, 0 < z 0 := by
    intro z hz
    have hg := hRgeometry z (squareWalkBetweenViaStart_support_subset R hzTRR hzBRR hz)
    omega
  have hzTRPos : 0 < zTR 1 := by
    have hg := hTgeometry zTR hzTRT
    omega
  have hzBRNeg : zBR 1 < 0 := by
    have hg := hBgeometry zBR hzBRB
    omega
  have htZero := horizontalRayCount_eq_zero_of_support_above tSeg htPos
  have hbZero := horizontalRayCount_eq_zero_of_support_below bSeg hbNeg
  have hlZero := horizontalRayCount_eq_zero_of_support_left lSeg hlNeg
  have hrOdd := odd_horizontalRayCount_of_support_right rSeg hrPos hzTRPos hzBRNeg
  have hWOdd : Odd
      (W.edges.countP (squareEdgeCrossesFaceHorizontalRayBool cubicOrigin)) := by
    simpa [W, SimpleGraph.Walk.edges_append, List.countP_append, htZero, hbZero, hlZero]
      using hrOdd
  have hWParity : closedSquareWalkFaceParity W cubicOrigin = 1 := by
    unfold closedSquareWalkFaceParity
    exact Nat.odd_iff.mp hWOdd
  obtain ⟨y, c, hcCycle, hcEdges, hcSupport, hcParity⟩ :=
    exists_oddFaceParityCycle_of_closedWalk W hWParity
  refine ⟨y, c, hcCycle, walkIsOpen_of_edges_subset hopenW hcEdges, ?_, hcParity⟩
  intro z hz
  exact hWgeometry z (hcSupport hz)

end Percolation
