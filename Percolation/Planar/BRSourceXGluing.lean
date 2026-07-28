import Percolation.Planar.BRSourceXPlacements
import Percolation.Planar.RSWIncidence

/-!
# Deterministic gluing for the Bollobás--Riordan source event

Two horizontally reflected copies of `X(R)`, together with a horizontal crossing of their
common source square, join the two outer sides of the union of the doubled rectangles.  The
union is represented as a translate of the standard boundary-free rectangle
`[0, 2m - 2n] × [-2n, 2n]`.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval

noncomputable section

/-- Place the standard union rectangle at `[2n-m,m] × [-n,3n]`. -/
def brSourceUnionPlacementIso (m n : ℕ) : squareGraph ≃g squareGraph :=
  cubicTranslationIso cubicOrigin
    (squareVertex (2 * (n : ℤ) - (m : ℤ)) (n : ℤ))

@[simp]
theorem brSourceUnionPlacementIso_zero (m n : ℕ) (x : SquareVertex) :
    brSourceUnionPlacementIso m n x 0 =
      x 0 + 2 * (n : ℤ) - (m : ℤ) := by
  simp [brSourceUnionPlacementIso, cubicTranslationIso_apply, cubicTranslate,
    cubicOrigin, squareVertex]
  ring

@[simp]
theorem brSourceUnionPlacementIso_one (m n : ℕ) (x : SquareVertex) :
    brSourceUnionPlacementIso m n x 1 = x 1 + (n : ℤ) := by
  simp [brSourceUnionPlacementIso, cubicTranslationIso_apply, cubicTranslate,
    cubicOrigin, squareVertex]

@[simp]
theorem brSourceUnionPlacementIso_symm_zero (m n : ℕ) (x : SquareVertex) :
    (brSourceUnionPlacementIso m n).symm x 0 =
      x 0 - 2 * (n : ℤ) + (m : ℤ) := by
  have hsymm : (brSourceUnionPlacementIso m n).symm =
      cubicTranslationIso
        (squareVertex (2 * (n : ℤ) - (m : ℤ)) (n : ℤ)) cubicOrigin := by
    ext z
    rfl
  rw [hsymm]
  simp [cubicTranslationIso_apply, cubicTranslate, cubicOrigin, squareVertex]
  ring

@[simp]
theorem brSourceUnionPlacementIso_symm_one (m n : ℕ) (x : SquareVertex) :
    (brSourceUnionPlacementIso m n).symm x 1 = x 1 - (n : ℤ) := by
  have hsymm : (brSourceUnionPlacementIso m n).symm =
      cubicTranslationIso
        (squareVertex (2 * (n : ℤ) - (m : ℤ)) (n : ℤ)) cubicOrigin := by
    ext z
    rfl
  rw [hsymm]
  simp [cubicTranslationIso_apply, cubicTranslate, cubicOrigin, squareVertex]
  ring

/-- The boundary-free crossing event of the union rectangle, expressed as a placement of the
standard centered rectangle. -/
def brSourceUnionCrossingEvent (m n : ℕ) : Set (EdgeConfiguration 2) :=
  cubicGraphIsoEvent (brSourceUnionPlacementIso m n)
    (squareBoundaryFreeRectangleCrossingEvent (2 * m - 2 * n) (2 * n))

theorem measurableSet_brSourceUnionCrossingEvent (m n : ℕ) :
    MeasurableSet (brSourceUnionCrossingEvent m n) :=
  measurableSet_cubicGraphIsoEvent _
    (measurableSet_squareBoundaryFreeRectangleCrossingEvent _ _)

theorem isIncreasingEvent_brSourceUnionCrossingEvent (m n : ℕ) :
    IsIncreasingEvent (brSourceUnionCrossingEvent m n) :=
  isIncreasingEvent_cubicGraphIsoEvent _
    (isIncreasingEvent_squareBoundaryFreeRectangleCrossingEvent _ _)

theorem bernoulliBondMeasure_real_brSourceUnionCrossingEvent
    (p : I) (m n : ℕ) :
    (bernoulliBondMeasure 2 p).real (brSourceUnionCrossingEvent m n) =
      (bernoulliBondMeasure 2 p).real
        (squareBoundaryFreeRectangleCrossingEvent (2 * m - 2 * n) (2 * n)) :=
  bernoulliBondMeasure_real_cubicGraphIsoEvent p _
    (measurableSet_squareBoundaryFreeRectangleCrossingEvent _ _)

/-- A centered left--right walk meets a centered bottom--top walk in the same square. -/
private theorem brCenteredSquareWalk_support_inter
    {n : ℕ} {a b c d : ℤ}
    (ha : -(n : ℤ) ≤ a) (ha' : a ≤ n)
    (hb : -(n : ℤ) ≤ b) (hb' : b ≤ n)
    (hc : 0 ≤ c) (hc' : c ≤ 2 * n)
    (hd : 0 ≤ d) (hd' : d ≤ 2 * n)
    (p : squareGraph.Walk (squareVertex 0 a)
      (squareVertex (2 * (n : ℤ)) b))
    (q : squareGraph.Walk (squareVertex c (-(n : ℤ)))
      (squareVertex d (n : ℤ)))
    (hpbox : ∀ z ∈ p.support,
      0 ≤ z 0 ∧ z 0 ≤ 2 * n ∧ -(n : ℤ) ≤ z 1 ∧ z 1 ≤ n)
    (hqbox : ∀ z ∈ q.support,
      0 ≤ z 0 ∧ z 0 ≤ 2 * n ∧ -(n : ℤ) ≤ z 1 ∧ z 1 ≤ n) :
    ∃ z, z ∈ p.support ∧ z ∈ q.support := by
  let F := rswNormalizeIso n
  let p' : squareGraph.Walk (squareVertex 0 (a + n))
      (squareVertex (2 * (n : ℤ)) (b + n)) :=
    (p.map F.toHom).copy
      (by ext i; fin_cases i <;> simp [F, squareVertex])
      (by ext i; fin_cases i <;> simp [F, squareVertex])
  let q' : squareGraph.Walk (squareVertex c 0)
      (squareVertex d (2 * (n : ℤ))) :=
    (q.map F.toHom).copy
      (by ext i; fin_cases i <;> simp [F, squareVertex])
      (by
        ext i
        fin_cases i
        · simp [F, squareVertex]
        · simp [F, squareVertex]
          ring)
  have hp'box : ∀ z ∈ p'.support,
      0 ≤ z 0 ∧ z 0 ≤ 2 * n ∧ 0 ≤ z 1 ∧ z 1 ≤ 2 * n := by
    intro z hz
    simp only [p', SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map,
      List.mem_map] at hz
    rcases hz with ⟨x, hx, rfl⟩
    have h := hpbox x hx
    change 0 ≤ F x 0 ∧ F x 0 ≤ 2 * (n : ℤ) ∧
      0 ≤ F x 1 ∧ F x 1 ≤ 2 * (n : ℤ)
    simp only [F, rswNormalizeIso_zero, rswNormalizeIso_one]
    omega
  have hq'box : ∀ z ∈ q'.support,
      0 ≤ z 0 ∧ z 0 ≤ 2 * n ∧ 0 ≤ z 1 ∧ z 1 ≤ 2 * n := by
    intro z hz
    simp only [q', SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map,
      List.mem_map] at hz
    rcases hz with ⟨x, hx, rfl⟩
    have h := hqbox x hx
    change 0 ≤ F x 0 ∧ F x 0 ≤ 2 * (n : ℤ) ∧
      0 ≤ F x 1 ∧ F x 1 ≤ 2 * (n : ℤ)
    simp only [F, rswNormalizeIso_zero, rswNormalizeIso_one]
    omega
  obtain ⟨z, hzp', hzq'⟩ :=
    squareWalk_support_inter_of_left_right_and_bottom_top_of_le_int
      (m := 2 * n) (n := 2 * n) (by rfl)
      (by omega) (by omega) (by omega) (by omega)
      hc hc' hd hd' p' q' hp'box hq'box
  have hinter : ∃ z, z ∈ (p.map F.toHom).support ∧
      z ∈ (q.map F.toHom).support := by
    refine ⟨z, ?_, ?_⟩
    · simpa [p'] using hzp'
    · simpa [q'] using hzq'
  exact walk_support_inter_of_map_support_inter F.toHom F.injective p q hinter

/-- The geometric boundary of the unnormalized union rectangle
`[2n-m,m] × [-n,3n]`. -/
private def brSourceUnionBoundaryVertex (m n : ℕ) (x : SquareVertex) : Prop :=
  x 0 = 2 * (n : ℤ) - (m : ℤ) ∨ x 0 = (m : ℤ) ∨
    x 1 = -(n : ℤ) ∨ x 1 = 3 * (n : ℤ)

private theorem brSourceUnionPlacementIso_symm_mem_rectangle
    {m n : ℕ} (hm : 2 * n ≤ m) {x : SquareVertex}
    (hx : 2 * (n : ℤ) - (m : ℤ) ≤ x 0 ∧ x 0 ≤ (m : ℤ) ∧
      -(n : ℤ) ≤ x 1 ∧ x 1 ≤ 3 * (n : ℤ)) :
    (brSourceUnionPlacementIso m n).symm x ∈
      squareRectangleVertices (2 * m - 2 * n) (2 * n) := by
  have hmn : 2 * n ≤ 2 * m := by omega
  have hcast : ((2 * m - 2 * n : ℕ) : ℤ) =
      2 * (m : ℤ) - 2 * (n : ℤ) := by
    rw [Nat.cast_sub hmn]
    push_cast
    ring
  rw [mem_squareRectangleVertices_iff]
  simp only [brSourceUnionPlacementIso_symm_zero,
    brSourceUnionPlacementIso_symm_one]
  rw [hcast]
  omega

private theorem brSourceUnionPlacementIso_symm_boundary_iff
    {m n : ℕ} (hm : 2 * n ≤ m) (x : SquareVertex) :
    squareRectangleBoundaryVertex (2 * m - 2 * n) (2 * n)
        ((brSourceUnionPlacementIso m n).symm x) ↔
      brSourceUnionBoundaryVertex m n x := by
  have hmn : 2 * n ≤ 2 * m := by omega
  have hcast : ((2 * m - 2 * n : ℕ) : ℤ) =
      2 * (m : ℤ) - 2 * (n : ℤ) := by
    rw [Nat.cast_sub hmn]
    push_cast
    ring
  unfold squareRectangleBoundaryVertex brSourceUnionBoundaryVertex
  simp only [brSourceUnionPlacementIso_symm_zero,
    brSourceUnionPlacementIso_symm_one]
  rw [hcast]
  omega

private theorem brSourceUnionPlacementIso_symm_mapEdge_not_both_boundary
    {m n : ℕ} (hm : 2 * n ≤ m) {e : SquareEdge}
    (he : ¬ (brSourceUnionBoundaryVertex m n e.1.out.1 ∧
      brSourceUnionBoundaryVertex m n e.1.out.2)) :
    ¬ (squareRectangleBoundaryVertex (2 * m - 2 * n) (2 * n)
          (((brSourceUnionPlacementIso m n).symm.mapEdgeSet e).1.out.1) ∧
      squareRectangleBoundaryVertex (2 * m - 2 * n) (2 * n)
          (((brSourceUnionPlacementIso m n).symm.mapEdgeSet e).1.out.2)) := by
  intro htarget
  apply he
  have hmapped : ∀ z ∈
      ((brSourceUnionPlacementIso m n).symm.mapEdgeSet e : Sym2 SquareVertex),
      squareRectangleBoundaryVertex (2 * m - 2 * n) (2 * n) z := by
    intro z hz
    rw [← ((brSourceUnionPlacementIso m n).symm.mapEdgeSet e).1.out_eq,
      Sym2.mem_iff] at hz
    exact hz.elim (fun h ↦ h ▸ htarget.1) (fun h ↦ h ▸ htarget.2)
  have hsource : ∀ z ∈ (e : Sym2 SquareVertex),
      brSourceUnionBoundaryVertex m n z := by
    intro z hz
    rw [← brSourceUnionPlacementIso_symm_boundary_iff hm z]
    apply hmapped ((brSourceUnionPlacementIso m n).symm z)
    exact Sym2.mem_map.mpr ⟨z, hz, rfl⟩
  exact ⟨hsource e.1.out.1 (Sym2.out_fst_mem _),
    hsource e.1.out.2 (Sym2.out_snd_mem _)⟩

/-- A mapped boundary-free edge cannot acquire two endpoints on a larger target boundary when
target-boundary vertices pull back to source-boundary vertices. -/
private theorem mappedBoundaryFreeEdge_not_both_boundary
    {ms ns : ℕ} {f : SquareEdge}
    (hf : f ∈ squareBoundaryFreeRectangleEdges ms ns)
    (F : squareGraph ≃g squareGraph) (targetBoundary : SquareVertex → Prop)
    (hboundary : ∀ x, x ∈ squareRectangleVertices ms ns →
      targetBoundary (F x) → squareRectangleBoundaryVertex ms ns x) :
    ¬ (targetBoundary (F.mapEdgeSet f).1.out.1 ∧
      targetBoundary (F.mapEdgeSet f).1.out.2) := by
  rw [squareBoundaryFreeRectangleEdges, Finset.mem_filter] at hf
  intro htarget
  apply hf.2
  have hmapped : ∀ z ∈ (F.mapEdgeSet f : Sym2 SquareVertex), targetBoundary z := by
    intro z hz
    rw [← (F.mapEdgeSet f).1.out_eq, Sym2.mem_iff] at hz
    exact hz.elim (fun h ↦ h ▸ htarget.1) (fun h ↦ h ▸ htarget.2)
  have hsource : ∀ z ∈ (f : Sym2 SquareVertex),
      squareRectangleBoundaryVertex ms ns z := by
    intro z hz
    apply hboundary z (endpoint_mem_squareRectangle_of_edge_mem hf.1 hz)
    apply hmapped (F z)
    exact Sym2.mem_map.mpr ⟨z, hz, rfl⟩
  exact ⟨hsource f.1.out.1 (Sym2.out_fst_mem _),
    hsource f.1.out.2 (Sym2.out_snd_mem _)⟩

private theorem brSourceSquareEdge_not_both_union_boundary
    {m n : ℕ} (hm : 2 * n ≤ m) {e : SquareEdge}
    (he : e ∈ brSourceSquareEdges n) :
    ¬ (brSourceUnionBoundaryVertex m n e.1.out.1 ∧
      brSourceUnionBoundaryVertex m n e.1.out.2) := by
  rw [brSourceSquareEdges, squareBoundaryFreeRectangleEdges,
    Finset.mem_filter] at he
  intro htarget
  apply he.2
  have hsource : ∀ z ∈ (e : Sym2 SquareVertex),
      squareRectangleBoundaryVertex (2 * n) n z := by
    intro z hz
    have hzRect := mem_squareRectangleVertices_iff.mp
      (endpoint_mem_squareRectangle_of_edge_mem he.1 hz)
    have hzBoundary : brSourceUnionBoundaryVertex m n z := by
      rw [← e.1.out_eq, Sym2.mem_iff] at hz
      rcases hz with hz | hz
      · exact hz ▸ htarget.1
      · exact hz ▸ htarget.2
    unfold brSourceUnionBoundaryVertex at hzBoundary
    unfold squareRectangleBoundaryVertex
    omega
  exact ⟨hsource e.1.out.1 (Sym2.out_fst_mem _),
    hsource e.1.out.2 (Sym2.out_snd_mem _)⟩

private theorem brReflectedSourceSquareEdge_not_both_union_boundary
    {m n : ℕ} (hm : 2 * n ≤ m) {e : SquareEdge}
    (he : e ∈ brSourceSquareEdges n) :
    ¬ (brSourceUnionBoundaryVertex m n
          ((brPrimalSourceVerticalAxisReflectionIso n).mapEdgeSet e).1.out.1 ∧
      brSourceUnionBoundaryVertex m n
          ((brPrimalSourceVerticalAxisReflectionIso n).mapEdgeSet e).1.out.2) := by
  apply mappedBoundaryFreeEdge_not_both_boundary he
    (brPrimalSourceVerticalAxisReflectionIso n) (brSourceUnionBoundaryVertex m n)
  intro x hx hboundary
  have hx' := mem_squareRectangleVertices_iff.mp hx
  unfold brSourceUnionBoundaryVertex at hboundary
  unfold squareRectangleBoundaryVertex
  simp only [brPrimalSourceVerticalAxisReflectionIso_zero,
    brPrimalSourceVerticalAxisReflectionIso_one] at hboundary
  omega

private theorem brExtensionEdge_not_both_union_boundary
    {m n : ℕ} (hm : 2 * n ≤ m) {e : SquareEdge}
    (he : e ∈ brExtensionRectangleEdges m n) :
    ¬ (brSourceUnionBoundaryVertex m n e.1.out.1 ∧
      brSourceUnionBoundaryVertex m n e.1.out.2) := by
  rw [brExtensionRectangleEdges, Finset.mem_map] at he
  obtain ⟨f, hf, rfl⟩ := he
  apply mappedBoundaryFreeEdge_not_both_boundary hf
    (brExtensionRectangleTranslateIso n) (brSourceUnionBoundaryVertex m n)
  intro x hx hboundary
  have hx' := mem_squareRectangleVertices_iff.mp hx
  unfold brSourceUnionBoundaryVertex at hboundary
  unfold squareRectangleBoundaryVertex
  simp only [brExtensionRectangleTranslateIso_zero,
    brExtensionRectangleTranslateIso_one] at hboundary
  omega

private theorem brReflectedExtensionEdge_not_both_union_boundary
    {m n : ℕ} (hm : 2 * n ≤ m) {e : SquareEdge}
    (he : e ∈ brExtensionRectangleEdges m n) :
    ¬ (brSourceUnionBoundaryVertex m n
          ((brPrimalSourceVerticalAxisReflectionIso n).mapEdgeSet e).1.out.1 ∧
      brSourceUnionBoundaryVertex m n
          ((brPrimalSourceVerticalAxisReflectionIso n).mapEdgeSet e).1.out.2) := by
  rw [brExtensionRectangleEdges, Finset.mem_map] at he
  obtain ⟨f, hf, rfl⟩ := he
  let F : squareGraph ≃g squareGraph := (brExtensionRectangleTranslateIso n).trans
    (brPrimalSourceVerticalAxisReflectionIso n)
  have hmap : F.mapEdgeSet f =
      (brPrimalSourceVerticalAxisReflectionIso n).mapEdgeSet
        ((brExtensionRectangleTranslateIso n).mapEdgeSet f) := by
    rcases f with ⟨e, he⟩
    induction e using Sym2.ind with
    | _ x y =>
        apply Subtype.ext
        rfl
  have hnot := mappedBoundaryFreeEdge_not_both_boundary hf F
    (brSourceUnionBoundaryVertex m n) (by
      intro x hx hboundary
      have hx' := mem_squareRectangleVertices_iff.mp hx
      change brSourceUnionBoundaryVertex m n
        (brPrimalSourceVerticalAxisReflectionIso n
          (brExtensionRectangleTranslateIso n x)) at hboundary
      unfold brSourceUnionBoundaryVertex at hboundary
      unfold squareRectangleBoundaryVertex
      simp only [brExtensionRectangleTranslateIso_zero,
        brExtensionRectangleTranslateIso_one,
        brPrimalSourceVerticalAxisReflectionIso_zero,
        brPrimalSourceVerticalAxisReflectionIso_one] at hboundary
      omega)
  simpa only [hmap] using hnot

private theorem endpoint_coordinates_of_mem_brSourceSquareEdges
    {n : ℕ} {e : SquareEdge} (he : e ∈ brSourceSquareEdges n)
    {x : SquareVertex} (hx : x ∈ (e : Sym2 SquareVertex)) :
    0 ≤ x 0 ∧ x 0 ≤ 2 * (n : ℤ) ∧
      -(n : ℤ) ≤ x 1 ∧ x 1 ≤ (n : ℤ) := by
  rw [brSourceSquareEdges, squareBoundaryFreeRectangleEdges,
    Finset.mem_filter] at he
  exact mem_squareRectangleVertices_iff.mp
    (endpoint_mem_squareRectangle_of_edge_mem he.1 hx)

private theorem endpoint_coordinates_of_mem_brExtensionRectangleEdges
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

private theorem endpoint_coordinates_of_mem_reflected_brSourceSquareEdges
    {n : ℕ} {e : SquareEdge}
    (he : e ∈ (brSourceSquareEdges n).image
      (brPrimalSourceVerticalAxisReflectionIso n).mapEdgeSet)
    {x : SquareVertex} (hx : x ∈ (e : Sym2 SquareVertex)) :
    0 ≤ x 0 ∧ x 0 ≤ 2 * (n : ℤ) ∧
      -(n : ℤ) ≤ x 1 ∧ x 1 ≤ (n : ℤ) := by
  rw [Finset.mem_image] at he
  obtain ⟨f, hf, rfl⟩ := he
  change x ∈ Sym2.map (brPrimalSourceVerticalAxisReflectionIso n)
    (f : Sym2 SquareVertex) at hx
  rw [Sym2.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have hy' := endpoint_coordinates_of_mem_brSourceSquareEdges hf hy
  simp only [brPrimalSourceVerticalAxisReflectionIso_zero,
    brPrimalSourceVerticalAxisReflectionIso_one]
  omega

private theorem endpoint_coordinates_of_mem_reflected_brExtensionRectangleEdges
    {m n : ℕ} {e : SquareEdge}
    (he : e ∈ (brExtensionRectangleEdges m n).image
      (brPrimalSourceVerticalAxisReflectionIso n).mapEdgeSet)
    {x : SquareVertex} (hx : x ∈ (e : Sym2 SquareVertex)) :
    2 * (n : ℤ) - (m : ℤ) ≤ x 0 ∧ x 0 ≤ 2 * (n : ℤ) ∧
      -(n : ℤ) ≤ x 1 ∧ x 1 ≤ 3 * (n : ℤ) := by
  rw [Finset.mem_image] at he
  obtain ⟨f, hf, rfl⟩ := he
  change x ∈ Sym2.map (brPrimalSourceVerticalAxisReflectionIso n)
    (f : Sym2 SquareVertex) at hx
  rw [Sym2.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have hy' := endpoint_coordinates_of_mem_brExtensionRectangleEdges hf hy
  simp only [brPrimalSourceVerticalAxisReflectionIso_zero,
    brPrimalSourceVerticalAxisReflectionIso_one]
  omega

private theorem reflected_brSourceSquareEdge_not_both_union_boundary_of_mem
    {m n : ℕ} (hm : 2 * n ≤ m) {e : SquareEdge}
    (he : e ∈ (brSourceSquareEdges n).image
      (brPrimalSourceVerticalAxisReflectionIso n).mapEdgeSet) :
    ¬ (brSourceUnionBoundaryVertex m n e.1.out.1 ∧
      brSourceUnionBoundaryVertex m n e.1.out.2) := by
  rw [Finset.mem_image] at he
  obtain ⟨f, hf, rfl⟩ := he
  exact brReflectedSourceSquareEdge_not_both_union_boundary hm hf

private theorem reflected_brExtensionEdge_not_both_union_boundary_of_mem
    {m n : ℕ} (hm : 2 * n ≤ m) {e : SquareEdge}
    (he : e ∈ (brExtensionRectangleEdges m n).image
      (brPrimalSourceVerticalAxisReflectionIso n).mapEdgeSet) :
    ¬ (brSourceUnionBoundaryVertex m n e.1.out.1 ∧
      brSourceUnionBoundaryVertex m n e.1.out.2) := by
  rw [Finset.mem_image] at he
  obtain ⟨f, hf, rfl⟩ := he
  exact brReflectedExtensionEdge_not_both_union_boundary hm hf

private theorem walk_support_coordinates_of_edge_coordinates
    {u v : SquareVertex} (w : squareGraph.Walk u v)
    (P : SquareVertex → Prop) (hv : P v)
    (hEdges : ∀ e ∈ walkEdgeFinset w, ∀ x ∈ (e : Sym2 SquareVertex), P x) :
    ∀ x ∈ w.support, P x := by
  intro x hx
  rw [SimpleGraph.Walk.mem_support_iff_exists_mem_edges] at hx
  rcases hx with rfl | ⟨e, he, hxe⟩
  · exact hv
  · let ee : SquareEdge := ⟨e, w.edges_subset_edgeSet he⟩
    exact hEdges ee ((mem_walkEdgeFinset_iff w ee).mpr he) x hxe

private theorem walk_support_coordinates_of_brSourceSquareEdges
    {n : ℕ} {u v : SquareVertex} (w : squareGraph.Walk u v)
    (hv : 0 ≤ v 0 ∧ v 0 ≤ 2 * (n : ℤ) ∧
      -(n : ℤ) ≤ v 1 ∧ v 1 ≤ (n : ℤ))
    (hEdges : walkEdgeFinset w ⊆ brSourceSquareEdges n) :
    ∀ x ∈ w.support,
      0 ≤ x 0 ∧ x 0 ≤ 2 * (n : ℤ) ∧
        -(n : ℤ) ≤ x 1 ∧ x 1 ≤ (n : ℤ) := by
  apply walk_support_coordinates_of_edge_coordinates w
    (fun x ↦ 0 ≤ x 0 ∧ x 0 ≤ 2 * (n : ℤ) ∧
      -(n : ℤ) ≤ x 1 ∧ x 1 ≤ (n : ℤ)) hv
  intro e he x hx
  exact endpoint_coordinates_of_mem_brSourceSquareEdges (hEdges he) hx

private theorem walk_support_coordinates_of_brExtensionRectangleEdges
    {m n : ℕ} {u v : SquareVertex} (w : squareGraph.Walk u v)
    (hv : 0 ≤ v 0 ∧ v 0 ≤ (m : ℤ) ∧
      -(n : ℤ) ≤ v 1 ∧ v 1 ≤ 3 * (n : ℤ))
    (hEdges : walkEdgeFinset w ⊆ brExtensionRectangleEdges m n) :
    ∀ x ∈ w.support,
      0 ≤ x 0 ∧ x 0 ≤ (m : ℤ) ∧
        -(n : ℤ) ≤ x 1 ∧ x 1 ≤ 3 * (n : ℤ) := by
  apply walk_support_coordinates_of_edge_coordinates w
    (fun x ↦ 0 ≤ x 0 ∧ x 0 ≤ (m : ℤ) ∧
      -(n : ℤ) ≤ x 1 ∧ x 1 ≤ 3 * (n : ℤ)) hv
  intro e he x hx
  exact endpoint_coordinates_of_mem_brExtensionRectangleEdges (hEdges he) hx

private theorem walk_support_coordinates_of_reflected_brSourceSquareEdges
    {n : ℕ} {u v : SquareVertex} (w : squareGraph.Walk u v)
    (hv : 0 ≤ v 0 ∧ v 0 ≤ 2 * (n : ℤ) ∧
      -(n : ℤ) ≤ v 1 ∧ v 1 ≤ (n : ℤ))
    (hEdges : walkEdgeFinset w ⊆ (brSourceSquareEdges n).image
      (brPrimalSourceVerticalAxisReflectionIso n).mapEdgeSet) :
    ∀ x ∈ w.support,
      0 ≤ x 0 ∧ x 0 ≤ 2 * (n : ℤ) ∧
        -(n : ℤ) ≤ x 1 ∧ x 1 ≤ (n : ℤ) := by
  apply walk_support_coordinates_of_edge_coordinates w
    (fun x ↦ 0 ≤ x 0 ∧ x 0 ≤ 2 * (n : ℤ) ∧
      -(n : ℤ) ≤ x 1 ∧ x 1 ≤ (n : ℤ)) hv
  intro e he x hx
  exact endpoint_coordinates_of_mem_reflected_brSourceSquareEdges (hEdges he) hx

private theorem walk_support_coordinates_of_reflected_brExtensionRectangleEdges
    {m n : ℕ} {u v : SquareVertex} (w : squareGraph.Walk u v)
    (hv : 2 * (n : ℤ) - (m : ℤ) ≤ v 0 ∧ v 0 ≤ 2 * (n : ℤ) ∧
      -(n : ℤ) ≤ v 1 ∧ v 1 ≤ 3 * (n : ℤ))
    (hEdges : walkEdgeFinset w ⊆ (brExtensionRectangleEdges m n).image
      (brPrimalSourceVerticalAxisReflectionIso n).mapEdgeSet) :
    ∀ x ∈ w.support,
      2 * (n : ℤ) - (m : ℤ) ≤ x 0 ∧ x 0 ≤ 2 * (n : ℤ) ∧
        -(n : ℤ) ≤ x 1 ∧ x 1 ≤ 3 * (n : ℤ) := by
  apply walk_support_coordinates_of_edge_coordinates w
    (fun x ↦ 2 * (n : ℤ) - (m : ℤ) ≤ x 0 ∧
      x 0 ≤ 2 * (n : ℤ) ∧ -(n : ℤ) ≤ x 1 ∧ x 1 ≤ 3 * (n : ℤ)) hv
  intro e he x hx
  exact endpoint_coordinates_of_mem_reflected_brExtensionRectangleEdges (hEdges he) hx

/-- Deterministic Bollobás--Riordan gluing: the two reflected source events and the crossing of
their common square produce a boundary-free crossing of the union rectangle. -/
theorem brSourceXGluingIntersection_subset_brSourceUnionCrossingEvent
    {m n : ℕ} (hm : 2 * n ≤ m) :
    brSourceXGluingIntersection m n ⊆ brSourceUnionCrossingEvent m n := by
  intro omega homega
  rcases homega with ⟨⟨hRight, hLeft⟩, hHorizontal⟩
  rcases hRight with ⟨XRight⟩
  let V := brPrimalSourceVerticalAxisReflectionIso n
  change cubicGraphIsoConfigurationPullback V omega ∈ brSourceXEvent m n at hLeft
  rcases hLeft with ⟨XLeft⟩
  change omega ∈ squareBoundaryFreeRectangleCrossingEvent (2 * n) n at hHorizontal
  obtain ⟨H, hHEdges⟩ :=
    exists_openSquareRectangleCrossing_of_mem_boundaryFree hHorizontal

  obtain ⟨wbR, hwbROpen, hwbREdges⟩ := XRight.connected_bottom
  obtain ⟨wtR, hwtROpen, hwtREdges⟩ := XRight.connected_top
  obtain ⟨wrR, hwrROpen, hwrREdges⟩ := XRight.connected_right
  have hwbRFinish : 0 ≤ XRight.bottom 0 ∧ XRight.bottom 0 ≤ 2 * (n : ℤ) ∧
      -(n : ℤ) ≤ XRight.bottom 1 ∧ XRight.bottom 1 ≤ (n : ℤ) := by
    have h := XRight.bottom_coordinates
    omega
  have hwtRFinish : 0 ≤ XRight.top 0 ∧ XRight.top 0 ≤ 2 * (n : ℤ) ∧
      -(n : ℤ) ≤ XRight.top 1 ∧ XRight.top 1 ≤ (n : ℤ) := by
    have h := XRight.top_coordinates
    omega
  have hwbRSupport := walk_support_coordinates_of_brSourceSquareEdges wbR
    hwbRFinish hwbREdges
  have hwtRSupport := walk_support_coordinates_of_brSourceSquareEdges wtR
    hwtRFinish hwtREdges
  have hwrRFinish : 0 ≤ XRight.right 0 ∧ XRight.right 0 ≤ (m : ℤ) ∧
      -(n : ℤ) ≤ XRight.right 1 ∧ XRight.right 1 ≤ 3 * (n : ℤ) := by
    have h := XRight.right_coordinates
    omega
  have hwrRSupport := walk_support_coordinates_of_brExtensionRectangleEdges wrR
    hwrRFinish hwrREdges

  have hwbLConnection :=
    (cubicGraphIsoConfigurationPullback_mem_connectionEventIn_iff V
      (brSourceSquareEdges n) omega XLeft.junction XLeft.bottom).mp
      XLeft.connected_bottom
  have hwtLConnection :=
    (cubicGraphIsoConfigurationPullback_mem_connectionEventIn_iff V
      (brSourceSquareEdges n) omega XLeft.junction XLeft.top).mp
      XLeft.connected_top
  have hwrLConnection :=
    (cubicGraphIsoConfigurationPullback_mem_connectionEventIn_iff V
      (brExtensionRectangleEdges m n) omega XLeft.junction XLeft.right).mp
      XLeft.connected_right
  obtain ⟨wbL, hwbLOpen, hwbLEdges⟩ := hwbLConnection
  obtain ⟨wtL, hwtLOpen, hwtLEdges⟩ := hwtLConnection
  obtain ⟨wrL, hwrLOpen, hwrLEdges⟩ := hwrLConnection
  have hwbLFinish : 0 ≤ V XLeft.bottom 0 ∧ V XLeft.bottom 0 ≤ 2 * (n : ℤ) ∧
      -(n : ℤ) ≤ V XLeft.bottom 1 ∧ V XLeft.bottom 1 ≤ (n : ℤ) := by
    have h := XLeft.bottom_coordinates
    simp only [V, brPrimalSourceVerticalAxisReflectionIso_zero,
      brPrimalSourceVerticalAxisReflectionIso_one]
    omega
  have hwtLFinish : 0 ≤ V XLeft.top 0 ∧ V XLeft.top 0 ≤ 2 * (n : ℤ) ∧
      -(n : ℤ) ≤ V XLeft.top 1 ∧ V XLeft.top 1 ≤ (n : ℤ) := by
    have h := XLeft.top_coordinates
    simp only [V, brPrimalSourceVerticalAxisReflectionIso_zero,
      brPrimalSourceVerticalAxisReflectionIso_one]
    omega
  have hwrLFinish : 2 * (n : ℤ) - (m : ℤ) ≤ V XLeft.right 0 ∧
      V XLeft.right 0 ≤ 2 * (n : ℤ) ∧
      -(n : ℤ) ≤ V XLeft.right 1 ∧ V XLeft.right 1 ≤ 3 * (n : ℤ) := by
    have h := XLeft.right_coordinates
    simp only [V, brPrimalSourceVerticalAxisReflectionIso_zero,
      brPrimalSourceVerticalAxisReflectionIso_one]
    omega
  have hwbLSupport := walk_support_coordinates_of_reflected_brSourceSquareEdges wbL
    hwbLFinish hwbLEdges
  have hwtLSupport := walk_support_coordinates_of_reflected_brSourceSquareEdges wtL
    hwtLFinish hwtLEdges
  have hwrLSupport :=
    walk_support_coordinates_of_reflected_brExtensionRectangleEdges wrL
      hwrLFinish hwrLEdges

  let vR := wbR.reverse.append wtR
  let vL := wbL.reverse.append wtL
  have hvRSupport : ∀ x ∈ vR.support,
      0 ≤ x 0 ∧ x 0 ≤ 2 * (n : ℤ) ∧
        -(n : ℤ) ≤ x 1 ∧ x 1 ≤ (n : ℤ) := by
    intro x hx
    simp only [vR, SimpleGraph.Walk.mem_support_append_iff,
      SimpleGraph.Walk.support_reverse, List.mem_reverse] at hx
    exact hx.elim (hwbRSupport x) (hwtRSupport x)
  have hvLSupport : ∀ x ∈ vL.support,
      0 ≤ x 0 ∧ x 0 ≤ 2 * (n : ℤ) ∧
        -(n : ℤ) ≤ x 1 ∧ x 1 ≤ (n : ℤ) := by
    intro x hx
    simp only [vL, SimpleGraph.Walk.mem_support_append_iff,
      SimpleGraph.Walk.support_reverse, List.mem_reverse] at hx
    exact hx.elim (hwbLSupport x) (hwtLSupport x)

  have hHStart := mem_squareRectangleLeft_iff.mp H.start_mem
  have hHFinish := mem_squareRectangleRight_iff.mp H.finish_mem
  let p : squareGraph.Walk (squareVertex 0 (H.start 1))
      (squareVertex (2 * (n : ℤ)) (H.finish 1)) :=
    H.walk.copy
      (by ext i; fin_cases i <;> simp [squareVertex, hHStart.1])
      (by ext i; fin_cases i <;> simp [squareVertex, hHFinish.1])
  let qR : squareGraph.Walk
      (squareVertex (XRight.bottom 0) (-(n : ℤ)))
      (squareVertex (XRight.top 0) (n : ℤ)) :=
    vR.copy
      (by
        ext i
        fin_cases i
        · simp [squareVertex]
        · have h := XRight.bottom_coordinates
          simp [squareVertex]
          omega)
      (by
        ext i
        fin_cases i
        · simp [squareVertex]
        · have h := XRight.top_coordinates
          simp [squareVertex]
          omega)
  let qL : squareGraph.Walk
      (squareVertex (V XLeft.bottom 0) (-(n : ℤ)))
      (squareVertex (V XLeft.top 0) (n : ℤ)) :=
    vL.copy
      (by
        ext i
        fin_cases i
        · simp [squareVertex]
        · have h := XLeft.bottom_coordinates
          simp [V, squareVertex]
          omega)
      (by
        ext i
        fin_cases i
        · simp [squareVertex]
        · have h := XLeft.top_coordinates
          simp [V, squareVertex]
          omega)
  have hpSupport : ∀ x ∈ p.support,
      0 ≤ x 0 ∧ x 0 ≤ 2 * (n : ℤ) ∧
        -(n : ℤ) ≤ x 1 ∧ x 1 ≤ (n : ℤ) := by
    intro x hx
    have hx' : x ∈ H.walk.support := by simpa [p] using hx
    exact mem_squareRectangleVertices_iff.mp (H.support_mem_rectangle hx')
  have hqRSupport : ∀ x ∈ qR.support,
      0 ≤ x 0 ∧ x 0 ≤ 2 * (n : ℤ) ∧
        -(n : ℤ) ≤ x 1 ∧ x 1 ≤ (n : ℤ) := by
    intro x hx
    exact hvRSupport x (by simpa [qR] using hx)
  have hqLSupport : ∀ x ∈ qL.support,
      0 ≤ x 0 ∧ x 0 ≤ 2 * (n : ℤ) ∧
        -(n : ℤ) ≤ x 1 ∧ x 1 ≤ (n : ℤ) := by
    intro x hx
    exact hvLSupport x (by simpa [qL] using hx)

  obtain ⟨zR, hzRH, hzRv⟩ := brCenteredSquareWalk_support_inter
    hHStart.2.1 hHStart.2.2 hHFinish.2.1 hHFinish.2.2
    XRight.bottom_coordinates.1 XRight.bottom_coordinates.2.1
    XRight.top_coordinates.1 XRight.top_coordinates.2.1
    p qR hpSupport hqRSupport
  obtain ⟨zL, hzLH, hzLv⟩ := brCenteredSquareWalk_support_inter
    hHStart.2.1 hHStart.2.2 hHFinish.2.1 hHFinish.2.2
    hwbLFinish.1 hwbLFinish.2.1 hwtLFinish.1 hwtLFinish.2.1
    p qL hpSupport hqLSupport
  have hzRH' : zR ∈ H.walk.support := by simpa [p] using hzRH
  have hzLH' : zL ∈ H.walk.support := by simpa [p] using hzLH
  have hzRv' : zR ∈ vR.support := by simpa [qR] using hzRv
  have hzLv' : zL ∈ vL.support := by simpa [qL] using hzLv

  let jR := wbR.append (wbR.reverse.append wtR)
  let jL := wbL.append (wbL.reverse.append wtL)
  have hzRj : zR ∈ jR.support := by
    simp only [jR, SimpleGraph.Walk.mem_support_append_iff]
    right
    simpa [vR] using hzRv'
  have hzLj : zL ∈ jL.support := by
    simp only [jL, SimpleGraph.Walk.mem_support_append_iff]
    right
    simpa [vL] using hzLv'
  let leftToContact := wrL.reverse.append (jL.takeUntil zL hzLj)
  let horizontalBetween :=
    (H.walk.takeUntil zL hzLH').reverse.append (H.walk.takeUntil zR hzRH')
  let contactToRight := (jR.takeUntil zR hzRj).reverse.append wrR
  let W := leftToContact.append (horizontalBetween.append contactToRight)
  have hjROpen : walkIsOpen omega jR :=
    walkIsOpen_append hwbROpen
      (walkIsOpen_append (walkIsOpen_reverse hwbROpen) hwtROpen)
  have hjLOpen : walkIsOpen omega jL :=
    walkIsOpen_append hwbLOpen
      (walkIsOpen_append (walkIsOpen_reverse hwbLOpen) hwtLOpen)
  have hleftOpen : walkIsOpen omega leftToContact :=
    walkIsOpen_append (walkIsOpen_reverse hwrLOpen)
      (walkIsOpen_of_edges_subset hjLOpen (jL.edges_takeUntil_subset hzLj))
  have hhorizontalOpen : walkIsOpen omega horizontalBetween :=
    walkIsOpen_append
      (walkIsOpen_reverse
        (walkIsOpen_of_edges_subset H.isOpen (H.walk.edges_takeUntil_subset hzLH')))
      (walkIsOpen_of_edges_subset H.isOpen (H.walk.edges_takeUntil_subset hzRH'))
  have hrightOpen : walkIsOpen omega contactToRight :=
    walkIsOpen_append
      (walkIsOpen_reverse
        (walkIsOpen_of_edges_subset hjROpen (jR.edges_takeUntil_subset hzRj)))
      hwrROpen
  have hWOpen : walkIsOpen omega W :=
    walkIsOpen_append hleftOpen (walkIsOpen_append hhorizontalOpen hrightOpen)

  have hWEdgeKind : ∀ e ∈ walkEdgeFinset W,
      e ∈ (brExtensionRectangleEdges m n).image V.mapEdgeSet ∨
      e ∈ (brSourceSquareEdges n).image V.mapEdgeSet ∨
      e ∈ brSourceSquareEdges n ∨ e ∈ brExtensionRectangleEdges m n := by
    intro e he
    have heW : (e : Sym2 SquareVertex) ∈ W.edges :=
      (mem_walkEdgeFinset_iff W e).mp he
    simp only [W, SimpleGraph.Walk.edges_append] at heW
    rcases List.mem_append.mp heW with heLeft | heRest
    · simp only [leftToContact, SimpleGraph.Walk.edges_append] at heLeft
      rcases List.mem_append.mp heLeft with heArm | heJtake
      · rw [SimpleGraph.Walk.edges_reverse, List.mem_reverse] at heArm
        exact Or.inl (hwrLEdges ((mem_walkEdgeFinset_iff wrL e).mpr heArm))
      · have heJ := jL.edges_takeUntil_subset hzLj heJtake
        simp only [jL, SimpleGraph.Walk.edges_append] at heJ
        rcases List.mem_append.mp heJ with heJ | heJrest
        · exact Or.inr (Or.inl
            (hwbLEdges ((mem_walkEdgeFinset_iff wbL e).mpr heJ)))
        · rcases List.mem_append.mp heJrest with heJ | heJ
          · rw [SimpleGraph.Walk.edges_reverse, List.mem_reverse] at heJ
            exact Or.inr (Or.inl
              (hwbLEdges ((mem_walkEdgeFinset_iff wbL e).mpr heJ)))
          · exact Or.inr (Or.inl
              (hwtLEdges ((mem_walkEdgeFinset_iff wtL e).mpr heJ)))
    · rcases List.mem_append.mp heRest with heHorizontal | heRight
      · simp only [horizontalBetween, SimpleGraph.Walk.edges_append] at heHorizontal
        rcases List.mem_append.mp heHorizontal with heH | heH
        · rw [SimpleGraph.Walk.edges_reverse, List.mem_reverse] at heH
          exact Or.inr (Or.inr (Or.inl
            (hHEdges ((mem_walkEdgeFinset_iff H.walk e).mpr
              (H.walk.edges_takeUntil_subset hzLH' heH)))))
        · exact Or.inr (Or.inr (Or.inl
            (hHEdges ((mem_walkEdgeFinset_iff H.walk e).mpr
              (H.walk.edges_takeUntil_subset hzRH' heH)))))
      · simp only [contactToRight, SimpleGraph.Walk.edges_append] at heRight
        rcases List.mem_append.mp heRight with heJtake | heArm
        · rw [SimpleGraph.Walk.edges_reverse, List.mem_reverse] at heJtake
          have heJ := jR.edges_takeUntil_subset hzRj heJtake
          simp only [jR, SimpleGraph.Walk.edges_append] at heJ
          rcases List.mem_append.mp heJ with heJ | heJrest
          · exact Or.inr (Or.inr (Or.inl
              (hwbREdges ((mem_walkEdgeFinset_iff wbR e).mpr heJ))))
          · rcases List.mem_append.mp heJrest with heJ | heJ
            · rw [SimpleGraph.Walk.edges_reverse, List.mem_reverse] at heJ
              exact Or.inr (Or.inr (Or.inl
                (hwbREdges ((mem_walkEdgeFinset_iff wbR e).mpr heJ))))
            · exact Or.inr (Or.inr (Or.inl
                (hwtREdges ((mem_walkEdgeFinset_iff wtR e).mpr heJ))))
        · exact Or.inr (Or.inr (Or.inr
            (hwrREdges ((mem_walkEdgeFinset_iff wrR e).mpr heArm))))

  have hWNoBoundary : ∀ e ∈ walkEdgeFinset W,
      ¬ (brSourceUnionBoundaryVertex m n e.1.out.1 ∧
        brSourceUnionBoundaryVertex m n e.1.out.2) := by
    intro e he
    rcases hWEdgeKind e he with he | he | he | he
    · exact reflected_brExtensionEdge_not_both_union_boundary_of_mem hm he
    · exact reflected_brSourceSquareEdge_not_both_union_boundary_of_mem hm he
    · exact brSourceSquareEdge_not_both_union_boundary hm he
    · exact brExtensionEdge_not_both_union_boundary hm he
  have hWEdgeCoordinates : ∀ e ∈ walkEdgeFinset W,
      ∀ x ∈ (e : Sym2 SquareVertex),
        2 * (n : ℤ) - (m : ℤ) ≤ x 0 ∧ x 0 ≤ (m : ℤ) ∧
          -(n : ℤ) ≤ x 1 ∧ x 1 ≤ 3 * (n : ℤ) := by
    intro e he x hx
    rcases hWEdgeKind e he with he | he | he | he
    · have h := endpoint_coordinates_of_mem_reflected_brExtensionRectangleEdges he hx
      omega
    · have h := endpoint_coordinates_of_mem_reflected_brSourceSquareEdges he hx
      omega
    · have h := endpoint_coordinates_of_mem_brSourceSquareEdges he hx
      omega
    · have h := endpoint_coordinates_of_mem_brExtensionRectangleEdges he hx
      omega
  have hWFinish : 2 * (n : ℤ) - (m : ℤ) ≤ XRight.right 0 ∧
      XRight.right 0 ≤ (m : ℤ) ∧ -(n : ℤ) ≤ XRight.right 1 ∧
        XRight.right 1 ≤ 3 * (n : ℤ) := by
    have h := XRight.right_coordinates
    omega
  have hWSupport : ∀ x ∈ W.support,
      2 * (n : ℤ) - (m : ℤ) ≤ x 0 ∧ x 0 ≤ (m : ℤ) ∧
        -(n : ℤ) ≤ x 1 ∧ x 1 ≤ 3 * (n : ℤ) :=
    walk_support_coordinates_of_edge_coordinates W _ hWFinish hWEdgeCoordinates

  let P := brSourceUnionPlacementIso m n
  let Wn := W.map P.symm.toHom
  have hWnOpen : walkIsOpen (cubicGraphIsoConfigurationPullback P omega) Wn := by
    apply walkIsOpen_map_cubicGraphIso P.symm W
    simpa [P] using hWOpen
  have hWnSupport : ∀ x ∈ Wn.support,
      x ∈ squareRectangleVertices (2 * m - 2 * n) (2 * n) := by
    intro x hx
    simp only [Wn, SimpleGraph.Walk.support_map, List.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact brSourceUnionPlacementIso_symm_mem_rectangle hm (hWSupport y hy)
  have hWnEdges : walkEdgeFinset Wn ⊆
      squareBoundaryFreeRectangleEdges (2 * m - 2 * n) (2 * n) := by
    intro e he
    rw [squareBoundaryFreeRectangleEdges, Finset.mem_filter]
    refine ⟨walkEdgeFinset_subset_squareRectangleEdges_of_support Wn hWnSupport he, ?_⟩
    simp only [mem_walkEdgeFinset_iff, Wn, SimpleGraph.Walk.edges_map] at he
    obtain ⟨f, hf, hef⟩ := List.mem_map.mp he
    let fe : SquareEdge := ⟨f, W.edges_subset_edgeSet hf⟩
    have hfe : fe ∈ walkEdgeFinset W := (mem_walkEdgeFinset_iff W fe).mpr hf
    have hnot := brSourceUnionPlacementIso_symm_mapEdge_not_both_boundary hm
      (hWNoBoundary fe hfe)
    have heq : e = P.symm.mapEdgeSet fe := by
      apply Subtype.ext
      exact hef.symm
    simpa [P, heq] using hnot

  change cubicGraphIsoConfigurationPullback P omega ∈
    squareBoundaryFreeRectangleCrossingEvent (2 * m - 2 * n) (2 * n)
  simp only [squareBoundaryFreeRectangleCrossingEvent, Set.mem_iUnion]
  refine ⟨P.symm (V XLeft.right), ?_, P.symm XRight.right, ?_, Wn, hWnOpen, hWnEdges⟩
  · rw [mem_squareRectangleLeft_iff]
    have h := XLeft.right_coordinates
    simp only [P, V, brSourceUnionPlacementIso_symm_zero,
      brSourceUnionPlacementIso_symm_one,
      brPrimalSourceVerticalAxisReflectionIso_zero,
      brPrimalSourceVerticalAxisReflectionIso_one]
    omega
  · rw [mem_squareRectangleRight_iff]
    have h := XRight.right_coordinates
    have hmn : 2 * n ≤ 2 * m := by omega
    have hcast : ((2 * m - 2 * n : ℕ) : ℤ) =
        2 * (m : ℤ) - 2 * (n : ℤ) := by
      rw [Nat.cast_sub hmn]
      push_cast
      ring
    simp only [P, brSourceUnionPlacementIso_symm_zero,
      brSourceUnionPlacementIso_symm_one]
    rw [hcast]
    omega

/-- Probability form of the deterministic source-event gluing, ready for the
Bollobás--Riordan recurrence. -/
theorem brSourceXGluing_probability_le_unionCrossing
    (p : I) {m n : ℕ} (hm : 2 * n ≤ m) :
    rswSquareCrossingProbability p n *
        (bernoulliBondMeasure 2 p).real (brSourceXEvent m n) ^ 2 ≤
      (bernoulliBondMeasure 2 p).real
        (squareBoundaryFreeRectangleCrossingEvent (2 * m - 2 * n) (2 * n)) := by
  calc
    rswSquareCrossingProbability p n *
          (bernoulliBondMeasure 2 p).real (brSourceXEvent m n) ^ 2 ≤
        (bernoulliBondMeasure 2 p).real
          (brSourceXGluingIntersection m n) :=
      brSourceXGluingIntersection_probability_ge p m n
    _ ≤ (bernoulliBondMeasure 2 p).real (brSourceUnionCrossingEvent m n) :=
      measureReal_mono
        (brSourceXGluingIntersection_subset_brSourceUnionCrossingEvent hm)
        (measure_ne_top _ _)
    _ = (bernoulliBondMeasure 2 p).real
          (squareBoundaryFreeRectangleCrossingEvent (2 * m - 2 * n) (2 * n)) :=
      bernoulliBondMeasure_real_brSourceUnionCrossingEvent p m n

end

end Percolation
