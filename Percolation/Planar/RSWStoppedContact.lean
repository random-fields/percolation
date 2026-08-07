import Percolation.Planar.RSWStoppedInterface

/-!
# Contact events for the stopped RSW interface

This file places an RSW square on `[0,2n] × [0,2n]` and records its deterministic contact
with the doubled stopped interface.  The later locality theorem will replace the full square
support below by the portion fresh for the stopped dual fiber.
-/

namespace Percolation

open SimpleGraph MeasureTheory ProbabilityTheory
open scoped unitInterval

noncomputable section

/-- Translation of the centered RSW square upward by `n`. -/
def rswStoppedSquareTranslationIso (n : ℕ) : squareGraph ≃g squareGraph :=
  cubicTranslationIso cubicOrigin (squareVertex 0 (n : ℤ))

@[simp]
theorem rswStoppedSquareTranslationIso_zero (n : ℕ) (x : SquareVertex) :
    rswStoppedSquareTranslationIso n x 0 = x 0 := by
  simp [rswStoppedSquareTranslationIso, cubicTranslationIso_apply,
    cubicTranslate, cubicOrigin, squareVertex]

@[simp]
theorem rswStoppedSquareTranslationIso_one (n : ℕ) (x : SquareVertex) :
    rswStoppedSquareTranslationIso n x 1 = x 1 + (n : ℤ) := by
  simp [rswStoppedSquareTranslationIso, cubicTranslationIso_apply,
    cubicTranslate, cubicOrigin, squareVertex]

/-- Boundary-free bonds in the translated square `[0,2n] × [0,2n]`. -/
def rswStoppedSquareEdges (n : ℕ) : Finset SquareEdge :=
  (squareBoundaryFreeRectangleEdges (2 * n) n).image
    (rswStoppedSquareTranslationIso n).mapEdgeSet

theorem brPrimalTopReflectionIso_mapEdgeSet_rswStoppedSquareTranslation
    (n : ℕ) (e : SquareEdge) :
    (brPrimalTopReflectionIso n).mapEdgeSet
        ((rswStoppedSquareTranslationIso n).mapEdgeSet e) =
      (rswStoppedSquareTranslationIso n).mapEdgeSet
        (brHorizontalAxisReflectionIso.mapEdgeSet e) := by
  simpa only [rswStoppedSquareTranslationIso,
    brExtensionRectangleTranslateIso, squareCrossingTranslateIso] using
      brPrimalTopReflectionIso_mapEdgeSet_extensionTranslate n e

/-- Reflection in the horizontal midline of the translated square preserves its exact finite
edge support. -/
theorem brPrimalTopReflectionIso_image_rswStoppedSquareEdges (n : ℕ) :
    (rswStoppedSquareEdges n).image
        (brPrimalTopReflectionIso n).mapEdgeSet =
      rswStoppedSquareEdges n := by
  classical
  apply Finset.eq_of_subset_of_card_le
  · intro e he
    rw [Finset.mem_image] at he
    obtain ⟨f, hf, rfl⟩ := he
    rw [rswStoppedSquareEdges, Finset.mem_image] at hf ⊢
    obtain ⟨g, hg, rfl⟩ := hf
    have hreflect : brHorizontalAxisReflectionIso.mapEdgeSet g ∈
        squareBoundaryFreeRectangleEdges (2 * n) n := by
      rw [← brHorizontalAxisReflectionIso_image_boundaryFreeRectangleEdges]
      exact Finset.mem_image.mpr ⟨g, hg, rfl⟩
    exact ⟨brHorizontalAxisReflectionIso.mapEdgeSet g, hreflect,
      (brPrimalTopReflectionIso_mapEdgeSet_rswStoppedSquareTranslation n g).symm⟩
  · rw [Finset.card_image_of_injective _
      (brPrimalTopReflectionIso n).mapEdgeSet.injective]

/-- Right side of the translated square. -/
def rswStoppedSquareRightSide (n : ℕ) : Finset SquareVertex :=
  (squareRectangleRight (2 * n) n).map
    (rswStoppedSquareTranslationIso n).toEquiv.toEmbedding

@[simp]
theorem mem_rswStoppedSquareRightSide_iff
    {n : ℕ} {x : SquareVertex} :
    x ∈ rswStoppedSquareRightSide n ↔
      x 0 = 2 * (n : ℤ) ∧ 0 ≤ x 1 ∧ x 1 ≤ 2 * (n : ℤ) := by
  classical
  rw [rswStoppedSquareRightSide, Finset.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' := mem_squareRectangleRight_iff.mp hy
    change rswStoppedSquareTranslationIso n y 0 = 2 * (n : ℤ) ∧
      0 ≤ rswStoppedSquareTranslationIso n y 1 ∧
        rswStoppedSquareTranslationIso n y 1 ≤ 2 * (n : ℤ)
    simp only [rswStoppedSquareTranslationIso_zero,
      rswStoppedSquareTranslationIso_one]
    omega
  · rintro ⟨hx0, hx1, hx1'⟩
    let y : SquareVertex := squareVertex (x 0) (x 1 - (n : ℤ))
    refine ⟨y, ?_, ?_⟩
    · rw [mem_squareRectangleRight_iff]
      change y 0 = 2 * (n : ℤ) ∧ -(n : ℤ) ≤ y 1 ∧ y 1 ≤ (n : ℤ)
      have hy0 : y 0 = x 0 := by simp [y, squareVertex]
      have hy1 : y 1 = x 1 - (n : ℤ) := by simp [y, squareVertex]
      omega
    · ext i
      fin_cases i
      · simp [y, squareVertex, hx0]
      · simp [y, squareVertex]

private theorem brPrimalTopReflectionIso_mem_rswStoppedSquareRightSide_iff
    (n : ℕ) (x : SquareVertex) :
    brPrimalTopReflectionIso n x ∈ rswStoppedSquareRightSide n ↔
      x ∈ rswStoppedSquareRightSide n := by
  rw [mem_rswStoppedSquareRightSide_iff,
    mem_rswStoppedSquareRightSide_iff]
  simp only [brPrimalTopReflectionIso_zero,
    brPrimalTopReflectionIso_one]
  omega

/-- The translated copy of the RSW square-crossing event. -/
def rswStoppedSquareCrossingEvent (n : ℕ) : Set (EdgeConfiguration 2) :=
  cubicGraphIsoEvent (rswStoppedSquareTranslationIso n)
    (rswSquareCrossingEvent n)

theorem measurableSet_rswStoppedSquareCrossingEvent (n : ℕ) :
    MeasurableSet (rswStoppedSquareCrossingEvent n) :=
  measurableSet_cubicGraphIsoEvent _ (measurableSet_rswSquareCrossingEvent n)

theorem isIncreasingEvent_rswStoppedSquareCrossingEvent (n : ℕ) :
    IsIncreasingEvent (rswStoppedSquareCrossingEvent n) :=
  isIncreasingEvent_cubicGraphIsoEvent _ (isIncreasingEvent_rswSquareCrossingEvent n)

theorem bernoulliBondMeasure_real_rswStoppedSquareCrossingEvent
    (p : I) (n : ℕ) :
    (bernoulliBondMeasure 2 p).real (rswStoppedSquareCrossingEvent n) =
      rswSquareCrossingProbability p n := by
  unfold rswStoppedSquareCrossingEvent rswSquareCrossingProbability
  exact bernoulliBondMeasure_real_cubicGraphIsoEvent p _
    (measurableSet_rswSquareCrossingEvent n)

private theorem walkEdgeFinset_map_subset_rswStoppedSquareEdges
    {n : ℕ} {u v : SquareVertex}
    (w : squareGraph.Walk u v)
    (hw : walkEdgeFinset w ⊆ squareBoundaryFreeRectangleEdges (2 * n) n) :
    walkEdgeFinset (w.map (rswStoppedSquareTranslationIso n).toHom) ⊆
      rswStoppedSquareEdges n := by
  intro e he
  rw [mem_walkEdgeFinset_iff, SimpleGraph.Walk.edges_map, List.mem_map] at he
  rcases he with ⟨f, hf, hfe⟩
  let fe : SquareEdge := ⟨f, w.edges_subset_edgeSet hf⟩
  have hfeAllowed : fe ∈ squareBoundaryFreeRectangleEdges (2 * n) n :=
    hw ((mem_walkEdgeFinset_iff w fe).mpr hf)
  rw [rswStoppedSquareEdges, Finset.mem_image]
  refine ⟨fe, hfeAllowed, ?_⟩
  apply Subtype.ext
  exact hfe

/-- A translated square crossing supplies an explicit open left--right walk in
`[0,2n] × [0,2n]`. -/
theorem exists_rswStoppedSquareCrossingWalk_of_mem
    {n : ℕ} {omega : EdgeConfiguration 2}
    (homega : omega ∈ rswStoppedSquareCrossingEvent n) :
    ∃ u v : SquareVertex, ∃ q : squareGraph.Walk u v,
      u 0 = 0 ∧ 0 ≤ u 1 ∧ u 1 ≤ 2 * (n : ℤ) ∧
      v ∈ rswStoppedSquareRightSide n ∧
      walkIsOpen omega q ∧
      walkEdgeFinset q ⊆ rswStoppedSquareEdges n ∧
      ∀ z ∈ q.support,
        0 ≤ z 0 ∧ z 0 ≤ 2 * (n : ℤ) ∧
          0 ≤ z 1 ∧ z 1 ≤ 2 * (n : ℤ) := by
  change cubicGraphIsoConfigurationPullback
      (rswStoppedSquareTranslationIso n) omega ∈ rswSquareCrossingEvent n at homega
  simp only [rswSquareCrossingEvent, rswRectangleCrossingEvent,
    squareBoundaryFreeRectangleCrossingEvent, Set.mem_iUnion] at homega
  obtain ⟨x, hx, y, hy, w, hwOpen, hwEdges⟩ := homega
  let F := rswStoppedSquareTranslationIso n
  let q := w.map F.toHom
  have hqOpen : walkIsOpen omega q := by
    apply walkIsOpen_map_cubicGraphIso F w
    simpa [F] using hwOpen
  have hqEdges : walkEdgeFinset q ⊆ rswStoppedSquareEdges n := by
    simpa [q, F] using walkEdgeFinset_map_subset_rswStoppedSquareEdges w hwEdges
  have hyRect : y ∈ squareRectangleVertices (2 * n) n :=
    (Finset.mem_filter.mp hy).1
  have hwRect : ∀ z ∈ w.support,
      z ∈ squareRectangleVertices (2 * n) n :=
    walk_support_mem_squareRectangle_of_boundaryFree_edges w hyRect hwEdges
  have hqSupport : ∀ z ∈ q.support,
      0 ≤ z 0 ∧ z 0 ≤ 2 * (n : ℤ) ∧
        0 ≤ z 1 ∧ z 1 ≤ 2 * (n : ℤ) := by
    intro z hz
    simp only [q, SimpleGraph.Walk.support_map, List.mem_map] at hz
    rcases hz with ⟨a, ha, rfl⟩
    have ha' := mem_squareRectangleVertices_iff.mp (hwRect a ha)
    change 0 ≤ F a 0 ∧ F a 0 ≤ 2 * (n : ℤ) ∧
      0 ≤ F a 1 ∧ F a 1 ≤ 2 * (n : ℤ)
    simp only [F, rswStoppedSquareTranslationIso_zero,
      rswStoppedSquareTranslationIso_one]
    omega
  have hx' := mem_squareRectangleLeft_iff.mp hx
  have hy' := mem_squareRectangleRight_iff.mp hy
  have hFx0 : F x 0 = 0 := by
    simpa only [F, rswStoppedSquareTranslationIso_zero] using hx'.1
  have hFx1Lower : 0 ≤ F x 1 := by
    simp only [F, rswStoppedSquareTranslationIso_one]
    omega
  have hFx1Upper : F x 1 ≤ 2 * (n : ℤ) := by
    simp only [F, rswStoppedSquareTranslationIso_one]
    omega
  have hFy : F y ∈ rswStoppedSquareRightSide n := by
    rw [mem_rswStoppedSquareRightSide_iff]
    simp only [F, rswStoppedSquareTranslationIso_zero,
      rswStoppedSquareTranslationIso_one]
    omega
  exact ⟨F x, F y, q, hFx0, hFx1Lower, hFx1Upper, hFy,
    hqOpen, hqEdges, hqSupport⟩

/-- Contact of a translated square crossing with the unreflected stopped tail, using the full
translated-square support. -/
def brStoppedLowerContactEvent
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    Set (EdgeConfiguration 2) :=
  ⋃ z ∈ (brFilledHullSelectedUpperTailPath hn hR).support.toFinset,
    ⋃ r ∈ rswStoppedSquareRightSide n,
      connectionEventIn 2 (rswStoppedSquareEdges n) z r

/-- Contact with the reflected half of the doubled stopped barrier. -/
def brStoppedUpperContactEvent
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    Set (EdgeConfiguration 2) :=
  ⋃ z ∈ (brReflectedFilledHullSelectedUpperTailPath hn hR).support.toFinset,
    ⋃ r ∈ rswStoppedSquareRightSide n,
      connectionEventIn 2 (rswStoppedSquareEdges n) z r

theorem measurableSet_brStoppedLowerContactEvent
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    MeasurableSet (brStoppedLowerContactEvent hn hR) := by
  unfold brStoppedLowerContactEvent
  apply (brFilledHullSelectedUpperTailPath hn hR).support.toFinset.measurableSet_biUnion
  intro z hz
  apply (rswStoppedSquareRightSide n).measurableSet_biUnion
  intro r hr
  exact (dependsOn_connectionEventIn 2 (rswStoppedSquareEdges n) z r).measurableSet

theorem measurableSet_brStoppedUpperContactEvent
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    MeasurableSet (brStoppedUpperContactEvent hn hR) := by
  unfold brStoppedUpperContactEvent
  apply (brReflectedFilledHullSelectedUpperTailPath hn hR).support.toFinset.measurableSet_biUnion
  intro z hz
  apply (rswStoppedSquareRightSide n).measurableSet_biUnion
  intro r hr
  exact (dependsOn_connectionEventIn 2 (rswStoppedSquareEdges n) z r).measurableSet

theorem isIncreasingEvent_brStoppedLowerContactEvent
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    IsIncreasingEvent (brStoppedLowerContactEvent hn hR) := by
  intro omega eta hmono
  simp only [brStoppedLowerContactEvent, Set.mem_iUnion, List.mem_toFinset]
  rintro ⟨z, hz, r, hr, hzr⟩
  exact ⟨z, hz, r, hr,
    isIncreasingEvent_connectionEventIn 2 (rswStoppedSquareEdges n) z r hmono hzr⟩

theorem isIncreasingEvent_brStoppedUpperContactEvent
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    IsIncreasingEvent (brStoppedUpperContactEvent hn hR) := by
  intro omega eta hmono
  simp only [brStoppedUpperContactEvent, Set.mem_iUnion, List.mem_toFinset]
  rintro ⟨z, hz, r, hr, hzr⟩
  exact ⟨z, hz, r, hr,
    isIncreasingEvent_connectionEventIn 2 (rswStoppedSquareEdges n) z r hmono hzr⟩

/-- Reflection across `y = n` exchanges contact with the stopped lower tail and contact with
its reflected upper copy. -/
theorem cubicGraphIsoEvent_brStoppedLowerContactEvent_eq_upper
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    cubicGraphIsoEvent (brPrimalTopReflectionIso n)
        (brStoppedLowerContactEvent hn hR) =
      brStoppedUpperContactEvent hn hR := by
  let F := brPrimalTopReflectionIso n
  ext omega
  change cubicGraphIsoConfigurationPullback F omega ∈
      brStoppedLowerContactEvent hn hR ↔
    omega ∈ brStoppedUpperContactEvent hn hR
  simp only [brStoppedLowerContactEvent, brStoppedUpperContactEvent,
    Set.mem_iUnion, List.mem_toFinset]
  constructor
  · rintro ⟨z, hz, r, hr, hzr⟩
    have hzr' :=
      (cubicGraphIsoConfigurationPullback_mem_connectionEventIn_iff F
        (rswStoppedSquareEdges n) omega z r).mp hzr
    rw [brPrimalTopReflectionIso_image_rswStoppedSquareEdges] at hzr'
    refine ⟨F z, ?_, F r, ?_, hzr'⟩
    · rw [mem_brReflectedFilledHullSelectedUpperTailPath_support_iff]
      simpa only [F, brPrimalTopReflectionIso_involutive] using hz
    · exact (brPrimalTopReflectionIso_mem_rswStoppedSquareRightSide_iff n r).2 hr
  · rintro ⟨z, hz, r, hr, hzr⟩
    refine ⟨F z, ?_, F r, ?_, ?_⟩
    · exact (mem_brReflectedFilledHullSelectedUpperTailPath_support_iff hn hR).mp hz
    · apply (brPrimalTopReflectionIso_mem_rswStoppedSquareRightSide_iff n
          (F r)).1
      simpa only [F, brPrimalTopReflectionIso_involutive] using hr
    · apply (cubicGraphIsoConfigurationPullback_mem_connectionEventIn_iff F
        (rswStoppedSquareEdges n) omega (F z) (F r)).mpr
      rw [brPrimalTopReflectionIso_image_rswStoppedSquareEdges]
      simpa only [F, brPrimalTopReflectionIso_involutive] using hzr

theorem bernoulliBondMeasure_real_brStoppedUpperContactEvent_eq_lower
    (p : I) {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    (bernoulliBondMeasure 2 p).real (brStoppedUpperContactEvent hn hR) =
      (bernoulliBondMeasure 2 p).real
        (brStoppedLowerContactEvent hn hR) := by
  rw [← cubicGraphIsoEvent_brStoppedLowerContactEvent_eq_upper hn hR]
  exact bernoulliBondMeasure_real_cubicGraphIsoEvent p _
    (measurableSet_brStoppedLowerContactEvent hn hR)

/-- Incidence with the doubled barrier gives one of the two full-support contact events. -/
theorem rswStoppedSquareCrossingEvent_subset_contact_union
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    rswStoppedSquareCrossingEvent n ⊆
      brStoppedLowerContactEvent hn hR ∪ brStoppedUpperContactEvent hn hR := by
  intro omega homega
  obtain ⟨u, v, q, hu0, _hu1Lower, _hu1Upper, hv,
      hqOpen, hqEdges, hqSupport⟩ :=
    exists_rswStoppedSquareCrossingWalk_of_mem homega
  have hv' := mem_rswStoppedSquareRightSide_iff.mp hv
  obtain ⟨z, hzq, hzBarrier⟩ :=
    squareWalk_support_inter_brFilledHullStoppedBarrier hn hR q hu0 hv'.1 hqSupport
  have hzqReverse : z ∈ q.reverse.support := by
    simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hzq
  let arm := (q.reverse.takeUntil z hzqReverse).reverse
  have harmOpen : walkIsOpen omega arm := by
    apply walkIsOpen_reverse
    apply walkIsOpen_of_edges_subset (walkIsOpen_reverse hqOpen)
    exact q.reverse.edges_takeUntil_subset hzqReverse
  have harmEdges : walkEdgeFinset arm ⊆ rswStoppedSquareEdges n := by
    intro e he
    rw [mem_walkEdgeFinset_iff, SimpleGraph.Walk.edges_reverse,
      List.mem_reverse] at he
    have heReverse : (e : Sym2 SquareVertex) ∈ q.reverse.edges :=
      q.reverse.edges_takeUntil_subset hzqReverse he
    rw [SimpleGraph.Walk.edges_reverse, List.mem_reverse] at heReverse
    exact hqEdges ((mem_walkEdgeFinset_iff q e).mpr heReverse)
  have hzv : omega ∈ connectionEventIn 2 (rswStoppedSquareEdges n) z v :=
    ⟨arm, harmOpen, harmEdges⟩
  rw [mem_brFilledHullStoppedBarrier_support_iff hn hR] at hzBarrier
  simp only [Set.mem_union, brStoppedLowerContactEvent,
    brStoppedUpperContactEvent, Set.mem_iUnion, List.mem_toFinset]
  rcases hzBarrier with hzLower | hzUpper
  · exact Or.inl ⟨z, hzLower, v, hv, hzv⟩
  · exact Or.inr ⟨z, hzUpper, v, hv, hzv⟩

/-- The square-root lower bound for contact with a prescribed half of the stopped barrier. -/
theorem one_sub_sqrt_rswSquare_le_brStoppedLowerContactProbability
    (p : I) {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    1 - Real.sqrt (1 - rswSquareCrossingProbability p n) ≤
      (bernoulliBondMeasure 2 p).real
        (brStoppedLowerContactEvent hn hR) := by
  rw [← bernoulliBondMeasure_real_rswStoppedSquareCrossingEvent p n]
  exact one_sub_sqrt_one_sub_measureReal_le_of_subset_union_of_eq (d := 2) p
    (H := rswStoppedSquareCrossingEvent n)
    (L := brStoppedLowerContactEvent hn hR)
    (U := brStoppedUpperContactEvent hn hR)
    (rswStoppedSquareCrossingEvent_subset_contact_union hn hR)
    (bernoulliBondMeasure_real_brStoppedUpperContactEvent_eq_lower p hn hR)
    (isIncreasingEvent_brStoppedLowerContactEvent hn hR)
    (isIncreasingEvent_brStoppedUpperContactEvent hn hR)
    (measurableSet_brStoppedLowerContactEvent hn hR)
    (measurableSet_brStoppedUpperContactEvent hn hR)

end

end Percolation
