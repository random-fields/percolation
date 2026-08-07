import Percolation.Planar.RSWStoppedFresh

/-!
# Tail contact events for Grimmett's lowest-crossing argument

The contact event used in the final gluing step of Grimmett, Lemma 11.73 must end on the
stopped upper tail of the selected interface.  Contact with an arbitrary earlier visit of the
full selected interface is insufficient when the lowest crossing revisits the axis.  This file
records the source-faithful events `M_π⁻` and `M_π⁺`, their exact reflection symmetry, and the
unconditional square-root estimate.
-/

namespace Percolation

open SimpleGraph MeasureTheory ProbabilityTheory
open scoped unitInterval

noncomputable section

/-- A stopped-square arm from the selected upper tail to the right side. -/
def brStoppedLowerTailContactEvent
    {n : ℕ} (R : Finset (BRLeftmostDualVertex n))
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    Set (EdgeConfiguration 2) :=
  ⋃ z ∈ (brFilledHullSelectedUpperTailPath hn hR).support.toFinset,
    ⋃ r ∈ rswStoppedSquareRightSide n,
      connectionEventIn 2 (rswStoppedSquareEdges n) z r

/-- The reflected stopped-tail contact event. -/
def brStoppedUpperTailContactEvent
    {n : ℕ} (R : Finset (BRLeftmostDualVertex n))
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    Set (EdgeConfiguration 2) :=
  cubicGraphIsoEvent (brPrimalTopReflectionIso n)
    (brStoppedLowerTailContactEvent R hn hR)

theorem measurableSet_brStoppedLowerTailContactEvent
    {n : ℕ} (R : Finset (BRLeftmostDualVertex n))
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    MeasurableSet (brStoppedLowerTailContactEvent R hn hR) := by
  apply (brFilledHullSelectedUpperTailPath hn hR).support.toFinset.measurableSet_biUnion
  intro z _hz
  apply (rswStoppedSquareRightSide n).measurableSet_biUnion
  intro r _hr
  exact (dependsOn_connectionEventIn 2 (rswStoppedSquareEdges n) z r).measurableSet

theorem isIncreasingEvent_brStoppedLowerTailContactEvent
    {n : ℕ} (R : Finset (BRLeftmostDualVertex n))
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    IsIncreasingEvent (brStoppedLowerTailContactEvent R hn hR) := by
  intro omega eta hmono
  simp only [brStoppedLowerTailContactEvent, Set.mem_iUnion]
  rintro ⟨z, hz, r, hr, hzr⟩
  exact ⟨z, hz, r, hr,
    isIncreasingEvent_connectionEventIn 2 (rswStoppedSquareEdges n) z r hmono hzr⟩

theorem measurableSet_brStoppedUpperTailContactEvent
    {n : ℕ} (R : Finset (BRLeftmostDualVertex n))
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    MeasurableSet (brStoppedUpperTailContactEvent R hn hR) :=
  measurableSet_cubicGraphIsoEvent _
    (measurableSet_brStoppedLowerTailContactEvent R hn hR)

theorem isIncreasingEvent_brStoppedUpperTailContactEvent
    {n : ℕ} (R : Finset (BRLeftmostDualVertex n))
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    IsIncreasingEvent (brStoppedUpperTailContactEvent R hn hR) :=
  isIncreasingEvent_cubicGraphIsoEvent _
    (isIncreasingEvent_brStoppedLowerTailContactEvent R hn hR)

theorem bernoulliBondMeasure_real_brStoppedUpperTailContactEvent_eq_lower
    (p : I) {n : ℕ} (R : Finset (BRLeftmostDualVertex n))
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    (bernoulliBondMeasure 2 p).real (brStoppedUpperTailContactEvent R hn hR) =
      (bernoulliBondMeasure 2 p).real (brStoppedLowerTailContactEvent R hn hR) :=
  bernoulliBondMeasure_real_cubicGraphIsoEvent p _
    (measurableSet_brStoppedLowerTailContactEvent R hn hR)

/-- Every translated square crossing meets the stopped tail or its reflected copy.  Retaining
the part of the crossing between that contact and the right side gives one of the two literal
tail-contact events. -/
theorem rswStoppedSquareCrossingEvent_subset_tailContact_union
    {n : ℕ} (R : Finset (BRLeftmostDualVertex n))
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    rswStoppedSquareCrossingEvent n ⊆
      brStoppedLowerTailContactEvent R hn hR ∪
        brStoppedUpperTailContactEvent R hn hR := by
  classical
  intro omega homega
  obtain ⟨u, v, q, hu, _huLower, _huUpper, hv,
      hqOpen, _hqEdges, hqSupport⟩ :=
    exists_rswStoppedSquareCrossingWalk_of_mem homega
  have hv' := mem_rswStoppedSquareRightSide_iff.mp hv
  obtain ⟨z, hzq, hzBarrier⟩ :=
    squareWalk_support_inter_brFilledHullStoppedBarrier
      hn hR q hu hv'.1 hqSupport
  have hzReverse : z ∈ q.reverse.support := by
    simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hzq
  let arm : squareGraph.Walk v z := q.reverse.takeUntil z hzReverse
  have harmOpen : walkIsOpen omega arm :=
    walkIsOpen_of_edges_subset (walkIsOpen_reverse hqOpen)
      (q.reverse.edges_takeUntil_subset hzReverse)
  have harmEdges : walkEdgeFinset arm ⊆ rswStoppedSquareEdges n := by
    intro e he
    rw [mem_walkEdgeFinset_iff] at he
    have heReverse : (e : Sym2 SquareVertex) ∈ q.reverse.edges :=
      q.reverse.edges_takeUntil_subset hzReverse he
    simp only [SimpleGraph.Walk.edges_reverse, List.mem_reverse] at heReverse
    exact _hqEdges ((mem_walkEdgeFinset_iff q e).mpr heReverse)
  have hzr : omega ∈ connectionEventIn 2 (rswStoppedSquareEdges n) z v := by
    refine ⟨arm.reverse, walkIsOpen_reverse harmOpen, ?_⟩
    intro e he
    rw [mem_walkEdgeFinset_iff, SimpleGraph.Walk.edges_reverse,
      List.mem_reverse] at he
    exact harmEdges ((mem_walkEdgeFinset_iff arm e).mpr he)
  rw [mem_brFilledHullStoppedBarrier_support_iff hn hR] at hzBarrier
  rcases hzBarrier with hzLower | hzUpper
  · left
    simp only [brStoppedLowerTailContactEvent, Set.mem_iUnion, List.mem_toFinset]
    exact ⟨z, hzLower, v, hv, hzr⟩
  · right
    change cubicGraphIsoConfigurationPullback
        (brPrimalTopReflectionIso n) omega ∈
      brStoppedLowerTailContactEvent R hn hR
    simp only [brStoppedLowerTailContactEvent, Set.mem_iUnion, List.mem_toFinset]
    refine ⟨brPrimalTopReflectionIso n z,
      (mem_brReflectedFilledHullSelectedUpperTailPath_support_iff hn hR).mp hzUpper,
      brPrimalTopReflectionIso n v, ?_, ?_⟩
    · rw [mem_rswStoppedSquareRightSide_iff]
      simp only [brPrimalTopReflectionIso_zero, brPrimalTopReflectionIso_one]
      omega
    · rw [cubicGraphIsoConfigurationPullback_mem_connectionEventIn_iff,
        brPrimalTopReflectionIso_image_rswStoppedSquareEdges,
        brPrimalTopReflectionIso_involutive,
        brPrimalTopReflectionIso_involutive]
      exact hzr

/-- The literal lower tail-contact event has the same square-root lower bound as in Grimmett's
definition of `M_π⁻`. -/
theorem one_sub_sqrt_rswSquare_le_brStoppedLowerTailContactProbability
    (p : I) {n : ℕ} (R : Finset (BRLeftmostDualVertex n))
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    1 - Real.sqrt (1 - rswSquareCrossingProbability p n) ≤
      (bernoulliBondMeasure 2 p).real
        (brStoppedLowerTailContactEvent R hn hR) := by
  rw [← bernoulliBondMeasure_real_rswStoppedSquareCrossingEvent p n]
  exact one_sub_sqrt_one_sub_measureReal_le_of_subset_union_of_eq (d := 2) p
    (H := rswStoppedSquareCrossingEvent n)
    (L := brStoppedLowerTailContactEvent R hn hR)
    (U := brStoppedUpperTailContactEvent R hn hR)
    (rswStoppedSquareCrossingEvent_subset_tailContact_union R hn hR)
    (bernoulliBondMeasure_real_brStoppedUpperTailContactEvent_eq_lower p R hn hR)
    (isIncreasingEvent_brStoppedLowerTailContactEvent R hn hR)
    (isIncreasingEvent_brStoppedUpperTailContactEvent R hn hR)
    (measurableSet_brStoppedLowerTailContactEvent R hn hR)
    (measurableSet_brStoppedUpperTailContactEvent R hn hR)

/-! ### The placed three-halves rectangle -/

/-- The target `3n × 2n` crossing after the quarter-turn used by the stopped exploration. -/
def rswStoppedThreeHalvesVerticalCrossingEvent (n : ℕ) :
    Set (EdgeConfiguration 2) :=
  cubicGraphIsoEvent (brSquareQuarterTurnIso n)
    (rswThreeHalvesCrossingEvent n)

/-- Boundary-free bonds in the quarter-turned `3n × 2n` target rectangle. -/
def rswStoppedThreeHalvesVerticalEdges (n : ℕ) : Finset SquareEdge :=
  (squareBoundaryFreeRectangleEdges (3 * n) n).image
    (brSquareQuarterTurnIso n).mapEdgeSet

theorem measurableSet_rswStoppedThreeHalvesVerticalCrossingEvent (n : ℕ) :
    MeasurableSet (rswStoppedThreeHalvesVerticalCrossingEvent n) :=
  measurableSet_cubicGraphIsoEvent _
    (measurableSet_rswThreeHalvesCrossingEvent n)

theorem bernoulliBondMeasure_real_rswStoppedThreeHalvesVerticalCrossingEvent
    (p : I) (n : ℕ) :
    (bernoulliBondMeasure 2 p).real
        (rswStoppedThreeHalvesVerticalCrossingEvent n) =
      rswThreeHalvesCrossingProbability p n := by
  unfold rswStoppedThreeHalvesVerticalCrossingEvent
    rswThreeHalvesCrossingProbability
  exact bernoulliBondMeasure_real_cubicGraphIsoEvent p _
    (measurableSet_rswThreeHalvesCrossingEvent n)

/-- Enlarging a centered rectangle to the right preserves its boundary-free edge set. -/
theorem squareBoundaryFreeRectangleEdges_mono_width
    {m M n : ℕ} (hmM : m ≤ M) :
    squareBoundaryFreeRectangleEdges m n ⊆
      squareBoundaryFreeRectangleEdges M n := by
  classical
  intro e he
  rw [squareBoundaryFreeRectangleEdges, Finset.mem_filter] at he ⊢
  have hendsSmall := (Finset.mem_filter.mp he.1).2
  have hendsLarge :
      e.1.out.1 ∈ squareRectangleVertices M n ∧
        e.1.out.2 ∈ squareRectangleVertices M n := by
    constructor
    · rw [mem_squareRectangleVertices_iff]
      have h := mem_squareRectangleVertices_iff.mp hendsSmall.1
      omega
    · rw [mem_squareRectangleVertices_iff]
      have h := mem_squareRectangleVertices_iff.mp hendsSmall.2
      omega
  refine ⟨?_, ?_⟩
  · rw [squareRectangleEdges, Finset.mem_filter]
    refine ⟨mem_cubicBoxEdges_of_endpoints (fun z hz ↦ ?_), hendsLarge⟩
    rw [← e.1.out_eq, Sym2.mem_iff] at hz
    rcases hz with rfl | rfl
    · exact mem_cubicMetricBox_max_of_mem_squareRectangleVertices hendsLarge.1
    · exact mem_cubicMetricBox_max_of_mem_squareRectangleVertices hendsLarge.2
  · intro hboundary
    apply he.2
    constructor
    · have hs := mem_squareRectangleVertices_iff.mp hendsSmall.1
      have hM := hboundary.1
      unfold squareRectangleBoundaryVertex at hM ⊢
      omega
    · have hs := mem_squareRectangleVertices_iff.mp hendsSmall.2
      have hM := hboundary.2
      unfold squareRectangleBoundaryVertex at hM ⊢
      omega

/-- The selected centered square is contained in the placed three-halves target support. -/
theorem squareBoundaryFreeRectangleEdges_subset_rswStoppedThreeHalvesVerticalEdges
    (n : ℕ) :
    squareBoundaryFreeRectangleEdges (2 * n) n ⊆
      rswStoppedThreeHalvesVerticalEdges n := by
  classical
  intro e he
  rw [rswStoppedThreeHalvesVerticalEdges, Finset.mem_image]
  let F := brSquareQuarterTurnIso n
  have hFeSmall : F.mapEdgeSet e ∈
      squareBoundaryFreeRectangleEdges (2 * n) n := by
    rw [← brSquareQuarterTurnIso_image_boundaryFreeRectangleEdges n]
    exact Finset.mem_image.mpr ⟨e, he, rfl⟩
  refine ⟨F.mapEdgeSet e,
    squareBoundaryFreeRectangleEdges_mono_width
      (show 2 * n ≤ 3 * n by omega) hFeSmall, ?_⟩
  apply Subtype.ext
  change Sym2.map F (Sym2.map F (e : Sym2 SquareVertex)) =
    (e : Sym2 SquareVertex)
  rw [Sym2.map_map]
  calc
    Sym2.map (F ∘ F) (e : Sym2 SquareVertex) =
        Sym2.map id (e : Sym2 SquareVertex) :=
      congrArg (fun f : SquareVertex → SquareVertex ↦
        Sym2.map f (e : Sym2 SquareVertex)) (funext fun z ↦
          brSquareQuarterTurnIso_involutive n z)
    _ = (e : Sym2 SquareVertex) := by rw [Sym2.map_id]; rfl

private theorem mappedStoppedSquareEdge_mem_threeHalves
    {n : ℕ} (hn : 0 < n) {f : SquareEdge}
    (hf : f ∈ squareBoundaryFreeRectangleEdges (2 * n) n) :
    (brSquareQuarterTurnIso n).mapEdgeSet
        ((rswStoppedSquareTranslationIso n).mapEdgeSet f) ∈
      squareBoundaryFreeRectangleEdges (3 * n) n := by
  classical
  let F : squareGraph ≃g squareGraph :=
    (rswStoppedSquareTranslationIso n).trans (brSquareQuarterTurnIso n)
  have hF0 (x : SquareVertex) : F x 0 = x 1 + 2 * (n : ℤ) := by
    simp [F]
    ring
  have hF1 (x : SquareVertex) : F x 1 = x 0 - (n : ℤ) := by
    simp [F]
  have hmap : F.mapEdgeSet f =
      (brSquareQuarterTurnIso n).mapEdgeSet
        ((rswStoppedSquareTranslationIso n).mapEdgeSet f) := by
    apply Subtype.ext
    change Sym2.map F (f : Sym2 SquareVertex) =
      Sym2.map (brSquareQuarterTurnIso n)
        (Sym2.map (rswStoppedSquareTranslationIso n) (f : Sym2 SquareVertex))
    rw [Sym2.map_map]
    rfl
  rw [← hmap, squareBoundaryFreeRectangleEdges, Finset.mem_filter]
  rw [squareBoundaryFreeRectangleEdges, Finset.mem_filter] at hf
  have hmappedRect : ∀ z ∈ (F.mapEdgeSet f : Sym2 SquareVertex),
      z ∈ squareRectangleVertices (3 * n) n := by
    intro z hz
    change z ∈ Sym2.map F (f : Sym2 SquareVertex) at hz
    rw [Sym2.mem_map] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    have hx' := mem_squareRectangleVertices_iff.mp
      (endpoint_mem_squareRectangle_of_edge_mem hf.1 hx)
    rw [mem_squareRectangleVertices_iff]
    change 0 ≤ F x 0 ∧ F x 0 ≤ 3 * (n : ℤ) ∧
      -(n : ℤ) ≤ F x 1 ∧ F x 1 ≤ (n : ℤ)
    rw [hF0, hF1]
    omega
  refine ⟨?_, ?_⟩
  · rw [squareRectangleEdges, Finset.mem_filter]
    refine ⟨mem_cubicBoxEdges_of_endpoints (fun z hz ↦ ?_),
      hmappedRect _ (Sym2.out_fst_mem _),
      hmappedRect _ (Sym2.out_snd_mem _)⟩
    exact mem_cubicMetricBox_max_of_mem_squareRectangleVertices
      (hmappedRect z hz)
  · intro hboundary
    apply hf.2
    have hmappedBoundary : ∀ z ∈ (F.mapEdgeSet f : Sym2 SquareVertex),
        squareRectangleBoundaryVertex (3 * n) n z := by
      intro z hz
      rw [← (F.mapEdgeSet f).1.out_eq, Sym2.mem_iff] at hz
      exact hz.elim (fun h ↦ h ▸ hboundary.1) (fun h ↦ h ▸ hboundary.2)
    have hsourceBoundary : ∀ x ∈ (f : Sym2 SquareVertex),
        squareRectangleBoundaryVertex (2 * n) n x := by
      intro x hx
      have hx' := mem_squareRectangleVertices_iff.mp
        (endpoint_mem_squareRectangle_of_edge_mem hf.1 hx)
      have htarget := hmappedBoundary (F x)
        (Sym2.mem_map.mpr ⟨x, hx, rfl⟩)
      unfold squareRectangleBoundaryVertex at htarget ⊢
      rw [hF0, hF1] at htarget
      omega
    exact ⟨hsourceBoundary f.1.out.1 (Sym2.out_fst_mem _),
      hsourceBoundary f.1.out.2 (Sym2.out_snd_mem _)⟩

/-- The translated stopped square is also contained in the placed target support. -/
theorem rswStoppedSquareEdges_subset_rswStoppedThreeHalvesVerticalEdges
    {n : ℕ} (hn : 0 < n) :
    rswStoppedSquareEdges n ⊆ rswStoppedThreeHalvesVerticalEdges n := by
  classical
  intro e he
  rw [rswStoppedSquareEdges, Finset.mem_image] at he
  obtain ⟨f, hf, rfl⟩ := he
  rw [rswStoppedThreeHalvesVerticalEdges, Finset.mem_image]
  let F := brSquareQuarterTurnIso n
  let e := (rswStoppedSquareTranslationIso n).mapEdgeSet f
  refine ⟨F.mapEdgeSet e, mappedStoppedSquareEdge_mem_threeHalves hn hf, ?_⟩
  apply Subtype.ext
  change Sym2.map F (Sym2.map F (e : Sym2 SquareVertex)) =
    (e : Sym2 SquareVertex)
  rw [Sym2.map_map]
  calc
    Sym2.map (F ∘ F) (e : Sym2 SquareVertex) =
        Sym2.map id (e : Sym2 SquareVertex) :=
      congrArg (fun f : SquareVertex → SquareVertex ↦
        Sym2.map f (e : Sym2 SquareVertex)) (funext fun z ↦
          brSquareQuarterTurnIso_involutive n z)
    _ = (e : Sym2 SquareVertex) := by rw [Sym2.map_id]; rfl

private theorem endpoint_coordinates_of_mem_rswStoppedSquareEdges
    {n : ℕ} {e : SquareEdge} (he : e ∈ rswStoppedSquareEdges n)
    {x : SquareVertex} (hx : x ∈ (e : Sym2 SquareVertex)) :
    0 ≤ x 0 ∧ x 0 ≤ 2 * (n : ℤ) ∧
      0 ≤ x 1 ∧ x 1 ≤ 2 * (n : ℤ) := by
  rw [rswStoppedSquareEdges, Finset.mem_image] at he
  obtain ⟨f, hf, rfl⟩ := he
  change x ∈ Sym2.map (rswStoppedSquareTranslationIso n)
    (f : Sym2 SquareVertex) at hx
  rw [Sym2.mem_map] at hx
  obtain ⟨z, hz, rfl⟩ := hx
  have hz' := mem_squareRectangleVertices_iff.mp
    (endpoint_mem_squareRectangle_of_edge_mem
      (Finset.mem_filter.mp hf).1 hz)
  simp only [rswStoppedSquareTranslationIso_zero,
    rswStoppedSquareTranslationIso_one]
  omega

private theorem walk_support_coordinates_of_rswStoppedSquareEdges
    {n : ℕ} {u v : SquareVertex} (w : squareGraph.Walk u v)
    (hv : 0 ≤ v 0 ∧ v 0 ≤ 2 * (n : ℤ) ∧
      0 ≤ v 1 ∧ v 1 ≤ 2 * (n : ℤ))
    (hw : walkEdgeFinset w ⊆ rswStoppedSquareEdges n) :
    ∀ x ∈ w.support,
      0 ≤ x 0 ∧ x 0 ≤ 2 * (n : ℤ) ∧
        0 ≤ x 1 ∧ x 1 ≤ 2 * (n : ℤ) := by
  intro x hx
  rw [SimpleGraph.Walk.mem_support_iff_exists_mem_edges] at hx
  rcases hx with rfl | ⟨e, he, hxe⟩
  · exact hv
  · let ee : SquareEdge := ⟨e, w.edges_subset_edgeSet he⟩
    exact endpoint_coordinates_of_mem_rswStoppedSquareEdges
      (hw ((mem_walkEdgeFinset_iff w ee).mpr he)) hxe

private theorem walkEdgeFinset_append_subset_local
    {u v w : SquareVertex} {p : squareGraph.Walk u v}
    {q : squareGraph.Walk v w} {E : Finset SquareEdge}
    (hp : walkEdgeFinset p ⊆ E) (hq : walkEdgeFinset q ⊆ E) :
    walkEdgeFinset (p.append q) ⊆ E := by
  intro e he
  rw [mem_walkEdgeFinset_iff, SimpleGraph.Walk.edges_append,
    List.mem_append] at he
  exact he.elim (fun he' ↦ hp ((mem_walkEdgeFinset_iff p e).mpr he'))
    (fun he' ↦ hq ((mem_walkEdgeFinset_iff q e).mpr he'))

private theorem exists_openSquareWalk_between_support_local
    {ω : EdgeConfiguration 2} {u v x y : SquareVertex}
    (w : squareGraph.Walk u v) (hwOpen : walkIsOpen ω w)
    (hx : x ∈ w.support) (hy : y ∈ w.support) :
    ∃ q : squareGraph.Walk x y,
      walkIsOpen ω q ∧ walkEdgeFinset q ⊆ walkEdgeFinset w := by
  let q := (w.takeUntil x hx).reverse.append (w.takeUntil y hy)
  refine ⟨q, ?_, ?_⟩
  · apply walkIsOpen_append
    · exact walkIsOpen_reverse
        (walkIsOpen_of_edges_subset hwOpen (w.edges_takeUntil_subset hx))
    · exact walkIsOpen_of_edges_subset hwOpen (w.edges_takeUntil_subset hy)
  · apply walkEdgeFinset_append_subset_local
    · intro e he
      rw [mem_walkEdgeFinset_iff, SimpleGraph.Walk.edges_reverse,
        List.mem_reverse] at he
      exact (mem_walkEdgeFinset_iff w e).mpr
        (w.edges_takeUntil_subset hx he)
    · intro e he
      rw [mem_walkEdgeFinset_iff] at he
      exact (mem_walkEdgeFinset_iff w e).mpr
        (w.edges_takeUntil_subset hy he)

private theorem mem_rswStoppedThreeHalvesVerticalCrossingEvent_of_connection
    {n : ℕ} {omega : EdgeConfiguration 2} {a d : SquareVertex}
    (ha0 : 0 ≤ a 0) (ha2 : a 0 ≤ 2 * (n : ℤ))
    (ha1 : a 1 = -(n : ℤ))
    (hd0 : 0 ≤ d 0) (hd2 : d 0 ≤ 2 * (n : ℤ))
    (hd1 : d 1 = 2 * (n : ℤ))
    (had : omega ∈ connectionEventIn 2
      (rswStoppedThreeHalvesVerticalEdges n) a d) :
    omega ∈ rswStoppedThreeHalvesVerticalCrossingEvent n := by
  let F := brSquareQuarterTurnIso n
  change cubicGraphIsoConfigurationPullback F omega ∈
    rswThreeHalvesCrossingEvent n
  simp only [rswThreeHalvesCrossingEvent,
    squareBoundaryFreeRectangleCrossingEvent, Set.mem_iUnion]
  refine ⟨F a, ?_, F d, ?_, ?_⟩
  · rw [mem_squareRectangleLeft_iff]
    simp only [F, brSquareQuarterTurnIso_zero,
      brSquareQuarterTurnIso_one]
    omega
  · rw [mem_squareRectangleRight_iff]
    simp only [F, brSquareQuarterTurnIso_zero,
      brSquareQuarterTurnIso_one]
    omega
  · apply (cubicGraphIsoConfigurationPullback_mem_connectionEventIn_iff
      F (squareBoundaryFreeRectangleEdges (3 * n) n) omega (F a) (F d)).mpr
    simpa only [rswStoppedThreeHalvesVerticalEdges, F,
      brSquareQuarterTurnIso_involutive] using had

/-! ### Ordered boundary incidence for the final gluing -/

/-- If a walk starts on the bottom side weakly to the left of a bottom--top walk and exits
through the right side, then the two walks meet.  The bottom--top walk is normalized to have no
other bottom-side visit.  The proof extends the first walk to the lower-left corner; the order of
the two bottom endpoints rules out a spurious intersection on that deterministic extension. -/
theorem squareWalk_support_inter_of_ordered_bottom_right_and_bottom_top
    {m : ℕ} {c r b t : SquareVertex}
    (hc0 : 0 ≤ c 0) (hcm : c 0 ≤ (m : ℤ)) (hc1 : c 1 = 0)
    (hr0 : r 0 = (m : ℤ)) (hr1 : 0 ≤ r 1) (hrm : r 1 ≤ (m : ℤ))
    (hb0 : 0 ≤ b 0) (hbm : b 0 ≤ (m : ℤ)) (hb1 : b 1 = 0)
    (ht0 : 0 ≤ t 0) (htm : t 0 ≤ (m : ℤ)) (ht1 : t 1 = (m : ℤ))
    (hcb : c 0 ≤ b 0)
    (p : squareGraph.Walk c r)
    (q : squareGraph.Walk b t)
    (hpbox : ∀ z ∈ p.support,
      0 ≤ z 0 ∧ z 0 ≤ (m : ℤ) ∧ 0 ≤ z 1 ∧ z 1 ≤ (m : ℤ))
    (hqbox : ∀ z ∈ q.support,
      0 ≤ z 0 ∧ z 0 ≤ (m : ℤ) ∧ 0 ≤ z 1 ∧ z 1 ≤ (m : ℤ))
    (hqBottom : ∀ z ∈ q.support, z 1 = 0 → z = b) :
    ∃ z, z ∈ p.support ∧ z ∈ q.support := by
  let leftRaw := cubicWalkFrom (squareVertex 0 0)
    (List.replicate (c 0).toNat ((0 : Fin 2), true))
  have hcCast : ((c 0).toNat : ℤ) = c 0 := Int.toNat_of_nonneg hc0
  let left : squareGraph.Walk (squareVertex 0 0) c := leftRaw.copy rfl (by
    rw [cubicEndpointFrom_replicate_pos]
    ext i
    fin_cases i
    · simp [squareVertex, hcCast, cubicOrigin]
    · simp [squareVertex, hc1, cubicOrigin])
  let P := left.append p
  let P' : squareGraph.Walk (squareVertex 0 0)
      (squareVertex (m : ℤ) (r 1)) := P.copy rfl (by
        ext i
        fin_cases i <;> simp [P, squareVertex, hr0])
  let Q' : squareGraph.Walk (squareVertex (b 0) 0)
      (squareVertex (t 0) (m : ℤ)) := q.copy (by
        ext i
        fin_cases i <;> simp [squareVertex, hb1]) (by
        ext i
        fin_cases i <;> simp [squareVertex, ht1])
  have hleftBox : ∀ z ∈ left.support,
      0 ≤ z 0 ∧ z 0 ≤ (m : ℤ) ∧ 0 ≤ z 1 ∧ z 1 ≤ (m : ℤ) := by
    intro z hz
    have hzRaw : z ∈ cubicVerticesFrom (squareVertex 0 0)
        (List.replicate (c 0).toNat ((0 : Fin 2), true)) := by
      simpa [left, leftRaw, SimpleGraph.Walk.support_copy, cubicWalkFrom_support] using hz
    have hz0 := cubicVerticesFrom_replicate_pos_coord_between
      (squareVertex 0 0) (0 : Fin 2) (c 0).toNat hzRaw
    have hz1 := cubicVerticesFrom_replicate_pos_coord_eq_of_ne
      (squareVertex 0 0) (0 : Fin 2) (1 : Fin 2) (c 0).toNat (by decide) hzRaw
    simp only [squareVertex] at hz0 hz1
    omega
  have hPbox : ∀ z ∈ P'.support,
      0 ≤ z 0 ∧ z 0 ≤ (m : ℤ) ∧ 0 ≤ z 1 ∧ z 1 ≤ (m : ℤ) := by
    intro z hz
    simp only [P', SimpleGraph.Walk.support_copy, P,
      SimpleGraph.Walk.mem_support_append_iff] at hz
    exact hz.elim (hleftBox z) (hpbox z)
  have hQbox : ∀ z ∈ Q'.support,
      0 ≤ z 0 ∧ z 0 ≤ (m : ℤ) ∧ 0 ≤ z 1 ∧ z 1 ≤ (m : ℤ) := by
    intro z hz
    exact hqbox z (by simpa [Q'] using hz)
  obtain ⟨z, hzP, hzQ⟩ :=
    squareWalk_support_inter_of_left_right_and_bottom_top_of_le_int
      (le_refl m) (by omega) (by omega) hr1 hrm hb0 hbm ht0 htm P' Q' hPbox hQbox
  have hzQ' : z ∈ q.support := by simpa [Q'] using hzQ
  have hzP' : z ∈ left.support ∨ z ∈ p.support := by
    simpa [P', P, SimpleGraph.Walk.mem_support_append_iff] using hzP
  rcases hzP' with hzLeft | hzP
  · have hzRaw : z ∈ cubicVerticesFrom (squareVertex 0 0)
        (List.replicate (c 0).toNat ((0 : Fin 2), true)) := by
      simpa [left, leftRaw, SimpleGraph.Walk.support_copy, cubicWalkFrom_support] using hzLeft
    have hz0 := cubicVerticesFrom_replicate_pos_coord_between
      (squareVertex 0 0) (0 : Fin 2) (c 0).toNat hzRaw
    have hz1 := cubicVerticesFrom_replicate_pos_coord_eq_of_ne
      (squareVertex 0 0) (0 : Fin 2) (1 : Fin 2) (c 0).toNat (by decide) hzRaw
    simp only [squareVertex] at hz0 hz1
    have hzb : z = b := hqBottom z hzQ' (by omega)
    have hbc : b = c := by
      have hbc0 : b 0 ≤ c 0 := by
        rw [← hzb]
        simpa [hcCast] using hz0.2
      have hbc0' : b 0 = c 0 := le_antisymm hbc0 hcb
      ext i
      fin_cases i
      · exact hbc0'
      · simp [hb1, hc1]
    exact ⟨c, p.start_mem_support, hbc ▸ q.start_mem_support⟩
  · exact ⟨z, hzP, hzQ'⟩

/-! ### Source-faithful deterministic gluing -/

/-- On a left-last-midline stopped fiber, contact with the literal stopped tail and a clean
right-half bottom--top crossing produce the quarter-turned `3n × 2n` crossing. -/
theorem inter_fiber_tailContact_endpoint_subset_stoppedThreeHalves
    {n : ℕ} (hn : 0 < n) (R : Finset (BRLeftmostDualVertex n))
    (hR : BRAdmissibleSeparatingFiber n R)
    (hleft : BRFilledHullLastMidlineLeft hn hR) :
    brReachableFaceFiber n R ∩ brStoppedLowerTailContactEvent R hn hR ∩
        rswStoppedRightBottomVerticalCrossingEvent n ⊆
      rswStoppedThreeHalvesVerticalCrossingEvent n := by
  classical
  intro omega homega
  rcases homega with ⟨⟨homegaFiber, homegaContact⟩, homegaEndpoint⟩
  simp only [brStoppedLowerTailContactEvent, Set.mem_iUnion,
    List.mem_toFinset] at homegaContact
  obtain ⟨z, hzTail, r, hr, wr, hwrOpen, hwrEdges⟩ := homegaContact
  obtain ⟨b, t, q, hbn, hb2, hb1, ht0, ht2, ht1,
      hqOpen, _hqPath, hqEdges, hqBottom, _hqTop, _hqInterior⟩ :=
    exists_normalized_rswStoppedRightBottomVerticalPath_of_mem homegaEndpoint
  let c := brFilledHullLastMidlineVertex hn hR
  let tail := brFilledHullSelectedUpperTailPath hn hR
  have hcCoords := brFilledHullLastMidlineVertex_coordinates hn hR
  have hrCoords := mem_rswStoppedSquareRightSide_iff.mp hr
  have hzReverse : z ∈ tail.reverse.support := by
    simpa only [tail, SimpleGraph.Walk.support_reverse, List.mem_reverse] using hzTail
  let tailToZ := tail.reverse.takeUntil z hzReverse
  let p := tailToZ.append wr
  have htailOpen : walkIsOpen omega tail :=
    walkIsOpen_brFilledHullSelectedUpperTailPath_of_mem_fiber hn hR homegaFiber
  have htailToZOpen : walkIsOpen omega tailToZ := by
    apply walkIsOpen_of_edges_subset (walkIsOpen_reverse htailOpen)
    exact tail.reverse.edges_takeUntil_subset hzReverse
  have hpOpen : walkIsOpen omega p :=
    walkIsOpen_append htailToZOpen hwrOpen
  have htailBox : ∀ x ∈ tail.reverse.support,
      0 ≤ x 0 ∧ x 0 ≤ 2 * (n : ℤ) ∧
        0 ≤ x 1 ∧ x 1 ≤ 2 * (n : ℤ) := by
    intro x hx
    have hxTail : x ∈ tail.support := by
      simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hx
    have hxSelected := brFilledHullSelectedUpperTailPath_support_subset_selected
      hn hR x hxTail
    have hxCoords := brSelectedPrimalWalk_support_coordinates
      hn hR.filledHull hxSelected
    have hxNonnegative := brFilledHullSelectedUpperTailPath_support_nonnegative
      hn hR hxTail
    omega
  have hwrBox : ∀ x ∈ wr.support,
      0 ≤ x 0 ∧ x 0 ≤ 2 * (n : ℤ) ∧
        0 ≤ x 1 ∧ x 1 ≤ 2 * (n : ℤ) :=
    walk_support_coordinates_of_rswStoppedSquareEdges wr
      ⟨by omega, by omega, hrCoords.2.1, hrCoords.2.2⟩ hwrEdges
  have hpBox : ∀ x ∈ p.support,
      0 ≤ x 0 ∧ x 0 ≤ 2 * (n : ℤ) ∧
        0 ≤ x 1 ∧ x 1 ≤ 2 * (n : ℤ) := by
    intro x hx
    simp only [p, SimpleGraph.Walk.mem_support_append_iff] at hx
    rcases hx with hx | hx
    · exact htailBox x
        (tail.reverse.support_takeUntil_subset_support hzReverse hx)
    · exact hwrBox x hx
  have hqBox : ∀ x ∈ q.support,
      0 ≤ x 0 ∧ x 0 ≤ 2 * (n : ℤ) ∧
        0 ≤ x 1 ∧ x 1 ≤ 2 * (n : ℤ) :=
    walk_support_coordinates_of_rswStoppedSquareEdges q
      ⟨ht0, ht2, by omega, by omega⟩ hqEdges
  obtain ⟨s, hsP, hsQ⟩ :=
    squareWalk_support_inter_of_ordered_bottom_right_and_bottom_top
      (m := 2 * n)
      hcCoords.1 hcCoords.2.1 hcCoords.2.2
      hrCoords.1 hrCoords.2.1 hrCoords.2.2
      (by omega) hb2 hb1 ht0 ht2 ht1
      (by
        change brFilledHullLastMidlineVertex hn hR 0 ≤ b 0
        exact hleft.trans hbn) p q hpBox hqBox hqBottom
  have htailEdges : walkEdgeFinset tail ⊆
      squareBoundaryFreeRectangleEdges (2 * n) n := by
    simpa only [tail] using
      walkEdgeFinset_brFilledHullSelectedUpperTailPath_subset_boundaryFree hn hR
  have htailToZEdges : walkEdgeFinset tailToZ ⊆
      rswStoppedThreeHalvesVerticalEdges n :=
    (walkEdgeFinset_takeUntil_subset tail.reverse hzReverse).trans
      ((walkEdgeFinset_reverse_subset tail).trans
        (htailEdges.trans
          (squareBoundaryFreeRectangleEdges_subset_rswStoppedThreeHalvesVerticalEdges n)))
  have hwrTarget : walkEdgeFinset wr ⊆
      rswStoppedThreeHalvesVerticalEdges n :=
    hwrEdges.trans
      (rswStoppedSquareEdges_subset_rswStoppedThreeHalvesVerticalEdges hn)
  have hpTarget : walkEdgeFinset p ⊆
      rswStoppedThreeHalvesVerticalEdges n :=
    walkEdgeFinset_append_subset_local htailToZEdges hwrTarget
  obtain ⟨ps, hpsOpen, hpsEdges⟩ :=
    exists_openSquareWalk_between_support_local p hpOpen
      p.start_mem_support hsP
  obtain ⟨qs, hqsOpen, hqsEdges⟩ :=
    exists_openSquareWalk_between_support_local q hqOpen hsQ q.end_mem_support
  let selected := brSelectedPrimalWalk hn hR.filledHull
  have hcSelected : c ∈ selected.support := by
    simpa only [c, selected] using brFilledHullLastMidlineVertex_mem_selected hn hR
  let bottomToC := selected.takeUntil c hcSelected
  have hselectedOpen : walkIsOpen omega selected :=
    walkIsOpen_brSelectedPrimalWalk_filledHull_of_mem_fiber hn hR homegaFiber
  have hbottomToCOpen : walkIsOpen omega bottomToC :=
    walkIsOpen_of_edges_subset hselectedOpen
      (selected.edges_takeUntil_subset hcSelected)
  have hselectedTarget : walkEdgeFinset selected ⊆
      rswStoppedThreeHalvesVerticalEdges n :=
    (walkEdgeFinset_brSelectedPrimalWalk_subset_boundaryFree hn hR.filledHull).trans
      (squareBoundaryFreeRectangleEdges_subset_rswStoppedThreeHalvesVerticalEdges n)
  have hbottomToCTarget : walkEdgeFinset bottomToC ⊆
      rswStoppedThreeHalvesVerticalEdges n :=
    (walkEdgeFinset_takeUntil_subset selected hcSelected).trans hselectedTarget
  have hpsTarget : walkEdgeFinset ps ⊆
      rswStoppedThreeHalvesVerticalEdges n := hpsEdges.trans hpTarget
  have hqsTarget : walkEdgeFinset qs ⊆
      rswStoppedThreeHalvesVerticalEdges n :=
    hqsEdges.trans (hqEdges.trans
      (rswStoppedSquareEdges_subset_rswStoppedThreeHalvesVerticalEdges hn))
  let W := (bottomToC.append ps).append qs
  have hWOpen : walkIsOpen omega W :=
    walkIsOpen_append (walkIsOpen_append hbottomToCOpen hpsOpen) hqsOpen
  have hWEdges : walkEdgeFinset W ⊆
      rswStoppedThreeHalvesVerticalEdges n :=
    walkEdgeFinset_append_subset_local
      (walkEdgeFinset_append_subset_local hbottomToCTarget hpsTarget) hqsTarget
  have ha := mem_brSquareBottomSide_iff.mp
    (brSelectedBottomPrimalVertex_mem_bottomSide hn hR.filledHull)
  apply mem_rswStoppedThreeHalvesVerticalCrossingEvent_of_connection
    ha.1 ha.2.1 ha.2.2 ht0 ht2 ht1
  exact ⟨W, hWOpen, hWEdges⟩

end

end Percolation
