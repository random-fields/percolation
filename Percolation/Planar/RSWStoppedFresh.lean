import Percolation.Planar.RSWStoppedEndpoint
import Percolation.Planar.BROuterInterface
import Percolation.Planar.BRFiberExtensionProbability

/-!
# Fresh contact events inside the stopped RSW square

The outer-interface parity theorem applies to a crossing trimmed at its first contact with the
entire doubled selected interface.  Starting from the smaller translated RSW square retains the
small square support, while the parity theorem removes every coordinate queried by the stopped
fiber.  This is the finite-support replacement for the informal conditioning step in
Grimmett's Lemma 11.73.
-/

namespace Percolation

open SimpleGraph MeasureTheory ProbabilityTheory
open scoped unitInterval

noncomputable section

set_option maxHeartbeats 800000

/-- Genuinely fresh bonds which also lie in the translated stopped square. -/
def rswStoppedFreshEdges
    (n : ℕ) (R : Finset (BRLeftmostDualVertex n)) : Finset SquareEdge :=
  rswStoppedSquareEdges n ∩ brFreshExtensionEdges (2 * n) n R

theorem rswStoppedFreshEdges_subset_freshExtensionEdges
    (n : ℕ) (R : Finset (BRLeftmostDualVertex n)) :
    rswStoppedFreshEdges n R ⊆ brFreshExtensionEdges (2 * n) n R := by
  intro e he
  exact (Finset.mem_inter.mp he).2

/-- Reflection in the horizontal midline preserves the stopped fresh support. -/
theorem brPrimalTopReflectionIso_image_rswStoppedFreshEdges
    (n : ℕ) (R : Finset (BRLeftmostDualVertex n)) :
    (rswStoppedFreshEdges n R).image
        (brPrimalTopReflectionIso n).mapEdgeSet =
      rswStoppedFreshEdges n R := by
  classical
  apply Finset.eq_of_subset_of_card_le
  · intro e he
    rw [Finset.mem_image] at he
    obtain ⟨f, hf, rfl⟩ := he
    rw [rswStoppedFreshEdges, Finset.mem_inter] at hf ⊢
    constructor
    · rw [← brPrimalTopReflectionIso_image_rswStoppedSquareEdges n]
      exact Finset.mem_image.mpr ⟨f, hf.1, rfl⟩
    · rw [← brPrimalTopReflectionIso_image_freshExtensionEdges (2 * n) n R]
      exact Finset.mem_image.mpr ⟨f, hf.2, rfl⟩
  · rw [Finset.card_image_of_injective _
      (brPrimalTopReflectionIso n).mapEdgeSet.injective]

theorem rswStoppedSquareEdges_subset_brExtensionRectangleEdges (n : ℕ) :
    rswStoppedSquareEdges n ⊆ brExtensionRectangleEdges (2 * n) n := by
  classical
  intro e he
  rw [rswStoppedSquareEdges, Finset.mem_image] at he
  obtain ⟨f, hf, rfl⟩ := he
  rw [brExtensionRectangleEdges, Finset.mem_map]
  refine ⟨f, ?_, ?_⟩
  · exact squareBoundaryFreeRectangleEdges_mono_centered_height
      (show n ≤ 2 * n by omega) hf
  · apply Subtype.ext
    rfl

/-- A fresh stopped-square arm from the selected lower interface to the right side. -/
def brStoppedLowerFreshContactEvent
    {n : ℕ} (R : Finset (BRLeftmostDualVertex n))
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    Set (EdgeConfiguration 2) :=
  ⋃ z ∈ (brSelectedPrimalWalk hn hR.filledHull).support.toFinset,
    ⋃ r ∈ rswStoppedSquareRightSide n,
      connectionEventIn 2 (rswStoppedFreshEdges n (brFilledReachableHull n R)) z r

/-- The upper stopped-square fresh contact event, by exact reflection. -/
def brStoppedUpperFreshContactEvent
    {n : ℕ} (R : Finset (BRLeftmostDualVertex n))
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    Set (EdgeConfiguration 2) :=
  cubicGraphIsoEvent (brPrimalTopReflectionIso n)
    (brStoppedLowerFreshContactEvent R hn hR)

theorem measurableSet_brStoppedLowerFreshContactEvent
    {n : ℕ} (R : Finset (BRLeftmostDualVertex n))
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    MeasurableSet (brStoppedLowerFreshContactEvent R hn hR) := by
  apply (brSelectedPrimalWalk hn hR.filledHull).support.toFinset.measurableSet_biUnion
  intro z _hz
  apply (rswStoppedSquareRightSide n).measurableSet_biUnion
  intro r _hr
  exact (dependsOn_connectionEventIn 2
    (rswStoppedFreshEdges n (brFilledReachableHull n R)) z r).measurableSet

theorem isIncreasingEvent_brStoppedLowerFreshContactEvent
    {n : ℕ} (R : Finset (BRLeftmostDualVertex n))
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    IsIncreasingEvent (brStoppedLowerFreshContactEvent R hn hR) := by
  intro omega eta hmono
  simp only [brStoppedLowerFreshContactEvent, Set.mem_iUnion]
  rintro ⟨z, hz, r, hr, hzr⟩
  exact ⟨z, hz, r, hr,
    isIncreasingEvent_connectionEventIn 2 _ z r hmono hzr⟩

/-- The lower stopped contact event reads only the stopped fresh coordinates. -/
theorem dependsOn_brStoppedLowerFreshContactEvent
    {n : ℕ} (R : Finset (BRLeftmostDualVertex n))
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    DependsOn (rswStoppedFreshEdges n (brFilledReachableHull n R))
      (brStoppedLowerFreshContactEvent R hn hR) := by
  intro omega eta hagree
  simp only [brStoppedLowerFreshContactEvent, Set.mem_iUnion]
  constructor
  · rintro ⟨z, hz, r, hr, hzr⟩
    exact ⟨z, hz, r, hr,
      (dependsOn_connectionEventIn 2
        (rswStoppedFreshEdges n (brFilledReachableHull n R)) z r hagree).mp hzr⟩
  · rintro ⟨z, hz, r, hr, hzr⟩
    exact ⟨z, hz, r, hr,
      (dependsOn_connectionEventIn 2
        (rswStoppedFreshEdges n (brFilledReachableHull n R)) z r hagree).mpr hzr⟩

theorem measurableSet_brStoppedUpperFreshContactEvent
    {n : ℕ} (R : Finset (BRLeftmostDualVertex n))
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    MeasurableSet (brStoppedUpperFreshContactEvent R hn hR) :=
  measurableSet_cubicGraphIsoEvent _
    (measurableSet_brStoppedLowerFreshContactEvent R hn hR)

theorem isIncreasingEvent_brStoppedUpperFreshContactEvent
    {n : ℕ} (R : Finset (BRLeftmostDualVertex n))
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    IsIncreasingEvent (brStoppedUpperFreshContactEvent R hn hR) :=
  isIncreasingEvent_cubicGraphIsoEvent _
    (isIncreasingEvent_brStoppedLowerFreshContactEvent R hn hR)

theorem bernoulliBondMeasure_real_brStoppedUpperFreshContactEvent_eq_lower
    (p : I) {n : ℕ} (R : Finset (BRLeftmostDualVertex n))
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    (bernoulliBondMeasure 2 p).real (brStoppedUpperFreshContactEvent R hn hR) =
      (bernoulliBondMeasure 2 p).real (brStoppedLowerFreshContactEvent R hn hR) :=
  bernoulliBondMeasure_real_cubicGraphIsoEvent p _
    (measurableSet_brStoppedLowerFreshContactEvent R hn hR)

/-- Trimming a stopped-square crossing at its first contact with the whole doubled filled
interface leaves an arm supported on genuinely fresh bonds. -/
theorem rswStoppedSquareCrossingEvent_subset_freshContact_union
    {n : ℕ} (R : Finset (BRLeftmostDualVertex n))
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    rswStoppedSquareCrossingEvent n ⊆
      brStoppedLowerFreshContactEvent R hn hR ∪
        brStoppedUpperFreshContactEvent R hn hR := by
  classical
  intro omega homega
  obtain ⟨u, v, q, hu0, _hu1Lower, _hu1Upper, hv,
      hqOpen, hqEdges, hqSupport⟩ :=
    exists_rswStoppedSquareCrossingWalk_of_mem homega
  have hv' := mem_rswStoppedSquareRightSide_iff.mp hv
  obtain ⟨z0, hz0q, hz0Stopped⟩ :=
    squareWalk_support_inter_brFilledHullStoppedBarrier
      hn hR q hu0 hv'.1 hqSupport
  have hz0Doubled : z0 ∈
      (brDoubledSelectedPrimalWalk hn hR.filledHull).support :=
    brFilledHullStoppedBarrier_support_subset_doubledSelected
      hn hR z0 hz0Stopped
  let barrier : Finset SquareVertex :=
    (brDoubledSelectedPrimalWalk hn hR.filledHull).support.toFinset
  let war := q.reverse
  have hinter : {t ∈ barrier | t ∈ war.support}.Nonempty := by
    refine ⟨z0, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
    · exact List.mem_toFinset.mpr hz0Doubled
    · simpa [war] using hz0q
  obtain ⟨z, hzBarrier, hzWar, hzFirst⟩ :=
    war.exists_mem_support_forall_mem_support_imp_eq barrier hinter
  have hzDoubled : z ∈
      (brDoubledSelectedPrimalWalk hn hR.filledHull).support :=
    List.mem_toFinset.mp hzBarrier
  let arm : squareGraph.Walk v z := war.takeUntil z hzWar
  let path : squareGraph.Walk v z := arm.toPath
  have harmOpen : walkIsOpen omega arm :=
    walkIsOpen_of_edges_subset (walkIsOpen_reverse hqOpen)
      (war.edges_takeUntil_subset hzWar)
  have hpathOpen : walkIsOpen omega path :=
    walkIsOpen_toPath arm harmOpen
  have hpathStopped : walkEdgeFinset path ⊆ rswStoppedSquareEdges n := by
    intro e he
    rw [mem_walkEdgeFinset_iff] at he
    have heArm : (e : Sym2 SquareVertex) ∈ arm.edges :=
      arm.edges_toPath_subset he
    have heWar : (e : Sym2 SquareVertex) ∈ war.edges :=
      war.edges_takeUntil_subset hzWar heArm
    simp only [war, SimpleGraph.Walk.edges_reverse, List.mem_reverse] at heWar
    exact hqEdges ((mem_walkEdgeFinset_iff q e).mpr heWar)
  have hvExtension : v ∈ brExtensionRectangleRightSide (2 * n) n := by
    rw [mem_brExtensionRectangleRightSide_iff]
    exact ⟨hv'.1, by omega, by omega⟩
  have hpathExtension : walkEdgeFinset path ⊆
      brExtensionRectangleEdges (2 * n) n :=
    hpathStopped.trans (rswStoppedSquareEdges_subset_brExtensionRectangleEdges n)
  have hfirstPath : ∀ t ∈
      (brDoubledSelectedPrimalWalk hn hR.filledHull).support,
      t ∈ path.support → t = z := by
    intro t htDoubled htPath
    apply hzFirst t (List.mem_toFinset.mpr htDoubled)
    exact arm.support_toPath_subset htPath
  have hdisjoint : Disjoint (walkEdgeFinset path)
      (brSymmetricReachableFaceFiberSupport n (brFilledReachableHull n R)) :=
    brFirstContactPath_edges_disjoint_symmetricFilledHullSupport
      (2 * n) le_rfl hn hR hvExtension hzDoubled path
        arm.toPath.property hpathExtension hfirstPath
  have hpathFreshExtension : walkEdgeFinset path ⊆
      brFreshExtensionEdges (2 * n) n (brFilledReachableHull n R) := by
    intro e he
    rw [brFreshExtensionEdges, Finset.mem_sdiff]
    exact ⟨hpathExtension he, fun heQueried ↦
      Finset.disjoint_left.mp hdisjoint he heQueried⟩
  have hpathFresh : walkEdgeFinset path ⊆
      rswStoppedFreshEdges n (brFilledReachableHull n R) := by
    intro e he
    rw [rswStoppedFreshEdges, Finset.mem_inter]
    exact ⟨hpathStopped he, hpathFreshExtension he⟩
  have hreverseFresh : walkEdgeFinset path.reverse ⊆
      rswStoppedFreshEdges n (brFilledReachableHull n R) := by
    intro e he
    rw [mem_walkEdgeFinset_iff, SimpleGraph.Walk.edges_reverse,
      List.mem_reverse] at he
    exact hpathFresh ((mem_walkEdgeFinset_iff path e).mpr he)
  have hzv : omega ∈ connectionEventIn 2
      (rswStoppedFreshEdges n (brFilledReachableHull n R)) z v :=
    ⟨path.reverse, walkIsOpen_reverse hpathOpen, hreverseFresh⟩
  rw [brDoubledSelectedPrimalWalk_support_iff] at hzDoubled
  rcases hzDoubled with hzLower | hzUpper
  · left
    simp only [brStoppedLowerFreshContactEvent, Set.mem_iUnion,
      List.mem_toFinset]
    exact ⟨z, hzLower, v, hv, hzv⟩
  · right
    change cubicGraphIsoConfigurationPullback
        (brPrimalTopReflectionIso n) omega ∈
      brStoppedLowerFreshContactEvent R hn hR
    simp only [brStoppedLowerFreshContactEvent, Set.mem_iUnion,
      List.mem_toFinset]
    refine ⟨brPrimalTopReflectionIso n z,
      (brReflectedSelectedPrimalWalk_support_iff hn hR.filledHull).1 hzUpper,
      brPrimalTopReflectionIso n v, ?_, ?_⟩
    · rw [mem_rswStoppedSquareRightSide_iff]
      simp only [brPrimalTopReflectionIso_zero,
        brPrimalTopReflectionIso_one]
      omega
    · rw [cubicGraphIsoConfigurationPullback_mem_connectionEventIn_iff,
        brPrimalTopReflectionIso_image_rswStoppedFreshEdges,
        brPrimalTopReflectionIso_involutive,
        brPrimalTopReflectionIso_involutive]
      exact hzv

/-- Square-root lower bound for the genuinely fresh stopped contact event. -/
theorem one_sub_sqrt_rswSquare_le_brStoppedLowerFreshContactProbability
    (p : I) {n : ℕ} (R : Finset (BRLeftmostDualVertex n))
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    1 - Real.sqrt (1 - rswSquareCrossingProbability p n) ≤
      (bernoulliBondMeasure 2 p).real
        (brStoppedLowerFreshContactEvent R hn hR) := by
  rw [← bernoulliBondMeasure_real_rswStoppedSquareCrossingEvent p n]
  exact one_sub_sqrt_one_sub_measureReal_le_of_subset_union_of_eq (d := 2) p
    (H := rswStoppedSquareCrossingEvent n)
    (L := brStoppedLowerFreshContactEvent R hn hR)
    (U := brStoppedUpperFreshContactEvent R hn hR)
    (rswStoppedSquareCrossingEvent_subset_freshContact_union R hn hR)
    (bernoulliBondMeasure_real_brStoppedUpperFreshContactEvent_eq_lower p R hn hR)
    (isIncreasingEvent_brStoppedLowerFreshContactEvent R hn hR)
    (isIncreasingEvent_brStoppedUpperFreshContactEvent R hn hR)
    (measurableSet_brStoppedLowerFreshContactEvent R hn hR)
    (measurableSet_brStoppedUpperFreshContactEvent R hn hR)

/-- Exact per-fiber factorization of the lower stopped fresh contact event. -/
theorem bernoulliBondMeasure_real_brReachableFaceFiber_inter_stoppedFreshContact_eq_mul
    (p : I) {n : ℕ} (R : Finset (BRLeftmostDualVertex n))
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    (bernoulliBondMeasure 2 p).real
        (brReachableFaceFiber n R ∩ brStoppedLowerFreshContactEvent R hn hR) =
      (bernoulliBondMeasure 2 p).real (brReachableFaceFiber n R) *
        (bernoulliBondMeasure 2 p).real
          (brStoppedLowerFreshContactEvent R hn hR) := by
  have hsupport : rswStoppedFreshEdges n (brFilledReachableHull n R) ⊆
      brFreshExtensionEdges (2 * n) n R :=
    (rswStoppedFreshEdges_subset_freshExtensionEdges n
      (brFilledReachableHull n R)).trans
        (brFreshExtensionEdges_anti (2 * n)
          (subset_brFilledReachableHull hR.2))
  exact bernoulliBondMeasure_real_brReachableFaceFiber_inter_fresh_eq_mul
    p (2 * n) n R
      ((dependsOn_brStoppedLowerFreshContactEvent R hn hR).mono hsupport)

/-- Ratio-free lower estimate on every admissible stopped fiber. -/
theorem one_sub_sqrt_rswSquare_mul_fiber_le_inter_stoppedFreshContact
    (p : I) {n : ℕ} (R : Finset (BRLeftmostDualVertex n))
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    (1 - Real.sqrt (1 - rswSquareCrossingProbability p n)) *
        (bernoulliBondMeasure 2 p).real (brReachableFaceFiber n R) ≤
      (bernoulliBondMeasure 2 p).real
        (brReachableFaceFiber n R ∩
          brStoppedLowerFreshContactEvent R hn hR) := by
  rw [bernoulliBondMeasure_real_brReachableFaceFiber_inter_stoppedFreshContact_eq_mul]
  calc
    (1 - Real.sqrt (1 - rswSquareCrossingProbability p n)) *
          (bernoulliBondMeasure 2 p).real (brReachableFaceFiber n R) ≤
        (bernoulliBondMeasure 2 p).real
            (brStoppedLowerFreshContactEvent R hn hR) *
          (bernoulliBondMeasure 2 p).real (brReachableFaceFiber n R) :=
      mul_le_mul_of_nonneg_right
        (one_sub_sqrt_rswSquare_le_brStoppedLowerFreshContactProbability
          p R hn hR) measureReal_nonneg
    _ = (bernoulliBondMeasure 2 p).real (brReachableFaceFiber n R) *
          (bernoulliBondMeasure 2 p).real
            (brStoppedLowerFreshContactEvent R hn hR) := mul_comm _ _

end

end Percolation
