import Percolation.Planar.BRFiberExtensionProbability
import Percolation.Planar.BRFirstContact
import Percolation.Planar.BROuterInterface
import Percolation.Planar.BRTruncatedCrossing

/-!
# Conditional Bollobás--Riordan crossing extension

This module assembles the probability inequality in Bollobás--Riordan Lemma 6 from the stopped
dual-fiber decomposition and a direct fresh-cover premise.  For each realizable exploration
fiber, the premise says that every doubled-rectangle crossing belongs to one of the two reflected
fresh extension events.  This is the exact geometric conclusion supplied by a correct canonical
outer-frontier argument.

The premise is required only for realizable good fibers.  The finite partition also contains
empty candidate fibers; a private totalization by the universal event lets the abstract fiber
assembler range over all indices without asserting that those empty fibers are admissible.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval

noncomputable section

/-- Totalize the lower fresh event across the full finite candidate-fiber index set. -/
private def brLowerFreshExtensionEventOrUniv
    (m n : ℕ) (hn : 0 < n) (R : Finset (BRLeftmostDualVertex n)) :
    Set (EdgeConfiguration 2) := by
  classical
  exact if hR : BRAdmissibleSeparatingFiber n R then
      brLowerFreshExtensionEvent m R hn hR
    else
      Set.univ

/-- Totalize the filled-hull lower fresh event across the full candidate-fiber index set. -/
private def brFilledHullLowerFreshExtensionEventOrUniv
    (m n : ℕ) (hn : 0 < n) (R : Finset (BRLeftmostDualVertex n)) :
    Set (EdgeConfiguration 2) := by
  classical
  exact if hR : BRAdmissibleSeparatingFiber n R then
      brLowerFreshExtensionEvent m (brFilledReachableHull n R) hn hR.filledHull
    else
      Set.univ

/-- Unconditional Bollobas--Riordan Lemma 6 from the filled outer interface.  The event used on
the fiber for `R` is supported on the fresh bonds left after filling all complementary holes.
Those bonds form a subset of the bonds fresh for `R`, so the original fiber-independence
assembler applies unchanged. -/
theorem brExtensionCrossingProbability_mul_rswSquare_div_two_le_sourceX_filledHull
    (p : I) (m n : ℕ) (hm : 2 * n ≤ m) (hn : 0 < n) :
    ((bernoulliBondMeasure 2 p).real (brExtensionRectangleCrossingEvent m n) *
        rswSquareCrossingProbability p n) / 2 ≤
      (bernoulliBondMeasure 2 p).real (brSourceXEvent m n) := by
  classical
  let Y : Finset (BRLeftmostDualVertex n) → Set (EdgeConfiguration 2) :=
    brFilledHullLowerFreshExtensionEventOrUniv m n hn
  have hcore :
      ((bernoulliBondMeasure 2 p).real (brExtensionRectangleCrossingEvent m n) / 2) *
          rswSquareCrossingProbability p n ≤
        (bernoulliBondMeasure 2 p).real (brSourceXEvent m n) := by
    apply brFiberExtensionProbability_mul_rswSquare_le_sourceX_of_event_eq p m n Y
    · intro R _hgood
      by_cases hR : BRAdmissibleSeparatingFiber n R
      · have hsubsetFresh : brFreshExtensionEdges m n (brFilledReachableHull n R) ⊆
            brFreshExtensionEdges m n R :=
          brFreshExtensionEdges_anti m (subset_brFilledReachableHull hR.2)
        simpa only [Y, brFilledHullLowerFreshExtensionEventOrUniv, dif_pos hR] using
          (dependsOn_brLowerFreshExtensionEvent m (brFilledReachableHull n R)
            hn hR.filledHull).mono hsubsetFresh
      · simpa only [Y, brFilledHullLowerFreshExtensionEventOrUniv, dif_neg hR] using
          dependsOn_univ (brFreshExtensionEdges m n R)
    · intro R _hgood
      by_cases hR : BRAdmissibleSeparatingFiber n R
      · simpa only [Y, brFilledHullLowerFreshExtensionEventOrUniv, dif_pos hR] using
          bernoulliBondMeasure_real_extensionCrossing_div_two_le_lowerFresh_of_fresh_cover
            p m (brFilledReachableHull n R) hn hR.filledHull
              (brExtensionRectangleCrossingEvent_subset_filledHull_fresh_union
                m hm hn hR)
      · simp only [Y, brFilledHullLowerFreshExtensionEventOrUniv, dif_neg hR,
          probReal_univ]
        have hnonneg : 0 ≤ (bernoulliBondMeasure 2 p).real
            (brExtensionRectangleCrossingEvent m n) := measureReal_nonneg
        have hle : (bernoulliBondMeasure 2 p).real
            (brExtensionRectangleCrossingEvent m n) ≤ 1 := measureReal_le_one
        linarith
    · intro omega homega
      simp only [Set.mem_iUnion, Set.mem_inter_iff] at homega
      rcases homega with ⟨R, hgood, hfiber, hY⟩
      have hR : BRAdmissibleSeparatingFiber n R :=
        brAdmissibleSeparatingFiber_of_mem_good_of_mem_fiber hgood hfiber
      apply inter_fiber_brLowerFreshExtensionEvent_filledHull_subset_brSourceXEvent
        m R hn hR
      refine ⟨hfiber, ?_⟩
      simpa only [Y, brFilledHullLowerFreshExtensionEventOrUniv, dif_pos hR] using hY
    · exact brRightTargetsUnreachedEvent_eq_brSquareVerticalCrossingEvent hn
  calc
    ((bernoulliBondMeasure 2 p).real (brExtensionRectangleCrossingEvent m n) *
          rswSquareCrossingProbability p n) / 2 =
        ((bernoulliBondMeasure 2 p).real (brExtensionRectangleCrossingEvent m n) / 2) *
          rswSquareCrossingProbability p n := by ring
    _ ≤ (bernoulliBondMeasure 2 p).real (brSourceXEvent m n) := hcore

/-- Square-root strengthening of the unconditional filled-hull extension estimate.  FKG between
the two reflected fresh-arm events upgrades the per-fiber half estimate to the exact
`1 - sqrt (1 - P(H))` bound used in Grimmett's square-root trick. -/
theorem one_sub_sqrt_extensionCrossing_mul_rswSquare_le_sourceX_filledHull
    (p : I) (m n : ℕ) (hm : 2 * n ≤ m) (hn : 0 < n) :
    (1 - Real.sqrt (1 - (bernoulliBondMeasure 2 p).real
          (brExtensionRectangleCrossingEvent m n))) *
        rswSquareCrossingProbability p n ≤
      (bernoulliBondMeasure 2 p).real (brSourceXEvent m n) := by
  classical
  let q : ℝ := 1 - Real.sqrt (1 - (bernoulliBondMeasure 2 p).real
    (brExtensionRectangleCrossingEvent m n))
  let Y : Finset (BRLeftmostDualVertex n) → Set (EdgeConfiguration 2) :=
    brFilledHullLowerFreshExtensionEventOrUniv m n hn
  apply brFiberExtensionProbability_mul_rswSquare_le_sourceX_of_uniform_lower
    p m n q Y
  · intro R _hgood
    by_cases hR : BRAdmissibleSeparatingFiber n R
    · have hsubsetFresh : brFreshExtensionEdges m n (brFilledReachableHull n R) ⊆
          brFreshExtensionEdges m n R :=
        brFreshExtensionEdges_anti m (subset_brFilledReachableHull hR.2)
      simpa only [Y, brFilledHullLowerFreshExtensionEventOrUniv, dif_pos hR] using
        (dependsOn_brLowerFreshExtensionEvent m (brFilledReachableHull n R)
          hn hR.filledHull).mono hsubsetFresh
    · simpa only [Y, brFilledHullLowerFreshExtensionEventOrUniv, dif_neg hR] using
        dependsOn_univ (brFreshExtensionEdges m n R)
  · intro R _hgood
    by_cases hR : BRAdmissibleSeparatingFiber n R
    · simpa only [q, Y, brFilledHullLowerFreshExtensionEventOrUniv, dif_pos hR] using
        one_sub_sqrt_one_sub_measureReal_le_of_subset_union_of_eq p
          (brExtensionRectangleCrossingEvent_subset_filledHull_fresh_union
            m hm hn hR)
          (bernoulliBondMeasure_real_brUpperFreshExtensionEvent_eq_lower
            p m (brFilledReachableHull n R) hn hR.filledHull)
          (isIncreasingEvent_brLowerFreshExtensionEvent
            m (brFilledReachableHull n R) hn hR.filledHull)
          (isIncreasingEvent_brUpperFreshExtensionEvent
            m (brFilledReachableHull n R) hn hR.filledHull)
          (measurableSet_brLowerFreshExtensionEvent
            m (brFilledReachableHull n R) hn hR.filledHull)
          (measurableSet_brUpperFreshExtensionEvent
            m (brFilledReachableHull n R) hn hR.filledHull)
    · simp only [Y, brFilledHullLowerFreshExtensionEventOrUniv, dif_neg hR,
        probReal_univ]
      dsimp [q]
      linarith [Real.sqrt_nonneg
        (1 - (bernoulliBondMeasure 2 p).real
          (brExtensionRectangleCrossingEvent m n))]
  · intro omega homega
    simp only [Set.mem_iUnion, Set.mem_inter_iff] at homega
    rcases homega with ⟨R, hgood, hfiber, hY⟩
    have hR : BRAdmissibleSeparatingFiber n R :=
      brAdmissibleSeparatingFiber_of_mem_good_of_mem_fiber hgood hfiber
    apply inter_fiber_brLowerFreshExtensionEvent_filledHull_subset_brSourceXEvent
      m R hn hR
    refine ⟨hfiber, ?_⟩
    simpa only [Y, brFilledHullLowerFreshExtensionEventOrUniv, dif_pos hR] using hY
  · exact brRightTargetsUnreachedEvent_eq_brSquareVerticalCrossingEvent hn

/-! ### Scale-matched source estimate

At `m = 2n`, the extension rectangle is twice as tall as the source square.  A centered
source-square crossing is still a crossing of this taller rectangle.  This elementary embedding
turns the filled-hull estimate above into the two-factor `u²` source bound used in the stopped
interface proof of Grimmett, Lemma 11.73. -/

theorem squareBoundaryFreeRectangleEdges_mono_centered_height
    {m n N : ℕ} (hnN : n ≤ N) :
    squareBoundaryFreeRectangleEdges m n ⊆
      squareBoundaryFreeRectangleEdges m N := by
  classical
  intro e he
  rw [squareBoundaryFreeRectangleEdges, Finset.mem_filter] at he ⊢
  have hendsSmall := (Finset.mem_filter.mp he.1).2
  have hendsLarge :
      e.1.out.1 ∈ squareRectangleVertices m N ∧
        e.1.out.2 ∈ squareRectangleVertices m N := by
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
      have hN := hboundary.1
      unfold squareRectangleBoundaryVertex at hN ⊢
      omega
    · have hs := mem_squareRectangleVertices_iff.mp hendsSmall.2
      have hN := hboundary.2
      unfold squareRectangleBoundaryVertex at hN ⊢
      omega

private theorem rswSquareCrossingEvent_subset_doubleHeightRectangle
    (n : ℕ) :
    rswSquareCrossingEvent n ⊆
      squareBoundaryFreeRectangleCrossingEvent (2 * n) (2 * n) := by
  intro omega homega
  change omega ∈ squareBoundaryFreeRectangleCrossingEvent (2 * n) n at homega
  simp only [squareBoundaryFreeRectangleCrossingEvent, Set.mem_iUnion] at homega ⊢
  obtain ⟨x, hx, y, hy, hxy⟩ := homega
  refine ⟨x, ?_, y, ?_, connectionEventIn_mono
    (squareBoundaryFreeRectangleEdges_mono_centered_height (show n ≤ 2 * n by omega))
      x y hxy⟩
  · rw [mem_squareRectangleLeft_iff]
    have hx' := mem_squareRectangleLeft_iff.mp hx
    omega
  · rw [mem_squareRectangleRight_iff]
    have hy' := mem_squareRectangleRight_iff.mp hy
    omega

/-- Two square-root factors already occur in the probability of the scale-matched BR source
event.  The third factor in Lemma 11.73 comes from the half-start crossing glued to the stopped
interface. -/
theorem one_sub_sqrt_rswSquare_mul_rswSquare_le_sourceX
    (p : I) (n : ℕ) (hn : 0 < n) :
    (1 - Real.sqrt (1 - rswSquareCrossingProbability p n)) *
        rswSquareCrossingProbability p n ≤
      (bernoulliBondMeasure 2 p).real (brSourceXEvent (2 * n) n) := by
  let r := rswSquareCrossingProbability p n
  let e := (bernoulliBondMeasure 2 p).real
    (brExtensionRectangleCrossingEvent (2 * n) n)
  have hre : r ≤ e := by
    dsimp [r, e, rswSquareCrossingProbability]
    rw [bernoulliBondMeasure_real_brExtensionRectangleCrossingEvent]
    exact measureReal_mono (rswSquareCrossingEvent_subset_doubleHeightRectangle n)
      (measure_ne_top _ _)
  have hr1 : r ≤ 1 := measureReal_le_one
  have he1 : e ≤ 1 := measureReal_le_one
  have hsqrt : Real.sqrt (1 - e) ≤ Real.sqrt (1 - r) :=
    Real.sqrt_le_sqrt (by linarith)
  have hfactor : 1 - Real.sqrt (1 - r) ≤ 1 - Real.sqrt (1 - e) := by
    linarith
  calc
    (1 - Real.sqrt (1 - rswSquareCrossingProbability p n)) *
          rswSquareCrossingProbability p n =
        (1 - Real.sqrt (1 - r)) * r := rfl
    _ ≤ (1 - Real.sqrt (1 - e)) * r :=
      mul_le_mul_of_nonneg_right hfactor measureReal_nonneg
    _ ≤ (bernoulliBondMeasure 2 p).real (brSourceXEvent (2 * n) n) := by
      simpa only [e, r] using
        one_sub_sqrt_extensionCrossing_mul_rswSquare_le_sourceX_filledHull
          p (2 * n) n (by omega) hn

/-- Source-normalized form of the unconditional filled-hull extension estimate. -/
theorem brLemmaSix_probability_filledHull
    (p : I) (m n : ℕ) (hm : 2 * n ≤ m) (hn : 0 < n) :
    ((bernoulliBondMeasure 2 p).real
          (squareBoundaryFreeRectangleCrossingEvent m (2 * n)) *
        rswSquareCrossingProbability p n) / 2 ≤
      (bernoulliBondMeasure 2 p).real (brSourceXEvent m n) := by
  rw [← bernoulliBondMeasure_real_brExtensionRectangleCrossingEvent p m n]
  exact brExtensionCrossingProbability_mul_rswSquare_div_two_le_sourceX_filledHull
    p m n hm hn

/-- Direct-fresh-cover probability form of the adapted Bollobás--Riordan Lemma 6.

The factor on the left is the horizontal crossing probability of the translated doubled
rectangle times the vertical square-crossing probability, divided by two.  All deterministic,
independence, finite-fiber summation, and probability steps after the direct per-fiber cover are
discharged here. -/
theorem brExtensionCrossingProbability_mul_rswSquare_div_two_le_sourceX_of_fresh_cover
    (p : I) (m n : ℕ) (hn : 0 < n)
    (hcover : ∀ (R : Finset (BRLeftmostDualVertex n))
        (_hgood : R ∈ brGoodReachableFaceFiberIndices n)
        (hR : BRAdmissibleSeparatingFiber n R),
      brExtensionRectangleCrossingEvent m n ⊆
        brLowerFreshExtensionEvent m R hn hR ∪
          brUpperFreshExtensionEvent m R hn hR) :
    ((bernoulliBondMeasure 2 p).real (brExtensionRectangleCrossingEvent m n) *
        rswSquareCrossingProbability p n) / 2 ≤
      (bernoulliBondMeasure 2 p).real (brSourceXEvent m n) := by
  classical
  let Y : Finset (BRLeftmostDualVertex n) → Set (EdgeConfiguration 2) :=
    brLowerFreshExtensionEventOrUniv m n hn
  have hcore :
      ((bernoulliBondMeasure 2 p).real (brExtensionRectangleCrossingEvent m n) / 2) *
          rswSquareCrossingProbability p n ≤
        (bernoulliBondMeasure 2 p).real (brSourceXEvent m n) := by
    apply brFiberExtensionProbability_mul_rswSquare_le_sourceX_of_event_eq p m n Y
    · intro R hgood
      by_cases hR : BRAdmissibleSeparatingFiber n R
      · simpa only [Y, brLowerFreshExtensionEventOrUniv, dif_pos hR] using
          dependsOn_brLowerFreshExtensionEvent m R hn hR
      · simpa only [Y, brLowerFreshExtensionEventOrUniv, dif_neg hR] using
          dependsOn_univ (brFreshExtensionEdges m n R)
    · intro R hgood
      by_cases hR : BRAdmissibleSeparatingFiber n R
      · simpa only [Y, brLowerFreshExtensionEventOrUniv, dif_pos hR] using
          bernoulliBondMeasure_real_extensionCrossing_div_two_le_lowerFresh_of_fresh_cover
            p m R hn hR (hcover R hgood hR)
      · simp only [Y, brLowerFreshExtensionEventOrUniv, dif_neg hR, probReal_univ]
        have hnonneg : 0 ≤ (bernoulliBondMeasure 2 p).real
            (brExtensionRectangleCrossingEvent m n) := measureReal_nonneg
        have hle : (bernoulliBondMeasure 2 p).real
            (brExtensionRectangleCrossingEvent m n) ≤ 1 := measureReal_le_one
        linarith
    · intro omega homega
      simp only [Set.mem_iUnion, Set.mem_inter_iff] at homega
      rcases homega with ⟨R, hgood, hfiber, hY⟩
      have hR : BRAdmissibleSeparatingFiber n R :=
        brAdmissibleSeparatingFiber_of_mem_good_of_mem_fiber hgood hfiber
      apply inter_fiber_brLowerFreshExtensionEvent_subset_brSourceXEvent m R hn hR
      refine ⟨hfiber, ?_⟩
      simpa only [Y, brLowerFreshExtensionEventOrUniv, dif_pos hR] using hY
    · exact brRightTargetsUnreachedEvent_eq_brSquareVerticalCrossingEvent hn
  calc
    ((bernoulliBondMeasure 2 p).real (brExtensionRectangleCrossingEvent m n) *
          rswSquareCrossingProbability p n) / 2 =
        ((bernoulliBondMeasure 2 p).real (brExtensionRectangleCrossingEvent m n) / 2) *
          rswSquareCrossingProbability p n := by ring
    _ ≤ (bernoulliBondMeasure 2 p).real (brSourceXEvent m n) := hcore

/-- Compatibility wrapper deriving the direct fresh cover from the former contact-to-fresh
premise.  The unrestricted premise has a finite counterexample and is retained only for auditing
the previously completed algebra. -/
theorem brExtensionCrossingProbability_mul_rswSquare_div_two_le_sourceX_of_contact_fresh
    (p : I) (m n : ℕ) (hm : 2 * n ≤ m) (hn : 0 < n)
    (hfresh : ∀ (R : Finset (BRLeftmostDualVertex n))
        (_hgood : R ∈ brGoodReachableFaceFiberIndices n)
        (hR : BRAdmissibleSeparatingFiber n R),
      brLowerContactEvent m hn hR ⊆ brLowerFreshExtensionEvent m R hn hR) :
    ((bernoulliBondMeasure 2 p).real (brExtensionRectangleCrossingEvent m n) *
        rswSquareCrossingProbability p n) / 2 ≤
      (bernoulliBondMeasure 2 p).real (brSourceXEvent m n) := by
  apply brExtensionCrossingProbability_mul_rswSquare_div_two_le_sourceX_of_fresh_cover
    p m n hn
  intro R hgood hR
  exact brExtensionRectangleCrossingEvent_subset_fresh_union_of_contact_fresh
    m R hm hn hR (hfresh R hgood hR)

/-- Source-normalized version of the direct-fresh-cover Bollobás--Riordan Lemma 6. -/
theorem brLemmaSix_probability_of_fresh_cover
    (p : I) (m n : ℕ) (hn : 0 < n)
    (hcover : ∀ (R : Finset (BRLeftmostDualVertex n))
        (_hgood : R ∈ brGoodReachableFaceFiberIndices n)
        (hR : BRAdmissibleSeparatingFiber n R),
      brExtensionRectangleCrossingEvent m n ⊆
        brLowerFreshExtensionEvent m R hn hR ∪
          brUpperFreshExtensionEvent m R hn hR) :
    ((bernoulliBondMeasure 2 p).real
          (squareBoundaryFreeRectangleCrossingEvent m (2 * n)) *
        rswSquareCrossingProbability p n) / 2 ≤
      (bernoulliBondMeasure 2 p).real (brSourceXEvent m n) := by
  rw [← bernoulliBondMeasure_real_brExtensionRectangleCrossingEvent p m n]
  exact brExtensionCrossingProbability_mul_rswSquare_div_two_le_sourceX_of_fresh_cover
    p m n hn hcover

/-- Source-normalized compatibility wrapper for the former contact-to-fresh scaffold. -/
theorem brLemmaSix_probability_of_contact_fresh
    (p : I) (m n : ℕ) (hm : 2 * n ≤ m) (hn : 0 < n)
    (hfresh : ∀ (R : Finset (BRLeftmostDualVertex n))
        (_hgood : R ∈ brGoodReachableFaceFiberIndices n)
        (hR : BRAdmissibleSeparatingFiber n R),
      brLowerContactEvent m hn hR ⊆ brLowerFreshExtensionEvent m R hn hR) :
    ((bernoulliBondMeasure 2 p).real
          (squareBoundaryFreeRectangleCrossingEvent m (2 * n)) *
        rswSquareCrossingProbability p n) / 2 ≤
      (bernoulliBondMeasure 2 p).real (brSourceXEvent m n) := by
  apply brLemmaSix_probability_of_fresh_cover p m n hn
  intro R hgood hR
  exact brExtensionRectangleCrossingEvent_subset_fresh_union_of_contact_fresh
    m R hm hn hR (hfresh R hgood hR)

end

end Percolation
