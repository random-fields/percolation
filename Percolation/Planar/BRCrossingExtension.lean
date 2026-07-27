import Percolation.Planar.BRFiberExtensionProbability
import Percolation.Planar.BRFirstContact
import Percolation.Planar.BRTruncatedCrossing

/-!
# Conditional Bollobás--Riordan crossing extension

This module assembles the probability inequality in Bollobás--Riordan Lemma 6 from the stopped
dual-fiber decomposition and the finite first-contact argument.  Its sole geometric premise is
the explicitly stated stopping-set implication `hfresh`: every full-support lower contact with
the selected crossing can be witnessed using coordinates outside the symmetric exploration
support.

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

/-- Conditional probability form of the adapted Bollobás--Riordan Lemma 6.

The factor on the left is the horizontal crossing probability of the translated doubled
rectangle times the vertical square-crossing probability, divided by two.  The hypothesis
`hfresh` is exactly the still-missing outermost-selector implication; all remaining deterministic,
independence, finite-fiber summation, and probability steps are discharged here. -/
theorem brExtensionCrossingProbability_mul_rswSquare_div_two_le_sourceX_of_contact_fresh
    (p : I) (m n : ℕ) (hm : 2 * n ≤ m) (hn : 0 < n)
    (hfresh : ∀ (R : Finset (BRLeftmostDualVertex n))
        (_hgood : R ∈ brGoodReachableFaceFiberIndices n)
        (hR : BRAdmissibleSeparatingFiber n R),
      brLowerContactEvent m hn hR ⊆ brLowerFreshExtensionEvent m R hn hR) :
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
          bernoulliBondMeasure_real_extensionCrossing_div_two_le_lowerFresh_of_contact_fresh
            p m R hm hn hR (hfresh R hgood hR)
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

/-- Source-normalized version of the conditional Bollobás--Riordan Lemma 6. -/
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
  rw [← bernoulliBondMeasure_real_brExtensionRectangleCrossingEvent p m n]
  exact brExtensionCrossingProbability_mul_rswSquare_div_two_le_sourceX_of_contact_fresh
    p m n hm hn hfresh

end

end Percolation
