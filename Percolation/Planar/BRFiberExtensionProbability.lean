import Percolation.Planar.BRGoodFibers
import Percolation.Planar.BRProbability
import Percolation.Planar.BRFreshSupport
import Percolation.Planar.BRSourceXEvent
import Percolation.Planar.BRVerticalSymmetry

/-!
# Probability assembly for the Bollobás--Riordan fiber extension

This module isolates the probability calculation in the adapted Bollobás--Riordan Lemma 6.
For each good stopped-exploration fiber, an extension event reads only genuinely fresh bonds.
Finite-coordinate independence therefore turns a uniform lower bound for the extension into a
ratio-free lower bound for the intersection with that fiber.  Summing over the disjoint fiber
partition gives the desired source `X`-event estimate.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval

noncomputable section

/-- A stopped-exploration fiber and an event on its fresh extension bonds factor exactly under
Bernoulli bond percolation. -/
theorem bernoulliBondMeasure_real_brReachableFaceFiber_inter_fresh_eq_mul
    (p : I) (m n : ℕ) (R : Finset (BRLeftmostDualVertex n))
    {Y : Set (EdgeConfiguration 2)}
    (hY : DependsOn (brFreshExtensionEdges m n R) Y) :
    (bernoulliBondMeasure 2 p).real (brReachableFaceFiber n R ∩ Y) =
      (bernoulliBondMeasure 2 p).real (brReachableFaceFiber n R) *
        (bernoulliBondMeasure 2 p).real Y := by
  exact bernoulliBondMeasure_real_inter_eq_mul_of_dependsOn_disjoint p
    (disjoint_brReachableFaceFiberSupport_brFreshExtensionEdges m n R)
    (dependsOn_brReachableFaceFiber n R) hY
    (measurableSet_brReachableFaceFiber n R) hY.measurableSet

/-- Abstract, ratio-free probability assembly for the adapted Bollobás--Riordan Lemma 6.

The event `Y R` may be chosen separately on each good exploration fiber.  Its only probabilistic
requirements are locality on the fresh coordinate set and the stated uniform lower bound.  The
first-contact geometry is entirely contained in `hsubset`. -/
theorem brFiberExtensionProbability_mul_unreached_le_sourceX
    (p : I) (m n : ℕ)
    (Y : Finset (BRLeftmostDualVertex n) → Set (EdgeConfiguration 2))
    (hY : ∀ R ∈ brGoodReachableFaceFiberIndices n,
      DependsOn (brFreshExtensionEdges m n R) (Y R))
    (hYlower : ∀ R ∈ brGoodReachableFaceFiberIndices n,
      (bernoulliBondMeasure 2 p).real (brExtensionRectangleCrossingEvent m n) / 2 ≤
        (bernoulliBondMeasure 2 p).real (Y R))
    (hsubset :
      (⋃ R ∈ brGoodReachableFaceFiberIndices n,
        brReachableFaceFiber n R ∩ Y R) ⊆ brSourceXEvent m n) :
    ((bernoulliBondMeasure 2 p).real (brExtensionRectangleCrossingEvent m n) / 2) *
        (bernoulliBondMeasure 2 p).real (brRightTargetsUnreachedEvent n) ≤
      (bernoulliBondMeasure 2 p).real (brSourceXEvent m n) := by
  apply mul_measureReal_brRightTargetsUnreachedEvent_le_of_fiber_extensions
    (bernoulliBondMeasure 2 p) n Y (brSourceXEvent m n)
    ((bernoulliBondMeasure 2 p).real (brExtensionRectangleCrossingEvent m n) / 2)
  · exact fun R hR ↦ (hY R hR).measurableSet
  · intro R hR
    have hfiberNonneg :
        0 ≤ (bernoulliBondMeasure 2 p).real (brReachableFaceFiber n R) :=
      measureReal_nonneg
    calc
      ((bernoulliBondMeasure 2 p).real
            (brExtensionRectangleCrossingEvent m n) / 2) *
          (bernoulliBondMeasure 2 p).real (brReachableFaceFiber n R) ≤
          (bernoulliBondMeasure 2 p).real (brReachableFaceFiber n R) *
            (bernoulliBondMeasure 2 p).real (Y R) := by
              calc
                _ ≤ (bernoulliBondMeasure 2 p).real (Y R) *
                    (bernoulliBondMeasure 2 p).real (brReachableFaceFiber n R) :=
                  mul_le_mul_of_nonneg_right (hYlower R hR) hfiberNonneg
                _ = _ := mul_comm _ _
      _ = (bernoulliBondMeasure 2 p).real
          (brReachableFaceFiber n R ∩ Y R) :=
        (bernoulliBondMeasure_real_brReachableFaceFiber_inter_fresh_eq_mul
          p m n R (hY R hR)).symm
  · exact hsubset

/-- Rewrite the good-event factor as the standard square-crossing probability once deterministic
geometry supplies equality with the vertical square-crossing event. -/
theorem brFiberExtensionProbability_mul_rswSquare_le_sourceX_of_event_eq
    (p : I) (m n : ℕ)
    (Y : Finset (BRLeftmostDualVertex n) → Set (EdgeConfiguration 2))
    (hY : ∀ R ∈ brGoodReachableFaceFiberIndices n,
      DependsOn (brFreshExtensionEdges m n R) (Y R))
    (hYlower : ∀ R ∈ brGoodReachableFaceFiberIndices n,
      (bernoulliBondMeasure 2 p).real (brExtensionRectangleCrossingEvent m n) / 2 ≤
        (bernoulliBondMeasure 2 p).real (Y R))
    (hsubset :
      (⋃ R ∈ brGoodReachableFaceFiberIndices n,
        brReachableFaceFiber n R ∩ Y R) ⊆ brSourceXEvent m n)
    (hunreached :
      brRightTargetsUnreachedEvent n = brSquareVerticalCrossingEvent n) :
    ((bernoulliBondMeasure 2 p).real (brExtensionRectangleCrossingEvent m n) / 2) *
        rswSquareCrossingProbability p n ≤
      (bernoulliBondMeasure 2 p).real (brSourceXEvent m n) := by
  rw [← bernoulliBondMeasure_real_brSquareVerticalCrossingEvent p n,
    ← hunreached]
  exact brFiberExtensionProbability_mul_unreached_le_sourceX
    p m n Y hY hYlower hsubset

/-- Generic uniform-lower-bound form of the stopped-fiber assembler.  This is the form used by
the square-root trick, where the per-fiber fresh event has the nonlinear lower bound
`1 - sqrt (1 - P(H))` rather than the elementary `P(H) / 2`. -/
theorem brFiberExtensionProbability_mul_rswSquare_le_sourceX_of_uniform_lower
    (p : I) (m n : ℕ) (q : ℝ)
    (Y : Finset (BRLeftmostDualVertex n) → Set (EdgeConfiguration 2))
    (hY : ∀ R ∈ brGoodReachableFaceFiberIndices n,
      DependsOn (brFreshExtensionEdges m n R) (Y R))
    (hYlower : ∀ R ∈ brGoodReachableFaceFiberIndices n,
      q ≤ (bernoulliBondMeasure 2 p).real (Y R))
    (hsubset :
      (⋃ R ∈ brGoodReachableFaceFiberIndices n,
        brReachableFaceFiber n R ∩ Y R) ⊆ brSourceXEvent m n)
    (hunreached :
      brRightTargetsUnreachedEvent n = brSquareVerticalCrossingEvent n) :
    q * rswSquareCrossingProbability p n ≤
      (bernoulliBondMeasure 2 p).real (brSourceXEvent m n) := by
  rw [← bernoulliBondMeasure_real_brSquareVerticalCrossingEvent p n,
    ← hunreached]
  apply mul_measureReal_brRightTargetsUnreachedEvent_le_of_fiber_extensions
    (bernoulliBondMeasure 2 p) n Y (brSourceXEvent m n) q
  · exact fun R hR ↦ (hY R hR).measurableSet
  · intro R hR
    have hfiberNonneg :
        0 ≤ (bernoulliBondMeasure 2 p).real (brReachableFaceFiber n R) :=
      measureReal_nonneg
    calc
      q * (bernoulliBondMeasure 2 p).real (brReachableFaceFiber n R) ≤
          (bernoulliBondMeasure 2 p).real (Y R) *
            (bernoulliBondMeasure 2 p).real (brReachableFaceFiber n R) :=
        mul_le_mul_of_nonneg_right (hYlower R hR) hfiberNonneg
      _ = (bernoulliBondMeasure 2 p).real
          (brReachableFaceFiber n R ∩ Y R) := by
        rw [mul_comm]
        exact (bernoulliBondMeasure_real_brReachableFaceFiber_inter_fresh_eq_mul
          p m n R (hY R hR)).symm
  · exact hsubset

end

end Percolation
