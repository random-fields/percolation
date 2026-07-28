import Percolation.Planar.BRBoundaryPrimalWalk
import Percolation.Planar.BRExplorationAlternative
import Percolation.Planar.BRTruncatedDegree
import Percolation.Planar.BRVerticalEvents
import Percolation.Planar.BRVerticalSymmetry

/-!
# A truncated resolved-boundary component gives a vertical crossing

This module is the deterministic integration seam between the finite graph argument and the
primal crossing event.  Once the resolved truncated boundary has a walk from a bottom port to a
top port, the canonical crossed primal bonds form an open bottom-to-top walk inside exactly the
boundary-free square support used by the RSW events.
-/

namespace Percolation

open SimpleGraph
open MeasureTheory ProbabilityTheory
open scoped unitInterval

noncomputable section

/-- A resolved-boundary connection between a retained bottom port and a retained top port gives
an open vertical primal crossing in the realized exploration fiber. -/
theorem mem_brSquareVerticalCrossingEvent_of_reachable_truncated_ports
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    {omega : EdgeConfiguration 2}
    (homega : omega ∈ brReachableFaceFiber n R)
    {b t : BRTruncatedInterfaceEdge n R}
    (hb : b ∈ brTruncatedBottomBoundaryVertices n R)
    (ht : t ∈ brTruncatedTopBoundaryVertices n R)
    (hbt : (brTruncatedResolvedBoundaryGraph n R).Reachable b t) :
    omega ∈ brSquareVerticalCrossingEvent n := by
  rcases hbt with ⟨w⟩
  have hbData := brTruncatedBottomBoundaryVertex_primalEndpoint hb
  have htData := brTruncatedTopBoundaryVertex_primalEndpoint ht
  simp only [brSquareVerticalCrossingEvent, Set.mem_iUnion]
  refine ⟨brBottomPortPrimalVertex b.1, ?_,
    brTopPortPrimalVertex t.1, ?_, ?_⟩
  · exact mem_brSquareBottomSide_iff.mpr hbData.2
  · exact mem_brSquareTopSide_iff.mpr htData.2
  · exact brTruncatedBoundaryWalk_exists_open_primalWalkIn
      homega w hbData.1 htData.1

/-- Event-level form of
`mem_brSquareVerticalCrossingEvent_of_reachable_truncated_ports`.  The finite graph theorem may
supply the port connection independently of the configuration realizing the fiber. -/
theorem brReachableFaceFiber_subset_brSquareVerticalCrossingEvent_of_reachable_truncated_ports
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hports : ∃ b ∈ brTruncatedBottomBoundaryVertices n R,
      ∃ t ∈ brTruncatedTopBoundaryVertices n R,
        (brTruncatedResolvedBoundaryGraph n R).Reachable b t) :
    brReachableFaceFiber n R ⊆ brSquareVerticalCrossingEvent n := by
  rintro omega homega
  rcases hports with ⟨b, hb, t, ht, hbt⟩
  exact mem_brSquareVerticalCrossingEvent_of_reachable_truncated_ports
    homega hb ht hbt

/-- If every realizable separating reached set has a resolved-boundary component joining its
bottom and top port sets, then failure of the stopped dual exploration to reach the right side
forces a vertical primal crossing.  The premise is deliberately configuration-free, so it can be
discharged solely by finite graph parity. -/
theorem brRightTargetsUnreachedEvent_subset_brSquareVerticalCrossingEvent_of_ports
    (n : ℕ)
    (hports : ∀ R : Finset (BRLeftmostDualVertex n),
      BRAdmissibleSeparatingFiber n R →
        ∃ b ∈ brTruncatedBottomBoundaryVertices n R,
          ∃ t ∈ brTruncatedTopBoundaryVertices n R,
            (brTruncatedResolvedBoundaryGraph n R).Reachable b t) :
    brRightTargetsUnreachedEvent n ⊆ brSquareVerticalCrossingEvent n := by
  intro omega homega
  let R := brLeftReachableFaces n omega
  have hfiber : omega ∈ brReachableFaceFiber n R :=
    mem_brReachableFaceFiber_self n omega
  have hgood : R ∈ brGoodReachableFaceFiberIndices n := by
    rw [mem_brGoodReachableFaceFiberIndices_iff]
    exact homega
  have hR : BRAdmissibleSeparatingFiber n R :=
    brAdmissibleSeparatingFiber_of_mem_good_of_mem_fiber hgood hfiber
  exact
    brReachableFaceFiber_subset_brSquareVerticalCrossingEvent_of_reachable_truncated_ports
      (hports R hR) hfiber

/-- The stopped dual exploration alternative in the direction supplied by the truncated resolved
boundary: if the right side is not reached, odd-degree parity produces an open bottom-to-top
primal crossing. -/
theorem brRightTargetsUnreachedEvent_subset_brSquareVerticalCrossingEvent
    {n : ℕ} (hn : 0 < n) :
    brRightTargetsUnreachedEvent n ⊆ brSquareVerticalCrossingEvent n := by
  apply brRightTargetsUnreachedEvent_subset_brSquareVerticalCrossingEvent_of_ports
  intro R hR
  exact exists_brTruncatedResolvedBoundaryGraph_reachable_bottom_top hn hR

/-- Exact stopped-dual alternative for the repository's boundary-free square event. -/
theorem brRightTargetsUnreachedEvent_eq_brSquareVerticalCrossingEvent
    {n : ℕ} (hn : 0 < n) :
    brRightTargetsUnreachedEvent n = brSquareVerticalCrossingEvent n := by
  apply Set.Subset.antisymm
  · exact brRightTargetsUnreachedEvent_subset_brSquareVerticalCrossingEvent hn
  · exact brSquareVerticalCrossingEvent_subset_brRightTargetsUnreachedEvent n

/-- The good stopped-fiber union has exactly the square-crossing probability. -/
theorem bernoulliBondMeasure_real_brRightTargetsUnreachedEvent
    (p : I) {n : ℕ} (hn : 0 < n) :
    (bernoulliBondMeasure 2 p).real (brRightTargetsUnreachedEvent n) =
      rswSquareCrossingProbability p n := by
  rw [brRightTargetsUnreachedEvent_eq_brSquareVerticalCrossingEvent hn]
  exact bernoulliBondMeasure_real_brSquareVerticalCrossingEvent p n

end

end Percolation
