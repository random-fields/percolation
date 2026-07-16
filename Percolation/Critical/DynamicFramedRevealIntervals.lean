import Percolation.Critical.DynamicRevealIntervals
import Percolation.Critical.DynamicFramedRestartPartition

/-!
# Reused-coordinate interval fibers in a full restart frame

This file transports the interval-history algebra to a `FramedRestartQuery`.  It identifies the
physical boundary thresholds exactly and supplies a finite partition constructor in which
earlier information may overlap the current restart support precisely on the current closed
boundary.  Only the residual closed constraints and all earlier open constraints must be fresh.
-/

namespace Percolation

open MeasureTheory
open scoped unitInterval

namespace FramedRestartQuery

/-- Current reference threshold transported to a physical edge coordinate. -/
noncomputable def physicalBoundaryThreshold {d : ℕ} (Q : FramedRestartQuery d) :
    CubicEdge d → I :=
  fun e ↦ Q.beta
    ((cubicRestartFrameIso Q.center Q.direction Q.transverseFlip).mapEdgeSet.symm e)

/-- Literal physical support of the current closed-boundary history. -/
noncomputable def boundarySupport {d : ℕ} (Q : FramedRestartQuery d) (n : ℕ) :
    Finset (CubicEdge d) :=
  framedBoundaryHistorySupport Q.center Q.direction Q.transverseFlip Q.region n

/-- A transported closed-boundary event is exactly the heterogeneous coordinate box on the
physical boundary support with the pulled-back thresholds. -/
theorem boundaryHistoryEvent_eq_physical {d n : ℕ} (Q : FramedRestartQuery d) :
    Q.boundaryHistoryEvent n =
      boundaryClosedHistoryEvent (Q.boundarySupport n) Q.physicalBoundaryThreshold := by
  ext X
  let F := cubicRestartFrameIso Q.center Q.direction Q.transverseFlip
  constructor
  · intro h e he
    rw [boundarySupport, framedBoundaryHistorySupport, Finset.mem_image] at he
    obtain ⟨f, hf, rfl⟩ := he
    have hfClosed : (Q.beta f : ℝ) ≤ X (F.mapEdgeSet f) := by
      exact h f hf
    change (Q.beta (F.mapEdgeSet.symm (F.mapEdgeSet f)) : ℝ) ≤
      X (F.mapEdgeSet f)
    rw [F.mapEdgeSet.symm_apply_apply]
    exact hfClosed
  · intro h f hf
    have hePhysical : F.mapEdgeSet f ∈ Q.boundarySupport n := by
      rw [boundarySupport, framedBoundaryHistorySupport, Finset.mem_image]
      exact ⟨f, hf, rfl⟩
    have := h (F.mapEdgeSet f) hePhysical
    change (Q.beta (F.mapEdgeSet.symm (F.mapEdgeSet f)) : ℝ) ≤
      X (F.mapEdgeSet f) at this
    rw [F.mapEdgeSet.symm_apply_apply] at this
    exact this

end FramedRestartQuery

namespace FiniteRevealIntervalProfile

/-- Source interval-fiber identity in a full frame.  All current boundary edges must already
carry their accumulated lower threshold, and that threshold must agree with the query's
transported `beta`. -/
theorem event_eq_withoutClosed_inter_framedBoundaryHistory
    {d : ℕ} (P : FiniteRevealIntervalProfile (CubicEdge d))
    (Q : FramedRestartQuery d) (n : ℕ)
    (hboundary : Q.boundarySupport n ⊆ P.closedSupport)
    (hlower : ∀ e ∈ Q.boundarySupport n,
      P.lower e = Q.physicalBoundaryThreshold e) :
    P.event = (P.withoutClosed (Q.boundarySupport n)).event ∩
      Q.boundaryHistoryEvent n := by
  rw [P.event_eq_withoutClosed_inter_boundaryClosedHistoryEvent
    (Q.boundarySupport n) hboundary, Q.boundaryHistoryEvent_eq_physical]
  congr 1
  ext X
  constructor <;> intro h e he
  · simpa [hlower e he] using h e he
  · simpa [hlower e he] using h e he

end FiniteRevealIntervalProfile

namespace AdaptiveSiteExploration

variable {C : Type*} [Fintype C] [DecidableEq C]

/-- Construct a full-frame partition from exact finite interval-history fibers.  Earlier
coordinates are allowed to overlap the current query on its closed boundary; after those
constraints are peeled into `boundaryHistoryEvent`, only the residual support must be fresh. -/
noncomputable def PartitionedFramedRestartStage.ofIntervalProfileRealization
    {d m n : ℕ} {p : I} {delta epsilon : ℝ}
    (history : Set (CubicEdge d → ℝ))
    (realizedCell : (CubicEdge d → ℝ) → C)
    (query : C → FramedRestartQuery d)
    (profile : C → FiniteRevealIntervalProfile (CubicEdge d))
    (hboundary : ∀ c, (query c).boundarySupport n ⊆ (profile c).closedSupport)
    (hlower : ∀ c e, e ∈ (query c).boundarySupport n →
      (profile c).lower e = (query c).physicalBoundaryThreshold e)
    (hfiber : ∀ c, (profile c).event =
      exactRevealCellEvent history realizedCell c)
    (hfreshClosed : ∀ c,
      Disjoint (((profile c).closedSupport \ (query c).boundarySupport n :
        Finset (CubicEdge d)) : Set (CubicEdge d))
        ((query c).restartSupport m n : Set (CubicEdge d)))
    (hfreshOpen : ∀ c,
      Disjoint ((profile c).openSupport : Set (CubicEdge d))
        ((query c).restartSupport m n : Set (CubicEdge d)))
    (hrestart : ∀ c,
      (1 - epsilon) * (couplingMeasure (CubicEdge d)).real
          ((query c).boundaryHistoryEvent n) <
        (couplingMeasure (CubicEdge d)).real
          ((query c).successEvent m n p delta ∩
            (query c).boundaryHistoryEvent n)) :
    PartitionedFramedRestartStage d C m n p delta epsilon :=
  PartitionedFramedRestartStage.ofFiniteRealization
    history realizedCell query
    (fun c ↦ ((profile c).withoutClosed ((query c).boundarySupport n)).support)
    (fun c ↦ ((profile c).withoutClosed ((query c).boundarySupport n)).event)
    (fun c ↦ ((profile c).withoutClosed
      ((query c).boundarySupport n)).measurableSet_event_coordSigma)
    (fun c ↦ (profile c).disjoint_withoutClosed_support
      ((query c).boundarySupport n) ((query c).restartSupport m n)
      (hfreshClosed c) (hfreshOpen c))
    (fun c ↦ by
      rw [← (profile c).event_eq_withoutClosed_inter_framedBoundaryHistory
        (query c) n (hboundary c) (hlower c), hfiber c])
    hrestart

@[simp]
theorem PartitionedFramedRestartStage.query_ofIntervalProfileRealization
    {d m n : ℕ} {p : I} {delta epsilon : ℝ}
    (history : Set (CubicEdge d → ℝ))
    (realizedCell : (CubicEdge d → ℝ) → C)
    (query : C → FramedRestartQuery d)
    (profile : C → FiniteRevealIntervalProfile (CubicEdge d))
    (hboundary : ∀ c, (query c).boundarySupport n ⊆ (profile c).closedSupport)
    (hlower : ∀ c e, e ∈ (query c).boundarySupport n →
      (profile c).lower e = (query c).physicalBoundaryThreshold e)
    (hfiber : ∀ c, (profile c).event =
      exactRevealCellEvent history realizedCell c)
    (hfreshClosed : ∀ c,
      Disjoint (((profile c).closedSupport \ (query c).boundarySupport n :
        Finset (CubicEdge d)) : Set (CubicEdge d))
        ((query c).restartSupport m n : Set (CubicEdge d)))
    (hfreshOpen : ∀ c,
      Disjoint ((profile c).openSupport : Set (CubicEdge d))
        ((query c).restartSupport m n : Set (CubicEdge d)))
    (hrestart : ∀ c,
      (1 - epsilon) * (couplingMeasure (CubicEdge d)).real
          ((query c).boundaryHistoryEvent n) <
        (couplingMeasure (CubicEdge d)).real
          ((query c).successEvent m n p delta ∩
            (query c).boundaryHistoryEvent n))
    (c : C) :
    (PartitionedFramedRestartStage.ofIntervalProfileRealization
      history realizedCell query profile hboundary hlower hfiber
        hfreshClosed hfreshOpen hrestart).query c = query c :=
  rfl

/-- Every concrete cell of the interval-profile constructor is the advertised accumulated
interval event, not merely an abstract classifier fiber. -/
theorem PartitionedFramedRestartStage.cell_ofIntervalProfileRealization
    {d m n : ℕ} {p : I} {delta epsilon : ℝ}
    (history : Set (CubicEdge d → ℝ))
    (realizedCell : (CubicEdge d → ℝ) → C)
    (query : C → FramedRestartQuery d)
    (profile : C → FiniteRevealIntervalProfile (CubicEdge d))
    (hboundary : ∀ c, (query c).boundarySupport n ⊆ (profile c).closedSupport)
    (hlower : ∀ c e, e ∈ (query c).boundarySupport n →
      (profile c).lower e = (query c).physicalBoundaryThreshold e)
    (hfiber : ∀ c, (profile c).event =
      exactRevealCellEvent history realizedCell c)
    (hfreshClosed : ∀ c,
      Disjoint (((profile c).closedSupport \ (query c).boundarySupport n :
        Finset (CubicEdge d)) : Set (CubicEdge d))
        ((query c).restartSupport m n : Set (CubicEdge d)))
    (hfreshOpen : ∀ c,
      Disjoint ((profile c).openSupport : Set (CubicEdge d))
        ((query c).restartSupport m n : Set (CubicEdge d)))
    (hrestart : ∀ c,
      (1 - epsilon) * (couplingMeasure (CubicEdge d)).real
          ((query c).boundaryHistoryEvent n) <
        (couplingMeasure (CubicEdge d)).real
          ((query c).successEvent m n p delta ∩
            (query c).boundaryHistoryEvent n))
    (c : C) :
    (PartitionedFramedRestartStage.ofIntervalProfileRealization
      history realizedCell query profile hboundary hlower hfiber
        hfreshClosed hfreshOpen hrestart).cell c = (profile c).event := by
  rw [(profile c).event_eq_withoutClosed_inter_framedBoundaryHistory
    (query c) n (hboundary c) (hlower c)]
  rfl

/-- The interval-profile cells cover the literal outer history whenever their advertised
profiles are its exact finite fibers. -/
theorem PartitionedFramedRestartStage.cellUnion_ofIntervalProfileRealization
    {d m n : ℕ} {p : I} {delta epsilon : ℝ}
    (history : Set (CubicEdge d → ℝ))
    (realizedCell : (CubicEdge d → ℝ) → C)
    (query : C → FramedRestartQuery d)
    (profile : C → FiniteRevealIntervalProfile (CubicEdge d))
    (hboundary : ∀ c, (query c).boundarySupport n ⊆ (profile c).closedSupport)
    (hlower : ∀ c e, e ∈ (query c).boundarySupport n →
      (profile c).lower e = (query c).physicalBoundaryThreshold e)
    (hfiber : ∀ c, (profile c).event =
      exactRevealCellEvent history realizedCell c)
    (hfreshClosed : ∀ c,
      Disjoint (((profile c).closedSupport \ (query c).boundarySupport n :
        Finset (CubicEdge d)) : Set (CubicEdge d))
        ((query c).restartSupport m n : Set (CubicEdge d)))
    (hfreshOpen : ∀ c,
      Disjoint ((profile c).openSupport : Set (CubicEdge d))
        ((query c).restartSupport m n : Set (CubicEdge d)))
    (hrestart : ∀ c,
      (1 - epsilon) * (couplingMeasure (CubicEdge d)).real
          ((query c).boundaryHistoryEvent n) <
        (couplingMeasure (CubicEdge d)).real
          ((query c).successEvent m n p delta ∩
            (query c).boundaryHistoryEvent n)) :
    (PartitionedFramedRestartStage.ofIntervalProfileRealization
      history realizedCell query profile hboundary hlower hfiber
        hfreshClosed hfreshOpen hrestart).cellUnion = history := by
  unfold PartitionedFramedRestartStage.ofIntervalProfileRealization
  apply PartitionedFramedRestartStage.cellUnion_ofFiniteRealization

end AdaptiveSiteExploration

end Percolation
