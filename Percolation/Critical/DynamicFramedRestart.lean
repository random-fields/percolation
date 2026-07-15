import Percolation.Critical.DynamicSteeringFrame

/-!
# Restart laws in a full signed steering frame

Grimmett's dynamic construction chooses both an exit direction and a transverse quadrant.  The
older `OrientedRestartQuery` records only the exit direction, so it is deliberately retained as
the no-transverse-flip special case.  This file gives the source-faithful interface: every query
records the complete transverse sign mask, and all events, finite supports, probability bounds,
and pathwise certificates are transported through that exact frame.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval

/-- Transport a uniform-label event through a full signed restart frame. -/
def framedCouplingTransportEvent {d : ℕ}
    (center : Cubic d) (a : CubicDirection d) (transverseFlip : Fin d → Bool)
    (A : Set (CubicEdge d → ℝ)) : Set (CubicEdge d → ℝ) :=
  cubicGraphIsoCouplingTransportEvent
    (cubicRestartFrameIso center a transverseFlip) A

theorem couplingMeasure_real_framedTransportEvent
    {d : ℕ} (center : Cubic d) (a : CubicDirection d)
    (transverseFlip : Fin d → Bool)
    {A : Set (CubicEdge d → ℝ)} (hA : MeasurableSet A) :
    (couplingMeasure (CubicEdge d)).real
        (framedCouplingTransportEvent center a transverseFlip A) =
      (couplingMeasure (CubicEdge d)).real A :=
  couplingMeasure_real_cubicGraphIsoTransportEvent
    (cubicRestartFrameIso center a transverseFlip) hA

theorem thresholdConfiguration_framedCouplingReindex
    {d : ℕ} (center : Cubic d) (a : CubicDirection d)
    (transverseFlip : Fin d → Bool) (p : I) (X : CubicEdge d → ℝ) :
    thresholdConfiguration p
        (cubicGraphIsoCouplingReindex
          (cubicRestartFrameIso center a transverseFlip) X) =
      cubicGraphIsoConfigurationPullback
        (cubicRestartFrameIso center a transverseFlip)
        (thresholdConfiguration p X) :=
  thresholdConfiguration_cubicGraphIsoCouplingReindex _ p X

theorem thresholdConfiguration_mem_framedConnectionEventIn
    {d : ℕ} (center : Cubic d) (a : CubicDirection d)
    (transverseFlip : Fin d → Bool) (p : I) (X : CubicEdge d → ℝ)
    (E : Finset (CubicEdge d)) (u v : Cubic d)
    (h : thresholdConfiguration p
      (cubicGraphIsoCouplingReindex
        (cubicRestartFrameIso center a transverseFlip) X) ∈
        connectionEventIn d E u v) :
    thresholdConfiguration p X ∈
      connectionEventIn d
        (E.image (cubicRestartFrameIso center a transverseFlip).mapEdgeSet)
        (cubicRestartFrameIso center a transverseFlip u)
        (cubicRestartFrameIso center a transverseFlip v) := by
  rw [thresholdConfiguration_framedCouplingReindex] at h
  exact (cubicGraphIsoConfigurationPullback_mem_connectionEventIn_iff
    (cubicRestartFrameIso center a transverseFlip) E
      (thresholdConfiguration p X) u v).1 h

/-- Full-frame copy of the reference restart success event. -/
def framedSprinkledRestartEvent {d : ℕ}
    (center : Cubic d) (a : CubicDirection d) (transverseFlip : Fin d → Bool)
    (m n : ℕ) (R : Finset (Cubic d))
    (p : I) (beta : CubicEdge d → I) (delta : ℝ) :
    Set (CubicEdge d → ℝ) :=
  framedCouplingTransportEvent center a transverseFlip
    (sprinkledRestartEvent d a.1 m n R p beta delta)

/-- Literal uniform-label coordinates read by a full-frame restart. -/
noncomputable def framedRestartSupport {d : ℕ}
    (center : Cubic d) (a : CubicDirection d) (transverseFlip : Fin d → Bool)
    (m n : ℕ) (R : Finset (Cubic d)) : Finset (CubicEdge d) :=
  (restartEventSupport d a.1 m n R).image
    (cubicRestartFrameIso center a transverseFlip).mapEdgeSet

/-- The former axis-only event is exactly the no-transverse-flip specialization. -/
theorem framedSprinkledRestartEvent_noTransverse_eq_oriented
    {d : ℕ} (center : Cubic d) (a : CubicDirection d)
    (m n : ℕ) (R : Finset (Cubic d))
    (p : I) (beta : CubicEdge d → I) (delta : ℝ) :
    framedSprinkledRestartEvent center a (fun _ ↦ false)
        m n R p beta delta =
      orientedSprinkledRestartEvent center a m n R p beta delta := by
  simp only [framedSprinkledRestartEvent, framedCouplingTransportEvent,
    orientedSprinkledRestartEvent, orientedCouplingTransportEvent,
    cubicRestartFrameIso_noTransverse_eq]

theorem framedRestartSupport_noTransverse_eq_oriented
    {d : ℕ} (center : Cubic d) (a : CubicDirection d)
    (m n : ℕ) (R : Finset (Cubic d)) :
    framedRestartSupport center a (fun _ ↦ false) m n R =
      orientedRestartSupport center a m n R := by
  simp only [framedRestartSupport, orientedRestartSupport,
    cubicRestartFrameIso_noTransverse_eq]

theorem measurableSet_framedSprinkledRestartEvent_coordSigma
    {d : ℕ} (center : Cubic d) (a : CubicDirection d)
    (transverseFlip : Fin d → Bool) (m n : ℕ) (R : Finset (Cubic d))
    (p : I) (beta : CubicEdge d → I) (delta : ℝ) :
    MeasurableSet[coordSigma (CubicEdge d)
      (framedRestartSupport center a transverseFlip m n R : Set (CubicEdge d))]
      (framedSprinkledRestartEvent center a transverseFlip m n R p beta delta) := by
  apply measurableSet_cubicGraphIsoCouplingTransportEvent_coordSigma
    (cubicRestartFrameIso center a transverseFlip)
    (restartEventSupport d a.1 m n R)
    (measurableSet_sprinkledRestartEvent d a.1 m n R p beta delta)
  intro X Y hXY
  exact sprinkledRestartEvent_congr_of_eqOn_restartEventSupport
    (fun e he => hXY e he)

/-- Full-frame copy of the reference closed-boundary history. -/
def framedBoundaryClosedHistoryEvent {d : ℕ}
    (center : Cubic d) (a : CubicDirection d) (transverseFlip : Fin d → Bool)
    (R : Finset (Cubic d)) (n : ℕ) (beta : CubicEdge d → I) :
    Set (CubicEdge d → ℝ) :=
  framedCouplingTransportEvent center a transverseFlip
    (boundaryClosedHistoryEvent (cubicRegionBoundaryEdgesWithinBox d R n) beta)

noncomputable def framedBoundaryHistorySupport {d : ℕ}
    (center : Cubic d) (a : CubicDirection d) (transverseFlip : Fin d → Bool)
    (R : Finset (Cubic d)) (n : ℕ) : Finset (CubicEdge d) :=
  (cubicRegionBoundaryEdgesWithinBox d R n).image
    (cubicRestartFrameIso center a transverseFlip).mapEdgeSet

theorem framedBoundaryHistorySupport_subset_restartSupport
    {d m n : ℕ} (center : Cubic d) (a : CubicDirection d)
    (transverseFlip : Fin d → Bool) (R : Finset (Cubic d)) :
    framedBoundaryHistorySupport center a transverseFlip R n ⊆
      framedRestartSupport center a transverseFlip m n R := by
  intro e he
  rw [framedBoundaryHistorySupport, Finset.mem_image] at he
  obtain ⟨f, hf, rfl⟩ := he
  rw [framedRestartSupport, Finset.mem_image]
  exact ⟨f, boundary_subset_restartEventSupport d a.1 m n R hf, rfl⟩

theorem measurableSet_framedBoundaryClosedHistoryEvent_coordSigma
    {d : ℕ} (center : Cubic d) (a : CubicDirection d)
    (transverseFlip : Fin d → Bool) (R : Finset (Cubic d))
    (n : ℕ) (beta : CubicEdge d → I) :
    MeasurableSet[coordSigma (CubicEdge d)
      (framedBoundaryHistorySupport center a transverseFlip R n :
        Set (CubicEdge d))]
      (framedBoundaryClosedHistoryEvent center a transverseFlip R n beta) := by
  apply measurableSet_cubicGraphIsoCouplingTransportEvent_coordSigma
    (cubicRestartFrameIso center a transverseFlip)
    (cubicRegionBoundaryEdgesWithinBox d R n)
    (measurableSet_boundaryClosedHistoryEvent _ beta)
  intro X Y hXY
  exact boundaryClosedHistoryEvent_congr_of_eqOn (fun e he => hXY e he)

/-- Lemma 7.17 is invariant under the complete steering frame, including transverse signs. -/
theorem framedSprinkledRestart_inter_history_gt
    {d m n : ℕ} (center : Cubic d) (a : CubicDirection d)
    (transverseFlip : Fin d → Bool) (R : Finset (Cubic d))
    (p : I) (beta : CubicEdge d → I) (delta epsilon : ℝ)
    (h : (1 - epsilon) *
        (couplingMeasure (CubicEdge d)).real
          (boundaryClosedHistoryEvent
            (cubicRegionBoundaryEdgesWithinBox d R n) beta) <
      (couplingMeasure (CubicEdge d)).real
        (sprinkledRestartEvent d a.1 m n R p beta delta ∩
          boundaryClosedHistoryEvent
            (cubicRegionBoundaryEdgesWithinBox d R n) beta)) :
    (1 - epsilon) *
        (couplingMeasure (CubicEdge d)).real
          (framedBoundaryClosedHistoryEvent center a transverseFlip R n beta) <
      (couplingMeasure (CubicEdge d)).real
        (framedSprinkledRestartEvent center a transverseFlip m n R p beta delta ∩
          framedBoundaryClosedHistoryEvent center a transverseFlip R n beta) := by
  let G := sprinkledRestartEvent d a.1 m n R p beta delta
  let H := boundaryClosedHistoryEvent
    (cubicRegionBoundaryEdgesWithinBox d R n) beta
  have hG : MeasurableSet G :=
    measurableSet_sprinkledRestartEvent d a.1 m n R p beta delta
  have hH : MeasurableSet H :=
    measurableSet_boundaryClosedHistoryEvent _ beta
  rw [show framedSprinkledRestartEvent center a transverseFlip m n R p beta delta =
      framedCouplingTransportEvent center a transverseFlip G by rfl,
    show framedBoundaryClosedHistoryEvent center a transverseFlip R n beta =
      framedCouplingTransportEvent center a transverseFlip H by rfl]
  simp only [framedCouplingTransportEvent]
  rw [← cubicGraphIsoCouplingTransportEvent_inter,
    couplingMeasure_real_cubicGraphIsoTransportEvent
      (cubicRestartFrameIso center a transverseFlip) hH,
    couplingMeasure_real_cubicGraphIsoTransportEvent
      (cubicRestartFrameIso center a transverseFlip) (hG.inter hH)]
  exact h

/-- A full-frame restart retains its ratio-free bound after adjoining an arbitrary earlier cell
on disjoint label coordinates. -/
theorem framedSprinkledRestart_inter_past_history_ge
    {d m n : ℕ} (center : Cubic d) (a : CubicDirection d)
    (transverseFlip : Fin d → Bool) (R : Finset (Cubic d))
    (p : I) (beta : CubicEdge d → I) (delta epsilon : ℝ)
    (pastSupport : Finset (CubicEdge d)) (past : Set (CubicEdge d → ℝ))
    (hpast : MeasurableSet[coordSigma (CubicEdge d)
      (pastSupport : Set (CubicEdge d))] past)
    (hfresh : Disjoint (pastSupport : Set (CubicEdge d))
      (framedRestartSupport center a transverseFlip m n R : Set (CubicEdge d)))
    (h : (1 - epsilon) *
        (couplingMeasure (CubicEdge d)).real
          (framedBoundaryClosedHistoryEvent center a transverseFlip R n beta) <
      (couplingMeasure (CubicEdge d)).real
        (framedSprinkledRestartEvent center a transverseFlip m n R p beta delta ∩
          framedBoundaryClosedHistoryEvent center a transverseFlip R n beta)) :
    (1 - epsilon) *
        (couplingMeasure (CubicEdge d)).real
          (past ∩ framedBoundaryClosedHistoryEvent center a transverseFlip R n beta) ≤
      (couplingMeasure (CubicEdge d)).real
        (framedSprinkledRestartEvent center a transverseFlip m n R p beta delta ∩
          (past ∩ framedBoundaryClosedHistoryEvent center a transverseFlip R n beta)) := by
  let restartSupport := framedRestartSupport center a transverseFlip m n R
  let G := framedSprinkledRestartEvent center a transverseFlip m n R p beta delta
  let H := framedBoundaryClosedHistoryEvent center a transverseFlip R n beta
  have hG : MeasurableSet[coordSigma (CubicEdge d)
      (restartSupport : Set (CubicEdge d))] G :=
    measurableSet_framedSprinkledRestartEvent_coordSigma
      center a transverseFlip m n R p beta delta
  have hHsmall : MeasurableSet[coordSigma (CubicEdge d)
      (framedBoundaryHistorySupport center a transverseFlip R n :
        Set (CubicEdge d))] H :=
    measurableSet_framedBoundaryClosedHistoryEvent_coordSigma
      center a transverseFlip R n beta
  have hH : MeasurableSet[coordSigma (CubicEdge d)
      (restartSupport : Set (CubicEdge d))] H :=
    (coordSigma_mono fun e he =>
      framedBoundaryHistorySupport_subset_restartSupport
        center a transverseFlip R he) H hHsmall
  have hpastH : IndepSet past H (couplingMeasure (CubicEdge d)) :=
    indepSet_of_measurableSet_coordSigma_of_disjoint hfresh hpast hH
  have hpastGH : IndepSet past (G ∩ H) (couplingMeasure (CubicEdge d)) :=
    indepSet_of_measurableSet_coordSigma_of_disjoint hfresh hpast (hG.inter hH)
  exact mul_measureReal_inter_le_inter_of_indepSet hpastH hpastGH h.le

/-- Source-faithful dynamic restart query.  The transverse mask is explicit data. -/
structure FramedRestartQuery (d : ℕ) where
  center : Cubic d
  direction : CubicDirection d
  transverseFlip : Fin d → Bool
  region : Finset (Cubic d)
  beta : CubicEdge d → I

namespace FramedRestartQuery

def successEvent {d : ℕ} (Q : FramedRestartQuery d)
    (m n : ℕ) (p : I) (delta : ℝ) : Set (CubicEdge d → ℝ) :=
  framedSprinkledRestartEvent Q.center Q.direction Q.transverseFlip
    m n Q.region p Q.beta delta

def boundaryHistoryEvent {d : ℕ} (Q : FramedRestartQuery d)
    (n : ℕ) : Set (CubicEdge d → ℝ) :=
  framedBoundaryClosedHistoryEvent Q.center Q.direction Q.transverseFlip
    Q.region n Q.beta

noncomputable def restartSupport {d : ℕ} (Q : FramedRestartQuery d)
    (m n : ℕ) : Finset (CubicEdge d) :=
  framedRestartSupport Q.center Q.direction Q.transverseFlip m n Q.region

theorem measurableSet_successEvent_coordSigma {d : ℕ} (Q : FramedRestartQuery d)
    (m n : ℕ) (p : I) (delta : ℝ) :
    MeasurableSet[coordSigma (CubicEdge d)
      (Q.restartSupport m n : Set (CubicEdge d))]
      (Q.successEvent m n p delta) :=
  measurableSet_framedSprinkledRestartEvent_coordSigma
    Q.center Q.direction Q.transverseFlip m n Q.region p Q.beta delta

end FramedRestartQuery

/-- Reference-coordinate form of the full-frame success certificate.  It retains exactly the
finite connection consumed by deterministic seed selection before that connection is mapped to
the physical block. -/
theorem exists_framedReferenceInletSeed_connectionToSeededTarget_of_sprinkledRestart
    {d m n : ℕ} (center : Cubic d) (a : CubicDirection d)
    (transverseFlip : Fin d → Bool) {X : CubicEdge d → ℝ}
    {p pFinal : I} {beta : CubicEdge d → I} {delta : ℝ}
    (hpFinal : (p : ℝ) ≤ (pFinal : ℝ))
    (hbetaFinal : ∀ e, (beta e : ℝ) ≤ (pFinal : ℝ))
    (hboundaryFinal : ∀ e ∈ cubicRegionBoundaryEdgesWithinBox d
      (restartExploredRegion d
        (heterogeneousThresholdConfiguration beta
          (cubicGraphIsoCouplingReindex
            (cubicRestartFrameIso center a transverseFlip) X)) m n) n,
      (beta e : ℝ) + delta ≤ (pFinal : ℝ))
    (hAvoid : RegionAvoidsSeededBoundaryQuadrant d a.1 n
      (restartExploredRegion d
        (heterogeneousThresholdConfiguration beta
          (cubicGraphIsoCouplingReindex
            (cubicRestartFrameIso center a transverseFlip) X)) m n))
    (hsuccess : X ∈ framedSprinkledRestartEvent center a transverseFlip m n
      (restartExploredRegion d
        (heterogeneousThresholdConfiguration beta
          (cubicGraphIsoCouplingReindex
            (cubicRestartFrameIso center a transverseFlip) X)) m n)
      p beta delta) :
    ∃ z ∈ cubicMetricBox d cubicOrigin m,
      ∃ y ∈ seededBoundaryPointFinset d a.1 m n
          (thresholdConfiguration pFinal
            (cubicGraphIsoCouplingReindex
              (cubicRestartFrameIso center a transverseFlip) X)),
        thresholdConfiguration pFinal
            (cubicGraphIsoCouplingReindex
              (cubicRestartFrameIso center a transverseFlip) X) ∈
          connectionEventIn d (cubicBoxEdges d cubicOrigin n) z y := by
  let F := cubicRestartFrameIso center a transverseFlip
  let Xref := cubicGraphIsoCouplingReindex F X
  apply exists_inletSeed_connectionToSeededTarget_of_sprinkledRestart
    hpFinal hbetaFinal hboundaryFinal hAvoid
  exact hsuccess

/-- Pathwise form of a successful full-frame query.  The inlet and new seed remain named in
reference coordinates; the displayed connection is the literal physical one. -/
theorem exists_framedInletSeed_connectionToSeededTarget_of_sprinkledRestart
    {d m n : ℕ} (center : Cubic d) (a : CubicDirection d)
    (transverseFlip : Fin d → Bool) {X : CubicEdge d → ℝ}
    {p pFinal : I} {beta : CubicEdge d → I} {delta : ℝ}
    (hpFinal : (p : ℝ) ≤ (pFinal : ℝ))
    (hbetaFinal : ∀ e, (beta e : ℝ) ≤ (pFinal : ℝ))
    (hboundaryFinal : ∀ e ∈ cubicRegionBoundaryEdgesWithinBox d
      (restartExploredRegion d
        (heterogeneousThresholdConfiguration beta
          (cubicGraphIsoCouplingReindex
            (cubicRestartFrameIso center a transverseFlip) X)) m n) n,
      (beta e : ℝ) + delta ≤ (pFinal : ℝ))
    (hAvoid : RegionAvoidsSeededBoundaryQuadrant d a.1 n
      (restartExploredRegion d
        (heterogeneousThresholdConfiguration beta
          (cubicGraphIsoCouplingReindex
            (cubicRestartFrameIso center a transverseFlip) X)) m n))
    (hsuccess : X ∈ framedSprinkledRestartEvent center a transverseFlip m n
      (restartExploredRegion d
        (heterogeneousThresholdConfiguration beta
          (cubicGraphIsoCouplingReindex
            (cubicRestartFrameIso center a transverseFlip) X)) m n)
      p beta delta) :
    ∃ z ∈ cubicMetricBox d cubicOrigin m,
      ∃ y ∈ seededBoundaryPointFinset d a.1 m n
          (thresholdConfiguration pFinal
            (cubicGraphIsoCouplingReindex
              (cubicRestartFrameIso center a transverseFlip) X)),
        thresholdConfiguration pFinal X ∈
          connectionEventIn d (cubicBoxEdges d center n)
            (cubicRestartFrameIso center a transverseFlip z)
            (cubicRestartFrameIso center a transverseFlip y) := by
  let F := cubicRestartFrameIso center a transverseFlip
  obtain ⟨z, hzSeed, y, hyTarget, hzy⟩ :=
    exists_framedReferenceInletSeed_connectionToSeededTarget_of_sprinkledRestart
      center a transverseFlip hpFinal hbetaFinal hboundaryFinal hAvoid hsuccess
  refine ⟨z, hzSeed, y, hyTarget, ?_⟩
  simpa [F, cubicRestartFrameIso_image_cubicBoxEdges_eq] using
    thresholdConfiguration_mem_framedConnectionEventIn
      center a transverseFlip pFinal X (cubicBoxEdges d cubicOrigin n) z y hzy

end Percolation
