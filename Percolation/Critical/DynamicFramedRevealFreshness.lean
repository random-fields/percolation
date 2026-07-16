import Percolation.Critical.DynamicRevealFreshness
import Percolation.Critical.DynamicFramedRestartPartition

/-!
# Exact reveal cells in a full steering frame

This is the full-frame counterpart of the earlier oriented realization constructor.  It
transports the internal explored-region fiber, the closed-boundary factor, the finite schedule
multiplicities, and the fresh-support proof through `cubicRestartFrameIso`, including the
transverse mask used on pp. 159--162.
-/

namespace Percolation

open MeasureTheory
open scoped unitInterval

/-- Physical support of the labels internal to a reference explored region. -/
noncomputable def framedRestartInternalSupport
    {d : ℕ} (center : Cubic d) (a : CubicDirection d)
    (transverseFlip : Fin d → Bool) (R : Finset (Cubic d)) (n : ℕ) :
    Finset (CubicEdge d) :=
  (cubicRegionInternalEdgesWithinBox d R n).image
    (cubicRestartFrameIso center a transverseFlip).mapEdgeSet

/-- Physical-label version of the internal explored-region cell. -/
def framedRestartInternalRegionLabelEvent
    {d : ℕ} (center : Cubic d) (a : CubicDirection d)
    (transverseFlip : Fin d → Bool) (R : Finset (Cubic d))
    (m n : ℕ) (beta : CubicEdge d → I) : Set (CubicEdge d → ℝ) :=
  framedCouplingTransportEvent center a transverseFlip
    (restartInternalRegionLabelEvent R m n beta)

theorem measurableSet_framedRestartInternalRegionLabelEvent_coordSigma
    {d : ℕ} (center : Cubic d) (a : CubicDirection d)
    (transverseFlip : Fin d → Bool) (R : Finset (Cubic d))
    (m n : ℕ) (beta : CubicEdge d → I) :
    MeasurableSet[coordSigma (CubicEdge d)
      (framedRestartInternalSupport center a transverseFlip R n : Set (CubicEdge d))]
      (framedRestartInternalRegionLabelEvent center a transverseFlip R m n beta) := by
  apply measurableSet_cubicGraphIsoCouplingTransportEvent_coordSigma
    (cubicRestartFrameIso center a transverseFlip)
    (cubicRegionInternalEdgesWithinBox d R n)
    (measurableSet_restartInternalRegionLabelEvent R m n beta)
  intro X Y hXY
  exact restartInternalRegionLabelEvent_congr_of_eqOn R m n beta hXY

theorem disjoint_framedRestartInternalSupport_restartSupport
    {d : ℕ} (center : Cubic d) (a : CubicDirection d)
    (transverseFlip : Fin d → Bool) (R : Finset (Cubic d)) (m n : ℕ) :
    Disjoint (framedRestartInternalSupport center a transverseFlip R n :
      Set (CubicEdge d))
      (framedRestartSupport center a transverseFlip m n R : Set (CubicEdge d)) := by
  rw [Set.disjoint_left]
  intro e heInternal heRestart
  rw [Finset.mem_coe, framedRestartInternalSupport, Finset.mem_image] at heInternal
  rw [Finset.mem_coe, framedRestartSupport, Finset.mem_image] at heRestart
  obtain ⟨f, hfInternal, rfl⟩ := heInternal
  obtain ⟨g, hgRestart, hgf⟩ := heRestart
  have hfg : f = g :=
    (cubicRestartFrameIso center a transverseFlip).mapEdgeSet.injective hgf.symm
  subst g
  exact Set.disjoint_left.mp
    (disjoint_cubicRegionInternalEdgesWithinBox_restartEventSupport
      d R a.1 m n) hfInternal hgRestart

/-- Physical-label realization of a reference reveal cell under the complete frame. -/
noncomputable def framedRealizedScheduleRevealCell
    {d m n : ℕ} (center : Cubic d) (a : CubicDirection d)
    (transverseFlip : Fin d → Bool) (beta : CubicEdge d → I)
    (S : FiniteRevealSchedule (CubicEdge d))
    (hS : S.HasOverlapBound (2 * d + 1))
    (X : CubicEdge d → ℝ) : RestartRevealCellIndex d a.1 m n :=
  realizedScheduleRevealCell a.1 beta S hS
    (cubicGraphIsoCouplingReindex (cubicRestartFrameIso center a transverseFlip) X)

/-- Exact factorization after transporting both the explored-region fiber and boundary history
through the full frame. -/
theorem framedInternalPast_inter_boundary_eq_exactRevealCellEvent
    {d m n : ℕ} (center : Cubic d) (a : CubicDirection d)
    (transverseFlip : Fin d → Bool) (beta : CubicEdge d → I)
    (S : FiniteRevealSchedule (CubicEdge d))
    (hS : S.HasOverlapBound (2 * d + 1))
    (history : Set (CubicEdge d → ℝ))
    (c : RestartRevealCellIndex d a.1 m n)
    (hc : c.IsScheduleRealizable S hS) :
    (history ∩ framedRestartInternalRegionLabelEvent center a transverseFlip
          c.regionVertices m n beta) ∩
        framedBoundaryClosedHistoryEvent center a transverseFlip
          c.regionVertices n beta =
      exactRevealCellEvent history
        (framedRealizedScheduleRevealCell center a transverseFlip beta S hS) c := by
  have href := c.exactRevealCellEvent_eq_internalPast_inter_boundary_of_isScheduleRealizable
    a.1 beta S hS (Set.univ : Set (CubicEdge d → ℝ)) hc
  ext X
  have hmem := Set.ext_iff.mp href
    (cubicGraphIsoCouplingReindex (cubicRestartFrameIso center a transverseFlip) X)
  have hfactor :
      (cubicGraphIsoCouplingReindex (cubicRestartFrameIso center a transverseFlip) X ∈
          restartInternalRegionLabelEvent c.regionVertices m n beta ∧
        cubicGraphIsoCouplingReindex (cubicRestartFrameIso center a transverseFlip) X ∈
          boundaryClosedHistoryEvent
            (cubicRegionBoundaryEdgesWithinBox d c.regionVertices n) beta) ↔
        framedRealizedScheduleRevealCell center a transverseFlip beta S hS X = c := by
    simpa [framedRealizedScheduleRevealCell, exactRevealCellEvent] using hmem
  simp only [framedRestartInternalRegionLabelEvent, framedBoundaryClosedHistoryEvent,
    framedCouplingTransportEvent, cubicGraphIsoCouplingTransportEvent,
    exactRevealCellEvent, Set.mem_inter_iff, Set.mem_preimage]
  constructor
  · rintro ⟨⟨hHistory, hInternal⟩, hBoundary⟩
    exact ⟨hHistory, hfactor.mp ⟨hInternal, hBoundary⟩⟩
  · rintro ⟨hHistory, hcell⟩
    exact ⟨⟨hHistory, (hfactor.mpr hcell).1⟩, (hfactor.mpr hcell).2⟩

/-- Support of an outer history together with the framed internal-region fiber. -/
noncomputable def framedRestartRevealPastSupport
    {d : ℕ} (historySupport : Finset (CubicEdge d))
    (center : Cubic d) (a : CubicDirection d) (transverseFlip : Fin d → Bool)
    (R : Finset (Cubic d)) (n : ℕ) : Finset (CubicEdge d) :=
  historySupport ∪ framedRestartInternalSupport center a transverseFlip R n

def framedRestartRevealPastEvent
    {d : ℕ} (history : Set (CubicEdge d → ℝ))
    (center : Cubic d) (a : CubicDirection d) (transverseFlip : Fin d → Bool)
    (R : Finset (Cubic d)) (m n : ℕ) (beta : CubicEdge d → I) :
    Set (CubicEdge d → ℝ) :=
  history ∩ framedRestartInternalRegionLabelEvent
    center a transverseFlip R m n beta

theorem measurableSet_framedRestartRevealPastEvent_coordSigma
    {d : ℕ} {historySupport : Finset (CubicEdge d)}
    {history : Set (CubicEdge d → ℝ)}
    (hHistory : MeasurableSet[coordSigma (CubicEdge d)
      (historySupport : Set (CubicEdge d))] history)
    (center : Cubic d) (a : CubicDirection d) (transverseFlip : Fin d → Bool)
    (R : Finset (Cubic d)) (m n : ℕ) (beta : CubicEdge d → I) :
    MeasurableSet[coordSigma (CubicEdge d)
      (framedRestartRevealPastSupport historySupport center a transverseFlip R n :
        Set (CubicEdge d))]
      (framedRestartRevealPastEvent history center a transverseFlip R m n beta) := by
  apply MeasurableSet.inter
  · exact (coordSigma_mono (fun e he ↦ Finset.mem_union_left _ he)) history hHistory
  · apply (coordSigma_mono (fun e he ↦ Finset.mem_union_right _ he))
    exact measurableSet_framedRestartInternalRegionLabelEvent_coordSigma
      center a transverseFlip R m n beta

theorem disjoint_framedRestartRevealPastSupport_restartSupport
    {d : ℕ} {historySupport : Finset (CubicEdge d)}
    (center : Cubic d) (a : CubicDirection d) (transverseFlip : Fin d → Bool)
    (R : Finset (Cubic d)) (m n : ℕ)
    (hHistoryFresh : Disjoint (historySupport : Set (CubicEdge d))
      (framedRestartSupport center a transverseFlip m n R : Set (CubicEdge d))) :
    Disjoint
      (framedRestartRevealPastSupport historySupport center a transverseFlip R n :
        Set (CubicEdge d))
      (framedRestartSupport center a transverseFlip m n R : Set (CubicEdge d)) := by
  rw [Set.disjoint_left]
  intro e hePast heRestart
  change e ∈ historySupport ∪ framedRestartInternalSupport
    center a transverseFlip R n at hePast
  rw [Finset.mem_union] at hePast
  rcases hePast with heHistory | heInternal
  · exact Set.disjoint_left.mp hHistoryFresh heHistory heRestart
  · exact Set.disjoint_left.mp
      (disjoint_framedRestartInternalSupport_restartSupport
        center a transverseFlip R m n) heInternal heRestart

namespace RestartRevealCellIndex

/-- Fully framed query carried by one schedule reveal cell. -/
noncomputable def scheduleFramedQuery
    {d m n : ℕ} {a : CubicDirection d}
    (c : RestartRevealCellIndex d a.1 m n) (center : Cubic d)
    (transverseFlip : Fin d → Bool) (beta : CubicEdge d → I) :
    FramedRestartQuery d where
  center := center
  direction := a
  transverseFlip := transverseFlip
  region := c.regionVertices
  beta := beta

@[simp]
theorem scheduleFramedQuery_restartSupport
    {d m n : ℕ} {a : CubicDirection d}
    (c : RestartRevealCellIndex d a.1 m n) (center : Cubic d)
    (transverseFlip : Fin d → Bool) (beta : CubicEdge d → I) :
    (c.scheduleFramedQuery center transverseFlip beta).restartSupport m n =
      framedRestartSupport center a transverseFlip m n c.regionVertices :=
  rfl

end RestartRevealCellIndex

namespace AdaptiveSiteExploration

/-- Complete fully framed stage from a fixed schedule and an outer history fresh for every
realizable region. -/
noncomputable def PartitionedFramedRestartStage.ofFramedScheduleRealization
    {d m n : ℕ} {p : I} {delta epsilon : ℝ}
    (center : Cubic d) (a : CubicDirection d) (transverseFlip : Fin d → Bool)
    (beta : CubicEdge d → I) (S : FiniteRevealSchedule (CubicEdge d))
    (hS : S.HasOverlapBound (2 * d + 1))
    (historySupport : Finset (CubicEdge d))
    (history : Set (CubicEdge d → ℝ))
    (hHistory : MeasurableSet[coordSigma (CubicEdge d)
      (historySupport : Set (CubicEdge d))] history)
    (hFresh : ∀ c : RestartRevealCellIndex d a.1 m n,
      c.IsScheduleRealizable S hS →
        Disjoint (historySupport : Set (CubicEdge d))
          (framedRestartSupport center a transverseFlip m n c.regionVertices :
            Set (CubicEdge d)))
    (hRestart : ∀ c : RestartRevealCellIndex d a.1 m n,
      c.IsScheduleRealizable S hS →
        (1 - epsilon) * (couplingMeasure (CubicEdge d)).real
            ((c.scheduleFramedQuery center transverseFlip beta).boundaryHistoryEvent n) <
          (couplingMeasure (CubicEdge d)).real
            ((c.scheduleFramedQuery center transverseFlip beta).successEvent
                m n p delta ∩
              (c.scheduleFramedQuery center transverseFlip beta).boundaryHistoryEvent n)) :
    PartitionedFramedRestartStage d (RestartRevealCellIndex d a.1 m n)
      m n p delta epsilon := by
  classical
  exact PartitionedFramedRestartStage.ofFiniteValidRealization
    (fun c : RestartRevealCellIndex d a.1 m n ↦ c.IsScheduleRealizable S hS)
    history (framedRealizedScheduleRevealCell center a transverseFlip beta S hS)
    (fun c ↦ c.scheduleFramedQuery center transverseFlip beta)
    (fun c ↦ framedRestartRevealPastSupport
      historySupport center a transverseFlip c.regionVertices n)
    (fun c ↦ framedRestartRevealPastEvent
      history center a transverseFlip c.regionVertices m n beta)
    (fun c _hc ↦ measurableSet_framedRestartRevealPastEvent_coordSigma
      hHistory center a transverseFlip c.regionVertices m n beta)
    (fun c hc ↦ disjoint_framedRestartRevealPastSupport_restartSupport
      center a transverseFlip c.regionVertices m n (hFresh c hc))
    (fun c hc ↦ framedInternalPast_inter_boundary_eq_exactRevealCellEvent
      center a transverseFlip beta S hS history c hc)
    hRestart

theorem PartitionedFramedRestartStage.cellUnion_ofFramedScheduleRealization
    {d m n : ℕ} {p : I} {delta epsilon : ℝ}
    (center : Cubic d) (a : CubicDirection d) (transverseFlip : Fin d → Bool)
    (beta : CubicEdge d → I) (S : FiniteRevealSchedule (CubicEdge d))
    (hS : S.HasOverlapBound (2 * d + 1))
    (historySupport : Finset (CubicEdge d))
    (history : Set (CubicEdge d → ℝ))
    (hHistory : MeasurableSet[coordSigma (CubicEdge d)
      (historySupport : Set (CubicEdge d))] history)
    (hmn : m ≤ n)
    (hFresh : ∀ c : RestartRevealCellIndex d a.1 m n,
      c.IsScheduleRealizable S hS →
        Disjoint (historySupport : Set (CubicEdge d))
          (framedRestartSupport center a transverseFlip m n c.regionVertices :
            Set (CubicEdge d)))
    (hRestart : ∀ c : RestartRevealCellIndex d a.1 m n,
      c.IsScheduleRealizable S hS →
        (1 - epsilon) * (couplingMeasure (CubicEdge d)).real
            ((c.scheduleFramedQuery center transverseFlip beta).boundaryHistoryEvent n) <
          (couplingMeasure (CubicEdge d)).real
            ((c.scheduleFramedQuery center transverseFlip beta).successEvent
                m n p delta ∩
              (c.scheduleFramedQuery center transverseFlip beta).boundaryHistoryEvent n)) :
    (PartitionedFramedRestartStage.ofFramedScheduleRealization center a transverseFlip
      beta S hS historySupport history hHistory hFresh hRestart).cellUnion = history := by
  classical
  apply PartitionedFramedRestartStage.cellUnion_ofFiniteValidRealization
  intro X _hX
  exact RestartRevealCellIndex.isScheduleRealizable_realizedScheduleRevealCell
    a.1 beta S hS hmn
      (cubicGraphIsoCouplingReindex (cubicRestartFrameIso center a transverseFlip) X)

end AdaptiveSiteExploration

end Percolation
