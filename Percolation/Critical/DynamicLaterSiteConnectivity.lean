import Percolation.Critical.DynamicLaterSiteRuntime
import Percolation.Critical.DynamicSourceConnectivity

/-!
# Pathwise connectivity of the non-root dynamic runtime

This module connects the exact mixed witness retained at a successful runtime slot to the
already root-connected source edge set.  It is deliberately separate from the probability
certificate: no conditional probability is used here.
-/

namespace Percolation

open scoped unitInterval

/-- Transport an unrestricted reference connection through a full restart frame. -/
theorem thresholdConfiguration_mem_framedConnectionEvent
    {d : ℕ} (center : Cubic d) (a : CubicDirection d)
    (transverseFlip : Fin d → Bool) (p : I) (X : CubicEdge d → ℝ)
    (u v : Cubic d)
    (h : thresholdConfiguration p
      (cubicGraphIsoCouplingReindex
        (cubicRestartFrameIso center a transverseFlip) X) ∈
        connectionEvent d u v) :
    thresholdConfiguration p X ∈
      connectionEvent d
        (cubicRestartFrameIso center a transverseFlip u)
        (cubicRestartFrameIso center a transverseFlip v) := by
  rw [thresholdConfiguration_framedCouplingReindex] at h
  rcases h with ⟨w, hw⟩
  exact ⟨w.map (cubicRestartFrameIso center a transverseFlip).toHom,
    walkIsOpen_map_cubicGraphIso
      (cubicRestartFrameIso center a transverseFlip) w hw⟩

namespace LaterSiteRuntime

/-- At a successful runtime slot, the exact selected target center is connected to the source
anchor at the final density.  The proof uses the old explored endpoint on the successful exit,
the increment-open exit edge, the retained exterior path, and the fully open selected seed. -/
theorem selectedTarget_connected_of_success
    {d m n : ℕ} {hmn : 2 * m ≤ n}
    (R : LaterSiteRuntime d) (inletCenter : Cubic d)
    (incoming : CubicDirection d) (firstFlip secondFlip : Fin d → Bool)
    (p pFinal : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) (anchor : Cubic d)
    (a : CubicDirection d) (k : ℕ)
    (hrooted : R.source.RootedOpen (thresholdConfiguration pFinal X) anchor)
    (hpFinal : (p : ℝ) ≤ (pFinal : ℝ))
    (hincrementedFinal : ∀ e, (incremented R.source a e : ℝ) ≤ (pFinal : ℝ))
    (hboundaryIncrement : ∀ e ∈
        (R.restartQuery inletCenter incoming firstFlip secondFlip a k).boundarySupport n,
      ((R.restartQuery inletCenter incoming firstFlip secondFlip a k
        ).physicalBoundaryThreshold e : ℝ) + delta ≤
        (incremented R.source a e : ℝ))
    (hsuccess : X ∈ (R.restartQuery inletCenter incoming firstFlip secondFlip a k
      ).successEvent m n p delta) :
    thresholdConfiguration pFinal X ∈
      connectionEvent d anchor
        (R.selectedTarget hmn inletCenter incoming firstFlip secondFlip p delta X a k) := by
  let center := R.slotCenterFor inletCenter a k
  let flip := R.slotTransverseFlip incoming firstFlip secondFlip a k
  let F := cubicRestartFrameIso center a flip
  let Q := R.restartQuery inletCenter incoming firstFlip secondFlip a k
  let Xref := cubicGraphIsoCouplingReindex F X
  let W := R.selectedWitness hmn inletCenter incoming firstFlip secondFlip p delta X a k
  have hW : W.IsMixedRestartWitness Q.region p Q.beta delta Xref := by
    simpa [W, Q, Xref, F, center, flip] using
      R.selectedWitness_isMixed_of_success (hmn := hmn) inletCenter incoming
        firstFlip secondFlip p delta X a k hsuccess
  have hpSub : thresholdConfiguration p Xref ⊆ thresholdConfiguration pFinal Xref := by
    intro e he
    exact he.trans_le hpFinal
  have hWFinal : W.IsRealized (thresholdConfiguration pFinal Xref) :=
    RestartSeedWitnessIndex.IsRealized.mono hpSub
      (RestartSeedWitnessIndex.isRealized_thresholdConfiguration_of_isMixedRestartWitness hW)
  rcases hW.2 with ⟨e, heBoundary, hExterior, heIncrement⟩
  let inside := cubicRegionBoundaryInsideEndpoint Q.region e
  let outside := cubicRegionBoundaryOutsideEndpoint Q.region e
  have hinsideRegion : inside ∈ Q.region :=
    cubicRegionBoundaryInsideEndpoint_mem heBoundary
  have hinsideEndpoint : F inside ∈ cubicEdgeEndpointVertices R.source.explored := by
    change inside ∈ cubicEdgeEndpointVertices (R.source.referenceExploredEdges F) at hinsideRegion
    obtain ⟨f, hfReference, hinsideF⟩ :=
      mem_cubicEdgeEndpointVertices_iff.mp hinsideRegion
    have hfPhysical : F.mapEdgeSet f ∈ R.source.explored := by
      have hfImage : F.mapEdgeSet f ∈
          (R.source.referenceExploredEdges F).image F.mapEdgeSet :=
        Finset.mem_image.mpr ⟨f, hfReference, rfl⟩
      rw [R.source.referenceExploredEdges_image F] at hfImage
      exact hfImage
    apply mem_cubicEdgeEndpointVertices_iff.mpr
    refine ⟨F.mapEdgeSet f, hfPhysical, ?_⟩
    change F inside ∈ Sym2.map F (f : Sym2 (Cubic d))
    rw [Sym2.mem_map]
    exact ⟨inside, hinsideF, rfl⟩
  obtain ⟨f, hfSource, hinsideF⟩ :=
    mem_cubicEdgeEndpointVertices_iff.mp hinsideEndpoint
  have hAnchorInside : thresholdConfiguration pFinal X ∈
      connectionEvent d anchor (F inside) :=
    hrooted.2 f hfSource (F inside) hinsideF
  have hePhysicalBoundary : F.mapEdgeSet e ∈ Q.boundarySupport n := by
    rw [FramedRestartQuery.boundarySupport, framedBoundaryHistorySupport,
      Finset.mem_image]
    exact ⟨e, heBoundary, rfl⟩
  have heBound := hboundaryIncrement (F.mapEdgeSet e) hePhysicalBoundary
  have heFinalBound : (Q.beta e : ℝ) + delta ≤ (pFinal : ℝ) := by
    have hQframe : cubicRestartFrameIso Q.center Q.direction Q.transverseFlip = F := by
      rfl
    have heThreshold : Q.physicalBoundaryThreshold (F.mapEdgeSet e) = Q.beta e := by
      rw [FramedRestartQuery.physicalBoundaryThreshold, hQframe,
        F.mapEdgeSet.symm_apply_apply]
    rw [heThreshold] at heBound
    exact heBound.trans (hincrementedFinal (F.mapEdgeSet e))
  have heOpenRef : e ∈ thresholdConfiguration pFinal Xref := by
    change Xref e < (pFinal : ℝ)
    exact heIncrement.trans_le heFinalBound
  have hclearedSub : clearedThreshold
      (cubicRegionBoundaryEdgesWithinBox d Q.region n) p Xref ⊆
      thresholdConfiguration pFinal Xref := by
    intro f hf
    exact hf.1.trans_le hpFinal
  have hExteriorFinal : thresholdConfiguration pFinal Xref ∈
      connectionEventIn d (cubicRegionExteriorEdgesWithinBox d Q.region n)
        outside W.boundaryPoint.1 :=
    isIncreasingEvent_connectionEventIn d
      (cubicRegionExteriorEdgesWithinBox d Q.region n) outside W.boundaryPoint.1
      hclearedSub (by simpa [outside] using hExterior)
  have hinsideEdge : inside ∈ (e : Sym2 (Cubic d)) := by
    rw [← cubicRegionBoundaryEndpoints_edge heBoundary]
    simp [inside]
  have houtsideEdge : outside ∈ (e : Sym2 (Cubic d)) := by
    rw [← cubicRegionBoundaryEndpoints_edge heBoundary]
    simp [outside]
  have hInsideOutsideRef : thresholdConfiguration pFinal Xref ∈
      connectionEvent d inside outside :=
    mem_connectionEvent_of_mem_open_edge heOpenRef hinsideEdge houtsideEdge
  have hInsideBoundaryRef : thresholdConfiguration pFinal Xref ∈
      connectionEvent d inside W.boundaryPoint.1 :=
    connectionEvent_trans_mem hInsideOutsideRef
      (connectionEventIn_subset d _ outside W.boundaryPoint.1 hExteriorFinal)
  have hInsideBoundary : thresholdConfiguration pFinal X ∈
      connectionEvent d (F inside) (F W.boundaryPoint.1) := by
    simpa [F, center, flip, Xref] using
      thresholdConfiguration_mem_framedConnectionEvent center a flip pFinal X
        inside W.boundaryPoint.1 hInsideBoundaryRef
  have hBoundaryTargetRef : thresholdConfiguration pFinal Xref ∈
      connectionEvent d W.boundaryPoint.1 W.seedCenter.1 :=
    RestartSeedWitnessIndex.IsRealized.mem_connectionEvent_boundaryPoint_seedCenter hWFinal
  have hBoundaryTarget : thresholdConfiguration pFinal X ∈
      connectionEvent d (F W.boundaryPoint.1) (F W.seedCenter.1) := by
    simpa [F, center, flip, Xref] using
      thresholdConfiguration_mem_framedConnectionEvent center a flip pFinal X
        W.boundaryPoint.1 W.seedCenter.1 hBoundaryTargetRef
  exact connectionEvent_trans_mem hAnchorInside
    (connectionEvent_trans_mem hInsideBoundary (by
      simpa [selectedTarget, W, F, center, flip] using hBoundaryTarget))

/-- One successful runtime slot preserves the combined root-connected source invariant. -/
theorem rootedOpen_step_of_success
    {d m n : ℕ} {hmn : 2 * m ≤ n}
    (R : LaterSiteRuntime d) (inletCenter : Cubic d)
    (incoming : CubicDirection d) (firstFlip secondFlip : Fin d → Bool)
    (p pFinal : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) (anchor : Cubic d)
    (a : CubicDirection d) (k : ℕ)
    (hrooted : R.source.RootedOpen (thresholdConfiguration pFinal X) anchor)
    (hpFinal : (p : ℝ) ≤ (pFinal : ℝ))
    (hincrementedFinal : ∀ e, (incremented R.source a e : ℝ) ≤ (pFinal : ℝ)) :
    (R.step hmn inletCenter incoming firstFlip secondFlip p delta incremented X a k
      ).source.RootedOpen (thresholdConfiguration pFinal X) anchor := by
  exact R.source.rootedOpen_next
    ((R.restartQuery inletCenter incoming firstFlip secondFlip a k).restartSupport m n)
    p pFinal (incremented R.source a) X hrooted hpFinal hincrementedFinal

/-- The root-connected source invariant survives an arbitrary total runtime schedule.  No
success hypothesis is needed here: a rejected restart can reveal fewer edges, but every edge
that is actually added is still open at the final density and line-connected to the old source. -/
theorem rootedOpen_runFrom
    {d m n : ℕ} (hmn : 2 * m ≤ n)
    (inletCenter : Cubic d) (incoming : CubicDirection d)
    (firstFlip secondFlip : Fin d → Bool)
    (p pFinal : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) (anchor : Cubic d)
    (R : LaterSiteRuntime d) (offset : ℕ)
    (directions : List (CubicDirection d))
    (hrooted : R.source.RootedOpen (thresholdConfiguration pFinal X) anchor)
    (hpFinal : (p : ℝ) ≤ (pFinal : ℝ))
    (hincrementedFinal : ∀ S a e,
      (incremented S a e : ℝ) ≤ (pFinal : ℝ)) :
    (runFrom hmn inletCenter incoming firstFlip secondFlip p delta incremented X
      R offset directions).source.RootedOpen (thresholdConfiguration pFinal X) anchor := by
  induction directions generalizing R offset with
  | nil => exact hrooted
  | cons a rest ih =>
      apply ih
      exact R.rootedOpen_step_of_success (hmn := hmn) inletCenter incoming
        firstFlip secondFlip p pFinal delta incremented X anchor a offset
          hrooted hpFinal (hincrementedFinal R.source a)

/-- Every literal successful slot of a successful total schedule installs a target that is
connected to the original source anchor.  This is the slotwise deterministic bridge later used
by the history replay: it names the exact selected target, not an existential replacement. -/
theorem selectedTarget_connected_of_succeedsFrom
    {d m n : ℕ} {hmn : 2 * m ≤ n}
    (inletCenter : Cubic d) (incoming : CubicDirection d)
    (firstFlip secondFlip : Fin d → Bool)
    (p pFinal : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) (anchor : Cubic d)
    (R : LaterSiteRuntime d) (offset : ℕ)
    (directions : List (CubicDirection d))
    (hrooted : R.source.RootedOpen (thresholdConfiguration pFinal X) anchor)
    (hpFinal : (p : ℝ) ≤ (pFinal : ℝ))
    (hincrementedFinal : ∀ S a e,
      (incremented S a e : ℝ) ≤ (pFinal : ℝ))
    (hboundaryIncrement : ∀ j (hj : j < directions.length),
      let Rj := runFrom hmn inletCenter incoming firstFlip secondFlip
        p delta incremented X R offset (directions.take j)
      let a := directions[j]
      ∀ e ∈ (Rj.restartQuery inletCenter incoming firstFlip secondFlip a (offset + j)
        ).boundarySupport n,
        ((Rj.restartQuery inletCenter incoming firstFlip secondFlip a (offset + j)
          ).physicalBoundaryThreshold e : ℝ) + delta ≤
          (incremented Rj.source a e : ℝ))
    (hsuccess : succeedsFrom hmn inletCenter incoming firstFlip secondFlip
      p delta incremented X R offset directions)
    (j : ℕ) (hj : j < directions.length) :
    let Rj := runFrom hmn inletCenter incoming firstFlip secondFlip
      p delta incremented X R offset (directions.take j)
    let a := directions[j]
    thresholdConfiguration pFinal X ∈ connectionEvent d anchor
      (Rj.selectedTarget hmn inletCenter incoming firstFlip secondFlip
        p delta X a (offset + j)) := by
  let Rj := runFrom hmn inletCenter incoming firstFlip secondFlip
    p delta incremented X R offset (directions.take j)
  let a := directions[j]
  have hrootedJ : Rj.source.RootedOpen (thresholdConfiguration pFinal X) anchor := by
    exact rootedOpen_runFrom hmn inletCenter incoming firstFlip secondFlip p pFinal
      delta incremented X anchor R offset (directions.take j) hrooted hpFinal
        hincrementedFinal
  have hsuccessJ : X ∈
      (Rj.restartQuery inletCenter incoming firstFlip secondFlip a (offset + j)
        ).successEvent m n p delta := by
    simpa [Rj, a] using succeedsFrom_getElem hmn inletCenter incoming firstFlip secondFlip
      p delta incremented X R offset directions hsuccess j hj
  exact Rj.selectedTarget_connected_of_success (hmn := hmn) inletCenter incoming
    firstFlip secondFlip p pFinal delta incremented X anchor a (offset + j)
      hrootedJ hpFinal (hincrementedFinal Rj.source a)
      (hboundaryIncrement j hj) hsuccessJ

end LaterSiteRuntime

end Percolation
