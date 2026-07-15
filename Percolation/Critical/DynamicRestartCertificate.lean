import Percolation.Critical.DynamicRevealFreshness

/-!
# Pathwise certificates for dynamic restart successes

The restart estimates in Lemma 7.17 are probability statements about a successful boundary
increment.  The Grimmett--Marstrand construction also needs their deterministic content: on a
successful label configuration, the newly opened boundary edge and the already exposed exterior
path give a genuine connection from the explored region to a fresh seeded target.  This file
records that implication at an arbitrary final density, with every threshold comparison explicit.
-/

namespace Percolation

open scoped unitInterval

/-- Reachability in the induced finite open graph is equivalent to a box-supported ambient open
walk in the direction needed by the restart construction.  `StaticLargeCrossing` contains the
reverse implication; keeping this direction here avoids unpacking induced-graph walks at every
restart stage. -/
theorem mem_connectionEventIn_of_finiteBoxOpenGraph_reachable
    {d n : ℕ} {omega : EdgeConfiguration d} {x u v : Cubic d}
    {hu : u ∈ cubicMetricBox d x n} {hv : v ∈ cubicMetricBox d x n}
    (hreach : (finiteBoxOpenGraph d omega x n).Reachable ⟨u, hu⟩ ⟨v, hv⟩) :
    omega ∈ connectionEventIn d (cubicBoxEdges d x n) u v := by
  let BoxVertex := {y : Cubic d // y ∈ cubicMetricBox d x n}
  have aux : ∀ {u' v' : BoxVertex},
      (finiteBoxOpenGraph d omega x n).Reachable u' v' →
        omega ∈ connectionEventIn d (cubicBoxEdges d x n) u'.1 v'.1 := by
    intro u' v' huvReach
    rcases huvReach with ⟨q⟩
    induction q with
    | nil =>
        refine ⟨SimpleGraph.Walk.nil, ?_, ?_⟩
        · intro e he
          simp at he
        · intro e he
          rw [mem_walkEdgeFinset_iff] at he
          simp at he
    | @cons u' v' w' huv tail ih =>
        rcases ih with ⟨tailAmbient, htailOpen, htailBox⟩
        have huvOpen : (cubicOpenGraph d omega).Adj u'.1 v'.1 := by
          exact SimpleGraph.induce_adj.mp huv
        obtain ⟨huvCubic, huvEdgeOpen⟩ := cubicOpenGraph_adj.mp huvOpen
        let headEdge : CubicEdge d :=
          ⟨s(u'.1, v'.1), (cubicGraph d).mem_edgeSet.mpr huvCubic⟩
        have headEdgeOpen : headEdge ∈ omega := by
          simpa [headEdge] using huvEdgeOpen
        have headEdgeBox : headEdge ∈ cubicBoxEdges d x n := by
          obtain ⟨a, ha⟩ :=
            (cubicGraph_adj_iff_exists_stepFrom u'.1 v'.1).mp huvCubic
          have heq : headEdge = cubicStepEdge u'.1 a := by
            apply Subtype.ext
            simp [headEdge, cubicStepEdge, ha]
          rw [heq]
          exact cubicStepEdge_mem_cubicBoxEdges u'.2 (by simpa [ha] using v'.2)
        let qAmbient : (cubicGraph d).Walk u'.1 w'.1 :=
          SimpleGraph.Walk.cons huvCubic tailAmbient
        refine ⟨qAmbient, ?_, ?_⟩
        · intro e he
          simp only [qAmbient, SimpleGraph.Walk.edges_cons, List.mem_cons] at he
          rcases he with he | he
          · have heHead :
                (⟨e, (SimpleGraph.Walk.cons huvCubic tailAmbient).edges_subset_edgeSet
                  (by simp [he])⟩ : CubicEdge d) = headEdge := by
              apply Subtype.ext
              simpa [headEdge] using he
            simpa [heHead] using headEdgeOpen
          · exact htailOpen e he
        · intro e he
          rw [mem_walkEdgeFinset_iff] at he
          simp only [qAmbient, SimpleGraph.Walk.edges_cons, List.mem_cons] at he
          rcases he with he | he
          · have heHead : e = headEdge := by
              apply Subtype.ext
              simpa [headEdge] using he
            simpa [heHead] using headEdgeBox
          · exact htailBox ((mem_walkEdgeFinset_iff tailAmbient e).mpr he)
  exact aux hreach

/-- A reference restart success gives an actual final-density connection from the explored
region to one of the seeded boundary targets.  The exterior path and the target seed were exposed
at density `p`; the last exit edge was exposed in the increment from `beta e` to
`beta e + delta`. -/
theorem sprinkledRestartEvent_subset_regionConnectionToSeededTarget
    {d m n : ℕ} {i : Fin d} {R : Finset (Cubic d)}
    {p pFinal : I} {beta : CubicEdge d → I} {delta : ℝ}
    (hpFinal : (p : ℝ) ≤ (pFinal : ℝ))
    (hboundaryFinal : ∀ e ∈ cubicRegionBoundaryEdgesWithinBox d R n,
      (beta e : ℝ) + delta ≤ (pFinal : ℝ))
    (hAvoid : RegionAvoidsSeededBoundaryQuadrant d i n R) :
    sprinkledRestartEvent d i m n R p beta delta ⊆
      {X | thresholdConfiguration pFinal X ∈
        regionConnectionToFiniteTargetEvent d R n
          (seededBoundaryPointFinset d i m n (thresholdConfiguration pFinal X))} := by
  classical
  intro X hsuccess
  let E := cubicRegionBoundaryEdgesWithinBox d R n
  let omegaFinal : EdgeConfiguration d := thresholdConfiguration pFinal X
  have hcleared : clearedThreshold E p X ⊆ omegaFinal := by
    intro e he
    change X e < (p : ℝ) ∧ e ∉ E at he
    change X e < (pFinal : ℝ)
    exact he.1.trans_le hpFinal
  rcases hsuccess with ⟨e, heAvailable, heIncrement⟩
  change e ∈ seededRegionAvailableExitEdges d i m n R (clearedThreshold E p X) at heAvailable
  rw [seededRegionAvailableExitEdges, mem_regionAvailableExitEdges_iff] at heAvailable
  rcases heAvailable with ⟨heBoundary, y, hyTarget, hExterior⟩
  have hySeeded : IsSeededBoundaryPoint d i m n omegaFinal y := by
    rw [mem_seededBoundaryPointFinset_iff] at hyTarget
    rcases hyTarget with ⟨hyQuadrant, hyOutward, c, hyCenter, hcLayer, hcSeed⟩
    refine ⟨hyQuadrant, hcleared hyOutward, c, hyCenter, hcLayer, ?_⟩
    exact isIncreasingEvent_cubicSeedEvent d c m hcleared hcSeed
  have hExteriorFinal : omegaFinal ∈
      connectionEventIn d (cubicRegionExteriorEdgesWithinBox d R n)
        (cubicRegionBoundaryOutsideEndpoint R e) y := by
    rcases hExterior with ⟨w, hwOpen, hwSupport⟩
    exact ⟨w, fun f hf ↦ hcleared (hwOpen f hf), hwSupport⟩
  have heAvailableFinal : e ∈ regionAvailableExitEdges d R n
      (seededBoundaryPointFinset d i m n omegaFinal) omegaFinal := by
    rw [mem_regionAvailableExitEdges_iff]
    exact ⟨heBoundary, y, mem_seededBoundaryPointFinset_iff.mpr hySeeded,
      hExteriorFinal⟩
  have htargetDisjoint :
      Disjoint (seededBoundaryPointFinset d i m n omegaFinal) R := by
    rw [Finset.disjoint_left]
    intro y hyTargetFinal hyR
    have hyQuadrant := (mem_seededBoundaryPointFinset_iff.mp hyTargetFinal).1
    exact Finset.disjoint_left.mp hAvoid.disjoint_quadrant_region hyQuadrant hyR
  apply (mem_regionConnectionToFiniteTargetEvent_iff_exists_open_availableExit
    htargetDisjoint).2
  refine ⟨e, heAvailableFinal, ?_⟩
  change X e < (pFinal : ℝ)
  exact heIncrement.trans_le (hboundaryFinal e heBoundary)

/-- When the region is the actual heterogeneous explored region, the previous certificate starts
at an inlet-seed vertex.  Thus a successful restart extends the connected seed chain by one new
seed, entirely inside the reference box support. -/
theorem exists_inletSeed_connectionToSeededTarget_of_sprinkledRestart
    {d m n : ℕ} {i : Fin d} {X : CubicEdge d → ℝ}
    {p pFinal : I} {beta : CubicEdge d → I} {delta : ℝ}
    (hpFinal : (p : ℝ) ≤ (pFinal : ℝ))
    (hbetaFinal : ∀ e, (beta e : ℝ) ≤ (pFinal : ℝ))
    (hboundaryFinal : ∀ e ∈ cubicRegionBoundaryEdgesWithinBox d
      (restartExploredRegion d (heterogeneousThresholdConfiguration beta X) m n) n,
      (beta e : ℝ) + delta ≤ (pFinal : ℝ))
    (hAvoid : RegionAvoidsSeededBoundaryQuadrant d i n
      (restartExploredRegion d (heterogeneousThresholdConfiguration beta X) m n))
    (hsuccess : X ∈ sprinkledRestartEvent d i m n
      (restartExploredRegion d (heterogeneousThresholdConfiguration beta X) m n)
      p beta delta) :
    ∃ z ∈ cubicMetricBox d cubicOrigin m,
      ∃ y ∈ seededBoundaryPointFinset d i m n (thresholdConfiguration pFinal X),
        thresholdConfiguration pFinal X ∈
          connectionEventIn d (cubicBoxEdges d cubicOrigin n) z y := by
  let omegaBeta : EdgeConfiguration d := heterogeneousThresholdConfiguration beta X
  let omegaFinal : EdgeConfiguration d := thresholdConfiguration pFinal X
  let R := restartExploredRegion d omegaBeta m n
  have hbetaSub : omegaBeta ⊆ omegaFinal := by
    intro e he
    change X e < (beta e : ℝ) at he
    change X e < (pFinal : ℝ)
    exact he.trans_le (hbetaFinal e)
  have hregionConnection : omegaFinal ∈
      regionConnectionToFiniteTargetEvent d R n
        (seededBoundaryPointFinset d i m n omegaFinal) := by
    exact sprinkledRestartEvent_subset_regionConnectionToSeededTarget
      hpFinal hboundaryFinal hAvoid hsuccess
  rcases hregionConnection with ⟨x, hxR, y, hyTarget, hxy⟩
  obtain ⟨hxBox, z, hzSeed, hzxReach⟩ :=
    mem_restartExploredRegion_iff.mp hxR
  have hzxBeta : omegaBeta ∈
      connectionEventIn d (cubicBoxEdges d cubicOrigin n) z x :=
    mem_connectionEventIn_of_finiteBoxOpenGraph_reachable hzxReach
  have hzxFinal : omegaFinal ∈
      connectionEventIn d (cubicBoxEdges d cubicOrigin n) z x :=
    isIncreasingEvent_connectionEventIn d (cubicBoxEdges d cubicOrigin n) z x
      hbetaSub hzxBeta
  rcases hzxFinal with ⟨q, hqOpen, hqBox⟩
  rcases hxy with ⟨w, hwOpen, hwBox⟩
  refine ⟨z, hzSeed, y, hyTarget, q.append w, walkIsOpen_append hqOpen hwOpen, ?_⟩
  intro e he
  rw [mem_walkEdgeFinset_iff, SimpleGraph.Walk.edges_append,
    List.mem_append] at he
  rcases he with he | he
  · exact hqBox ((mem_walkEdgeFinset_iff q e).mpr he)
  · exact hwBox ((mem_walkEdgeFinset_iff w e).mpr he)

/-- Signed-coordinate and translation transport of the inlet-to-new-seed certificate.  The
witnesses are retained in reference coordinates, while the displayed connection is the literal
physical connection read by an oriented restart stage. -/
theorem exists_orientedInletSeed_connectionToSeededTarget_of_sprinkledRestart
    {d m n : ℕ} (center : Cubic d) (a : CubicDirection d)
    {X : CubicEdge d → ℝ} {p pFinal : I}
    {beta : CubicEdge d → I} {delta : ℝ}
    (hpFinal : (p : ℝ) ≤ (pFinal : ℝ))
    (hbetaFinal : ∀ e, (beta e : ℝ) ≤ (pFinal : ℝ))
    (hboundaryFinal : ∀ e ∈ cubicRegionBoundaryEdgesWithinBox d
      (restartExploredRegion d
        (heterogeneousThresholdConfiguration beta
          (cubicGraphIsoCouplingReindex (cubicDirectionOrientationIso center a) X))
        m n) n,
      (beta e : ℝ) + delta ≤ (pFinal : ℝ))
    (hAvoid : RegionAvoidsSeededBoundaryQuadrant d a.1 n
      (restartExploredRegion d
        (heterogeneousThresholdConfiguration beta
          (cubicGraphIsoCouplingReindex (cubicDirectionOrientationIso center a) X))
        m n))
    (hsuccess : X ∈ orientedSprinkledRestartEvent center a m n
      (restartExploredRegion d
        (heterogeneousThresholdConfiguration beta
          (cubicGraphIsoCouplingReindex (cubicDirectionOrientationIso center a) X))
        m n)
      p beta delta) :
    ∃ z ∈ cubicMetricBox d cubicOrigin m,
      ∃ y ∈ seededBoundaryPointFinset d a.1 m n
          (thresholdConfiguration pFinal
            (cubicGraphIsoCouplingReindex (cubicDirectionOrientationIso center a) X)),
        thresholdConfiguration pFinal X ∈
          connectionEventIn d
            (cubicBoxEdges d center n)
            (cubicDirectionOrientationIso center a z)
            (cubicDirectionOrientationIso center a y) := by
  let Xref := cubicGraphIsoCouplingReindex (cubicDirectionOrientationIso center a) X
  have hsuccessRef : Xref ∈ sprinkledRestartEvent d a.1 m n
      (restartExploredRegion d (heterogeneousThresholdConfiguration beta Xref) m n)
      p beta delta := by
    exact hsuccess
  obtain ⟨z, hzSeed, y, hyTarget, hzy⟩ :=
    exists_inletSeed_connectionToSeededTarget_of_sprinkledRestart
      hpFinal hbetaFinal hboundaryFinal hAvoid hsuccessRef
  refine ⟨z, hzSeed, y, hyTarget, ?_⟩
  simpa [cubicDirectionOrientationIso_image_cubicBoxEdges_eq] using
    thresholdConfiguration_mem_orientedConnectionEventIn
      center a pFinal X (cubicBoxEdges d cubicOrigin n) z y hzy

/-- Reveal-cell form of the oriented certificate.  Equality with the realized finite cell is the
semantic fact supplied by the partition constructor; this theorem converts it into the exact
explored-region equality required by the pathwise restart lemma. -/
theorem exists_orientedInletSeed_connectionToSeededTarget_of_realizedCell
    {d m n : ℕ} (center : Cubic d) (a : CubicDirection d)
    (beta : CubicEdge d → I) (S : FiniteRevealSchedule (CubicEdge d))
    (hS : S.HasOverlapBound (2 * d + 1))
    (c : RestartRevealCellIndex d a.1 m n) {X : CubicEdge d → ℝ}
    {p pFinal : I} {delta : ℝ}
    (hpFinal : (p : ℝ) ≤ (pFinal : ℝ))
    (hbetaFinal : ∀ e, (beta e : ℝ) ≤ (pFinal : ℝ))
    (hboundaryFinal : ∀ e ∈ cubicRegionBoundaryEdgesWithinBox d c.regionVertices n,
      (beta e : ℝ) + delta ≤ (pFinal : ℝ))
    (hAvoid : RegionAvoidsSeededBoundaryQuadrant d a.1 n c.regionVertices)
    (hcell : orientedRealizedScheduleRevealCell center a beta S hS X = c)
    (hsuccess : X ∈ orientedSprinkledRestartEvent center a m n
      c.regionVertices p beta delta) :
    ∃ z ∈ cubicMetricBox d cubicOrigin m,
      ∃ y ∈ seededBoundaryPointFinset d a.1 m n
          (thresholdConfiguration pFinal
            (cubicGraphIsoCouplingReindex (cubicDirectionOrientationIso center a) X)),
        thresholdConfiguration pFinal X ∈
          connectionEventIn d (cubicBoxEdges d center n)
            (cubicDirectionOrientationIso center a z)
            (cubicDirectionOrientationIso center a y) := by
  have hregion : restartExploredRegion d
      (heterogeneousThresholdConfiguration beta
        (cubicGraphIsoCouplingReindex (cubicDirectionOrientationIso center a) X))
      m n = c.regionVertices := by
    exact congrArg RestartRevealCellIndex.regionVertices hcell
  apply exists_orientedInletSeed_connectionToSeededTarget_of_sprinkledRestart
    center a hpFinal hbetaFinal
  · simpa [hregion] using hboundaryFinal
  · simpa [hregion] using hAvoid
  · simpa [hregion] using hsuccess

end Percolation
