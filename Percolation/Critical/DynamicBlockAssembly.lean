import Percolation.Critical.DynamicBlockCertificate
import Percolation.Critical.DynamicBlockGeometry
import Percolation.Critical.DynamicInitializedProgram
import Percolation.Critical.BondToSiteCritical

/-!
# Dynamic-block bond-percolation assembly

The adaptive restart program produces infinitely many accepted coarse sites.  This file supplies
the deterministic and measure-theoretic bridge from that conclusion to bond percolation in the
literal Grimmett--Marstrand thickening.  A concrete Chapter 7 program now only has to prove its
source-facing invariant: every accepted site center is connected to the root center by bonds open
at the final density.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval

theorem couplingMeasure_real_hasInfiniteOpenClusterInVertices_thresholdConfiguration
    (d : ℕ) (A : Set (Cubic d)) (p : I) :
    (couplingMeasure (CubicEdge d)).real
        ((thresholdConfiguration p) ⁻¹'
          {ω | hasInfiniteOpenClusterInVertices d A ω}) =
      regionHasInfiniteClusterProbability d A p := by
  unfold regionHasInfiniteClusterProbability bernoulliBondMeasure
  rw [← couplingMeasure_map_thresholdConfiguration (ι := CubicEdge d) p]
  simp only [Measure.real]
  rw [Measure.map_apply (measurable_thresholdConfiguration p)
    (measurableSet_hasInfiniteOpenClusterInVertices d A)]

namespace AdaptiveSiteExploration.FinitePartitionedOrientedRestartProgram

variable {C : Type*} [DecidableEq C]

/-- A concrete partitioned dynamic-block program percolates in the literal thickening once its
accepted-site centers carry open connections to the root center.  All other certificate fields
(root membership, distinct anchors, containment, and conversion from the uniform coupling to the
Bernoulli bond law) are discharged here. -/
theorem regionHasInfiniteClusterProbability_pos_dynamicBlock
    {d m n N : ℕ} {F : Set (Cubic d)} [LinearOrder F] (root : F)
    (hF : (cubicRegionGraph d F).Connected) (hd : 0 < d) (hN : 0 < N)
    (hsite1 : siteCriticalProbability (cubicRegionGraph d F) < 1)
    {pRestart : I} {delta : ℝ}
    (P : FinitePartitionedOrientedRestartProgram d F C m n pRestart delta
      (dynamicBlockRestartError d (siteCriticalProbability (cubicRegionGraph d F)))
      (2 * d + 1))
    (pBond : I)
    (hconnection : ∀ X v,
      v ∈ (cubicRegionSiteExploration d F root).toAdaptive.occupiedLimit
        (P.fullHistoryAnswer
          (cubicRegionSiteExploration d F root).initial.history X) →
      thresholdConfiguration pBond X ∈
        connectionEventWithinVertices d (grimmettMarstrandThickening d F N)
          (grimmettMarstrandSiteCenter N root)
          (grimmettMarstrandSiteCenter N v)) :
    0 < regionHasInfiniteClusterProbability d
      (grimmettMarstrandThickening d F N) pBond := by
  let E := (cubicRegionSiteExploration d F root).toAdaptive
  let answer := P.fullHistoryAnswer
    (cubicRegionSiteExploration d F root).initial.history
  have hinfinite :
      0 < (couplingMeasure (CubicEdge d)).real
        {X | (E.occupiedLimit (answer X)).Infinite} := by
    simpa [E, answer] using P.cubicRegion_infinite_probability_pos_dynamicBlock
      F root hF hd (siteCriticalProbability_nonneg _) hsite1
  have hroot : ∀ X, root ∈ E.occupiedLimit (answer X) := by
    intro X
    apply E.occupied_subset_occupiedLimit (answer X) 0
    exact (cubicRegionSiteExploration_initial_openRootedAt d F root).1
  have hsubset :
      {X | (E.occupiedLimit (answer X)).Infinite} ⊆
        (thresholdConfiguration pBond) ⁻¹'
          {ω | hasInfiniteOpenClusterInVertices d
            (grimmettMarstrandThickening d F N) ω} := by
    intro X hX
    apply hasInfiniteOpenClusterInVertices_of_infinite_anchor_connections
      hX (fun v : F ↦ grimmettMarstrandSiteCenter N v)
    · intro v _hv w _hw hvw
      exact Subtype.ext ((grimmettMarstrandSiteCenter_injective hN) hvw)
    · exact hroot X
    · intro v hv
      apply grimmettMarstrandSiteBox_subset_thickening v.2
      simp [grimmettMarstrandSiteBox, grimmettMarstrandSiteCenter,
        mem_cubicMetricBox]
    · intro v hv
      exact hconnection X v (by simpa [E, answer] using hv)
  rw [← couplingMeasure_real_hasInfiniteOpenClusterInVertices_thresholdConfiguration]
  exact hinfinite.trans_le (measureReal_mono hsubset)

/-- Order-theoretic Theorem 7.2(a) conclusion after the concrete program's connection invariant
has been verified. -/
theorem exists_regionCriticalProbability_thickening_le_add_dynamicBlock
    {d m n N : ℕ} {F : Set (Cubic d)} [LinearOrder F] (root : F)
    (hF : (cubicRegionGraph d F).Connected) (hd : 0 < d) (hN : 0 < N)
    (hsite1 : siteCriticalProbability (cubicRegionGraph d F) < 1)
    {pRestart : I} {delta : ℝ}
    (P : FinitePartitionedOrientedRestartProgram d F C m n pRestart delta
      (dynamicBlockRestartError d (siteCriticalProbability (cubicRegionGraph d F)))
      (2 * d + 1))
    (pBond : I) {eta : ℝ}
    (hpBond : (pBond : ℝ) ≤ regionCriticalProbability d F + eta)
    (hconnection : ∀ X v,
      v ∈ (cubicRegionSiteExploration d F root).toAdaptive.occupiedLimit
        (P.fullHistoryAnswer
          (cubicRegionSiteExploration d F root).initial.history X) →
      thresholdConfiguration pBond X ∈
        connectionEventWithinVertices d (grimmettMarstrandThickening d F N)
          (grimmettMarstrandSiteCenter N root)
          (grimmettMarstrandSiteCenter N v)) :
    ∃ k : ℕ,
      regionCriticalProbability d (cubicDilatedThickening d F k) ≤
        regionCriticalProbability d F + eta := by
  apply exists_regionCriticalProbability_thickening_le_add_of_dynamicPercolation hpBond
  exact P.regionHasInfiniteClusterProbability_pos_dynamicBlock
    root hF hd hN hsite1 pBond hconnection

/-- The dynamic-block assembly with its site-critical hypothesis discharged by the finite
incoming-green bond-to-site comparison. -/
theorem exists_regionCriticalProbability_thickening_le_add_dynamicBlock_of_bondCritical_lt_one
    {d m n N : ℕ} {F : Set (Cubic d)} [LinearOrder F] (root : F)
    (hF : (cubicRegionGraph d F).Connected) (hd : 2 ≤ d) (hN : 0 < N)
    (hcrit : regionCriticalProbability d F < 1)
    {pRestart : I} {delta : ℝ}
    (P : FinitePartitionedOrientedRestartProgram d F C m n pRestart delta
      (dynamicBlockRestartError d (siteCriticalProbability (cubicRegionGraph d F)))
      (2 * d + 1))
    (pBond : I) {eta : ℝ}
    (hpBond : (pBond : ℝ) ≤ regionCriticalProbability d F + eta)
    (hconnection : ∀ X v,
      v ∈ (cubicRegionSiteExploration d F root).toAdaptive.occupiedLimit
        (P.fullHistoryAnswer
          (cubicRegionSiteExploration d F root).initial.history X) →
      thresholdConfiguration pBond X ∈
        connectionEventWithinVertices d (grimmettMarstrandThickening d F N)
          (grimmettMarstrandSiteCenter N root)
          (grimmettMarstrandSiteCenter N v)) :
    ∃ k : ℕ,
      regionCriticalProbability d (cubicDilatedThickening d F k) ≤
        regionCriticalProbability d F + eta := by
  apply P.exists_regionCriticalProbability_thickening_le_add_dynamicBlock
    root hF (by omega) hN
    (siteCriticalProbability_lt_one_of_regionCriticalProbability_lt_one
      root hd hF hcrit)
    pBond hpBond
  exact hconnection

end AdaptiveSiteExploration.FinitePartitionedOrientedRestartProgram

namespace AdaptiveSiteExploration.InitializedFinitePartitionedRestartProgram

variable {C : Type*} [DecidableEq C]

/-- Source-faithful initialized dynamic-block assembly.  Only configurations in the proved
positive root event are used; on that event, every accepted coarse center is connected to the
root center at the final bond density. -/
theorem regionHasInfiniteClusterProbability_pos_initializedDynamicBlock
    {d m n N : ℕ} {F : Set (Cubic d)} [LinearOrder F] (root : F)
    (hF : (cubicRegionGraph d F).Connected) (hd : 0 < d) (hN : 0 < N)
    (hsite1 : siteCriticalProbability (cubicRegionGraph d F) < 1)
    {pRestart : I} {delta : ℝ}
    (P : InitializedFinitePartitionedRestartProgram d F C m n pRestart delta
      (dynamicBlockRestartError d (siteCriticalProbability (cubicRegionGraph d F)))
      (4 * d))
    (hadmissibleQuery : ∀ history,
      ((cubicRegionSiteExploration d F root).replayState history).frontier.Nonempty →
      P.admissible history
        ((cubicRegionSiteExploration d F root).replayQuery root history))
    (pBond : I)
    (hconnection : ∀ X, X ∈ P.initialEvent → ∀ v,
      v ∈ (cubicRegionSiteExploration d F root).toAdaptive.occupiedLimit
        (P.fullHistoryAnswer
          (cubicRegionSiteExploration d F root).initial.history X) →
      thresholdConfiguration pBond X ∈
        connectionEventWithinVertices d (grimmettMarstrandThickening d F N)
          (grimmettMarstrandSiteCenter N root)
          (grimmettMarstrandSiteCenter N v)) :
    0 < regionHasInfiniteClusterProbability d
      (grimmettMarstrandThickening d F N) pBond := by
  let E := (cubicRegionSiteExploration d F root).toAdaptive
  let answer := P.fullHistoryAnswer
    (cubicRegionSiteExploration d F root).initial.history
  have hinfinite :
      0 < (couplingMeasure (CubicEdge d)).real
        (P.initialEvent ∩ {X | (E.occupiedLimit (answer X)).Infinite}) := by
    simpa [E, answer] using P.cubicRegion_infinite_inter_probability_pos_dynamicBlock
      F root hF hd (siteCriticalProbability_nonneg _) hsite1 hadmissibleQuery
  have hroot : ∀ X, root ∈ E.occupiedLimit (answer X) := by
    intro X
    apply E.occupied_subset_occupiedLimit (answer X) 0
    exact (cubicRegionSiteExploration_initial_openRootedAt d F root).1
  have hsubset :
      P.initialEvent ∩ {X | (E.occupiedLimit (answer X)).Infinite} ⊆
        (thresholdConfiguration pBond) ⁻¹'
          {ω | hasInfiniteOpenClusterInVertices d
            (grimmettMarstrandThickening d F N) ω} := by
    intro X hX
    apply hasInfiniteOpenClusterInVertices_of_infinite_anchor_connections
      hX.2 (fun v : F ↦ grimmettMarstrandSiteCenter N v)
    · intro v _hv w _hw hvw
      exact Subtype.ext ((grimmettMarstrandSiteCenter_injective hN) hvw)
    · exact hroot X
    · intro v hv
      apply grimmettMarstrandSiteBox_subset_thickening v.2
      simp [grimmettMarstrandSiteBox, grimmettMarstrandSiteCenter,
        mem_cubicMetricBox]
    · intro v hv
      exact hconnection X hX.1 v (by simpa [E, answer] using hv)
  rw [← couplingMeasure_real_hasInfiniteOpenClusterInVertices_thresholdConfiguration]
  exact hinfinite.trans_le (measureReal_mono hsubset)

/-- Order-theoretic Theorem 7.2(a) adapter for the initialized source program. -/
theorem exists_regionCriticalProbability_thickening_le_add_initializedDynamicBlock
    {d m n N : ℕ} {F : Set (Cubic d)} [LinearOrder F] (root : F)
    (hF : (cubicRegionGraph d F).Connected) (hd : 2 ≤ d) (hN : 0 < N)
    (hcrit : regionCriticalProbability d F < 1)
    {pRestart : I} {delta : ℝ}
    (P : InitializedFinitePartitionedRestartProgram d F C m n pRestart delta
      (dynamicBlockRestartError d (siteCriticalProbability (cubicRegionGraph d F)))
      (4 * d))
    (hadmissibleQuery : ∀ history,
      ((cubicRegionSiteExploration d F root).replayState history).frontier.Nonempty →
      P.admissible history
        ((cubicRegionSiteExploration d F root).replayQuery root history))
    (pBond : I) {eta : ℝ}
    (hpBond : (pBond : ℝ) ≤ regionCriticalProbability d F + eta)
    (hconnection : ∀ X, X ∈ P.initialEvent → ∀ v,
      v ∈ (cubicRegionSiteExploration d F root).toAdaptive.occupiedLimit
        (P.fullHistoryAnswer
          (cubicRegionSiteExploration d F root).initial.history X) →
      thresholdConfiguration pBond X ∈
        connectionEventWithinVertices d (grimmettMarstrandThickening d F N)
          (grimmettMarstrandSiteCenter N root)
          (grimmettMarstrandSiteCenter N v)) :
    ∃ k : ℕ,
      regionCriticalProbability d (cubicDilatedThickening d F k) ≤
        regionCriticalProbability d F + eta := by
  apply exists_regionCriticalProbability_thickening_le_add_of_dynamicPercolation hpBond
  exact P.regionHasInfiniteClusterProbability_pos_initializedDynamicBlock
    root hF (by omega) hN
    (siteCriticalProbability_lt_one_of_regionCriticalProbability_lt_one
      root hd hF hcrit)
    hadmissibleQuery pBond hconnection

end AdaptiveSiteExploration.InitializedFinitePartitionedRestartProgram

namespace AdaptiveSiteExploration.InitializedPartitionedAdaptiveProgram

/-- Source-faithful dynamic-block assembly with realization-dependent seed anchors.  This is
the interface used by the executable history replay: block locations are selected by restart
witnesses and need not equal the deterministic coarse site centers. -/
theorem regionHasInfiniteClusterProbability_pos_initializedAdaptiveProgram_withAnchors
    {d m n N : ℕ} {F : Set (Cubic d)} [LinearOrder F] (root : F)
    (hF : (cubicRegionGraph d F).Connected) (hd : 0 < d)
    (hsite1 : siteCriticalProbability (cubicRegionGraph d F) < 1)
    (P : InitializedPartitionedAdaptiveProgram d F m n
      (dynamicBlockRestartError d (siteCriticalProbability (cubicRegionGraph d F)))
      (4 * d))
    (hadmissibleQuery : ∀ history,
      ((cubicRegionSiteExploration d F root).replayState history).frontier.Nonempty →
      P.admissible history
        ((cubicRegionSiteExploration d F root).replayQuery root history))
    (pBond : I) (anchor : (CubicEdge d → ℝ) → F → Cubic d)
    (hinjective : ∀ X, X ∈ P.initialEvent →
      Set.InjOn (anchor X)
        ((cubicRegionSiteExploration d F root).toAdaptive.occupiedLimit
          (P.fullHistoryAnswer
            (cubicRegionSiteExploration d F root).initial.history X)))
    (hcontained : ∀ X, X ∈ P.initialEvent → ∀ v,
      v ∈ (cubicRegionSiteExploration d F root).toAdaptive.occupiedLimit
        (P.fullHistoryAnswer
          (cubicRegionSiteExploration d F root).initial.history X) →
      anchor X v ∈ grimmettMarstrandThickening d F N)
    (hconnection : ∀ X, X ∈ P.initialEvent → ∀ v,
      v ∈ (cubicRegionSiteExploration d F root).toAdaptive.occupiedLimit
        (P.fullHistoryAnswer
          (cubicRegionSiteExploration d F root).initial.history X) →
      thresholdConfiguration pBond X ∈
        connectionEventWithinVertices d (grimmettMarstrandThickening d F N)
          (anchor X root) (anchor X v)) :
    0 < regionHasInfiniteClusterProbability d
      (grimmettMarstrandThickening d F N) pBond := by
  let E := (cubicRegionSiteExploration d F root).toAdaptive
  let answer := P.fullHistoryAnswer
    (cubicRegionSiteExploration d F root).initial.history
  have hinfinite :
      0 < (couplingMeasure (CubicEdge d)).real
        (P.initialEvent ∩ {X | (E.occupiedLimit (answer X)).Infinite}) := by
    simpa [E, answer] using P.cubicRegion_infinite_inter_probability_pos_dynamicBlock
      F root hF hd (siteCriticalProbability_nonneg _) hsite1 hadmissibleQuery
  have hroot : ∀ X, root ∈ E.occupiedLimit (answer X) := by
    intro X
    apply E.occupied_subset_occupiedLimit (answer X) 0
    exact (cubicRegionSiteExploration_initial_openRootedAt d F root).1
  have hsubset :
      P.initialEvent ∩ {X | (E.occupiedLimit (answer X)).Infinite} ⊆
        (thresholdConfiguration pBond) ⁻¹'
          {omega | hasInfiniteOpenClusterInVertices d
            (grimmettMarstrandThickening d F N) omega} := by
    intro X hX
    exact hasInfiniteOpenClusterInVertices_of_infinite_anchor_connections hX.2
      (anchor X) (hinjective X hX.1) (hroot X)
      (hcontained X hX.1) (hconnection X hX.1)
  rw [← couplingMeasure_real_hasInfiniteOpenClusterInVertices_thresholdConfiguration]
  exact hinfinite.trans_le (measureReal_mono hsubset)

/-- Order-theoretic Theorem 7.2(a) adapter for realization-dependent selected anchors. -/
theorem exists_regionCriticalProbability_thickening_le_add_initializedAdaptiveProgram_withAnchors
    {d m n N : ℕ} {F : Set (Cubic d)} [LinearOrder F] (root : F)
    (hF : (cubicRegionGraph d F).Connected) (hd : 2 ≤ d)
    (hcrit : regionCriticalProbability d F < 1)
    (P : InitializedPartitionedAdaptiveProgram d F m n
      (dynamicBlockRestartError d (siteCriticalProbability (cubicRegionGraph d F)))
      (4 * d))
    (hadmissibleQuery : ∀ history,
      ((cubicRegionSiteExploration d F root).replayState history).frontier.Nonempty →
      P.admissible history
        ((cubicRegionSiteExploration d F root).replayQuery root history))
    (pBond : I) {eta : ℝ}
    (hpBond : (pBond : ℝ) ≤ regionCriticalProbability d F + eta)
    (anchor : (CubicEdge d → ℝ) → F → Cubic d)
    (hinjective : ∀ X, X ∈ P.initialEvent →
      Set.InjOn (anchor X)
        ((cubicRegionSiteExploration d F root).toAdaptive.occupiedLimit
          (P.fullHistoryAnswer
            (cubicRegionSiteExploration d F root).initial.history X)))
    (hcontained : ∀ X, X ∈ P.initialEvent → ∀ v,
      v ∈ (cubicRegionSiteExploration d F root).toAdaptive.occupiedLimit
        (P.fullHistoryAnswer
          (cubicRegionSiteExploration d F root).initial.history X) →
      anchor X v ∈ grimmettMarstrandThickening d F N)
    (hconnection : ∀ X, X ∈ P.initialEvent → ∀ v,
      v ∈ (cubicRegionSiteExploration d F root).toAdaptive.occupiedLimit
        (P.fullHistoryAnswer
          (cubicRegionSiteExploration d F root).initial.history X) →
      thresholdConfiguration pBond X ∈
        connectionEventWithinVertices d (grimmettMarstrandThickening d F N)
          (anchor X root) (anchor X v)) :
    ∃ k : ℕ,
      regionCriticalProbability d (cubicDilatedThickening d F k) ≤
        regionCriticalProbability d F + eta := by
  apply exists_regionCriticalProbability_thickening_le_add_of_dynamicPercolation hpBond
  exact P.regionHasInfiniteClusterProbability_pos_initializedAdaptiveProgram_withAnchors
    root hF (by omega)
    (siteCriticalProbability_lt_one_of_regionCriticalProbability_lt_one
      root hd hF hcrit)
    hadmissibleQuery pBond anchor hinjective hcontained hconnection

/-- Dynamic-block assembly for the non-circular semantic-runtime interface. -/
theorem regionHasInfiniteClusterProbability_pos_initializedAdaptiveProgram
    {d m n N : ℕ} {F : Set (Cubic d)} [LinearOrder F] (root : F)
    (hF : (cubicRegionGraph d F).Connected) (hd : 0 < d) (hN : 0 < N)
    (hsite1 : siteCriticalProbability (cubicRegionGraph d F) < 1)
    (P : InitializedPartitionedAdaptiveProgram d F m n
      (dynamicBlockRestartError d (siteCriticalProbability (cubicRegionGraph d F)))
      (4 * d))
    (hadmissibleQuery : ∀ history,
      ((cubicRegionSiteExploration d F root).replayState history).frontier.Nonempty →
      P.admissible history
        ((cubicRegionSiteExploration d F root).replayQuery root history))
    (pBond : I)
    (hconnection : ∀ X, X ∈ P.initialEvent → ∀ v,
      v ∈ (cubicRegionSiteExploration d F root).toAdaptive.occupiedLimit
        (P.fullHistoryAnswer
          (cubicRegionSiteExploration d F root).initial.history X) →
      thresholdConfiguration pBond X ∈
        connectionEventWithinVertices d (grimmettMarstrandThickening d F N)
          (grimmettMarstrandSiteCenter N root)
          (grimmettMarstrandSiteCenter N v)) :
    0 < regionHasInfiniteClusterProbability d
      (grimmettMarstrandThickening d F N) pBond := by
  let E := (cubicRegionSiteExploration d F root).toAdaptive
  let answer := P.fullHistoryAnswer
    (cubicRegionSiteExploration d F root).initial.history
  have hinfinite :
      0 < (couplingMeasure (CubicEdge d)).real
        (P.initialEvent ∩ {X | (E.occupiedLimit (answer X)).Infinite}) := by
    simpa [E, answer] using P.cubicRegion_infinite_inter_probability_pos_dynamicBlock
      F root hF hd (siteCriticalProbability_nonneg _) hsite1 hadmissibleQuery
  have hroot : ∀ X, root ∈ E.occupiedLimit (answer X) := by
    intro X
    apply E.occupied_subset_occupiedLimit (answer X) 0
    exact (cubicRegionSiteExploration_initial_openRootedAt d F root).1
  have hsubset :
      P.initialEvent ∩ {X | (E.occupiedLimit (answer X)).Infinite} ⊆
        (thresholdConfiguration pBond) ⁻¹'
          {ω | hasInfiniteOpenClusterInVertices d
            (grimmettMarstrandThickening d F N) ω} := by
    intro X hX
    apply hasInfiniteOpenClusterInVertices_of_infinite_anchor_connections
      hX.2 (fun v : F ↦ grimmettMarstrandSiteCenter N v)
    · intro v _hv w _hw hvw
      exact Subtype.ext ((grimmettMarstrandSiteCenter_injective hN) hvw)
    · exact hroot X
    · intro v hv
      apply grimmettMarstrandSiteBox_subset_thickening v.2
      simp [grimmettMarstrandSiteBox, grimmettMarstrandSiteCenter,
        mem_cubicMetricBox]
    · intro v hv
      exact hconnection X hX.1 v (by simpa [E, answer] using hv)
  rw [← couplingMeasure_real_hasInfiniteOpenClusterInVertices_thresholdConfiguration]
  exact hinfinite.trans_le (measureReal_mono hsubset)

/-- Order-theoretic Theorem 7.2(a) adapter for an explicit semantic runtime. -/
theorem exists_regionCriticalProbability_thickening_le_add_initializedAdaptiveProgram
    {d m n N : ℕ} {F : Set (Cubic d)} [LinearOrder F] (root : F)
    (hF : (cubicRegionGraph d F).Connected) (hd : 2 ≤ d) (hN : 0 < N)
    (hcrit : regionCriticalProbability d F < 1)
    (P : InitializedPartitionedAdaptiveProgram d F m n
      (dynamicBlockRestartError d (siteCriticalProbability (cubicRegionGraph d F)))
      (4 * d))
    (hadmissibleQuery : ∀ history,
      ((cubicRegionSiteExploration d F root).replayState history).frontier.Nonempty →
      P.admissible history
        ((cubicRegionSiteExploration d F root).replayQuery root history))
    (pBond : I) {eta : ℝ}
    (hpBond : (pBond : ℝ) ≤ regionCriticalProbability d F + eta)
    (hconnection : ∀ X, X ∈ P.initialEvent → ∀ v,
      v ∈ (cubicRegionSiteExploration d F root).toAdaptive.occupiedLimit
        (P.fullHistoryAnswer
          (cubicRegionSiteExploration d F root).initial.history X) →
      thresholdConfiguration pBond X ∈
        connectionEventWithinVertices d (grimmettMarstrandThickening d F N)
          (grimmettMarstrandSiteCenter N root)
          (grimmettMarstrandSiteCenter N v)) :
    ∃ k : ℕ,
      regionCriticalProbability d (cubicDilatedThickening d F k) ≤
        regionCriticalProbability d F + eta := by
  apply exists_regionCriticalProbability_thickening_le_add_of_dynamicPercolation hpBond
  exact P.regionHasInfiniteClusterProbability_pos_initializedAdaptiveProgram
    root hF (by omega) hN
    (siteCriticalProbability_lt_one_of_regionCriticalProbability_lt_one
      root hd hF hcrit)
    hadmissibleQuery pBond hconnection

end AdaptiveSiteExploration.InitializedPartitionedAdaptiveProgram

end Percolation
