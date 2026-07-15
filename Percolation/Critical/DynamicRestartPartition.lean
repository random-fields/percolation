import Percolation.Critical.DynamicBlockAnswerLaw

/-!
# Finite reveal-cell partitions for dynamic restarts

The explored region in Grimmett's dynamic construction is random.  A coarse Boolean exploration
history therefore does not determine the region `R` or its heterogeneous boundary thresholds.
This file supplies the missing semantic layer: one restart stage is partitioned into finitely
many exact reveal cells, and each cell carries its own oriented restart query.  Lemma 7.17 is
applied on every cell and the ratio-free estimates are summed before the stage is exposed as one
Boolean coarse-site event.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval

namespace AdaptiveSiteExploration

variable {V C : Type*}

/-- One random-region restart stage, represented by finitely many exact reveal cells.  The
`past` part of a cell is measurable on coordinates disjoint from the cell's restart support;
the remaining part is exactly the closed-boundary history required by Lemma 7.17. -/
structure PartitionedOrientedRestartStage
    (d : ℕ) (C : Type*) [DecidableEq C]
    (m n : ℕ) (p : I) (delta epsilon : ℝ) where
  cells : Finset C
  query : C → OrientedRestartQuery d
  pastSupport : C → Finset (CubicEdge d)
  past : C → Set (CubicEdge d → ℝ)
  past_measurable : ∀ c ∈ cells,
    MeasurableSet[coordSigma (CubicEdge d)
      (pastSupport c : Set (CubicEdge d))] (past c)
  fresh : ∀ c ∈ cells,
    Disjoint (pastSupport c : Set (CubicEdge d))
      ((query c).restartSupport m n : Set (CubicEdge d))
  pairwise_cells : Set.PairwiseDisjoint (cells : Set C) fun c =>
    past c ∩ (query c).boundaryHistoryEvent n
  restart_gt : ∀ c ∈ cells,
    (1 - epsilon) *
        (couplingMeasure (CubicEdge d)).real
          ((query c).boundaryHistoryEvent n) <
      (couplingMeasure (CubicEdge d)).real
        ((query c).successEvent m n p delta ∩
          (query c).boundaryHistoryEvent n)

namespace PartitionedOrientedRestartStage

variable {d m n : ℕ} {p : I} {delta epsilon : ℝ} [DecidableEq C]
    (S : PartitionedOrientedRestartStage d C m n p delta epsilon)

/-- Exact reveal cell, including the closed boundary at the cell's current threshold profile. -/
def cell (c : C) : Set (CubicEdge d → ℝ) :=
  S.past c ∩ (S.query c).boundaryHistoryEvent n

/-- Successful portion of one reveal cell. -/
def successfulCell (c : C) : Set (CubicEdge d → ℝ) :=
  (S.query c).successEvent m n p delta ∩ S.cell c

/-- The history slice partitioned by this stage. -/
def cellUnion : Set (CubicEdge d → ℝ) :=
  ⋃ c ∈ S.cells, S.cell c

/-- The single Boolean success event exposed to the coarse exploration. -/
def successEvent : Set (CubicEdge d → ℝ) :=
  ⋃ c ∈ S.cells, S.successfulCell c

theorem measurableSet_cell (c : C) (hc : c ∈ S.cells) :
    MeasurableSet (S.cell c) := by
  have hpast : MeasurableSet (S.past c) :=
    (coordSigma_le _) _ (S.past_measurable c hc)
  have hboundary : MeasurableSet ((S.query c).boundaryHistoryEvent n) :=
    measurableSet_orientedBoundaryClosedHistoryEvent_coordSigma
      (S.query c).center (S.query c).direction (S.query c).region n
        (S.query c).beta
      |> fun h => (coordSigma_le _) _ h
  exact hpast.inter hboundary

theorem measurableSet_successfulCell (c : C) (hc : c ∈ S.cells) :
    MeasurableSet (S.successfulCell c) := by
  have hsuccess : MeasurableSet ((S.query c).successEvent m n p delta) :=
    (coordSigma_le _) _ ((S.query c).measurableSet_successEvent_coordSigma m n p delta)
  exact hsuccess.inter (S.measurableSet_cell c hc)

theorem measurableSet_successEvent : MeasurableSet S.successEvent := by
  apply MeasurableSet.biUnion S.cells.countable_toSet
  intro c hc
  exact S.measurableSet_successfulCell c hc

theorem successfulCell_subset_cell (c : C) : S.successfulCell c ⊆ S.cell c :=
  Set.inter_subset_right

theorem successEvent_subset_cellUnion : S.successEvent ⊆ S.cellUnion := by
  intro omega homega
  simp only [successEvent, Set.mem_iUnion] at homega
  obtain ⟨c, hc, hsuccess⟩ := homega
  exact Set.mem_iUnion_of_mem c <| Set.mem_iUnion_of_mem hc
    (S.successfulCell_subset_cell c hsuccess)

/-- Cellwise Lemma 7.17 bounds glue to one null-safe stage lower bound. -/
theorem success_lower_bound :
    (1 - epsilon) *
        (couplingMeasure (CubicEdge d)).real S.cellUnion ≤
      (couplingMeasure (CubicEdge d)).real S.successEvent := by
  apply mul_measureReal_le_partitionedSuccess S.cells S.cell S.successfulCell
    S.cellUnion (1 - epsilon) rfl S.pairwise_cells
  · exact S.measurableSet_cell
  · exact S.measurableSet_successfulCell
  · intro c _hc
    exact S.successfulCell_subset_cell c
  · intro c hc
    simpa only [successfulCell, cell, Set.inter_assoc] using
      orientedSprinkledRestart_inter_past_history_ge
        (S.query c).center (S.query c).direction (S.query c).region p
        (S.query c).beta delta epsilon (S.pastSupport c) (S.past c)
        (S.past_measurable c hc) (S.fresh c hc) (S.restart_gt c hc)

end PartitionedOrientedRestartStage

/-- Event family of a history-indexed finite program whose individual stages are finite reveal
partitions. -/
def finitePartitionedRestartStageFamily
    {d : ℕ} [DecidableEq C] {m n : ℕ} {p : I} {delta epsilon : ℝ}
    (stage : List (V × Bool) → V → ℕ →
      PartitionedOrientedRestartStage d C m n p delta epsilon) :
    List (V × Bool) → V → ℕ → Set (CubicEdge d → ℝ) :=
  fun history v j => (stage history v j).successEvent

/-- A finite dynamic block program with random explored regions.  At stage `j`, the exact outer
answer history together with the first `j` successes must be partitioned by the stage's reveal
cells.  Unlike `FiniteFreshOrientedRestartProgram`, no single query is incorrectly required to
be determined by the coarse Boolean history. -/
structure FinitePartitionedOrientedRestartProgram
    (d : ℕ) (V C : Type*) [DecidableEq C]
    (m n : ℕ) (p : I) (delta epsilon : ℝ) (k : ℕ) where
  stage : List (V × Bool) → V → ℕ →
    PartitionedOrientedRestartStage d C m n p delta epsilon
  partition_eq : ∀ (history : List (V × Bool)) (v : V) (j : ℕ), j < k →
    finiteAdaptiveSuccessPrefix
          (finitePartitionedRestartStageFamily stage) history v j ∩
        adaptiveAnswerHistoryEvent
          (finiteAdaptiveSuccessAnswer
            (finitePartitionedRestartStageFamily stage) k) history =
      (stage history v j).cellUnion

namespace FinitePartitionedOrientedRestartProgram

variable {d m n k : ℕ} {p : I} {delta epsilon : ℝ} [DecidableEq C]
    (P : FinitePartitionedOrientedRestartProgram d V C m n p delta epsilon k)

/-- The coarse-site answer accepts exactly when all partitioned restart stages succeed. -/
noncomputable def answer :
    (CubicEdge d → ℝ) → List (V × Bool) → V → Bool :=
  finiteAdaptiveSuccessAnswer (finitePartitionedRestartStageFamily P.stage) k

theorem measurableAnswer : MeasurableAnswer P.answer := by
  apply measurableAnswer_finiteAdaptiveSuccessAnswer
  intro history v j
  exact (P.stage history v j).measurableSet_successEvent

/-- Finite reveal-cell stages compose with the same source factor `(1-ε)^k`. -/
theorem hasAdaptiveAnswerLowerBound (hepsilon : epsilon ≤ 1) :
    HasAdaptiveAnswerLowerBoundOn (couplingMeasure (CubicEdge d)) P.answer
      (fun _ _ => True) ((1 - epsilon) ^ k) := by
  apply hasAdaptiveAnswerLowerBoundOn_finiteAdaptiveSuccessAnswer
    (finitePartitionedRestartStageFamily P.stage) k
      (fun _ _ => True) (1 - epsilon) (sub_nonneg.mpr hepsilon)
  intro history v _ j hj
  rw [finiteAdaptiveSuccessPrefix_succ, Set.inter_assoc,
    P.partition_eq history v j hj]
  have hlower := (P.stage history v j).success_lower_bound
  simpa only [finitePartitionedRestartStageFamily,
    Set.inter_eq_left.mpr (P.stage history v j).successEvent_subset_cellUnion] using hlower

/-- Full-history oracle installed in the rooted coarse-site exploration. -/
noncomputable def fullHistoryAnswer (prior : List (V × Bool)) :
    (CubicEdge d → ℝ) → List (V × Bool) → V → Bool :=
  SiteExploration.realizePrefixedAdaptiveAnswer prior P.answer

theorem measurableAnswer_fullHistoryAnswer (prior : List (V × Bool)) :
    MeasurableAnswer (P.fullHistoryAnswer prior) :=
  SiteExploration.measurableAnswer_realizePrefixedAdaptiveAnswer P.measurableAnswer prior

/-- The source parameter choice turns the concrete `2d+1`-extension program for a non-root
coarse site into a uniform lower bound strictly above the region's critical site density. -/
theorem hasAdaptiveAnswerLowerBound_dynamicBlockSiteDensity
    {d : ℕ} (hd : 0 < d) {pcSite : ℝ}
    (hsite0 : 0 ≤ pcSite) (hsite1 : pcSite < 1)
    (P : FinitePartitionedOrientedRestartProgram d V C m n p delta
      (dynamicBlockRestartError d pcSite) (2 * d + 1)) :
    HasAdaptiveAnswerLowerBoundOn (couplingMeasure (CubicEdge d)) P.answer
      (fun _ _ => True) (dynamicBlockSiteDensity pcSite) := by
  apply (P.hasAdaptiveAnswerLowerBound
    ((dynamicBlockRestartError_le_one_eighth hd hsite0).trans (by norm_num))).mono_density
  exact (dynamicBlock_laterSiteRestartPow_gt_siteDensity hd hsite0 hsite1).le

/-- A concrete partitioned restart program now plugs directly into source-facing Lemma 7.24. -/
theorem cubicRegion_infinite_probability_pos_dynamicBlock
    (F : Set (Cubic d)) [LinearOrder F] (root : F)
    (hF : (cubicRegionGraph d F).Connected) (hd : 0 < d)
    (hsite0 : 0 ≤ siteCriticalProbability (cubicRegionGraph d F))
    (hsite1 : siteCriticalProbability (cubicRegionGraph d F) < 1)
    (P : FinitePartitionedOrientedRestartProgram d F C m n p delta
      (dynamicBlockRestartError d (siteCriticalProbability (cubicRegionGraph d F)))
      (2 * d + 1)) :
    0 < (couplingMeasure (CubicEdge d)).real {omega |
      ((cubicRegionSiteExploration d F root).toAdaptive.occupiedLimit
        (P.fullHistoryAnswer
          (cubicRegionSiteExploration d F root).initial.history omega)).Infinite} := by
  let q := dynamicBlockSiteDensityUnit
    (siteCriticalProbability (cubicRegionGraph d F)) hsite0 hsite1
  apply SiteExploration.cubicRegionSiteExploration_infinite_probability_pos_of_adaptiveLowerBound
    d F root hF (couplingMeasure (CubicEdge d)) q
      (by simpa [q] using dynamicBlockSiteDensity_gt hsite1)
      (P.measurableAnswer_fullHistoryAnswer _)
  simpa [fullHistoryAnswer, q] using
    hasAdaptiveAnswerLowerBound_dynamicBlockSiteDensity hd hsite0 hsite1 P

end FinitePartitionedOrientedRestartProgram

end AdaptiveSiteExploration

end Percolation
