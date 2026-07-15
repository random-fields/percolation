import Percolation.Critical.AdaptiveOuterConditioning
import Percolation.Critical.DynamicRestartPartition

/-!
# Root-initialized partitioned restart programs

The root of the Grimmett--Marstrand coarse exploration is conditioned to contain a central seed
and successful initial branches.  Later sites use `2d+1` sequential restart extensions.  This
file combines those two source features: exact reveal-cell partitions are required only inside
the positive initialization event, and Lemma 7.24 is applied through the conditional-measure
adapter from `AdaptiveOuterConditioning`.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval

namespace AdaptiveSiteExploration

variable {V C : Type*}

/-- Finite composition inside a fixed outer event. -/
theorem hasAdaptiveAnswerLowerBoundWithin_finiteAdaptiveSuccessAnswer
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} (outer : Set Omega)
    (stage : List (V × Bool) → V → ℕ → Set Omega) (k : ℕ)
    (admissible : List (V × Bool) → V → Prop) (q : ℝ) (hq : 0 ≤ q)
    (hstep : ∀ history v, admissible history v → ∀ j < k,
      q * mu.real (outer ∩
          (finiteAdaptiveSuccessPrefix stage history v j ∩
            adaptiveAnswerHistoryEvent (finiteAdaptiveSuccessAnswer stage k) history)) ≤
        mu.real (outer ∩
          (finiteAdaptiveSuccessPrefix stage history v (j + 1) ∩
            adaptiveAnswerHistoryEvent (finiteAdaptiveSuccessAnswer stage k) history))) :
    HasAdaptiveAnswerLowerBoundWithin mu outer
      (finiteAdaptiveSuccessAnswer stage k) admissible (q ^ k) := by
  intro history v hadmissible
  let H := adaptiveAnswerHistoryEvent (finiteAdaptiveSuccessAnswer stage k) history
  have hpow := pow_mul_measureReal_le_of_step
    (fun j => outer ∩ (finiteAdaptiveSuccessPrefix stage history v j ∩ H)) q hq k
    (fun j hj => hstep history v hadmissible j hj)
  simpa [finiteAdaptiveSuccessAnswer, H,
    adaptiveAnswerHistoryEvent_eventAdaptiveAnswer_append_true,
    Set.inter_comm, Set.inter_left_comm, Set.inter_assoc] using hpow

/-- Source-faithful dynamic program after root initialization.  The partition equation includes
the initialization event literally, so it remains valid under histories that reuse old edge
coordinates at larger thresholds. -/
structure InitializedFinitePartitionedRestartProgram
    (d : ℕ) (V C : Type*) [DecidableEq C]
    (m n : ℕ) (p : I) (delta epsilon : ℝ) (k : ℕ) where
  initialEvent : Set (CubicEdge d → ℝ)
  initialEvent_measurable : MeasurableSet initialEvent
  initialEvent_pos : 0 < (couplingMeasure (CubicEdge d)).real initialEvent
  stage : List (V × Bool) → V → ℕ →
    PartitionedOrientedRestartStage d C m n p delta epsilon
  partition_eq : ∀ (history : List (V × Bool)) (v : V) (j : ℕ), j < k →
    initialEvent ∩
        (finiteAdaptiveSuccessPrefix
            (finitePartitionedRestartStageFamily stage) history v j ∩
          adaptiveAnswerHistoryEvent
            (finiteAdaptiveSuccessAnswer
              (finitePartitionedRestartStageFamily stage) k) history) =
      (stage history v j).cellUnion

namespace InitializedFinitePartitionedRestartProgram

variable {d m n k : ℕ} {p : I} {delta epsilon : ℝ} [DecidableEq C]
    (P : InitializedFinitePartitionedRestartProgram d V C m n p delta epsilon k)

/-- The non-root coarse-site answer accepts exactly when its `k` restart extensions succeed. -/
noncomputable def answer :
    (CubicEdge d → ℝ) → List (V × Bool) → V → Bool :=
  finiteAdaptiveSuccessAnswer (finitePartitionedRestartStageFamily P.stage) k

theorem measurableAnswer : MeasurableAnswer P.answer := by
  apply measurableAnswer_finiteAdaptiveSuccessAnswer
  intro history v j
  exact (P.stage history v j).measurableSet_successEvent

/-- Exact reveal-cell stages compose inside the positive root initialization event. -/
theorem hasAdaptiveAnswerLowerBoundWithin (hepsilon : epsilon ≤ 1) :
    HasAdaptiveAnswerLowerBoundWithin (couplingMeasure (CubicEdge d)) P.initialEvent
      P.answer (fun _ _ => True) ((1 - epsilon) ^ k) := by
  apply hasAdaptiveAnswerLowerBoundWithin_finiteAdaptiveSuccessAnswer P.initialEvent
    (finitePartitionedRestartStageFamily P.stage) k
      (fun _ _ => True) (1 - epsilon) (sub_nonneg.mpr hepsilon)
  intro history v _ j hj
  let H := adaptiveAnswerHistoryEvent P.answer history
  have hpartition :
      P.initialEvent ∩
          (finiteAdaptiveSuccessPrefix
              (finitePartitionedRestartStageFamily P.stage) history v j ∩ H) =
        (P.stage history v j).cellUnion := by
    simpa [H, answer] using P.partition_eq history v j hj
  have hprefix :
      finiteAdaptiveSuccessPrefix
          (finitePartitionedRestartStageFamily P.stage) history v (j + 1) =
        (P.stage history v j).successEvent ∩
          finiteAdaptiveSuccessPrefix
            (finitePartitionedRestartStageFamily P.stage) history v j := by
    exact finiteAdaptiveSuccessPrefix_succ _ _ _ _
  have hnext :
      P.initialEvent ∩
          (finiteAdaptiveSuccessPrefix
              (finitePartitionedRestartStageFamily P.stage) history v (j + 1) ∩ H) =
        (P.stage history v j).successEvent := by
    rw [hprefix]
    calc
      P.initialEvent ∩
          ((P.stage history v j).successEvent ∩
              finiteAdaptiveSuccessPrefix
                (finitePartitionedRestartStageFamily P.stage) history v j ∩ H) =
          (P.stage history v j).successEvent ∩
            (P.initialEvent ∩
              (finiteAdaptiveSuccessPrefix
                (finitePartitionedRestartStageFamily P.stage) history v j ∩ H)) := by
        ext omega
        simp only [Set.mem_inter_iff]
        tauto
      _ = (P.stage history v j).successEvent ∩
          (P.stage history v j).cellUnion := by
        rw [hpartition]
      _ = (P.stage history v j).successEvent :=
        Set.inter_eq_left.mpr
          (P.stage history v j).successEvent_subset_cellUnion
  change (1 - epsilon) *
      (couplingMeasure (CubicEdge d)).real
        (P.initialEvent ∩
          (finiteAdaptiveSuccessPrefix
            (finitePartitionedRestartStageFamily P.stage) history v j ∩ H)) ≤
    (couplingMeasure (CubicEdge d)).real
      (P.initialEvent ∩
        (finiteAdaptiveSuccessPrefix
          (finitePartitionedRestartStageFamily P.stage) history v (j + 1) ∩ H))
  rw [hpartition, hnext]
  exact (P.stage history v j).success_lower_bound

/-- Full-history oracle installed after the rooted exploration's forced-root history. -/
noncomputable def fullHistoryAnswer (prior : List (V × Bool)) :
    (CubicEdge d → ℝ) → List (V × Bool) → V → Bool :=
  SiteExploration.realizePrefixedAdaptiveAnswer prior P.answer

theorem measurableAnswer_fullHistoryAnswer (prior : List (V × Bool)) :
    MeasurableAnswer (P.fullHistoryAnswer prior) :=
  SiteExploration.measurableAnswer_realizePrefixedAdaptiveAnswer P.measurableAnswer prior

/-- The `2d+1` non-root extension program has the source target density inside the initialized
root event. -/
theorem hasAdaptiveAnswerLowerBoundWithin_dynamicBlockSiteDensity
    {d : ℕ} (hd : 0 < d) {pcSite : ℝ}
    (hsite0 : 0 ≤ pcSite) (hsite1 : pcSite < 1)
    (P : InitializedFinitePartitionedRestartProgram d V C m n p delta
      (dynamicBlockRestartError d pcSite) (2 * d + 1)) :
    HasAdaptiveAnswerLowerBoundWithin (couplingMeasure (CubicEdge d)) P.initialEvent
      P.answer (fun _ _ => True) (dynamicBlockSiteDensity pcSite) := by
  apply (P.hasAdaptiveAnswerLowerBoundWithin
    ((dynamicBlockRestartError_le_one_eighth hd hsite0).trans (by norm_num))).mono_density
  exact (dynamicBlock_laterSiteRestartPow_gt_siteDensity hd hsite0 hsite1).le

/-- Initialized form of Lemma 7.24 for the concrete dynamic-block density. -/
theorem cubicRegion_infinite_inter_probability_pos_dynamicBlock
    (F : Set (Cubic d)) [LinearOrder F] (root : F)
    (hF : (cubicRegionGraph d F).Connected) (hd : 0 < d)
    (hsite0 : 0 ≤ siteCriticalProbability (cubicRegionGraph d F))
    (hsite1 : siteCriticalProbability (cubicRegionGraph d F) < 1)
    (P : InitializedFinitePartitionedRestartProgram d F C m n p delta
      (dynamicBlockRestartError d (siteCriticalProbability (cubicRegionGraph d F)))
      (2 * d + 1)) :
    0 < (couplingMeasure (CubicEdge d)).real (P.initialEvent ∩ {omega |
      ((cubicRegionSiteExploration d F root).toAdaptive.occupiedLimit
        (P.fullHistoryAnswer
          (cubicRegionSiteExploration d F root).initial.history omega)).Infinite}) := by
  let q := dynamicBlockSiteDensityUnit
    (siteCriticalProbability (cubicRegionGraph d F)) hsite0 hsite1
  apply SiteExploration.cubicRegionSiteExploration_infinite_inter_probability_pos_of_adaptiveLowerBoundWithin
    d F root hF (couplingMeasure (CubicEdge d)) P.initialEvent
      P.initialEvent_measurable P.initialEvent_pos q
      (by simpa [q] using dynamicBlockSiteDensity_gt hsite1)
      (P.measurableAnswer_fullHistoryAnswer _)
  simpa [fullHistoryAnswer, q] using
    hasAdaptiveAnswerLowerBoundWithin_dynamicBlockSiteDensity hd hsite0 hsite1 P

end InitializedFinitePartitionedRestartProgram

end AdaptiveSiteExploration

end Percolation
