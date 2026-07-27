import Percolation.Critical.AdaptiveOuterConditioning
import Percolation.Critical.DynamicFramedRestartPartition

/-!
# Root-initialized partitioned restart programs

The root of the Grimmett--Marstrand coarse exploration is conditioned to contain a central seed
and successful initial branches.  Later sites use at most `4d` sequential restart applications:
two inlet link-ups and two applications for each fresh outgoing direction.  This
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

/-- Successful reveal-cell slices recover the same finite conjunction as their raw semantic
restart events.  At slot `j`, the slice is the raw event intersected with the literal outer
history and all preceding slices.  The statement is purely set-theoretic and removes the last
apparent circularity from a history-replayed partition construction. -/
theorem outer_finitePrefix_eq_of_stageSlice
    {Omega : Type*}
    (outer historyEvent : Set Omega)
    (raw sliced : ℕ → Set Omega)
    (hslice : ∀ j,
      sliced j = raw j ∩
        (outer ∩
          (finiteAdaptiveSuccessPrefix (fun (_ : List (Unit × Bool)) (_ : Unit) l ↦
            sliced l) [] () j ∩ historyEvent))) :
    ∀ k,
      outer ∩
          (finiteAdaptiveSuccessPrefix (fun (_ : List (Unit × Bool)) (_ : Unit) l ↦
            sliced l) [] () k ∩ historyEvent) =
        outer ∩
          (finiteAdaptiveSuccessPrefix (fun (_ : List (Unit × Bool)) (_ : Unit) l ↦
            raw l) [] () k ∩ historyEvent) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      rw [finiteAdaptiveSuccessPrefix_succ, finiteAdaptiveSuccessPrefix_succ,
        hslice k]
      calc
        outer ∩
            (((raw k ∩
                (outer ∩
                  (finiteAdaptiveSuccessPrefix
                    (fun (_ : List (Unit × Bool)) (_ : Unit) l ↦ sliced l) [] () k ∩
                      historyEvent))) ∩
              finiteAdaptiveSuccessPrefix
                (fun (_ : List (Unit × Bool)) (_ : Unit) l ↦ sliced l) [] () k) ∩
              historyEvent) =
            raw k ∩
              (outer ∩
                (finiteAdaptiveSuccessPrefix
                  (fun (_ : List (Unit × Bool)) (_ : Unit) l ↦ sliced l) [] () k ∩
                    historyEvent)) := by
          ext omega
          simp only [Set.mem_inter_iff]
          tauto
        _ = raw k ∩
              (outer ∩
                (finiteAdaptiveSuccessPrefix
                  (fun (_ : List (Unit × Bool)) (_ : Unit) l ↦ raw l) [] () k ∩
                    historyEvent)) := by
          rw [ih]
        _ = outer ∩
            (((raw k ∩
              finiteAdaptiveSuccessPrefix
                (fun (_ : List (Unit × Bool)) (_ : Unit) l ↦ raw l) [] () k) ∩
              historyEvent)) := by
          ext omega
          simp only [Set.mem_inter_iff]
          tauto

/-- Source-faithful dynamic program after root initialization.  The partition equation includes
the initialization event literally, so it remains valid under histories that reuse old edge
coordinates at larger thresholds. -/
structure InitializedFinitePartitionedRestartProgram
    (d : ℕ) (V C : Type*) [DecidableEq C]
    (m n : ℕ) (p : I) (delta epsilon : ℝ) (k : ℕ) where
  initialEvent : Set (CubicEdge d → ℝ)
  initialEvent_measurable : MeasurableSet initialEvent
  initialEvent_pos : 0 < (couplingMeasure (CubicEdge d)).real initialEvent
  /-- Histories and queried vertices for which the concrete replay program supplies an exact
  reveal-cell partition.  The source construction only needs this on genuine active queries. -/
  admissible : List (V × Bool) → V → Prop
  /-- Successful part of each concrete restart stage.  The finite classifier type may vary
  with the history and slot, so the initialized program stores its proved semantic outputs
  rather than imposing one artificial global cell type. -/
  stageSuccess : List (V × Bool) → V → ℕ → Set (CubicEdge d → ℝ)
  stageCellUnion : List (V × Bool) → V → ℕ → Set (CubicEdge d → ℝ)
  stageSuccess_measurable : ∀ history v j, MeasurableSet (stageSuccess history v j)
  stageSuccess_subset_cellUnion : ∀ history v j,
    stageSuccess history v j ⊆ stageCellUnion history v j
  stageSuccess_lower_bound : ∀ history v j,
    (1 - epsilon) * (couplingMeasure (CubicEdge d)).real
        (stageCellUnion history v j) ≤
      (couplingMeasure (CubicEdge d)).real (stageSuccess history v j)
  partition_eq : ∀ (history : List (V × Bool)) (v : V), admissible history v →
    ∀ (j : ℕ), j < k →
    initialEvent ∩
        (finiteAdaptiveSuccessPrefix
            stageSuccess history v j ∩
          adaptiveAnswerHistoryEvent
            (finiteAdaptiveSuccessAnswer
              stageSuccess k) history) =
      stageCellUnion history v j

/-- Root-initialized partitioned program with an explicit semantic answer.

The concrete Grimmett--Marstrand runtime is defined by replaying the complete preceding coarse
history and then checking its literal restart schedule.  Its finite reveal partitions are
successful *slices* of that semantic event, so defining the Boolean answer back from those
slices would be circular.  This interface keeps the runtime answer as data and requires one
final-prefix identity.  It is the exact non-circular form of the same null-safe composition
argument. -/
structure InitializedPartitionedAdaptiveProgram
    (d : ℕ) (V : Type*) (m n : ℕ) (epsilon : ℝ) (k : ℕ) where
  initialEvent : Set (CubicEdge d → ℝ)
  initialEvent_measurable : MeasurableSet initialEvent
  initialEvent_pos : 0 < (couplingMeasure (CubicEdge d)).real initialEvent
  answer : (CubicEdge d → ℝ) → List (V × Bool) → V → Bool
  answer_measurable : MeasurableAnswer answer
  admissible : List (V × Bool) → V → Prop
  stageSuccess : List (V × Bool) → V → ℕ → Set (CubicEdge d → ℝ)
  stageCellUnion : List (V × Bool) → V → ℕ → Set (CubicEdge d → ℝ)
  stageSuccess_measurable : ∀ history v j, MeasurableSet (stageSuccess history v j)
  stageSuccess_subset_cellUnion : ∀ history v j,
    stageSuccess history v j ⊆ stageCellUnion history v j
  stageSuccess_lower_bound : ∀ history v j,
    (1 - epsilon) * (couplingMeasure (CubicEdge d)).real
        (stageCellUnion history v j) ≤
      (couplingMeasure (CubicEdge d)).real (stageSuccess history v j)
  partition_eq : ∀ (history : List (V × Bool)) (v : V), admissible history v →
    ∀ (j : ℕ), j < k →
    initialEvent ∩
        (finiteAdaptiveSuccessPrefix stageSuccess history v j ∩
          adaptiveAnswerHistoryEvent answer history) =
      stageCellUnion history v j
  answer_true_eq_finalPrefix : ∀ (history : List (V × Bool)) (v : V),
    admissible history v →
    initialEvent ∩ adaptiveAnswerHistoryEvent answer (history ++ [(v, true)]) =
      initialEvent ∩
        (finiteAdaptiveSuccessPrefix stageSuccess history v k ∩
          adaptiveAnswerHistoryEvent answer history)

namespace InitializedPartitionedAdaptiveProgram

variable {d m n k : ℕ} {epsilon : ℝ}
    (P : InitializedPartitionedAdaptiveProgram d V m n epsilon k)

/-- Exact reveal-cell stages compose for the explicit history-replayed answer. -/
theorem hasAdaptiveAnswerLowerBoundWithin (hepsilon : epsilon ≤ 1) :
    HasAdaptiveAnswerLowerBoundWithin (couplingMeasure (CubicEdge d)) P.initialEvent
      P.answer P.admissible ((1 - epsilon) ^ k) := by
  intro history v hadmissible
  let H := adaptiveAnswerHistoryEvent P.answer history
  have hstep : ∀ j < k,
      (1 - epsilon) * (couplingMeasure (CubicEdge d)).real
          (P.initialEvent ∩
            (finiteAdaptiveSuccessPrefix P.stageSuccess history v j ∩ H)) ≤
        (couplingMeasure (CubicEdge d)).real
          (P.initialEvent ∩
            (finiteAdaptiveSuccessPrefix P.stageSuccess history v (j + 1) ∩ H)) := by
    intro j hj
    have hpartition :
        P.initialEvent ∩
            (finiteAdaptiveSuccessPrefix P.stageSuccess history v j ∩ H) =
          P.stageCellUnion history v j := by
      simpa [H] using P.partition_eq history v hadmissible j hj
    have hprefix :
        finiteAdaptiveSuccessPrefix P.stageSuccess history v (j + 1) =
          P.stageSuccess history v j ∩
            finiteAdaptiveSuccessPrefix P.stageSuccess history v j :=
      finiteAdaptiveSuccessPrefix_succ _ _ _ _
    have hnext :
        P.initialEvent ∩
            (finiteAdaptiveSuccessPrefix P.stageSuccess history v (j + 1) ∩ H) =
          P.stageSuccess history v j := by
      rw [hprefix]
      calc
        P.initialEvent ∩
            ((P.stageSuccess history v j ∩
                finiteAdaptiveSuccessPrefix P.stageSuccess history v j) ∩ H) =
            P.stageSuccess history v j ∩
              (P.initialEvent ∩
                (finiteAdaptiveSuccessPrefix P.stageSuccess history v j ∩ H)) := by
          ext omega
          simp only [Set.mem_inter_iff]
          tauto
        _ = P.stageSuccess history v j ∩ P.stageCellUnion history v j := by
          rw [hpartition]
        _ = P.stageSuccess history v j :=
          Set.inter_eq_left.mpr (P.stageSuccess_subset_cellUnion history v j)
    rw [hpartition, hnext]
    exact P.stageSuccess_lower_bound history v j
  have hpow := pow_mul_measureReal_le_of_step
    (fun j ↦ P.initialEvent ∩
      (finiteAdaptiveSuccessPrefix P.stageSuccess history v j ∩ H))
    (1 - epsilon) (sub_nonneg.mpr hepsilon) k hstep
  calc
    (1 - epsilon) ^ k *
        (couplingMeasure (CubicEdge d)).real
          (P.initialEvent ∩ adaptiveAnswerHistoryEvent P.answer history) =
        (1 - epsilon) ^ k *
          (couplingMeasure (CubicEdge d)).real
            (P.initialEvent ∩
              (finiteAdaptiveSuccessPrefix P.stageSuccess history v 0 ∩ H)) := by
      simp [H]
    _ ≤ (couplingMeasure (CubicEdge d)).real
        (P.initialEvent ∩
          (finiteAdaptiveSuccessPrefix P.stageSuccess history v k ∩ H)) := by
      simpa using hpow
    _ = (couplingMeasure (CubicEdge d)).real
        (P.initialEvent ∩
          adaptiveAnswerHistoryEvent P.answer (history ++ [(v, true)])) := by
      rw [P.answer_true_eq_finalPrefix history v hadmissible]

/-- Install the semantic program after the rooted exploration's forced initial history. -/
noncomputable def fullHistoryAnswer (prior : List (V × Bool)) :
    (CubicEdge d → ℝ) → List (V × Bool) → V → Bool :=
  SiteExploration.realizePrefixedAdaptiveAnswer prior P.answer

theorem measurableAnswer_fullHistoryAnswer (prior : List (V × Bool)) :
    MeasurableAnswer (P.fullHistoryAnswer prior) :=
  SiteExploration.measurableAnswer_realizePrefixedAdaptiveAnswer P.answer_measurable prior

/-- The source-faithful `4d` runtime has the required coarse-site density. -/
theorem hasAdaptiveAnswerLowerBoundWithin_dynamicBlockSiteDensity
    {d : ℕ} (hd : 0 < d) {pcSite : ℝ}
    (hsite0 : 0 ≤ pcSite) (hsite1 : pcSite < 1)
    (P : InitializedPartitionedAdaptiveProgram d V m n
      (dynamicBlockRestartError d pcSite) (4 * d)) :
    HasAdaptiveAnswerLowerBoundWithin (couplingMeasure (CubicEdge d)) P.initialEvent
      P.answer P.admissible (dynamicBlockSiteDensity pcSite) := by
  apply (P.hasAdaptiveAnswerLowerBoundWithin
    ((dynamicBlockRestartError_le_one_eighth hd hsite0).trans (by norm_num))).mono_density
  exact (dynamicBlock_restartPow_gt_siteDensity hd hsite0 hsite1).le

/-- Initialized form of Lemma 7.24 for an explicit semantic runtime answer. -/
theorem cubicRegion_infinite_inter_probability_pos_dynamicBlock
    (F : Set (Cubic d)) [LinearOrder F] (root : F)
    (hF : (cubicRegionGraph d F).Connected) (hd : 0 < d)
    (hsite0 : 0 ≤ siteCriticalProbability (cubicRegionGraph d F))
    (hsite1 : siteCriticalProbability (cubicRegionGraph d F) < 1)
    (P : InitializedPartitionedAdaptiveProgram d F m n
      (dynamicBlockRestartError d (siteCriticalProbability (cubicRegionGraph d F)))
      (4 * d))
    (hadmissibleQuery : ∀ history,
      ((cubicRegionSiteExploration d F root).replayState history).frontier.Nonempty →
      P.admissible history
        ((cubicRegionSiteExploration d F root).replayQuery root history)) :
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
      (P.measurableAnswer_fullHistoryAnswer _) P.admissible
      (by simpa [fullHistoryAnswer] using
        hasAdaptiveAnswerLowerBoundWithin_dynamicBlockSiteDensity hd hsite0 hsite1 P)
      hadmissibleQuery

end InitializedPartitionedAdaptiveProgram

namespace InitializedFinitePartitionedRestartProgram

variable {d m n k : ℕ} {p : I} {delta epsilon : ℝ} [DecidableEq C]
    (P : InitializedFinitePartitionedRestartProgram d V C m n p delta epsilon k)

/-- The non-root coarse-site answer accepts exactly when its `k` restart extensions succeed. -/
noncomputable def answer :
    (CubicEdge d → ℝ) → List (V × Bool) → V → Bool :=
  finiteAdaptiveSuccessAnswer P.stageSuccess k

theorem measurableAnswer : MeasurableAnswer P.answer := by
  apply measurableAnswer_finiteAdaptiveSuccessAnswer
  exact P.stageSuccess_measurable

/-- Exact reveal-cell stages compose inside the positive root initialization event. -/
theorem hasAdaptiveAnswerLowerBoundWithin (hepsilon : epsilon ≤ 1) :
    HasAdaptiveAnswerLowerBoundWithin (couplingMeasure (CubicEdge d)) P.initialEvent
      P.answer P.admissible ((1 - epsilon) ^ k) := by
  apply hasAdaptiveAnswerLowerBoundWithin_finiteAdaptiveSuccessAnswer P.initialEvent
    P.stageSuccess k
      P.admissible (1 - epsilon) (sub_nonneg.mpr hepsilon)
  intro history v hadmissible j hj
  let H := adaptiveAnswerHistoryEvent P.answer history
  have hpartition :
      P.initialEvent ∩
          (finiteAdaptiveSuccessPrefix
              P.stageSuccess history v j ∩ H) =
        P.stageCellUnion history v j := by
    simpa [H, answer] using P.partition_eq history v hadmissible j hj
  have hprefix :
      finiteAdaptiveSuccessPrefix
          P.stageSuccess history v (j + 1) =
        P.stageSuccess history v j ∩
          finiteAdaptiveSuccessPrefix
            P.stageSuccess history v j := by
    exact finiteAdaptiveSuccessPrefix_succ _ _ _ _
  have hnext :
      P.initialEvent ∩
          (finiteAdaptiveSuccessPrefix
              P.stageSuccess history v (j + 1) ∩ H) =
        P.stageSuccess history v j := by
    rw [hprefix]
    calc
      P.initialEvent ∩
          (P.stageSuccess history v j ∩
              finiteAdaptiveSuccessPrefix
                P.stageSuccess history v j ∩ H) =
          P.stageSuccess history v j ∩
            (P.initialEvent ∩
              (finiteAdaptiveSuccessPrefix
                P.stageSuccess history v j ∩ H)) := by
        ext omega
        simp only [Set.mem_inter_iff]
        tauto
      _ = P.stageSuccess history v j ∩
          P.stageCellUnion history v j := by
        rw [hpartition]
      _ = P.stageSuccess history v j :=
        Set.inter_eq_left.mpr
          (P.stageSuccess_subset_cellUnion history v j)
  change (1 - epsilon) *
      (couplingMeasure (CubicEdge d)).real
        (P.initialEvent ∩
          (finiteAdaptiveSuccessPrefix
            P.stageSuccess history v j ∩ H)) ≤
    (couplingMeasure (CubicEdge d)).real
      (P.initialEvent ∩
        (finiteAdaptiveSuccessPrefix
          P.stageSuccess history v (j + 1) ∩ H))
  rw [hpartition, hnext]
  exact P.stageSuccess_lower_bound history v j

/-- Full-history oracle installed after the rooted exploration's forced-root history. -/
noncomputable def fullHistoryAnswer (prior : List (V × Bool)) :
    (CubicEdge d → ℝ) → List (V × Bool) → V → Bool :=
  SiteExploration.realizePrefixedAdaptiveAnswer prior P.answer

theorem measurableAnswer_fullHistoryAnswer (prior : List (V × Bool)) :
    MeasurableAnswer (P.fullHistoryAnswer prior) :=
  SiteExploration.measurableAnswer_realizePrefixedAdaptiveAnswer P.measurableAnswer prior

/-- The source-faithful `4d` non-root restart program has the target density inside the initialized
root event. -/
theorem hasAdaptiveAnswerLowerBoundWithin_dynamicBlockSiteDensity
    {d : ℕ} (hd : 0 < d) {pcSite : ℝ}
    (hsite0 : 0 ≤ pcSite) (hsite1 : pcSite < 1)
    (P : InitializedFinitePartitionedRestartProgram d V C m n p delta
      (dynamicBlockRestartError d pcSite) (4 * d)) :
    HasAdaptiveAnswerLowerBoundWithin (couplingMeasure (CubicEdge d)) P.initialEvent
      P.answer P.admissible (dynamicBlockSiteDensity pcSite) := by
  apply (P.hasAdaptiveAnswerLowerBoundWithin
    ((dynamicBlockRestartError_le_one_eighth hd hsite0).trans (by norm_num))).mono_density
  exact (dynamicBlock_restartPow_gt_siteDensity hd hsite0 hsite1).le

/-- Initialized form of Lemma 7.24 for the concrete dynamic-block density. -/
theorem cubicRegion_infinite_inter_probability_pos_dynamicBlock
    (F : Set (Cubic d)) [LinearOrder F] (root : F)
    (hF : (cubicRegionGraph d F).Connected) (hd : 0 < d)
    (hsite0 : 0 ≤ siteCriticalProbability (cubicRegionGraph d F))
    (hsite1 : siteCriticalProbability (cubicRegionGraph d F) < 1)
    (P : InitializedFinitePartitionedRestartProgram d F C m n p delta
      (dynamicBlockRestartError d (siteCriticalProbability (cubicRegionGraph d F)))
      (4 * d))
    (hadmissibleQuery : ∀ history,
      ((cubicRegionSiteExploration d F root).replayState history).frontier.Nonempty →
      P.admissible history
        ((cubicRegionSiteExploration d F root).replayQuery root history)) :
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
      (P.measurableAnswer_fullHistoryAnswer _) P.admissible
      (by simpa [fullHistoryAnswer] using
        hasAdaptiveAnswerLowerBoundWithin_dynamicBlockSiteDensity hd hsite0 hsite1 P)
      hadmissibleQuery

end InitializedFinitePartitionedRestartProgram

end AdaptiveSiteExploration

end Percolation
