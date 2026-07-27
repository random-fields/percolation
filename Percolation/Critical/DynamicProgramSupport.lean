import Percolation.Critical.AdaptiveAnswerSupport
import Percolation.Critical.DynamicRevealFreshness

/-!
# Finite supports for multi-restart dynamic programs

One coarse-site answer is the intersection of finitely many restart stages.  At stage `j`, its
outer history is the intersection of the first `j` stage successes with the exact coarse-site
answer history.  This file computes a finite support for both pieces and proves the resulting
outer event measurable on their union.
-/

namespace Percolation

open MeasureTheory

namespace AdaptiveSiteExploration

variable {V ι : Type*} [DecidableEq ι]

/-- Union of the supports of the first `k` stage events. -/
def finiteAdaptiveSuccessPrefixSupport
    (stageSupport : List (V × Bool) → V → ℕ → Finset ι)
    (history : List (V × Bool)) (v : V) (k : ℕ) : Finset ι :=
  (Finset.range k).biUnion fun j => stageSupport history v j

@[simp]
theorem finiteAdaptiveSuccessPrefixSupport_zero
    (stageSupport : List (V × Bool) → V → ℕ → Finset ι)
    (history : List (V × Bool)) (v : V) :
    finiteAdaptiveSuccessPrefixSupport stageSupport history v 0 = ∅ := by
  simp [finiteAdaptiveSuccessPrefixSupport]

theorem finiteAdaptiveSuccessPrefixSupport_succ
    (stageSupport : List (V × Bool) → V → ℕ → Finset ι)
    (history : List (V × Bool)) (v : V) (k : ℕ) :
    finiteAdaptiveSuccessPrefixSupport stageSupport history v (k + 1) =
      stageSupport history v k ∪
        finiteAdaptiveSuccessPrefixSupport stageSupport history v k := by
  ext e
  simp only [finiteAdaptiveSuccessPrefixSupport, Finset.mem_biUnion, Finset.mem_range,
    Finset.mem_union]
  constructor
  · rintro ⟨j, hj, he⟩
    by_cases hjk : j = k
    · exact Or.inl (hjk ▸ he)
    · exact Or.inr ⟨j, by omega, he⟩
  · rintro (he | ⟨j, hj, he⟩)
    · exact ⟨k, by omega, he⟩
    · exact ⟨j, by omega, he⟩

/-- Every stage event is measurable on its advertised coordinate support. -/
def HasFiniteStageSupports
    (stage : List (V × Bool) → V → ℕ → Set (ι → ℝ))
    (stageSupport : List (V × Bool) → V → ℕ → Finset ι) : Prop :=
  ∀ history v j, @MeasurableSet (ι → ℝ)
    (coordSigma ι (stageSupport history v j : Set ι)) (stage history v j)

theorem measurableSet_finiteAdaptiveSuccessPrefix_coordSigma
    {stage : List (V × Bool) → V → ℕ → Set (ι → ℝ)}
    {stageSupport : List (V × Bool) → V → ℕ → Finset ι}
    (hstage : HasFiniteStageSupports stage stageSupport)
    (history : List (V × Bool)) (v : V) (k : ℕ) :
    @MeasurableSet (ι → ℝ)
      (coordSigma ι
        (finiteAdaptiveSuccessPrefixSupport stageSupport history v k : Set ι))
      (finiteAdaptiveSuccessPrefix stage history v k) := by
  apply MeasurableSet.biInter (Finset.range k).countable_toSet
  intro j hj
  apply (coordSigma_mono fun e he => Finset.mem_biUnion.mpr ⟨j, hj, he⟩)
  exact hstage history v j

theorem hasFiniteAnswerSupports_finiteAdaptiveSuccessAnswer
    {stage : List (V × Bool) → V → ℕ → Set (ι → ℝ)}
    {stageSupport : List (V × Bool) → V → ℕ → Finset ι}
    (hstage : HasFiniteStageSupports stage stageSupport) (k : ℕ) :
    HasFiniteAnswerSupports (finiteAdaptiveSuccessAnswer stage k)
      (fun history v => finiteAdaptiveSuccessPrefixSupport stageSupport history v k) := by
  intro history v b
  cases b
  · have hmeas := measurableSet_finiteAdaptiveSuccessPrefix_coordSigma
      hstage history v k
    have hset : {X | finiteAdaptiveSuccessAnswer stage k X history v = false} =
        (finiteAdaptiveSuccessPrefix stage history v k)ᶜ := by
      ext X
      simp [finiteAdaptiveSuccessAnswer, eventAdaptiveAnswer]
    rw [hset]
    exact hmeas.compl
  · have hset : {X | finiteAdaptiveSuccessAnswer stage k X history v = true} =
        finiteAdaptiveSuccessPrefix stage history v k := by
      ext X
      simp [finiteAdaptiveSuccessAnswer]
    rw [hset]
    exact measurableSet_finiteAdaptiveSuccessPrefix_coordSigma hstage history v k

/-- Support of the literal outer event used before adjoining restart stage `j`. -/
def finiteAdaptiveOuterHistorySupport
    (stageSupport : List (V × Bool) → V → ℕ → Finset ι)
    (answerSupport : List (V × Bool) → V → Finset ι)
    (history : List (V × Bool)) (v : V) (j : ℕ) : Finset ι :=
  finiteAdaptiveSuccessPrefixSupport stageSupport history v j ∪
    adaptiveAnswerHistorySupport answerSupport history

/-- Literal event used before adjoining restart stage `j`. -/
def finiteAdaptiveOuterHistoryEvent
    (stage : List (V × Bool) → V → ℕ → Set (ι → ℝ))
    (answer : (ι → ℝ) → List (V × Bool) → V → Bool)
    (history : List (V × Bool)) (v : V) (j : ℕ) : Set (ι → ℝ) :=
  finiteAdaptiveSuccessPrefix stage history v j ∩
    adaptiveAnswerHistoryEvent answer history

theorem measurableSet_finiteAdaptiveOuterHistoryEvent_coordSigma
    {stage : List (V × Bool) → V → ℕ → Set (ι → ℝ)}
    {stageSupport : List (V × Bool) → V → ℕ → Finset ι}
    {answer : (ι → ℝ) → List (V × Bool) → V → Bool}
    {answerSupport : List (V × Bool) → V → Finset ι}
    (hstage : HasFiniteStageSupports stage stageSupport)
    (hanswer : HasFiniteAnswerSupports answer answerSupport)
    (history : List (V × Bool)) (v : V) (j : ℕ) :
    @MeasurableSet (ι → ℝ)
      (coordSigma ι
        (finiteAdaptiveOuterHistorySupport stageSupport answerSupport history v j : Set ι))
      (finiteAdaptiveOuterHistoryEvent stage answer history v j) := by
  apply MeasurableSet.inter
  · apply (coordSigma_mono fun e he => Finset.mem_union_left _ he)
    exact measurableSet_finiteAdaptiveSuccessPrefix_coordSigma hstage history v j
  · apply (coordSigma_mono fun e he => Finset.mem_union_right _ he)
    exact measurableSet_adaptiveAnswerHistoryEvent_coordSigma hanswer history

/-- Freshness hypotheses for the two constituents of one outer stage history. -/
structure OuterHistorySupportsFresh
    (stageSupport : List (V × Bool) → V → ℕ → Finset ι)
    (answerSupport : List (V × Bool) → V → Finset ι)
    (history : List (V × Bool)) (v : V) (j : ℕ) (current : Finset ι) : Prop where
  stage : ∀ l < j,
    Disjoint (stageSupport history v l : Set ι) (current : Set ι)
  answer : HistoryQuerySupportsFresh answerSupport current [] history

theorem OuterHistorySupportsFresh.disjoint_prefixSupport
    {stageSupport : List (V × Bool) → V → ℕ → Finset ι}
    {answerSupport : List (V × Bool) → V → Finset ι}
    {history : List (V × Bool)} {v : V} {j : ℕ} {current : Finset ι}
    (h : OuterHistorySupportsFresh stageSupport answerSupport history v j current) :
    Disjoint (finiteAdaptiveSuccessPrefixSupport stageSupport history v j : Set ι)
      (current : Set ι) := by
  rw [Set.disjoint_left]
  intro e hePrefix heCurrent
  change e ∈ (Finset.range j).biUnion (fun l => stageSupport history v l) at hePrefix
  obtain ⟨l, hl, heStage⟩ := Finset.mem_biUnion.mp hePrefix
  exact Set.disjoint_left.mp (h.stage l (Finset.mem_range.mp hl)) heStage heCurrent

theorem OuterHistorySupportsFresh.disjoint_outerHistorySupport
    {stageSupport : List (V × Bool) → V → ℕ → Finset ι}
    {answerSupport : List (V × Bool) → V → Finset ι}
    {history : List (V × Bool)} {v : V} {j : ℕ} {current : Finset ι}
    (h : OuterHistorySupportsFresh stageSupport answerSupport history v j current) :
    Disjoint
      (finiteAdaptiveOuterHistorySupport stageSupport answerSupport history v j : Set ι)
      (current : Set ι) := by
  rw [Set.disjoint_left]
  intro e heOuter heCurrent
  change e ∈ finiteAdaptiveSuccessPrefixSupport stageSupport history v j ∪
    adaptiveAnswerHistorySupport answerSupport history at heOuter
  rw [Finset.mem_union] at heOuter
  rcases heOuter with hePrefix | heAnswer
  · exact Set.disjoint_left.mp h.disjoint_prefixSupport hePrefix heCurrent
  · exact Set.disjoint_left.mp h.answer.disjoint_historySupport heAnswer heCurrent

end AdaptiveSiteExploration

end Percolation
