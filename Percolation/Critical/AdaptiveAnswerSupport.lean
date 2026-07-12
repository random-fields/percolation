import Percolation.Critical.AdaptiveAnswerHistory

/-!
# Finite coordinate supports for adaptive answer histories

An adaptive decision history is an intersection of answer fibers evaluated at successively
longer prefixes.  This file records the exact finite union of their coordinate supports.  It
turns pointwise finite-support certificates for an answer oracle into a coordinate-sigma
measurability theorem for every literal history cell, and propagates freshness from every
prefix query to the complete history.
-/

namespace Percolation

open MeasureTheory

namespace AdaptiveSiteExploration

variable {V ι : Type*} [DecidableEq ι]

/-- Union of the coordinate supports read while replaying `suffix` after `prior`. -/
def adaptiveAnswerHistorySupportFrom
    (support : List (V × Bool) → V → Finset ι) :
    List (V × Bool) → List (V × Bool) → Finset ι
  | _prior, [] => ∅
  | prior, (v, b) :: suffix =>
      support prior v ∪
        adaptiveAnswerHistorySupportFrom support (prior ++ [(v, b)]) suffix

/-- Support of a complete chronological adaptive history. -/
def adaptiveAnswerHistorySupport
    (support : List (V × Bool) → V → Finset ι)
    (history : List (V × Bool)) : Finset ι :=
  adaptiveAnswerHistorySupportFrom support [] history

@[simp]
theorem adaptiveAnswerHistorySupportFrom_nil
    (support : List (V × Bool) → V → Finset ι) (prior : List (V × Bool)) :
    adaptiveAnswerHistorySupportFrom support prior [] = ∅ :=
  rfl

@[simp]
theorem adaptiveAnswerHistorySupport_nil
    (support : List (V × Bool) → V → Finset ι) :
    adaptiveAnswerHistorySupport support [] = ∅ :=
  rfl

theorem adaptiveAnswerHistorySupportFrom_append_singleton
    (support : List (V × Bool) → V → Finset ι)
    (prior history : List (V × Bool)) (v : V) (b : Bool) :
    adaptiveAnswerHistorySupportFrom support prior (history ++ [(v, b)]) =
      adaptiveAnswerHistorySupportFrom support prior history ∪
        support (prior ++ history) v := by
  induction history generalizing prior with
  | nil => simp [adaptiveAnswerHistorySupportFrom]
  | cons head history ih =>
      rcases head with ⟨u, c⟩
      simp only [List.cons_append, adaptiveAnswerHistorySupportFrom]
      rw [ih, Finset.union_assoc]
      congr 2
      simp [List.append_assoc]

theorem adaptiveAnswerHistorySupport_append_singleton
    (support : List (V × Bool) → V → Finset ι)
    (history : List (V × Bool)) (v : V) (b : Bool) :
    adaptiveAnswerHistorySupport support (history ++ [(v, b)]) =
      adaptiveAnswerHistorySupport support history ∪ support history v := by
  simpa [adaptiveAnswerHistorySupport] using
    adaptiveAnswerHistorySupportFrom_append_singleton support [] history v b

/-- Every answer fiber is measurable on its advertised finite coordinate support. -/
def HasFiniteAnswerSupports
    (answer : (ι → ℝ) → List (V × Bool) → V → Bool)
    (support : List (V × Bool) → V → Finset ι) : Prop :=
  ∀ history v b, @MeasurableSet (ι → ℝ)
    (coordSigma ι (support history v : Set ι)) {X | answer X history v = b}

omit [DecidableEq ι] in
theorem HasFiniteAnswerSupports.measurableAnswer
    {answer : (ι → ℝ) → List (V × Bool) → V → Bool}
    {support : List (V × Bool) → V → Finset ι}
    (h : HasFiniteAnswerSupports answer support) : MeasurableAnswer answer := by
  intro history v
  apply measurable_to_bool
  exact (coordSigma_le (support history v : Set ι)) _ (h history v true)

theorem measurableSet_adaptiveAnswerHistoryEventFrom_coordSigma
    {answer : (ι → ℝ) → List (V × Bool) → V → Bool}
    {support : List (V × Bool) → V → Finset ι}
    (h : HasFiniteAnswerSupports answer support) :
    ∀ prior suffix, @MeasurableSet (ι → ℝ)
      (coordSigma ι
        (adaptiveAnswerHistorySupportFrom support prior suffix : Set ι))
      (adaptiveAnswerHistoryEventFrom answer prior suffix) := by
  intro prior suffix
  induction suffix generalizing prior with
  | nil => exact MeasurableSet.univ
  | cons head suffix ih =>
      rcases head with ⟨v, b⟩
      apply MeasurableSet.inter
      · apply (coordSigma_mono fun e he => Finset.mem_union_left _ he)
        exact h prior v b
      · apply (coordSigma_mono fun e he => Finset.mem_union_right _ he)
        exact ih (prior ++ [(v, b)])

theorem measurableSet_adaptiveAnswerHistoryEvent_coordSigma
    {answer : (ι → ℝ) → List (V × Bool) → V → Bool}
    {support : List (V × Bool) → V → Finset ι}
    (h : HasFiniteAnswerSupports answer support) (history : List (V × Bool)) :
    @MeasurableSet (ι → ℝ)
      (coordSigma ι (adaptiveAnswerHistorySupport support history : Set ι))
      (adaptiveAnswerHistoryEvent answer history) :=
  measurableSet_adaptiveAnswerHistoryEventFrom_coordSigma h [] history

/-- Every query support appearing in `suffix` is disjoint from `current`. -/
def HistoryQuerySupportsFresh
    (support : List (V × Bool) → V → Finset ι) (current : Finset ι) :
    List (V × Bool) → List (V × Bool) → Prop
  | _prior, [] => True
  | prior, (v, b) :: suffix =>
      Disjoint (support prior v : Set ι) (current : Set ι) ∧
        HistoryQuerySupportsFresh support current (prior ++ [(v, b)]) suffix

theorem HistoryQuerySupportsFresh.disjoint_historySupportFrom
    {support : List (V × Bool) → V → Finset ι} {current : Finset ι} :
    ∀ {prior suffix}, HistoryQuerySupportsFresh support current prior suffix →
      Disjoint (adaptiveAnswerHistorySupportFrom support prior suffix : Set ι)
        (current : Set ι) := by
  intro prior suffix hfresh
  induction suffix generalizing prior with
  | nil => simp
  | cons head suffix ih =>
      rcases head with ⟨v, b⟩
      rw [Set.disjoint_left]
      intro e heUnion heCurrent
      have heUnion' : e ∈ support prior v ∪
          adaptiveAnswerHistorySupportFrom support (prior ++ [(v, b)]) suffix := by
        simpa only [adaptiveAnswerHistorySupportFrom, Finset.mem_coe] using heUnion
      rw [Finset.mem_union] at heUnion'
      rcases heUnion' with heQuery | heTail
      · exact Set.disjoint_left.mp hfresh.1 heQuery heCurrent
      · exact Set.disjoint_left.mp (ih hfresh.2) heTail heCurrent

theorem HistoryQuerySupportsFresh.disjoint_historySupport
    {support : List (V × Bool) → V → Finset ι} {current : Finset ι}
    {history : List (V × Bool)}
    (h : HistoryQuerySupportsFresh support current [] history) :
    Disjoint (adaptiveAnswerHistorySupport support history : Set ι) (current : Set ι) :=
  h.disjoint_historySupportFrom

end AdaptiveSiteExploration

end Percolation
