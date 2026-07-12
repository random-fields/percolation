import Percolation.Critical.DynamicSteeringSymmetry

/-!
# Exact events for history-dependent exploration answers

The dynamic block construction queries a measurable answer whose event changes with the complete
previous history.  This file gives that phrase an exact meaning.  In particular, the event for an
extended history is the old history event intersected with the next answer event, and its true and
false extensions form a measurable disjoint partition.  All inequalities are ratio-free, so no
conditional probability is assigned a junk value on a null history.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory

namespace AdaptiveSiteExploration

variable {V Omega : Type*}

/-- Event that `answer` produces the list of decisions `suffix`, starting after the already fixed
`prior`.  The accumulator makes the history supplied to each query literal. -/
def adaptiveAnswerHistoryEventFrom
    (answer : Omega → List (V × Bool) → V → Bool) :
    List (V × Bool) → List (V × Bool) → Set Omega
  | _prior, [] => Set.univ
  | prior, (v, b) :: suffix =>
      {omega | answer omega prior v = b} ∩
        adaptiveAnswerHistoryEventFrom answer (prior ++ [(v, b)]) suffix

/-- Event that the answer oracle produces exactly the supplied finite chronological history. -/
def adaptiveAnswerHistoryEvent
    (answer : Omega → List (V × Bool) → V → Bool)
    (history : List (V × Bool)) : Set Omega :=
  adaptiveAnswerHistoryEventFrom answer [] history

@[simp]
theorem adaptiveAnswerHistoryEventFrom_nil
    (answer : Omega → List (V × Bool) → V → Bool)
    (prior : List (V × Bool)) :
    adaptiveAnswerHistoryEventFrom answer prior [] = Set.univ :=
  rfl

@[simp]
theorem adaptiveAnswerHistoryEvent_nil
    (answer : Omega → List (V × Bool) → V → Bool) :
    adaptiveAnswerHistoryEvent answer [] = Set.univ :=
  rfl

theorem adaptiveAnswerHistoryEventFrom_append_singleton
    (answer : Omega → List (V × Bool) → V → Bool)
    (prior history : List (V × Bool)) (v : V) (b : Bool) :
    adaptiveAnswerHistoryEventFrom answer prior (history ++ [(v, b)]) =
      adaptiveAnswerHistoryEventFrom answer prior history ∩
        {omega | answer omega (prior ++ history) v = b} := by
  induction history generalizing prior with
  | nil =>
      ext omega
      simp [adaptiveAnswerHistoryEventFrom]
  | cons head history ih =>
      rcases head with ⟨u, c⟩
      rw [List.cons_append]
      simp only [adaptiveAnswerHistoryEventFrom]
      rw [ih]
      ext omega
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
      rw [List.append_assoc]
      tauto

theorem adaptiveAnswerHistoryEvent_append_singleton
    (answer : Omega → List (V × Bool) → V → Bool)
    (history : List (V × Bool)) (v : V) (b : Bool) :
    adaptiveAnswerHistoryEvent answer (history ++ [(v, b)]) =
      adaptiveAnswerHistoryEvent answer history ∩
        {omega | answer omega history v = b} := by
  simpa [adaptiveAnswerHistoryEvent] using
    adaptiveAnswerHistoryEventFrom_append_singleton answer [] history v b

theorem measurableSet_adaptiveAnswerHistoryEventFrom
    [MeasurableSpace Omega]
    {answer : Omega → List (V × Bool) → V → Bool}
    (hanswer : MeasurableAnswer answer) :
    ∀ prior suffix,
      MeasurableSet (adaptiveAnswerHistoryEventFrom answer prior suffix) := by
  intro prior suffix
  induction suffix generalizing prior with
  | nil => exact MeasurableSet.univ
  | cons head suffix ih =>
      rcases head with ⟨v, b⟩
      exact ((hanswer prior v) (MeasurableSet.singleton b)).inter
        (ih (prior ++ [(v, b)]))

theorem measurableSet_adaptiveAnswerHistoryEvent
    [MeasurableSpace Omega]
    {answer : Omega → List (V × Bool) → V → Bool}
    (hanswer : MeasurableAnswer answer) (history : List (V × Bool)) :
    MeasurableSet (adaptiveAnswerHistoryEvent answer history) :=
  measurableSet_adaptiveAnswerHistoryEventFrom hanswer [] history

theorem adaptiveAnswerHistoryEvent_append_true_disjoint_false
    (answer : Omega → List (V × Bool) → V → Bool)
    (history : List (V × Bool)) (v : V) :
    Disjoint
      (adaptiveAnswerHistoryEvent answer (history ++ [(v, true)]))
      (adaptiveAnswerHistoryEvent answer (history ++ [(v, false)])) := by
  rw [adaptiveAnswerHistoryEvent_append_singleton,
    adaptiveAnswerHistoryEvent_append_singleton]
  apply Set.disjoint_left.mpr
  intro omega homegaTrue homegaFalse
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq] at homegaTrue homegaFalse
  simp [homegaTrue.2] at homegaFalse

theorem adaptiveAnswerHistoryEvent_append_true_union_false
    (answer : Omega → List (V × Bool) → V → Bool)
    (history : List (V × Bool)) (v : V) :
    adaptiveAnswerHistoryEvent answer (history ++ [(v, true)]) ∪
        adaptiveAnswerHistoryEvent answer (history ++ [(v, false)]) =
      adaptiveAnswerHistoryEvent answer history := by
  rw [adaptiveAnswerHistoryEvent_append_singleton,
    adaptiveAnswerHistoryEvent_append_singleton]
  ext omega
  cases hbit : answer omega history v <;> simp [hbit]

/-- Exact real-mass partition of a finite history into its two possible next answers. -/
theorem measureReal_adaptiveAnswerHistoryEvent_append_true_add_false
    [MeasurableSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    {answer : Omega → List (V × Bool) → V → Bool}
    (hanswer : MeasurableAnswer answer)
    (history : List (V × Bool)) (v : V) :
    mu.real (adaptiveAnswerHistoryEvent answer (history ++ [(v, true)])) +
        mu.real (adaptiveAnswerHistoryEvent answer (history ++ [(v, false)])) =
      mu.real (adaptiveAnswerHistoryEvent answer history) := by
  rw [← measureReal_union
    (adaptiveAnswerHistoryEvent_append_true_disjoint_false answer history v)
    (measurableSet_adaptiveAnswerHistoryEvent hanswer _),
    adaptiveAnswerHistoryEvent_append_true_union_false]

/-- Uniform ratio-free lower bound for the next true answer on every history/query admitted by
`admissible`. -/
def HasAdaptiveAnswerLowerBoundOn
    [MeasurableSpace Omega]
    (mu : Measure Omega)
    (answer : Omega → List (V × Bool) → V → Bool)
    (admissible : List (V × Bool) → V → Prop) (q : ℝ) : Prop :=
  ∀ history v, admissible history v →
    q * mu.real (adaptiveAnswerHistoryEvent answer history) ≤
      mu.real (adaptiveAnswerHistoryEvent answer (history ++ [(v, true)]))

theorem HasAdaptiveAnswerLowerBoundOn.conditionalRatio
    [MeasurableSpace Omega]
    {mu : Measure Omega}
    {answer : Omega → List (V × Bool) → V → Bool}
    {admissible : List (V × Bool) → V → Prop} {q : ℝ}
    (h : HasAdaptiveAnswerLowerBoundOn mu answer admissible q)
    {history : List (V × Bool)} {v : V} (hadmissible : admissible history v)
    (hhistory : 0 < mu.real (adaptiveAnswerHistoryEvent answer history)) :
    q ≤
      mu.real (adaptiveAnswerHistoryEvent answer (history ++ [(v, true)])) /
        mu.real (adaptiveAnswerHistoryEvent answer history) :=
  (le_div_iff₀ hhistory).2 (h history v hadmissible)

/-- The lower true-answer bound gives the complementary upper bound for a false extension. -/
theorem HasAdaptiveAnswerLowerBoundOn.false_mass_le
    [MeasurableSpace Omega]
    {mu : Measure Omega} [IsFiniteMeasure mu]
    {answer : Omega → List (V × Bool) → V → Bool}
    (hanswer : MeasurableAnswer answer)
    {admissible : List (V × Bool) → V → Prop} {q : ℝ}
    (h : HasAdaptiveAnswerLowerBoundOn mu answer admissible q)
    {history : List (V × Bool)} {v : V} (hadmissible : admissible history v) :
    mu.real (adaptiveAnswerHistoryEvent answer (history ++ [(v, false)])) ≤
      (1 - q) * mu.real (adaptiveAnswerHistoryEvent answer history) := by
  have hpartition := measureReal_adaptiveAnswerHistoryEvent_append_true_add_false
    mu hanswer history v
  have htrue := h history v hadmissible
  linarith

/-- Turn a measurable history-indexed family of success events into a Boolean adaptive answer. -/
noncomputable def eventAdaptiveAnswer
    (success : List (V × Bool) → V → Set Omega) :
    Omega → List (V × Bool) → V → Bool := by
  classical
  exact fun omega history v ↦ decide (omega ∈ success history v)

theorem measurableAnswer_eventAdaptiveAnswer
    [MeasurableSpace Omega]
    {success : List (V × Bool) → V → Set Omega}
  (hsuccess : ∀ history v, MeasurableSet (success history v)) :
    MeasurableAnswer (eventAdaptiveAnswer success) := by
  intro history v
  classical
  change Measurable fun omega ↦ if omega ∈ success history v then true else false
  exact Measurable.ite (hsuccess history v) measurable_const measurable_const

@[simp]
theorem eventAdaptiveAnswer_eq_true_iff
    (success : List (V × Bool) → V → Set Omega)
    (omega : Omega) (history : List (V × Bool)) (v : V) :
    eventAdaptiveAnswer success omega history v = true ↔
      omega ∈ success history v := by
  simp [eventAdaptiveAnswer]

@[simp]
theorem eventAdaptiveAnswer_eq_false_iff
    (success : List (V × Bool) → V → Set Omega)
    (omega : Omega) (history : List (V × Bool)) (v : V) :
    eventAdaptiveAnswer success omega history v = false ↔
      omega ∉ success history v := by
  simp [eventAdaptiveAnswer]

end AdaptiveSiteExploration

end Percolation
