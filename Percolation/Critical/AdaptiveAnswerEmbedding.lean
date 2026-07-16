import Percolation.Critical.AdaptiveDecisionRealization

/-!
# Transporting adaptive answer laws along vertex embeddings

Finite induced-ball explorations use subtype vertices, while the source exploration is indexed by
ambient region vertices.  Mapping each finite history through the subtype embedding transports
both the answer oracle and its exact ratio-free history inequalities without conditioning on a
null event.
-/

namespace Percolation

open MeasureTheory

namespace AdaptiveSiteExploration

variable {U V Omega : Type*}

/-- Map a chronological Boolean-decision history through a vertex map. -/
def mapDecisionHistory (f : U → V) (history : List (U × Bool)) : List (V × Bool) :=
  history.map fun ub ↦ (f ub.1, ub.2)

@[simp]
theorem mapDecisionHistory_nil (f : U → V) :
    mapDecisionHistory f [] = [] :=
  rfl

@[simp]
theorem mapDecisionHistory_append (f : U → V)
    (h k : List (U × Bool)) :
    mapDecisionHistory f (h ++ k) = mapDecisionHistory f h ++ mapDecisionHistory f k := by
  simp [mapDecisionHistory]

@[simp]
theorem mapDecisionHistory_singleton (f : U → V) (u : U) (b : Bool) :
    mapDecisionHistory f [(u, b)] = [(f u, b)] :=
  rfl

/-- Pull an ambient history-dependent answer oracle back along a vertex map. -/
def pullbackAdaptiveAnswer (f : U → V)
    (answer : Omega → List (V × Bool) → V → Bool) :
    Omega → List (U × Bool) → U → Bool :=
  fun omega history u ↦ answer omega (mapDecisionHistory f history) (f u)

theorem measurableAnswer_pullbackAdaptiveAnswer
    [MeasurableSpace Omega]
    {answer : Omega → List (V × Bool) → V → Bool}
    (hanswer : MeasurableAnswer answer) (f : U → V) :
    MeasurableAnswer (pullbackAdaptiveAnswer f answer) :=
  fun history u ↦ hanswer (mapDecisionHistory f history) (f u)

/-- Exact histories commute with pulling an adaptive answer back along a vertex map. -/
theorem adaptiveAnswerHistoryEventFrom_pullbackAdaptiveAnswer
    (f : U → V) (answer : Omega → List (V × Bool) → V → Bool) :
    ∀ prior suffix,
      adaptiveAnswerHistoryEventFrom (pullbackAdaptiveAnswer f answer) prior suffix =
        adaptiveAnswerHistoryEventFrom answer (mapDecisionHistory f prior)
          (mapDecisionHistory f suffix) := by
  intro prior suffix
  induction suffix generalizing prior with
  | nil => rfl
  | cons head suffix ih =>
      rcases head with ⟨u, b⟩
      simp only [adaptiveAnswerHistoryEventFrom, pullbackAdaptiveAnswer,
        mapDecisionHistory, List.map_cons]
      rw [ih]
      congr 1
      simp [mapDecisionHistory]

/-- Rooted exact histories commute with answer pullback. -/
theorem adaptiveAnswerHistoryEvent_pullbackAdaptiveAnswer
    (f : U → V) (answer : Omega → List (V × Bool) → V → Bool)
    (history : List (U × Bool)) :
    adaptiveAnswerHistoryEvent (pullbackAdaptiveAnswer f answer) history =
      adaptiveAnswerHistoryEvent answer (mapDecisionHistory f history) := by
  simpa [adaptiveAnswerHistoryEvent] using
    adaptiveAnswerHistoryEventFrom_pullbackAdaptiveAnswer f answer [] history

/-- Uniform ratio-free lower bounds transport to the pulled-back oracle. -/
theorem HasAdaptiveAnswerLowerBoundOn.pullback
    [MeasurableSpace Omega] {mu : Measure Omega}
    {answer : Omega → List (V × Bool) → V → Bool} {q : ℝ}
    (h : HasAdaptiveAnswerLowerBoundOn mu answer (fun _ _ ↦ True) q)
    (f : U → V) :
    HasAdaptiveAnswerLowerBoundOn mu (pullbackAdaptiveAnswer f answer)
      (fun _ _ ↦ True) q := by
  intro history u _hadmissible
  rw [adaptiveAnswerHistoryEvent_pullbackAdaptiveAnswer,
    adaptiveAnswerHistoryEvent_pullbackAdaptiveAnswer]
  simpa using h (mapDecisionHistory f history) (f u) trivial

/-- Uniform ratio-free lower bounds with an explicit admissibility predicate transport along
the vertex/history embedding by pulling that predicate back as well. -/
theorem HasAdaptiveAnswerLowerBoundOn.pullbackAdmissible
    [MeasurableSpace Omega] {mu : Measure Omega}
    {answer : Omega → List (V × Bool) → V → Bool}
    {admissible : List (V × Bool) → V → Prop} {q : ℝ}
    (h : HasAdaptiveAnswerLowerBoundOn mu answer admissible q)
    (f : U → V) :
    HasAdaptiveAnswerLowerBoundOn mu (pullbackAdaptiveAnswer f answer)
      (fun history u ↦ admissible (mapDecisionHistory f history) (f u)) q := by
  intro history u hadmissible
  rw [adaptiveAnswerHistoryEvent_pullbackAdaptiveAnswer,
    adaptiveAnswerHistoryEvent_pullbackAdaptiveAnswer]
  simpa using h (mapDecisionHistory f history) (f u) hadmissible

end AdaptiveSiteExploration

namespace SiteExploration

variable {U V Omega : Type*}

/-- Prefixing commutes with history pullback when the two initial histories correspond. -/
theorem prefixedAdaptiveAnswer_pullback
    (f : U → V) (smallPrior : List (U × Bool)) (largePrior : List (V × Bool))
    (hprior : AdaptiveSiteExploration.mapDecisionHistory f smallPrior = largePrior)
    (answer : Omega → List (V × Bool) → V → Bool) :
    prefixedAdaptiveAnswer smallPrior
        (AdaptiveSiteExploration.pullbackAdaptiveAnswer f answer) =
      AdaptiveSiteExploration.pullbackAdaptiveAnswer f
        (prefixedAdaptiveAnswer largePrior answer) := by
  funext omega history u
  simp [prefixedAdaptiveAnswer, AdaptiveSiteExploration.pullbackAdaptiveAnswer,
    AdaptiveSiteExploration.mapDecisionHistory_append, hprior]

end SiteExploration

end Percolation
