import Percolation.Critical.DynamicBlockAnswerLaw

/-!
# Realized suffix histories

An initialized block program receives suffix histories, while the site exploration stores a
forced root prefix in every state.  The theorem below proves directly that the suffix recorded
after any finite number of adaptive steps is an exact answer-history event for the original
program oracle.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory

namespace AdaptiveSiteExploration

variable {V Omega : Type*} [DecidableEq V] [LinearOrder V]

/-- The state reached under an initialized full-history oracle retains the initial history as a
prefix, and its remaining suffix is exactly realized by the unprefixed answer. -/
theorem exists_realized_suffix_stateAfter
    (E : AdaptiveSiteExploration V)
    (answer : Omega → List (V × Bool) → V → Bool)
    (omega : Omega) : ∀ n : ℕ,
    ∃ suffix : List (V × Bool),
      (E.stateAfter
          (SiteExploration.realizePrefixedAdaptiveAnswer E.initial.history answer omega) n
        ).history = E.initial.history ++ suffix ∧
      omega ∈ adaptiveAnswerHistoryEvent answer suffix := by
  intro n
  induction n with
  | zero =>
      exact ⟨[], by simp [AdaptiveSiteExploration.stateAfter], by simp⟩
  | succ n ih =>
      obtain ⟨suffix, hhistory, hsuffix⟩ := ih
      let fullAnswer :=
        SiteExploration.realizePrefixedAdaptiveAnswer E.initial.history answer omega
      let s := E.stateAfter fullAnswer n
      have hdrop : s.history.drop E.initial.history.length = suffix := by
        rw [show s.history = E.initial.history ++ suffix from hhistory]
        simp
      simp only [AdaptiveSiteExploration.stateAfter]
      unfold AdaptiveSiteExploration.step
      split
      · exact ⟨suffix, hhistory, hsuffix⟩
      next v _hnext =>
        by_cases hv : answer omega suffix v
        · have hfull : fullAnswer s.history v = true := by
            simpa [fullAnswer, SiteExploration.realizePrefixedAdaptiveAnswer, hdrop] using hv
          have hfull' :
              SiteExploration.realizePrefixedAdaptiveAnswer E.initial.history answer omega
                  (E.stateAfter
                    (SiteExploration.realizePrefixedAdaptiveAnswer E.initial.history answer omega) n
                  ).history v = true := by
            simpa [fullAnswer, s] using hfull
          simp only [hfull']
          refine ⟨suffix ++ [(v, true)], ?_, ?_⟩
          · simp [hhistory, List.append_assoc]
          · rw [adaptiveAnswerHistoryEvent_append_singleton]
            exact ⟨hsuffix, by simpa using hv⟩
        · have hfull : fullAnswer s.history v = false := by
            simp [fullAnswer, SiteExploration.realizePrefixedAdaptiveAnswer, hdrop, hv]
          have hfull' :
              ¬SiteExploration.realizePrefixedAdaptiveAnswer E.initial.history answer omega
                  (E.stateAfter
                    (SiteExploration.realizePrefixedAdaptiveAnswer E.initial.history answer omega) n
                  ).history v = true := by
            simpa [fullAnswer, s] using hfull
          simp only [hfull']
          refine ⟨suffix ++ [(v, false)], ?_, ?_⟩
          · simp [hhistory, List.append_assoc]
          · rw [adaptiveAnswerHistoryEvent_append_singleton]
            exact ⟨hsuffix, by simpa using hv⟩

/-- Concrete suffix form, obtained by dropping the forced initial history. -/
theorem stateAfter_drop_initialHistory_mem_adaptiveAnswerHistoryEvent
    (E : AdaptiveSiteExploration V)
    (answer : Omega → List (V × Bool) → V → Bool)
    (omega : Omega) (n : ℕ) :
    omega ∈ adaptiveAnswerHistoryEvent answer
      ((E.stateAfter
        (SiteExploration.realizePrefixedAdaptiveAnswer E.initial.history answer omega) n
        ).history.drop E.initial.history.length) := by
  obtain ⟨suffix, hhistory, hsuffix⟩ :=
    E.exists_realized_suffix_stateAfter answer omega n
  rw [hhistory]
  simpa using hsuffix

end AdaptiveSiteExploration

end Percolation
