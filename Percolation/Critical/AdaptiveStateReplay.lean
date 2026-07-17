import Percolation.Critical.AdaptiveDecisionRealization
import Percolation.Critical.AdaptiveRealizedHistory

/-!
# Identifying an adaptive state with its Boolean replay

The dynamic block construction records a forced root history before its adaptive oracle starts.
At every finite time, dropping that fixed prefix from the actual chronological history and
replaying the remaining Boolean decisions reconstructs the complete site-exploration state.
-/

namespace Percolation

namespace SiteExploration

variable {V : Type*} [DecidableEq V] [LinearOrder V]

/-- A suffix is a genuine chronological replay trace if each appended vertex was the actual
next frontier query at that prefix. -/
inductive IsReplayTrace (E : SiteExploration V) : List (V × Bool) → Prop
  | nil : IsReplayTrace E []
  | snoc {history : List (V × Bool)} {v : V} {accepted : Bool} :
      IsReplayTrace E history →
      SiteExploration.nextVertex (E.replayState history) = some v →
      IsReplayTrace E (history ++ [(v, accepted)])

namespace IsReplayTrace

/-- Every entry of a replay trace is the next query after replaying its preceding entries. -/
theorem nextVertex_take_getElem
    {E : SiteExploration V} {history : List (V × Bool)}
    (htrace : E.IsReplayTrace history) (i : ℕ) (hi : i < history.length) :
    SiteExploration.nextVertex (E.replayState (history.take i)) =
      some history[i].1 := by
  induction htrace with
  | nil => simp at hi
  | @snoc history v accepted htrace hnext ih =>
      by_cases hiOld : i < history.length
      · simpa [List.take_append_of_le_length hiOld.le, hiOld] using ih hiOld
      · have hieq : i = history.length := by simp at hi; omega
        subst i
        simpa using hnext

/-- Decomposition form used by dynamic replay: every recorded entry was an admissible next
query at the corresponding prefix. -/
theorem nextVertex_of_eq_append_cons
    {E : SiteExploration V} {history prior tail : List (V × Bool)}
    {v : V} {accepted : Bool} (htrace : E.IsReplayTrace history)
    (hdecomp : history = prior ++ (v, accepted) :: tail) :
    SiteExploration.nextVertex (E.replayState prior) = some v := by
  subst history
  have hi : prior.length < (prior ++ (v, accepted) :: tail).length := by
    simp
  have h := htrace.nextVertex_take_getElem prior.length hi
  simpa using h

end IsReplayTrace

/-- A finite history-dependent execution is exactly the static replay of its realized suffix.
The statement retains the prefix equation as well because later acceptance-time arguments use
it to move between full and suffix histories. -/
theorem exists_suffix_stateAfter_eq_replayState_isReplayTrace
    (E : SiteExploration V) (answer : List (V × Bool) → V → Bool) : ∀ n : ℕ,
    ∃ suffix : List (V × Bool),
      E.toAdaptive.stateAfter answer n = E.replayState suffix ∧
        (E.toAdaptive.stateAfter answer n).history = E.initial.history ++ suffix ∧
          E.IsReplayTrace suffix := by
  intro n
  induction n with
  | zero =>
      exact ⟨[], rfl, by simp [AdaptiveSiteExploration.stateAfter, SiteExploration.toAdaptive],
        IsReplayTrace.nil⟩
  | succ n ih =>
      obtain ⟨suffix, hstate, hhistory, htrace⟩ := ih
      let s := E.toAdaptive.stateAfter answer n
      by_cases hnext : SiteExploration.nextVertex s = none
      · have hfrontier : s.frontier = ∅ :=
          (SiteExploration.nextVertex_eq_none_iff s).mp hnext
        have hadaptive : E.toAdaptive.step answer s = s := by
          simp [AdaptiveSiteExploration.step, hnext]
        refine ⟨suffix, ?_, ?_, htrace⟩
        · simpa [AdaptiveSiteExploration.stateAfter, s, hadaptive] using hstate
        · simpa [AdaptiveSiteExploration.stateAfter, s, hadaptive] using hhistory
      · obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp hnext
        let b := answer s.history v
        have hanswer : ∀ w, SiteExploration.nextVertex s = some w →
            answer s.history w = b := by
          intro w hw
          have hwv : w = v := Option.some.inj (hw.symm.trans hv)
          simpa [b, hwv]
        have hadaptive : E.toAdaptive.step answer s = E.step (fun _ ↦ b) s :=
          E.toAdaptive_step_eq_step_const answer s b hanswer
        have hreplay : E.replayState (suffix ++ [(v, b)]) =
            E.step (fun _ ↦ b) (E.replayState suffix) := by
          rw [E.replayState_append_singleton]
        have hnextReplay : SiteExploration.nextVertex (E.replayState suffix) = some v := by
          simpa [s, hstate] using hv
        have hhistoryStep :
            (E.step (fun _ ↦ b) s).history = s.history ++ [(v, b)] := by
          cases b <;> simp [SiteExploration.step, hv]
        refine ⟨suffix ++ [(v, b)], ?_, ?_, ?_⟩
        · rw [AdaptiveSiteExploration.stateAfter, hadaptive, hreplay]
          simpa [s] using congrArg (E.step (fun _ ↦ b)) hstate
        · rw [AdaptiveSiteExploration.stateAfter, hadaptive, hhistoryStep, hhistory]
          simp [List.append_assoc]
        · exact IsReplayTrace.snoc htrace hnextReplay

/-- State-identification form without retaining the trace witness. -/
theorem exists_suffix_stateAfter_eq_replayState
    (E : SiteExploration V) (answer : List (V × Bool) → V → Bool) (n : ℕ) :
    ∃ suffix : List (V × Bool),
      E.toAdaptive.stateAfter answer n = E.replayState suffix ∧
        (E.toAdaptive.stateAfter answer n).history = E.initial.history ++ suffix := by
  obtain ⟨suffix, hstate, hhistory, _htrace⟩ :=
    E.exists_suffix_stateAfter_eq_replayState_isReplayTrace answer n
  exact ⟨suffix, hstate, hhistory⟩

/-- Direct reconstruction using the suffix obtained by dropping the fixed initial history. -/
theorem stateAfter_eq_replayState_drop_initialHistory
    (E : SiteExploration V) (answer : List (V × Bool) → V → Bool) (n : ℕ) :
    E.toAdaptive.stateAfter answer n =
      E.replayState
        ((E.toAdaptive.stateAfter answer n).history.drop E.initial.history.length) := by
  obtain ⟨suffix, hstate, hhistory⟩ :=
    E.exists_suffix_stateAfter_eq_replayState answer n
  rw [hhistory]
  simpa using hstate

end SiteExploration

end Percolation
