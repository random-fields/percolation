import Percolation.Critical.DynamicHistoryReplay
import Percolation.Critical.AdaptiveStateReplay

/-!
# Chronology of the canonical dynamic replay

The public replay oracle accepts an arbitrary list of Boolean answers whose vertex fields may
be malformed.  `canonicalSuffix` deliberately discards those fields and reconstructs the actual
queries made by the deterministic site exploration.  This file records the missing semantic
fact: the reconstructed suffix is itself a genuine `SiteExploration.IsReplayTrace`.

The result is the chronology input needed by the history-indexed stage-certificate induction.
It prevents later proofs from carrying a separate, caller-supplied admissibility premise for
every decomposition of a canonical suffix.
-/

namespace Percolation

namespace SiteExploration

variable {V : Type*} [DecidableEq V] [LinearOrder V]

/-- Appending the chronological trace generated from a replay state preserves the replay-trace
property.  The prefix formulation is the induction invariant needed when an input list contains
junk vertex fields or continues after the frontier has become empty. -/
theorem IsReplayTrace.append_chronologicalTraceFrom
    (E : SiteExploration V) {historyPrefix : List (V × Bool)}
    (htrace : E.IsReplayTrace historyPrefix) (input : List (V × Bool)) :
    E.IsReplayTrace
      (historyPrefix ++ DynamicBlockHistoryReplay.chronologicalTraceFrom E
        (E.replayState historyPrefix) input) := by
  induction input generalizing historyPrefix with
  | nil => simpa [DynamicBlockHistoryReplay.chronologicalTraceFrom] using htrace
  | cons entry rest ih =>
      rcases entry with ⟨ignored, accepted⟩
      simp only [DynamicBlockHistoryReplay.chronologicalTraceFrom]
      split
      next hnext =>
        have hfrontier : (E.replayState historyPrefix).frontier = ∅ :=
          (SiteExploration.nextVertex_eq_none_iff _).mp hnext
        have hstep :
            E.step (fun _ ↦ accepted) (E.replayState historyPrefix) =
              E.replayState historyPrefix :=
          E.step_eq_self_of_frontier_eq_empty (fun _ ↦ accepted) hfrontier
        simpa [hstep] using ih htrace
      next v hnext =>
        have htrace' : E.IsReplayTrace (historyPrefix ++ [(v, accepted)]) :=
          IsReplayTrace.snoc htrace hnext
        have hreplay :
            E.replayState (historyPrefix ++ [(v, accepted)]) =
              E.step (fun _ ↦ accepted) (E.replayState historyPrefix) := by
          rw [E.replayState_append_singleton]
        simpa [List.append_assoc, hreplay] using ih htrace'

/-- The chronological trace generated from the initial state is a genuine replay trace. -/
theorem isReplayTrace_chronologicalTraceFrom
    (E : SiteExploration V) (input : List (V × Bool)) :
    E.IsReplayTrace
      (DynamicBlockHistoryReplay.chronologicalTraceFrom E E.initial input) := by
  simpa using
    (IsReplayTrace.append_chronologicalTraceFrom E (IsReplayTrace.nil (E := E)) input)

end SiteExploration

namespace DynamicBlockHistoryReplay

variable {d : ℕ} {F : Set (Cubic d)} [LinearOrder F]

/-- Canonicalization turns every arbitrary caller history into a genuine chronological trace
of the induced-region site exploration. -/
theorem canonicalSuffix_isReplayTrace (root : F) (history : List (F × Bool)) :
    (cubicRegionSiteExploration d F root).IsReplayTrace (canonicalSuffix root history) := by
  rw [canonicalSuffix_eq_chronologicalTraceFrom]
  exact SiteExploration.isReplayTrace_chronologicalTraceFrom _ _

/-- Every entry of the canonical suffix is an admissible coarse query after its canonical
prefix.  This is the decomposition form consumed by dynamic replay induction. -/
theorem admissibleQuery_of_canonicalSuffix_eq_append_cons
    (root : F) (history prior tail : List (F × Bool))
    (v : F) (accepted : Bool)
    (hdecomp : canonicalSuffix root history = prior ++ (v, accepted) :: tail) :
    AdmissibleQuery root prior v := by
  let E := cubicRegionSiteExploration d F root
  have hnext : SiteExploration.nextVertex (E.replayState prior) = some v :=
    (canonicalSuffix_isReplayTrace root history).nextVertex_of_eq_append_cons hdecomp
  constructor
  · exact ⟨v, SiteExploration.mem_frontier_of_nextVertex_eq_some hnext⟩
  · exact (E.replayQuery_eq_of_nextVertex_eq_some root prior hnext).symm

end DynamicBlockHistoryReplay

end Percolation
