import Percolation.Critical.AdaptiveAcceptanceTime
import Percolation.Critical.AdaptiveStateReplay
import Percolation.Critical.DynamicReplayFinalThreshold

/-!
# Acceptance-time anchors for the dynamic block construction

A vertex in the limiting occupied coarse cluster was accepted at a finite chronological query.
This file packages that query, its exact answer-history cell, and its deterministic replay state.
It is the bridge from Lemma 7.24's limiting site cluster to a concrete selected bond seed.
-/

namespace Percolation

open scoped unitInterval

namespace SiteExploration

variable {V Omega : Type*} [DecidableEq V] [LinearOrder V]

/-- Finite replay data witnessing that `v` received a true answer. -/
structure AcceptedReplayQuery (E : SiteExploration V)
    (answer : Omega → List (V × Bool) → V → Bool) (X : Omega) (v : V) where
  history : List (V × Bool)
  trace : E.IsReplayTrace history
  history_mem : X ∈ AdaptiveSiteExploration.adaptiveAnswerHistoryEvent answer history
  next_eq : SiteExploration.nextVertex (E.replayState history) = some v
  accepted : answer X history v = true

namespace AcceptedReplayQuery

/-- Every earlier entry in an accepted replay query is itself a genuine chronological query. -/
theorem prior_next_eq
    {E : SiteExploration V} {answer : Omega → List (V × Bool) → V → Bool}
    {X : Omega} {v : V} (Q : E.AcceptedReplayQuery answer X v)
    {prior tail : List (V × Bool)} {u : V} {accepted : Bool}
    (hdecomp : Q.history = prior ++ (u, accepted) :: tail) :
    SiteExploration.nextVertex (E.replayState prior) = some u :=
  Q.trace.nextVertex_of_eq_append_cons hdecomp

end AcceptedReplayQuery

/-- Every non-initial vertex in the occupied limit has an exact accepted replay query. -/
theorem exists_acceptedReplayQuery_of_mem_occupiedLimit
    (E : SiteExploration V)
    (answer : Omega → List (V × Bool) → V → Bool) (X : Omega) {v : V}
    (hv : v ∈ E.toAdaptive.occupiedLimit
      (SiteExploration.realizePrefixedAdaptiveAnswer E.initial.history answer X))
    (hvInitial : v ∉ E.initial.occupied) :
    Nonempty (E.AcceptedReplayQuery answer X v) := by
  let fullAnswer :=
    SiteExploration.realizePrefixedAdaptiveAnswer E.initial.history answer X
  obtain ⟨k, hnext, haccepted⟩ :=
    E.toAdaptive.exists_acceptance_step_of_mem_occupiedLimit fullAnswer hv hvInitial
  obtain ⟨history, hstate, hhistory, htrace⟩ :=
    E.exists_suffix_stateAfter_eq_replayState_isReplayTrace fullAnswer k
  have hhistoryMem :=
    E.toAdaptive.stateAfter_drop_initialHistory_mem_adaptiveAnswerHistoryEvent
      answer X k
  have hnext' : SiteExploration.nextVertex (E.replayState history) = some v := by
    rw [← hstate]
    exact hnext
  have haccepted' : answer X history v = true := by
    change answer X
      ((E.toAdaptive.stateAfter fullAnswer k).history.drop E.initial.history.length) v =
        true at haccepted
    rw [hhistory] at haccepted
    simpa using haccepted
  refine ⟨⟨history, htrace, ?_, hnext', haccepted'⟩⟩
  change X ∈ AdaptiveSiteExploration.adaptiveAnswerHistoryEvent answer
    ((E.toAdaptive.stateAfter fullAnswer k).history.drop E.initial.history.length) at hhistoryMem
  rw [hhistory] at hhistoryMem
  simpa using hhistoryMem

end SiteExploration

namespace DynamicBlockHistoryReplay

variable {d m n : ℕ} {F : Set (Cubic d)} [LinearOrder F]

/-- A chronological accepted query in the induced cubic exploration is an `AdmissibleQuery`
for the concrete dynamic replay, and so is every one of its prior entries. -/
theorem AcceptedReplayQuery.admissible
    {Omega : Type*} {root : F}
    {answer : Omega → List (F × Bool) → F → Bool} {X : Omega} {v : F}
    (Q : (cubicRegionSiteExploration d F root).AcceptedReplayQuery answer X v) :
    AdmissibleQuery root Q.history v := by
  constructor
  · exact ⟨v, SiteExploration.mem_frontier_of_nextVertex_eq_some Q.next_eq⟩
  · exact (cubicRegionSiteExploration d F root).replayQuery_eq_of_nextVertex_eq_some
      root Q.history Q.next_eq |>.symm

theorem AcceptedReplayQuery.allPriorAdmissible
    {Omega : Type*} {root : F}
    {answer : Omega → List (F × Bool) → F → Bool} {X : Omega} {v : F}
    (Q : (cubicRegionSiteExploration d F root).AcceptedReplayQuery answer X v) :
    ∀ (prior : List (F × Bool)) (u : F) (accepted : Bool)
      (tail : List (F × Bool)),
      Q.history = prior ++ (u, accepted) :: tail → AdmissibleQuery root prior u := by
  intro prior u accepted tail hdecomp
  have hnext := Q.prior_next_eq hdecomp
  constructor
  · exact ⟨u, SiteExploration.mem_frontier_of_nextVertex_eq_some hnext⟩
  · exact (cubicRegionSiteExploration d F root).replayQuery_eq_of_nextVertex_eq_some
      root prior hnext |>.symm

end DynamicBlockHistoryReplay

end Percolation
