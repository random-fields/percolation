import Percolation.Critical.FiniteSiteExplorationCompleteness
import Percolation.Bernoulli.Russo

set_option maxHeartbeats 800000

/-!
# Bellman probabilities for finite site explorations

Chronological Boolean answers are not a coordinatewise monotone encoding of an exploration:
accepting a site can change the identities of later queries.  The correct invariant is instead
the Bernoulli completion probability of the current partial state.  Splitting at the next
frontier site gives the usual Bernoulli Bellman equation, while forcing that site open can only
increase the target-connection event.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open Classical

namespace SiteExplorationState

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Sites whose status has not yet been decided. -/
def remaining (s : SiteExplorationState V) : Finset V :=
  Finset.univ \ s.decided

/-- Complete a partial state by adjoining the open sites in `xi` to its accepted set. -/
def completionOpenSet (s : SiteExplorationState V) (xi : Finset V) : Set V :=
  (s.occupied : Set V) ∪ (xi : Set V)

end SiteExplorationState

namespace SiteExploration

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

/-- The completion joins the root to at least one vertex of the finite target. -/
def completionHitsTarget (E : SiteExploration V) (root : V) (target : Finset V)
    (s : SiteExplorationState V) : Set (Finset V) :=
  {xi | ∃ t ∈ target, s.completionOpenSet xi ∈ siteConnectionEvent E.graph root t}

/-- Bernoulli-`q` probability that a random completion of the undecided sites hits `target`. -/
noncomputable def completionHitProbability (E : SiteExploration V) (q : ℝ)
    (root : V) (target : Finset V) (s : SiteExplorationState V) : ℝ :=
  finiteBernoulliProbability s.remaining q (E.completionHitsTarget root target s)

/-- State obtained by accepting a specified queried site. -/
def acceptState (E : SiteExploration V) (s : SiteExplorationState V) (v : V) :
    SiteExplorationState V :=
  { occupied := insert v s.occupied
    rejected := s.rejected
    frontier :=
      (s.frontier.erase v ∪ E.neighbors v) \ (insert v s.occupied ∪ s.rejected)
    history := s.history ++ [(v, true)] }

/-- State obtained by rejecting a specified queried site. -/
def rejectState (s : SiteExplorationState V) (v : V) : SiteExplorationState V :=
  { occupied := s.occupied
    rejected := insert v s.rejected
    frontier := s.frontier.erase v
    history := s.history ++ [(v, false)] }

omit [Fintype V] in
theorem step_eq_acceptState_of_nextVertex_of_answer
    (E : SiteExploration V) (answer : V → Bool) (s : SiteExplorationState V) {v : V}
    (hnext : nextVertex s = some v) (hanswer : answer v = true) :
    E.step answer s = E.acceptState s v := by
  simp [SiteExploration.step, hnext, hanswer, acceptState]

omit [Fintype V] in
theorem step_eq_rejectState_of_nextVertex_of_answer
    (E : SiteExploration V) (answer : V → Bool) (s : SiteExplorationState V) {v : V}
    (hnext : nextVertex s = some v) (hanswer : answer v = false) :
    E.step answer s = rejectState s v := by
  simp [SiteExploration.step, hnext, hanswer, rejectState]

theorem remaining_acceptState (E : SiteExploration V) (s : SiteExplorationState V) (v : V) :
    (E.acceptState s v).remaining = s.remaining.erase v := by
  ext z
  simp [SiteExplorationState.remaining, SiteExplorationState.decided, acceptState]

omit [LinearOrder V] in
theorem remaining_rejectState (s : SiteExplorationState V) (v : V) :
    (rejectState s v).remaining = s.remaining.erase v := by
  ext z
  simp [SiteExplorationState.remaining, SiteExplorationState.decided, rejectState]

omit [Fintype V] in
theorem completionOpenSet_acceptState_insert
    (E : SiteExploration V) (s : SiteExplorationState V) (v : V) (xi : Finset V) :
    (E.acceptState s v).completionOpenSet xi = s.completionOpenSet (insert v xi) := by
  ext z
  simp [SiteExplorationState.completionOpenSet, acceptState, or_assoc]

omit [Fintype V] [LinearOrder V] in
@[simp]
theorem completionOpenSet_rejectState
    (s : SiteExplorationState V) (v : V) (xi : Finset V) :
    (rejectState s v).completionOpenSet xi = s.completionOpenSet xi := by
  rfl

omit [Fintype V] in
theorem completionHitsTarget_acceptState_iff
    (E : SiteExploration V) (root : V) (target : Finset V)
    (s : SiteExplorationState V) (v : V) (xi : Finset V) :
    xi ∈ E.completionHitsTarget root target (E.acceptState s v) ↔
      insert v xi ∈ E.completionHitsTarget root target s := by
  simp only [completionHitsTarget, Set.mem_setOf_eq]
  rw [completionOpenSet_acceptState_insert]

omit [Fintype V] in
@[simp]
theorem completionHitsTarget_rejectState_iff
    (E : SiteExploration V) (root : V) (target : Finset V)
    (s : SiteExplorationState V) (v : V) (xi : Finset V) :
    xi ∈ E.completionHitsTarget root target (rejectState s v) ↔
      xi ∈ E.completionHitsTarget root target s := by
  rfl

omit [Fintype V] in
theorem completionHitsTarget_rejectState_subset_acceptState
    (E : SiteExploration V) (root : V) (target : Finset V)
    (s : SiteExplorationState V) (v : V) :
    E.completionHitsTarget root target (rejectState s v) ⊆
      E.completionHitsTarget root target (E.acceptState s v) := by
  intro xi hxi
  rw [completionHitsTarget_acceptState_iff]
  rcases hxi with ⟨t, ht, w, hw⟩
  refine ⟨t, ht, w, ?_⟩
  intro z hz
  have hzOpen : z ∈ s.completionOpenSet xi := by
    simpa using hw z hz
  rcases hzOpen with hzOccupied | hzXi
  · exact Or.inl hzOccupied
  · exact Or.inr (Finset.mem_insert_of_mem hzXi)

/-- Forcing the queried site open cannot lower the random-completion target probability. -/
theorem completionHitProbability_reject_le_accept
    (E : SiteExploration V) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (root : V) (target : Finset V) (s : SiteExplorationState V) (v : V) :
    E.completionHitProbability q root target (rejectState s v) ≤
      E.completionHitProbability q root target (E.acceptState s v) := by
  rw [completionHitProbability, completionHitProbability,
    remaining_rejectState, remaining_acceptState]
  exact finiteBernoulliProbability_mono hq0 hq1
    (E.completionHitsTarget_rejectState_subset_acceptState root target s v)

omit [LinearOrder V] in
theorem mem_remaining_of_mem_frontier
    {s : SiteExplorationState V} (hs : s.WellFormed) {v : V}
    (hv : v ∈ s.frontier) : v ∈ s.remaining := by
  simp only [SiteExplorationState.remaining, Finset.mem_sdiff, Finset.mem_univ, true_and]
  exact fun hvdecided ↦ Finset.disjoint_left.mp hs.2 hv hvdecided

/-- Bernoulli conditioning at the next queried site. -/
theorem completionHitProbability_eq_open_closed
    (E : SiteExploration V) (q : ℝ) (root : V) (target : Finset V)
    {s : SiteExplorationState V} (hs : s.WellFormed) {v : V}
    (hv : v ∈ s.frontier) :
    E.completionHitProbability q root target s =
      q * E.completionHitProbability q root target (E.acceptState s v) +
        (1 - q) * E.completionHitProbability q root target (rejectState s v) := by
  have hvremaining : v ∈ s.remaining := mem_remaining_of_mem_frontier hs hv
  have hinsert : insert v (s.remaining.erase v) = s.remaining :=
    Finset.insert_erase hvremaining
  have hopen :
      {xi : Finset V | insert v xi ∈ E.completionHitsTarget root target s} =
        E.completionHitsTarget root target (E.acceptState s v) := by
    ext xi
    exact (E.completionHitsTarget_acceptState_iff root target s v xi).symm
  have hclosed : E.completionHitsTarget root target s =
      E.completionHitsTarget root target (rejectState s v) := by
    ext xi
    exact (E.completionHitsTarget_rejectState_iff root target s v xi).symm
  rw [completionHitProbability, ← hinsert]
  calc
    finiteBernoulliProbability (insert v (s.remaining.erase v)) q
        (E.completionHitsTarget root target s) =
      q * finiteBernoulliProbability (s.remaining.erase v) q
          {xi : Finset V | insert v xi ∈ E.completionHitsTarget root target s} +
        (1 - q) * finiteBernoulliProbability (s.remaining.erase v) q
          (E.completionHitsTarget root target s) :=
      by
        convert finiteBernoulliProbability_insert
          (Finset.notMem_erase v s.remaining) q
            (E.completionHitsTarget root target s) using 1
        · apply congrArg (fun F : Finset V ↦
            finiteBernoulliProbability F q (E.completionHitsTarget root target s))
          ext z
          simp
        · apply congrArg (fun x : ℝ ↦ x +
            (1 - q) * finiteBernoulliProbability (s.remaining.erase v) q
              (E.completionHitsTarget root target s))
          apply congrArg (fun x : ℝ ↦ q * x)
          apply finiteBernoulliProbability_congr q
          intro xi _hxi
          simp only [Set.mem_setOf_eq]
          constructor <;> intro h
          · convert h using 1
            ext z
            simp
          · convert h using 1
            ext z
            simp
    _ = _ := by
      rw [hopen, hclosed, completionHitProbability, completionHitProbability,
        remaining_acceptState, remaining_rejectState]

omit [LinearOrder V] in
theorem answersAgree_completionOpenSet
    {s : SiteExplorationState V} (hs : s.WellFormed)
    {xi : Finset V} (hxi : xi ⊆ s.remaining) :
    s.AnswersAgree (s.completionOpenSet xi) := by
  constructor
  · intro v hv
    exact Or.inl hv
  · intro v hvRejected hvOpen
    rcases hvOpen with hvOccupied | hvXi
    · exact Finset.disjoint_left.mp hs.1 hvOccupied hvRejected
    · have hvRemaining := hxi hvXi
      exact (Finset.mem_sdiff.mp hvRemaining).2
        (Finset.mem_union_right s.occupied hvRejected)

theorem completionHitsTarget_iff_occupied_inter
    (E : SiteExploration V) (root : V) (target : Finset V)
    {s : SiteExplorationState V} (hs : s.WellFormed)
    (hrooted : E.OpenRootedAt root s)
    (hclosed : E.FrontierClosed s) (hfrontier : s.frontier = ∅)
    {xi : Finset V} (hxi : xi ⊆ s.remaining) :
    xi ∈ E.completionHitsTarget root target s ↔
      ∃ t ∈ target, t ∈ s.occupied := by
  have hagree := answersAgree_completionOpenSet hs hxi
  have heq := E.occupied_eq_siteOpenCluster_of_frontier_eq_empty
    (s.completionOpenSet xi) root hrooted hagree hclosed hfrontier
  constructor
  · rintro ⟨t, ht, hconn⟩
    change t ∈ siteOpenCluster E.graph (s.completionOpenSet xi) root at hconn
    rw [← heq] at hconn
    exact ⟨t, ht, hconn⟩
  · rintro ⟨t, ht, htOccupied⟩
    refine ⟨t, ht, ?_⟩
    change t ∈ siteOpenCluster E.graph (s.completionOpenSet xi) root
    rw [← heq]
    exact htOccupied

/-- Once the frontier is empty, the completion probability is the deterministic hit indicator. -/
theorem completionHitProbability_of_frontier_eq_empty
    (E : SiteExploration V) (q : ℝ) (root : V) (target : Finset V)
    {s : SiteExplorationState V} (hs : s.WellFormed)
    (hrooted : E.OpenRootedAt root s)
    (hclosed : E.FrontierClosed s) (hfrontier : s.frontier = ∅) :
    E.completionHitProbability q root target s =
      if ∃ t ∈ target, t ∈ s.occupied then 1 else 0 := by
  by_cases hhit : ∃ t ∈ target, t ∈ s.occupied
  · have hevent : E.completionHitsTarget root target s = Set.univ := by
      ext xi
      constructor
      · intro _
        trivial
      · intro _
        obtain ⟨t, ht, htOccupied⟩ := hhit
        obtain ⟨w, hw⟩ := hrooted.2.1 t htOccupied
        exact ⟨t, ht, w, fun z hz ↦ Or.inl (hw z hz)⟩
    simp [completionHitProbability, hhit, hevent]
  · have heventOn : ∀ xi ∈ s.remaining.powerset,
        xi ∉ E.completionHitsTarget root target s := by
      intro xi hxi hmem
      exact hhit ((E.completionHitsTarget_iff_occupied_inter root target hs hrooted hclosed
        hfrontier (Finset.mem_powerset.mp hxi)).1 hmem)
    rw [completionHitProbability]
    have hzero : finiteBernoulliProbability s.remaining q
        (E.completionHitsTarget root target s) =
          finiteBernoulliProbability s.remaining q (∅ : Set (Finset V)) :=
      finiteBernoulliProbability_congr q fun xi hxi ↦
        iff_of_false (heventOn xi hxi) (Set.notMem_empty xi)
    simp [hhit, hzero]

/-! ### Replaying chronological answer histories -/

/-- Replay a chronological answer history from an arbitrary partial state.  The recorded vertex
is redundant: the exploration's deterministic frontier rule determines the actual query. -/
noncomputable def replayStateFrom (E : SiteExploration V) :
    SiteExplorationState V → List (V × Bool) → SiteExplorationState V
  | s, [] => s
  | s, (_, b) :: history =>
      E.replayStateFrom (E.step (fun _ ↦ b) s) history

/-- Replay from the exploration's designated initial state. -/
noncomputable def replayState (E : SiteExploration V) (history : List (V × Bool)) :
    SiteExplorationState V :=
  E.replayStateFrom E.initial history

omit [Fintype V] in
theorem replayStateFrom_append
    (E : SiteExploration V) (s : SiteExplorationState V)
    (history tail : List (V × Bool)) :
    E.replayStateFrom s (history ++ tail) =
      E.replayStateFrom (E.replayStateFrom s history) tail := by
  induction history generalizing s with
  | nil => rfl
  | cons head history ih =>
      rcases head with ⟨v, b⟩
      simp only [List.cons_append, replayStateFrom]
      exact ih (E.step (fun _ ↦ b) s)

omit [Fintype V] in
theorem replayStateFrom_append_singleton
    (E : SiteExploration V) (s : SiteExplorationState V)
    (history : List (V × Bool)) (v : V) (b : Bool) :
    E.replayStateFrom s (history ++ [(v, b)]) =
      E.step (fun _ ↦ b) (E.replayStateFrom s history) := by
  rw [E.replayStateFrom_append s history]
  rfl

omit [Fintype V] in
theorem replayState_append_singleton
    (E : SiteExploration V) (history : List (V × Bool)) (v : V) (b : Bool) :
    E.replayState (history ++ [(v, b)]) =
      E.step (fun _ ↦ b) (E.replayState history) :=
  E.replayStateFrom_append_singleton E.initial history v b

/-- Total query rule obtained from replaying the history; `root` is a harmless dummy after the
frontier has become empty. -/
noncomputable def replayQuery (E : SiteExploration V) (root : V)
    (history : List (V × Bool)) : V :=
  (nextVertex (E.replayState history)).getD root

/-- Terminal target-hit predicate read from a replayed state. -/
def replayHitsTarget (E : SiteExploration V) (target : Finset V)
    (history : List (V × Bool)) : Prop :=
  ∃ t ∈ target, t ∈ (E.replayState history).occupied

omit [Fintype V] in
theorem replayQuery_eq_of_nextVertex_eq_some
    (E : SiteExploration V) (root : V) (history : List (V × Bool)) {v : V}
    (hnext : nextVertex (E.replayState history) = some v) :
    E.replayQuery root history = v := by
  simp [replayQuery, hnext]

omit [Fintype V] in
theorem replayState_append_true_eq_acceptState
    (E : SiteExploration V) (root : V) (history : List (V × Bool)) {v : V}
    (hnext : nextVertex (E.replayState history) = some v) :
    E.replayState (history ++ [(E.replayQuery root history, true)]) =
      E.acceptState (E.replayState history) v := by
  rw [E.replayQuery_eq_of_nextVertex_eq_some root history hnext,
    E.replayState_append_singleton]
  exact E.step_eq_acceptState_of_nextVertex_of_answer _ _ hnext rfl

omit [Fintype V] in
theorem replayState_append_false_eq_rejectState
    (E : SiteExploration V) (root : V) (history : List (V × Bool)) {v : V}
    (hnext : nextVertex (E.replayState history) = some v) :
    E.replayState (history ++ [(E.replayQuery root history, false)]) =
      rejectState (E.replayState history) v := by
  rw [E.replayQuery_eq_of_nextVertex_eq_some root history hnext,
    E.replayState_append_singleton]
  exact E.step_eq_rejectState_of_nextVertex_of_answer _ _ hnext rfl

omit [Fintype V] in
theorem replayState_append_eq_of_frontier_eq_empty
    (E : SiteExploration V) (root : V) (history : List (V × Bool)) (b : Bool)
    (hfrontier : (E.replayState history).frontier = ∅) :
    E.replayState (history ++ [(E.replayQuery root history, b)]) =
      E.replayState history := by
  rw [E.replayState_append_singleton]
  exact E.step_eq_self_of_frontier_eq_empty (fun _ ↦ b) hfrontier

omit [Fintype V] in
theorem iidAdaptiveDecisionValue_replayHitsTarget_of_frontier_eq_empty
    (E : SiteExploration V) (q : ℝ) (root : V) (target : Finset V)
    (history : List (V × Bool))
    (hfrontier : (E.replayState history).frontier = ∅) :
    ∀ depth,
      AdaptiveSiteExploration.iidAdaptiveDecisionValue q (E.replayQuery root)
          (E.replayHitsTarget target) history depth =
        if E.replayHitsTarget target history then 1 else 0 := by
  intro depth
  induction depth generalizing history with
  | zero => rfl
  | succ depth ih =>
      rw [AdaptiveSiteExploration.iidAdaptiveDecisionValue]
      have htrue := E.replayState_append_eq_of_frontier_eq_empty
        root history true hfrontier
      have hfalse := E.replayState_append_eq_of_frontier_eq_empty
        root history false hfrontier
      have hfrontierTrue :
          (E.replayState (history ++ [(E.replayQuery root history, true)])).frontier = ∅ := by
        rw [htrue]
        exact hfrontier
      have hfrontierFalse :
          (E.replayState (history ++ [(E.replayQuery root history, false)])).frontier = ∅ := by
        rw [hfalse]
        exact hfrontier
      rw [ih _ hfrontierTrue, ih _ hfrontierFalse]
      have hwinTrue : E.replayHitsTarget target
          (history ++ [(E.replayQuery root history, true)]) ↔
            E.replayHitsTarget target history := by
        simp only [replayHitsTarget]
        rw [htrue]
      have hwinFalse : E.replayHitsTarget target
          (history ++ [(E.replayQuery root history, false)]) ↔
            E.replayHitsTarget target history := by
        simp only [replayHitsTarget]
        rw [hfalse]
      simp only [hwinTrue, hwinFalse]
      split <;> ring

/-- The iid decision-tree value at the exhaustion depth is exactly the Bernoulli completion
probability of the current replayed state. -/
theorem iidAdaptiveDecisionValue_eq_completionHitProbability
    (E : SiteExploration V) (q : ℝ) (root : V) (target : Finset V)
    (history : List (V × Bool))
    (hwf : (E.replayState history).WellFormed)
    (hrooted : E.OpenRootedAt root (E.replayState history))
    (hclosed : E.FrontierClosed (E.replayState history)) :
    AdaptiveSiteExploration.iidAdaptiveDecisionValue q (E.replayQuery root)
        (E.replayHitsTarget target) history
        (E.replayState history).remaining.card =
      E.completionHitProbability q root target (E.replayState history) := by
  let s := E.replayState history
  by_cases hfrontier : s.frontier = ∅
  · rw [E.iidAdaptiveDecisionValue_replayHitsTarget_of_frontier_eq_empty
      q root target history hfrontier]
    rw [E.completionHitProbability_of_frontier_eq_empty q root target hwf hrooted hclosed
      hfrontier]
    simp [replayHitsTarget]
  · have hfrontierNonempty : s.frontier.Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hfrontier
    let v := s.frontier.min' hfrontierNonempty
    have hnext : nextVertex s = some v := by
      simp [SiteExploration.nextVertex, hfrontierNonempty, v]
    have hvfrontier : v ∈ s.frontier :=
      SiteExploration.mem_frontier_of_nextVertex_eq_some hnext
    have hvremaining : v ∈ s.remaining := mem_remaining_of_mem_frontier hwf hvfrontier
    let historyTrue := history ++ [(E.replayQuery root history, true)]
    let historyFalse := history ++ [(E.replayQuery root history, false)]
    have hstateTrue : E.replayState historyTrue = E.acceptState s v := by
      exact E.replayState_append_true_eq_acceptState root history hnext
    have hstateFalse : E.replayState historyFalse = rejectState s v := by
      exact E.replayState_append_false_eq_rejectState root history hnext
    have hstepTrue : E.step (fun _ ↦ true) s = E.acceptState s v :=
      E.step_eq_acceptState_of_nextVertex_of_answer (fun _ ↦ true) s hnext rfl
    have hstepFalse : E.step (fun _ ↦ false) s = rejectState s v :=
      E.step_eq_rejectState_of_nextVertex_of_answer (fun _ ↦ false) s hnext rfl
    have hwfTrue : (E.replayState historyTrue).WellFormed := by
      rw [hstateTrue, ← hstepTrue]
      exact E.step_wellFormed (fun _ ↦ true) hwf
    have hwfFalse : (E.replayState historyFalse).WellFormed := by
      rw [hstateFalse, ← hstepFalse]
      exact E.step_wellFormed (fun _ ↦ false) hwf
    have hrootedTrue : E.OpenRootedAt root (E.replayState historyTrue) := by
      rw [hstateTrue, ← hstepTrue]
      exact E.step_openRootedAt (fun _ ↦ true) root hrooted
    have hrootedFalse : E.OpenRootedAt root (E.replayState historyFalse) := by
      rw [hstateFalse, ← hstepFalse]
      exact E.step_openRootedAt (fun _ ↦ false) root hrooted
    have hclosedTrue : E.FrontierClosed (E.replayState historyTrue) := by
      rw [hstateTrue, ← hstepTrue]
      exact E.step_frontierClosed (fun _ ↦ true) hclosed
    have hclosedFalse : E.FrontierClosed (E.replayState historyFalse) := by
      rw [hstateFalse, ← hstepFalse]
      exact E.step_frontierClosed (fun _ ↦ false) hclosed
    have hcardTrue : (E.replayState historyTrue).remaining.card + 1 = s.remaining.card := by
      rw [hstateTrue, remaining_acceptState]
      exact Finset.card_erase_add_one hvremaining
    have hcardFalse : (E.replayState historyFalse).remaining.card + 1 = s.remaining.card := by
      rw [hstateFalse, remaining_rejectState]
      exact Finset.card_erase_add_one hvremaining
    have hltTrue : (E.replayState historyTrue).remaining.card <
        (E.replayState history).remaining.card := by
      change (E.replayState historyTrue).remaining.card < s.remaining.card
      omega
    have hltFalse : (E.replayState historyFalse).remaining.card <
        (E.replayState history).remaining.card := by
      change (E.replayState historyFalse).remaining.card < s.remaining.card
      omega
    have ihTrue := E.iidAdaptiveDecisionValue_eq_completionHitProbability
      q root target historyTrue hwfTrue hrootedTrue hclosedTrue
    have ihFalse := E.iidAdaptiveDecisionValue_eq_completionHitProbability
      q root target historyFalse hwfFalse hrootedFalse hclosedFalse
    rw [← hcardTrue, AdaptiveSiteExploration.iidAdaptiveDecisionValue]
    change q * AdaptiveSiteExploration.iidAdaptiveDecisionValue q (E.replayQuery root)
        (E.replayHitsTarget target) historyTrue
          (E.replayState historyTrue).remaining.card +
        (1 - q) * AdaptiveSiteExploration.iidAdaptiveDecisionValue q (E.replayQuery root)
          (E.replayHitsTarget target) historyFalse
            (E.replayState historyTrue).remaining.card = _
    have hcards : (E.replayState historyFalse).remaining.card =
        (E.replayState historyTrue).remaining.card := by omega
    rw [ihTrue, ← hcards, ihFalse]
    rw [hstateTrue, hstateFalse]
    exact (E.completionHitProbability_eq_open_closed q root target hwf hvfrontier).symm
termination_by (E.replayState history).remaining.card
decreasing_by
  · exact hltTrue
  · exact hltFalse

omit [Fintype V] in
theorem adaptiveDecisionWinMass_replayHitsTarget_of_frontier_eq_empty
    {Omega : Type*} [MeasurableSpace Omega]
    (E : SiteExploration V) (mu : Measure Omega) [IsFiniteMeasure mu]
    {answer : Omega → List (V × Bool) → V → Bool}
    (hanswer : AdaptiveSiteExploration.MeasurableAnswer answer)
    (root : V) (target : Finset V) (history : List (V × Bool))
    (hfrontier : (E.replayState history).frontier = ∅) :
    ∀ depth,
      AdaptiveSiteExploration.adaptiveDecisionWinMass mu answer (E.replayQuery root)
          (E.replayHitsTarget target) history depth =
        if E.replayHitsTarget target history then
          mu.real (AdaptiveSiteExploration.adaptiveAnswerHistoryEvent answer history)
        else 0 := by
  intro depth
  induction depth generalizing history with
  | zero =>
      exact AdaptiveSiteExploration.adaptiveDecisionWinMass_zero
        mu answer (E.replayQuery root) (E.replayHitsTarget target) history
  | succ depth ih =>
      rw [AdaptiveSiteExploration.adaptiveDecisionWinMass_succ]
      have htrue := E.replayState_append_eq_of_frontier_eq_empty
        root history true hfrontier
      have hfalse := E.replayState_append_eq_of_frontier_eq_empty
        root history false hfrontier
      have hfrontierTrue :
          (E.replayState (history ++ [(E.replayQuery root history, true)])).frontier = ∅ := by
        rw [htrue]
        exact hfrontier
      have hfrontierFalse :
          (E.replayState (history ++ [(E.replayQuery root history, false)])).frontier = ∅ := by
        rw [hfalse]
        exact hfrontier
      rw [ih _ hfrontierTrue, ih _ hfrontierFalse]
      have hwinTrue : E.replayHitsTarget target
          (history ++ [(E.replayQuery root history, true)]) ↔
            E.replayHitsTarget target history := by
        simp only [replayHitsTarget]
        rw [htrue]
      have hwinFalse : E.replayHitsTarget target
          (history ++ [(E.replayQuery root history, false)]) ↔
            E.replayHitsTarget target history := by
        simp only [replayHitsTarget]
        rw [hfalse]
      simp only [hwinTrue, hwinFalse]
      split
      · exact AdaptiveSiteExploration.measureReal_adaptiveAnswerHistoryEvent_append_true_add_false
          mu hanswer history (E.replayQuery root history)
      · simp

/-- Ratio-free finite target-hitting comparison for the actual exploration tree.  Unlike the
generic decision-tree theorem, this result only needs branch favorability at the exhaustion
depth, where it follows from the Bellman completion probability. -/
theorem completionHitProbability_mul_historyMass_le_adaptiveDecisionWinMass
    {Omega : Type*} [MeasurableSpace Omega]
    (E : SiteExploration V) (mu : Measure Omega) [IsFiniteMeasure mu]
    {answer : Omega → List (V × Bool) → V → Bool}
    (hanswer : AdaptiveSiteExploration.MeasurableAnswer answer)
    (admissible : List (V × Bool) → V → Prop)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hlower : AdaptiveSiteExploration.HasAdaptiveAnswerLowerBoundOn
      mu answer admissible q)
    (root : V) (target : Finset V)
    (hquery : ∀ history, admissible history (E.replayQuery root history))
    (history : List (V × Bool))
    (hwf : (E.replayState history).WellFormed)
    (hrooted : E.OpenRootedAt root (E.replayState history))
    (hclosed : E.FrontierClosed (E.replayState history)) :
    E.completionHitProbability q root target (E.replayState history) *
        mu.real (AdaptiveSiteExploration.adaptiveAnswerHistoryEvent answer history) ≤
      AdaptiveSiteExploration.adaptiveDecisionWinMass mu answer (E.replayQuery root)
        (E.replayHitsTarget target) history
        (E.replayState history).remaining.card := by
  let s := E.replayState history
  by_cases hfrontier : s.frontier = ∅
  · rw [E.completionHitProbability_of_frontier_eq_empty q root target hwf hrooted hclosed
      hfrontier]
    rw [E.adaptiveDecisionWinMass_replayHitsTarget_of_frontier_eq_empty
      mu hanswer root target history hfrontier]
    by_cases hhit : ∃ t ∈ target, t ∈ (E.replayState history).occupied <;>
      simp [replayHitsTarget, hhit]
  · have hfrontierNonempty : s.frontier.Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hfrontier
    let v := s.frontier.min' hfrontierNonempty
    have hnext : nextVertex s = some v := by
      simp [SiteExploration.nextVertex, hfrontierNonempty, v]
    have hvfrontier : v ∈ s.frontier :=
      SiteExploration.mem_frontier_of_nextVertex_eq_some hnext
    have hvremaining : v ∈ s.remaining := mem_remaining_of_mem_frontier hwf hvfrontier
    have hqueryv : E.replayQuery root history = v :=
      E.replayQuery_eq_of_nextVertex_eq_some root history hnext
    let historyTrue := history ++ [(E.replayQuery root history, true)]
    let historyFalse := history ++ [(E.replayQuery root history, false)]
    have hstateTrue : E.replayState historyTrue = E.acceptState s v :=
      E.replayState_append_true_eq_acceptState root history hnext
    have hstateFalse : E.replayState historyFalse = rejectState s v :=
      E.replayState_append_false_eq_rejectState root history hnext
    have hstepTrue : E.step (fun _ ↦ true) s = E.acceptState s v :=
      E.step_eq_acceptState_of_nextVertex_of_answer (fun _ ↦ true) s hnext rfl
    have hstepFalse : E.step (fun _ ↦ false) s = rejectState s v :=
      E.step_eq_rejectState_of_nextVertex_of_answer (fun _ ↦ false) s hnext rfl
    have hwfTrue : (E.replayState historyTrue).WellFormed := by
      rw [hstateTrue, ← hstepTrue]
      exact E.step_wellFormed (fun _ ↦ true) hwf
    have hwfFalse : (E.replayState historyFalse).WellFormed := by
      rw [hstateFalse, ← hstepFalse]
      exact E.step_wellFormed (fun _ ↦ false) hwf
    have hrootedTrue : E.OpenRootedAt root (E.replayState historyTrue) := by
      rw [hstateTrue, ← hstepTrue]
      exact E.step_openRootedAt (fun _ ↦ true) root hrooted
    have hrootedFalse : E.OpenRootedAt root (E.replayState historyFalse) := by
      rw [hstateFalse, ← hstepFalse]
      exact E.step_openRootedAt (fun _ ↦ false) root hrooted
    have hclosedTrue : E.FrontierClosed (E.replayState historyTrue) := by
      rw [hstateTrue, ← hstepTrue]
      exact E.step_frontierClosed (fun _ ↦ true) hclosed
    have hclosedFalse : E.FrontierClosed (E.replayState historyFalse) := by
      rw [hstateFalse, ← hstepFalse]
      exact E.step_frontierClosed (fun _ ↦ false) hclosed
    have hcardTrue : (E.replayState historyTrue).remaining.card + 1 = s.remaining.card := by
      rw [hstateTrue, remaining_acceptState]
      exact Finset.card_erase_add_one hvremaining
    have hcardFalse : (E.replayState historyFalse).remaining.card + 1 = s.remaining.card := by
      rw [hstateFalse, remaining_rejectState]
      exact Finset.card_erase_add_one hvremaining
    have hltTrue : (E.replayState historyTrue).remaining.card <
        (E.replayState history).remaining.card := by
      change (E.replayState historyTrue).remaining.card < s.remaining.card
      omega
    have hltFalse : (E.replayState historyFalse).remaining.card <
        (E.replayState history).remaining.card := by
      change (E.replayState historyFalse).remaining.card < s.remaining.card
      omega
    have ihTrue := E.completionHitProbability_mul_historyMass_le_adaptiveDecisionWinMass
      mu hanswer admissible q hq0 hq1 hlower root target hquery historyTrue
      hwfTrue hrootedTrue hclosedTrue
    have ihFalse := E.completionHitProbability_mul_historyMass_le_adaptiveDecisionWinMass
      mu hanswer admissible q hq0 hq1 hlower root target hquery historyFalse
      hwfFalse hrootedFalse hclosedFalse
    let valueTrue := E.completionHitProbability q root target (E.replayState historyTrue)
    let valueFalse := E.completionHitProbability q root target (E.replayState historyFalse)
    let massHistory := mu.real
      (AdaptiveSiteExploration.adaptiveAnswerHistoryEvent answer history)
    let massTrue := mu.real
      (AdaptiveSiteExploration.adaptiveAnswerHistoryEvent answer historyTrue)
    let massFalse := mu.real
      (AdaptiveSiteExploration.adaptiveAnswerHistoryEvent answer historyFalse)
    have hvalueTrue0 : 0 ≤ valueTrue := by
      exact finiteBernoulliProbability_nonneg hq0 hq1 _
    have hvalueFalse0 : 0 ≤ valueFalse := by
      exact finiteBernoulliProbability_nonneg hq0 hq1 _
    have hvalue : valueFalse ≤ valueTrue := by
      dsimp [valueTrue, valueFalse]
      rw [hstateTrue, hstateFalse]
      exact E.completionHitProbability_reject_le_accept hq0 hq1 root target s v
    have hmassPartition : massTrue + massFalse = massHistory := by
      exact AdaptiveSiteExploration.measureReal_adaptiveAnswerHistoryEvent_append_true_add_false
        mu hanswer history (E.replayQuery root history)
    have hmassTrue : q * massHistory ≤ massTrue := by
      exact hlower history (E.replayQuery root history) (hquery history)
    have hbranches : valueTrue * massTrue + valueFalse * massFalse ≤
        AdaptiveSiteExploration.adaptiveDecisionWinMass mu answer (E.replayQuery root)
            (E.replayHitsTarget target) historyTrue
              (E.replayState historyTrue).remaining.card +
          AdaptiveSiteExploration.adaptiveDecisionWinMass mu answer (E.replayQuery root)
            (E.replayHitsTarget target) historyFalse
              (E.replayState historyFalse).remaining.card := by
      exact add_le_add ihTrue ihFalse
    rw [E.completionHitProbability_eq_open_closed q root target hwf hvfrontier]
    rw [← hcardTrue, AdaptiveSiteExploration.adaptiveDecisionWinMass_succ]
    rw [← hstateTrue, ← hstateFalse]
    change (q * valueTrue + (1 - q) * valueFalse) * massHistory ≤ _
    have hcards : (E.replayState historyFalse).remaining.card =
        (E.replayState historyTrue).remaining.card := by omega
    calc
      (q * valueTrue + (1 - q) * valueFalse) * massHistory ≤
          valueTrue * massTrue + valueFalse * massFalse := by
        nlinarith
      _ ≤ _ := by
        simpa [historyTrue, historyFalse, hcards] using hbranches
termination_by (E.replayState history).remaining.card
decreasing_by
  · exact hltTrue
  · exact hltFalse

/-- Dual ratio-free finite target comparison.  If every adaptive true answer has conditional
mass at most `q`, then its finite target-hit mass is at most the iid Bernoulli completion
probability.  The recursion is specialized to the exploration's decreasing set of undecided
vertices, so no fixed-depth monotonicity assumption on history-dependent query orders is used. -/
theorem adaptiveDecisionWinMass_le_completionHitProbability_mul_historyMass
    {Omega : Type*} [MeasurableSpace Omega]
    (E : SiteExploration V) (mu : Measure Omega) [IsFiniteMeasure mu]
    {answer : Omega → List (V × Bool) → V → Bool}
    (hanswer : AdaptiveSiteExploration.MeasurableAnswer answer)
    (admissible : List (V × Bool) → V → Prop)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hupper : AdaptiveSiteExploration.HasAdaptiveAnswerUpperBoundOn
      mu answer admissible q)
    (root : V) (target : Finset V)
    (hquery : ∀ history, admissible history (E.replayQuery root history))
    (history : List (V × Bool))
    (hwf : (E.replayState history).WellFormed)
    (hrooted : E.OpenRootedAt root (E.replayState history))
    (hclosed : E.FrontierClosed (E.replayState history)) :
    AdaptiveSiteExploration.adaptiveDecisionWinMass mu answer (E.replayQuery root)
        (E.replayHitsTarget target) history
        (E.replayState history).remaining.card ≤
      E.completionHitProbability q root target (E.replayState history) *
        mu.real (AdaptiveSiteExploration.adaptiveAnswerHistoryEvent answer history) := by
  let s := E.replayState history
  by_cases hfrontier : s.frontier = ∅
  · rw [E.completionHitProbability_of_frontier_eq_empty q root target hwf hrooted hclosed
      hfrontier]
    rw [E.adaptiveDecisionWinMass_replayHitsTarget_of_frontier_eq_empty
      mu hanswer root target history hfrontier]
    by_cases hhit : ∃ t ∈ target, t ∈ (E.replayState history).occupied <;>
      simp [replayHitsTarget, hhit]
  · have hfrontierNonempty : s.frontier.Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hfrontier
    let v := s.frontier.min' hfrontierNonempty
    have hnext : nextVertex s = some v := by
      simp [SiteExploration.nextVertex, hfrontierNonempty, v]
    have hvfrontier : v ∈ s.frontier :=
      SiteExploration.mem_frontier_of_nextVertex_eq_some hnext
    have hvremaining : v ∈ s.remaining := mem_remaining_of_mem_frontier hwf hvfrontier
    let historyTrue := history ++ [(E.replayQuery root history, true)]
    let historyFalse := history ++ [(E.replayQuery root history, false)]
    have hstateTrue : E.replayState historyTrue = E.acceptState s v :=
      E.replayState_append_true_eq_acceptState root history hnext
    have hstateFalse : E.replayState historyFalse = rejectState s v :=
      E.replayState_append_false_eq_rejectState root history hnext
    have hstepTrue : E.step (fun _ ↦ true) s = E.acceptState s v :=
      E.step_eq_acceptState_of_nextVertex_of_answer (fun _ ↦ true) s hnext rfl
    have hstepFalse : E.step (fun _ ↦ false) s = rejectState s v :=
      E.step_eq_rejectState_of_nextVertex_of_answer (fun _ ↦ false) s hnext rfl
    have hwfTrue : (E.replayState historyTrue).WellFormed := by
      rw [hstateTrue, ← hstepTrue]
      exact E.step_wellFormed (fun _ ↦ true) hwf
    have hwfFalse : (E.replayState historyFalse).WellFormed := by
      rw [hstateFalse, ← hstepFalse]
      exact E.step_wellFormed (fun _ ↦ false) hwf
    have hrootedTrue : E.OpenRootedAt root (E.replayState historyTrue) := by
      rw [hstateTrue, ← hstepTrue]
      exact E.step_openRootedAt (fun _ ↦ true) root hrooted
    have hrootedFalse : E.OpenRootedAt root (E.replayState historyFalse) := by
      rw [hstateFalse, ← hstepFalse]
      exact E.step_openRootedAt (fun _ ↦ false) root hrooted
    have hclosedTrue : E.FrontierClosed (E.replayState historyTrue) := by
      rw [hstateTrue, ← hstepTrue]
      exact E.step_frontierClosed (fun _ ↦ true) hclosed
    have hclosedFalse : E.FrontierClosed (E.replayState historyFalse) := by
      rw [hstateFalse, ← hstepFalse]
      exact E.step_frontierClosed (fun _ ↦ false) hclosed
    have hcardTrue : (E.replayState historyTrue).remaining.card + 1 = s.remaining.card := by
      rw [hstateTrue, remaining_acceptState]
      exact Finset.card_erase_add_one hvremaining
    have hcardFalse : (E.replayState historyFalse).remaining.card + 1 = s.remaining.card := by
      rw [hstateFalse, remaining_rejectState]
      exact Finset.card_erase_add_one hvremaining
    have hltTrue : (E.replayState historyTrue).remaining.card <
        (E.replayState history).remaining.card := by
      change (E.replayState historyTrue).remaining.card < s.remaining.card
      omega
    have hltFalse : (E.replayState historyFalse).remaining.card <
        (E.replayState history).remaining.card := by
      change (E.replayState historyFalse).remaining.card < s.remaining.card
      omega
    have ihTrue := E.adaptiveDecisionWinMass_le_completionHitProbability_mul_historyMass
      mu hanswer admissible q hq0 hq1 hupper root target hquery historyTrue
      hwfTrue hrootedTrue hclosedTrue
    have ihFalse := E.adaptiveDecisionWinMass_le_completionHitProbability_mul_historyMass
      mu hanswer admissible q hq0 hq1 hupper root target hquery historyFalse
      hwfFalse hrootedFalse hclosedFalse
    let valueTrue := E.completionHitProbability q root target (E.replayState historyTrue)
    let valueFalse := E.completionHitProbability q root target (E.replayState historyFalse)
    let massHistory := mu.real
      (AdaptiveSiteExploration.adaptiveAnswerHistoryEvent answer history)
    let massTrue := mu.real
      (AdaptiveSiteExploration.adaptiveAnswerHistoryEvent answer historyTrue)
    let massFalse := mu.real
      (AdaptiveSiteExploration.adaptiveAnswerHistoryEvent answer historyFalse)
    have hvalueTrue0 : 0 ≤ valueTrue :=
      finiteBernoulliProbability_nonneg hq0 hq1 _
    have hvalueFalse0 : 0 ≤ valueFalse :=
      finiteBernoulliProbability_nonneg hq0 hq1 _
    have hvalue : valueFalse ≤ valueTrue := by
      dsimp [valueTrue, valueFalse]
      rw [hstateTrue, hstateFalse]
      exact E.completionHitProbability_reject_le_accept hq0 hq1 root target s v
    have hmassHistory0 : 0 ≤ massHistory := measureReal_nonneg
    have hmassTrue0 : 0 ≤ massTrue := measureReal_nonneg
    have hmassFalse0 : 0 ≤ massFalse := measureReal_nonneg
    have hmassPartition : massTrue + massFalse = massHistory := by
      exact AdaptiveSiteExploration.measureReal_adaptiveAnswerHistoryEvent_append_true_add_false
        mu hanswer history (E.replayQuery root history)
    have hmassTrue : massTrue ≤ q * massHistory := by
      exact hupper history (E.replayQuery root history) (hquery history)
    have hbranches :
        AdaptiveSiteExploration.adaptiveDecisionWinMass mu answer (E.replayQuery root)
              (E.replayHitsTarget target) historyTrue
                (E.replayState historyTrue).remaining.card +
            AdaptiveSiteExploration.adaptiveDecisionWinMass mu answer (E.replayQuery root)
              (E.replayHitsTarget target) historyFalse
                (E.replayState historyFalse).remaining.card ≤
          valueTrue * massTrue + valueFalse * massFalse := by
      exact add_le_add ihTrue ihFalse
    rw [E.completionHitProbability_eq_open_closed q root target hwf hvfrontier]
    rw [← hcardTrue, AdaptiveSiteExploration.adaptiveDecisionWinMass_succ]
    rw [← hstateTrue, ← hstateFalse]
    change _ ≤ (q * valueTrue + (1 - q) * valueFalse) * massHistory
    have hcards : (E.replayState historyFalse).remaining.card =
        (E.replayState historyTrue).remaining.card := by omega
    calc
      _ ≤ valueTrue * massTrue + valueFalse * massFalse := by
        simpa [historyTrue, historyFalse, hcards] using hbranches
      _ ≤ (q * valueTrue + (1 - q) * valueFalse) * massHistory := by
        nlinarith
termination_by (E.replayState history).remaining.card
decreasing_by
  · exact hltTrue
  · exact hltFalse

/-- Root form of the upper ratio-free finite target comparison. -/
theorem adaptiveDecisionWinMass_le_completionHitProbability_initial
    {Omega : Type*} [MeasurableSpace Omega]
    (E : SiteExploration V) (mu : Measure Omega) [IsProbabilityMeasure mu]
    {answer : Omega → List (V × Bool) → V → Bool}
    (hanswer : AdaptiveSiteExploration.MeasurableAnswer answer)
    (admissible : List (V × Bool) → V → Prop)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hupper : AdaptiveSiteExploration.HasAdaptiveAnswerUpperBoundOn
      mu answer admissible q)
    (root : V) (target : Finset V)
    (hquery : ∀ history, admissible history (E.replayQuery root history))
    (hwf : E.initial.WellFormed) (hrooted : E.OpenRootedAt root E.initial)
    (hclosed : E.FrontierClosed E.initial) :
    AdaptiveSiteExploration.adaptiveDecisionWinMass mu answer (E.replayQuery root)
        (E.replayHitsTarget target) [] E.initial.remaining.card ≤
      E.completionHitProbability q root target E.initial := by
  simpa [replayState, AdaptiveSiteExploration.adaptiveAnswerHistoryEvent,
    AdaptiveSiteExploration.adaptiveAnswerHistoryEventFrom, probReal_univ] using
    E.adaptiveDecisionWinMass_le_completionHitProbability_mul_historyMass
      mu hanswer admissible q hq0 hq1 hupper root target hquery [] hwf hrooted hclosed

/-- Root form of the ratio-free finite target-hitting comparison. -/
theorem completionHitProbability_initial_le_adaptiveDecisionWinMass
    {Omega : Type*} [MeasurableSpace Omega]
    (E : SiteExploration V) (mu : Measure Omega) [IsProbabilityMeasure mu]
    {answer : Omega → List (V × Bool) → V → Bool}
    (hanswer : AdaptiveSiteExploration.MeasurableAnswer answer)
    (admissible : List (V × Bool) → V → Prop)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hlower : AdaptiveSiteExploration.HasAdaptiveAnswerLowerBoundOn
      mu answer admissible q)
    (root : V) (target : Finset V)
    (hquery : ∀ history, admissible history (E.replayQuery root history))
    (hwf : E.initial.WellFormed) (hrooted : E.OpenRootedAt root E.initial)
    (hclosed : E.FrontierClosed E.initial) :
    E.completionHitProbability q root target E.initial ≤
      AdaptiveSiteExploration.adaptiveDecisionWinMass mu answer (E.replayQuery root)
        (E.replayHitsTarget target) [] E.initial.remaining.card := by
  simpa [replayState, AdaptiveSiteExploration.adaptiveAnswerHistoryEvent,
    AdaptiveSiteExploration.adaptiveAnswerHistoryEventFrom, probReal_univ] using
    E.completionHitProbability_mul_historyMass_le_adaptiveDecisionWinMass
      mu hanswer admissible q hq0 hq1 hlower root target hquery [] hwf hrooted hclosed

/-- Finite-cube event that the open-site set joins `root` to `target`. -/
def finiteSiteHitsTarget (G : SimpleGraph V) (root : V) (target : Finset V) :
    Set (Finset V) :=
  {xi | ∃ t ∈ target, (xi : Set V) ∈ siteConnectionEvent G root t}

omit [Fintype V] [DecidableEq V] [LinearOrder V] in
theorem not_mem_finiteSiteHitsTarget_of_root_notMem
    (G : SimpleGraph V) (root : V) (target : Finset V) {xi : Finset V}
    (hroot : root ∉ xi) : xi ∉ finiteSiteHitsTarget G root target := by
  rintro ⟨t, ht, w, hw⟩
  exact hroot (hw root (by simp))

omit [Fintype V] in
theorem finiteSiteHitsTarget_insert_root_iff_completionHitsTarget_initial
    (G : SimpleGraph V) (neighbors : V → Finset V)
    (mem_neighbors : ∀ {x y}, y ∈ neighbors x ↔ G.Adj x y)
    (root : V) (target : Finset V) (xi : Finset V) :
    insert root xi ∈ finiteSiteHitsTarget G root target ↔
      xi ∈ (rootedSiteExploration G neighbors mem_neighbors root).completionHitsTarget
        root target (rootedSiteExploration G neighbors mem_neighbors root).initial := by
  simp [finiteSiteHitsTarget, completionHitsTarget, rootedSiteExploration,
    SiteExplorationState.completionOpenSet]

/-- The ordinary iid target-connection mass is at most the completion probability in which the
exploration's root is forced open. -/
theorem finiteBernoulliProbability_finiteSiteHitsTarget_le_rooted_completion
    (G : SimpleGraph V) (neighbors : V → Finset V)
    (mem_neighbors : ∀ {x y}, y ∈ neighbors x ↔ G.Adj x y)
    (root : V) (target : Finset V) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    finiteBernoulliProbability Finset.univ q (finiteSiteHitsTarget G root target) ≤
      (rootedSiteExploration G neighbors mem_neighbors root).completionHitProbability
        q root target (rootedSiteExploration G neighbors mem_neighbors root).initial := by
  let E := rootedSiteExploration G neighbors mem_neighbors root
  change finiteBernoulliProbability Finset.univ q (finiteSiteHitsTarget G root target) ≤
    E.completionHitProbability q root target E.initial
  have hremaining : E.initial.remaining = Finset.univ.erase root := by
    ext z
    simp [E, rootedSiteExploration, SiteExplorationState.remaining,
      SiteExplorationState.decided]
  have huniv : insert root (Finset.univ.erase root) = (Finset.univ : Finset V) := by
    exact Finset.insert_erase (Finset.mem_univ root)
  have hopen :
      {xi : Finset V | insert root xi ∈ finiteSiteHitsTarget G root target} =
        E.completionHitsTarget root target E.initial := by
    ext xi
    exact finiteSiteHitsTarget_insert_root_iff_completionHitsTarget_initial
      G neighbors mem_neighbors root target xi
  have hclosed : finiteBernoulliProbability (Finset.univ.erase root) q
      (finiteSiteHitsTarget G root target) = 0 := by
    have heq : finiteBernoulliProbability (Finset.univ.erase root) q
        (finiteSiteHitsTarget G root target) =
          finiteBernoulliProbability (Finset.univ.erase root) q (∅ : Set (Finset V)) :=
      finiteBernoulliProbability_congr q fun xi hxi ↦ by
        apply iff_of_false
        · apply not_mem_finiteSiteHitsTarget_of_root_notMem G root target
          intro hrootXi
          exact Finset.notMem_erase root Finset.univ
            ((Finset.mem_powerset.mp hxi) hrootXi)
        · exact Set.notMem_empty xi
    simp [heq]
  rw [← huniv]
  calc
    finiteBernoulliProbability (insert root (Finset.univ.erase root)) q
        (finiteSiteHitsTarget G root target) =
      q * finiteBernoulliProbability (Finset.univ.erase root) q
          {xi : Finset V | insert root xi ∈ finiteSiteHitsTarget G root target} +
        (1 - q) * finiteBernoulliProbability (Finset.univ.erase root) q
          (finiteSiteHitsTarget G root target) :=
      by
        convert finiteBernoulliProbability_insert
          (Finset.notMem_erase root Finset.univ) q
            (finiteSiteHitsTarget G root target) using 1
        · apply congrArg (fun F : Finset V ↦
            finiteBernoulliProbability F q (finiteSiteHitsTarget G root target))
          ext z
          by_cases hz : z = root <;> simp [hz]
        · apply congrArg (fun x : ℝ ↦ x +
            (1 - q) * finiteBernoulliProbability (Finset.univ.erase root) q
              (finiteSiteHitsTarget G root target))
          apply congrArg (fun x : ℝ ↦ q * x)
          apply finiteBernoulliProbability_congr q
          intro xi _hxi
          simp only [Set.mem_setOf_eq]
          constructor <;> intro h
          · convert h using 1
            ext z
            simp
          · convert h using 1
            ext z
            simp
    _ = q * E.completionHitProbability q root target E.initial := by
      rw [hopen, hclosed, mul_zero, add_zero, completionHitProbability, hremaining]
    _ ≤ E.completionHitProbability q root target E.initial :=
      mul_le_of_le_one_left (finiteBernoulliProbability_nonneg hq0 hq1 _) hq1

/-- Finite, ratio-free target-hitting form of Grimmett Lemma 7.24. -/
theorem finiteSiteHitsTarget_probability_le_adaptiveDecisionWinMass
    {Omega : Type*} [MeasurableSpace Omega]
    (G : SimpleGraph V) (neighbors : V → Finset V)
    (mem_neighbors : ∀ {x y}, y ∈ neighbors x ↔ G.Adj x y)
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    {answer : Omega → List (V × Bool) → V → Bool}
    (hanswer : AdaptiveSiteExploration.MeasurableAnswer answer)
    (admissible : List (V × Bool) → V → Prop)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hlower : AdaptiveSiteExploration.HasAdaptiveAnswerLowerBoundOn
      mu answer admissible q)
    (root : V) (target : Finset V)
    (hquery : ∀ history,
      admissible history
        ((rootedSiteExploration G neighbors mem_neighbors root).replayQuery root history)) :
    finiteBernoulliProbability Finset.univ q (finiteSiteHitsTarget G root target) ≤
      AdaptiveSiteExploration.adaptiveDecisionWinMass mu answer
        ((rootedSiteExploration G neighbors mem_neighbors root).replayQuery root)
        ((rootedSiteExploration G neighbors mem_neighbors root).replayHitsTarget target)
        [] (rootedSiteExploration G neighbors mem_neighbors root).initial.remaining.card := by
  let E := rootedSiteExploration G neighbors mem_neighbors root
  calc
    finiteBernoulliProbability Finset.univ q (finiteSiteHitsTarget G root target) ≤
        E.completionHitProbability q root target E.initial :=
      finiteBernoulliProbability_finiteSiteHitsTarget_le_rooted_completion
        G neighbors mem_neighbors root target hq0 hq1
    _ ≤ _ := E.completionHitProbability_initial_le_adaptiveDecisionWinMass
      mu hanswer admissible q hq0 hq1 hlower root target hquery
      (rootedSiteExploration_initial_wellFormed G neighbors mem_neighbors root)
      (rootedSiteExploration_initial_openRootedAt G neighbors mem_neighbors root)
      (rootedSiteExploration_initial_frontierClosed G neighbors mem_neighbors root)

end SiteExploration

end Percolation
