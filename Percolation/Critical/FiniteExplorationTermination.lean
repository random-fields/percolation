import Percolation.Critical.AdaptiveDecisionTree

/-!
# Termination of finite site explorations

On a finite graph, every nonempty-frontier step decides a genuinely new vertex.  Consequently
both the static and history-dependent exploration kernels have empty frontier after at most
`Fintype.card V` steps.  This is the finiteness input needed to identify finite decision-tree
target events with ordinary site-connectivity events in the proof of Grimmett Lemma 7.24.
-/

namespace Percolation

namespace SiteExploration

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

omit [Fintype V] in
theorem step_decided_card_eq_add_one
    (E : SiteExploration V) (answer : V → Bool)
    {s : SiteExplorationState V} (hs : s.WellFormed)
    (hfrontier : s.frontier.Nonempty) :
    (E.step answer s).decided.card = s.decided.card + 1 := by
  classical
  let v := s.frontier.min' hfrontier
  have hnext : SiteExploration.nextVertex s = some v := by
    simp [SiteExploration.nextVertex, hfrontier, v]
  have hvfront : v ∈ s.frontier :=
    SiteExploration.mem_frontier_of_nextVertex_eq_some hnext
  have hvnot : v ∉ s.decided := fun hv ↦
    Finset.disjoint_left.mp hs.2 hvfront hv
  by_cases ha : answer v = true
  · have hstep : E.step answer s =
        { occupied := insert v s.occupied
          rejected := s.rejected
          frontier :=
            (s.frontier.erase v ∪ E.neighbors v) \
              (insert v s.occupied ∪ s.rejected)
          history := s.history ++ [(v, true)] } := by
      simp [SiteExploration.step, hnext, ha]
    rw [hstep]
    change (insert v s.occupied ∪ s.rejected).card = s.decided.card + 1
    have hdecided :
        (insert v s.occupied ∪ s.rejected) = insert v s.decided := by
      ext z
      simp [SiteExplorationState.decided]
    rw [hdecided, Finset.card_insert_of_notMem hvnot]
  · have hstep : E.step answer s =
        { occupied := s.occupied
          rejected := insert v s.rejected
          frontier := s.frontier.erase v
          history := s.history ++ [(v, false)] } := by
      have hafalse : answer v = false := Bool.eq_false_of_not_eq_true ha
      simp [SiteExploration.step, hnext, hafalse]
    rw [hstep]
    change (s.occupied ∪ insert v s.rejected).card = s.decided.card + 1
    have hdecided :
        (s.occupied ∪ insert v s.rejected) = insert v s.decided := by
      ext z
      simp [SiteExplorationState.decided]
    rw [hdecided, Finset.card_insert_of_notMem hvnot]

omit [Fintype V] in
theorem stateAfter_frontier_empty_persists
    (E : SiteExploration V) (answer : V → Bool)
    {n : ℕ} (hn : (E.stateAfter answer n).frontier = ∅) :
    ∀ m, (E.stateAfter answer (n + m)).frontier = ∅ := by
  intro m
  induction m with
  | zero => simpa
  | succ m ih =>
      rw [Nat.add_succ, SiteExploration.stateAfter,
        E.step_eq_self_of_frontier_eq_empty answer ih]
      exact ih

omit [Fintype V] in
theorem stateAfter_frontier_nonempty_of_succ
    (E : SiteExploration V) (answer : V → Bool) {n : ℕ}
    (h : (E.stateAfter answer (n + 1)).frontier.Nonempty) :
    (E.stateAfter answer n).frontier.Nonempty := by
  by_contra hn
  have hempty : (E.stateAfter answer n).frontier = ∅ :=
    Finset.not_nonempty_iff_eq_empty.mp hn
  have hpersist := E.stateAfter_frontier_empty_persists answer hempty 1
  simpa using h.ne_empty hpersist

omit [Fintype V] in
theorem stateAfter_decided_card_eq_add_of_frontier_nonempty
    (E : SiteExploration V) (answer : V → Bool)
    (hinitial : E.initial.WellFormed) {n : ℕ}
    (hfrontier : (E.stateAfter answer n).frontier.Nonempty) :
    (E.stateAfter answer n).decided.card = E.initial.decided.card + n := by
  induction n with
  | zero => simp [SiteExploration.stateAfter]
  | succ n ih =>
      have hprev := E.stateAfter_frontier_nonempty_of_succ answer hfrontier
      rw [SiteExploration.stateAfter,
        E.step_decided_card_eq_add_one answer
          (E.stateAfter_wellFormed answer hinitial n) hprev,
        ih hprev]
      omega

/-- A finite static exploration has exhausted its frontier after at most `|V|` queries. -/
theorem stateAfter_card_frontier_eq_empty
    (E : SiteExploration V) (answer : V → Bool)
    (hinitial : E.initial.WellFormed) :
    (E.stateAfter answer (Fintype.card V)).frontier = ∅ := by
  by_contra hne
  have hfrontier : (E.stateAfter answer (Fintype.card V)).frontier.Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr hne
  have hcard := E.stateAfter_decided_card_eq_add_of_frontier_nonempty
    answer hinitial hfrontier
  have hproper : (E.stateAfter answer (Fintype.card V)).decided ⊂
      (Finset.univ : Finset V) := by
    rw [Finset.ssubset_univ_iff]
    intro heq
    obtain ⟨v, hv⟩ := hfrontier
    have hwf := E.stateAfter_wellFormed answer hinitial (Fintype.card V)
    exact Finset.disjoint_left.mp hwf.2 hv (heq.symm ▸ Finset.mem_univ v)
  have hlt := Finset.card_lt_card hproper
  simp only [Finset.card_univ] at hlt
  omega

end SiteExploration

namespace AdaptiveSiteExploration

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

/-- Forget history dependence while retaining an adaptive exploration's graph and state data. -/
def toStatic (E : AdaptiveSiteExploration V) : SiteExploration V where
  graph := E.graph
  neighbors := E.neighbors
  mem_neighbors := E.mem_neighbors
  initial := E.initial

omit [Fintype V] in
theorem step_eq_toStatic_step
    (E : AdaptiveSiteExploration V)
    (answer : List (V × Bool) → V → Bool) (s : SiteExplorationState V) :
    E.step answer s = E.toStatic.step (answer s.history) s := by
  rfl

omit [Fintype V] in
theorem step_wellFormed
    (E : AdaptiveSiteExploration V)
    (answer : List (V × Bool) → V → Bool)
    {s : SiteExplorationState V} (hs : s.WellFormed) :
    (E.step answer s).WellFormed := by
  rw [E.step_eq_toStatic_step answer s]
  exact E.toStatic.step_wellFormed (answer s.history) hs

omit [Fintype V] in
theorem stateAfter_wellFormed
    (E : AdaptiveSiteExploration V)
    (answer : List (V × Bool) → V → Bool)
    (hinitial : E.initial.WellFormed) (n : ℕ) :
    (E.stateAfter answer n).WellFormed := by
  induction n with
  | zero => exact hinitial
  | succ n ih => exact E.step_wellFormed answer ih

omit [Fintype V] in
theorem step_decided_card_eq_add_one
    (E : AdaptiveSiteExploration V)
    (answer : List (V × Bool) → V → Bool)
    {s : SiteExplorationState V} (hs : s.WellFormed)
    (hfrontier : s.frontier.Nonempty) :
    (E.step answer s).decided.card = s.decided.card + 1 := by
  rw [E.step_eq_toStatic_step answer s]
  exact E.toStatic.step_decided_card_eq_add_one (answer s.history) hs hfrontier

omit [Fintype V] in
theorem step_eq_self_of_frontier_eq_empty
    (E : AdaptiveSiteExploration V)
    (answer : List (V × Bool) → V → Bool)
    {s : SiteExplorationState V} (hs : s.frontier = ∅) :
    E.step answer s = s := by
  rw [E.step_eq_toStatic_step answer s]
  exact E.toStatic.step_eq_self_of_frontier_eq_empty (answer s.history) hs

omit [Fintype V] in
theorem stateAfter_frontier_empty_persists
    (E : AdaptiveSiteExploration V)
    (answer : List (V × Bool) → V → Bool)
    {n : ℕ} (hn : (E.stateAfter answer n).frontier = ∅) :
    ∀ m, (E.stateAfter answer (n + m)).frontier = ∅ := by
  intro m
  induction m with
  | zero => simpa
  | succ m ih =>
      rw [Nat.add_succ, AdaptiveSiteExploration.stateAfter,
        E.step_eq_self_of_frontier_eq_empty answer ih]
      exact ih

omit [Fintype V] in
theorem stateAfter_frontier_nonempty_of_succ
    (E : AdaptiveSiteExploration V)
    (answer : List (V × Bool) → V → Bool) {n : ℕ}
    (h : (E.stateAfter answer (n + 1)).frontier.Nonempty) :
    (E.stateAfter answer n).frontier.Nonempty := by
  by_contra hn
  have hempty : (E.stateAfter answer n).frontier = ∅ :=
    Finset.not_nonempty_iff_eq_empty.mp hn
  have hpersist := E.stateAfter_frontier_empty_persists answer hempty 1
  simpa using h.ne_empty hpersist

omit [Fintype V] in
theorem stateAfter_decided_card_eq_add_of_frontier_nonempty
    (E : AdaptiveSiteExploration V)
    (answer : List (V × Bool) → V → Bool)
    (hinitial : E.initial.WellFormed) {n : ℕ}
    (hfrontier : (E.stateAfter answer n).frontier.Nonempty) :
    (E.stateAfter answer n).decided.card = E.initial.decided.card + n := by
  induction n with
  | zero => simp [AdaptiveSiteExploration.stateAfter]
  | succ n ih =>
      have hprev := E.stateAfter_frontier_nonempty_of_succ answer hfrontier
      rw [AdaptiveSiteExploration.stateAfter,
        E.step_decided_card_eq_add_one answer
          (E.stateAfter_wellFormed answer hinitial n) hprev,
        ih hprev]
      omega

/-- A finite history-dependent exploration also exhausts its frontier after `|V|` queries. -/
theorem stateAfter_card_frontier_eq_empty
    (E : AdaptiveSiteExploration V)
    (answer : List (V × Bool) → V → Bool)
    (hinitial : E.initial.WellFormed) :
    (E.stateAfter answer (Fintype.card V)).frontier = ∅ := by
  by_contra hne
  have hfrontier : (E.stateAfter answer (Fintype.card V)).frontier.Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr hne
  have hcard := E.stateAfter_decided_card_eq_add_of_frontier_nonempty
    answer hinitial hfrontier
  have hproper : (E.stateAfter answer (Fintype.card V)).decided ⊂
      (Finset.univ : Finset V) := by
    rw [Finset.ssubset_univ_iff]
    intro heq
    obtain ⟨v, hv⟩ := hfrontier
    have hwf := E.stateAfter_wellFormed answer hinitial (Fintype.card V)
    exact Finset.disjoint_left.mp hwf.2 hv (heq.symm ▸ Finset.mem_univ v)
  have hlt := Finset.card_lt_card hproper
  simp only [Finset.card_univ] at hlt
  omega

end AdaptiveSiteExploration

end Percolation
