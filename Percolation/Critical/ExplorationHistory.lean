import Percolation.Critical.DynamicBlockParameters

/-!
# Exact histories and inlet parents for adaptive block exploration

The source steers each new block relative to the branch by which it was first reached.  The
definitions here recover that inlet deterministically from the finite accepted/rejected history
and prove that the adaptive state machine records precisely those two history projections.
-/

namespace Percolation

/-- Deterministic signed coordinate direction witnessing a cubic adjacency. -/
noncomputable def cubicDirectionOfAdjacent
    {d : ℕ} {x y : Cubic d} (hxy : (cubicGraph d).Adj x y) : CubicDirection d :=
  Classical.choose ((cubicGraph_adj_iff_exists_stepFrom x y).mp hxy)

theorem cubicStepFrom_directionOfAdjacent
    {d : ℕ} {x y : Cubic d} (hxy : (cubicGraph d).Adj x y) :
    cubicStepFrom x (cubicDirectionOfAdjacent hxy) = y := by
  exact (Classical.choose_spec ((cubicGraph_adj_iff_exists_stepFrom x y).mp hxy)).symm

/-- Vertices recorded with answer `true`. -/
def explorationHistoryAccepted {V : Type*} [DecidableEq V] :
    List (V × Bool) → Finset V
  | [] => ∅
  | (v, b) :: history =>
      if b then insert v (explorationHistoryAccepted history)
      else explorationHistoryAccepted history

/-- Vertices recorded with answer `false`. -/
def explorationHistoryRejected {V : Type*} [DecidableEq V] :
    List (V × Bool) → Finset V
  | [] => ∅
  | (v, b) :: history =>
      if b then explorationHistoryRejected history
      else insert v (explorationHistoryRejected history)

@[simp]
theorem explorationHistoryAccepted_nil {V : Type*} [DecidableEq V] :
    explorationHistoryAccepted ([] : List (V × Bool)) = ∅ := rfl

@[simp]
theorem explorationHistoryRejected_nil {V : Type*} [DecidableEq V] :
    explorationHistoryRejected ([] : List (V × Bool)) = ∅ := rfl

@[simp]
theorem explorationHistoryAccepted_append_true
    {V : Type*} [DecidableEq V] (history : List (V × Bool)) (v : V) :
    explorationHistoryAccepted (history ++ [(v, true)]) =
      insert v (explorationHistoryAccepted history) := by
  induction history with
  | nil => simp [explorationHistoryAccepted]
  | cons head history ih =>
      rcases head with ⟨u, b⟩
      cases b <;> simp [explorationHistoryAccepted, ih, Finset.insert_comm]

@[simp]
theorem explorationHistoryAccepted_append_false
    {V : Type*} [DecidableEq V] (history : List (V × Bool)) (v : V) :
    explorationHistoryAccepted (history ++ [(v, false)]) =
      explorationHistoryAccepted history := by
  induction history with
  | nil => simp [explorationHistoryAccepted]
  | cons head history ih =>
      rcases head with ⟨u, b⟩
      cases b <;> simp [explorationHistoryAccepted, ih]

@[simp]
theorem explorationHistoryRejected_append_true
    {V : Type*} [DecidableEq V] (history : List (V × Bool)) (v : V) :
    explorationHistoryRejected (history ++ [(v, true)]) =
      explorationHistoryRejected history := by
  induction history with
  | nil => simp [explorationHistoryRejected]
  | cons head history ih =>
      rcases head with ⟨u, b⟩
      cases b <;> simp [explorationHistoryRejected, ih]

@[simp]
theorem explorationHistoryRejected_append_false
    {V : Type*} [DecidableEq V] (history : List (V × Bool)) (v : V) :
    explorationHistoryRejected (history ++ [(v, false)]) =
      insert v (explorationHistoryRejected history) := by
  induction history with
  | nil => simp [explorationHistoryRejected]
  | cons head history ih =>
      rcases head with ⟨u, b⟩
      cases b <;> simp [explorationHistoryRejected, ih, Finset.insert_comm]

/-- The finite state and its recorded history contain exactly the same decisions. -/
def SiteExplorationState.HistoryConsistent
    {V : Type*} [DecidableEq V] (s : SiteExplorationState V) : Prop :=
  s.occupied = explorationHistoryAccepted s.history ∧
    s.rejected = explorationHistoryRejected s.history

namespace AdaptiveSiteExploration

variable {V : Type*} [DecidableEq V] [LinearOrder V]

theorem step_historyConsistent (E : AdaptiveSiteExploration V)
    (answer : List (V × Bool) → V → Bool)
    {s : SiteExplorationState V} (hs : s.HistoryConsistent) :
    (E.step answer s).HistoryConsistent := by
  classical
  unfold SiteExplorationState.HistoryConsistent at hs ⊢
  unfold step
  split
  · exact hs
  next v _hnext =>
    split
    · simp [hs.1, hs.2]
    · simp [hs.1, hs.2]

theorem stateAfter_historyConsistent (E : AdaptiveSiteExploration V)
    (answer : List (V × Bool) → V → Bool)
    (hinitial : E.initial.HistoryConsistent) (n : ℕ) :
    (E.stateAfter answer n).HistoryConsistent := by
  induction n with
  | zero => exact hinitial
  | succ n ih => exact E.step_historyConsistent answer ih

theorem cubicRegion_initial_historyConsistent
    {d : ℕ} {F : Set (Cubic d)} [LinearOrder F] (root : F) :
    (AdaptiveSiteExploration.cubicRegion d F root).initial.HistoryConsistent := by
  simp [AdaptiveSiteExploration.cubicRegion, SiteExploration.toAdaptive,
    cubicRegionSiteExploration, rootedSiteExploration,
    SiteExplorationState.HistoryConsistent, explorationHistoryAccepted,
    explorationHistoryRejected]

theorem cubicRegion_stateAfter_historyConsistent
    {d : ℕ} {F : Set (Cubic d)} [LinearOrder F] (root : F)
    (answer : List (F × Bool) → F → Bool) (n : ℕ) :
    ((AdaptiveSiteExploration.cubicRegion d F root).stateAfter answer n).HistoryConsistent :=
  (AdaptiveSiteExploration.cubicRegion d F root).stateAfter_historyConsistent answer
    (cubicRegion_initial_historyConsistent root) n

/-- Previously accepted neighbors that may serve as the inlet of `v`. -/
noncomputable def historyInletCandidates (E : AdaptiveSiteExploration V)
    (history : List (V × Bool)) (v : V) : Finset V := by
  classical
  exact (explorationHistoryAccepted history).filter fun u ↦ E.graph.Adj u v

theorem historyInletCandidates_nonempty_of_frontier
    (E : AdaptiveSiteExploration V) (root : V)
    {s : SiteExplorationState V}
    (hrooted : E.OpenRootedAt root s) (hconsistent : s.HistoryConsistent)
    {v : V} (hv : v ∈ s.frontier) :
    (E.historyInletCandidates s.history v).Nonempty := by
  classical
  obtain ⟨u, hu, huv⟩ := hrooted.2.2 v hv
  have huAccepted : u ∈ explorationHistoryAccepted s.history := by
    rw [← hconsistent.1]
    exact hu
  refine ⟨u, ?_⟩
  rw [historyInletCandidates, Finset.mem_filter]
  exact ⟨huAccepted, huv⟩

/-- Earliest accepted neighbor in the fixed vertex order; this is the deterministic inlet used
to orient the next block construction. -/
noncomputable def historyInletParent (E : AdaptiveSiteExploration V)
    (history : List (V × Bool)) (v : V)
    (hne : (E.historyInletCandidates history v).Nonempty) : V :=
  (E.historyInletCandidates history v).min' hne

theorem historyInletParent_mem_accepted (E : AdaptiveSiteExploration V)
    (history : List (V × Bool)) (v : V)
    (hne : (E.historyInletCandidates history v).Nonempty) :
    E.historyInletParent history v hne ∈ explorationHistoryAccepted history := by
  classical
  have hmem := (E.historyInletCandidates history v).min'_mem hne
  change (E.historyInletCandidates history v).min' hne ∈
    explorationHistoryAccepted history
  change (E.historyInletCandidates history v).min' hne ∈
    (explorationHistoryAccepted history).filter (fun u ↦ E.graph.Adj u v) at hmem
  exact (Finset.mem_filter.mp hmem).1

theorem historyInletParent_adj (E : AdaptiveSiteExploration V)
    (history : List (V × Bool)) (v : V)
    (hne : (E.historyInletCandidates history v).Nonempty) :
    E.graph.Adj (E.historyInletParent history v hne) v := by
  classical
  have hmem := (E.historyInletCandidates history v).min'_mem hne
  change E.graph.Adj ((E.historyInletCandidates history v).min' hne) v
  change (E.historyInletCandidates history v).min' hne ∈
    (explorationHistoryAccepted history).filter (fun u ↦ E.graph.Adj u v) at hmem
  exact (Finset.mem_filter.mp hmem).2

theorem cubicRegion_historyInletParent_ambient_adj
    {d : ℕ} {F : Set (Cubic d)} [LinearOrder F] (root : F)
    {s : SiteExplorationState F}
    (hrooted : (AdaptiveSiteExploration.cubicRegion d F root).OpenRootedAt root s)
    (hconsistent : s.HistoryConsistent)
    {v : F} (hv : v ∈ s.frontier) :
    (cubicGraph d).Adj
      ((AdaptiveSiteExploration.cubicRegion d F root).historyInletParent s.history v
        ((AdaptiveSiteExploration.cubicRegion d F root
          ).historyInletCandidates_nonempty_of_frontier root hrooted hconsistent hv))
      v := by
  rw [← SimpleGraph.induce_adj]
  exact (AdaptiveSiteExploration.cubicRegion d F root).historyInletParent_adj _ _ _

/-- At every finite time, the next frontier vertex of the actual induced-region exploration has
a deterministic accepted inlet adjacent in the ambient cubic graph. -/
theorem cubicRegion_stateAfter_frontier_has_inlet
    {d : ℕ} {F : Set (Cubic d)} [LinearOrder F] (root : F)
    (answer : List (F × Bool) → F → Bool) (n : ℕ)
    {v : F}
    (hv : v ∈ ((AdaptiveSiteExploration.cubicRegion d F root).stateAfter answer n).frontier) :
    ∃ u ∈ explorationHistoryAccepted
        ((AdaptiveSiteExploration.cubicRegion d F root).stateAfter answer n).history,
      (cubicGraph d).Adj u v := by
  let E := AdaptiveSiteExploration.cubicRegion d F root
  let s := E.stateAfter answer n
  have hrooted : E.OpenRootedAt root s :=
    E.stateAfter_openRootedAt answer root
      (AdaptiveSiteExploration.cubicRegion_initial_openRootedAt d F root) n
  have hconsistent : s.HistoryConsistent :=
    cubicRegion_stateAfter_historyConsistent root answer n
  obtain ⟨u, hu, huv⟩ := hrooted.2.2 v hv
  refine ⟨u, ?_, ?_⟩
  · rw [← hconsistent.1]
    exact hu
  · exact SimpleGraph.induce_adj.mp huv

/-- Signed coarse-lattice direction from the deterministic inlet parent to a frontier site. -/
noncomputable def cubicRegionHistoryInletDirection
    {d : ℕ} {F : Set (Cubic d)} [LinearOrder F] (root : F)
    (history : List (F × Bool)) (v : F)
    (hne : ((AdaptiveSiteExploration.cubicRegion d F root
      ).historyInletCandidates history v).Nonempty) : CubicDirection d :=
  cubicDirectionOfAdjacent <|
    SimpleGraph.induce_adj.mp <|
      (AdaptiveSiteExploration.cubicRegion d F root).historyInletParent_adj history v hne

theorem cubicStepFrom_historyInletParent_inletDirection
    {d : ℕ} {F : Set (Cubic d)} [LinearOrder F] (root : F)
    (history : List (F × Bool)) (v : F)
    (hne : ((AdaptiveSiteExploration.cubicRegion d F root
      ).historyInletCandidates history v).Nonempty) :
    cubicStepFrom
        ((AdaptiveSiteExploration.cubicRegion d F root).historyInletParent history v hne :
          Cubic d)
        (cubicRegionHistoryInletDirection root history v hne) = v := by
  apply cubicStepFrom_directionOfAdjacent

end AdaptiveSiteExploration

end Percolation
