import Percolation.Critical.Seeds

/-!
# Dynamic renormalization explorations

This file contains the deterministic exploration kernel shared by Grimmett's slab and
half-space block constructions.  Probabilistic estimates are kept outside the state machine:
the kernel only fixes the order in which frontier sites are queried and records every answer.
This separation prevents later conditional-probability arguments from hiding information in an
informal exploration history.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval

/-- Ratio-free form of a conditional success lower bound.  It remains meaningful when the
history event has probability zero; a conditional-probability corollary may divide only after
establishing positive history probability. -/
def HistorySuccessLowerBound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (success history : Set Ω) (γ : ℝ) : Prop :=
  γ * μ.real history ≤ μ.real (success ∩ history)

theorem HistorySuccessLowerBound.conditionalRatio {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {success history : Set Ω} {γ : ℝ}
    (h : HistorySuccessLowerBound μ success history γ)
    (hh : 0 < μ.real history) :
    γ ≤ μ.real (success ∩ history) / μ.real history := by
  exact (le_div_iff₀ hh).2 h

/-- A finite profile of edge-opening thresholds.  Edges outside `support` are assigned the
background threshold. -/
structure BoundaryThresholdProfile (d : ℕ) where
  support : Finset (CubicEdge d)
  threshold : CubicEdge d → I

/-- The inhomogeneous configuration selected from common uniform labels by a boundary profile. -/
def BoundaryThresholdProfile.configuration {d : ℕ}
    (β : BoundaryThresholdProfile d) (background : I)
    (X : CubicEdge d → ℝ) : EdgeConfiguration d :=
  {e | X e < if e ∈ β.support then (β.threshold e : ℝ) else (background : ℝ)}

theorem BoundaryThresholdProfile.configuration_mono {d : ℕ}
    (β β' : BoundaryThresholdProfile d) (background background' : I)
    (hsupport : β.support = β'.support)
    (hthreshold : ∀ e ∈ β.support, β.threshold e ≤ β'.threshold e)
    (hbackground : background ≤ background') (X : CubicEdge d → ℝ) :
    β.configuration background X ⊆ β'.configuration background' X := by
  intro e he
  simp only [BoundaryThresholdProfile.configuration, Set.mem_setOf_eq] at he ⊢
  by_cases hes : e ∈ β.support
  · have hes' : e ∈ β'.support := by simpa [← hsupport] using hes
    rw [if_pos hes] at he
    rw [if_pos hes']
    exact he.trans_le (by exact_mod_cast hthreshold e hes)
  · have hes' : e ∉ β'.support := by simpa [← hsupport] using hes
    rw [if_neg hes] at he
    rw [if_neg hes']
    exact he.trans_le (by exact_mod_cast hbackground)

/-- Finite state of a site exploration.  `frontier` contains sites still eligible to be queried;
`occupied` and `rejected` contain the two possible recorded outcomes. -/
structure SiteExplorationState (V : Type*) [DecidableEq V] where
  occupied : Finset V
  rejected : Finset V
  frontier : Finset V
  history : List (V × Bool)

namespace SiteExplorationState

variable {V : Type*} [DecidableEq V]

/-- Sites whose status has already been decided. -/
def decided (s : SiteExplorationState V) : Finset V :=
  s.occupied ∪ s.rejected

/-- A well-formed state never places a decided site back on the frontier and never records a site
as both occupied and rejected. -/
def WellFormed (s : SiteExplorationState V) : Prop :=
  Disjoint s.occupied s.rejected ∧ Disjoint s.frontier s.decided

end SiteExplorationState

/-- A fixed deterministic exploration rule.  The `LinearOrder` is the promised enumeration:
the least frontier site is always queried next. -/
structure SiteExploration (V : Type*) [DecidableEq V] [LinearOrder V] where
  graph : SimpleGraph V
  neighbors : V → Finset V
  mem_neighbors : ∀ {x y}, y ∈ neighbors x ↔ graph.Adj x y
  initial : SiteExplorationState V

namespace SiteExploration

variable {V : Type*} [DecidableEq V] [LinearOrder V]

/-- Least site in the current frontier, or `none` when exploration is exhausted. -/
noncomputable def nextVertex (s : SiteExplorationState V) : Option V :=
  if h : s.frontier.Nonempty then some (s.frontier.min' h) else none

theorem nextVertex_eq_none_iff (s : SiteExplorationState V) :
    nextVertex s = none ↔ s.frontier = ∅ := by
  classical
  unfold nextVertex
  split_ifs with h
  · simp [Finset.Nonempty.ne_empty h]
  · simp [Finset.not_nonempty_iff_eq_empty.mp h]

theorem mem_frontier_of_nextVertex_eq_some {s : SiteExplorationState V} {v : V}
    (h : nextVertex s = some v) : v ∈ s.frontier := by
  classical
  unfold nextVertex at h
  split_ifs at h with hs
  · have hv : s.frontier.min' hs = v := Option.some.inj h
    simpa [hv] using s.frontier.min'_mem hs

/-- One deterministic query step.  On acceptance, new neighboring sites are added to the
frontier, except for sites whose status is already known. -/
noncomputable def step (E : SiteExploration V) (answer : V → Bool)
    (s : SiteExplorationState V) : SiteExplorationState V := by
  classical
  match nextVertex s with
  | none => exact s
  | some v =>
      if answer v then
        exact
          { occupied := insert v s.occupied
            rejected := s.rejected
            frontier :=
              (s.frontier.erase v ∪ E.neighbors v) \
                (insert v s.occupied ∪ s.rejected)
            history := s.history ++ [(v, true)] }
      else
        exact
          { occupied := s.occupied
            rejected := insert v s.rejected
            frontier := s.frontier.erase v
            history := s.history ++ [(v, false)] }

theorem step_wellFormed (E : SiteExploration V) (answer : V → Bool)
    {s : SiteExplorationState V} (hs : s.WellFormed) :
    (E.step answer s).WellFormed := by
  classical
  unfold step
  split
  · exact hs
  next v hnext =>
    have hvfront : v ∈ s.frontier := mem_frontier_of_nextVertex_eq_some hnext
    have hvnotDecided : v ∉ s.decided :=
      Finset.disjoint_left.mp hs.2 hvfront
    have hvnotOccupied : v ∉ s.occupied := fun hv ↦
      hvnotDecided (Finset.mem_union_left _ hv)
    have hvnotRejected : v ∉ s.rejected := fun hv ↦
      hvnotDecided (Finset.mem_union_right _ hv)
    split
    · change Disjoint (insert v s.occupied) s.rejected ∧
        Disjoint
          ((s.frontier.erase v ∪ E.neighbors v) \
            (insert v s.occupied ∪ s.rejected))
          (insert v s.occupied ∪ s.rejected)
      exact ⟨Finset.disjoint_insert_left.mpr ⟨hvnotRejected, hs.1⟩,
        Finset.sdiff_disjoint⟩
    · change Disjoint s.occupied (insert v s.rejected) ∧
        Disjoint (s.frontier.erase v) (s.occupied ∪ insert v s.rejected)
      refine ⟨Finset.disjoint_insert_right.mpr ⟨hvnotOccupied, hs.1⟩, ?_⟩
      rw [Finset.disjoint_left]
      intro z hzfront hzdecided
      rw [Finset.mem_union] at hzdecided
      rcases hzdecided with hzocc | hzrej
      · exact (Finset.disjoint_left.mp hs.2 (Finset.mem_of_mem_erase hzfront))
          (Finset.mem_union_left _ hzocc)
      · rw [Finset.mem_insert] at hzrej
        rcases hzrej with rfl | hzrej
        · simp at hzfront
        · exact (Finset.disjoint_left.mp hs.2 (Finset.mem_of_mem_erase hzfront))
            (Finset.mem_union_right _ hzrej)

/-- State after `n` queries. -/
noncomputable def stateAfter (E : SiteExploration V) (answer : V → Bool) :
    ℕ → SiteExplorationState V
  | 0 => E.initial
  | n + 1 => E.step answer (E.stateAfter answer n)

theorem stateAfter_wellFormed (E : SiteExploration V) (answer : V → Bool)
    (hinitial : E.initial.WellFormed) (n : ℕ) :
    (E.stateAfter answer n).WellFormed := by
  induction n with
  | zero => exact hinitial
  | succ n ih => exact E.step_wellFormed answer ih

theorem occupied_subset_step (E : SiteExploration V) (answer : V → Bool)
    (s : SiteExplorationState V) : s.occupied ⊆ (E.step answer s).occupied := by
  classical
  unfold step
  split
  · exact Finset.Subset.rfl
  · split
    · exact Finset.subset_insert _ _
    · exact Finset.Subset.rfl

theorem rejected_subset_step (E : SiteExploration V) (answer : V → Bool)
    (s : SiteExplorationState V) : s.rejected ⊆ (E.step answer s).rejected := by
  classical
  unfold step
  split
  · exact Finset.Subset.rfl
  · split
    · exact Finset.Subset.rfl
    · exact Finset.subset_insert _ _

theorem occupied_mono_stateAfter (E : SiteExploration V) (answer : V → Bool) :
    Monotone fun n ↦ (E.stateAfter answer n).occupied := by
  intro m n hmn
  induction n, hmn using Nat.le_induction with
  | base => exact Finset.Subset.rfl
  | succ n hmn ih =>
      exact ih.trans (E.occupied_subset_step answer (E.stateAfter answer n))

theorem rejected_mono_stateAfter (E : SiteExploration V) (answer : V → Bool) :
    Monotone fun n ↦ (E.stateAfter answer n).rejected := by
  intro m n hmn
  induction n, hmn using Nat.le_induction with
  | base => exact Finset.Subset.rfl
  | succ n hmn ih =>
      exact ih.trans (E.rejected_subset_step answer (E.stateAfter answer n))

theorem step_eq_self_of_frontier_eq_empty (E : SiteExploration V) (answer : V → Bool)
    {s : SiteExplorationState V} (hs : s.frontier = ∅) : E.step answer s = s := by
  classical
  unfold step
  rw [(nextVertex_eq_none_iff s).mpr hs]

/-! ### The limiting explored set and rooted connectivity -/

/-- The increasing union `A∞` of all accepted sites. -/
def occupiedLimit (E : SiteExploration V) (answer : V → Bool) : Set V :=
  {v | ∃ n, v ∈ (E.stateAfter answer n).occupied}

/-- The increasing union of all rejected sites. -/
def rejectedLimit (E : SiteExploration V) (answer : V → Bool) : Set V :=
  {v | ∃ n, v ∈ (E.stateAfter answer n).rejected}

theorem occupied_subset_occupiedLimit (E : SiteExploration V) (answer : V → Bool)
    (n : ℕ) :
    ((E.stateAfter answer n).occupied : Set V) ⊆ E.occupiedLimit answer := by
  intro v hv
  exact ⟨n, hv⟩

theorem rejected_subset_rejectedLimit (E : SiteExploration V) (answer : V → Bool)
    (n : ℕ) :
    ((E.stateAfter answer n).rejected : Set V) ⊆ E.rejectedLimit answer := by
  intro v hv
  exact ⟨n, hv⟩

/-- State invariant used to retain the source's rooted conclusion: every occupied site is
reachable from `root`, and every frontier site has an already occupied neighbor. -/
def RootedAt (E : SiteExploration V) (root : V) (s : SiteExplorationState V) : Prop :=
  root ∈ s.occupied ∧
    (∀ v ∈ s.occupied, E.graph.Reachable root v) ∧
    ∀ v ∈ s.frontier, ∃ u ∈ s.occupied, E.graph.Adj u v

theorem step_rootedAt (E : SiteExploration V) (answer : V → Bool) (root : V)
    {s : SiteExplorationState V} (hs : E.RootedAt root s) :
    E.RootedAt root (E.step answer s) := by
  classical
  unfold RootedAt at hs ⊢
  unfold step
  split
  · exact hs
  next v hnext =>
    have hvfront : v ∈ s.frontier := mem_frontier_of_nextVertex_eq_some hnext
    obtain ⟨u, huocc, huv⟩ := hs.2.2 v hvfront
    split
    · refine ⟨Finset.mem_insert_of_mem hs.1, ?_, ?_⟩
      · intro z hz
        rw [Finset.mem_insert] at hz
        rcases hz with rfl | hz
        · exact (hs.2.1 u huocc).trans (SimpleGraph.Adj.reachable huv)
        · exact hs.2.1 z hz
      · intro z hz
        have hz' := Finset.mem_sdiff.mp hz
        rw [Finset.mem_union] at hz'
        rcases hz'.1 with hzold | hznew
        · obtain ⟨w, hwocc, hwz⟩ := hs.2.2 z (Finset.mem_of_mem_erase hzold)
          exact ⟨w, Finset.mem_insert_of_mem hwocc, hwz⟩
        · exact ⟨v, by simp, (E.mem_neighbors).mp hznew⟩
    · refine ⟨hs.1, hs.2.1, ?_⟩
      intro z hz
      exact hs.2.2 z (Finset.mem_of_mem_erase hz)

theorem stateAfter_rootedAt (E : SiteExploration V) (answer : V → Bool) (root : V)
    (hinitial : E.RootedAt root E.initial) (n : ℕ) :
    E.RootedAt root (E.stateAfter answer n) := by
  induction n with
  | zero => exact hinitial
  | succ n ih => exact E.step_rootedAt answer root ih

/-- Every site in the limiting explored set remains connected to the fixed initial root. -/
theorem reachable_of_mem_occupiedLimit (E : SiteExploration V) (answer : V → Bool)
    (root : V) (hinitial : E.RootedAt root E.initial)
    {v : V} (hv : v ∈ E.occupiedLimit answer) : E.graph.Reachable root v := by
  obtain ⟨n, hvn⟩ := hv
  exact (E.stateAfter_rootedAt answer root hinitial n).2.1 v hvn

/-- Any two accepted sites in `A∞` are joined through the fixed root. -/
theorem reachable_between_of_mem_occupiedLimit (E : SiteExploration V)
    (answer : V → Bool) (root : V) (hinitial : E.RootedAt root E.initial)
    {u v : V} (hu : u ∈ E.occupiedLimit answer) (hv : v ∈ E.occupiedLimit answer) :
    E.graph.Reachable u v :=
  (E.reachable_of_mem_occupiedLimit answer root hinitial hu).symm.trans
    (E.reachable_of_mem_occupiedLimit answer root hinitial hv)

/-! ### Connectivity through accepted sites

`RootedAt` above records ambient reachability, which is useful for coarse geometry but is not
strong enough by itself to produce a site-open cluster: an ambient witness may pass through
rejected vertices.  The strengthened invariant below retains an explicit walk supported by the
accepted set. -/

/-- Every accepted site is joined to `root` by a walk whose entire support is accepted, and
every frontier site has an accepted neighbor. -/
def OpenRootedAt (E : SiteExploration V) (root : V) (s : SiteExplorationState V) : Prop :=
  root ∈ s.occupied ∧
    (∀ v ∈ s.occupied, ∃ w : E.graph.Walk root v,
      ∀ z ∈ w.support, z ∈ s.occupied) ∧
    ∀ v ∈ s.frontier, ∃ u ∈ s.occupied, E.graph.Adj u v

theorem step_openRootedAt (E : SiteExploration V) (answer : V → Bool) (root : V)
    {s : SiteExplorationState V} (hs : E.OpenRootedAt root s) :
    E.OpenRootedAt root (E.step answer s) := by
  classical
  unfold OpenRootedAt at hs ⊢
  unfold step
  split
  · exact hs
  next v hnext =>
    have hvfront : v ∈ s.frontier := mem_frontier_of_nextVertex_eq_some hnext
    obtain ⟨u, huocc, huv⟩ := hs.2.2 v hvfront
    split
    · refine ⟨Finset.mem_insert_of_mem hs.1, ?_, ?_⟩
      · intro z hz
        rw [Finset.mem_insert] at hz
        rcases hz with hzEq | hz
        · subst z
          obtain ⟨w, hw⟩ := hs.2.1 u huocc
          let stepWalk : E.graph.Walk u v :=
            SimpleGraph.Walk.cons huv SimpleGraph.Walk.nil
          refine ⟨w.append stepWalk, ?_⟩
          intro a ha
          rw [SimpleGraph.Walk.mem_support_append_iff] at ha
          rcases ha with ha | ha
          · exact Finset.mem_insert_of_mem (hw a ha)
          · simp only [stepWalk, SimpleGraph.Walk.support_cons, List.mem_cons,
              SimpleGraph.Walk.support_nil] at ha
            rcases ha with hau | ha
            · rw [hau]
              exact Finset.mem_insert_of_mem huocc
            · rcases ha with hav | ha
              · rw [hav]
                exact Finset.mem_insert_self v s.occupied
              · simp at ha
        · obtain ⟨w, hw⟩ := hs.2.1 z hz
          exact ⟨w, fun a ha ↦ Finset.mem_insert_of_mem (hw a ha)⟩
      · intro z hz
        have hz' := Finset.mem_sdiff.mp hz
        rw [Finset.mem_union] at hz'
        rcases hz'.1 with hzold | hznew
        · obtain ⟨w, hwocc, hwz⟩ := hs.2.2 z (Finset.mem_of_mem_erase hzold)
          exact ⟨w, Finset.mem_insert_of_mem hwocc, hwz⟩
        · exact ⟨v, Finset.mem_insert_self v s.occupied, (E.mem_neighbors).mp hznew⟩
    · refine ⟨hs.1, hs.2.1, ?_⟩
      intro z hz
      exact hs.2.2 z (Finset.mem_of_mem_erase hz)

theorem stateAfter_openRootedAt (E : SiteExploration V) (answer : V → Bool) (root : V)
    (hinitial : E.OpenRootedAt root E.initial) (n : ℕ) :
    E.OpenRootedAt root (E.stateAfter answer n) := by
  induction n with
  | zero => exact hinitial
  | succ n ih => exact E.step_openRootedAt answer root ih

/-- Every limiting accepted site has a root path supported entirely by the limiting accepted
set. -/
theorem exists_open_walk_of_mem_occupiedLimit (E : SiteExploration V)
    (answer : V → Bool) (root : V) (hinitial : E.OpenRootedAt root E.initial)
    {v : V} (hv : v ∈ E.occupiedLimit answer) :
    ∃ w : E.graph.Walk root v,
      ∀ z ∈ w.support, z ∈ E.occupiedLimit answer := by
  obtain ⟨n, hvn⟩ := hv
  obtain ⟨w, hw⟩ := (E.stateAfter_openRootedAt answer root hinitial n).2.1 v hvn
  exact ⟨w, fun z hz ↦ E.occupied_subset_occupiedLimit answer n (hw z hz)⟩

/-- The limiting accepted set is contained in the site-open component of its root. -/
theorem occupiedLimit_subset_siteOpenCluster (E : SiteExploration V)
    (answer : V → Bool) (root : V) (hinitial : E.OpenRootedAt root E.initial) :
    E.occupiedLimit answer ⊆ siteOpenCluster E.graph (E.occupiedLimit answer) root := by
  intro v hv
  exact E.exists_open_walk_of_mem_occupiedLimit answer root hinitial hv

/-- An infinite limiting accepted set therefore contains an infinite site-open cluster. -/
theorem hasInfiniteSiteCluster_occupiedLimit_of_infinite (E : SiteExploration V)
    (answer : V → Bool) (root : V) (hinitial : E.OpenRootedAt root E.initial)
    (hInf : (E.occupiedLimit answer).Infinite) :
    hasInfiniteSiteCluster E.graph (E.occupiedLimit answer) := by
  exact ⟨root, hInf.mono (E.occupiedLimit_subset_siteOpenCluster answer root hinitial)⟩

end SiteExploration

end Percolation
