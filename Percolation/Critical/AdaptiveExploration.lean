import Percolation.Critical.RootedSiteExploration

/-!
# History-dependent site explorations

The Grimmett--Marstrand answer at a coarse vertex depends on the inlet seed and all previously
revealed thresholds.  A static function `V → Bool` therefore cannot faithfully encode the
construction.  This file supplies the history-indexed version of the exploration kernel and
proves its deterministic connectivity and measurable-output laws.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval

/-- A deterministic frontier exploration whose answer may depend on the complete finite
history accumulated before the query. -/
structure AdaptiveSiteExploration (V : Type*) [DecidableEq V] [LinearOrder V] where
  graph : SimpleGraph V
  neighbors : V → Finset V
  mem_neighbors : ∀ {x y}, y ∈ neighbors x ↔ graph.Adj x y
  initial : SiteExplorationState V

/-- Regard a static-answer exploration as an adaptive one; this is also a convenient constructor
because both kernels use the same graph, neighbor, and initial-state data. -/
def SiteExploration.toAdaptive
    {V : Type*} [DecidableEq V] [LinearOrder V]
    (E : SiteExploration V) : AdaptiveSiteExploration V where
  graph := E.graph
  neighbors := E.neighbors
  mem_neighbors := E.mem_neighbors
  initial := E.initial

namespace AdaptiveSiteExploration

variable {V : Type*} [DecidableEq V] [LinearOrder V]

/-- Adaptive exploration of an induced cubic region in the source's fixed vertex order. -/
noncomputable def cubicRegion
    (d : ℕ) (F : Set (Cubic d)) [LinearOrder F] (root : F) :
    AdaptiveSiteExploration F :=
  (cubicRegionSiteExploration d F root).toAdaptive

/-- One adaptive query step. -/
noncomputable def step (E : AdaptiveSiteExploration V)
    (answer : List (V × Bool) → V → Bool)
    (s : SiteExplorationState V) : SiteExplorationState V := by
  classical
  match SiteExploration.nextVertex s with
  | none => exact s
  | some v =>
      if answer s.history v then
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

theorem occupied_subset_step (E : AdaptiveSiteExploration V)
    (answer : List (V × Bool) → V → Bool) (s : SiteExplorationState V) :
    s.occupied ⊆ (E.step answer s).occupied := by
  classical
  unfold step
  split
  · exact Finset.Subset.rfl
  · split
    · exact Finset.subset_insert _ _
    · exact Finset.Subset.rfl

/-- State after `n` history-dependent queries. -/
noncomputable def stateAfter (E : AdaptiveSiteExploration V)
    (answer : List (V × Bool) → V → Bool) : ℕ → SiteExplorationState V
  | 0 => E.initial
  | n + 1 => E.step answer (E.stateAfter answer n)

theorem occupied_mono_stateAfter (E : AdaptiveSiteExploration V)
    (answer : List (V × Bool) → V → Bool) :
    Monotone fun n ↦ (E.stateAfter answer n).occupied := by
  intro m n hmn
  induction n, hmn using Nat.le_induction with
  | base => exact Finset.Subset.rfl
  | succ n _ ih => exact ih.trans (E.occupied_subset_step answer (E.stateAfter answer n))

/-- Increasing union of all adaptively accepted sites. -/
def occupiedLimit (E : AdaptiveSiteExploration V)
    (answer : List (V × Bool) → V → Bool) : Set V :=
  {v | ∃ n, v ∈ (E.stateAfter answer n).occupied}

theorem occupied_subset_occupiedLimit (E : AdaptiveSiteExploration V)
    (answer : List (V × Bool) → V → Bool) (n : ℕ) :
    ((E.stateAfter answer n).occupied : Set V) ⊆ E.occupiedLimit answer := by
  intro v hv
  exact ⟨n, hv⟩

/-- Accepted-support rooted invariant for an adaptive exploration. -/
def OpenRootedAt (E : AdaptiveSiteExploration V)
    (root : V) (s : SiteExplorationState V) : Prop :=
  root ∈ s.occupied ∧
    (∀ v ∈ s.occupied, ∃ w : E.graph.Walk root v,
      ∀ z ∈ w.support, z ∈ s.occupied) ∧
    ∀ v ∈ s.frontier, ∃ u ∈ s.occupied, E.graph.Adj u v

theorem cubicRegion_initial_openRootedAt
    (d : ℕ) (F : Set (Cubic d)) [LinearOrder F] (root : F) :
    (cubicRegion d F root).OpenRootedAt root (cubicRegion d F root).initial := by
  simpa [cubicRegion, SiteExploration.toAdaptive, OpenRootedAt,
    SiteExploration.OpenRootedAt] using
      cubicRegionSiteExploration_initial_openRootedAt d F root

theorem step_openRootedAt (E : AdaptiveSiteExploration V)
    (answer : List (V × Bool) → V → Bool) (root : V)
    {s : SiteExplorationState V} (hs : E.OpenRootedAt root s) :
    E.OpenRootedAt root (E.step answer s) := by
  classical
  unfold OpenRootedAt at hs ⊢
  unfold step
  split
  · exact hs
  next v hnext =>
    have hvfront : v ∈ s.frontier :=
      SiteExploration.mem_frontier_of_nextVertex_eq_some hnext
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

theorem stateAfter_openRootedAt (E : AdaptiveSiteExploration V)
    (answer : List (V × Bool) → V → Bool) (root : V)
    (hinitial : E.OpenRootedAt root E.initial) (n : ℕ) :
    E.OpenRootedAt root (E.stateAfter answer n) := by
  induction n with
  | zero => exact hinitial
  | succ n ih => exact E.step_openRootedAt answer root ih

theorem exists_open_walk_of_mem_occupiedLimit (E : AdaptiveSiteExploration V)
    (answer : List (V × Bool) → V → Bool) (root : V)
    (hinitial : E.OpenRootedAt root E.initial)
    {v : V} (hv : v ∈ E.occupiedLimit answer) :
    ∃ w : E.graph.Walk root v,
      ∀ z ∈ w.support, z ∈ E.occupiedLimit answer := by
  obtain ⟨n, hvn⟩ := hv
  obtain ⟨w, hw⟩ := (E.stateAfter_openRootedAt answer root hinitial n).2.1 v hvn
  exact ⟨w, fun z hz ↦ E.occupied_subset_occupiedLimit answer n (hw z hz)⟩

theorem hasInfiniteSiteCluster_occupiedLimit_of_infinite
    (E : AdaptiveSiteExploration V)
    (answer : List (V × Bool) → V → Bool) (root : V)
    (hinitial : E.OpenRootedAt root E.initial)
    (hInf : (E.occupiedLimit answer).Infinite) :
    hasInfiniteSiteCluster E.graph (E.occupiedLimit answer) := by
  refine ⟨root, hInf.mono ?_⟩
  intro v hv
  exact E.exists_open_walk_of_mem_occupiedLimit answer root hinitial hv

section Measurable

variable {Omega : Type*} [MeasurableSpace Omega] [Countable V]

/-- Every fixed history/query answer bit is measurable. -/
def MeasurableAnswer
    (answer : Omega → List (V × Bool) → V → Bool) : Prop :=
  ∀ history v, Measurable fun omega ↦ answer omega history v

omit [Countable V] in
theorem measurableSet_step_fiber (E : AdaptiveSiteExploration V)
    {answer : Omega → List (V × Bool) → V → Bool}
    (hanswer : MeasurableAnswer answer) (s t : SiteExplorationState V) :
    MeasurableSet {omega | E.step (answer omega) s = t} := by
  classical
  unfold step
  split
  · by_cases hst : s = t
    · simp [hst]
    · simp [hst]
  next v _hnext =>
    let accepted : SiteExplorationState V :=
      { occupied := insert v s.occupied
        rejected := s.rejected
        frontier :=
          (s.frontier.erase v ∪ E.neighbors v) \
            (insert v s.occupied ∪ s.rejected)
        history := s.history ++ [(v, true)] }
    let rejected : SiteExplorationState V :=
      { occupied := s.occupied
        rejected := insert v s.rejected
        frontier := s.frontier.erase v
        history := s.history ++ [(v, false)] }
    change MeasurableSet
      {omega | (if answer omega s.history v then accepted else rejected) = t}
    by_cases ha : accepted = t <;> by_cases hr : rejected = t
    · convert MeasurableSet.univ
      ext omega
      simp [ha, hr]
    · have hset : {omega |
          (if answer omega s.history v then accepted else rejected) = t} =
          {omega | answer omega s.history v = true} := by
        ext omega
        cases hbit : answer omega s.history v <;> simp [hbit, ha, hr]
      rw [hset]
      exact (hanswer s.history v) (MeasurableSet.singleton true)
    · have hset : {omega |
          (if answer omega s.history v then accepted else rejected) = t} =
          {omega | answer omega s.history v = false} := by
        ext omega
        cases hbit : answer omega s.history v <;> simp [hbit, ha, hr]
      rw [hset]
      exact (hanswer s.history v) (MeasurableSet.singleton false)
    · convert MeasurableSet.empty
      ext omega
      cases hbit : answer omega s.history v <;> simp [hbit, ha, hr]

theorem measurableSet_stateAfter_fiber (E : AdaptiveSiteExploration V)
    {answer : Omega → List (V × Bool) → V → Bool}
    (hanswer : MeasurableAnswer answer) :
    ∀ n (t : SiteExplorationState V),
      MeasurableSet {omega | E.stateAfter (answer omega) n = t} := by
  intro n
  induction n with
  | zero =>
      intro t
      by_cases h : E.initial = t <;> simp [stateAfter, h]
  | succ n ih =>
      intro t
      have hrepr : {omega | E.stateAfter (answer omega) (n + 1) = t} =
          ⋃ s : SiteExplorationState V,
            {omega | E.stateAfter (answer omega) n = s} ∩
              {omega | E.step (answer omega) s = t} := by
        ext omega
        simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff, stateAfter]
        constructor
        · intro h
          exact ⟨E.stateAfter (answer omega) n, rfl, h⟩
        · rintro ⟨s, hs, hst⟩
          simpa [hs] using hst
      rw [hrepr]
      exact MeasurableSet.iUnion fun s ↦
        (ih s).inter (E.measurableSet_step_fiber hanswer s t)

theorem measurableSet_mem_occupiedLimit (E : AdaptiveSiteExploration V)
    {answer : Omega → List (V × Bool) → V → Bool}
    (hanswer : MeasurableAnswer answer) (v : V) :
    MeasurableSet {omega | v ∈ E.occupiedLimit (answer omega)} := by
  have hrepr : {omega | v ∈ E.occupiedLimit (answer omega)} =
      ⋃ n : ℕ, ⋃ s : SiteExplorationState V,
        if v ∈ s.occupied then
          {omega | E.stateAfter (answer omega) n = s}
        else ∅ := by
    ext omega
    simp only [occupiedLimit, Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨n, hv⟩
      refine ⟨n, E.stateAfter (answer omega) n, ?_⟩
      rw [if_pos hv]
      rfl
    · rintro ⟨n, s, hs⟩
      split at hs
      next hv => exact ⟨n, hs ▸ hv⟩
      next => simp at hs
  rw [hrepr]
  apply MeasurableSet.iUnion
  intro n
  apply MeasurableSet.iUnion
  intro s
  split
  · exact E.measurableSet_stateAfter_fiber hanswer n s
  · exact MeasurableSet.empty

theorem measurable_occupiedLimit (E : AdaptiveSiteExploration V)
    {answer : Omega → List (V × Bool) → V → Bool}
    (hanswer : MeasurableAnswer answer) :
    Measurable fun omega ↦ E.occupiedLimit (answer omega) := by
  change Measurable
    ((fun P : V → Prop ↦ {v | P v}) ∘
      fun omega v ↦ (v ∈ E.occupiedLimit (answer omega) : Prop))
  refine Measurable.comp (by fun_prop) ?_
  exact measurable_pi_lambda _ fun v ↦
    (E.measurableSet_mem_occupiedLimit hanswer v).mem

/-- Pushforward law of the adaptive occupied limit. -/
noncomputable def occupiedLimitLaw (E : AdaptiveSiteExploration V)
    (mu : Measure Omega) (answer : Omega → List (V × Bool) → V → Bool) :
    Measure (Set V) :=
  mu.map fun omega ↦ E.occupiedLimit (answer omega)

instance occupiedLimitLaw_isProbabilityMeasure (E : AdaptiveSiteExploration V)
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (answer : Omega → List (V × Bool) → V → Bool)
    (hanswer : MeasurableAnswer answer) :
    IsProbabilityMeasure (E.occupiedLimitLaw mu answer) :=
  Measure.isProbabilityMeasure_map
    (E.measurable_occupiedLimit hanswer).aemeasurable

/-- Adaptive analogue of Lemma 7.24: finite-prefix lower bounds on the actual output law imply
positive probability of an infinite connected accepted component. -/
theorem infiniteCluster_probability_pos_of_prefixLowerBound
    (E : AdaptiveSiteExploration V)
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (answer : Omega → List (V × Bool) → V → Bool)
    (hanswer : MeasurableAnswer answer)
    (e : ℕ ≃ V) (p : I) (hp : 0 < (p : ℝ)) (root : V)
    (hinitial : E.OpenRootedAt root E.initial)
    (hseq : ∀ n, HasFiniteSequentialLowerBound
      (enumerationPrefixLaw e n (E.occupiedLimitLaw mu answer)) (p : ℝ)) :
    0 < mu.real {omega |
      hasInfiniteSiteCluster E.graph (E.occupiedLimit (answer omega))} := by
  letI : IsProbabilityMeasure (E.occupiedLimitLaw mu answer) :=
    E.occupiedLimitLaw_isProbabilityMeasure mu answer hanswer
  have hInf := infinite_siteSet_probability_pos_of_prefixSequential e
    (E.occupiedLimitLaw mu answer) p hp hseq
  have hMeas := E.measurable_occupiedLimit hanswer
  have hSetInf : MeasurableSet {eta : Set V | eta.Infinite} := MeasurableSet.setOf_infinite
  rw [occupiedLimitLaw, map_measureReal_apply hMeas hSetInf] at hInf
  exact hInf.trans_le <| measureReal_mono fun omega homega ↦
    E.hasInfiniteSiteCluster_occupiedLimit_of_infinite
      (answer omega) root hinitial homega

end Measurable

end AdaptiveSiteExploration

end Percolation
