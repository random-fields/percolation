import Percolation.Critical.AdaptiveAnswerEmbedding
import Percolation.Critical.RootedSiteShellProbability

/-!
# Compatibility of finite-ball and ambient adaptive explorations

Before a rooted exploration first accepts a vertex on its radius-`n` sphere, every queried
frontier vertex lies in the finite radius-`n` ball.  Consequently the finite induced exploration
and the ambient region exploration have identical lifted states.  At the first accepted boundary
vertex the ambient occupied limit has hit the same sphere.  This is the deterministic compatibility
step needed to apply the finite Bellman estimate at every radius in Grimmett Lemma 7.24.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory Classical

namespace SiteExploration

/-- The subtype embedding of a finite region ball into the full region. -/
def cubicRegionBallEmbedding
    (d : ℕ) (F : Set (Cubic d)) (root : F) (n : ℕ) :
    {v : F // v ∈ cubicRegionMetricBall d F root n} ↪ F :=
  ⟨Subtype.val, Subtype.val_injective⟩

@[simp]
theorem cubicRegionBallEmbedding_apply
    (d : ℕ) (F : Set (Cubic d)) (root : F) (n : ℕ)
    (v : {v : F // v ∈ cubicRegionMetricBall d F root n}) :
    cubicRegionBallEmbedding d F root n v = (v : F) :=
  rfl

/-- Neighbor finset for the graph induced on a finite region ball. -/
noncomputable def cubicRegionBallNeighborFinset
    (d : ℕ) (F : Set (Cubic d)) (root : F) (n : ℕ)
    (v : {v : F // v ∈ cubicRegionMetricBall d F root n}) :
    Finset {v : F // v ∈ cubicRegionMetricBall d F root n} :=
  (cubicRegionNeighborFinset d F v).subtype
    fun z ↦ z ∈ cubicRegionMetricBall d F root n

@[simp]
theorem mem_cubicRegionBallNeighborFinset_iff
    {d n : ℕ} {F : Set (Cubic d)} {root : F}
    {u v : {v : F // v ∈ cubicRegionMetricBall d F root n}} :
    v ∈ cubicRegionBallNeighborFinset d F root n u ↔
      ((cubicRegionGraph d F).induce
        (cubicRegionMetricBall d F root n : Set F)).Adj u v := by
  classical
  rw [cubicRegionBallNeighborFinset, Finset.mem_subtype,
    SimpleGraph.induce_adj]
  exact mem_cubicRegionNeighborFinset_iff

/-- Canonical finite rooted exploration of a region metric ball. -/
noncomputable def cubicRegionBallSiteExploration
    (d : ℕ) (F : Set (Cubic d)) [LinearOrder F] (root : F) (n : ℕ) :
    SiteExploration {v : F // v ∈ cubicRegionMetricBall d F root n} :=
  rootedSiteExploration
    ((cubicRegionGraph d F).induce
      (cubicRegionMetricBall d F root n : Set F))
    (cubicRegionBallNeighborFinset d F root n)
    mem_cubicRegionBallNeighborFinset_iff
    (cubicRegionBallRoot d F root n)

/-- Lift a finite-ball exploration state into the ambient region. -/
noncomputable def liftCubicRegionBallState
    (d : ℕ) (F : Set (Cubic d)) (root : F) (n : ℕ)
    (s : SiteExplorationState {v : F // v ∈ cubicRegionMetricBall d F root n}) :
    SiteExplorationState F where
  occupied := s.occupied.map (cubicRegionBallEmbedding d F root n)
  rejected := s.rejected.map (cubicRegionBallEmbedding d F root n)
  frontier := s.frontier.map (cubicRegionBallEmbedding d F root n)
  history := AdaptiveSiteExploration.mapDecisionHistory
    (cubicRegionBallEmbedding d F root n) s.history

@[simp]
theorem mem_liftCubicRegionBallState_occupied
    {d n : ℕ} {F : Set (Cubic d)} {root : F}
    {s : SiteExplorationState {v : F // v ∈ cubicRegionMetricBall d F root n}}
    {v : {v : F // v ∈ cubicRegionMetricBall d F root n}} :
    (v : F) ∈ (liftCubicRegionBallState d F root n s).occupied ↔ v ∈ s.occupied := by
  simp [liftCubicRegionBallState, cubicRegionBallEmbedding]

@[simp]
theorem mem_liftCubicRegionBallState_frontier
    {d n : ℕ} {F : Set (Cubic d)} {root : F}
    {s : SiteExplorationState {v : F // v ∈ cubicRegionMetricBall d F root n}}
    {v : {v : F // v ∈ cubicRegionMetricBall d F root n}} :
    (v : F) ∈ (liftCubicRegionBallState d F root n s).frontier ↔ v ∈ s.frontier := by
  simp [liftCubicRegionBallState, cubicRegionBallEmbedding]

/-- An interior ball vertex has exactly the same neighbors in the finite ball and in the full
region. -/
theorem map_cubicRegionBallNeighborFinset_eq_of_lt
    {d n : ℕ} {F : Set (Cubic d)} {root : F}
    (v : {v : F // v ∈ cubicRegionMetricBall d F root n})
    (hv : cubicL1Dist (root : Cubic d) (v : Cubic d) < n) :
    (cubicRegionBallNeighborFinset d F root n v).map
        (cubicRegionBallEmbedding d F root n) =
      cubicRegionNeighborFinset d F v := by
  classical
  ext z
  constructor
  · intro hz
    obtain ⟨z', hz', rfl⟩ := Finset.mem_map.mp hz
    exact (Finset.mem_subtype.mp hz')
  · intro hz
    have hadj : (cubicGraph d).Adj (v : Cubic d) (z : Cubic d) := by
      exact SimpleGraph.induce_adj.mp (mem_cubicRegionNeighborFinset_iff.mp hz)
    obtain ⟨a, ha⟩ := (cubicGraph_adj_iff_exists_stepFrom _ _).mp hadj
    have hzBall : z ∈ cubicRegionMetricBall d F root n := by
      rw [mem_cubicRegionMetricBall_iff]
      calc
        cubicL1Dist (root : Cubic d) (z : Cubic d) ≤
            cubicL1Dist (root : Cubic d) (v : Cubic d) +
              cubicL1Dist (v : Cubic d) (z : Cubic d) :=
          cubicL1Dist_triangle _ _ _
        _ = cubicL1Dist (root : Cubic d) (v : Cubic d) + 1 := by
          rw [ha, cubicL1Dist_stepFrom]
        _ ≤ n := by omega
    refine Finset.mem_map.mpr ⟨⟨z, hzBall⟩, ?_, rfl⟩
    exact Finset.mem_subtype.mpr hz

/-- Taking the least frontier vertex commutes with lifting a finite-ball state. -/
theorem nextVertex_liftCubicRegionBallState
    {d n : ℕ} {F : Set (Cubic d)} [LinearOrder F] {root : F}
    (s : SiteExplorationState {v : F // v ∈ cubicRegionMetricBall d F root n}) :
    Option.map (cubicRegionBallEmbedding d F root n)
        (nextVertex s) =
      nextVertex (liftCubicRegionBallState d F root n s) := by
  classical
  unfold nextVertex
  by_cases hs : s.frontier.Nonempty
  · have hlift : (liftCubicRegionBallState d F root n s).frontier.Nonempty := by
      simpa [liftCubicRegionBallState] using
        (Finset.Nonempty.map (f := cubicRegionBallEmbedding d F root n) hs)
    rw [dif_pos hs, dif_pos hlift, Option.map_some]
    apply congrArg some
    symm
    apply (Finset.min'_eq_iff _ _ _).mpr
    constructor
    · exact Finset.mem_map.mpr ⟨s.frontier.min' hs, s.frontier.min'_mem hs, rfl⟩
    · intro z hz
      obtain ⟨z', hz', rfl⟩ := Finset.mem_map.mp hz
      exact s.frontier.min'_le z' hz'
  · have hempty : s.frontier = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    have hliftEmpty : (liftCubicRegionBallState d F root n s).frontier = ∅ := by
      simp [liftCubicRegionBallState, hempty]
    rw [dif_neg hs, dif_neg (by simp [hliftEmpty])]
    rfl

/-- For positive radius, the finite-ball and ambient rooted explorations have the same lifted
initial state. -/
theorem lift_cubicRegionBallSiteExploration_initial_eq
    (d : ℕ) (F : Set (Cubic d)) [LinearOrder F] (root : F) {n : ℕ} (hn : 0 < n) :
    liftCubicRegionBallState d F root n
        (cubicRegionBallSiteExploration d F root n).initial =
      (cubicRegionSiteExploration d F root).initial := by
  classical
  apply SiteExplorationState.ext
  · ext z
    simp [liftCubicRegionBallState, cubicRegionBallSiteExploration,
      cubicRegionSiteExploration, rootedSiteExploration, cubicRegionBallEmbedding,
      cubicRegionBallRoot]
  · simp [liftCubicRegionBallState, cubicRegionBallSiteExploration,
      cubicRegionSiteExploration, rootedSiteExploration]
  · ext z
    simp only [liftCubicRegionBallState, cubicRegionBallSiteExploration,
      cubicRegionSiteExploration, rootedSiteExploration, Finset.mem_map,
      mem_cubicRegionNeighborFinset_iff, cubicRegionBallEmbedding]
    constructor
    · rintro ⟨z', hzAdj, rfl⟩
      exact SimpleGraph.induce_adj.mp
        (mem_cubicRegionBallNeighborFinset_iff.mp hzAdj)
    · intro hzAdj
      have hadj : (cubicGraph d).Adj (root : Cubic d) (z : Cubic d) :=
        SimpleGraph.induce_adj.mp hzAdj
      obtain ⟨a, ha⟩ := (cubicGraph_adj_iff_exists_stepFrom _ _).mp hadj
      have hzBall : z ∈ cubicRegionMetricBall d F root n := by
        rw [mem_cubicRegionMetricBall_iff, ha, cubicL1Dist_stepFrom]
        omega
      exact ⟨⟨z, hzBall⟩,
        mem_cubicRegionBallNeighborFinset_iff.mpr
          (SimpleGraph.induce_adj.mpr hzAdj), rfl⟩
  · simp [liftCubicRegionBallState, cubicRegionBallSiteExploration,
      cubicRegionSiteExploration, rootedSiteExploration,
      AdaptiveSiteExploration.mapDecisionHistory,
      cubicRegionBallRoot, cubicRegionBallEmbedding]

/-- Restriction of an ambient adaptive answer to finite-ball vertices and histories. -/
def cubicRegionBallAdaptiveAnswer
    {Omega : Type*} (d : ℕ) (F : Set (Cubic d)) (root : F) (n : ℕ)
    (answer : Omega → List (F × Bool) → F → Bool) :
    Omega →
      List ({v : F // v ∈ cubicRegionMetricBall d F root n} × Bool) →
      {v : F // v ∈ cubicRegionMetricBall d F root n} → Bool :=
  AdaptiveSiteExploration.pullbackAdaptiveAnswer
    (cubicRegionBallEmbedding d F root n) answer

/-- As long as neither the old nor new finite state has hit the boundary target, one adaptive
step commutes exactly with lifting to the ambient region. -/
theorem lift_cubicRegionBall_step_eq_of_not_hitsTarget
    {Omega : Type*} (d : ℕ) (F : Set (Cubic d)) [LinearOrder F]
    (root : F) (n : ℕ)
    (answer : Omega → List (F × Bool) → F → Bool) (omega : Omega)
    (s : SiteExplorationState {v : F // v ∈ cubicRegionMetricBall d F root n})
    (hafter : Disjoint (cubicRegionBallTarget d F root n)
      ((cubicRegionBallSiteExploration d F root n).toAdaptive.step
        (cubicRegionBallAdaptiveAnswer d F root n answer omega) s).occupied) :
    liftCubicRegionBallState d F root n
        ((cubicRegionBallSiteExploration d F root n).toAdaptive.step
          (cubicRegionBallAdaptiveAnswer d F root n answer omega) s) =
      (cubicRegionSiteExploration d F root).toAdaptive.step
        (answer omega) (liftCubicRegionBallState d F root n s) := by
  classical
  let Esmall := cubicRegionBallSiteExploration d F root n
  let Elarge := cubicRegionSiteExploration d F root
  let smallAnswer := cubicRegionBallAdaptiveAnswer d F root n answer omega
  have hnext := nextVertex_liftCubicRegionBallState (d := d) (F := F)
    (root := root) (n := n) s
  cases hq : nextVertex s with
  | none =>
      have hqLarge : nextVertex (liftCubicRegionBallState d F root n s) = none := by
        rw [← hnext, hq]
        rfl
      simp [AdaptiveSiteExploration.step, hq, hqLarge]
  | some v =>
      have hqLarge : nextVertex (liftCubicRegionBallState d F root n s) = some (v : F) := by
        rw [← hnext, hq]
        rfl
      by_cases hvAnswer : smallAnswer s.history v = true
      · have hvNewOccupied : v ∈
            (Esmall.toAdaptive.step smallAnswer s).occupied := by
          simp [AdaptiveSiteExploration.step, Esmall, hq, hvAnswer]
        have hvNotTarget : v ∉ cubicRegionBallTarget d F root n := by
          exact fun hvTarget ↦ Finset.disjoint_left.mp hafter hvTarget hvNewOccupied
        have hvDistNe :
            cubicL1Dist (root : Cubic d) (v : Cubic d) ≠ n := by
          intro hvEq
          apply hvNotTarget
          rw [cubicRegionBallTarget, mem_finsetTargetSubtype_iff,
            mem_cubicRegionMetricSphere_iff]
          exact hvEq
        have hvDistLt : cubicL1Dist (root : Cubic d) (v : Cubic d) < n := by
          have hvLe := mem_cubicRegionMetricBall_iff.mp v.property
          omega
        have hneighbors := map_cubicRegionBallNeighborFinset_eq_of_lt v hvDistLt
        have hvAnswerLarge :
            answer omega (liftCubicRegionBallState d F root n s).history (v : F) = true := by
          simpa [smallAnswer, cubicRegionBallAdaptiveAnswer,
            AdaptiveSiteExploration.pullbackAdaptiveAnswer,
            liftCubicRegionBallState] using hvAnswer
        have hsmallStep : Esmall.toAdaptive.step smallAnswer s =
            { occupied := insert v s.occupied
              rejected := s.rejected
              frontier :=
                (s.frontier.erase v ∪ Esmall.toAdaptive.neighbors v) \
                  (insert v s.occupied ∪ s.rejected)
              history := s.history ++ [(v, true)] } := by
          simp [AdaptiveSiteExploration.step, hq, hvAnswer]
        have hlargeStep : Elarge.toAdaptive.step (answer omega)
              (liftCubicRegionBallState d F root n s) =
            { occupied := insert (v : F)
                (liftCubicRegionBallState d F root n s).occupied
              rejected := (liftCubicRegionBallState d F root n s).rejected
              frontier :=
                ((liftCubicRegionBallState d F root n s).frontier.erase (v : F) ∪
                    Elarge.toAdaptive.neighbors (v : F)) \
                  (insert (v : F)
                    (liftCubicRegionBallState d F root n s).occupied ∪
                    (liftCubicRegionBallState d F root n s).rejected)
              history := (liftCubicRegionBallState d F root n s).history ++
                [((v : F), true)] } := by
          simp [AdaptiveSiteExploration.step, hqLarge, hvAnswerLarge]
        change liftCubicRegionBallState d F root n
            (Esmall.toAdaptive.step smallAnswer s) =
          Elarge.toAdaptive.step (answer omega)
            (liftCubicRegionBallState d F root n s)
        rw [hsmallStep, hlargeStep]
        apply SiteExplorationState.ext
        · simp [liftCubicRegionBallState, cubicRegionBallEmbedding]
        · simp [liftCubicRegionBallState, cubicRegionBallEmbedding]
        · change Finset.map (cubicRegionBallEmbedding d F root n)
              ((s.frontier.erase v ∪ Esmall.toAdaptive.neighbors v) \
                (insert v s.occupied ∪ s.rejected)) = _
          rw [Finset.map_sdiff, Finset.map_union, Finset.map_erase,
            Finset.map_union, Finset.map_insert]
          change
            ((Finset.map (cubicRegionBallEmbedding d F root n) s.frontier).erase (v : F) ∪
                Finset.map (cubicRegionBallEmbedding d F root n)
                  (Esmall.toAdaptive.neighbors v)) \
              (insert (v : F)
                (Finset.map (cubicRegionBallEmbedding d F root n) s.occupied) ∪
                Finset.map (cubicRegionBallEmbedding d F root n) s.rejected) =
            ((Finset.map (cubicRegionBallEmbedding d F root n) s.frontier).erase (v : F) ∪
                Elarge.toAdaptive.neighbors (v : F)) \
              (insert (v : F)
                (Finset.map (cubicRegionBallEmbedding d F root n) s.occupied) ∪
                Finset.map (cubicRegionBallEmbedding d F root n) s.rejected)
          rw [show Finset.map (cubicRegionBallEmbedding d F root n)
                (Esmall.toAdaptive.neighbors v) =
              Elarge.toAdaptive.neighbors (v : F) by
            simpa [Esmall, Elarge, cubicRegionBallSiteExploration,
              cubicRegionSiteExploration, rootedSiteExploration,
              SiteExploration.toAdaptive] using hneighbors]
        · change AdaptiveSiteExploration.mapDecisionHistory
              (cubicRegionBallEmbedding d F root n) (s.history ++ [(v, true)]) =
            AdaptiveSiteExploration.mapDecisionHistory
                (cubicRegionBallEmbedding d F root n) s.history ++ [((v : F), true)]
          simp
      · have hvAnswerFalse : smallAnswer s.history v = false := by
          cases h : smallAnswer s.history v <;> simp_all
        have hvAnswerLarge :
            answer omega (liftCubicRegionBallState d F root n s).history (v : F) = false := by
          simpa [smallAnswer, cubicRegionBallAdaptiveAnswer,
            AdaptiveSiteExploration.pullbackAdaptiveAnswer,
            liftCubicRegionBallState] using hvAnswerFalse
        have hsmallStep : Esmall.toAdaptive.step smallAnswer s =
            { occupied := s.occupied
              rejected := insert v s.rejected
              frontier := s.frontier.erase v
              history := s.history ++ [(v, false)] } := by
          simp [AdaptiveSiteExploration.step, hq, hvAnswerFalse]
        have hlargeStep : Elarge.toAdaptive.step (answer omega)
              (liftCubicRegionBallState d F root n s) =
            { occupied := (liftCubicRegionBallState d F root n s).occupied
              rejected := insert (v : F)
                (liftCubicRegionBallState d F root n s).rejected
              frontier :=
                (liftCubicRegionBallState d F root n s).frontier.erase (v : F)
              history := (liftCubicRegionBallState d F root n s).history ++
                [((v : F), false)] } := by
          simp [AdaptiveSiteExploration.step, hqLarge, hvAnswerLarge]
        change liftCubicRegionBallState d F root n
            (Esmall.toAdaptive.step smallAnswer s) =
          Elarge.toAdaptive.step (answer omega)
            (liftCubicRegionBallState d F root n s)
        rw [hsmallStep, hlargeStep]
        apply SiteExplorationState.ext
        · simp [liftCubicRegionBallState, cubicRegionBallEmbedding]
        · simp [liftCubicRegionBallState, cubicRegionBallEmbedding]
        · simp [liftCubicRegionBallState, cubicRegionBallEmbedding]
        · change AdaptiveSiteExploration.mapDecisionHistory
              (cubicRegionBallEmbedding d F root n) (s.history ++ [(v, false)]) =
            AdaptiveSiteExploration.mapDecisionHistory
                (cubicRegionBallEmbedding d F root n) s.history ++ [((v : F), false)]
          simp

/-- The occupied field of an adaptive step depends only on the next query and its Boolean
answer, not on the neighbor update. -/
theorem AdaptiveSiteExploration.step_occupied_eq
    {V : Type*} [DecidableEq V] [LinearOrder V]
    (E : AdaptiveSiteExploration V)
    (answer : List (V × Bool) → V → Bool) (s : SiteExplorationState V) :
    (E.step answer s).occupied =
      match nextVertex s with
      | none => s.occupied
      | some v => if answer s.history v then insert v s.occupied else s.occupied := by
  classical
  unfold AdaptiveSiteExploration.step
  split
  · simp_all
  · split <;> simp_all

/-- The occupied field of one finite-ball step always lifts to the occupied field of the
corresponding ambient step.  Boundary-neighbor discrepancies affect only the frontier, after the
boundary vertex has already been accepted. -/
theorem map_cubicRegionBall_step_occupied_eq
    {Omega : Type*} (d : ℕ) (F : Set (Cubic d)) [LinearOrder F]
    (root : F) (n : ℕ)
    (answer : Omega → List (F × Bool) → F → Bool) (omega : Omega)
    (s : SiteExplorationState {v : F // v ∈ cubicRegionMetricBall d F root n}) :
    ((cubicRegionBallSiteExploration d F root n).toAdaptive.step
        (cubicRegionBallAdaptiveAnswer d F root n answer omega) s).occupied.map
        (cubicRegionBallEmbedding d F root n) =
      ((cubicRegionSiteExploration d F root).toAdaptive.step
        (answer omega) (liftCubicRegionBallState d F root n s)).occupied := by
  classical
  let smallAnswer := cubicRegionBallAdaptiveAnswer d F root n answer omega
  change (((cubicRegionBallSiteExploration d F root n).toAdaptive.step
      smallAnswer s).occupied.map (cubicRegionBallEmbedding d F root n)) = _
  have hnext := nextVertex_liftCubicRegionBallState (d := d) (F := F)
    (root := root) (n := n) s
  cases hq : nextVertex s with
  | none =>
      have hqLarge : nextVertex (liftCubicRegionBallState d F root n s) = none := by
        rw [← hnext, hq]
        rfl
      rw [AdaptiveSiteExploration.step_occupied_eq,
        AdaptiveSiteExploration.step_occupied_eq, hq, hqLarge]
      rfl
  | some v =>
      have hqLarge : nextVertex (liftCubicRegionBallState d F root n s) = some (v : F) := by
        rw [← hnext, hq]
        rfl
      cases hbit : smallAnswer s.history v with
      | false =>
          have hbitLarge :
              answer omega (liftCubicRegionBallState d F root n s).history (v : F) = false := by
            simpa [smallAnswer, cubicRegionBallAdaptiveAnswer,
              AdaptiveSiteExploration.pullbackAdaptiveAnswer,
              liftCubicRegionBallState] using hbit
          have hbitLargeMap :
              answer omega
                (AdaptiveSiteExploration.mapDecisionHistory
                  (cubicRegionBallEmbedding d F root n) s.history) (v : F) = false := by
            simpa [liftCubicRegionBallState] using hbitLarge
          rw [AdaptiveSiteExploration.step_occupied_eq,
            AdaptiveSiteExploration.step_occupied_eq, hq, hqLarge]
          simp [hbit, hbitLargeMap, liftCubicRegionBallState]
      | true =>
          have hbitLarge :
              answer omega (liftCubicRegionBallState d F root n s).history (v : F) = true := by
            simpa [smallAnswer, cubicRegionBallAdaptiveAnswer,
              AdaptiveSiteExploration.pullbackAdaptiveAnswer,
              liftCubicRegionBallState] using hbit
          have hbitLargeMap :
              answer omega
                (AdaptiveSiteExploration.mapDecisionHistory
                  (cubicRegionBallEmbedding d F root n) s.history) (v : F) = true := by
            simpa [liftCubicRegionBallState] using hbitLarge
          rw [AdaptiveSiteExploration.step_occupied_eq,
            AdaptiveSiteExploration.step_occupied_eq, hq, hqLarge]
          simp [hbit, hbitLargeMap, liftCubicRegionBallState]

/-- At every finite time, either the ambient exploration has already hit the radius-`n` sphere,
or its state is exactly the lift of the finite-ball state. -/
theorem cubicRegionBall_hit_or_stateAfter_lift_eq
    {Omega : Type*} (d : ℕ) (F : Set (Cubic d)) [LinearOrder F]
    (root : F) {n : ℕ} (hn : 0 < n)
    (answer : Omega → List (F × Bool) → F → Bool) (omega : Omega) :
    ∀ k,
      (∃ t ∈ cubicRegionMetricSphere d F root n,
        t ∈ (cubicRegionSiteExploration d F root).toAdaptive.occupiedLimit
          (answer omega)) ∨
      liftCubicRegionBallState d F root n
          ((cubicRegionBallSiteExploration d F root n).toAdaptive.stateAfter
            (cubicRegionBallAdaptiveAnswer d F root n answer omega) k) =
        (cubicRegionSiteExploration d F root).toAdaptive.stateAfter
          (answer omega) k := by
  intro k
  induction k with
  | zero =>
      right
      exact lift_cubicRegionBallSiteExploration_initial_eq d F root hn
  | succ k ih =>
      rcases ih with hhit | hstate
      · exact Or.inl hhit
      · let s := (cubicRegionBallSiteExploration d F root n).toAdaptive.stateAfter
          (cubicRegionBallAdaptiveAnswer d F root n answer omega) k
        let sNext := (cubicRegionBallSiteExploration d F root n).toAdaptive.step
          (cubicRegionBallAdaptiveAnswer d F root n answer omega) s
        have hocc := map_cubicRegionBall_step_occupied_eq d F root n answer omega s
        by_cases htarget : ∃ t ∈ cubicRegionBallTarget d F root n, t ∈ sNext.occupied
        · left
          obtain ⟨t, htTarget, htOccupied⟩ := htarget
          refine ⟨(t : F), ?_, ?_⟩
          · exact mem_finsetTargetSubtype_iff.mp htTarget
          · refine ⟨k + 1, ?_⟩
            change (t : F) ∈
              ((cubicRegionSiteExploration d F root).toAdaptive.step
                (answer omega)
                ((cubicRegionSiteExploration d F root).toAdaptive.stateAfter
                  (answer omega) k)).occupied
            rw [← hstate]
            rw [← hocc]
            exact Finset.mem_map.mpr ⟨t, htOccupied, rfl⟩
        · right
          have hdisjoint : Disjoint (cubicRegionBallTarget d F root n) sNext.occupied := by
            rw [Finset.disjoint_left]
            intro t htTarget htOccupied
            exact htarget ⟨t, htTarget, htOccupied⟩
          change liftCubicRegionBallState d F root n sNext =
            (cubicRegionSiteExploration d F root).toAdaptive.step
              (answer omega)
              ((cubicRegionSiteExploration d F root).toAdaptive.stateAfter
                (answer omega) k)
          rw [← hstate]
          exact lift_cubicRegionBall_step_eq_of_not_hitsTarget
            d F root n answer omega s hdisjoint

/-- A finite-ball adaptive boundary hit is also an ambient occupied-limit boundary hit. -/
theorem cubicRegionBall_adaptiveLimitTargetHitEvent_subset
    {Omega : Type*} (d : ℕ) (F : Set (Cubic d)) [LinearOrder F]
    (root : F) (n : ℕ)
    (answer : Omega → List (F × Bool) → F → Bool) :
    (cubicRegionBallSiteExploration d F root n).adaptiveLimitTargetHitEvent
        (cubicRegionBallAdaptiveAnswer d F root n answer)
        (cubicRegionBallTarget d F root n) ⊆
      (cubicRegionSiteExploration d F root).adaptiveLimitTargetHitEvent
        answer (cubicRegionMetricSphere d F root n) := by
  intro omega hhit
  by_cases hn : n = 0
  · subst n
    refine ⟨root, by simp [mem_cubicRegionMetricSphere_iff], ?_⟩
    exact ⟨0, by simp [AdaptiveSiteExploration.stateAfter,
      cubicRegionSiteExploration, rootedSiteExploration, SiteExploration.toAdaptive]⟩
  · have hnPos : 0 < n := Nat.pos_of_ne_zero hn
    obtain ⟨t, htTarget, kt, htOccupied⟩ := hhit
    rcases cubicRegionBall_hit_or_stateAfter_lift_eq d F root hnPos answer omega kt with
      hAmbient | hstate
    · exact hAmbient
    · refine ⟨(t : F), mem_finsetTargetSubtype_iff.mp htTarget, ?_⟩
      refine ⟨kt, ?_⟩
      rw [← hstate]
      exact Finset.mem_map.mpr ⟨t, htOccupied, rfl⟩
end SiteExploration

end Percolation
