import Percolation.Bernoulli.FKGInfinite
import Percolation.Critical.Regions

/-!
# Rooted infinite-cluster events for site percolation

The site critical probability in `Regions.lean` is defined through the existence of an infinite
site-open component somewhere in the graph.  Grimmett's exploration argument needs a rooted
positive-probability event.  On a countable graph, positivity of the unrooted event supplies at
least one such root by countable subadditivity.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval

/-- The event that the site-open cluster of `root` is infinite. -/
def rootedInfiniteSiteClusterEvent {V : Type*} (G : SimpleGraph V) (root : V) :
    Set (Set V) :=
  {eta | (siteOpenCluster G eta root).Infinite}

theorem measurableSet_rootedInfiniteSiteClusterEvent
    {V : Type*} [Countable V] (G : SimpleGraph V) (root : V) :
    MeasurableSet (rootedInfiniteSiteClusterEvent G root) := by
  classical
  have hrepr : rootedInfiniteSiteClusterEvent G root =
      ⋂ s : Finset V, ⋃ y : V, ⋃ (_hy : y ∉ s), siteConnectionEvent G root y := by
    ext eta
    simp only [rootedInfiniteSiteClusterEvent, Set.mem_setOf_eq, Set.mem_iInter,
      Set.mem_iUnion]
    constructor
    · intro hinfinite s
      obtain ⟨y, hy, hys⟩ := hinfinite.exists_notMem_finset s
      exact ⟨y, hys, hy⟩
    · intro houtside
      rw [← Set.not_finite]
      intro hfinite
      obtain ⟨y, hys, hy⟩ := houtside hfinite.toFinset
      exact hys (hfinite.mem_toFinset.mpr hy)
  rw [hrepr]
  exact MeasurableSet.iInter fun s ↦
    MeasurableSet.iUnion fun y ↦ MeasurableSet.iUnion fun _hy ↦
      measurableSet_siteConnectionEvent G root y

theorem isIncreasingEvent_rootedInfiniteSiteClusterEvent
    {V : Type*} (G : SimpleGraph V) (root : V) :
    IsIncreasingEvent (rootedInfiniteSiteClusterEvent G root) := by
  intro eta xi hetaXi hInfinite
  exact hInfinite.mono fun y hy ↦
    isIncreasingEvent_siteConnectionEvent G root y hetaXi hy

theorem hasInfiniteSiteCluster_event_eq_iUnion_rooted
    {V : Type*} (G : SimpleGraph V) :
    {eta : Set V | hasInfiniteSiteCluster G eta} =
      ⋃ root : V, rootedInfiniteSiteClusterEvent G root := by
  ext eta
  simp [hasInfiniteSiteCluster, rootedInfiniteSiteClusterEvent]

/-- A positive unrooted infinite-cluster probability on a countable graph has a root whose
infinite site-open cluster has positive probability. -/
theorem exists_root_rootedInfiniteSiteCluster_probability_pos
    {V : Type*} [Countable V] (G : SimpleGraph V) (p : I)
    (hpos : 0 < siteTheta G p) :
    ∃ root : V,
      0 < setBer((Set.univ : Set V), p).real
        (rootedInfiniteSiteClusterEvent G root) := by
  let mu : Measure (Set V) := setBer((Set.univ : Set V), p)
  have hunionReal : 0 < mu.real (⋃ root : V, rootedInfiniteSiteClusterEvent G root) := by
    simpa [mu, siteTheta, hasInfiniteSiteCluster_event_eq_iUnion_rooted G] using hpos
  have hunion : mu (⋃ root : V, rootedInfiniteSiteClusterEvent G root) ≠ 0 := by
    intro hzero
    have : mu.real (⋃ root : V, rootedInfiniteSiteClusterEvent G root) = 0 := by
      simp [measureReal_def, hzero]
    exact (ne_of_gt hunionReal) this
  obtain ⟨root, hroot⟩ := exists_measure_pos_of_not_measure_iUnion_null hunion
  refine ⟨root, ?_⟩
  rw [measureReal_def]
  exact ENNReal.toReal_pos (ne_of_gt hroot) (by finiteness)

/-- Above the site critical probability, at least one root percolates with positive
probability. -/
theorem exists_root_rootedInfiniteSiteCluster_probability_pos_of_criticalProbability_lt
    {V : Type*} [Countable V] (G : SimpleGraph V) (p : I)
    (hp : siteCriticalProbability G < (p : ℝ)) :
    ∃ root : V,
      0 < setBer((Set.univ : Set V), p).real
        (rootedInfiniteSiteClusterEvent G root) :=
  exists_root_rootedInfiniteSiteCluster_probability_pos G p
    (siteTheta_pos_of_criticalProbability_lt hp)

/-- On a connected countable graph, positive unrooted percolation probability gives positive
infinite-cluster probability at every prescribed root.  The finite open path from a root with
positive probability to the prescribed root is joined to the infinite cluster using FKG. -/
theorem rootedInfiniteSiteCluster_probability_pos_of_connected
    {V : Type*} [Countable V] [DecidableEq V]
    {G : SimpleGraph V} (hG : G.Connected) (p : I) (hp0 : 0 < (p : ℝ))
    (hpos : 0 < siteTheta G p) (root : V) :
    0 < setBer((Set.univ : Set V), p).real
      (rootedInfiniteSiteClusterEvent G root) := by
  obtain ⟨x, hx⟩ := exists_root_rootedInfiniteSiteCluster_probability_pos G p hpos
  let w : G.Walk root x := Classical.choice (hG.preconnected root x)
  let pathEvent : Set (Set V) := {eta | (w.support.toFinset : Set V) ⊆ eta}
  have hpathMeas : MeasurableSet pathEvent := by
    simpa [pathEvent] using measurableSet_superset_finset w.support.toFinset
  have hpathInc : IsIncreasingEvent pathEvent := by
    simpa [pathEvent] using isIncreasingEvent_superset (w.support.toFinset : Set V)
  have hpathPos :
      0 < setBer((Set.univ : Set V), p).real pathEvent := by
    rw [show setBer((Set.univ : Set V), p).real pathEvent =
        (p : ℝ) ^ w.support.toFinset.card by
      simpa [pathEvent] using setBernoulli_real_superset_finset_univ w.support.toFinset p]
    positivity
  have hinterLower := setBernoulli_real_fkg p hpathInc
    (isIncreasingEvent_rootedInfiniteSiteClusterEvent G x) hpathMeas
    (measurableSet_rootedInfiniteSiteClusterEvent G x)
  have hinterPos :
      0 < setBer((Set.univ : Set V), p).real
        (pathEvent ∩ rootedInfiniteSiteClusterEvent G x) :=
    (mul_pos hpathPos hx).trans_le hinterLower
  have hinterSubset :
      pathEvent ∩ rootedInfiniteSiteClusterEvent G x ⊆
        rootedInfiniteSiteClusterEvent G root := by
    rintro eta ⟨hpath, hxInfinite⟩
    exact hxInfinite.mono fun y hy ↦ by
      obtain ⟨q, hqOpen⟩ := hy
      refine ⟨w.append q, ?_⟩
      intro z hz
      rw [SimpleGraph.Walk.support_append] at hz
      rcases List.mem_append.mp hz with hz | hz
      · exact hpath (by simpa using hz)
      · exact hqOpen z (List.mem_of_mem_tail hz)
  exact hinterPos.trans_le (measureReal_mono hinterSubset)

/-- Rooted supercritical site percolation on a connected countable graph. -/
theorem rootedInfiniteSiteCluster_probability_pos_of_connected_of_criticalProbability_lt
    {V : Type*} [Countable V] [DecidableEq V]
    {G : SimpleGraph V} (hG : G.Connected) (p : I)
    (hp : siteCriticalProbability G < (p : ℝ)) (root : V) :
    0 < setBer((Set.univ : Set V), p).real
      (rootedInfiniteSiteClusterEvent G root) := by
  have hp0 : 0 < (p : ℝ) :=
    (siteCriticalProbability_nonneg G).trans_lt hp
  exact rootedInfiniteSiteCluster_probability_pos_of_connected hG p hp0
    (siteTheta_pos_of_criticalProbability_lt hp) root

end Percolation
