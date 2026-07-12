import Percolation.Critical.AdaptiveRegionShells
import Percolation.Critical.FiniteInducedSite
import Percolation.Critical.RootedSitePercolation

/-!
# Uniform finite-shell probabilities from rooted site percolation

An infinite site-open cluster at a root must cross every finite Manhattan sphere.  Stopping the
witness walk at its first hit keeps the connection inside the corresponding finite ball.  The
finite induced-graph probability is therefore bounded below by the same rooted infinite-cluster
probability at every radius.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory Classical
open scoped unitInterval

/-- The ambient site event that `root` connects to its radius-`n` sphere without leaving the
radius-`n` ball of the region. -/
def cubicRegionSiteConnectionToSphereEvent
    (d : ℕ) (F : Set (Cubic d)) (root : F) (n : ℕ) : Set (Set F) :=
  {eta | ∃ t ∈ cubicRegionMetricSphere d F root n,
    eta ∈ siteConnectionEventIn (cubicRegionGraph d F)
      (cubicRegionMetricBall d F root n) root t}

theorem measurableSet_cubicRegionSiteConnectionToSphereEvent
    (d : ℕ) (F : Set (Cubic d)) (root : F) (n : ℕ) :
    MeasurableSet (cubicRegionSiteConnectionToSphereEvent d F root n) := by
  classical
  have heq : cubicRegionSiteConnectionToSphereEvent d F root n =
      ⋃ t ∈ cubicRegionMetricSphere d F root n,
        siteConnectionEventIn (cubicRegionGraph d F)
          (cubicRegionMetricBall d F root n) root t := by
    ext eta
    simp [cubicRegionSiteConnectionToSphereEvent]
  rw [heq]
  exact (cubicRegionMetricSphere d F root n).measurableSet_biUnion fun t _ht ↦
    measurableSet_siteConnectionEventIn (cubicRegionGraph d F)
      (cubicRegionMetricBall d F root n) root t

/-- Every rooted infinite site-open cluster supplies a first-hit connection to each finite
Manhattan sphere inside its ball. -/
theorem rootedInfiniteSiteClusterEvent_subset_cubicRegionSiteConnectionToSphereEvent
    (d : ℕ) (F : Set (Cubic d)) (root : F) (n : ℕ) :
    rootedInfiniteSiteClusterEvent (cubicRegionGraph d F) root ⊆
      cubicRegionSiteConnectionToSphereEvent d F root n := by
  intro eta hInfinite
  have hBallFinite : ((cubicRegionMetricBall d F root n : Finset F) : Set F).Finite :=
    (cubicRegionMetricBall d F root n).finite_toSet
  obtain ⟨y, hyCluster, hyNotBall⟩ :=
    hInfinite.exists_notMem_finset (cubicRegionMetricBall d F root n)
  have hyFar : n ≤ cubicL1Dist (root : Cubic d) (y : Cubic d) := by
    have hyNotLe : ¬ cubicL1Dist (root : Cubic d) (y : Cubic d) ≤ n := by
      intro hyLe
      exact hyNotBall (mem_cubicRegionMetricBall_iff.mpr hyLe)
    omega
  obtain ⟨w, hwOpen⟩ := hyCluster
  obtain ⟨z, q, hzSphere, hqBall, hqSupport⟩ :=
    exists_cubicRegionWalk_prefix_to_metricSphere w (by simp) hyFar
  refine ⟨z, hzSphere, q, hqBall, ?_⟩
  intro v hv
  exact hwOpen v (hqSupport v hv)

/-- The finite induced ball and its boundary target used in the radius-`n` Bellman problem. -/
noncomputable def cubicRegionBallTarget
    (d : ℕ) (F : Set (Cubic d)) (root : F) (n : ℕ) :
    Finset {v : F // v ∈ cubicRegionMetricBall d F root n} :=
  finsetTargetSubtype (cubicRegionMetricBall d F root n)
    (cubicRegionMetricSphere d F root n)

/-- The root regarded as a vertex of its finite induced metric ball. -/
def cubicRegionBallRoot
    (d : ℕ) (F : Set (Cubic d)) (root : F) (n : ℕ) :
    {v : F // v ∈ cubicRegionMetricBall d F root n} :=
  ⟨root, mem_cubicRegionMetricBall_iff.mpr (by simp)⟩

/-- At every radius, the finite induced-ball connection probability dominates the probability
that the root has an infinite site-open cluster. -/
theorem rootedInfiniteSiteCluster_probability_le_finiteBallHitsSphere
    (d : ℕ) (F : Set (Cubic d)) (root : F) (n : ℕ) (p : I) :
    setBer((Set.univ : Set F), p).real
        (rootedInfiniteSiteClusterEvent (cubicRegionGraph d F) root) ≤
      finiteBernoulliProbability Finset.univ (p : ℝ)
        (SiteExploration.finiteSiteHitsTarget
          ((cubicRegionGraph d F).induce
            (cubicRegionMetricBall d F root n : Set F))
          (cubicRegionBallRoot d F root n)
          (cubicRegionBallTarget d F root n)) := by
  have hmono : setBer((Set.univ : Set F), p).real
      (rootedInfiniteSiteClusterEvent (cubicRegionGraph d F) root) ≤
      setBer((Set.univ : Set F), p).real
        (cubicRegionSiteConnectionToSphereEvent d F root n) :=
    measureReal_mono
      (rootedInfiniteSiteClusterEvent_subset_cubicRegionSiteConnectionToSphereEvent
        d F root n)
  have heq := finiteBernoulliProbability_induced_siteHitsTarget_eq_ambient
    (cubicRegionGraph d F) (cubicRegionMetricBall d F root n)
      (cubicRegionMetricSphere d F root n) root
      (mem_cubicRegionMetricBall_iff.mpr (by simp)) p
  have heq' :
      finiteBernoulliProbability Finset.univ (p : ℝ)
          (SiteExploration.finiteSiteHitsTarget
            ((cubicRegionGraph d F).induce
              (cubicRegionMetricBall d F root n : Set F))
            (cubicRegionBallRoot d F root n)
            (cubicRegionBallTarget d F root n)) =
        setBer((Set.univ : Set F), p).real
          (cubicRegionSiteConnectionToSphereEvent d F root n) := by
    simpa [cubicRegionBallRoot, cubicRegionBallTarget,
      cubicRegionSiteConnectionToSphereEvent] using heq
  exact hmono.trans_eq heq'.symm

/-- Supercritical site percolation supplies a single positive constant that lower-bounds every
finite metric-ball connection problem rooted at `root`. -/
theorem exists_pos_forall_finiteBallHitsSphere_of_connected_of_criticalProbability_lt
    (d : ℕ) (F : Set (Cubic d)) (root : F)
    (hF : (cubicRegionGraph d F).Connected) (p : I)
    (hp : siteCriticalProbability (cubicRegionGraph d F) < (p : ℝ)) :
    ∃ c : ℝ, 0 < c ∧ ∀ n,
      c ≤ finiteBernoulliProbability Finset.univ (p : ℝ)
        (SiteExploration.finiteSiteHitsTarget
          ((cubicRegionGraph d F).induce
            (cubicRegionMetricBall d F root n : Set F))
          (cubicRegionBallRoot d F root n)
          (cubicRegionBallTarget d F root n)) := by
  let c := setBer((Set.univ : Set F), p).real
    (rootedInfiniteSiteClusterEvent (cubicRegionGraph d F) root)
  have hc : 0 < c :=
    rootedInfiniteSiteCluster_probability_pos_of_connected_of_criticalProbability_lt
      hF p hp root
  exact ⟨c, hc, fun n ↦
    rootedInfiniteSiteCluster_probability_le_finiteBallHitsSphere d F root n p⟩

end Percolation
