import Percolation.Critical.AdaptiveBallCompatibility

/-!
# Grimmett Lemma 7.24: adaptive supercritical site exploration

Every measurable history-dependent query succeeds with conditional probability at least a
supercritical iid site density, expressed by a ratio-free inequality on exact finite histories.
Finite Bellman comparison on successive metric balls, compatibility with the ambient exploration,
and exhaustion over Manhattan spheres then give an infinite occupied component with positive
probability.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory Classical
open scoped unitInterval

namespace SiteExploration

/-- The initial history of the finite-ball rooted exploration maps to the initial history of the
ambient rooted region exploration. -/
theorem mapDecisionHistory_cubicRegionBall_initial
    (d : ℕ) (F : Set (Cubic d)) [LinearOrder F] (root : F) (n : ℕ) :
    AdaptiveSiteExploration.mapDecisionHistory
        (cubicRegionBallEmbedding d F root n)
        (cubicRegionBallSiteExploration d F root n).initial.history =
      (cubicRegionSiteExploration d F root).initial.history := by
  simp [cubicRegionBallSiteExploration, cubicRegionSiteExploration,
    rootedSiteExploration, AdaptiveSiteExploration.mapDecisionHistory,
    cubicRegionBallRoot]

/-- The finite-ball Bellman comparison, transported to the ambient adaptive sphere-hit event. -/
theorem finiteBallHitsSphere_probability_le_cubicRegion_adaptiveLimitSphereHit
    {Omega : Type*} [MeasurableSpace Omega]
    (d : ℕ) (F : Set (Cubic d)) [LinearOrder F] (root : F)
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    {answer : Omega → List (F × Bool) → F → Bool}
    (hanswer : AdaptiveSiteExploration.MeasurableAnswer answer)
    (q : I)
    (hlower : AdaptiveSiteExploration.HasAdaptiveAnswerLowerBoundOn mu
      (prefixedAdaptiveAnswer
        (cubicRegionSiteExploration d F root).initial.history answer)
      (fun _ _ ↦ True) (q : ℝ))
    (n : ℕ) :
    finiteBernoulliProbability Finset.univ (q : ℝ)
        (finiteSiteHitsTarget
          ((cubicRegionGraph d F).induce
            (cubicRegionMetricBall d F root n : Set F))
          (cubicRegionBallRoot d F root n)
          (cubicRegionBallTarget d F root n)) ≤
      mu.real ((cubicRegionSiteExploration d F root).adaptiveLimitTargetHitEvent
        answer (cubicRegionMetricSphere d F root n)) := by
  let f := cubicRegionBallEmbedding d F root n
  let smallAnswer := cubicRegionBallAdaptiveAnswer d F root n answer
  have hsmallAnswer : AdaptiveSiteExploration.MeasurableAnswer smallAnswer :=
    AdaptiveSiteExploration.measurableAnswer_pullbackAdaptiveAnswer hanswer f
  have hpull := hlower.pullback f
  have hprefix := prefixedAdaptiveAnswer_pullback f
    (cubicRegionBallSiteExploration d F root n).initial.history
    (cubicRegionSiteExploration d F root).initial.history
    (mapDecisionHistory_cubicRegionBall_initial d F root n) answer
  have hsmallLower : AdaptiveSiteExploration.HasAdaptiveAnswerLowerBoundOn mu
      (prefixedAdaptiveAnswer
        (cubicRegionBallSiteExploration d F root n).initial.history smallAnswer)
      (fun _ _ ↦ True) (q : ℝ) := by
    change AdaptiveSiteExploration.HasAdaptiveAnswerLowerBoundOn mu
      (prefixedAdaptiveAnswer
        (cubicRegionBallSiteExploration d F root n).initial.history
        (AdaptiveSiteExploration.pullbackAdaptiveAnswer f answer))
      (fun _ _ ↦ True) (q : ℝ)
    rw [hprefix]
    exact hpull
  have hfinite := finiteSiteHitsTarget_probability_le_adaptiveLimitTargetHitEvent
    ((cubicRegionGraph d F).induce
      (cubicRegionMetricBall d F root n : Set F))
    (cubicRegionBallNeighborFinset d F root n)
    mem_cubicRegionBallNeighborFinset_iff
    mu hsmallAnswer (fun _ _ ↦ True) (q : ℝ) q.2.1 q.2.2
    (cubicRegionBallRoot d F root n) hsmallLower
    (cubicRegionBallTarget d F root n) (fun _ ↦ trivial)
  calc
    finiteBernoulliProbability Finset.univ (q : ℝ)
        (finiteSiteHitsTarget
          ((cubicRegionGraph d F).induce
            (cubicRegionMetricBall d F root n : Set F))
          (cubicRegionBallRoot d F root n)
          (cubicRegionBallTarget d F root n)) ≤
        mu.real ((cubicRegionBallSiteExploration d F root n).adaptiveLimitTargetHitEvent
          smallAnswer (cubicRegionBallTarget d F root n)) := by
      simpa [cubicRegionBallSiteExploration, smallAnswer] using hfinite
    _ ≤ mu.real ((cubicRegionSiteExploration d F root).adaptiveLimitTargetHitEvent
        answer (cubicRegionMetricSphere d F root n)) :=
      measureReal_mono
        (cubicRegionBall_adaptiveLimitTargetHitEvent_subset d F root n answer)

/-- **Grimmett Lemma 7.24.**  On a connected cubic region, uniform ratio-free history-wise
success bounds at a density strictly above the site's critical probability force the rooted
adaptive exploration to have an infinite occupied set with positive probability. -/
theorem cubicRegionSiteExploration_infinite_probability_pos_of_adaptiveLowerBound
    {Omega : Type*} [MeasurableSpace Omega]
    (d : ℕ) (F : Set (Cubic d)) [LinearOrder F] (root : F)
    (hF : (cubicRegionGraph d F).Connected)
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (q : I) (hq : siteCriticalProbability (cubicRegionGraph d F) < (q : ℝ))
    {answer : Omega → List (F × Bool) → F → Bool}
    (hanswer : AdaptiveSiteExploration.MeasurableAnswer answer)
    (hlower : AdaptiveSiteExploration.HasAdaptiveAnswerLowerBoundOn mu
      (prefixedAdaptiveAnswer
        (cubicRegionSiteExploration d F root).initial.history answer)
      (fun _ _ ↦ True) (q : ℝ)) :
    0 < mu.real {omega |
      ((cubicRegionSiteExploration d F root).toAdaptive.occupiedLimit
        (answer omega)).Infinite} := by
  obtain ⟨c, hc, hcFinite⟩ :=
    exists_pos_forall_finiteBallHitsSphere_of_connected_of_criticalProbability_lt
      d F root hF q hq
  have hcSphere : ∀ n,
      c ≤ mu.real ((cubicRegionSiteExploration d F root).adaptiveLimitTargetHitEvent
        answer (cubicRegionMetricSphere d F root n)) := by
    intro n
    exact (hcFinite n).trans
      (finiteBallHitsSphere_probability_le_cubicRegion_adaptiveLimitSphereHit
        d F root mu hanswer q hlower n)
  exact hc.trans_le
    (cubicRegion_occupiedLimit_infinite_probability_ge_of_sphere_lowerBounds
      d F root mu hanswer c hcSphere)

/-- Connected-cluster formulation of Lemma 7.24. -/
theorem cubicRegionSiteExploration_hasInfiniteSiteCluster_probability_pos_of_adaptiveLowerBound
    {Omega : Type*} [MeasurableSpace Omega]
    (d : ℕ) (F : Set (Cubic d)) [LinearOrder F] (root : F)
    (hF : (cubicRegionGraph d F).Connected)
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (q : I) (hq : siteCriticalProbability (cubicRegionGraph d F) < (q : ℝ))
    {answer : Omega → List (F × Bool) → F → Bool}
    (hanswer : AdaptiveSiteExploration.MeasurableAnswer answer)
    (hlower : AdaptiveSiteExploration.HasAdaptiveAnswerLowerBoundOn mu
      (prefixedAdaptiveAnswer
        (cubicRegionSiteExploration d F root).initial.history answer)
      (fun _ _ ↦ True) (q : ℝ)) :
    0 < mu.real {omega |
      hasInfiniteSiteCluster (cubicRegionGraph d F)
        ((cubicRegionSiteExploration d F root).toAdaptive.occupiedLimit
          (answer omega))} := by
  have hInfinite :=
    cubicRegionSiteExploration_infinite_probability_pos_of_adaptiveLowerBound
      d F root hF mu q hq hanswer hlower
  exact hInfinite.trans_le <| measureReal_mono fun omega homega ↦
    (cubicRegionSiteExploration d F root).toAdaptive
      |>.hasInfiniteSiteCluster_occupiedLimit_of_infinite
        (answer omega) root
        (by simpa [SiteExploration.toAdaptive] using
          cubicRegionSiteExploration_initial_openRootedAt d F root)
        homega

end SiteExploration

end Percolation
