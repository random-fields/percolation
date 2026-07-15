import Percolation.Critical.AdaptiveBallCompatibility
import Percolation.Critical.FiniteInducedBond

/-!
# Infinite-volume bond-to-site comparison on cubic regions

The finite incoming-dart comparison is applied on successive induced metric balls.  Exact root
factors and the bond/site shell exhaustion then show that bond percolation at density `p` forces
site percolation at density `1 - (1-p)^(2d)`.  In particular, every connected cubic region with
bond critical probability below one has site critical probability below one, which is the
comparison input required by Grimmett's dynamic renormalization construction.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory Classical
open scoped unitInterval

namespace IncomingGreenDomination

/-- Endpoint-safe unit-interval form of the incoming-green density. -/
def densityI (p : I) (Delta : ℕ) : I :=
  ⟨density p Delta, density_nonneg p Delta, density_le_one p Delta⟩

@[simp]
theorem coe_densityI (p : I) (Delta : ℕ) :
    (densityI p Delta : ℝ) = density p Delta :=
  rfl

theorem density_pos {p : I} {Delta : ℕ}
    (hp : 0 < (p : ℝ)) (hDelta : 0 < Delta) :
    0 < density p Delta := by
  unfold density
  apply sub_pos.mpr
  apply pow_lt_one₀ (unitInterval.one_minus_nonneg p)
  · linarith
  · omega

theorem density_lt_one {p : I} {Delta : ℕ}
    (hp : (p : ℝ) < 1) :
    density p Delta < 1 := by
  unfold density
  have hbase : 0 < 1 - (p : ℝ) := sub_pos.mpr hp
  nlinarith [pow_pos hbase Delta]

end IncomingGreenDomination

/-- Every neighbor in a finite induced cubic-region ball determines a unique signed coordinate
direction. -/
noncomputable def cubicRegionBallNeighborDirectionEmbedding
    {d : ℕ} {F : Set (Cubic d)} {root : F} {n : ℕ}
    (u : {v : F // v ∈ cubicRegionMetricBall d F root n}) :
    (CubicRegionBallGraph d F root n).neighborSet u ↪ CubicDirection d where
  toFun v := Classical.choose <|
    (cubicGraph_adj_iff_exists_stepFrom
      (cubicRegionBallVertexVal u) (cubicRegionBallVertexVal v.1)).mp <| by
        exact (cubicRegionBallToCubicHom d F root n).map_rel v.2
  inj' := by
    intro v w hvw
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    have hv := Classical.choose_spec <|
      (cubicGraph_adj_iff_exists_stepFrom
        (cubicRegionBallVertexVal u) (cubicRegionBallVertexVal v.1)).mp <| by
          exact (cubicRegionBallToCubicHom d F root n).map_rel v.2
    have hw := Classical.choose_spec <|
      (cubicGraph_adj_iff_exists_stepFrom
        (cubicRegionBallVertexVal u) (cubicRegionBallVertexVal w.1)).mp <| by
          exact (cubicRegionBallToCubicHom d F root n).map_rel w.2
    exact hv.trans ((congrArg (cubicStepFrom (cubicRegionBallVertexVal u)) hvw).trans hw.symm)

/-- Every finite induced cubic-region ball has degree at most `2d`. -/
theorem cubicRegionBallGraph_degree_le_two_mul
    {d : ℕ} {F : Set (Cubic d)} {root : F} {n : ℕ}
    (u : {v : F // v ∈ cubicRegionMetricBall d F root n}) :
    (CubicRegionBallGraph d F root n).degree u ≤ 2 * d := by
  classical
  calc
    (CubicRegionBallGraph d F root n).degree u =
        Fintype.card ((CubicRegionBallGraph d F root n).neighborSet u) :=
      ((CubicRegionBallGraph d F root n).card_neighborSet_eq_degree u).symm
    _ ≤ Fintype.card (CubicDirection d) :=
      Fintype.card_le_of_injective (cubicRegionBallNeighborDirectionEmbedding u)
        (cubicRegionBallNeighborDirectionEmbedding u).injective
    _ = 2 * d := by simp [Fintype.card_prod, Nat.mul_comm]

/-- Pointwise infinite-volume comparison.  If a connected region percolates in bonds at `p`,
then it percolates in sites at the incoming-green density `1 - (1-p)^(2d)`. -/
theorem siteTheta_densityI_pos_of_regionCriticalProbability_lt
    {d : ℕ} {F : Set (Cubic d)} (root : F)
    (hd : 2 ≤ d) (hF : (cubicRegionGraph d F).Connected)
    (p : I) (hp : regionCriticalProbability d F < (p : ℝ)) :
    0 < siteTheta (cubicRegionGraph d F)
      (IncomingGreenDomination.densityI p (2 * d)) := by
  classical
  let Delta := 2 * d
  let q : I := IncomingGreenDomination.densityI p Delta
  let thetaRoot := regionThetaFrom d F p (root : Cubic d)
  have hp0 : 0 < (p : ℝ) :=
    (regionCriticalProbability_nonneg d F).trans_lt hp
  have hDelta : 0 < Delta := by simp [Delta]; omega
  have hqpos : 0 < (q : ℝ) := by
    exact IncomingGreenDomination.density_pos hp0 hDelta
  have htheta : 0 < thetaRoot := by
    exact regionThetaFrom_pos_of_critical_lt_of_connected hF hp root.2
  have hshellBond (n : ℕ) :
      thetaRoot ≤
        setBer((Set.univ : Set (Sym2 {v : F //
          v ∈ cubicRegionMetricBall d F root n})), p).real
          (IncomingGreenDomination.bondHitsTargetEvent
            (CubicRegionBallGraph d F root n)
            (cubicRegionBallRoot d F root n)
            (cubicRegionBallTarget d F root n)) := by
    calc
      thetaRoot ≤ (bernoulliBondMeasure d p).real
          (cubicRegionBondConnectionToSphereEvent d F root n) :=
        measureReal_mono
          (regionInfiniteClusterEvent_subset_cubicRegionBondConnectionToSphereEvent
            d F root n)
      _ = _ :=
        (setBernoulli_real_finiteRegionBall_bondHitsTarget_eq_ambient
          d F root n p).symm
  have hfiniteSite (n : ℕ) :
      (q : ℝ) * thetaRoot ≤
        finiteBernoulliProbability Finset.univ (q : ℝ)
          (SiteExploration.finiteSiteHitsTarget
            (CubicRegionBallGraph d F root n)
            (cubicRegionBallRoot d F root n)
            (cubicRegionBallTarget d F root n)) := by
    letI : LinearOrder {v : F // v ∈ cubicRegionMetricBall d F root n} :=
      linearOrderOfSTO WellOrderingRel
    calc
      (q : ℝ) * thetaRoot ≤
          (q : ℝ) *
            setBer((Set.univ : Set (Sym2 {v : F //
              v ∈ cubicRegionMetricBall d F root n})), p).real
              (IncomingGreenDomination.bondHitsTargetEvent
                (CubicRegionBallGraph d F root n)
                (cubicRegionBallRoot d F root n)
                (cubicRegionBallTarget d F root n)) :=
        mul_le_mul_of_nonneg_left (hshellBond n) q.2.1
      _ ≤ _ := by
        simpa [q, Delta] using
          IncomingGreenDomination.density_mul_setBernoulli_bondHitsTarget_le_finiteSiteHitsTarget
            (CubicRegionBallGraph d F root n)
            (SiteExploration.cubicRegionBallNeighborFinset d F root n)
            SiteExploration.mem_cubicRegionBallNeighborFinset_iff
            p (2 * d) cubicRegionBallGraph_degree_le_two_mul
            (cubicRegionBallRoot d F root n)
            (cubicRegionBallTarget d F root n)
  have hrooted : (q : ℝ) * thetaRoot ≤
      setBer((Set.univ : Set F), q).real
        (rootedInfiniteSiteClusterEvent (cubicRegionGraph d F) root) :=
    rootedInfiniteSiteCluster_probability_ge_of_finiteBallHitsSphere_lowerBounds
      d F root q ((q : ℝ) * thetaRoot) hfiniteSite
  have hrootedPos : 0 < setBer((Set.univ : Set F), q).real
      (rootedInfiniteSiteClusterEvent (cubicRegionGraph d F) root) :=
    (mul_pos hqpos htheta).trans_le hrooted
  have hsubset : rootedInfiniteSiteClusterEvent (cubicRegionGraph d F) root ⊆
      {eta | hasInfiniteSiteCluster (cubicRegionGraph d F) eta} := by
    intro eta hroot
    exact ⟨root, hroot⟩
  have hmono :
      setBer((Set.univ : Set F), q).real
          (rootedInfiniteSiteClusterEvent (cubicRegionGraph d F) root) ≤
        setBer((Set.univ : Set F), q).real
          {eta | hasInfiniteSiteCluster (cubicRegionGraph d F) eta} :=
    measureReal_mono hsubset
  exact hrootedPos.trans_le (by simpa [siteTheta, q] using hmono)

/-- The bond-to-site comparison required by the dynamic construction: a connected cubic region
whose bond critical probability is below one also has site critical probability below one. -/
theorem siteCriticalProbability_lt_one_of_regionCriticalProbability_lt_one
    {d : ℕ} {F : Set (Cubic d)} (root : F)
    (hd : 2 ≤ d) (hF : (cubicRegionGraph d F).Connected)
    (hcrit : regionCriticalProbability d F < 1) :
    siteCriticalProbability (cubicRegionGraph d F) < 1 := by
  let c := regionCriticalProbability d F
  let p : I := ⟨(c + 1) / 2, by
    constructor
    · have hc0 := regionCriticalProbability_nonneg d F
      dsimp [c]
      linarith
    · have hc1 := regionCriticalProbability_le_one d F
      dsimp [c]
      linarith⟩
  have hcp : regionCriticalProbability d F < (p : ℝ) := by
    dsimp [p, c]
    linarith
  have hp1 : (p : ℝ) < 1 := by
    dsimp [p, c]
    linarith
  let q : I := IncomingGreenDomination.densityI p (2 * d)
  have hqpos : 0 < siteTheta (cubicRegionGraph d F) q := by
    exact siteTheta_densityI_pos_of_regionCriticalProbability_lt root hd hF p hcp
  have hq1 : (q : ℝ) < 1 := by
    exact IncomingGreenDomination.density_lt_one hp1
  exact (siteCriticalProbability_le_of_siteTheta_pos hqpos).trans_lt hq1

end Percolation
