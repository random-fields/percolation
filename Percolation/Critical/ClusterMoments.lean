import Percolation.Critical.ConnectedKernel

/-!
# Cluster moments from the tree-graph inequality

This module turns the ordered multipoint estimate into Grimmett's moment bound (6.94).  The
intermediate identity expands a power of the cluster cardinality as a sum over ordered tuples;
it is stated in `ℝ≥0∞`, so infinite clusters and infinite moments retain their correct values.
-/

namespace Percolation

open Set MeasureTheory
open scoped BigOperators ENNReal unitInterval

attribute [local instance] Classical.propDecidable

/-- A finite power of a nonnegative series is the series over ordered tuples. -/
theorem tsum_pi_prod_eq_pow {α : Type*} (f : α → ℝ≥0∞) (n : ℕ) :
    (∑' x : Fin n → α, ∏ i, f (x i)) = (∑' a, f a) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', ← ih, ← ENNReal.tsum_mul_right]
      simp_rw [← ENNReal.tsum_mul_left]
      rw [← ENNReal.tsum_prod]
      rw [← (Fin.consEquiv (fun _ : Fin (n + 1) ↦ α)).tsum_eq]
      apply tsum_congr
      intro x
      rw [Fin.prod_univ_succ]
      simp

/-- The `n`th extended moment of the origin-cluster size. -/
noncomputable def clusterSizeMomentENNReal (d : ℕ) (p : unitInterval) (n : ℕ) : ℝ≥0∞ :=
  ∫⁻ ω, clusterSizeENNReal d ω ^ n ∂bernoulliBondMeasure d p

/-- Membership of a vertex in the origin cluster, as a zero-one `ℝ≥0∞` random variable. -/
private noncomputable def clusterMembershipIndicator (d : ℕ) (y : Cubic d) :
    EdgeConfiguration d → ℝ≥0∞ :=
  (connectionEvent d cubicOrigin y).indicator fun _ ↦ 1

private theorem clusterMembershipIndicator_apply (d : ℕ) (y : Cubic d)
    (ω : EdgeConfiguration d) :
    clusterMembershipIndicator d y ω =
      if y ∈ cubicOpenCluster d ω then 1 else 0 := by
  classical
  simp only [clusterMembershipIndicator, Set.indicator, connectionEvent, cubicOpenCluster,
    cubicOpenClusterFrom, Set.mem_setOf_eq]
  rfl

private theorem measurable_clusterMembershipIndicator (d : ℕ) (y : Cubic d) :
    Measurable (clusterMembershipIndicator d y) :=
  measurable_const.indicator (measurableSet_connectionEvent d cubicOrigin y)

/-- Pointwise ordered-tuple expansion of a power of the cluster cardinality. -/
theorem clusterSizeENNReal_pow_eq_tsum_prod (d n : ℕ) (ω : EdgeConfiguration d) :
    clusterSizeENNReal d ω ^ n =
      ∑' y : Fin n → Cubic d, ∏ i, clusterMembershipIndicator d (y i) ω := by
  classical
  unfold clusterSizeENNReal
  rw [show (∑' y : Cubic d,
      if y ∈ cubicOpenCluster d ω then (1 : ℝ≥0∞) else 0) =
      ∑' y : Cubic d, clusterMembershipIndicator d y ω by
    apply tsum_congr
    intro y
    exact (clusterMembershipIndicator_apply d y ω).symm]
  exact (tsum_pi_prod_eq_pow (fun y ↦ clusterMembershipIndicator d y ω) n).symm

theorem measurableSet_orderedMultiPointConnectionEvent (d k : ℕ)
    (x : Fin (k + 3) → Cubic d) :
    MeasurableSet (orderedMultiPointConnectionEvent d k x) := by
  change MeasurableSet {ω | ∀ i, ω ∈ connectionEvent d (x 0) (x i)}
  rw [show {ω | ∀ i, ω ∈ connectionEvent d (x 0) (x i)} =
      ⋂ i, connectionEvent d (x 0) (x i) by ext; simp]
  exact MeasurableSet.iInter fun i ↦ measurableSet_connectionEvent d (x 0) (x i)

private theorem prod_clusterMembershipIndicator_rooted (d k : ℕ)
    (y : Fin (k + 2) → Cubic d) (ω : EdgeConfiguration d) :
    (∏ i, clusterMembershipIndicator d (y i) ω) =
      (orderedMultiPointConnectionEvent d k
        (rootedTerminalTuple cubicOrigin y)).indicator (fun _ ↦ (1 : ℝ≥0∞)) ω := by
  classical
  simp_rw [clusterMembershipIndicator_apply]
  simp only [Set.indicator, orderedMultiPointConnectionEvent, Set.mem_setOf_eq]
  have hequiv :
      (∀ i : Fin (k + 3),
        ω ∈ connectionEvent d (rootedTerminalTuple cubicOrigin y 0)
          (rootedTerminalTuple cubicOrigin y i)) ↔
        ∀ j : Fin (k + 2), ω ∈ connectionEvent d cubicOrigin (y j) := by
    constructor
    · intro h j
      simpa [rootedTerminalTuple] using h j.succ
    · intro h i
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · change ω ∈ connectionEvent d cubicOrigin cubicOrigin
        exact ⟨SimpleGraph.Walk.nil, by simp [walkIsOpen]⟩
      · simpa [rootedTerminalTuple] using h j
  rw [if_congr hequiv rfl rfl]
  by_cases h : ∀ i, ω ∈ connectionEvent d cubicOrigin (y i)
  · rw [if_pos h]
    apply Finset.prod_eq_one
    intro i _hi
    have hi := h i
    change y i ∈ cubicOpenCluster d ω at hi
    rw [if_pos hi]
  · rw [if_neg h]
    push_neg at h
    obtain ⟨j, hj⟩ := h
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    change y j ∉ cubicOpenCluster d ω at hj
    rw [if_neg hj]

private theorem measurable_prod_clusterMembershipIndicator (d k : ℕ)
    (y : Fin (k + 2) → Cubic d) :
    Measurable fun ω ↦ ∏ i, clusterMembershipIndicator d (y i) ω := by
  rw [show (fun ω ↦ ∏ i, clusterMembershipIndicator d (y i) ω) =
      (orderedMultiPointConnectionEvent d k
        (rootedTerminalTuple cubicOrigin y)).indicator (fun _ ↦ (1 : ℝ≥0∞)) by
    funext ω
    exact prod_clusterMembershipIndicator_rooted d k y ω]
  exact measurable_const.indicator
    (measurableSet_orderedMultiPointConnectionEvent d k
      (rootedTerminalTuple cubicOrigin y))

/-- The `(k+2)`nd cluster moment is the total mass of ordered `(k+2)`-tuples connected to the
origin. -/
theorem clusterSizeMomentENNReal_eq_orderedConnectionMass (d k : ℕ) (p : unitInterval) :
    clusterSizeMomentENNReal d p (k + 2) =
      ∑' y : Fin (k + 2) → Cubic d,
        bernoulliBondMeasure d p
          (orderedMultiPointConnectionEvent d k
            (rootedTerminalTuple cubicOrigin y)) := by
  unfold clusterSizeMomentENNReal
  simp_rw [clusterSizeENNReal_pow_eq_tsum_prod]
  rw [lintegral_tsum fun y ↦
    (measurable_prod_clusterMembershipIndicator d k y).aemeasurable]
  apply tsum_congr
  intro y
  rw [show (fun ω ↦ ∏ i, clusterMembershipIndicator d (y i) ω) =
      (orderedMultiPointConnectionEvent d k
        (rootedTerminalTuple cubicOrigin y)).indicator (fun _ ↦ (1 : ℝ≥0∞)) by
    funext ω
    exact prod_clusterMembershipIndicator_rooted d k y ω]
  simp [measurableSet_orderedMultiPointConnectionEvent]

/-- Grimmett (6.94), indexed so the moment is `k+2`: the tree-graph estimate bounds it by the
number of labelled trivalent skeletons times one susceptibility factor per skeleton edge. -/
theorem clusterSizeMoment_le (d k : ℕ) (p : unitInterval) :
    clusterSizeMomentENNReal d p (k + 2) ≤
      (connectivitySkeletonCount (k + 3) : ℝ≥0∞) *
        susceptibility d p ^ (2 * k + 3) := by
  rw [clusterSizeMomentENNReal_eq_orderedConnectionMass]
  refine (orderedMultiPointConnectionMass_le d k p).trans_eq ?_
  congr 2

#print axioms tsum_pi_prod_eq_pow
#print axioms clusterSizeENNReal_pow_eq_tsum_prod
#print axioms clusterSizeMomentENNReal_eq_orderedConnectionMass
#print axioms clusterSizeMoment_le

end Percolation
