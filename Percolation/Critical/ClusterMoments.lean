import Percolation.Critical.ConnectedKernel
import Mathlib.Analysis.Analytic.Binomial

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

@[simp] theorem clusterSizeMomentENNReal_one (d : ℕ) (p : unitInterval) :
    clusterSizeMomentENNReal d p 1 = susceptibility d p := by
  simp [clusterSizeMomentENNReal, susceptibility]

/-- Uniform reindexing of (6.94), including its first-moment endpoint. -/
theorem clusterSizeMoment_succ_le (d n : ℕ) (p : unitInterval) :
    clusterSizeMomentENNReal d p (n + 1) ≤
      (connectivitySkeletonCount (n + 2) : ℝ≥0∞) *
        susceptibility d p ^ (2 * n + 1) := by
  cases n with
  | zero => simp [connectivitySkeletonCount]
  | succ k => simpa [Nat.mul_add, Nat.add_assoc] using clusterSizeMoment_le d k p

/-- Power-series form of `E(|C| exp(t|C|))`; keeping the series in `ℝ≥0∞` preserves infinite
clusters and avoids a lossy `toReal` convention. -/
noncomputable def clusterSizeWeightedExpMoment
    (d : ℕ) (p : unitInterval) (t : ℝ≥0∞) : ℝ≥0∞ :=
  ∑' n : ℕ, t ^ n / (Nat.factorial n : ℝ≥0∞) *
    clusterSizeMomentENNReal d p (n + 1)

/-- The moment estimate summed termwise, before evaluating the skeleton generating function. -/
theorem clusterSizeWeightedExpMoment_le_skeletonSeries
    (d : ℕ) (p : unitInterval) (t : ℝ≥0∞) :
    clusterSizeWeightedExpMoment d p t ≤
      susceptibility d p *
        ∑' n : ℕ, (connectivitySkeletonCount (n + 2) : ℝ≥0∞) /
          (Nat.factorial n : ℝ≥0∞) *
            (t * susceptibility d p ^ 2) ^ n := by
  rw [clusterSizeWeightedExpMoment, ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro n
  calc
    t ^ n / (Nat.factorial n : ℝ≥0∞) * clusterSizeMomentENNReal d p (n + 1) ≤
        t ^ n / (Nat.factorial n : ℝ≥0∞) *
          ((connectivitySkeletonCount (n + 2) : ℝ≥0∞) *
            susceptibility d p ^ (2 * n + 1)) :=
      mul_le_mul_left' (clusterSizeMoment_succ_le d n p) _
    _ = susceptibility d p *
        ((connectivitySkeletonCount (n + 2) : ℝ≥0∞) /
          (Nat.factorial n : ℝ≥0∞) *
            (t * susceptibility d p ^ 2) ^ n) := by
      rw [mul_pow]
      have hexp : 2 * n + 1 = 1 + 2 * n := by omega
      rw [hexp, pow_add, pow_one, pow_mul]
      simp only [div_eq_mul_inv]
      ac_rfl

/-! ### The skeleton generating function -/

/-- The skeleton coefficient is the scaled half-multichoose coefficient. -/
theorem connectivitySkeletonCount_eq_scaled_half_multichoose (n : ℕ) :
    (2 : ℝ) ^ n * Nat.factorial n * Ring.multichoose (1 / 2 : ℝ) n =
      connectivitySkeletonCount (n + 2) := by
  induction n with
  | zero => norm_num [connectivitySkeletonCount]
  | succ n ih =>
      by_cases hn : n = 0
      · subst n
        norm_num [connectivitySkeletonCount]
      have hp_n := Ring.factorial_nsmul_multichoose_eq_ascPochhammer (1 / 2 : ℝ) n
      have hp_succ := Ring.factorial_nsmul_multichoose_eq_ascPochhammer
        (1 / 2 : ℝ) (n + 1)
      simp only [nsmul_eq_mul] at hp_n hp_succ
      rw [ascPochhammer_succ_right, Polynomial.smeval_mul,
        Polynomial.smeval_add, Polynomial.smeval_X, Polynomial.smeval_natCast] at hp_succ
      norm_num [nsmul_eq_mul] at hp_succ
      rw [pow_succ]
      calc
        (2 : ℝ) ^ n * 2 * Nat.factorial (n + 1) *
            Ring.multichoose (1 / 2 : ℝ) (n + 1) =
            (2 : ℝ) ^ n * 2 *
              (Nat.factorial (n + 1) * Ring.multichoose (1 / 2 : ℝ) (n + 1)) := by ring
        _ = (2 : ℝ) ^ n * 2 *
              ((ascPochhammer ℕ n).smeval (1 / 2 : ℝ) * (1 / 2 + n)) := by rw [hp_succ]
        _ = (2 * n + 1 : ℝ) *
              ((2 : ℝ) ^ n * Nat.factorial n * Ring.multichoose (1 / 2 : ℝ) n) := by
                rw [← hp_n]
                push_cast
                ring
        _ = (2 * n + 1 : ℝ) * connectivitySkeletonCount (n + 2) := by rw [ih]
        _ = connectivitySkeletonCount (n + 1 + 2) := by
          have hfactor : 2 * (n + 2) - 3 = 2 * n + 1 := by omega
          rw [show n + 1 + 2 = (n + 2) + 1 by omega,
            connectivitySkeletonCount_succ (n := n + 2) (by omega), hfactor]
          push_cast
          ring

/-- Generating function for the labelled-skeleton coefficients. -/
theorem hasSum_connectivitySkeletonCount_div_factorial (x : ℝ) (hx : |2 * x| < 1) :
    HasSum (fun n : ℕ ↦
      (connectivitySkeletonCount (n + 2) : ℝ) / Nat.factorial n * x ^ n)
      (1 / (1 - 2 * x) ^ (1 / 2 : ℝ)) := by
  have hy : (2 * x : ℝ) ∈ Metric.eball (0 : ℝ) 1 := by
    rw [Metric.mem_eball, edist_dist, Real.dist_eq, sub_zero]
    change ENNReal.ofReal |2 * x| < 1
    exact ENNReal.ofReal_lt_one.mpr hx
  have hs :=
    (Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero (1 / 2 : ℝ)).hasSum_sub hy
  convert hs using 1
  · funext n
    rw [FormalMultilinearSeries.ofScalars_apply_eq]
    simp only [sub_zero, smul_eq_mul]
    rw [← connectivitySkeletonCount_eq_scaled_half_multichoose n]
    rw [show Ring.choose (1 / 2 + (n : ℝ) - 1) n =
        Ring.multichoose (1 / 2 : ℝ) n by
      symm
      exact Ring.multichoose_eq (1 / 2 : ℝ) n]
    field_simp [Nat.factorial_ne_zero]
    ring

/-- `ℝ≥0∞` form of the skeleton generating function, suitable for moment estimates. -/
theorem tsum_connectivitySkeletonCount_div_factorial
    (x : ℝ≥0∞) (hx : 2 * x < 1) :
    (∑' n : ℕ, (connectivitySkeletonCount (n + 2) : ℝ≥0∞) /
      (Nat.factorial n : ℝ≥0∞) * x ^ n) =
        ENNReal.ofReal
          (1 / (1 - 2 * x.toReal) ^ (1 / 2 : ℝ)) := by
  have hx_top : x ≠ ⊤ := by
    intro h
    simp [h] at hx
  have hx_nonneg : 0 ≤ x.toReal := ENNReal.toReal_nonneg
  have hx_real : |2 * x.toReal| < 1 := by
    rw [abs_of_nonneg (mul_nonneg (by norm_num) hx_nonneg)]
    apply ENNReal.ofReal_lt_one.mp
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat,
      ENNReal.ofReal_toReal hx_top]
    simpa using hx
  have hs := hasSum_connectivitySkeletonCount_div_factorial x.toReal hx_real
  calc
    (∑' n : ℕ, (connectivitySkeletonCount (n + 2) : ℝ≥0∞) /
        (Nat.factorial n : ℝ≥0∞) * x ^ n) =
        ∑' n : ℕ, ENNReal.ofReal
          ((connectivitySkeletonCount (n + 2) : ℝ) /
            Nat.factorial n * x.toReal ^ n) := by
      apply tsum_congr
      intro n
      rw [ENNReal.ofReal_mul (div_nonneg (by positivity) (by positivity)),
        ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_pow hx_nonneg,
        ENNReal.ofReal_toReal hx_top]
      norm_cast
    _ = ENNReal.ofReal (∑' n : ℕ,
        (connectivitySkeletonCount (n + 2) : ℝ) /
          Nat.factorial n * x.toReal ^ n) := by
      rw [ENNReal.ofReal_tsum_of_nonneg (fun n ↦
        mul_nonneg (div_nonneg (by positivity) (by positivity)) (by positivity)) hs.summable]
    _ = ENNReal.ofReal
        (1 / (1 - 2 * x.toReal) ^ (1 / 2 : ℝ)) := by rw [hs.tsum_eq]

/-- Grimmett (6.97): the size-weighted exponential moment is controlled by the square-root
singularity of the skeleton generating function. -/
theorem clusterSize_expMoment_le
    (d : ℕ) (p : unitInterval) (t : ℝ≥0∞)
    (ht : 2 * (t * susceptibility d p ^ 2) < 1) :
    clusterSizeWeightedExpMoment d p t ≤
      susceptibility d p * ENNReal.ofReal
        (1 / (1 - 2 * (t * susceptibility d p ^ 2).toReal) ^ (1 / 2 : ℝ)) := by
  refine (clusterSizeWeightedExpMoment_le_skeletonSeries d p t).trans_eq ?_
  rw [tsum_connectivitySkeletonCount_div_factorial _ ht]

#print axioms tsum_pi_prod_eq_pow
#print axioms clusterSizeENNReal_pow_eq_tsum_prod
#print axioms clusterSizeMomentENNReal_eq_orderedConnectionMass
#print axioms clusterSizeMoment_le
#print axioms connectivitySkeletonCount_eq_scaled_half_multichoose
#print axioms hasSum_connectivitySkeletonCount_div_factorial
#print axioms tsum_connectivitySkeletonCount_div_factorial
#print axioms clusterSize_expMoment_le

end Percolation
