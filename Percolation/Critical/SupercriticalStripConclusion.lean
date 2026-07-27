import Percolation.Critical.SupercriticalRadiusPositivity
import Percolation.Critical.SupercriticalStripContraction

/-!
# Exponential hyperplane avoidance from a supercritical strip

This file connects the abstract fresh-strip contraction to Grimmett's event `G_n`, completing
equations (8.44)--(8.48) once one coordinate strip is known to be supercritical.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

/-- A finite origin cluster reaching beyond the `r`-th strip boundary belongs to the accumulated
avoidance history `A_r`. -/
theorem mem_coordinateStripAvoidanceHistory_of_finiteCluster_of_connection
    {d : ℕ} {i : Fin d} {k r : ℕ} (hk : 0 < k)
    {x : Cubic d} {ω : EdgeConfiguration d}
    (hfinite : ω ∈ finiteClusterEvent d)
    (hconn : ω ∈ connectionEvent d cubicOrigin x)
    (hx : coordinateStripBoundary k r ≤ x i) :
    ω ∈ coordinateStripAvoidanceHistory d i k r := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
      rcases r with _ | r
      · simp [coordinateStripAvoidanceHistory]
      · rcases r with _ | r
        · change ω ∈ coordinateStripAvoidanceEvent d i 0 k cubicOrigin
          apply mem_coordinateStripAvoidanceEvent_of_finiteCluster_of_connection hfinite
          exact ⟨SimpleGraph.Walk.nil, by
            intro e he
            simp at he⟩
        · rw [show r + 1 + 1 = r + 2 by omega, coordinateStripAvoidanceHistory]
          have hbound : coordinateStripBoundary k (r + 1) ≤
              coordinateStripBoundary k (r + 2) := by
            simp only [coordinateStripBoundary, Nat.cast_add, Nat.cast_one]
            have hk0 : (0 : ℤ) ≤ (k : ℤ) := by positivity
            apply mul_le_mul_of_nonneg_right _ hk0
            norm_num
          have hxPrev : coordinateStripBoundary k (r + 1) ≤ x i := hbound.trans hx
          constructor
          · exact ih (r + 1) (by omega) hxPrev
          · apply mem_coordinateStripRestartEvent_of_finiteCluster_of_exists_entrance hfinite
            apply exists_coordinateStripEntrance_of_connection
            · rw [coordinateStripBoundary]
              positivity
            · exact hxPrev
            · exact hconn

/-- Event form of equation (8.46): `G_n` is contained in the avoidance history through every
completed width-`k` strip. -/
theorem finiteClusterHitsHyperplaneEvent_subset_coordinateStripAvoidanceHistory
    {d : ℕ} (hd : 0 < d) (k n : ℕ) (hk : 0 < k) :
    finiteClusterHitsHyperplaneEvent d hd n ⊆
      coordinateStripAvoidanceHistory d ⟨0, hd⟩ k (n / k) := by
  intro ω hω
  rw [finiteClusterHitsHyperplaneEvent,
    mem_finiteClusterHitsSignedHyperplaneEvent_iff] at hω
  obtain ⟨hfinite, x, hx, hconn⟩ := hω
  apply mem_coordinateStripAvoidanceHistory_of_finiteCluster_of_connection
    hk hfinite hconn
  rw [coordinateStripBoundary]
  change (((n / k) * k : ℕ) : ℤ) ≤ x ⟨0, hd⟩
  have hx' : x ⟨0, hd⟩ = (n : ℤ) := by simpa using hx
  rw [hx']
  exact_mod_cast Nat.div_mul_le_self n k

/-- Equation (8.47), in its exact floor form. -/
theorem finiteClusterHitsHyperplane_probability_le_stripAvoidance_pow
    {d : ℕ} (hd : 0 < d) (p : I) (k n : ℕ) (hk : 0 < k) :
    (bernoulliBondMeasure d p).real
        (finiteClusterHitsHyperplaneEvent d hd n) ≤
      (1 - regionThetaFrom d
        (cubicCoordinateStrip d ⟨0, hd⟩ 0 k) p cubicOrigin) ^ (n / k) := by
  calc
    (bernoulliBondMeasure d p).real
        (finiteClusterHitsHyperplaneEvent d hd n) ≤
      (bernoulliBondMeasure d p).real
        (coordinateStripAvoidanceHistory d ⟨0, hd⟩ k (n / k)) :=
      measureReal_mono
        (finiteClusterHitsHyperplaneEvent_subset_coordinateStripAvoidanceHistory hd k n hk)
    _ ≤ (1 - regionThetaFrom d
        (cubicCoordinateStrip d ⟨0, hd⟩ 0 k) p cubicOrigin) ^ (n / k) :=
      bernoulliBondMeasure_real_coordinateStripAvoidanceHistory_le_pow
        p ⟨0, hd⟩ k (n / k)

/-- Even before completing a whole strip, `G_n` is bounded by the probability that the
origin's cluster internal to the initial strip is finite. -/
theorem finiteClusterHitsHyperplaneEvent_subset_coordinateStripAvoidanceEvent
    {d : ℕ} (hd : 0 < d) (k n : ℕ) :
    finiteClusterHitsHyperplaneEvent d hd n ⊆
      coordinateStripAvoidanceEvent d ⟨0, hd⟩ 0 k cubicOrigin := by
  intro ω hω
  rw [finiteClusterHitsHyperplaneEvent,
    mem_finiteClusterHitsSignedHyperplaneEvent_iff] at hω
  exact mem_coordinateStripAvoidanceEvent_of_finiteCluster_of_connection hω.1
    ⟨SimpleGraph.Walk.nil, by
      intro e he
      simp at he⟩

theorem finiteClusterHitsHyperplane_probability_le_stripAvoidance
    {d : ℕ} (hd : 0 < d) (p : I) (k n : ℕ) :
    (bernoulliBondMeasure d p).real
        (finiteClusterHitsHyperplaneEvent d hd n) ≤
      1 - regionThetaFrom d
        (cubicCoordinateStrip d ⟨0, hd⟩ 0 k) p cubicOrigin := by
  calc
    _ ≤ (bernoulliBondMeasure d p).real
        (coordinateStripAvoidanceEvent d ⟨0, hd⟩ 0 k cubicOrigin) :=
      measureReal_mono
        (finiteClusterHitsHyperplaneEvent_subset_coordinateStripAvoidanceEvent hd k n)
    _ = _ := bernoulliBondMeasure_real_coordinateStripAvoidanceEvent
      p ⟨0, hd⟩ k rfl

/-- The explicit positive rate in (8.48).  Replacing the failure probability `q` by
`(q+1)/2` makes the formula endpoint-safe even when `q=0`. -/
noncomputable def coordinateStripExponentialRate (q : ℝ) (k : ℕ) : ℝ :=
  -Real.log ((q + 1) / 2) / (2 * k)

theorem coordinateStripExponentialRate_pos {q : ℝ} {k : ℕ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hk : 0 < k) :
    0 < coordinateStripExponentialRate q k := by
  rw [coordinateStripExponentialRate]
  apply div_pos
  · apply neg_pos.mpr
    apply Real.log_neg
    · linarith
    · linarith
  · positivity

private theorem nat_le_two_mul_mul_div_strip {n k : ℕ} (hk : 0 < k) (hn : k ≤ n) :
    n ≤ 2 * k * (n / k) := by
  have hquot : 1 ≤ n / k := (Nat.le_div_iff_mul_le hk).2 (by simpa using hn)
  have hk_le : k ≤ k * (n / k) := by
    simpa using Nat.mul_le_mul_left k hquot
  have hmod : n % k < k := Nat.mod_lt n hk
  calc
    n = k * (n / k) + n % k := (Nat.div_add_mod n k).symm
    _ ≤ k * (n / k) + k * (n / k) := Nat.add_le_add_left (hmod.le.trans hk_le) _
    _ = 2 * k * (n / k) := by ring

private theorem pow_natDiv_le_exp_neg_coordinateStripExponentialRate
    {q : ℝ} {n k : ℕ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hk : 0 < k) (hn : k ≤ n) :
    q ^ (n / k) ≤ Real.exp (-(coordinateStripExponentialRate q k) * n) := by
  let q' := (q + 1) / 2
  let m := n / k
  have hq'0 : 0 < q' := by dsimp [q']; linarith
  have hq'1 : q' < 1 := by dsimp [q']; linarith
  have hqq' : q ≤ q' := by dsimp [q']; linarith
  have hlog : Real.log q' < 0 := Real.log_neg hq'0 hq'1
  have hnat := nat_le_two_mul_mul_div_strip hk hn
  have hcast : (n : ℝ) ≤ 2 * (k : ℝ) * (m : ℝ) := by
    exact_mod_cast hnat
  have hden : 0 < 2 * (k : ℝ) := by positivity
  have hratio : (n : ℝ) / (2 * k) ≤ (m : ℝ) := by
    rw [div_le_iff₀ hden]
    nlinarith
  have hexp : (m : ℝ) * Real.log q' ≤ Real.log q' * (n / (2 * k)) := by
    nlinarith
  calc
    q ^ m ≤ q' ^ m := pow_le_pow_left₀ hq0 hqq' m
    _ = Real.exp ((m : ℝ) * Real.log q') := by
      calc
        q' ^ m = Real.exp (Real.log q') ^ m := by rw [Real.exp_log hq'0]
        _ = Real.exp ((m : ℝ) * Real.log q') := (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp (Real.log q' * (n / (2 * k))) := Real.exp_le_exp.mpr hexp
    _ = Real.exp (-(coordinateStripExponentialRate q k) * n) := by
      congr 1
      dsimp [coordinateStripExponentialRate, q']
      field_simp

private theorem le_exp_neg_coordinateStripExponentialRate_of_lt
    {q : ℝ} {n k : ℕ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hk : 0 < k) (hn : n < k) :
    q ≤ Real.exp (-(coordinateStripExponentialRate q k) * n) := by
  let q' := (q + 1) / 2
  have hq'0 : 0 < q' := by dsimp [q']; linarith
  have hq'1 : q' < 1 := by dsimp [q']; linarith
  have hqq' : q ≤ q' := by dsimp [q']; linarith
  calc
    q ≤ q' := hqq'
    _ = Real.exp (Real.log q') := (Real.exp_log hq'0).symm
    _ ≤ Real.exp (-(coordinateStripExponentialRate q k) * n) := by
      apply Real.exp_le_exp.mpr
      have hlog : Real.log q' < 0 := Real.log_neg hq'0 hq'1
      have hkR : 0 < (k : ℝ) := by positivity
      have hnR : (n : ℝ) < k := by exact_mod_cast hn
      change Real.log q' ≤
        -(-Real.log q' / (2 * (k : ℝ))) * (n : ℝ)
      rw [show -(-Real.log q' / (2 * (k : ℝ))) * (n : ℝ) =
          Real.log q' * n / (2 * k) by ring]
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * k)]
      nlinarith

/-- Equation (8.48): positive percolation in one finite-width coordinate strip gives a
strict exponential upper bound for Grimmett's finite-cluster hyperplane event. -/
theorem finiteClusterHitsHyperplane_probability_le_exp_of_stripTheta_pos
    {d : ℕ} (hd : 0 < d) (p : I) {k : ℕ} (hk : 0 < k)
    (htheta : 0 < regionThetaFrom d
      (cubicCoordinateStrip d ⟨0, hd⟩ 0 k) p cubicOrigin) :
    let q := 1 - regionThetaFrom d
      (cubicCoordinateStrip d ⟨0, hd⟩ 0 k) p cubicOrigin
    0 < coordinateStripExponentialRate q k ∧
      ∀ n : ℕ,
        (bernoulliBondMeasure d p).real
            (finiteClusterHitsHyperplaneEvent d hd n) ≤
          Real.exp (-(coordinateStripExponentialRate q k) * n) := by
  let theta := regionThetaFrom d
    (cubicCoordinateStrip d ⟨0, hd⟩ 0 k) p cubicOrigin
  let q := 1 - theta
  have htheta1 : theta ≤ 1 := measureReal_le_one
  have hq0 : 0 ≤ q := by dsimp [q]; linarith
  have hq1 : q < 1 := by dsimp [q]; linarith
  refine ⟨coordinateStripExponentialRate_pos hq0 hq1 hk, ?_⟩
  intro n
  by_cases hn : k ≤ n
  · exact (finiteClusterHitsHyperplane_probability_le_stripAvoidance_pow
      hd p k n hk).trans
        (pow_natDiv_le_exp_neg_coordinateStripExponentialRate hq0 hq1 hk hn)
  · exact (finiteClusterHitsHyperplane_probability_le_stripAvoidance
      hd p k n).trans
        (le_exp_neg_coordinateStripExponentialRate_of_lt hq0 hq1 hk (Nat.lt_of_not_ge hn))

/-- Uniform form of (8.48): a positive lower bound `theta0` for the strip-percolation
probability gives one exponential rate for every density having at least that strip probability. -/
theorem finiteClusterHitsHyperplane_probability_le_exp_of_stripTheta_ge
    {d : ℕ} (hd : 0 < d) (p : I) {k : ℕ} (hk : 0 < k)
    {theta0 : ℝ} (htheta0 : 0 < theta0)
    (htheta : theta0 ≤ regionThetaFrom d
      (cubicCoordinateStrip d ⟨0, hd⟩ 0 k) p cubicOrigin) :
    let q := 1 - theta0
    0 < coordinateStripExponentialRate q k ∧
      ∀ n : ℕ,
        (bernoulliBondMeasure d p).real
            (finiteClusterHitsHyperplaneEvent d hd n) ≤
          Real.exp (-(coordinateStripExponentialRate q k) * n) := by
  let theta := regionThetaFrom d
    (cubicCoordinateStrip d ⟨0, hd⟩ 0 k) p cubicOrigin
  let q := 1 - theta0
  let qp := 1 - theta
  have htheta1 : theta ≤ 1 := measureReal_le_one
  have htheta01 : theta0 ≤ 1 := htheta.trans htheta1
  have hq0 : 0 ≤ q := by dsimp [q]; linarith
  have hq1 : q < 1 := by dsimp [q]; linarith
  have hqp0 : 0 ≤ qp := by dsimp [qp]; linarith
  have hqpq : qp ≤ q := by dsimp [qp, q, theta]; linarith
  refine ⟨coordinateStripExponentialRate_pos hq0 hq1 hk, ?_⟩
  intro n
  by_cases hn : k ≤ n
  · calc
      (bernoulliBondMeasure d p).real
          (finiteClusterHitsHyperplaneEvent d hd n) ≤ qp ^ (n / k) :=
        finiteClusterHitsHyperplane_probability_le_stripAvoidance_pow hd p k n hk
      _ ≤ q ^ (n / k) := pow_le_pow_left₀ hqp0 hqpq _
      _ ≤ Real.exp (-(coordinateStripExponentialRate q k) * n) :=
        pow_natDiv_le_exp_neg_coordinateStripExponentialRate hq0 hq1 hk hn
  · calc
      (bernoulliBondMeasure d p).real
          (finiteClusterHitsHyperplaneEvent d hd n) ≤ qp :=
        finiteClusterHitsHyperplane_probability_le_stripAvoidance hd p k n
      _ ≤ q := hqpq
      _ ≤ Real.exp (-(coordinateStripExponentialRate q k) * n) :=
        le_exp_neg_coordinateStripExponentialRate_of_lt hq0 hq1 hk (Nat.lt_of_not_ge hn)

/-- Above the critical probability of the reference coordinate strip, its rooted infinite
cluster probability is positive. -/
theorem regionThetaFrom_coordinateStrip_pos_of_critical_lt
    {d : ℕ} (hd : 0 < d) (p : I) {k : ℕ} (hk : 0 < k)
    (hcrit : regionCriticalProbability d
      (cubicCoordinateStrip d ⟨0, hd⟩ 0 k) < (p : ℝ)) :
    0 < regionThetaFrom d
      (cubicCoordinateStrip d ⟨0, hd⟩ 0 k) p cubicOrigin :=
  regionThetaFrom_pos_of_critical_lt_of_connected
    (cubicRegionGraph_coordinateStrip_zero_connected ⟨0, hd⟩ hk)
    hcrit (cubicOrigin_mem_coordinateStrip_zero ⟨0, hd⟩ hk)

/-- **Theorem 8.21 from a supercritical coordinate strip.**  This is the complete Chapter 8
argument (8.43)--(8.48); the only premise left for Chapter 7 is the existence of a finite-width
coordinate strip whose critical probability lies below `p`. -/
theorem finiteClusterRadiusDecayRate_pos_of_coordinateStrip_critical_lt
    {d : ℕ} (hd : 2 ≤ d) (p : I) (hp1 : (p : ℝ) < 1)
    {k : ℕ} (hk : 0 < k)
    (hcrit : regionCriticalProbability d
      (cubicCoordinateStrip d ⟨0, Nat.zero_lt_of_lt hd⟩ 0 k) < (p : ℝ)) :
    0 < finiteClusterRadiusDecayRate d p := by
  have htheta := regionThetaFrom_coordinateStrip_pos_of_critical_lt
    (Nat.zero_lt_of_lt hd) p hk hcrit
  obtain ⟨hgamma, hbound⟩ :=
    finiteClusterHitsHyperplane_probability_le_exp_of_stripTheta_pos
      (Nat.zero_lt_of_lt hd) p hk htheta
  have hp0 : 0 < (p : ℝ) :=
    (regionCriticalProbability_nonneg d
      (cubicCoordinateStrip d ⟨0, Nat.zero_lt_of_lt hd⟩ 0 k)).trans_lt hcrit
  apply finiteClusterRadiusDecayRate_pos_of_hyperplane_bound hd p hp0 hp1 hgamma
  intro n
  simpa [mul_comm] using hbound n

end Percolation
