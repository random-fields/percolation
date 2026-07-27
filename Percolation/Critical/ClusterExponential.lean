import Percolation.Critical.ClusterMoments
import Percolation.Critical.ClusterTail

/-!
# Exponential cluster-size tails

This module formalizes Grimmett (6.74)--(6.77).  The at-least tail is kept distinct from the
strict tail used in Chapter 5, and the concrete bound retains the source constant `1 / 2`.
-/

namespace Percolation

open Set MeasureTheory
open scoped BigOperators ENNReal unitInterval

/-- Event that the origin cluster has at least `n` vertices. -/
def clusterSizeAtLeastEvent (d n : ℕ) : Set (EdgeConfiguration d) :=
  {ω | (n : ℝ≥0∞) ≤ clusterSizeENNReal d ω}

theorem measurableSet_clusterSizeAtLeastEvent (d n : ℕ) :
    MeasurableSet (clusterSizeAtLeastEvent d n) := by
  exact (measurable_clusterSizeENNReal d) measurableSet_Ici

/-- The at-least cluster-size tail `Pₚ(|C| ≥ n)`. -/
noncomputable def clusterSizeAtLeast (d : ℕ) (p : unitInterval) (n : ℕ) : ℝ :=
  (bernoulliBondMeasure d p).real (clusterSizeAtLeastEvent d n)

/-- ENNReal-valued form used by integral inequalities. -/
noncomputable def clusterSizeAtLeastENNReal (d : ℕ) (p : unitInterval) (n : ℕ) : ℝ≥0∞ :=
  bernoulliBondMeasure d p (clusterSizeAtLeastEvent d n)

theorem clusterSizeAtLeastENNReal_eq_ofReal (d : ℕ) (p : unitInterval) (n : ℕ) :
    clusterSizeAtLeastENNReal d p n = ENNReal.ofReal (clusterSizeAtLeast d p n) := by
  exact (ofReal_measureReal (measure_ne_top _ _)).symm

/-- The exact shift from the new at-least tail to Chapter 5's strict tail. -/
theorem clusterSizeAtLeast_eq_clusterSizeTail (d : ℕ) (p : unitInterval) (n : ℕ) :
    clusterSizeAtLeast d p (n + 1) = clusterSizeTail d p n := by
  unfold clusterSizeAtLeast clusterSizeTail
  congr 1
  ext ω
  simp only [clusterSizeAtLeastEvent, Set.mem_setOf_eq]
  rw [clusterSizeENNReal_eq_encard]
  norm_cast
  exact ENat.add_one_le_iff (ENat.coe_ne_top n)

/-- Markov's moment inequality specialized to the cluster-size event. -/
theorem clusterSize_pow_mul_atLeast_le_moment
    (d : ℕ) (p : unitInterval) (n m : ℕ) :
    (n : ℝ≥0∞) ^ m * clusterSizeAtLeastENNReal d p n ≤
      clusterSizeMomentENNReal d p m := by
  let μ := bernoulliBondMeasure d p
  let A := clusterSizeAtLeastEvent d n
  calc
    (n : ℝ≥0∞) ^ m * clusterSizeAtLeastENNReal d p n =
        ∫⁻ ω in A, (n : ℝ≥0∞) ^ m ∂μ := by
      simp [clusterSizeAtLeastENNReal, A, μ,
        measurableSet_clusterSizeAtLeastEvent]
    _ ≤ ∫⁻ ω in A, clusterSizeENNReal d ω ^ m ∂μ := by
      apply setLIntegral_mono (Measurable.pow_const (measurable_clusterSizeENNReal d) m)
      intro ω hω
      change (n : ℝ≥0∞) ≤ clusterSizeENNReal d ω at hω
      exact pow_le_pow_left' hω m
    _ ≤ ∫⁻ ω, clusterSizeENNReal d ω ^ m ∂μ :=
      setLIntegral_le_lintegral A _
    _ = clusterSizeMomentENNReal d p m := rfl

/-- The ENNReal exponential series at a finite nonnegative argument. -/
theorem tsum_pow_div_factorial_eq_ofReal_exp (x : ℝ≥0∞) (hx : x ≠ ⊤) :
    (∑' n : ℕ, x ^ n / (Nat.factorial n : ℝ≥0∞)) =
      ENNReal.ofReal (Real.exp x.toReal) := by
  have hs := NormedSpace.expSeries_div_hasSum_exp x.toReal
  calc
    (∑' n : ℕ, x ^ n / (Nat.factorial n : ℝ≥0∞)) =
        ∑' n : ℕ, ENNReal.ofReal (x.toReal ^ n / Nat.factorial n) := by
      apply tsum_congr
      intro n
      rw [ENNReal.ofReal_div_of_pos (by positivity),
        ENNReal.ofReal_pow ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hx]
      norm_cast
    _ = ENNReal.ofReal (∑' n : ℕ, x.toReal ^ n / Nat.factorial n) := by
      rw [ENNReal.ofReal_tsum_of_nonneg (fun n ↦ div_nonneg (by positivity) (by positivity))
        hs.summable]
    _ = ENNReal.ofReal (Real.exp x.toReal) := by
      rw [hs.tsum_eq, Real.exp_eq_exp_ℝ]

/-- Series-form Markov bound: on `|C| ≥ n`, every moment term dominates its value at `n`. -/
theorem clusterSizeAtLeast_mul_exp_le_weightedExpMoment
    (d : ℕ) (p : unitInterval) (n : ℕ) (t : ℝ≥0∞) (ht : t ≠ ⊤) :
    (n : ℝ≥0∞) * clusterSizeAtLeastENNReal d p n *
        ENNReal.ofReal (Real.exp (t * (n : ℝ≥0∞)).toReal) ≤
      clusterSizeWeightedExpMoment d p t := by
  have htn : t * (n : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.mul_ne_top ht ENNReal.coe_ne_top
  rw [← tsum_pow_div_factorial_eq_ofReal_exp _ htn,
    clusterSizeWeightedExpMoment, ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro k
  calc
    (n : ℝ≥0∞) * clusterSizeAtLeastENNReal d p n *
        ((t * (n : ℝ≥0∞)) ^ k / (Nat.factorial k : ℝ≥0∞)) =
        t ^ k / (Nat.factorial k : ℝ≥0∞) *
          ((n : ℝ≥0∞) ^ (k + 1) * clusterSizeAtLeastENNReal d p n) := by
      rw [mul_pow, pow_succ]
      simp only [div_eq_mul_inv]
      ac_rfl
    _ ≤ t ^ k / (Nat.factorial k : ℝ≥0∞) *
        clusterSizeMomentENNReal d p (k + 1) :=
      mul_le_mul_left' (clusterSize_pow_mul_atLeast_le_moment d p n (k + 1)) _

/-- Equation (6.99) before dividing by the positive Markov denominator. -/
theorem clusterSizeAtLeast_mul_exp_le_sqrtBound
    (d : ℕ) (p : unitInterval) (n : ℕ) (t : ℝ≥0∞) (ht : t ≠ ⊤)
    (hsmall : 2 * (t * susceptibility d p ^ 2) < 1) :
    (n : ℝ≥0∞) * clusterSizeAtLeastENNReal d p n *
        ENNReal.ofReal (Real.exp (t * (n : ℝ≥0∞)).toReal) ≤
      susceptibility d p * ENNReal.ofReal
        (1 / (1 - 2 * (t * susceptibility d p ^ 2).toReal) ^ (1 / 2 : ℝ)) :=
  (clusterSizeAtLeast_mul_exp_le_weightedExpMoment d p n t ht).trans
    (clusterSize_expMoment_le d p t hsmall)


/-- Grimmett (6.77), with its exact constant and source threshold. -/
theorem clusterSizeAtLeast_le_two_exp_neg
    {d : ℕ} (hd : 0 < d) {p : unitInterval} (hp : 0 < (p : ℝ))
    (hchi : susceptibility d p < ⊤) (n : ℕ)
    (hn : (susceptibility d p).toReal ^ 2 < n) :
    clusterSizeAtLeast d p n ≤
      2 * Real.exp (-(1 / 2 : ℝ) * n / (susceptibility d p).toReal ^ 2) := by
  let chi := (susceptibility d p).toReal
  let t : ℝ := 1 / (2 * chi ^ 2) - 1 / (2 * n)
  have hchi_pos : 0 < chi := by
    dsimp [chi]
    exact zero_lt_one.trans (one_lt_susceptibility_toReal_of_pos hd hp hchi)
  have hn' : chi ^ 2 < (n : ℝ) := by simpa [chi] using hn
  have hn_pos : 0 < (n : ℝ) := lt_of_le_of_lt (sq_nonneg chi) hn'
  have ht_pos : 0 < t := by
    dsimp [t]
    rw [one_div, one_div, sub_pos]
    rw [inv_lt_inv₀ (by positivity) (by positivity)]
    nlinarith
  let te : ℝ≥0∞ := ENNReal.ofReal t
  have hchi_repr : susceptibility d p = ENNReal.ofReal chi := by
    symm
    exact ENNReal.ofReal_toReal hchi.ne
  have hsmall : 2 * (te * susceptibility d p ^ 2) < 1 := by
    rw [hchi_repr]
    dsimp only [te]
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by norm_num]
    rw [← ENNReal.ofReal_pow (le_of_lt hchi_pos),
      ← ENNReal.ofReal_mul (le_of_lt ht_pos),
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    rw [ENNReal.ofReal_lt_one]
    dsimp [t]
    field_simp
    nlinarith [hn]
  have hb := clusterSizeAtLeast_mul_exp_le_sqrtBound d p n te
    ENNReal.ofReal_ne_top hsmall
  have hrhs_top : susceptibility d p * ENNReal.ofReal
      (1 / (1 - 2 * (te * susceptibility d p ^ 2).toReal) ^ (1 / 2 : ℝ)) ≠ ⊤ :=
    ENNReal.mul_ne_top hchi.ne ENNReal.ofReal_ne_top
  have hbr := ENNReal.toReal_mono hrhs_top hb
  have hprob_nonneg : 0 ≤ clusterSizeAtLeast d p n := measureReal_nonneg
  have hbase_pos : 0 < 1 - 2 * (t * chi ^ 2) := by
    dsimp [t]
    field_simp
    nlinarith [sq_pos_of_pos hchi_pos]
  have hsqrt_nonneg : 0 ≤ 1 / (1 - 2 * (t * chi ^ 2)) ^ (1 / 2 : ℝ) := by positivity
  have hrpow_pos : 0 < (1 - 2 * (t * chi ^ 2)) ^ (1 / 2 : ℝ) :=
    Real.rpow_pos_of_pos hbase_pos _
  have htn_real : (te * (n : ℝ≥0∞)).toReal = t * n := by
    simp [te, ENNReal.toReal_ofReal ht_pos.le]
  have htchi_real : (te * susceptibility d p ^ 2).toReal = t * chi ^ 2 := by
    rw [hchi_repr]
    simp [te, ENNReal.toReal_ofReal ht_pos.le, ENNReal.toReal_ofReal hchi_pos.le]
  have hlhs_real :
      ((n : ℝ≥0∞) * clusterSizeAtLeastENNReal d p n *
        ENNReal.ofReal (Real.exp (te * (n : ℝ≥0∞)).toReal)).toReal =
        (n : ℝ) * clusterSizeAtLeast d p n * Real.exp (t * n) := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul,
      clusterSizeAtLeastENNReal_eq_ofReal,
      ENNReal.toReal_ofReal hprob_nonneg,
      ENNReal.toReal_ofReal (Real.exp_pos _).le, htn_real]
    norm_cast
  have hrhs_real :
      (susceptibility d p * ENNReal.ofReal
        (1 / (1 - 2 * (te * susceptibility d p ^ 2).toReal) ^ (1 / 2 : ℝ))).toReal =
        chi * (1 / (1 - 2 * (t * chi ^ 2)) ^ (1 / 2 : ℝ)) := by
    rw [ENNReal.toReal_mul, htchi_real, ENNReal.toReal_ofReal hsqrt_nonneg]
  have hbr' : (n : ℝ) * clusterSizeAtLeast d p n * Real.exp (t * n) ≤
      chi * (1 / (1 - 2 * (t * chi ^ 2)) ^ (1 / 2 : ℝ)) := by
    rw [← hlhs_real, ← hrhs_real]
    exact hbr
  have hbase_eq : 1 - 2 * (t * chi ^ 2) = chi ^ 2 / n := by
    dsimp [t]
    field_simp
    ring
  have htn_eq : t * n = n / (2 * chi ^ 2) - 1 / 2 := by
    dsimp [t]
    field_simp
  have hsqrt_n_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hn_pos
  have hrhs_eq :
      chi * (1 / (1 - 2 * (t * chi ^ 2)) ^ (1 / 2 : ℝ)) = Real.sqrt n := by
    rw [hbase_eq, ← Real.sqrt_eq_rpow, Real.sqrt_div (sq_nonneg chi),
      Real.sqrt_sq hchi_pos.le]
    field_simp
  have hbr_opt : (n : ℝ) * clusterSizeAtLeast d p n * Real.exp (t * n) ≤
      Real.sqrt n := by rwa [hrhs_eq] at hbr'
  have hn_nat : 0 < n := by exact_mod_cast hn_pos
  have hn_one : (1 : ℝ) ≤ n := by exact_mod_cast hn_nat
  have hsqrt_le_n : Real.sqrt (n : ℝ) ≤ n := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · nlinarith
  have hmark : clusterSizeAtLeast d p n * Real.exp (t * n) ≤ 1 := by
    have h := hbr_opt.trans hsqrt_le_n
    nlinarith
  have htail : clusterSizeAtLeast d p n ≤ Real.exp (-(t * n)) := by
    calc
      clusterSizeAtLeast d p n =
          (clusterSizeAtLeast d p n * Real.exp (t * n)) * Real.exp (-(t * n)) := by
        rw [mul_assoc, ← Real.exp_add]
        ring_nf
        simp
      _ ≤ 1 * Real.exp (-(t * n)) :=
        mul_le_mul_of_nonneg_right hmark (Real.exp_pos _).le
      _ = Real.exp (-(t * n)) := one_mul _
  have hexp_half_lt_two : Real.exp (1 / 2 : ℝ) < 2 := by
    have hsquare : Real.exp (1 / 2 : ℝ) ^ 2 = Real.exp 1 := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    nlinarith [Real.exp_one_lt_three, Real.exp_pos (1 / 2 : ℝ)]
  calc
    clusterSizeAtLeast d p n ≤ Real.exp (-(t * n)) := htail
    _ = Real.exp (1 / 2 : ℝ) *
        Real.exp (-(1 / 2 : ℝ) * n / chi ^ 2) := by
      rw [htn_eq, neg_sub, Real.exp_sub, div_eq_mul_inv, ← Real.exp_neg]
      congr 2
      field_simp
    _ ≤ 2 * Real.exp (-(1 / 2 : ℝ) * n / chi ^ 2) := by
      exact mul_le_mul_of_nonneg_right hexp_half_lt_two.le (Real.exp_pos _).le
    _ = 2 * Real.exp (-(1 / 2 : ℝ) * n /
        (susceptibility d p).toReal ^ 2) := by rfl

/-- Corrected source-facing form of Theorem 6.75.  The book says `n ≥ 1`, which is impossible
because `P(|C| ≥ 1) = 1`; the mathematically intended conclusion is eventual strict exponential
decay. -/
theorem clusterSizeAtLeast_exponential_decay_of_lt_critical
    (d : ℕ) (hd : 2 ≤ d) (p : unitInterval) (hp0 : 0 < (p : ℝ))
    (hp : (p : ℝ) < cubicCriticalProbability d) :
    ∃ lambda : ℝ, 0 < lambda ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      clusterSizeAtLeast d p n ≤ Real.exp (-lambda * n) := by
  have hchi := susceptibility_lt_top_of_lt_critical d hd p hp
  let chi := (susceptibility d p).toReal
  have hchi_pos : 0 < chi := by
    dsimp [chi]
    exact zero_lt_one.trans
      (one_lt_susceptibility_toReal_of_pos (Nat.zero_lt_of_lt hd) hp0 hchi)
  let lambda : ℝ := 1 / (4 * chi ^ 2)
  have hlambda : 0 < lambda := by dsimp [lambda]; positivity
  obtain ⟨N, hN⟩ := exists_nat_gt (max (chi ^ 2) (4 * chi ^ 2 * Real.log 2))
  refine ⟨lambda, hlambda, N, fun n hn ↦ ?_⟩
  have hnN : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hnchi : chi ^ 2 < (n : ℝ) :=
    ((le_max_left (chi ^ 2) (4 * chi ^ 2 * Real.log 2)).trans_lt hN).trans_le hnN
  have hlog : Real.log 2 ≤ (n : ℝ) / (4 * chi ^ 2) := by
    have haux : 4 * chi ^ 2 * Real.log 2 < (n : ℝ) :=
      ((le_max_right (chi ^ 2) (4 * chi ^ 2 * Real.log 2)).trans_lt hN).trans_le hnN
    apply (le_div_iff₀' (by positivity : (0 : ℝ) < 4 * chi ^ 2)).mpr
    exact haux.le
  calc
    clusterSizeAtLeast d p n ≤
        2 * Real.exp (-(1 / 2 : ℝ) * n / chi ^ 2) := by
      exact clusterSizeAtLeast_le_two_exp_neg
        (Nat.zero_lt_of_lt hd) hp0 hchi n (by simpa [chi] using hnchi)
    _ = Real.exp (Real.log 2 - (n : ℝ) / (2 * chi ^ 2)) := by
      calc
        2 * Real.exp (-(1 / 2 : ℝ) * n / chi ^ 2) =
            Real.exp (Real.log 2) * Real.exp (-(1 / 2 : ℝ) * n / chi ^ 2) := by
          rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
        _ = Real.exp (Real.log 2 + (-(1 / 2 : ℝ) * n / chi ^ 2)) :=
          (Real.exp_add _ _).symm
        _ = Real.exp (Real.log 2 - (n : ℝ) / (2 * chi ^ 2)) := by
          congr 1
          field_simp
          ring
    _ ≤ Real.exp (-(n : ℝ) / (4 * chi ^ 2)) := by
      rw [Real.exp_le_exp]
      have hhalf : (n : ℝ) / (2 * chi ^ 2) =
          2 * ((n : ℝ) / (4 * chi ^ 2)) := by field_simp; norm_num
      rw [hhalf]
      let A := (n : ℝ) / (4 * chi ^ 2)
      have hA : Real.log 2 ≤ A := by simpa [A] using hlog
      have : Real.log 2 - 2 * A ≤ -A := by linarith
      simpa [A, neg_div] using this
    _ = Real.exp (-lambda * n) := by
      congr 1
      dsimp [lambda]
      field_simp


#print axioms clusterSize_pow_mul_atLeast_le_moment
#print axioms tsum_pow_div_factorial_eq_ofReal_exp
#print axioms clusterSizeAtLeast_mul_exp_le_weightedExpMoment
#print axioms clusterSizeAtLeast_mul_exp_le_sqrtBound
#print axioms clusterSizeAtLeast_le_two_exp_neg
#print axioms clusterSizeAtLeast_exponential_decay_of_lt_critical

end Percolation
