import Percolation.Critical.SupercriticalDiameterGluing
import Percolation.Critical.ShiftedQuasiSubadditive

/-!
# Exponential rate of a finite supercritical cluster's diameter and radius

This file turns Lemma 8.27 into the generalized-subadditive limit in Theorem 8.18, and transfers
that rate from exact `L∞` diameter to Grimmett's finite box-radius event using (8.39)--(8.40).
-/

namespace Percolation

open Set MeasureTheory Filter Topology
open scoped BigOperators unitInterval

/-- Negative logarithm of the exact finite-cluster `L∞` diameter probability. -/
noncomputable def finiteClusterDiameterNegLog (d : ℕ) (p : I) (n : ℕ) : ℝ :=
  -Real.log (finiteClusterLInfDiameterProbability d p n)

/-- The logarithmic polynomial/finite-energy correction in Grimmett's equation (8.36). -/
noncomputable def finiteClusterDiameterLogCorrection (d : ℕ) (p : I) (n : ℕ) : ℝ :=
  -2 * Real.log (p : ℝ) - (2 * d - 2 : ℕ) * Real.log (1 - (p : ℝ)) +
    2 * Real.log (d : ℝ) + d * Real.log ((2 * n + 1 : ℕ) : ℝ)

theorem finiteClusterDiameterNegLog_nonneg
    {d : ℕ} (p : I) (n : ℕ) :
    0 ≤ finiteClusterDiameterNegLog d p n := by
  exact neg_nonneg.mpr (Real.log_nonpos
    (finiteClusterLInfDiameterProbability_nonneg d p n)
    measureReal_le_one)

theorem finiteClusterDiameterLogCorrection_nonneg
    {d : ℕ} (hd : 2 ≤ d) (p : I)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (n : ℕ) :
    0 ≤ finiteClusterDiameterLogCorrection d p n := by
  have hpLog : Real.log (p : ℝ) ≤ 0 := Real.log_nonpos hp0.le p.2.2
  have hq0 : 0 < 1 - (p : ℝ) := sub_pos.mpr hp1
  have hqLog : Real.log (1 - (p : ℝ)) ≤ 0 :=
    Real.log_nonpos hq0.le (by linarith [p.2.1])
  have hd1 : 1 ≤ d := by omega
  have hdLog : 0 ≤ Real.log (d : ℝ) := Real.log_nonneg (by exact_mod_cast hd1)
  have hnLog : 0 ≤ Real.log ((2 * n + 1 : ℕ) : ℝ) :=
    Real.log_nonneg (by norm_num)
  have hpTerm : 0 ≤ -2 * Real.log (p : ℝ) := by linarith
  have hqTerm : 0 ≤ -(2 * d - 2 : ℕ) * Real.log (1 - (p : ℝ)) := by
    exact mul_nonneg_of_nonpos_of_nonpos
      (neg_nonpos.mpr (Nat.cast_nonneg (2 * d - 2))) hqLog
  have hdTerm : 0 ≤ 2 * Real.log (d : ℝ) := mul_nonneg (by norm_num) hdLog
  have hnTerm : 0 ≤ (d : ℝ) * Real.log ((2 * n + 1 : ℕ) : ℝ) :=
    mul_nonneg (Nat.cast_nonneg d) hnLog
  unfold finiteClusterDiameterLogCorrection
  linarith

/-- Logarithmic form of Lemma 8.27, equation (8.36). -/
theorem finiteClusterDiameterNegLog_shifted_quasiSubadditive
    {d : ℕ} (hd : 2 ≤ d) (p : I)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (m n : ℕ) :
    finiteClusterDiameterNegLog d p (m + n + 2) ≤
      finiteClusterDiameterNegLog d p m + finiteClusterDiameterNegLog d p n +
        finiteClusterDiameterLogCorrection d p n := by
  let q : ℝ := 1 - (p : ℝ)
  let P : ℕ → ℝ := finiteClusterLInfDiameterProbability d p
  have hq0 : 0 < q := sub_pos.mpr hp1
  have hPm : 0 < P m := finiteClusterLInfDiameterProbability_pos hd p hp0 hp1 m
  have hPn : 0 < P n := finiteClusterLInfDiameterProbability_pos hd p hp0 hp1 n
  have hPout : 0 < P (m + n + 2) :=
    finiteClusterLInfDiameterProbability_pos hd p hp0 hp1 _
  have hdR : 0 < (d : ℝ) := by positivity
  have hbox : 0 < (((2 * n + 1 : ℕ) ^ d : ℕ) : ℝ) := by positivity
  have hc : 0 < (p : ℝ) ^ 2 * q ^ (2 * d - 2) := by positivity
  have hden : 0 < (d : ℝ) ^ 2 * (((2 * n + 1 : ℕ) ^ d : ℕ) : ℝ) := by
    positivity
  have hprob : (p : ℝ) ^ 2 * q ^ (2 * d - 2) * P m * P n ≤
      (d : ℝ) ^ 2 * (((2 * n + 1 : ℕ) ^ d : ℕ) : ℝ) * P (m + n + 2) := by
    simpa only [q, P, Nat.cast_pow] using
      sourcePenalty_mul_finiteClusterLInfDiameterProbabilities_le
        hd p hp0 hp1 m n
  have hlog := Real.log_le_log (mul_pos (mul_pos hc hPm) hPn) hprob
  have hleft : Real.log ((p : ℝ) ^ 2 * q ^ (2 * d - 2) * P m * P n) =
      2 * Real.log (p : ℝ) + (2 * d - 2 : ℕ) * Real.log q +
        Real.log (P m) + Real.log (P n) := by
    rw [Real.log_mul (mul_pos hc hPm).ne' hPn.ne',
      Real.log_mul hc.ne' hPm.ne',
      Real.log_mul (pow_pos hp0 2).ne' (pow_pos hq0 (2 * d - 2)).ne',
      Real.log_pow, Real.log_pow]
    ring
  have hright : Real.log
      ((d : ℝ) ^ 2 * (((2 * n + 1 : ℕ) ^ d : ℕ) : ℝ) * P (m + n + 2)) =
      2 * Real.log (d : ℝ) + d * Real.log ((2 * n + 1 : ℕ) : ℝ) +
        Real.log (P (m + n + 2)) := by
    rw [Real.log_mul hden.ne' hPout.ne',
      Real.log_mul (pow_pos hdR 2).ne' hbox.ne', Real.log_pow]
    norm_num only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    rw [Real.log_pow]
  rw [hleft, hright] at hlog
  change -Real.log (P (m + n + 2)) ≤
    -Real.log (P m) + -Real.log (P n) +
      (-2 * Real.log (p : ℝ) - (2 * d - 2 : ℕ) * Real.log q +
        2 * Real.log (d : ℝ) + d * Real.log ((2 * n + 1 : ℕ) : ℝ))
  linarith

theorem finiteClusterDiameterLogCorrection_sublinear
    {d : ℕ} (p : I) :
    Tendsto (fun n : ℕ ↦ finiteClusterDiameterLogCorrection d p n / n)
      atTop (nhds 0) := by
  let C : ℝ := -2 * Real.log (p : ℝ) -
    (2 * d - 2 : ℕ) * Real.log (1 - (p : ℝ)) + 2 * Real.log (d : ℝ)
  have hconst : Tendsto (fun n : ℕ ↦ C / (n : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hinput : Tendsto (fun n : ℕ ↦ 2 * (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1
      (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num))
  have hreal : Tendsto
      (fun x : ℝ ↦ Real.log x ^ 1 / ((1 / 2 : ℝ) * x + (-1 / 2)))
      atTop (nhds 0) :=
    Real.tendsto_pow_log_div_mul_add_atTop (1 / 2 : ℝ) (-1 / 2) 1 (by norm_num)
  have hlog : Tendsto
      (fun n : ℕ ↦ Real.log ((2 * n + 1 : ℕ) : ℝ) / (n : ℝ))
      atTop (nhds 0) := by
    have hcomp := hreal.comp hinput
    convert hcomp using 1
    funext n
    congr 1
    · norm_num
    · ring
  have hsum : Tendsto
      (fun n : ℕ ↦ C / (n : ℝ) + (d : ℝ) *
        (Real.log ((2 * n + 1 : ℕ) : ℝ) / (n : ℝ)))
      atTop (nhds 0) := by
    simpa using hconst.add (hlog.const_mul (d : ℝ))
  convert hsum using 1
  funext n
  unfold finiteClusterDiameterLogCorrection
  dsimp only [C]
  ring

/-- Diameter decay rate appearing in Theorem 8.18. -/
noncomputable def finiteClusterRadiusDecayRate (d : ℕ) (p : I) : ℝ :=
  shiftedQuasiSubadditiveRate
    (finiteClusterDiameterNegLog d p) (finiteClusterDiameterLogCorrection d p)

/-- Equation (8.37): the exact finite-diameter negative logarithm has a linear rate. -/
theorem finiteClusterLInfDiameterProbability_logRate_tendsto
    {d : ℕ} (hd : 2 ≤ d) (p : I)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    Tendsto (fun n : ℕ ↦
      -Real.log (finiteClusterLInfDiameterProbability d p n) / n) atTop
      (nhds (finiteClusterRadiusDecayRate d p)) := by
  exact tendsto_div_shiftedQuasiSubadditiveRate
    (finiteClusterDiameterNegLog_nonneg p)
    (finiteClusterDiameterLogCorrection_nonneg hd p hp0 hp1)
    (finiteClusterDiameterNegLog_shifted_quasiSubadditive hd p hp0 hp1)
    (finiteClusterDiameterLogCorrection_sublinear p)

/-- The finite-index negative-log estimate following (8.37). -/
theorem finiteClusterDiameter_rate_mul_sub_correction_le_negLog
    {d : ℕ} (hd : 2 ≤ d) (p : I)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (k : ℕ) :
    (k + 2 : ℝ) * finiteClusterRadiusDecayRate d p -
        finiteClusterDiameterLogCorrection d p k ≤
      finiteClusterDiameterNegLog d p k := by
  exact add_mul_shiftedQuasiSubadditiveRate_sub_error_le
    (finiteClusterDiameterNegLog_nonneg p)
    (finiteClusterDiameterLogCorrection_nonneg hd p hp0 hp1) k

private theorem exp_finiteClusterDiameterLogCorrection
    {d : ℕ} (hd : 2 ≤ d) (p : I)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (k : ℕ) :
    Real.exp (finiteClusterDiameterLogCorrection d p k) =
      (d : ℝ) ^ 2 * (((2 * k + 1 : ℕ) : ℝ) ^ d) /
        ((p : ℝ) ^ 2 * (1 - (p : ℝ)) ^ (2 * d - 2)) := by
  have hq0 : 0 < 1 - (p : ℝ) := sub_pos.mpr hp1
  have hd0 : 0 < (d : ℝ) := by positivity
  have hk0 : 0 < (((2 * k + 1 : ℕ) : ℝ)) := by positivity
  unfold finiteClusterDiameterLogCorrection
  rw [show
      -2 * Real.log (p : ℝ) - (2 * d - 2 : ℕ) * Real.log (1 - (p : ℝ)) +
          2 * Real.log (d : ℝ) + d * Real.log ((2 * k + 1 : ℕ) : ℝ) =
        -(2 * Real.log (p : ℝ)) +
          (-((2 * d - 2 : ℕ) * Real.log (1 - (p : ℝ))) +
            (2 * Real.log (d : ℝ) +
              d * Real.log ((2 * k + 1 : ℕ) : ℝ))) by ring]
  rw [Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_neg, Real.exp_neg,
    Real.exp_nat_mul, Real.exp_nat_mul, Real.exp_log hq0, Real.exp_log hk0]
  have hpExp : Real.exp (2 * Real.log (p : ℝ)) = (p : ℝ) ^ 2 := by
    rw [show 2 * Real.log (p : ℝ) =
      Real.log (p : ℝ) + Real.log (p : ℝ) by ring, Real.exp_add,
      Real.exp_log hp0]
    ring
  have hdExp : Real.exp (2 * Real.log (d : ℝ)) = (d : ℝ) ^ 2 := by
    rw [show 2 * Real.log (d : ℝ) =
      Real.log (d : ℝ) + Real.log (d : ℝ) by ring, Real.exp_add,
      Real.exp_log hd0]
    ring
  rw [hpExp, hdExp]
  field_simp

/-- Equation (8.38), with the exact source prefactor. -/
theorem finiteClusterLInfDiameterProbability_le_rate
    {d : ℕ} (hd : 2 ≤ d) (p : I)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (k : ℕ) :
    finiteClusterLInfDiameterProbability d p k ≤
      ((d : ℝ) ^ 2 /
          ((p : ℝ) ^ 2 * (1 - (p : ℝ)) ^ (2 * d - 2))) *
        (((2 * k + 1 : ℕ) : ℝ) ^ d) *
          Real.exp (-(k + 2 : ℝ) * finiteClusterRadiusDecayRate d p) := by
  let P := finiteClusterLInfDiameterProbability d p k
  let a := finiteClusterRadiusDecayRate d p
  have hP : 0 < P := finiteClusterLInfDiameterProbability_pos hd p hp0 hp1 k
  have hrate := finiteClusterDiameter_rate_mul_sub_correction_le_negLog
    hd p hp0 hp1 k
  have hlog : Real.log P ≤
      finiteClusterDiameterLogCorrection d p k - (k + 2 : ℝ) * a := by
    change (k + 2 : ℝ) * a - finiteClusterDiameterLogCorrection d p k ≤
      -Real.log P at hrate
    linarith
  have hexp := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log hP] at hexp
  calc
    P ≤ Real.exp (finiteClusterDiameterLogCorrection d p k -
        (k + 2 : ℝ) * a) := hexp
    _ = Real.exp (finiteClusterDiameterLogCorrection d p k) *
        Real.exp (-(k + 2 : ℝ) * a) := by
      rw [sub_eq_add_neg, Real.exp_add]
      congr 2
      ring
    _ = ((d : ℝ) ^ 2 /
          ((p : ℝ) ^ 2 * (1 - (p : ℝ)) ^ (2 * d - 2))) *
        (((2 * k + 1 : ℕ) : ℝ) ^ d) *
          Real.exp (-(k + 2 : ℝ) * finiteClusterRadiusDecayRate d p) := by
      rw [exp_finiteClusterDiameterLogCorrection hd p hp0 hp1 k]
      simp only [a]
      ring

/-- The diameter rate is nonnegative throughout `0 < p < 1`. -/
theorem finiteClusterRadiusDecayRate_nonneg
    {d : ℕ} (hd : 2 ≤ d) (p : I)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    0 ≤ finiteClusterRadiusDecayRate d p := by
  have hzero : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (nhds 0) := tendsto_const_nhds
  have hlimit := finiteClusterLInfDiameterProbability_logRate_tendsto hd p hp0 hp1
  have hnonneg : ∀ᶠ n : ℕ in atTop,
      0 ≤ -Real.log (finiteClusterLInfDiameterProbability d p n) / (n : ℝ) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hprob := finiteClusterLInfDiameterProbability_pos hd p hp0 hp1 n
    have hlog := Real.log_nonpos hprob.le measureReal_le_one
    exact div_nonneg (neg_nonneg.mpr hlog) (by positivity)
  exact le_of_tendsto_of_tendsto hzero hlimit hnonneg

theorem pairwiseDisjoint_finiteClusterLInfDiameterEvent (d : ℕ) :
    Pairwise (Function.onFun Disjoint (finiteClusterLInfDiameterEvent d)) := by
  intro m n hmn
  change Disjoint (finiteClusterLInfDiameterEvent d m)
    (finiteClusterLInfDiameterEvent d n)
  rw [Set.disjoint_left]
  intro omega hm hn
  have hm' := mem_finiteClusterLInfDiameterEvent_iff.mp hm
  have hn' := mem_finiteClusterLInfDiameterEvent_iff.mp hn
  exact hmn (hm'.2.symm.trans hn'.2)

theorem summable_finiteClusterLInfDiameterProbability (d : ℕ) (p : I) :
    Summable (finiteClusterLInfDiameterProbability d p) := by
  apply summable_of_sum_le (finiteClusterLInfDiameterProbability_nonneg d p)
  intro s
  have hpair : Set.PairwiseDisjoint (s : Set ℕ) (finiteClusterLInfDiameterEvent d) := by
    intro m _hm n _hn hmn
    exact pairwiseDisjoint_finiteClusterLInfDiameterEvent d hmn
  have hsum := measureReal_biUnion_finset
    (μ := bernoulliBondMeasure d p) hpair
    (fun n _hn ↦ measurableSet_finiteClusterLInfDiameterEvent d n)
  calc
    ∑ n ∈ s, finiteClusterLInfDiameterProbability d p n =
        (bernoulliBondMeasure d p).real
          (⋃ n ∈ s, finiteClusterLInfDiameterEvent d n) := hsum.symm
    _ ≤ (bernoulliBondMeasure d p).real Set.univ :=
      measureReal_mono (Set.subset_univ _)
    _ = 1 := probReal_univ

theorem finiteClusterLInfDiameterTailEvent_eq_iUnion_add (d n : ℕ) :
    finiteClusterLInfDiameterTailEvent d n =
      ⋃ k : ℕ, finiteClusterLInfDiameterEvent d (k + n) := by
  ext omega
  constructor
  · intro homega
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp homega
    exact Set.mem_iUnion.mpr ⟨k.1 - n, by simpa [Nat.sub_add_cancel k.2] using hk⟩
  · intro homega
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp homega
    exact Set.mem_iUnion.mpr ⟨⟨k + n, Nat.le_add_left n k⟩, hk⟩

/-- The finite-diameter tail is the sum of the disjoint exact-diameter probabilities. -/
theorem finiteClusterLInfDiameterTailProbability_eq_tsum_add
    (d : ℕ) (p : I) (n : ℕ) :
    finiteClusterLInfDiameterTailProbability d p n =
      ∑' k : ℕ, finiteClusterLInfDiameterProbability d p (k + n) := by
  rw [finiteClusterLInfDiameterTailProbability,
    finiteClusterLInfDiameterTailEvent_eq_iUnion_add]
  rw [measureReal_def,
    measure_iUnion (μ := bernoulliBondMeasure d p)
      (by
        intro k l hkl
        exact pairwiseDisjoint_finiteClusterLInfDiameterEvent d (by omega))
      (fun k ↦ measurableSet_finiteClusterLInfDiameterEvent d (k + n)),
    ENNReal.tsum_toReal_eq]
  · rfl
  · intro k
    exact measure_ne_top _ _

theorem finiteClusterLInfDiameterProbability_le_tailProbability
    (d : ℕ) (p : I) (n : ℕ) :
    finiteClusterLInfDiameterProbability d p n ≤
      finiteClusterLInfDiameterTailProbability d p n := by
  unfold finiteClusterLInfDiameterProbability finiteClusterLInfDiameterTailProbability
  exact measureReal_mono (by
    intro omega homega
    exact Set.mem_iUnion.mpr ⟨⟨n, le_rfl⟩, homega⟩) (measure_ne_top _ _)

theorem finiteClusterLInfDiameterTailProbability_pos
    {d : ℕ} (hd : 2 ≤ d) (p : I)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (n : ℕ) :
    0 < finiteClusterLInfDiameterTailProbability d p n :=
  (finiteClusterLInfDiameterProbability_pos hd p hp0 hp1 n).trans_le
    (finiteClusterLInfDiameterProbability_le_tailProbability d p n)

noncomputable def diameterPolynomialGeometricMoment (d : ℕ) (r : ℝ) : ℝ :=
  ∑' k : ℕ, (((2 * k + 1 : ℕ) : ℝ) ^ d) * r ^ k

private theorem summable_succ_pow_mul_geometric
    {d : ℕ} {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable fun k : ℕ ↦ (((k + 1 : ℕ) : ℝ) ^ d) * r ^ k := by
  have hrnorm : ‖r‖ < 1 := by
    simpa [Real.norm_eq_abs, abs_of_nonneg hr0] using hr1
  have hbase : Summable fun k : ℕ ↦ ((k : ℝ) ^ d) * r ^ k :=
    summable_pow_mul_geometric_of_norm_lt_one d hrnorm
  have hgeom : Summable fun k : ℕ ↦ r ^ k := summable_geometric_of_norm_lt_one hrnorm
  have hmajorant : Summable fun k : ℕ ↦
      r ^ k + (2 : ℝ) ^ d * (((k : ℝ) ^ d) * r ^ k) :=
    hgeom.add (hbase.mul_left ((2 : ℝ) ^ d))
  apply hmajorant.of_nonneg_of_le
  · intro k
    positivity
  · intro k
    by_cases hk : k = 0
    · subst k
      simp
    · have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
      have hadd : ((k + 1 : ℕ) : ℝ) ≤ 2 * (k : ℝ) := by
        push_cast
        linarith
      have hpow : (((k + 1 : ℕ) : ℝ) ^ d) ≤ (2 * (k : ℝ)) ^ d :=
        pow_le_pow_left₀ (by positivity) hadd d
      rw [mul_pow] at hpow
      have hmul := mul_le_mul_of_nonneg_right hpow (pow_nonneg hr0 k)
      calc
        (((k + 1 : ℕ) : ℝ) ^ d) * r ^ k ≤
            ((2 : ℝ) ^ d * (k : ℝ) ^ d) * r ^ k := hmul
        _ ≤ r ^ k + (2 : ℝ) ^ d * (((k : ℝ) ^ d) * r ^ k) := by
          rw [mul_assoc]
          exact le_add_of_nonneg_left (pow_nonneg hr0 k)

theorem summable_diameterPolynomialGeometricMoment
    {d : ℕ} {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable fun k : ℕ ↦ (((2 * k + 1 : ℕ) : ℝ) ^ d) * r ^ k := by
  have hbase := summable_succ_pow_mul_geometric (d := d) hr0 hr1
  have hmajorant : Summable fun k : ℕ ↦
      (2 : ℝ) ^ d * ((((k + 1 : ℕ) : ℝ) ^ d) * r ^ k) :=
    hbase.mul_left ((2 : ℝ) ^ d)
  apply hmajorant.of_nonneg_of_le
  · intro k
    positivity
  · intro k
    have hlin : (((2 * k + 1 : ℕ) : ℝ)) ≤
        2 * (((k + 1 : ℕ) : ℝ)) := by
      push_cast
      linarith
    have hpow := pow_le_pow_left₀ (by positivity) hlin d
    rw [mul_pow] at hpow
    nlinarith [pow_nonneg hr0 k]

theorem diameterPolynomialGeometricMoment_pos
    {d : ℕ} {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    0 < diameterPolynomialGeometricMoment d r := by
  rw [diameterPolynomialGeometricMoment]
  have hs := summable_diameterPolynomialGeometricMoment (d := d) hr0 hr1
  apply lt_of_lt_of_le zero_lt_one
  have hle := hs.sum_le_tsum ({0} : Finset ℕ) (fun k _hk ↦ by positivity)
  simpa using hle

/-- Summed form of (8.38), used in (8.42). -/
theorem finiteClusterLInfDiameterTailProbability_le_rate_prefactor_of_rate_pos
    {d : ℕ} (hd : 2 ≤ d) (p : I)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (ha : 0 < finiteClusterRadiusDecayRate d p) (n : ℕ) :
    finiteClusterLInfDiameterTailProbability d p n ≤
      (((d : ℝ) ^ 2 /
          ((p : ℝ) ^ 2 * (1 - (p : ℝ)) ^ (2 * d - 2))) *
        (((2 * n + 1 : ℕ) : ℝ) ^ d) *
          Real.exp (-(n + 2 : ℝ) * finiteClusterRadiusDecayRate d p)) *
        diameterPolynomialGeometricMoment d
          (Real.exp (-finiteClusterRadiusDecayRate d p)) := by
  let a := finiteClusterRadiusDecayRate d p
  let r := Real.exp (-a)
  let K := (d : ℝ) ^ 2 /
    ((p : ℝ) ^ 2 * (1 - (p : ℝ)) ^ (2 * d - 2))
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := by
    dsimp only [r, a]
    rw [Real.exp_lt_one_iff]
    linarith
  have hK : 0 ≤ K := by positivity
  have hsource : Summable (fun k : ℕ ↦
      finiteClusterLInfDiameterProbability d p (k + n)) :=
    (summable_nat_add_iff n).mpr (summable_finiteClusterLInfDiameterProbability d p)
  have hmoment := summable_diameterPolynomialGeometricMoment (d := d) hr0 hr1
  let C := K * (((2 * n + 1 : ℕ) : ℝ) ^ d) * Real.exp (-(n + 2 : ℝ) * a)
  have htarget : Summable (fun k : ℕ ↦
      C * ((((2 * k + 1 : ℕ) : ℝ) ^ d) * r ^ k)) := hmoment.mul_left C
  have hterm (k : ℕ) :
      finiteClusterLInfDiameterProbability d p (k + n) ≤
        C * ((((2 * k + 1 : ℕ) : ℝ) ^ d) * r ^ k) := by
    have hrate := finiteClusterLInfDiameterProbability_le_rate
      hd p hp0 hp1 (k + n)
    have hnat : 2 * (k + n) + 1 ≤ (2 * n + 1) * (2 * k + 1) := by
      nlinarith [Nat.zero_le (k * n)]
    have hreal : (((2 * (k + n) + 1 : ℕ) : ℝ)) ≤
        (((2 * n + 1 : ℕ) : ℝ)) * (((2 * k + 1 : ℕ) : ℝ)) := by
      exact_mod_cast hnat
    have hpoly := pow_le_pow_left₀ (by positivity) hreal d
    rw [mul_pow] at hpoly
    have hexp : Real.exp (-(k + n + 2 : ℝ) * a) =
        Real.exp (-(n + 2 : ℝ) * a) * r ^ k := by
      rw [show -(k + n + 2 : ℝ) * a =
          -(n + 2 : ℝ) * a + (k : ℝ) * (-a) by
        ring, Real.exp_add, Real.exp_nat_mul]
    have hrate' : finiteClusterLInfDiameterProbability d p (k + n) ≤
        K * (((2 * (k + n) + 1 : ℕ) : ℝ) ^ d) *
          Real.exp (-(k + n + 2 : ℝ) * a) := by
      simpa only [K, a, Nat.cast_add] using hrate
    rw [hexp] at hrate'
    calc
      finiteClusterLInfDiameterProbability d p (k + n) ≤
          K * (((2 * (k + n) + 1 : ℕ) : ℝ) ^ d) *
            (Real.exp (-(n + 2 : ℝ) * a) * r ^ k) := hrate'
      _ ≤ K *
          ((((2 * n + 1 : ℕ) : ℝ) ^ d) * (((2 * k + 1 : ℕ) : ℝ) ^ d) *
            (Real.exp (-(n + 2 : ℝ) * a) * r ^ k)) := by
        have hE : 0 ≤ Real.exp (-(n + 2 : ℝ) * a) * r ^ k :=
          mul_nonneg (Real.exp_pos _).le (pow_nonneg hr0 k)
        have hpolyE := mul_le_mul_of_nonneg_right hpoly hE
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hpolyE hK
      _ = C * ((((2 * k + 1 : ℕ) : ℝ) ^ d) * r ^ k) := by
        dsimp only [C]
        ring
  rw [finiteClusterLInfDiameterTailProbability_eq_tsum_add]
  calc
    (∑' k : ℕ, finiteClusterLInfDiameterProbability d p (k + n)) ≤
        ∑' k : ℕ, C * ((((2 * k + 1 : ℕ) : ℝ) ^ d) * r ^ k) :=
      hsource.tsum_le_tsum hterm htarget
    _ = C * diameterPolynomialGeometricMoment d r := by
      rw [hmoment.tsum_mul_left]
      rfl
    _ = (((d : ℝ) ^ 2 /
          ((p : ℝ) ^ 2 * (1 - (p : ℝ)) ^ (2 * d - 2))) *
        (((2 * n + 1 : ℕ) : ℝ) ^ d) *
          Real.exp (-(n + 2 : ℝ) * finiteClusterRadiusDecayRate d p)) *
        diameterPolynomialGeometricMoment d
          (Real.exp (-finiteClusterRadiusDecayRate d p)) := by rfl

theorem tendsto_log_two_mul_add_one_div_nat :
    Tendsto (fun n : ℕ ↦ Real.log ((2 * n + 1 : ℕ) : ℝ) / (n : ℝ))
      atTop (nhds 0) := by
  have hinput : Tendsto (fun n : ℕ ↦ 2 * (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1
      (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num))
  have hreal : Tendsto
      (fun x : ℝ ↦ Real.log x ^ 1 / ((1 / 2 : ℝ) * x + (-1 / 2)))
      atTop (nhds 0) :=
    Real.tendsto_pow_log_div_mul_add_atTop (1 / 2 : ℝ) (-1 / 2) 1 (by norm_num)
  have hcomp := hreal.comp hinput
  convert hcomp using 1
  funext n
  congr 1
  · norm_num
  · ring

/-- The finite-diameter tail has the same logarithmic rate as the exact-diameter law. -/
theorem finiteClusterLInfDiameterTailProbability_logRate_tendsto
    {d : ℕ} (hd : 2 ≤ d) (p : I)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    Tendsto (fun n : ℕ ↦
      -Real.log (finiteClusterLInfDiameterTailProbability d p n) / n) atTop
      (nhds (finiteClusterRadiusDecayRate d p)) := by
  let a := finiteClusterRadiusDecayRate d p
  by_cases ha0 : a = 0
  · have hexact := finiteClusterLInfDiameterProbability_logRate_tendsto hd p hp0 hp1
    have hzero : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (nhds a) := by
      rw [ha0]
      exact tendsto_const_nhds
    have hlower : ∀ᶠ n : ℕ in atTop,
        0 ≤ -Real.log (finiteClusterLInfDiameterTailProbability d p n) / (n : ℝ) := by
      filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
      have htail := finiteClusterLInfDiameterTailProbability_pos hd p hp0 hp1 n
      have htailOne : finiteClusterLInfDiameterTailProbability d p n ≤ 1 :=
        measureReal_le_one
      exact div_nonneg (neg_nonneg.mpr (Real.log_nonpos htail.le htailOne)) (by positivity)
    have hupper : ∀ᶠ n : ℕ in atTop,
        -Real.log (finiteClusterLInfDiameterTailProbability d p n) / (n : ℝ) ≤
          -Real.log (finiteClusterLInfDiameterProbability d p n) / (n : ℝ) := by
      filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
      have hprob := finiteClusterLInfDiameterProbability_pos hd p hp0 hp1 n
      have hle := finiteClusterLInfDiameterProbability_le_tailProbability d p n
      exact div_le_div_of_nonneg_right (neg_le_neg (Real.log_le_log hprob hle))
        (by positivity)
    exact hzero.squeeze' hexact hlower hupper
  · have ha : 0 < a := lt_of_le_of_ne
      (finiteClusterRadiusDecayRate_nonneg hd p hp0 hp1) (Ne.symm ha0)
    let r := Real.exp (-a)
    let K := (d : ℝ) ^ 2 /
      ((p : ℝ) ^ 2 * (1 - (p : ℝ)) ^ (2 * d - 2))
    let M := diameterPolynomialGeometricMoment d r
    let D := K * M * Real.exp (-2 * a)
    have hr0 : 0 ≤ r := (Real.exp_pos _).le
    have hr1 : r < 1 := by
      dsimp only [r]
      rw [Real.exp_lt_one_iff]
      linarith
    have hK : 0 < K := by positivity
    have hM : 0 < M := diameterPolynomialGeometricMoment_pos hr0 hr1
    have hD : 0 < D := mul_pos (mul_pos hK hM) (Real.exp_pos _)
    have hlogPref : Tendsto (fun n : ℕ ↦
        Real.log (D * (((2 * n + 1 : ℕ) : ℝ) ^ d)) / (n : ℝ))
        atTop (nhds 0) := by
      have hconst := tendsto_const_div_atTop_nhds_zero_nat (Real.log D)
      have hpoly := tendsto_log_two_mul_add_one_div_nat.const_mul (d : ℝ)
      have hsum : Tendsto (fun n : ℕ ↦
          Real.log D / (n : ℝ) +
            (d : ℝ) * (Real.log ((2 * n + 1 : ℕ) : ℝ) / (n : ℝ)))
          atTop (nhds 0) := by simpa using hconst.add hpoly
      apply hsum.congr'
      filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
      have hbase : 0 < (((2 * n + 1 : ℕ) : ℝ)) := by positivity
      rw [Real.log_mul hD.ne' (pow_pos hbase d).ne', Real.log_pow]
      field_simp
    have hlowerT : Tendsto (fun n : ℕ ↦
        a - Real.log (D * (((2 * n + 1 : ℕ) : ℝ) ^ d)) / (n : ℝ))
        atTop (nhds a) := by
      simpa using tendsto_const_nhds.sub hlogPref
    have hupperT := finiteClusterLInfDiameterProbability_logRate_tendsto hd p hp0 hp1
    have hlower : ∀ᶠ n : ℕ in atTop,
        a - Real.log (D * (((2 * n + 1 : ℕ) : ℝ) ^ d)) / (n : ℝ) ≤
          -Real.log (finiteClusterLInfDiameterTailProbability d p n) / n := by
      filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
      have htail := finiteClusterLInfDiameterTailProbability_pos hd p hp0 hp1 n
      have hbound0 := finiteClusterLInfDiameterTailProbability_le_rate_prefactor_of_rate_pos
        hd p hp0 hp1 (by simpa [a] using ha) n
      have hbound : finiteClusterLInfDiameterTailProbability d p n ≤
          D * (((2 * n + 1 : ℕ) : ℝ) ^ d) * Real.exp (-(n : ℝ) * a) := by
        calc
          finiteClusterLInfDiameterTailProbability d p n ≤
              ((K * (((2 * n + 1 : ℕ) : ℝ) ^ d) *
                Real.exp (-(n + 2 : ℝ) * a)) * M) := by
            simpa only [K, M, a, r] using hbound0
          _ = D * (((2 * n + 1 : ℕ) : ℝ) ^ d) * Real.exp (-(n : ℝ) * a) := by
            rw [show Real.exp (-(n + 2 : ℝ) * a) =
                Real.exp (-2 * a) * Real.exp (-(n : ℝ) * a) by
              rw [← Real.exp_add]
              congr 1
              ring]
            dsimp only [D]
            ring
      have hright : 0 < D * (((2 * n + 1 : ℕ) : ℝ) ^ d) *
          Real.exp (-(n : ℝ) * a) := by positivity
      have hlog := Real.log_le_log htail hbound
      rw [Real.log_mul (mul_pos hD (pow_pos (by positivity) d)).ne'
          (Real.exp_ne_zero _), Real.log_exp] at hlog
      have hnreal : (0 : ℝ) < n := by positivity
      rw [le_div_iff₀ hnreal]
      field_simp
      nlinarith
    have hupper : ∀ᶠ n : ℕ in atTop,
        -Real.log (finiteClusterLInfDiameterTailProbability d p n) / n ≤
          -Real.log (finiteClusterLInfDiameterProbability d p n) / n := by
      filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
      have hprob := finiteClusterLInfDiameterProbability_pos hd p hp0 hp1 n
      have hle := finiteClusterLInfDiameterProbability_le_tailProbability d p n
      exact div_le_div_of_nonneg_right (neg_le_neg (Real.log_le_log hprob hle))
        (by positivity)
    exact hlowerT.squeeze' hupperT hlower hupper

theorem finiteBoxRadiusProbability_pos
    {d : ℕ} (hd : 2 ≤ d) (p : I)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (n : ℕ) :
    0 < finiteBoxRadiusProbability d p n := by
  have hq := finiteClusterLInfDiameterProbability_pos hd p hp0 hp1 n
  have hle := finiteClusterLInfDiameterProbability_le_radius_prefactor
    (Nat.zero_lt_of_lt hd) p n
  have hfactor : 0 ≤ (d : ℝ) * (((2 * n + 1 : ℕ) : ℝ) ^ d) := by positivity
  exact pos_of_mul_pos_right (hq.trans_le hle) hfactor

/-- **Grimmett, Theorem 8.18, equation (8.19).**  The finite box-radius probability has the
same logarithmic decay rate as the exact finite-diameter law. -/
theorem finiteBoxRadiusProbability_logRate_tendsto
    {d : ℕ} (hd : 2 ≤ d) (p : I)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    Tendsto (fun n : ℕ ↦ -Real.log (finiteBoxRadiusProbability d p n) / n) atTop
      (nhds (finiteClusterRadiusDecayRate d p)) := by
  let a := finiteClusterRadiusDecayRate d p
  have hlowerT := finiteClusterLInfDiameterTailProbability_logRate_tendsto hd p hp0 hp1
  have hexact := finiteClusterLInfDiameterProbability_logRate_tendsto hd p hp0 hp1
  have hdR : 0 < (d : ℝ) := by positivity
  have hlogPref : Tendsto (fun n : ℕ ↦
      Real.log ((d : ℝ) * (((2 * n + 1 : ℕ) : ℝ) ^ d)) / (n : ℝ))
      atTop (nhds 0) := by
    have hconst := tendsto_const_div_atTop_nhds_zero_nat (Real.log (d : ℝ))
    have hpoly := tendsto_log_two_mul_add_one_div_nat.const_mul (d : ℝ)
    have hsum : Tendsto (fun n : ℕ ↦
        Real.log (d : ℝ) / (n : ℝ) +
          (d : ℝ) * (Real.log ((2 * n + 1 : ℕ) : ℝ) / (n : ℝ)))
        atTop (nhds 0) := by simpa using hconst.add hpoly
    apply hsum.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hbase : 0 < (((2 * n + 1 : ℕ) : ℝ)) := by positivity
    rw [Real.log_mul hdR.ne' (pow_pos hbase d).ne', Real.log_pow]
    field_simp
  have hupperT : Tendsto (fun n : ℕ ↦
      -Real.log (finiteClusterLInfDiameterProbability d p n) / n +
        Real.log ((d : ℝ) * (((2 * n + 1 : ℕ) : ℝ) ^ d)) / n)
      atTop (nhds a) := by
    simpa [a] using hexact.add hlogPref
  have hlower : ∀ᶠ n : ℕ in atTop,
      -Real.log (finiteClusterLInfDiameterTailProbability d p n) / n ≤
        -Real.log (finiteBoxRadiusProbability d p n) / n := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hradius := finiteBoxRadiusProbability_pos hd p hp0 hp1 n
    have hle := finiteBoxRadiusProbability_le_finiteClusterLInfDiameterTailProbability d p n
    exact div_le_div_of_nonneg_right (neg_le_neg (Real.log_le_log hradius hle))
      (by positivity)
  have hupper : ∀ᶠ n : ℕ in atTop,
      -Real.log (finiteBoxRadiusProbability d p n) / n ≤
        -Real.log (finiteClusterLInfDiameterProbability d p n) / n +
          Real.log ((d : ℝ) * (((2 * n + 1 : ℕ) : ℝ) ^ d)) / n := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    let Q := finiteClusterLInfDiameterProbability d p n
    let R := finiteBoxRadiusProbability d p n
    let F := (d : ℝ) * (((2 * n + 1 : ℕ) : ℝ) ^ d)
    have hQ : 0 < Q := finiteClusterLInfDiameterProbability_pos hd p hp0 hp1 n
    have hR : 0 < R := finiteBoxRadiusProbability_pos hd p hp0 hp1 n
    have hF : 0 < F := by positivity
    have hle : Q ≤ F * R := by
      simpa only [Q, R, F, mul_assoc] using
        finiteClusterLInfDiameterProbability_le_radius_prefactor
          (Nat.zero_lt_of_lt hd) p n
    have hlog := Real.log_le_log hQ hle
    rw [Real.log_mul hF.ne' hR.ne'] at hlog
    have hnR : (0 : ℝ) < n := by positivity
    rw [← add_div]
    exact div_le_div_of_nonneg_right (by linarith) hnR.le
  exact hlowerT.squeeze' hupperT hlower hupper

/-- Endpoint-safe form of Theorem 8.18, equation (8.20).  The source writes `n^d` and uses
positive radii; `(n+1)^d` makes the bound meaningful also at radius zero. -/
theorem exists_finiteBoxRadiusProbability_le_succ_pow_mul_exp_neg_rate
    {d : ℕ} (hd : 2 ≤ d) (p : I)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ n : ℕ,
      finiteBoxRadiusProbability d p n ≤
        A * (((n + 1 : ℕ) : ℝ) ^ d) *
          Real.exp (-(n : ℝ) * finiteClusterRadiusDecayRate d p) := by
  let a := finiteClusterRadiusDecayRate d p
  by_cases ha0 : a = 0
  · refine ⟨1, zero_le_one, fun n ↦ ?_⟩
    simp only [show finiteClusterRadiusDecayRate d p = 0 by exact ha0,
      mul_zero, Real.exp_zero, mul_one, one_mul]
    exact (finiteBoxRadiusProbability_le_one d p n).trans (by
      have hbase : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left 1 n
      simpa using pow_le_pow_left₀ zero_le_one hbase d)
  · have ha : 0 < a := lt_of_le_of_ne
      (finiteClusterRadiusDecayRate_nonneg hd p hp0 hp1) (Ne.symm ha0)
    let r := Real.exp (-a)
    let K := (d : ℝ) ^ 2 /
      ((p : ℝ) ^ 2 * (1 - (p : ℝ)) ^ (2 * d - 2))
    let M := diameterPolynomialGeometricMoment d r
    let A := K * M * (2 : ℝ) ^ d
    have hr0 : 0 ≤ r := (Real.exp_pos _).le
    have hr1 : r < 1 := by
      dsimp only [r]
      rw [Real.exp_lt_one_iff]
      linarith
    have hK : 0 ≤ K := by positivity
    have hM : 0 ≤ M := (diameterPolynomialGeometricMoment_pos hr0 hr1).le
    refine ⟨A, mul_nonneg (mul_nonneg hK hM) (pow_nonneg (by norm_num) d), fun n ↦ ?_⟩
    have hradius := finiteBoxRadiusProbability_le_finiteClusterLInfDiameterTailProbability
      d p n
    have htail := finiteClusterLInfDiameterTailProbability_le_rate_prefactor_of_rate_pos
      hd p hp0 hp1 (by simpa only [a] using ha) n
    have hpolyBase : (((2 * n + 1 : ℕ) : ℝ)) ≤
        2 * (((n + 1 : ℕ) : ℝ)) := by
      push_cast
      linarith
    have hpoly := pow_le_pow_left₀ (by positivity) hpolyBase d
    rw [mul_pow] at hpoly
    have hexp : Real.exp (-(n + 2 : ℝ) * a) ≤ Real.exp (-(n : ℝ) * a) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    have hKM : 0 ≤ K * M := mul_nonneg hK hM
    calc
      finiteBoxRadiusProbability d p n ≤
          finiteClusterLInfDiameterTailProbability d p n := hradius
      _ ≤ (K * (((2 * n + 1 : ℕ) : ℝ) ^ d) *
          Real.exp (-(n + 2 : ℝ) * a)) * M := by
        simpa only [K, M, a, r] using htail
      _ ≤ (K * (((2 * n + 1 : ℕ) : ℝ) ^ d) *
          Real.exp (-(n : ℝ) * a)) * M := by
        gcongr
      _ = (K * M) * (((2 * n + 1 : ℕ) : ℝ) ^ d) *
          Real.exp (-(n : ℝ) * a) := by ring
      _ ≤ (K * M) * ((2 : ℝ) ^ d * (((n + 1 : ℕ) : ℝ) ^ d)) *
          Real.exp (-(n : ℝ) * a) := by
        gcongr
      _ = A * (((n + 1 : ℕ) : ℝ) ^ d) *
          Real.exp (-(n : ℝ) * finiteClusterRadiusDecayRate d p) := by
        dsimp only [A, a]
        ring

/-- Exact source-facing positive-radius form of (8.20). -/
theorem exists_finiteBoxRadiusProbability_le_pow_mul_exp_neg_rate
    {d : ℕ} (hd : 2 ≤ d) (p : I)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ n : ℕ, 0 < n →
      finiteBoxRadiusProbability d p n ≤
        A * ((n : ℝ) ^ d) *
          Real.exp (-(n : ℝ) * finiteClusterRadiusDecayRate d p) := by
  obtain ⟨A, hA, hbound⟩ :=
    exists_finiteBoxRadiusProbability_le_succ_pow_mul_exp_neg_rate hd p hp0 hp1
  refine ⟨A * (2 : ℝ) ^ d, mul_nonneg hA (pow_nonneg (by norm_num) d), ?_⟩
  intro n hn
  have hsucc : (((n + 1 : ℕ) : ℝ)) ≤ 2 * (n : ℝ) := by
    exact_mod_cast (by omega : n + 1 ≤ 2 * n)
  have hpow := pow_le_pow_left₀ (by positivity) hsucc d
  rw [mul_pow] at hpow
  calc
    finiteBoxRadiusProbability d p n ≤
        A * (((n + 1 : ℕ) : ℝ) ^ d) *
          Real.exp (-(n : ℝ) * finiteClusterRadiusDecayRate d p) := hbound n
    _ ≤ A * ((2 : ℝ) ^ d * (n : ℝ) ^ d) *
          Real.exp (-(n : ℝ) * finiteClusterRadiusDecayRate d p) := by
      gcongr
    _ = (A * (2 : ℝ) ^ d) * (n : ℝ) ^ d *
          Real.exp (-(n : ℝ) * finiteClusterRadiusDecayRate d p) := by ring

end Percolation
