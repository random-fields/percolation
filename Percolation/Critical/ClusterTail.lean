import Percolation.Critical.RadiusDecay

/-!
# Cluster-size tails from radius tails

This file formalizes Grimmett's volume comparison (5.6)--(5.7): a cluster
larger than a metric ball must reach the next metric sphere.
-/

namespace Percolation

open MeasureTheory
open scoped unitInterval ENNReal

/-- The tail probability `P_p(|C| > n)`, with infinite clusters included. -/
noncomputable def clusterSizeTail (d : ℕ) (p : I) (n : ℕ) : ℝ :=
  (bernoulliBondMeasure d p).real
    {omega : EdgeConfiguration d | (n : ℝ≥0∞) < clusterSizeENNReal d omega}

theorem measurableSet_clusterSizeTailEvent (d n : ℕ) :
    MeasurableSet {omega : EdgeConfiguration d |
      (n : ℝ≥0∞) < clusterSizeENNReal d omega} :=
  (measurable_clusterSizeENNReal d) (measurableSet_Ioi : MeasurableSet (Set.Ioi (n : ℝ≥0∞)))

/-- If the radius-`r` ball has at most `n` vertices, a cluster of size
strictly greater than `n` reaches radius `r+1`. -/
theorem clusterSizeTailEvent_subset_radiusConnectionEvent_of_ball_card_le
    {d n r : ℕ} (hcard : (cubicMetricBall d cubicOrigin r).card ≤ n) :
    {omega : EdgeConfiguration d | (n : ℝ≥0∞) < clusterSizeENNReal d omega} ⊆
      radiusConnectionEvent d cubicOrigin (r + 1) := by
  intro omega hsize
  by_contra hnotRadius
  have hclusterSub : cubicOpenCluster d omega ⊆
      (cubicMetricBall d cubicOrigin r : Set (Cubic d)) := by
    intro y hy
    change y ∈ cubicMetricBall d cubicOrigin r
    rw [mem_cubicMetricBall_iff_l1Dist_le]
    by_contra hnot
    have hradius : r + 1 ≤ cubicL1Dist cubicOrigin y := by omega
    rcases hy with ⟨w, hwopen⟩
    exact hnotRadius (exists_open_walk_to_cubicMetricSphere_in_ball w hwopen hradius)
  have hencard : (cubicOpenCluster d omega).encard ≤
      ((cubicMetricBall d cubicOrigin r : Set (Cubic d))).encard :=
    Set.encard_mono hclusterSub
  have hclusterSize : clusterSizeENNReal d omega ≤ n := by
    rw [clusterSizeENNReal_eq_encard]
    have hball : ((cubicMetricBall d cubicOrigin r : Set (Cubic d))).encard =
        (cubicMetricBall d cubicOrigin r).card := by simp
    rw [hball] at hencard
    have hcard' : ((cubicMetricBall d cubicOrigin r).card : ℕ∞) ≤ n := by
      exact_mod_cast hcard
    exact_mod_cast hencard.trans hcard'
  exact (not_lt_of_ge hclusterSize) hsize

theorem clusterSizeTail_le_radiusTail_of_ball_card_le
    {d n r : ℕ} (p : I)
    (hcard : (cubicMetricBall d cubicOrigin r).card ≤ n) :
    clusterSizeTail d p n ≤ radiusTail d p (r + 1) := by
  exact measureReal_mono (μ := bernoulliBondMeasure d p)
    (clusterSizeTailEvent_subset_radiusConnectionEvent_of_ball_card_le hcard)
    (measure_ne_top _ _)

/-- Equations (5.6)--(5.7) before inversion of the polynomial volume bound. -/
theorem clusterSizeTail_volume_le_radiusTail
    (d : ℕ) (p : I) (r : ℕ) :
    clusterSizeTail d p (3 ^ d * (r + 1) ^ d) ≤
      radiusTail d p (r + 1) :=
  clusterSizeTail_le_radiusTail_of_ball_card_le p
    (cubicMetricBall_card_le d cubicOrigin r)

theorem clusterSizeTail_antitone (d : ℕ) (p : I) :
    Antitone (clusterSizeTail d p) := by
  intro m n hmn
  apply measureReal_mono (μ := bernoulliBondMeasure d p) _ (measure_ne_top _ _)
  intro omega homega
  change (n : ℝ≥0∞) < clusterSizeENNReal d omega at homega
  change (m : ℝ≥0∞) < clusterSizeENNReal d omega
  have hmn' : (m : ℝ≥0∞) ≤ n := by exact_mod_cast hmn
  exact hmn'.trans_lt homega

theorem clusterSizeTail_one_lt_one {d : ℕ} {p : I} (hp1 : (p : ℝ) < 1) :
    clusterSizeTail d p 1 < 1 := by
  have hcard : (cubicMetricBall d cubicOrigin 0).card ≤ 1 := by
    have hball : cubicMetricBall d cubicOrigin 0 = {cubicOrigin} := by
      ext y
      rw [mem_cubicMetricBall_iff_l1Dist_le, Finset.mem_singleton]
      constructor
      · intro h
        exact (cubicL1Dist_eq_zero_iff.mp (Nat.eq_zero_of_le_zero h)).symm
      · rintro rfl
        simp
    simp [hball]
  exact (clusterSizeTail_le_radiusTail_of_ball_card_le p hcard).trans_lt
    (radiusTail_one_lt_one hp1)

/-- The integer radius used to invert the polynomial volume bound. -/
noncomputable def clusterTailRadius (d n : ℕ) : ℕ :=
  ⌊(n : ℝ) ^ ((d : ℝ)⁻¹) / 3⌋₊

theorem clusterTailRadius_cast_le_root_div_three
    {d n : ℕ} :
    (clusterTailRadius d n : ℝ) ≤ (n : ℝ) ^ ((d : ℝ)⁻¹) / 3 := by
  apply Nat.floor_le
  positivity

theorem three_pow_mul_clusterTailRadius_pow_le
    {d n : ℕ} (hd : 0 < d) :
    3 ^ d * clusterTailRadius d n ^ d ≤ n := by
  let root : ℝ := (n : ℝ) ^ ((d : ℝ)⁻¹)
  let m := clusterTailRadius d n
  have hm : (m : ℝ) ≤ root / 3 := by
    simpa [root, m] using clusterTailRadius_cast_le_root_div_three (d := d) (n := n)
  have hroot0 : 0 ≤ root := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have h3m : (3 : ℝ) * m ≤ root := by linarith
  have hpows : ((3 : ℝ) * m) ^ d ≤ root ^ d :=
    pow_le_pow_left₀ (by positivity) h3m d
  have hrootpow : root ^ d = (n : ℝ) := by
    dsimp only [root]
    simpa using Real.rpow_inv_natCast_pow (Nat.cast_nonneg n) hd.ne'
  rw [mul_pow, hrootpow] at hpows
  exact_mod_cast hpows

theorem root_div_six_le_clusterTailRadius
    {d n : ℕ} (hroot : 6 ≤ (n : ℝ) ^ ((d : ℝ)⁻¹)) :
    (n : ℝ) ^ ((d : ℝ)⁻¹) / 6 ≤ clusterTailRadius d n := by
  have hfloor := Nat.sub_one_lt_floor
    ((n : ℝ) ^ ((d : ℝ)⁻¹) / 3)
  change (n : ℝ) ^ ((d : ℝ)⁻¹) / 3 - 1 <
    (clusterTailRadius d n : ℝ) at hfloor
  linarith

theorem clusterSizeTail_le_radiusTail_clusterTailRadius
    {d n : ℕ} (hd : 0 < d) (p : I)
    (hm : 0 < clusterTailRadius d n) :
    clusterSizeTail d p n ≤ radiusTail d p (clusterTailRadius d n) := by
  let m := clusterTailRadius d n
  have hball : (cubicMetricBall d cubicOrigin (m - 1)).card ≤ n := by
    calc
      (cubicMetricBall d cubicOrigin (m - 1)).card ≤
          3 ^ d * (m - 1 + 1) ^ d :=
        cubicMetricBall_card_le d cubicOrigin (m - 1)
      _ = 3 ^ d * m ^ d := by rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hm.ne')]
      _ ≤ n := three_pow_mul_clusterTailRadius_pow_le hd
  simpa [m, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hm.ne')] using
    clusterSizeTail_le_radiusTail_of_ball_card_le p hball

/-- Grimmett, equation (5.7): below `p_c`, the cluster-size tail is at
most a stretched exponential with exponent `n^(1/d)`. -/
theorem clusterSize_tail_le_exp_neg_rpow_of_lt_critical
    (d : ℕ) (hd : 2 ≤ d) (p : I)
    (hp : (p : ℝ) < cubicCriticalProbability d) :
    ∃ beta : ℝ, 0 < beta ∧ ∀ n : ℕ,
      clusterSizeTail d p n ≤
        Real.exp (-beta * (n : ℝ) ^ ((d : ℝ)⁻¹)) := by
  obtain ⟨c, hc, hdecay⟩ :=
    radiusTail_exponential_decay_of_lt_critical d hd p hp
  have hp1 : (p : ℝ) < 1 := hp.trans_le (cubicCriticalProbability_le_one d)
  let q := clusterSizeTail d p 1
  have hq0 : 0 ≤ q := measureReal_nonneg
  have hq1 : q < 1 := clusterSizeTail_one_lt_one hp1
  by_cases hqzero : q = 0
  · refine ⟨1, by norm_num, ?_⟩
    intro n
    by_cases hn0 : n = 0
    · subst n
      have hdreal : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
      have hexpne : ((d : ℝ)⁻¹) ≠ 0 := inv_ne_zero hdreal.ne'
      norm_num only [Nat.cast_zero]
      rw [Real.zero_rpow hexpne]
      norm_num
      exact measureReal_le_one
    · have htail : clusterSizeTail d p n ≤ q :=
        clusterSizeTail_antitone d p (Nat.one_le_iff_ne_zero.mpr hn0)
      rw [hqzero] at htail
      exact htail.trans (Real.exp_pos _).le
  · have hqpos : 0 < q := lt_of_le_of_ne hq0 (Ne.symm hqzero)
    let beta₁ := c / 6
    let beta₂ := -Real.log q / 6
    let beta := min beta₁ beta₂
    have hbeta₁ : 0 < beta₁ := div_pos hc (by norm_num)
    have hlogq : Real.log q < 0 := Real.log_neg hqpos hq1
    have hbeta₂ : 0 < beta₂ := div_pos (neg_pos.mpr hlogq) (by norm_num)
    have hbeta : 0 < beta := lt_min hbeta₁ hbeta₂
    refine ⟨beta, hbeta, ?_⟩
    intro n
    let root : ℝ := (n : ℝ) ^ ((d : ℝ)⁻¹)
    have hroot0 : 0 ≤ root := Real.rpow_nonneg (Nat.cast_nonneg n) _
    by_cases hn0 : n = 0
    · subst n
      have hdreal : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
      have hexpne : ((d : ℝ)⁻¹) ≠ 0 := inv_ne_zero hdreal.ne'
      norm_num only [Nat.cast_zero]
      rw [Real.zero_rpow hexpne]
      norm_num
      exact measureReal_le_one
    by_cases hroot6 : root < 6
    · have htail : clusterSizeTail d p n ≤ q :=
        clusterSizeTail_antitone d p (Nat.one_le_iff_ne_zero.mpr hn0)
      have hbetaLe : beta ≤ beta₂ := min_le_right _ _
      have hprod : beta * root ≤ -Real.log q := by
        calc
          beta * root ≤ beta * 6 :=
            mul_le_mul_of_nonneg_left hroot6.le hbeta.le
          _ ≤ beta₂ * 6 := mul_le_mul_of_nonneg_right hbetaLe (by norm_num)
          _ = -Real.log q := by dsimp [beta₂]; ring
      calc
        clusterSizeTail d p n ≤ q := htail
        _ = Real.exp (Real.log q) := (Real.exp_log hqpos).symm
        _ ≤ Real.exp (-beta * root) := by
          apply Real.exp_le_exp.mpr
          linarith
    · have hrootGe : 6 ≤ root := le_of_not_gt hroot6
      have hmReal : root / 6 ≤ (clusterTailRadius d n : ℝ) := by
        exact root_div_six_le_clusterTailRadius hrootGe
      have hm : 0 < clusterTailRadius d n := by
        have : (0 : ℝ) < root := by
          exact lt_of_lt_of_le (by norm_num) hrootGe
        exact_mod_cast (lt_of_lt_of_le (div_pos this (by norm_num)) hmReal)
      have htailRadius := clusterSizeTail_le_radiusTail_clusterTailRadius
        (d := d) (n := n) (by omega) p hm
      have hbetaLe : beta ≤ beta₁ := min_le_left _ _
      have hexponent : beta * root ≤ c * clusterTailRadius d n := by
        calc
          beta * root ≤ beta₁ * root :=
            mul_le_mul_of_nonneg_right hbetaLe hroot0
          _ = c * (root / 6) := by dsimp [beta₁]; ring
          _ ≤ c * clusterTailRadius d n :=
            mul_le_mul_of_nonneg_left hmReal hc.le
      calc
        clusterSizeTail d p n ≤ radiusTail d p (clusterTailRadius d n) := htailRadius
        _ ≤ Real.exp (-c * clusterTailRadius d n) := hdecay _
        _ ≤ Real.exp (-beta * root) := by
          apply Real.exp_le_exp.mpr
          linarith

#print axioms clusterSizeTail_volume_le_radiusTail
#print axioms clusterSize_tail_le_exp_neg_rpow_of_lt_critical

end Percolation
