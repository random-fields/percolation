import Percolation.Critical.SupercriticalTruncatedGluing
import Percolation.Critical.ClusterTail

/-!
# Finite-cluster volume tails from the supercritical radius rate

This file formalizes the direct volume--radius consequence (8.64).  Its main probabilistic
statement only assumes positivity of the radius rate; Theorem 8.21 is the separate slab input
which supplies that positivity throughout the supercritical interval.
-/

namespace Percolation

open Set MeasureTheory Filter Topology
open scoped unitInterval ENNReal

/-- A finite cluster with at least `n` vertices cannot fit in a coordinate box of cardinality
strictly less than `n`. -/
theorem finiteClusterAtLeastEvent_subset_finiteBoxRadiusEvent_of_box_card_lt
    {d n r : ℕ} (hr : 0 < r)
    (hcard : (cubicMetricBox d cubicOrigin (r - 1)).card < n) :
    finiteClusterEvent d ∩ clusterSizeAtLeastEvent d n ⊆
      finiteBoxRadiusEvent d r := by
  intro omega homega
  rcases homega with ⟨hfinite, hsize⟩
  refine ⟨?_, hfinite⟩
  by_contra hnotRadius
  have hclusterSub : cubicOpenCluster d omega ⊆
      (cubicMetricBox d cubicOrigin (r - 1) : Set (Cubic d)) := by
    intro y hy
    apply mem_cubicMetricBox_iff_lInfDist_le.mpr
    by_contra hnot
    have hradius : r ≤ cubicLInfDist cubicOrigin y := by omega
    rcases hy with ⟨w, hwOpen⟩
    obtain ⟨z, hzSurface, hzConn⟩ :=
      exists_open_walk_to_cubicBoxSurface_in_box w hwOpen hradius
    apply hnotRadius
    simp only [connectionToBoxSurfaceEvent, Set.mem_iUnion]
    exact ⟨z, hzSurface, hzConn⟩
  have hencard : (cubicOpenCluster d omega).encard ≤
      ((cubicMetricBox d cubicOrigin (r - 1) : Set (Cubic d))).encard :=
    Set.encard_mono hclusterSub
  have hbox : ((cubicMetricBox d cubicOrigin (r - 1) : Set (Cubic d))).encard =
      (cubicMetricBox d cubicOrigin (r - 1)).card := by simp
  have hclusterSize : clusterSizeENNReal d omega < n := by
    rw [clusterSizeENNReal_eq_encard]
    rw [hbox] at hencard
    have hcardE :
        ((cubicMetricBox d cubicOrigin (r - 1)).card : ℕ∞) < n := by
      exact_mod_cast hcard
    exact_mod_cast hencard.trans_lt hcardE
  exact (not_lt_of_ge hsize) hclusterSize

theorem finiteClusterSizeTail_le_finiteBoxRadiusProbability_of_box_card_lt
    {d n r : ℕ} (p : I) (hr : 0 < r)
    (hcard : (cubicMetricBox d cubicOrigin (r - 1)).card < n) :
    finiteClusterSizeTail d p n ≤ finiteBoxRadiusProbability d p r := by
  rw [finiteClusterSizeTail_eq_measure_inter]
  exact measureReal_mono
    (finiteClusterAtLeastEvent_subset_finiteBoxRadiusEvent_of_box_card_lt hr hcard)

/-- The Chapter 5 inverse-volume radius also works for coordinate boxes, now with the strict
cardinality inequality required by the at-least tail. -/
theorem cubicMetricBox_pred_clusterTailRadius_card_lt
    {d n : ℕ} (hd : 0 < d) (hm : 0 < clusterTailRadius d n) :
    (cubicMetricBox d cubicOrigin (clusterTailRadius d n - 1)).card < n := by
  let m := clusterTailRadius d n
  have hscale : 3 ^ d * m ^ d ≤ n :=
    three_pow_mul_clusterTailRadius_pow_le hd
  have hbase : 2 * (m - 1) + 1 < 3 * m := by omega
  have hpow : (2 * (m - 1) + 1) ^ d < (3 * m) ^ d :=
    Nat.pow_lt_pow_left hbase (Nat.ne_of_gt hd)
  rw [cubicMetricBox_card]
  change (2 * (m - 1) + 1) ^ d < n
  rw [mul_pow] at hpow
  exact hpow.trans_le hscale

theorem finiteClusterSizeTail_le_finiteBoxRadius_clusterTailRadius
    {d n : ℕ} (hd : 0 < d) (p : I)
    (hm : 0 < clusterTailRadius d n) :
    finiteClusterSizeTail d p n ≤
      finiteBoxRadiusProbability d p (clusterTailRadius d n) :=
  finiteClusterSizeTail_le_finiteBoxRadiusProbability_of_box_card_lt p hm
    (cubicMetricBox_pred_clusterTailRadius_card_lt hd hm)

theorem finiteClusterSizeTail_one_eq_one_sub_theta (d : ℕ) (p : I) :
    finiteClusterSizeTail d p 1 = 1 - theta d p := by
  rw [finiteClusterSizeTail_eq_measure_inter]
  have hset : finiteClusterEvent d ∩ clusterSizeAtLeastEvent d 1 = finiteClusterEvent d := by
    apply Set.inter_eq_left.mpr
    intro omega hfinite
    simp only [clusterSizeAtLeastEvent, Set.mem_setOf_eq]
    rw [clusterSizeENNReal_eq_encard]
    have hencard : (1 : ℕ∞) ≤ (cubicOpenCluster d omega).encard :=
      Set.one_le_encard_iff_nonempty.mpr
        ⟨cubicOrigin, ⟨.nil, by simp [walkIsOpen]⟩⟩
    simpa using ENat.toENNReal_mono hencard
  rw [hset, finiteClusterProbability_eq_tsum,
    tsum_finiteClusterSizeProbability_eq_one_sub_theta]

theorem finiteClusterSizeTail_antitone (d : ℕ) (p : I) :
    Antitone (finiteClusterSizeTail d p) := by
  intro m n hmn
  rw [finiteClusterSizeTail_eq_measure_inter,
    finiteClusterSizeTail_eq_measure_inter]
  apply measureReal_mono
  rintro omega ⟨hfinite, hsize⟩
  refine ⟨hfinite, ?_⟩
  change (n : ℝ≥0∞) ≤ clusterSizeENNReal d omega at hsize
  change (m : ℝ≥0∞) ≤ clusterSizeENNReal d omega
  exact (by exact_mod_cast hmn : (m : ℝ≥0∞) ≤ n).trans hsize
  exact measure_ne_top _ _

/-- Once the radius rate is positive, the defining logarithmic limit supplies a pure
exponential radius bound beyond one deterministic scale. -/
theorem exists_finiteBoxRadiusProbability_le_exp_neg_half_rate
    {d : ℕ} (hd : 2 ≤ d) (p : I)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hrate : 0 < finiteClusterRadiusDecayRate d p) :
    ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
      finiteBoxRadiusProbability d p m ≤
        Real.exp (-(finiteClusterRadiusDecayRate d p / 2) * m) := by
  let a := finiteClusterRadiusDecayRate d p
  have hhalf : a / 2 < a := by dsimp [a]; linarith
  have hevent := (finiteBoxRadiusProbability_logRate_tendsto hd p hp0 hp1).eventually
    (Ioi_mem_nhds hhalf)
  rw [eventually_atTop] at hevent
  obtain ⟨M, hM⟩ := hevent
  refine ⟨max M 1, ?_⟩
  intro m hm
  have hmSlope := hM m ((le_max_left M 1).trans hm)
  have hmPos : 1 ≤ m := (le_max_right M 1).trans hm
  have hR : 0 < finiteBoxRadiusProbability d p m :=
    finiteBoxRadiusProbability_pos hd p hp0 hp1 m
  have hmR : (0 : ℝ) < m := by positivity
  have hlog : Real.log (finiteBoxRadiusProbability d p m) ≤ -(a / 2) * m := by
    rw [lt_div_iff₀ hmR] at hmSlope
    linarith
  rw [← Real.exp_log hR]
  exact Real.exp_le_exp.mpr hlog

/-- Equation (8.64), with Theorem 8.21 isolated as the positivity hypothesis on `a(p)`.
The eventual radius estimate and all small-size endpoints are discharged here. -/
theorem finiteClusterSizeTail_le_exp_neg_rpow_of_radiusRate_pos
    {d : ℕ} (hd : 2 ≤ d) (p : I)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hpc : cubicCriticalProbability d < (p : ℝ))
    (hrate : 0 < finiteClusterRadiusDecayRate d p) :
    ∃ eta : ℝ, 0 < eta ∧ ∀ n : ℕ,
      finiteClusterSizeTail d p n ≤
        Real.exp (-eta * (n : ℝ) ^ ((d : ℝ)⁻¹)) := by
  obtain ⟨M, hM⟩ :=
    exists_finiteBoxRadiusProbability_le_exp_neg_half_rate hd p hp0 hp1 hrate
  let q := finiteClusterSizeTail d p 1
  have hq0 : 0 ≤ q := by dsimp [q]; rw [finiteClusterSizeTail_eq_measure_inter]; exact measureReal_nonneg
  have htheta : 0 < theta d p := theta_pos_of_criticalProbability_lt hpc
  have hqEq : q = 1 - theta d p := by
    simpa [q] using finiteClusterSizeTail_one_eq_one_sub_theta d p
  have hq1 : q < 1 := by rw [hqEq]; linarith
  by_cases hqzero : q = 0
  · refine ⟨1, by norm_num, ?_⟩
    intro n
    by_cases hn0 : n = 0
    · subst n
      have hdR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
      have hle : finiteClusterSizeTail d p 0 ≤ 1 := by
        rw [finiteClusterSizeTail_eq_measure_inter]
        exact measureReal_le_one
      simpa [Real.zero_rpow (inv_ne_zero hdR.ne')] using hle
    · have htail : finiteClusterSizeTail d p n ≤ q :=
        finiteClusterSizeTail_antitone d p (Nat.one_le_iff_ne_zero.mpr hn0)
      rw [hqzero] at htail
      exact htail.trans (Real.exp_pos _).le
  · have hqpos : 0 < q := lt_of_le_of_ne hq0 (Ne.symm hqzero)
    let K : ℝ := max 6 (6 * M)
    let eta₁ := finiteClusterRadiusDecayRate d p / 12
    let eta₂ := -Real.log q / K
    let eta := min eta₁ eta₂
    have hK6 : 6 ≤ K := le_max_left _ _
    have hK0 : 0 < K := lt_of_lt_of_le (by norm_num) hK6
    have heta₁ : 0 < eta₁ := by dsimp [eta₁]; positivity
    have hlogq : Real.log q < 0 := Real.log_neg hqpos hq1
    have heta₂ : 0 < eta₂ := div_pos (neg_pos.mpr hlogq) hK0
    have heta : 0 < eta := lt_min heta₁ heta₂
    refine ⟨eta, heta, ?_⟩
    intro n
    let root : ℝ := (n : ℝ) ^ ((d : ℝ)⁻¹)
    have hroot0 : 0 ≤ root := Real.rpow_nonneg (Nat.cast_nonneg n) _
    by_cases hn0 : n = 0
    · subst n
      have hdR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
      have hle : finiteClusterSizeTail d p 0 ≤ 1 := by
        rw [finiteClusterSizeTail_eq_measure_inter]
        exact measureReal_le_one
      simpa [Real.zero_rpow (inv_ne_zero hdR.ne')] using hle
    by_cases hrootK : root < K
    · have htail : finiteClusterSizeTail d p n ≤ q :=
        finiteClusterSizeTail_antitone d p (Nat.one_le_iff_ne_zero.mpr hn0)
      have hetaLe : eta ≤ eta₂ := min_le_right _ _
      have hprod : eta * root ≤ -Real.log q := by
        calc
          eta * root ≤ eta * K :=
            mul_le_mul_of_nonneg_left hrootK.le heta.le
          _ ≤ eta₂ * K := mul_le_mul_of_nonneg_right hetaLe hK0.le
          _ = -Real.log q := by dsimp [eta₂]; field_simp
      calc
        finiteClusterSizeTail d p n ≤ q := htail
        _ = Real.exp (Real.log q) := (Real.exp_log hqpos).symm
        _ ≤ Real.exp (-eta * root) := Real.exp_le_exp.mpr (by linarith)
    · have hrootGe : K ≤ root := le_of_not_gt hrootK
      have hroot6 : 6 ≤ root := hK6.trans hrootGe
      have hmReal : root / 6 ≤ (clusterTailRadius d n : ℝ) :=
        root_div_six_le_clusterTailRadius hroot6
      have hm : 0 < clusterTailRadius d n := by
        have : (0 : ℝ) < root := lt_of_lt_of_le (by norm_num) hroot6
        exact_mod_cast (lt_of_lt_of_le (div_pos this (by norm_num)) hmReal)
      have hKM : (6 : ℝ) * M ≤ K := le_max_right _ _
      have hmM : M ≤ clusterTailRadius d n := by
        have : (M : ℝ) ≤ root / 6 := by nlinarith
        exact_mod_cast this.trans hmReal
      have htail := finiteClusterSizeTail_le_finiteBoxRadius_clusterTailRadius
        (d := d) (n := n) (by omega) p hm
      have hradius := hM (clusterTailRadius d n) hmM
      have hetaLe : eta ≤ eta₁ := min_le_left _ _
      have hexponent : eta * root ≤
          (finiteClusterRadiusDecayRate d p / 2) * clusterTailRadius d n := by
        calc
          eta * root ≤ eta₁ * root :=
            mul_le_mul_of_nonneg_right hetaLe hroot0
          _ = (finiteClusterRadiusDecayRate d p / 2) * (root / 6) := by
            dsimp [eta₁]
            ring
          _ ≤ (finiteClusterRadiusDecayRate d p / 2) * clusterTailRadius d n :=
            mul_le_mul_of_nonneg_left hmReal (by positivity)
      calc
        finiteClusterSizeTail d p n ≤
            finiteBoxRadiusProbability d p (clusterTailRadius d n) := htail
        _ ≤ Real.exp (-(finiteClusterRadiusDecayRate d p / 2) *
            clusterTailRadius d n) := hradius
        _ ≤ Real.exp (-eta * root) := Real.exp_le_exp.mpr (by linarith)

end Percolation
