import Percolation.Critical.TorusAnimals

/-!
# Infinite-volume limits for the ghost field

This file supplies Grimmett Appendix I.  Small periodic animals are identified exactly with
their infinite-lattice counterparts in `TorusAnimals`; the analytic layer below turns that
eventual coefficient equality into convergence of the ghost probability and its two partial
derivatives.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators unitInterval Topology

noncomputable section

/-- A discrete tightness lemma tailored to Appendix I.  If probability mass functions have
mass at most one, agree on every initial segment once the volume is large enough, and the
observable tends to zero at infinity, then their expectations converge. -/
theorem tendsto_weighted_tsum_of_probability_stabilizes
    (a : ℕ → ℕ → ℝ) (b w : ℕ → ℝ) {C : ℝ}
    (ha0 : ∀ j n, 0 ≤ a j n) (hb0 : ∀ n, 0 ≤ b n)
    (haSum : ∀ j, Summable (a j)) (hbSum : Summable b)
    (haMass : ∀ j, (∑' n, a j n) ≤ 1) (hbMass : (∑' n, b n) ≤ 1)
    (hstable : ∀ n j, n < j → a j n = b n)
    (hwBound : ∀ n, |w n| ≤ C)
    (hw0 : Tendsto w atTop (nhds 0)) :
    Tendsto (fun j ↦ ∑' n, w n * a j n) atTop
      (nhds (∑' n, w n * b n)) := by
  have hwa : ∀ j, Summable (fun n ↦ w n * a j n) := by
    intro j
    apply ((haSum j).mul_left C).of_norm_bounded_eventually
    filter_upwards with n
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (ha0 j n)]
    exact mul_le_mul_of_nonneg_right (hwBound n) (ha0 j n)
  have hwb : Summable (fun n ↦ w n * b n) := by
    apply (hbSum.mul_left C).of_norm_bounded_eventually
    filter_upwards with n
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hb0 n)]
    exact mul_le_mul_of_nonneg_right (hwBound n) (hb0 n)
  refine Metric.tendsto_atTop.mpr fun ε hε ↦ ?_
  obtain ⟨K, hK⟩ := Metric.tendsto_atTop.mp hw0 (ε / 4) (by positivity)
  refine ⟨K, fun j hj ↦ ?_⟩
  have hlow : (∑ n ∈ Finset.range K, w n * a j n) =
      ∑ n ∈ Finset.range K, w n * b n := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [hstable n j ((Finset.mem_range.mp hn).trans_le hj)]
  have haShift : Summable (fun n ↦ a j (n + K)) :=
    (summable_nat_add_iff K).2 (haSum j)
  have hbShift : Summable (fun n ↦ b (n + K)) :=
    (summable_nat_add_iff K).2 hbSum
  have hwaShift : Summable (fun n ↦ w (n + K) * a j (n + K)) :=
    (summable_nat_add_iff K).2 (hwa j)
  have hwbShift : Summable (fun n ↦ w (n + K) * b (n + K)) :=
    (summable_nat_add_iff K).2 hwb
  have haShiftMass : (∑' n, a j (n + K)) ≤ 1 := by
    calc
      (∑' n, a j (n + K)) ≤
          (∑ n ∈ Finset.range K, a j n) + ∑' n, a j (n + K) :=
        le_add_of_nonneg_left (Finset.sum_nonneg fun n hn ↦ ha0 j n)
      _ = ∑' n, a j n := (haSum j).sum_add_tsum_nat_add K
      _ ≤ 1 := haMass j
  have hbShiftMass : (∑' n, b (n + K)) ≤ 1 := by
    calc
      (∑' n, b (n + K)) ≤
          (∑ n ∈ Finset.range K, b n) + ∑' n, b (n + K) :=
        le_add_of_nonneg_left (Finset.sum_nonneg fun n hn ↦ hb0 n)
      _ = ∑' n, b n := hbSum.sum_add_tsum_nat_add K
      _ ≤ 1 := hbMass
  have htailA : ‖∑' n, w (n + K) * a j (n + K)‖ ≤ ε / 4 := by
    have hnorm : Summable (fun n ↦ ‖w (n + K) * a j (n + K)‖) := hwaShift.norm
    have hdom : ∀ n, ‖w (n + K) * a j (n + K)‖ ≤
        (ε / 4) * a j (n + K) := by
      intro n
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (ha0 j (n + K))]
      exact mul_le_mul_of_nonneg_right
        (le_of_lt (by simpa [Real.dist_eq] using hK (n + K) (by omega)))
        (ha0 j (n + K))
    calc
      ‖∑' n, w (n + K) * a j (n + K)‖ ≤
          ∑' n, ‖w (n + K) * a j (n + K)‖ := norm_tsum_le_tsum_norm hnorm
      _ ≤ ∑' n, (ε / 4) * a j (n + K) :=
        hnorm.tsum_le_tsum hdom (haShift.mul_left (ε / 4))
      _ = (ε / 4) * ∑' n, a j (n + K) := haShift.tsum_mul_left (ε / 4)
      _ ≤ ε / 4 := by
        nlinarith [haShiftMass]
  have htailB : ‖∑' n, w (n + K) * b (n + K)‖ ≤ ε / 4 := by
    have hnorm : Summable (fun n ↦ ‖w (n + K) * b (n + K)‖) := hwbShift.norm
    have hdom : ∀ n, ‖w (n + K) * b (n + K)‖ ≤
        (ε / 4) * b (n + K) := by
      intro n
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hb0 (n + K))]
      exact mul_le_mul_of_nonneg_right
        (le_of_lt (by simpa [Real.dist_eq] using hK (n + K) (by omega)))
        (hb0 (n + K))
    calc
      ‖∑' n, w (n + K) * b (n + K)‖ ≤
          ∑' n, ‖w (n + K) * b (n + K)‖ := norm_tsum_le_tsum_norm hnorm
      _ ≤ ∑' n, (ε / 4) * b (n + K) :=
        hnorm.tsum_le_tsum hdom (hbShift.mul_left (ε / 4))
      _ = (ε / 4) * ∑' n, b (n + K) := hbShift.tsum_mul_left (ε / 4)
      _ ≤ ε / 4 := by
        nlinarith [hbShiftMass]
  rw [Real.dist_eq, ← (hwa j).sum_add_tsum_nat_add K,
    ← hwb.sum_add_tsum_nat_add K, hlow, add_sub_add_left_eq_sub]
  exact (norm_sub_le _ _).trans_lt <| lt_of_le_of_lt
    (add_le_add htailA htailB) (by linarith)

/-- Signed version of the preceding tightness lemma.  The summands themselves may have either
sign, but their absolute values are controlled by a vanishing observable times the corresponding
probability mass. -/
theorem tendsto_tsum_of_stabilizes_dominated_by_probability
    (a : ℕ → ℕ → ℝ) (b : ℕ → ℝ) (c : ℕ → ℕ → ℝ) (e w : ℕ → ℝ)
    {C : ℝ}
    (ha0 : ∀ j n, 0 ≤ a j n) (hb0 : ∀ n, 0 ≤ b n)
    (haSum : ∀ j, Summable (a j)) (hbSum : Summable b)
    (haMass : ∀ j, (∑' n, a j n) ≤ 1) (hbMass : (∑' n, b n) ≤ 1)
    (hstable : ∀ n j, n < j → c j n = e n)
    (hw0 : ∀ n, 0 ≤ w n) (hwBound : ∀ n, w n ≤ C)
    (hcBound : ∀ j n, |c j n| ≤ w n * a j n)
    (heBound : ∀ n, |e n| ≤ w n * b n)
    (hwTendsto : Tendsto w atTop (nhds 0)) :
    Tendsto (fun j ↦ ∑' n, c j n) atTop (nhds (∑' n, e n)) := by
  have hcSum : ∀ j, Summable (c j) := by
    intro j
    apply ((haSum j).mul_left C).of_norm_bounded_eventually
    filter_upwards with n
    rw [Real.norm_eq_abs]
    exact (hcBound j n).trans <|
      mul_le_mul_of_nonneg_right (hwBound n) (ha0 j n)
  have heSum : Summable e := by
    apply (hbSum.mul_left C).of_norm_bounded_eventually
    filter_upwards with n
    rw [Real.norm_eq_abs]
    exact (heBound n).trans <|
      mul_le_mul_of_nonneg_right (hwBound n) (hb0 n)
  refine Metric.tendsto_atTop.mpr fun ε hε ↦ ?_
  obtain ⟨K, hK⟩ := Metric.tendsto_atTop.mp hwTendsto (ε / 4) (by positivity)
  refine ⟨K, fun j hj ↦ ?_⟩
  have hlow : (∑ n ∈ Finset.range K, c j n) = ∑ n ∈ Finset.range K, e n := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [hstable n j ((Finset.mem_range.mp hn).trans_le hj)]
  have haShift : Summable (fun n ↦ a j (n + K)) :=
    (summable_nat_add_iff K).2 (haSum j)
  have hbShift : Summable (fun n ↦ b (n + K)) :=
    (summable_nat_add_iff K).2 hbSum
  have hcShift : Summable (fun n ↦ c j (n + K)) :=
    (summable_nat_add_iff K).2 (hcSum j)
  have heShift : Summable (fun n ↦ e (n + K)) :=
    (summable_nat_add_iff K).2 heSum
  have haShiftMass : (∑' n, a j (n + K)) ≤ 1 := by
    calc
      (∑' n, a j (n + K)) ≤
          (∑ n ∈ Finset.range K, a j n) + ∑' n, a j (n + K) :=
        le_add_of_nonneg_left (Finset.sum_nonneg fun n hn ↦ ha0 j n)
      _ = ∑' n, a j n := (haSum j).sum_add_tsum_nat_add K
      _ ≤ 1 := haMass j
  have hbShiftMass : (∑' n, b (n + K)) ≤ 1 := by
    calc
      (∑' n, b (n + K)) ≤
          (∑ n ∈ Finset.range K, b n) + ∑' n, b (n + K) :=
        le_add_of_nonneg_left (Finset.sum_nonneg fun n hn ↦ hb0 n)
      _ = ∑' n, b n := hbSum.sum_add_tsum_nat_add K
      _ ≤ 1 := hbMass
  have htailC : ‖∑' n, c j (n + K)‖ ≤ ε / 4 := by
    have hnorm := hcShift.norm
    have hdom : ∀ n, ‖c j (n + K)‖ ≤ (ε / 4) * a j (n + K) := by
      intro n
      rw [Real.norm_eq_abs]
      have hwle : w (n + K) ≤ ε / 4 := by
        have hdist := hK (n + K) (by omega)
        simpa [Real.dist_eq, abs_of_nonneg (hw0 (n + K))] using hdist.le
      exact (hcBound j (n + K)).trans
        (mul_le_mul_of_nonneg_right hwle (ha0 j (n + K)))
    calc
      ‖∑' n, c j (n + K)‖ ≤ ∑' n, ‖c j (n + K)‖ :=
        norm_tsum_le_tsum_norm hnorm
      _ ≤ ∑' n, (ε / 4) * a j (n + K) :=
        hnorm.tsum_le_tsum hdom (haShift.mul_left (ε / 4))
      _ = (ε / 4) * ∑' n, a j (n + K) := haShift.tsum_mul_left (ε / 4)
      _ ≤ ε / 4 := by nlinarith [haShiftMass]
  have htailE : ‖∑' n, e (n + K)‖ ≤ ε / 4 := by
    have hnorm := heShift.norm
    have hdom : ∀ n, ‖e (n + K)‖ ≤ (ε / 4) * b (n + K) := by
      intro n
      rw [Real.norm_eq_abs]
      have hwle : w (n + K) ≤ ε / 4 := by
        have hdist := hK (n + K) (by omega)
        simpa [Real.dist_eq, abs_of_nonneg (hw0 (n + K))] using hdist.le
      exact (heBound (n + K)).trans
        (mul_le_mul_of_nonneg_right hwle (hb0 (n + K)))
    calc
      ‖∑' n, e (n + K)‖ ≤ ∑' n, ‖e (n + K)‖ :=
        norm_tsum_le_tsum_norm hnorm
      _ ≤ ∑' n, (ε / 4) * b (n + K) :=
        hnorm.tsum_le_tsum hdom (hbShift.mul_left (ε / 4))
      _ = (ε / 4) * ∑' n, b (n + K) := hbShift.tsum_mul_left (ε / 4)
      _ ≤ ε / 4 := by nlinarith [hbShiftMass]
  rw [Real.dist_eq, ← (hcSum j).sum_add_tsum_nat_add K,
    ← heSum.sum_add_tsum_nat_add K, hlow, add_sub_add_left_eq_sub]
  exact (norm_sub_le _ _).trans_lt <| lt_of_le_of_lt
    (add_le_add htailC htailE) (by linarith)

theorem torusGhostTheta_eq_one_sub_tsum_clusterSizeProbability
    (d N : ℕ) (hN : 2 ≤ N) (p γ : I) :
    torusGhostTheta d N p γ =
      1 - ∑' n : ℕ, (1 - (γ : ℝ)) ^ n *
        torusFiniteClusterSizeProbability d N hN p n := by
  rw [torusGhostTheta_eq_polynomial d N hN p γ,
    torusGhostThetaPolynomial_eq_byCluster d N hN p γ,
    torusGhostThetaByCluster_eq_sum_clusterSizes]
  have hzero : ∀ n ∉ Finset.range
      ((cubicTorusVertexFinset d N hN).card + 1),
      (1 - (γ : ℝ)) ^ n * torusFiniteClusterSizeProbability d N hN p n = 0 := by
    intro n hn
    rw [Finset.mem_range, not_lt] at hn
    rw [torusFiniteClusterSizeProbability_eq_zero_of_large d N hN p (by omega), mul_zero]
  rw [tsum_eq_sum hzero]
  calc
    (∑ n ∈ Finset.range ((cubicTorusVertexFinset d N hN).card + 1),
        (1 - (1 - (γ : ℝ)) ^ n) *
          finiteBernoulliProbability (cubicTorusEdgeFinset d N hN) p
            (torusClusterSizeTrace d N hN n)) =
        ∑ n ∈ Finset.range ((cubicTorusVertexFinset d N hN).card + 1),
          (1 - (1 - (γ : ℝ)) ^ n) *
            torusFiniteClusterSizeProbability d N hN p n := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [torusFiniteClusterSizeProbability_eq_finiteBernoulliProbability]
    _ = (∑ n ∈ Finset.range
          ((cubicTorusVertexFinset d N hN).card + 1),
          torusFiniteClusterSizeProbability d N hN p n) -
        ∑ n ∈ Finset.range ((cubicTorusVertexFinset d N hN).card + 1),
          (1 - (γ : ℝ)) ^ n *
            torusFiniteClusterSizeProbability d N hN p n := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro n hn
      ring
    _ = 1 - ∑ n ∈ Finset.range
        ((cubicTorusVertexFinset d N hN).card + 1),
          (1 - (γ : ℝ)) ^ n *
            torusFiniteClusterSizeProbability d N hN p n := by
      rw [sum_torusFiniteClusterSizeProbability_eq_one]

/-- Grimmett Appendix I, equation (5.64): periodic ghost probabilities converge to the
infinite-volume ghost probability.  The periodic side uses volume parameter `N+2`, ensuring the
simple torus has degree `2d` at every index. -/
theorem torusGhostTheta_tendsto (d : ℕ) (p γ : I)
    (hγ0 : 0 < (γ : ℝ)) :
    Tendsto (fun N : ℕ ↦ torusGhostTheta d (N + 2) p γ) atTop
      (nhds (ghostTheta d p γ)) := by
  let a : ℕ → ℕ → ℝ := fun N n ↦
    torusFiniteClusterSizeProbability d (N + 2) (by omega) p n
  let b : ℕ → ℝ := finiteClusterSizeProbability d p
  let w : ℕ → ℝ := fun n ↦ (1 - (γ : ℝ)) ^ n
  have hq0 : 0 ≤ 1 - (γ : ℝ) := sub_nonneg.mpr γ.2.2
  have hq1 : 1 - (γ : ℝ) < 1 := by linarith
  have havoid : Tendsto (fun N ↦ ∑' n, w n * a N n) atTop
      (nhds (∑' n, w n * b n)) := by
    apply tendsto_weighted_tsum_of_probability_stabilizes a b w (C := 1)
    · intro N n
      exact measureReal_nonneg
    · exact finiteClusterSizeProbability_nonneg d p
    · intro N
      exact summable_torusFiniteClusterSizeProbability d (N + 2) (by omega) p
    · exact summable_finiteClusterSizeProbability d p
    · intro N
      rw [tsum_torusFiniteClusterSizeProbability_eq_one]
    · rw [tsum_finiteClusterSizeProbability_eq_one_sub_theta]
      exact sub_le_self 1 measureReal_nonneg
    · intro n N hn
      exact torusFiniteClusterSizeProbability_eq_finiteClusterSizeProbability
        (d := d) (N := N + 2) (by omega) (by omega) p
    · intro n
      rw [abs_of_nonneg (pow_nonneg hq0 n)]
      exact pow_le_one₀ hq0 (sub_le_self 1 γ.2.1)
    · exact tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
  have honeSub : Tendsto (fun N : ℕ ↦ 1 - ∑' n, w n * a N n) atTop
      (nhds (1 - ∑' n, w n * b n)) :=
    (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1)).sub havoid
  rw [ghostTheta_eq_series d p γ hγ0]
  convert honeSub using 1
  · funext N
    exact (torusGhostTheta_eq_one_sub_tsum_clusterSizeProbability
      d (N + 2) (by omega) p γ)

theorem torusGhostThetaGammaDerivative_eq_tsum_clusterSizeProbability
    (d N : ℕ) (hN : 2 ≤ N) (p γ : I)
    (hγ0 : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1) :
    torusGhostThetaGammaDerivative d N hN p γ =
      ∑' n : ℕ, (n : ℝ) * (1 - (γ : ℝ)) ^ (n - 1) *
        torusFiniteClusterSizeProbability d N hN p n := by
  rw [torusGhostThetaGammaDerivative_eq_byCluster d N hN p γ hγ0 hγ1]
  have hzero : ∀ n ∉ Finset.range
      ((cubicTorusVertexFinset d N hN).card + 1),
      (n : ℝ) * (1 - (γ : ℝ)) ^ (n - 1) *
        torusFiniteClusterSizeProbability d N hN p n = 0 := by
    intro n hn
    rw [Finset.mem_range, not_lt] at hn
    rw [torusFiniteClusterSizeProbability_eq_zero_of_large d N hN p (by omega), mul_zero]
  rw [tsum_eq_sum hzero]
  unfold torusGhostThetaGammaDerivativeByCluster
  calc
    (finiteBernoulliExpectation (cubicTorusEdgeFinset d N hN) p fun ω ↦
        let k := (cubicTorusOpenClusterFinset d N hN
          (ω : Set (CubicTorusEdge d N))).card
        (k : ℝ) * (1 - (γ : ℝ)) ^ (k - 1)) =
        ∑ n ∈ Finset.range ((cubicTorusVertexFinset d N hN).card + 1),
          ((n : ℝ) * (1 - (γ : ℝ)) ^ (n - 1)) *
            finiteBernoulliProbability (cubicTorusEdgeFinset d N hN) p
              (torusClusterSizeTrace d N hN n) := by
      exact torusFiniteBernoulliExpectation_eq_sum_clusterSizes d N hN p
        (fun n ↦ (n : ℝ) * (1 - (γ : ℝ)) ^ (n - 1))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [torusFiniteClusterSizeProbability_eq_finiteBernoulliProbability]

/-- Grimmett Appendix I, equation (5.66): the green-density derivatives of the periodic ghost
probabilities converge to the infinite-volume derivative. -/
theorem torusGhostTheta_gammaDeriv_tendsto (d : ℕ) (p γ : I)
    (hγ0 : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1) :
    Tendsto (fun N : ℕ ↦
      torusGhostThetaGammaDerivative d (N + 2) (by omega) p γ) atTop
      (nhds (deriv (ghostThetaSeries d p) (γ : ℝ))) := by
  let a : ℕ → ℕ → ℝ := fun N n ↦
    torusFiniteClusterSizeProbability d (N + 2) (by omega) p n
  let b : ℕ → ℝ := finiteClusterSizeProbability d p
  let q : ℝ := 1 - (γ : ℝ)
  let w : ℕ → ℝ := fun n ↦ (n : ℝ) * q ^ (n - 1)
  have hq0 : 0 < q := by dsimp only [q]; linarith
  have hq1 : q < 1 := by dsimp only [q]; linarith
  have hraw : Tendsto (fun n : ℕ ↦ (n : ℝ) * q ^ n) atTop (nhds 0) :=
    tendsto_self_mul_const_pow_of_lt_one hq0.le hq1
  have hw0 : Tendsto w atTop (nhds 0) := by
    have hscaled := hraw.const_mul q⁻¹
    have hscaled' : Tendsto (fun n : ℕ ↦ q⁻¹ * ((n : ℝ) * q ^ n)) atTop
        (nhds 0) := by simpa using hscaled
    convert hscaled' using 1
    funext n
    cases n with
    | zero => simp [w]
    | succ n =>
        dsimp only [w]
        rw [Nat.succ_sub_one, pow_succ]
        field_simp
  obtain ⟨C, hC⟩ := hw0.norm.bddAbove_range
  have hweighted : Tendsto (fun N ↦ ∑' n, w n * a N n) atTop
      (nhds (∑' n, w n * b n)) := by
    apply tendsto_weighted_tsum_of_probability_stabilizes a b w (C := C)
    · intro N n
      exact measureReal_nonneg
    · exact finiteClusterSizeProbability_nonneg d p
    · intro N
      exact summable_torusFiniteClusterSizeProbability d (N + 2) (by omega) p
    · exact summable_finiteClusterSizeProbability d p
    · intro N
      rw [tsum_torusFiniteClusterSizeProbability_eq_one]
    · rw [tsum_finiteClusterSizeProbability_eq_one_sub_theta]
      exact sub_le_self 1 measureReal_nonneg
    · intro n N hn
      exact torusFiniteClusterSizeProbability_eq_finiteClusterSizeProbability
        (d := d) (N := N + 2) (by omega) (by omega) p
    · intro n
      rw [← Real.norm_eq_abs]
      exact hC ⟨n, rfl⟩
    · exact hw0
  have hderiv := ghostThetaSeries_hasDerivAt d p hγ0 hγ1
  rw [hderiv.deriv]
  convert hweighted using 1
  · funext N
    exact torusGhostThetaGammaDerivative_eq_tsum_clusterSizeProbability
      d (N + 2) (by omega) p γ hγ0 hγ1

theorem clusterPolynomialDerivativeTerm_eq_score
    (m b : ℕ) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    (m : ℝ) * p ^ (m - 1) * (1 - p) ^ b -
        (b : ℝ) * p ^ m * (1 - p) ^ (b - 1) =
      p ^ m * (1 - p) ^ b * ((m : ℝ) / p - (b : ℝ) / (1 - p)) := by
  rw [natCast_mul_pow_pred_eq_pow_mul_div m hp0.ne']
  have hb := natCast_mul_pow_pred_eq_pow_mul_div b (sub_pos.mpr hp1).ne'
  calc
    p ^ m * ((m : ℝ) / p) * (1 - p) ^ b -
        (b : ℝ) * p ^ m * (1 - p) ^ (b - 1) =
      p ^ m * ((m : ℝ) / p) * (1 - p) ^ b -
        p ^ m * ((1 - p) ^ b * ((b : ℝ) / (1 - p))) := by
      rw [← hb]
      ring
    _ = _ := by ring

theorem abs_cubicClusterSizePolynomialDerivative_le
    {d n : ℕ} {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    |cubicClusterSizePolynomialDerivative d n p| ≤
      (((d : ℝ) / p + (2 * d : ℝ) / (1 - p)) * n) *
        finiteClusterSizeProbability d ⟨p, hp0.le, hp1.le⟩ n := by
  let q : I := ⟨p, hp0.le, hp1.le⟩
  let C : ℝ := ((d : ℝ) / p + (2 * d : ℝ) / (1 - p)) * n
  have hC0 : 0 ≤ C := by dsimp only [C]; positivity
  have hterm : ∀ A : CubicBondAnimal d n,
      |(A.edges.card : ℝ) * p ^ (A.edges.card - 1) * (1 - p) ^ A.boundary.card -
          (A.boundary.card : ℝ) * p ^ A.edges.card *
            (1 - p) ^ (A.boundary.card - 1)| ≤
        C * (p ^ A.edges.card * (1 - p) ^ A.boundary.card) := by
    intro A
    rw [clusterPolynomialDerivativeTerm_eq_score A.edges.card A.boundary.card hp0 hp1,
      abs_mul, abs_of_nonneg (mul_nonneg (pow_nonneg hp0.le _) (pow_nonneg (sub_pos.mpr hp1).le _))]
    have hm : (A.edges.card : ℝ) ≤ (d : ℝ) * n := by
      exact_mod_cast A.edges_card_upper
    have hb : (A.boundary.card : ℝ) ≤ (2 * d : ℝ) * n := by
      exact_mod_cast A.boundary_card_le
    have hscore : |(A.edges.card : ℝ) / p -
        (A.boundary.card : ℝ) / (1 - p)| ≤ C := by
      calc
        |(A.edges.card : ℝ) / p - (A.boundary.card : ℝ) / (1 - p)| ≤
            (A.edges.card : ℝ) / p + (A.boundary.card : ℝ) / (1 - p) := by
          simpa [abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) hp0.le),
            abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) (sub_pos.mpr hp1).le),
            abs_of_pos hp0, abs_of_pos (sub_pos.mpr hp1)] using
              (norm_sub_le ((A.edges.card : ℝ) / p)
                ((A.boundary.card : ℝ) / (1 - p)))
        _ ≤ ((d : ℝ) * n) / p + ((2 * d : ℝ) * n) / (1 - p) := by
          gcongr
        _ = C := by dsimp only [C]; ring
    calc
      p ^ A.edges.card * (1 - p) ^ A.boundary.card *
          |(A.edges.card : ℝ) / p - (A.boundary.card : ℝ) / (1 - p)| ≤
          (p ^ A.edges.card * (1 - p) ^ A.boundary.card) * C :=
        mul_le_mul_of_nonneg_left hscore
          (mul_nonneg (pow_nonneg hp0.le A.edges.card)
            (pow_nonneg (sub_pos.mpr hp1).le A.boundary.card))
      _ = C * (p ^ A.edges.card * (1 - p) ^ A.boundary.card) := mul_comm _ _
  unfold cubicClusterSizePolynomialDerivative
  calc
    |∑ A : CubicBondAnimal d n,
        ((A.edges.card : ℝ) * p ^ (A.edges.card - 1) * (1 - p) ^ A.boundary.card -
          (A.boundary.card : ℝ) * p ^ A.edges.card *
            (1 - p) ^ (A.boundary.card - 1))| ≤
        ∑ A : CubicBondAnimal d n,
          |(A.edges.card : ℝ) * p ^ (A.edges.card - 1) * (1 - p) ^ A.boundary.card -
            (A.boundary.card : ℝ) * p ^ A.edges.card *
              (1 - p) ^ (A.boundary.card - 1)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ A : CubicBondAnimal d n,
        C * (p ^ A.edges.card * (1 - p) ^ A.boundary.card) :=
      Finset.sum_le_sum fun A hA ↦ hterm A
    _ = C * cubicClusterSizePolynomial d n p := by
      unfold cubicClusterSizePolynomial
      rw [Finset.mul_sum]
    _ = C * finiteClusterSizeProbability d q n := by
      exact congrArg (fun x : ℝ ↦ C * x)
        (cubicClusterSizePolynomial_eq_probability d n q)

theorem abs_torusClusterSizePolynomialDerivative_le
    {d N n : ℕ} (hN : 2 ≤ N) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    |torusClusterSizePolynomialDerivative d N hN n p| ≤
      (((2 * d : ℝ) / p + (2 * d : ℝ) / (1 - p)) * n) *
        torusFiniteClusterSizeProbability d N hN ⟨p, hp0.le, hp1.le⟩ n := by
  let q : I := ⟨p, hp0.le, hp1.le⟩
  let C : ℝ := ((2 * d : ℝ) / p + (2 * d : ℝ) / (1 - p)) * n
  have hterm : ∀ A : CubicTorusBondAnimal d N n hN,
      |(A.edges.card : ℝ) * p ^ (A.edges.card - 1) * (1 - p) ^ A.boundary.card -
          (A.boundary.card : ℝ) * p ^ A.edges.card *
            (1 - p) ^ (A.boundary.card - 1)| ≤
        C * (p ^ A.edges.card * (1 - p) ^ A.boundary.card) := by
    intro A
    rw [clusterPolynomialDerivativeTerm_eq_score A.edges.card A.boundary.card hp0 hp1,
      abs_mul, abs_of_nonneg (mul_nonneg (pow_nonneg hp0.le _) (pow_nonneg (sub_pos.mpr hp1).le _))]
    have hm : (A.edges.card : ℝ) ≤ (2 * d : ℝ) * n := by
      exact_mod_cast A.edges_card_le.trans_eq (Nat.mul_comm n (2 * d))
    have hb : (A.boundary.card : ℝ) ≤ (2 * d : ℝ) * n := by
      exact_mod_cast A.boundary_card_le.trans_eq (Nat.mul_comm n (2 * d))
    have hscore : |(A.edges.card : ℝ) / p -
        (A.boundary.card : ℝ) / (1 - p)| ≤ C := by
      calc
        |(A.edges.card : ℝ) / p - (A.boundary.card : ℝ) / (1 - p)| ≤
            (A.edges.card : ℝ) / p + (A.boundary.card : ℝ) / (1 - p) := by
          simpa [abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) hp0.le),
            abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) (sub_pos.mpr hp1).le),
            abs_of_pos hp0, abs_of_pos (sub_pos.mpr hp1)] using
              (norm_sub_le ((A.edges.card : ℝ) / p)
                ((A.boundary.card : ℝ) / (1 - p)))
        _ ≤ ((2 * d : ℝ) * n) / p + ((2 * d : ℝ) * n) / (1 - p) := by
          gcongr
        _ = C := by dsimp only [C]; ring
    calc
      p ^ A.edges.card * (1 - p) ^ A.boundary.card *
          |(A.edges.card : ℝ) / p - (A.boundary.card : ℝ) / (1 - p)| ≤
          (p ^ A.edges.card * (1 - p) ^ A.boundary.card) * C :=
        mul_le_mul_of_nonneg_left hscore
          (mul_nonneg (pow_nonneg hp0.le A.edges.card)
            (pow_nonneg (sub_pos.mpr hp1).le A.boundary.card))
      _ = C * (p ^ A.edges.card * (1 - p) ^ A.boundary.card) := mul_comm _ _
  unfold torusClusterSizePolynomialDerivative
  calc
    |∑ A : CubicTorusBondAnimal d N n hN,
        ((A.edges.card : ℝ) * p ^ (A.edges.card - 1) * (1 - p) ^ A.boundary.card -
          (A.boundary.card : ℝ) * p ^ A.edges.card *
            (1 - p) ^ (A.boundary.card - 1))| ≤
        ∑ A : CubicTorusBondAnimal d N n hN,
          |(A.edges.card : ℝ) * p ^ (A.edges.card - 1) * (1 - p) ^ A.boundary.card -
            (A.boundary.card : ℝ) * p ^ A.edges.card *
              (1 - p) ^ (A.boundary.card - 1)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ A : CubicTorusBondAnimal d N n hN,
        C * (p ^ A.edges.card * (1 - p) ^ A.boundary.card) :=
      Finset.sum_le_sum fun A hA ↦ hterm A
    _ = C * torusClusterSizePolynomial d N hN n p := by
      unfold torusClusterSizePolynomial
      rw [Finset.mul_sum]
    _ = C * torusFiniteClusterSizeProbability d N hN q n := by
      exact congrArg (fun x : ℝ ↦ C * x)
        (torusClusterSizePolynomial_eq_probability d N hN n q)

theorem torusClusterSizePolynomial_eq_zero_of_large
    (d N : ℕ) (hN : 2 ≤ N) {n : ℕ}
    (hn : (cubicTorusVertexFinset d N hN).card < n) (p : ℝ) :
    torusClusterSizePolynomial d N hN n p = 0 := by
  unfold torusClusterSizePolynomial
  apply Finset.sum_eq_zero
  intro A hA
  exfalso
  have hcard := Finset.card_le_card A.vertices_subset
  rw [A.vertices_card] at hcard
  omega

/-- Infinite-volume formal `p` derivative of the positive-ghost-density generating series. -/
noncomputable def ghostThetaPDerivativeSeries (d : ℕ) (γ p : ℝ) : ℝ :=
  -(∑' n : ℕ, (1 - γ) ^ n * cubicClusterSizePolynomialDerivative d n p)

/-- Periodic formal `p` derivative, written in the stabilized animal basis. -/
noncomputable def torusGhostThetaPDerivativeByAnimals
    (d N : ℕ) (hN : 2 ≤ N) (p γ : ℝ) : ℝ :=
  -(∑ n ∈ Finset.range ((cubicTorusVertexFinset d N hN).card + 1),
    (1 - γ) ^ n * torusClusterSizePolynomialDerivative d N hN n p)

theorem torusGhostThetaPolynomial_eq_one_sub_sum_clusterPolynomials
    (d N : ℕ) (hN : 2 ≤ N) (p γ : I) :
    torusGhostThetaPolynomial d N hN p γ =
      1 - ∑ n ∈ Finset.range ((cubicTorusVertexFinset d N hN).card + 1),
        (1 - (γ : ℝ)) ^ n * torusClusterSizePolynomial d N hN n p := by
  have h := torusGhostTheta_eq_one_sub_tsum_clusterSizeProbability d N hN p γ
  rw [torusGhostTheta_eq_polynomial d N hN p γ] at h
  have hzero : ∀ n ∉ Finset.range
      ((cubicTorusVertexFinset d N hN).card + 1),
      (1 - (γ : ℝ)) ^ n * torusFiniteClusterSizeProbability d N hN p n = 0 := by
    intro n hn
    rw [Finset.mem_range, not_lt] at hn
    rw [torusFiniteClusterSizeProbability_eq_zero_of_large d N hN p (by omega), mul_zero]
  rw [tsum_eq_sum hzero] at h
  calc
    torusGhostThetaPolynomial d N hN p γ =
        1 - ∑ n ∈ Finset.range ((cubicTorusVertexFinset d N hN).card + 1),
          (1 - (γ : ℝ)) ^ n * torusFiniteClusterSizeProbability d N hN p n := h
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro n hn
      rw [torusClusterSizePolynomial_eq_probability]

theorem torusGhostThetaPDerivative_eq_byAnimals
    (d N : ℕ) (hN : 2 ≤ N) (p γ : I)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    torusGhostThetaPDerivative d N hN p γ =
      torusGhostThetaPDerivativeByAnimals d N hN p γ := by
  let F : ℝ → ℝ := fun y ↦
    1 - ∑ n ∈ Finset.range ((cubicTorusVertexFinset d N hN).card + 1),
      (1 - (γ : ℝ)) ^ n * torusClusterSizePolynomial d N hN n y
  have hF : HasDerivAt F (torusGhostThetaPDerivativeByAnimals d N hN p γ) p := by
    have hsum : HasDerivAt
        (fun y : ℝ ↦ ∑ n ∈ Finset.range
          ((cubicTorusVertexFinset d N hN).card + 1),
            (1 - (γ : ℝ)) ^ n * torusClusterSizePolynomial d N hN n y)
        (∑ n ∈ Finset.range ((cubicTorusVertexFinset d N hN).card + 1),
          (1 - (γ : ℝ)) ^ n *
            torusClusterSizePolynomialDerivative d N hN n p) p := by
      apply HasDerivAt.fun_sum
      intro n hn
      exact (torusClusterSizePolynomial_hasDerivAt d N hN n p).const_mul _
    simpa [F, torusGhostThetaPDerivativeByAnimals] using hsum.const_sub 1
  have heq : (fun y : ℝ ↦ torusGhostThetaPolynomial d N hN y γ) =ᶠ[nhds (p : ℝ)] F := by
    filter_upwards [Ioo_mem_nhds hp0 hp1] with y hy
    let yI : I := ⟨y, hy.1.le, hy.2.le⟩
    exact torusGhostThetaPolynomial_eq_one_sub_sum_clusterPolynomials
      d N hN yI γ
  have hForiginal : HasDerivAt (fun y : ℝ ↦
      torusGhostThetaPolynomial d N hN y γ)
      (torusGhostThetaPDerivativeByAnimals d N hN p γ) p :=
    hF.congr_of_eventuallyEq heq
  exact (torusGhostThetaPolynomial_hasDerivAt_p d N hN p γ).unique hForiginal

theorem torusClusterSizePolynomialDerivative_eq_zero_of_large
    (d N : ℕ) (hN : 2 ≤ N) {n : ℕ}
    (hn : (cubicTorusVertexFinset d N hN).card < n) (p : ℝ) :
    torusClusterSizePolynomialDerivative d N hN n p = 0 := by
  have hfun : torusClusterSizePolynomial d N hN n = fun _ ↦ 0 :=
    funext fun q ↦ torusClusterSizePolynomial_eq_zero_of_large d N hN hn q
  have hderiv := torusClusterSizePolynomial_hasDerivAt d N hN n p
  rw [hfun] at hderiv
  exact hderiv.unique (hasDerivAt_const p 0)

/-- Grimmett Appendix I, equation (5.65): the bond-density derivatives of the periodic ghost
probabilities converge to the infinite animal-series derivative. -/
theorem torusGhostTheta_pDeriv_tendsto_series (d : ℕ) (p γ : I)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hγ0 : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1) :
    Tendsto (fun N : ℕ ↦ torusGhostThetaPDerivative d (N + 2) (by omega) p γ) atTop
      (nhds (ghostThetaPDerivativeSeries d γ p)) := by
  let a : ℕ → ℕ → ℝ := fun N n ↦
    torusFiniteClusterSizeProbability d (N + 2) (by omega) p n
  let b : ℕ → ℝ := finiteClusterSizeProbability d p
  let q : ℝ := 1 - (γ : ℝ)
  let Kp : ℝ := (2 * d : ℝ) / p + (2 * d : ℝ) / (1 - p)
  let w : ℕ → ℝ := fun n ↦ Kp * n * q ^ n
  let c : ℕ → ℕ → ℝ := fun N n ↦
    -(q ^ n * torusClusterSizePolynomialDerivative d (N + 2) (by omega) n p)
  let e : ℕ → ℝ := fun n ↦ -(q ^ n * cubicClusterSizePolynomialDerivative d n p)
  have hq0 : 0 ≤ q := by dsimp only [q]; linarith
  have hq1 : q < 1 := by dsimp only [q]; linarith
  have hKp0 : 0 ≤ Kp := by dsimp only [Kp]; positivity
  have hw0 : ∀ n, 0 ≤ w n := by
    intro n
    exact mul_nonneg (mul_nonneg hKp0 (Nat.cast_nonneg n)) (pow_nonneg hq0 n)
  have hwTendsto : Tendsto w atTop (nhds 0) := by
    have hbase := tendsto_self_mul_const_pow_of_lt_one hq0 hq1
    simpa [w, mul_assoc, mul_left_comm, mul_comm] using hbase.const_mul Kp
  obtain ⟨C, hC⟩ := hwTendsto.bddAbove_range
  have hconv : Tendsto (fun N ↦ ∑' n, c N n) atTop (nhds (∑' n, e n)) := by
    apply tendsto_tsum_of_stabilizes_dominated_by_probability a b c e w (C := C)
    · intro N n
      exact measureReal_nonneg
    · exact finiteClusterSizeProbability_nonneg d p
    · intro N
      exact summable_torusFiniteClusterSizeProbability d (N + 2) (by omega) p
    · exact summable_finiteClusterSizeProbability d p
    · intro N
      rw [tsum_torusFiniteClusterSizeProbability_eq_one]
    · rw [tsum_finiteClusterSizeProbability_eq_one_sub_theta]
      exact sub_le_self 1 measureReal_nonneg
    · intro n N hn
      dsimp only [c, e]
      rw [torusClusterSizePolynomialDerivative_eq_cubic (hN := by omega) (by omega)]
    · exact hw0
    · intro n
      exact hC ⟨n, rfl⟩
    · intro N n
      dsimp only [c, w, a, q, Kp]
      rw [abs_neg, abs_mul, abs_of_nonneg (pow_nonneg hq0 n)]
      calc
        q ^ n * |torusClusterSizePolynomialDerivative d (N + 2) (by omega) n p| ≤
            q ^ n * ((((2 * d : ℝ) / p + (2 * d : ℝ) / (1 - p)) * n) *
              torusFiniteClusterSizeProbability d (N + 2) (by omega) p n) :=
          mul_le_mul_of_nonneg_left
            (abs_torusClusterSizePolynomialDerivative_le (d := d) (N := N + 2)
              (n := n) (by omega) hp0 hp1) (pow_nonneg hq0 n)
        _ = (((2 * d : ℝ) / (p : ℝ) + (2 * d : ℝ) / (1 - p)) * (n : ℝ) * q ^ n) *
            torusFiniteClusterSizeProbability d (N + 2) (by omega) p n := by ring
    · intro n
      dsimp only [e, w, b, q, Kp]
      rw [abs_neg, abs_mul, abs_of_nonneg (pow_nonneg hq0 n)]
      have hbase := abs_cubicClusterSizePolynomialDerivative_le
        (d := d) (n := n) hp0 hp1
      have hcoef : ((d : ℝ) / p + (2 * d : ℝ) / (1 - p)) * n ≤
          ((2 * d : ℝ) / p + (2 * d : ℝ) / (1 - p)) * n := by
        have hd : (d : ℝ) / p ≤ (2 * d : ℝ) / p := by
          exact div_le_div_of_nonneg_right
            (by have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d; nlinarith) hp0.le
        exact mul_le_mul_of_nonneg_right
          (add_le_add hd le_rfl) (Nat.cast_nonneg n)
      calc
        q ^ n * |cubicClusterSizePolynomialDerivative d n p| ≤
            q ^ n * ((((d : ℝ) / p + (2 * d : ℝ) / (1 - p)) * n) *
              finiteClusterSizeProbability d p n) :=
          mul_le_mul_of_nonneg_left hbase (pow_nonneg hq0 n)
        _ ≤ q ^ n * ((((2 * d : ℝ) / p + (2 * d : ℝ) / (1 - p)) * n) *
              finiteClusterSizeProbability d p n) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hcoef
              (finiteClusterSizeProbability_nonneg d p n)) (pow_nonneg hq0 n)
        _ = (((2 * d : ℝ) / p + (2 * d : ℝ) / (1 - p)) * (n : ℝ) * q ^ n) *
            finiteClusterSizeProbability d p n := by ring
    · exact hwTendsto
  convert hconv using 1
  · funext N
    rw [torusGhostThetaPDerivative_eq_byAnimals d (N + 2) (by omega) p γ hp0 hp1]
    unfold torusGhostThetaPDerivativeByAnimals
    dsimp only [c, q]
    rw [tsum_eq_sum (s := Finset.range
      ((cubicTorusVertexFinset d (N + 2) (by omega)).card + 1)) fun n hn ↦ by
        rw [Finset.mem_range, not_lt] at hn
        rw [torusClusterSizePolynomialDerivative_eq_zero_of_large
          d (N + 2) (by omega) (by omega), mul_zero, neg_zero]]
    rw [Finset.sum_neg_distrib]
  · unfold ghostThetaPDerivativeSeries
    dsimp only [e, q]
    rw [tsum_neg]

/-- Real-parameter extension of the infinite-volume ghost probability in the bond-density
variable. -/
noncomputable def ghostThetaPSeries (d : ℕ) (γ p : ℝ) : ℝ :=
  1 - ∑' n : ℕ, (1 - γ) ^ n * cubicClusterSizePolynomial d n p

theorem ghostThetaPSeries_eq_ghostThetaSeries (d : ℕ) (p γ : I) :
    ghostThetaPSeries d γ p = ghostThetaSeries d p γ := by
  unfold ghostThetaPSeries ghostThetaSeries
  congr 2
  funext n
  rw [cubicClusterSizePolynomial_eq_probability]

theorem ghostThetaPSeries_hasDerivAt (d : ℕ) {p γ : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    HasDerivAt (ghostThetaPSeries d γ) (ghostThetaPDerivativeSeries d γ p) p := by
  let p₁ : ℝ := p / 2
  let p₂ : ℝ := (1 + p) / 2
  let q : ℝ := 1 - γ
  let C : ℝ := (d : ℝ) / p₁ + (2 * d : ℝ) / (1 - p₂)
  let u : ℕ → ℝ := fun n ↦ C * n * q ^ n
  have hp₁0 : 0 < p₁ := by dsimp only [p₁]; linarith
  have hp₂1 : p₂ < 1 := by dsimp only [p₂]; linarith
  have hp_mem : p ∈ Ioo p₁ p₂ := by
    dsimp only [p₁, p₂]
    constructor <;> linarith
  have hq0 : 0 ≤ q := by dsimp only [q]; linarith
  have hq1 : q < 1 := by dsimp only [q]; linarith
  have hqnorm : ‖q‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hq0]; exact hq1
  have hU : Summable u := by
    have hbase := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hqnorm
    have hbase' : Summable (fun n : ℕ ↦ (n : ℝ) * q ^ n) := by
      simpa [pow_one] using hbase
    simpa [u, mul_assoc] using hbase'.mul_left C
  have hbase : Summable (fun n : ℕ ↦
      q ^ n * cubicClusterSizePolynomial d n p) := by
    have hgeom := summable_geometric_of_norm_lt_one hqnorm
    apply hgeom.of_norm_bounded
    intro n
    let pI : I := ⟨p, hp0.le, hp1.le⟩
    have hpoly : cubicClusterSizePolynomial d n p =
        finiteClusterSizeProbability d pI n :=
      cubicClusterSizePolynomial_eq_probability d n pI
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hq0, hpoly,
      abs_of_nonneg (finiteClusterSizeProbability_nonneg d ⟨p, hp0.le, hp1.le⟩ n)]
    exact mul_le_of_le_one_right (pow_nonneg hq0 n)
      (finiteClusterSizeProbability_le_one d ⟨p, hp0.le, hp1.le⟩ n)
  have hbound : ∀ (n : ℕ) (y : ℝ), y ∈ Ioo p₁ p₂ →
      ‖q ^ n * cubicClusterSizePolynomialDerivative d n y‖ ≤ u n := by
    intro n y hy
    have hy0 : 0 < y := hp₁0.trans hy.1
    have hy1 : y < 1 := hy.2.trans hp₂1
    have hderiv := abs_cubicClusterSizePolynomialDerivative_le
      (d := d) (n := n) hy0 hy1
    have hfirst : (d : ℝ) / y ≤ (d : ℝ) / p₁ := by
      exact div_le_div_of_nonneg_left (Nat.cast_nonneg d) hp₁0 hy.1.le
    have hsecond : (2 * d : ℝ) / (1 - y) ≤ (2 * d : ℝ) / (1 - p₂) := by
      exact div_le_div_of_nonneg_left (by positivity) (sub_pos.mpr hp₂1)
        (sub_le_sub_left hy.2.le 1)
    have hcoef : ((d : ℝ) / y + (2 * d : ℝ) / (1 - y)) * n ≤ C * n := by
      exact mul_le_mul_of_nonneg_right (add_le_add hfirst hsecond) (Nat.cast_nonneg n)
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hq0]
    calc
      q ^ n * |cubicClusterSizePolynomialDerivative d n y| ≤
          q ^ n * ((((d : ℝ) / y + (2 * d : ℝ) / (1 - y)) * n) *
            finiteClusterSizeProbability d ⟨y, hy0.le, hy1.le⟩ n) :=
        mul_le_mul_of_nonneg_left hderiv (pow_nonneg hq0 n)
      _ ≤ q ^ n * (C * n * finiteClusterSizeProbability d
            ⟨y, hy0.le, hy1.le⟩ n) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hcoef
            (finiteClusterSizeProbability_nonneg d ⟨y, hy0.le, hy1.le⟩ n))
          (pow_nonneg hq0 n)
      _ ≤ q ^ n * (C * n) := by
        have hCn : 0 ≤ C * (n : ℝ) := by dsimp only [C]; positivity
        exact mul_le_mul_of_nonneg_left
          (mul_le_of_le_one_right hCn
            (finiteClusterSizeProbability_le_one d ⟨y, hy0.le, hy1.le⟩ n))
          (pow_nonneg hq0 n)
      _ = u n := by dsimp only [u]; ring
  have hsum := hasDerivAt_tsum_of_isPreconnected hU isOpen_Ioo isPreconnected_Ioo
    (fun n y _hy ↦ (cubicClusterSizePolynomial_hasDerivAt d n y).const_mul (q ^ n))
    hbound hp_mem hbase hp_mem
  have htheta := hsum.const_sub 1
  have hneg :
      -(∑' n : ℕ, q ^ n * cubicClusterSizePolynomialDerivative d n p) =
        ghostThetaPDerivativeSeries d γ p := by
    rfl
  rw [hneg] at htheta
  exact htheta

theorem ghostThetaPDerivativeSeries_eq_deriv (d : ℕ) (p γ : I)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hγ0 : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1) :
    ghostThetaPDerivativeSeries d γ p = deriv (ghostThetaPSeries d γ) p := by
  rw [(ghostThetaPSeries_hasDerivAt d hp0 hp1 hγ0 hγ1).deriv]

/-- Source-facing form of Appendix I (5.65), with the limit identified as the actual
infinite-volume `p` derivative. -/
theorem torusGhostTheta_pDeriv_tendsto (d : ℕ) (p γ : I)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hγ0 : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1) :
    Tendsto (fun N : ℕ ↦ torusGhostThetaPDerivative d (N + 2) (by omega) p γ) atTop
      (nhds (deriv (ghostThetaPSeries d γ) p)) := by
  rw [← ghostThetaPDerivativeSeries_eq_deriv d p γ hp0 hp1 hγ0 hγ1]
  exact torusGhostTheta_pDeriv_tendsto_series d p γ hp0 hp1 hγ0 hγ1

end

end Percolation
