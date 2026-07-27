import Percolation.Bernoulli.StochasticDomination

/-!
# Numerical parameters for Liggett--Schonmann--Stacey domination

The proof of Grimmett Theorem 7.65 uses two auxiliary densities `a,p` satisfying

`(1-a)(1-p)^B ≥ 1-θ` and `(1-a)a^B ≥ 1-θ`,

where `B` is the cardinality of the dependence neighbourhood.  This file makes the
source's asymptotic choice explicit: for any desired iid density `q<1`, take
`a=p=(1+q)/2` and then choose `θ` sufficiently close to one.  The probabilistic
dilution argument is kept separate.
-/

namespace Percolation

open scoped unitInterval

/-- Auxiliary density used twice in the LSS dilution argument. -/
noncomputable def lssAuxiliaryDensity (q : ℝ) : ℝ :=
  (1 + q) / 2

/-- Positive slack available in both inequalities (7.114)--(7.115). -/
noncomputable def lssParameterSlack (B : ℕ) (q : ℝ) : ℝ :=
  min
    ((1 - lssAuxiliaryDensity q) * (1 - lssAuxiliaryDensity q) ^ B)
    ((1 - lssAuxiliaryDensity q) * lssAuxiliaryDensity q ^ B)

/-- A concrete marginal threshold strictly below one.  The factor `1/2` leaves
strict slack, which is useful when a later argument starts from a strict marginal bound. -/
noncomputable def lssMarginalThreshold (B : ℕ) (q : ℝ) : ℝ :=
  1 - lssParameterSlack B q / 2

theorem lssAuxiliaryDensity_pos {q : ℝ} (hq0 : 0 ≤ q) :
    0 < lssAuxiliaryDensity q := by
  unfold lssAuxiliaryDensity
  linarith

theorem lssAuxiliaryDensity_lt_one {q : ℝ} (hq1 : q < 1) :
    lssAuxiliaryDensity q < 1 := by
  unfold lssAuxiliaryDensity
  linarith

theorem one_sub_lssAuxiliaryDensity_pos {q : ℝ} (hq1 : q < 1) :
    0 < 1 - lssAuxiliaryDensity q := by
  linarith [lssAuxiliaryDensity_lt_one hq1]

/-- The two auxiliary Bernoulli fields retain at least the requested density. -/
theorem le_sq_lssAuxiliaryDensity (q : ℝ) :
    q ≤ lssAuxiliaryDensity q ^ 2 := by
  unfold lssAuxiliaryDensity
  nlinarith [sq_nonneg (1 - q)]

theorem lssParameterSlack_pos (B : ℕ) {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) :
    0 < lssParameterSlack B q := by
  unfold lssParameterSlack
  apply lt_min
  · exact mul_pos (one_sub_lssAuxiliaryDensity_pos hq1)
      (pow_pos (one_sub_lssAuxiliaryDensity_pos hq1) B)
  · exact mul_pos (one_sub_lssAuxiliaryDensity_pos hq1)
      (pow_pos (lssAuxiliaryDensity_pos hq0) B)

theorem lssParameterSlack_le_one (B : ℕ) {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) :
    lssParameterSlack B q ≤ 1 := by
  have ha0 : 0 ≤ lssAuxiliaryDensity q := (lssAuxiliaryDensity_pos hq0).le
  have ha1 : lssAuxiliaryDensity q ≤ 1 := (lssAuxiliaryDensity_lt_one hq1).le
  have hsub0 : 0 ≤ 1 - lssAuxiliaryDensity q :=
    (one_sub_lssAuxiliaryDensity_pos hq1).le
  have hsub1 : 1 - lssAuxiliaryDensity q ≤ 1 := by linarith
  calc
    lssParameterSlack B q ≤
        (1 - lssAuxiliaryDensity q) * (1 - lssAuxiliaryDensity q) ^ B :=
      min_le_left _ _
    _ ≤ 1 * 1 ^ B := by gcongr
    _ = 1 := by simp

theorem lssMarginalThreshold_nonneg (B : ℕ) {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) :
    0 ≤ lssMarginalThreshold B q := by
  unfold lssMarginalThreshold
  have h := lssParameterSlack_le_one B hq0 hq1
  linarith

theorem lssMarginalThreshold_lt_one (B : ℕ) {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) :
    lssMarginalThreshold B q < 1 := by
  unfold lssMarginalThreshold
  have h := lssParameterSlack_pos B hq0 hq1
  linarith

/-- Unit-interval form of the explicit LSS marginal threshold. -/
noncomputable def lssMarginalThresholdUnit (B : ℕ) (q : I)
    (hq : (q : ℝ) < 1) : I :=
  ⟨lssMarginalThreshold B q,
    lssMarginalThreshold_nonneg B q.2.1 hq,
    (lssMarginalThreshold_lt_one B q.2.1 hq).le⟩

@[simp]
theorem lssMarginalThresholdUnit_coe (B : ℕ) (q : I)
    (hq : (q : ℝ) < 1) :
    (lssMarginalThresholdUnit B q hq : ℝ) = lssMarginalThreshold B q :=
  rfl

/-- Explicit source inequalities (7.114)--(7.115), uniformly for every actual
marginal density above the selected threshold. -/
theorem lss_parameter_selection (B : ℕ) (q : I) (hq : (q : ℝ) < 1) :
    let a := lssAuxiliaryDensity (q : ℝ)
    let δ := lssMarginalThresholdUnit B q hq
    0 < a ∧ a < 1 ∧ (q : ℝ) ≤ a * a ∧ (δ : ℝ) < 1 ∧
      ∀ θ : I, δ ≤ θ →
        1 - (θ : ℝ) ≤ (1 - a) * (1 - a) ^ B ∧
        1 - (θ : ℝ) ≤ (1 - a) * a ^ B := by
  dsimp only
  refine ⟨lssAuxiliaryDensity_pos q.2.1, lssAuxiliaryDensity_lt_one hq, ?_,
    lssMarginalThreshold_lt_one B q.2.1 hq, ?_⟩
  · simpa [pow_two] using le_sq_lssAuxiliaryDensity (q : ℝ)
  · intro θ hθ
    have htheta : lssMarginalThreshold B q ≤ (θ : ℝ) := by
      exact_mod_cast hθ
    have hhalf : lssParameterSlack B q / 2 ≤ lssParameterSlack B q := by
      have hslack := (lssParameterSlack_pos B q.2.1 hq).le
      linarith
    have hone : 1 - (θ : ℝ) ≤ lssParameterSlack B q / 2 := by
      unfold lssMarginalThreshold at htheta
      linarith
    refine ⟨(hone.trans hhalf).trans ?_, (hone.trans hhalf).trans ?_⟩
    · exact min_le_left _ _
    · exact min_le_right _ _

/-- The two endpoint parameter inequalities imply the mixed factor needed after the
`N⁰/N¹` partition.  This is the final scalar comparison in the proof of (7.117). -/
theorem one_sub_le_lss_mixed_factor
    (B nzero none : ℕ) (p : I) {a theta : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hcard : nzero + none ≤ B)
    (hzero : 1 - theta ≤ (1 - a) * (1 - (p : ℝ)) ^ B)
    (hone : 1 - theta ≤ (1 - a) * a ^ B) :
    1 - theta ≤
      (1 - a) * (1 - (p : ℝ)) ^ nzero * a ^ none := by
  have hp0 : 0 ≤ (p : ℝ) := p.2.1
  have hp1 : (p : ℝ) ≤ 1 := p.2.2
  have hsub0 : 0 ≤ 1 - (p : ℝ) := by linarith
  have hsub1 : 1 - (p : ℝ) ≤ 1 := by linarith
  have honeSub : 0 ≤ 1 - a := by linarith
  by_cases hpa : 1 - (p : ℝ) ≤ a
  · calc
      1 - theta ≤ (1 - a) * (1 - (p : ℝ)) ^ B := hzero
      _ ≤ (1 - a) * (1 - (p : ℝ)) ^ (nzero + none) := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_of_le_one hsub0 hsub1 hcard) honeSub
      _ = (1 - a) * (1 - (p : ℝ)) ^ nzero *
          (1 - (p : ℝ)) ^ none := by rw [pow_add]; ring
      _ ≤ (1 - a) * (1 - (p : ℝ)) ^ nzero * a ^ none := by
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hsub0 hpa none)
          (mul_nonneg honeSub (pow_nonneg hsub0 nzero))
  · have hap : a ≤ 1 - (p : ℝ) := le_of_not_ge hpa
    calc
      1 - theta ≤ (1 - a) * a ^ B := hone
      _ ≤ (1 - a) * a ^ (nzero + none) := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_of_le_one ha0 ha1 hcard) honeSub
      _ = (1 - a) * a ^ nzero * a ^ none := by rw [pow_add]; ring
      _ ≤ (1 - a) * (1 - (p : ℝ)) ^ nzero * a ^ none := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha0 hap nzero) honeSub)
          (pow_nonneg ha0 none)

end Percolation
