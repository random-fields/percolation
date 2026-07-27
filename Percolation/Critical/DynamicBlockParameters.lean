import Percolation.Critical.BlockSuccessComposition

/-!
# Parameters for the Grimmett--Marstrand construction

This file records the dimension-uniform version of (7.26).  Starting at
`p = p_c + eta/2`, the `2d+1` possible reveal overlaps each spend
`delta = eta / (2(2d+1))`, leaving the final density at most `p_c+eta`.
-/

namespace Percolation

open scoped unitInterval

/-- Background density used by the dynamic construction. -/
noncomputable def dynamicBlockBaseDensity (pc eta : ℝ) : ℝ :=
  pc + eta / 2

/-- Per-reveal sprinkling increment.  At `d=3` this is the source's `eta/14`. -/
noncomputable def dynamicBlockIncrement (d : ℕ) (eta : ℝ) : ℝ :=
  eta / (2 * (2 * d + 1))

/-- Error assigned to each restart.  At `d=3` this is `(1-pcSite)/24`. -/
noncomputable def dynamicBlockRestartError (d : ℕ) (pcSite : ℝ) : ℝ :=
  (1 - pcSite) / (8 * d)

/-- Supercritical site density targeted by the block exploration. -/
noncomputable def dynamicBlockSiteDensity (pcSite : ℝ) : ℝ :=
  (1 + pcSite) / 2

/-- Unit-interval representative of the target coarse-site density. -/
noncomputable def dynamicBlockSiteDensityUnit (pcSite : ℝ) (hsite0 : 0 ≤ pcSite)
    (hsite1 : pcSite < 1) : I :=
  ⟨dynamicBlockSiteDensity pcSite, by
    constructor
    · unfold dynamicBlockSiteDensity
      linarith
    · unfold dynamicBlockSiteDensity
      linarith⟩

@[simp]
theorem dynamicBlockSiteDensityUnit_coe (pcSite : ℝ) (hsite0 : 0 ≤ pcSite)
    (hsite1 : pcSite < 1) :
    (dynamicBlockSiteDensityUnit pcSite hsite0 hsite1 : ℝ) =
      dynamicBlockSiteDensity pcSite :=
  rfl

theorem dynamicBlockBaseDensity_add_half (pc eta : ℝ) :
    dynamicBlockBaseDensity pc eta + eta / 2 = pc + eta := by
  simp [dynamicBlockBaseDensity]
  ring

/-- Spending the maximal `2d+1` increments uses exactly the remaining half of the density
budget. -/
theorem dynamicBlockBaseDensity_add_maxIncrement (d : ℕ) (pc eta : ℝ) :
    dynamicBlockBaseDensity pc eta +
        (2 * d + 1 : ℕ) * dynamicBlockIncrement d eta =
      pc + eta := by
  unfold dynamicBlockBaseDensity dynamicBlockIncrement
  push_cast
  have hden : (2 * (2 * (d : ℝ) + 1)) ≠ 0 := by positivity
  field_simp
  ring

theorem dynamicBlockIncrement_pos {d : ℕ} {eta : ℝ}
    (heta : 0 < eta) : 0 < dynamicBlockIncrement d eta := by
  unfold dynamicBlockIncrement
  positivity

theorem dynamicBlockRestartError_pos {d : ℕ} (hd : 0 < d)
    {pcSite : ℝ} (hsite : pcSite < 1) :
    0 < dynamicBlockRestartError d pcSite := by
  unfold dynamicBlockRestartError
  positivity

theorem dynamicBlockRestartError_le_one_eighth {d : ℕ} (hd : 0 < d)
    {pcSite : ℝ} (hsite0 : 0 ≤ pcSite) :
    dynamicBlockRestartError d pcSite ≤ 1 / 8 := by
  unfold dynamicBlockRestartError
  have hdCast : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hden : (8 : ℝ) ≤ 8 * d := by nlinarith
  have hnum : 1 - pcSite ≤ 1 := by linarith
  have hdenPos : (0 : ℝ) < 8 * d := by positivity
  calc
    (1 - pcSite) / (8 * (d : ℝ)) ≤ 1 / (8 * (d : ℝ)) :=
      div_le_div_of_nonneg_right hnum hdenPos.le
    _ ≤ 1 / 8 := by
      exact one_div_le_one_div_of_le (by norm_num) hden

theorem dynamicBlockSiteDensity_gt {pcSite : ℝ} (hsite : pcSite < 1) :
    pcSite < dynamicBlockSiteDensity pcSite := by
  unfold dynamicBlockSiteDensity
  linarith

theorem one_sub_four_d_mul_restartError_eq_siteDensity
    {d : ℕ} (hd : 0 < d) (pcSite : ℝ) :
    1 - 4 * d * dynamicBlockRestartError d pcSite =
      dynamicBlockSiteDensity pcSite := by
  unfold dynamicBlockRestartError dynamicBlockSiteDensity
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  field_simp
  ring

/-- Dimension-uniform form of the numerical inequality in (7.33). -/
theorem dynamicBlock_successFactor_gt_siteDensity
    {d : ℕ} (hd : 0 < d) {pcSite : ℝ}
    (hsite0 : 0 ≤ pcSite) (hsite1 : pcSite < 1) :
    (1 - 2 * d * dynamicBlockRestartError d pcSite) *
        (1 - dynamicBlockRestartError d pcSite) ^ (2 * d) >
      dynamicBlockSiteDensity pcSite := by
  let epsilon := dynamicBlockRestartError d pcSite
  have heps0 : 0 < epsilon := dynamicBlockRestartError_pos hd hsite1
  have hepsLe : epsilon ≤ 1 / 8 :=
    dynamicBlockRestartError_le_one_eighth hd hsite0
  have hBernoulli :
      1 - (2 * d : ℕ) * epsilon ≤ (1 - epsilon) ^ (2 * d) := by
    simpa [sub_eq_add_neg, mul_neg] using
      (one_add_mul_le_pow (a := -epsilon) (by linarith) (2 * d))
  have hx0 : 0 < (2 * d : ℕ) * epsilon := by positivity
  have hx1 : (2 * d : ℕ) * epsilon < 1 := by
    have hdCast : (1 : ℝ) ≤ d := by exact_mod_cast hd
    unfold epsilon dynamicBlockRestartError
    have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
    field_simp
    norm_num [Nat.cast_mul] at *
    nlinarith
  have hfactor0 : 0 ≤ 1 - (2 * d : ℕ) * epsilon := by linarith
  calc
    dynamicBlockSiteDensity pcSite =
        1 - 2 * ((2 * d : ℕ) * epsilon) := by
      rw [← one_sub_four_d_mul_restartError_eq_siteDensity hd pcSite]
      simp [epsilon]
      ring
    _ < (1 - (2 * d : ℕ) * epsilon) ^ 2 := by nlinarith
    _ ≤ (1 - (2 * d : ℕ) * epsilon) * (1 - epsilon) ^ (2 * d) := by
      rw [pow_two]
      exact mul_le_mul_of_nonneg_left hBernoulli hfactor0
    _ = (1 - 2 * d * dynamicBlockRestartError d pcSite) *
        (1 - dynamicBlockRestartError d pcSite) ^ (2 * d) := by
      simp [epsilon]

/-- Source-faithful success budget for a non-root block.  The two inlet link-ups consume two
restart applications.  Each of the at most `2d-1` fresh outgoing directions then consumes two
more applications: one to place a face seed and one to link that seed to the neighbouring
half-way box.  Thus Grimmett--Marstrand's safe bound is `4d` applications. -/
theorem dynamicBlock_restartPow_gt_siteDensity
    {d : ℕ} (hd : 0 < d) {pcSite : ℝ}
    (hsite0 : 0 ≤ pcSite) (hsite1 : pcSite < 1) :
    dynamicBlockSiteDensity pcSite <
      (1 - dynamicBlockRestartError d pcSite) ^ (4 * d) := by
  let epsilon := dynamicBlockRestartError d pcSite
  have heps0 : 0 ≤ epsilon := (dynamicBlockRestartError_pos hd hsite1).le
  have heps1 : epsilon ≤ 1 :=
    (dynamicBlockRestartError_le_one_eighth hd hsite0).trans (by norm_num)
  have hBernoulli :
      1 - (2 * d : ℕ) * epsilon ≤ (1 - epsilon) ^ (2 * d) := by
    simpa [sub_eq_add_neg, mul_neg] using
      (one_add_mul_le_pow (a := -epsilon) (by linarith) (2 * d))
  have hBernoulli' :
      1 - 2 * (d : ℝ) * epsilon ≤ (1 - epsilon) ^ (2 * d) := by
    simpa [Nat.cast_mul] using hBernoulli
  calc
    dynamicBlockSiteDensity pcSite <
        (1 - 2 * d * epsilon) * (1 - epsilon) ^ (2 * d) := by
      simpa [epsilon] using dynamicBlock_successFactor_gt_siteDensity hd hsite0 hsite1
    _ ≤ (1 - epsilon) ^ (2 * d) * (1 - epsilon) ^ (2 * d) := by
      exact mul_le_mul_of_nonneg_right hBernoulli'
        (pow_nonneg (sub_nonneg.mpr heps1) _)
    _ = (1 - epsilon) ^ (4 * d) := by
      rw [← pow_add]
      congr 1
      omega

/-- Compatibility inequality for the earlier compressed schedule.  The inequality is true, but
the literal spatial construction does not use it: a fresh outgoing direction needs both a
face-seed application and a subsequent half-way-box link-up, so the concrete program uses the
`4d` theorem above. -/
theorem dynamicBlock_laterSiteRestartPow_gt_siteDensity
    {d : ℕ} (hd : 0 < d) {pcSite : ℝ}
    (hsite0 : 0 ≤ pcSite) (hsite1 : pcSite < 1) :
    dynamicBlockSiteDensity pcSite <
      (1 - dynamicBlockRestartError d pcSite) ^ (2 * d + 1) := by
  let epsilon := dynamicBlockRestartError d pcSite
  have heps0 : 0 ≤ epsilon := (dynamicBlockRestartError_pos hd hsite1).le
  have heps1 : epsilon ≤ 1 :=
    (dynamicBlockRestartError_le_one_eighth hd hsite0).trans (by norm_num)
  have hdCast : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hfirst :
      1 - 2 * (d : ℝ) * epsilon ≤ 1 - epsilon := by
    nlinarith
  calc
    dynamicBlockSiteDensity pcSite <
        (1 - 2 * d * epsilon) * (1 - epsilon) ^ (2 * d) := by
      simpa [epsilon] using
        dynamicBlock_successFactor_gt_siteDensity hd hsite0 hsite1
    _ ≤ (1 - epsilon) * (1 - epsilon) ^ (2 * d) :=
      mul_le_mul_of_nonneg_right hfirst (pow_nonneg (sub_nonneg.mpr heps1) _)
    _ = (1 - epsilon) ^ (2 * d + 1) := by
      rw [pow_succ']
    _ = (1 - dynamicBlockRestartError d pcSite) ^ (2 * d + 1) := by
      rfl

/-- Exact (7.34) budget: starting at `p_c+eta/2`, all `2d+1` reveal charges remain below
`p_c+eta`. -/
theorem FiniteRevealSchedule.accumulatedThreshold_le_dynamicBlockBudget
    {iota : Type*} [DecidableEq iota]
    (S : FiniteRevealSchedule iota) (d : ℕ)
    (hS : S.HasOverlapBound (2 * d + 1))
    (pc eta : ℝ) (heta : 0 ≤ eta) (e : iota) :
    S.accumulatedThreshold (dynamicBlockBaseDensity pc eta)
        (dynamicBlockIncrement d eta) e ≤ pc + eta := by
  have hhalf : 0 ≤ eta / 2 := by positivity
  have hbudget := S.accumulatedThreshold_le_add_budget (b := 2 * d + 1)
    (by omega) hS (dynamicBlockBaseDensity pc eta) (eta / 2) hhalf e
  have hdelta : (eta / 2) / (2 * d + 1 : ℕ) = dynamicBlockIncrement d eta := by
    unfold dynamicBlockIncrement
    push_cast
    field_simp
  rw [hdelta] at hbudget
  calc
    S.accumulatedThreshold (dynamicBlockBaseDensity pc eta)
        (dynamicBlockIncrement d eta) e ≤
        dynamicBlockBaseDensity pc eta + eta / 2 := hbudget
    _ = pc + eta := dynamicBlockBaseDensity_add_half pc eta

end Percolation
