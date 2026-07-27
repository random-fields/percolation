import Percolation.Extensions.LongRangeKalikowGenerator
import Mathlib.Analysis.PSeries

/-!
# Inverse-power long-range profiles

The canonical one-dimensional model in Grimmett's Theorems 12.8 and 12.9 has an independently
specified nearest-neighbour density and tail probabilities
`1 - exp (-β n^{-α})`.  This file records the literal profile and its elementary analytic
properties before the multiscale connectivity argument.
-/

namespace Percolation

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators unitInterval

/-- The canonical inverse-power bond probability, totalized to zero at distance zero and to
`max β 0` for a negative input parameter. -/
noncomputable def longRangePowerLawTailProbability (β α : ℝ) (n : ℕ) : I :=
  if hn : n = 0 then 0 else
    ⟨1 - Real.exp (-(max β 0) / (n : ℝ) ^ α), by
      constructor
      · have hden : 0 < (n : ℝ) ^ α := Real.rpow_pos_of_pos (by positivity) _
        have harg : -(max β 0) / (n : ℝ) ^ α ≤ 0 :=
          div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (le_max_right _ _)) hden.le
        linarith [Real.exp_le_one_iff.mpr harg]
      · linarith [Real.exp_pos (-(max β 0) / (n : ℝ) ^ α)]⟩

@[simp]
theorem longRangePowerLawTailProbability_zero (β α : ℝ) :
    longRangePowerLawTailProbability β α 0 = 0 := by
  simp [longRangePowerLawTailProbability]

theorem coe_longRangePowerLawTailProbability
    {β α : ℝ} {n : ℕ} (hn : n ≠ 0) :
    (longRangePowerLawTailProbability β α n : ℝ) =
      1 - Real.exp (-(max β 0) / (n : ℝ) ^ α) := by
  simp [longRangePowerLawTailProbability, hn]

/-- Replace the distance-one coordinate by `q`, leaving the inverse-power tail at distances
at least two. -/
noncomputable def longRangePowerLawProfile (q : I) (β α : ℝ) : LongRangeProfile where
  prob n := if n = 0 then 0 else if n = 1 then q else
    longRangePowerLawTailProbability β α n
  prob_zero := by simp

@[simp]
theorem longRangePowerLawProfile_zero (q : I) (β α : ℝ) :
    longRangePowerLawProfile q β α 0 = 0 := by
  simp [longRangePowerLawProfile]

@[simp]
theorem longRangePowerLawProfile_one (q : I) (β α : ℝ) :
    longRangePowerLawProfile q β α 1 = q := by
  simp [longRangePowerLawProfile]

theorem longRangePowerLawProfile_of_two_le (q : I) (β α : ℝ)
    {n : ℕ} (hn : 2 ≤ n) :
    longRangePowerLawProfile q β α n =
      longRangePowerLawTailProbability β α n := by
  simp [longRangePowerLawProfile, show n ≠ 0 by omega, show n ≠ 1 by omega]

theorem coe_longRangePowerLawProfile_of_two_le
    (q : I) {β α : ℝ} {n : ℕ} (hn : 2 ≤ n) :
    (longRangePowerLawProfile q β α n : ℝ) =
      1 - Real.exp (-(max β 0) / (n : ℝ) ^ α) := by
  rw [longRangePowerLawProfile_of_two_le q β α hn,
    coe_longRangePowerLawTailProbability (by omega)]

theorem longRangePowerLawTailProbability_pos
    {β α : ℝ} (hβ : 0 < β) {n : ℕ} (hn : 0 < n) :
    0 < (longRangePowerLawTailProbability β α n : ℝ) := by
  rw [coe_longRangePowerLawTailProbability hn.ne']
  have hden : 0 < (n : ℝ) ^ α := Real.rpow_pos_of_pos (by positivity) _
  have hquot : 0 < max β 0 / (n : ℝ) ^ α := div_pos (by simpa [hβ.le]) hden
  apply sub_pos.mpr
  apply Real.exp_lt_one_iff.mpr
  exact div_neg_of_neg_of_pos (neg_neg_of_pos (by simpa [hβ.le] using hβ)) hden

theorem longRangePowerLawTailProbability_lt_one
    {β α : ℝ} {n : ℕ} (hn : 0 < n) :
    (longRangePowerLawTailProbability β α n : ℝ) < 1 := by
  rw [coe_longRangePowerLawTailProbability hn.ne']
  linarith [Real.exp_pos (-(max β 0) / (n : ℝ) ^ α)]

/-- `1-exp(-x)≤x`, specialized to the inverse-power tail. -/
theorem longRangePowerLawTailProbability_le
    {β α : ℝ} (hβ : 0 ≤ β) {n : ℕ} (hn : 0 < n) :
    (longRangePowerLawTailProbability β α n : ℝ) ≤
      β / (n : ℝ) ^ α := by
  rw [coe_longRangePowerLawTailProbability hn.ne', max_eq_left hβ]
  have h := Real.one_sub_le_exp_neg (β / (n : ℝ) ^ α)
  have heq : -β / (n : ℝ) ^ α = -(β / (n : ℝ) ^ α) := by ring
  rw [heq]
  linarith

theorem LongRangeProfile.IsStrict.longRangePowerLaw
    (q : I) (hq : (q : ℝ) < 1) (β α : ℝ) :
    (longRangePowerLawProfile q β α).IsStrict := by
  intro n hn
  by_cases hn1 : n = 1
  · subst n
    simpa using hq
  · rw [longRangePowerLawProfile_of_two_le q β α (by omega)]
    exact longRangePowerLawTailProbability_lt_one hn

/-- For `α>1`, the total inverse-power intensity is summable. -/
theorem summable_longRangePowerLawProfile
    (q : I) {β α : ℝ} (hβ : 0 ≤ β) (hα : 1 < α) :
    Summable fun n : ℕ ↦ (longRangePowerLawProfile q β α n : ℝ) := by
  apply (summable_nat_add_iff 2).mp
  have hs0 : Summable fun n : ℕ ↦ (n : ℝ) ^ (-α) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hs : Summable fun n : ℕ ↦ ((n + 2 : ℕ) : ℝ) ^ (-α) :=
    (summable_nat_add_iff 2).mpr hs0
  have hmajor : Summable fun n : ℕ ↦ β * ((n + 2 : ℕ) : ℝ) ^ (-α) :=
    hs.mul_left β
  refine Summable.of_nonneg_of_le
    (fun n ↦ unitInterval.nonneg (longRangePowerLawProfile q β α (n + 2))) ?_ hmajor
  intro n
  rw [coe_longRangePowerLawProfile_of_two_le q (by omega)]
  calc
    1 - Real.exp (-(max β 0) / ((n + 2 : ℕ) : ℝ) ^ α) ≤
        β / ((n + 2 : ℕ) : ℝ) ^ α :=
      longRangePowerLawTailProbability_le (n := n + 2) hβ (by omega)
    _ = β * ((n + 2 : ℕ) : ℝ) ^ (-α) := by
      rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ (n + 2 : ℕ))]
      field_simp

/-- Percolation probability of the canonical profile. -/
noncomputable def longRangePowerLawTheta (q : I) (β α : ℝ) : ℝ :=
  longRangeTheta (longRangePowerLawProfile q β α)

/-- The critical nearest-neighbour parameter used in Theorems 12.8 and 12.9. -/
noncomputable def longRangePowerLawCriticalProbability (β α : ℝ) : ℝ :=
  sSup {q : ℝ | ∃ qI : I, (qI : ℝ) = q ∧ longRangePowerLawTheta qI β α = 0}

end Percolation
