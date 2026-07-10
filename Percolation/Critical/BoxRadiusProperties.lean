import Percolation.Critical.BoxRadiusRate
import Percolation.Bernoulli.Reliability

/-!
# Basic properties of the box-radius decay rate

This file starts Grimmett's Theorem 6.14 with the order and subcritical-positivity statements.
-/

namespace Percolation

open Filter Set Topology MeasureTheory
open scoped unitInterval ENNReal

/-- The box-radius decay rate is nonnegative on its source domain. -/
theorem boxRadiusDecayRate_nonneg
    (d : ℕ) (hd : 0 < d) (p : I) (hp : 0 < (p : ℝ)) :
    0 ≤ boxRadiusDecayRate d p := by
  have hlimit := boxRadiusTail_logRate_tendsto d hd p hp
  have hzero : Tendsto (fun _n : ℕ ↦ (0 : ℝ)) atTop (𝓝 0) := tendsto_const_nhds
  apply le_of_tendsto_of_tendsto hzero hlimit
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hnreal : (0 : ℝ) ≤ n := by positivity
  have hlog : Real.log (boxRadiusTail d p n) ≤ 0 :=
    Real.log_nonpos (boxRadiusTail_pos_of_pos_density hd hp).le measureReal_le_one
  exact div_nonneg (neg_nonneg.mpr hlog) hnreal

/-- Increasing the density can only decrease the logarithmic decay rate. -/
theorem boxRadiusDecayRate_antitoneOn_pos (d : ℕ) (hd : 0 < d) :
    AntitoneOn (boxRadiusDecayRate d) {p : I | 0 < (p : ℝ)} := by
  intro p hp q hq hpq
  have hpLimit := boxRadiusTail_logRate_tendsto d hd p hp
  have hqLimit := boxRadiusTail_logRate_tendsto d hd q hq
  apply le_of_tendsto_of_tendsto hqLimit hpLimit
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hpn := boxRadiusTail_mono_density d n hpq
  have hpTail := boxRadiusTail_pos_of_pos_density hd (n := n) hp
  have hlog := Real.log_le_log hpTail hpn
  have hnreal : (0 : ℝ) ≤ n := by positivity
  exact div_le_div_of_nonneg_right (neg_le_neg hlog) hnreal

/-- Below the critical density the decay rate is strictly positive. -/
theorem boxRadiusDecayRate_pos_of_lt_critical
    (d : ℕ) (hd : 2 ≤ d) (p : I) (hp0 : 0 < (p : ℝ))
    (hp : (p : ℝ) < cubicCriticalProbability d) :
    0 < boxRadiusDecayRate d p := by
  have hchi : susceptibility d p < ⊤ :=
    susceptibility_lt_top_of_lt_critical d hd p hp
  obtain ⟨c, hc, hdecay⟩ :=
    boxRadiusTail_exponential_decay_of_susceptibility_lt_top d hd p hchi
  have hlimit := boxRadiusTail_logRate_tendsto d (by omega) p hp0
  have hconst : Tendsto (fun _n : ℕ ↦ c) atTop (𝓝 c) := tendsto_const_nhds
  have hcle : c ≤ boxRadiusDecayRate d p := by
    apply le_of_tendsto_of_tendsto hconst hlimit
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hnpos : 0 < n := zero_lt_one.trans_le hn
    have htail := boxRadiusTail_pos_of_pos_density (d := d) (n := n) (by omega) hp0
    have hlog := Real.log_le_log htail (hdecay n)
    rw [Real.log_exp] at hlog
    have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
    apply (le_div_iff₀ hnreal).2
    nlinarith
  exact hc.trans_le hcle

/-- Limit form of the reliability comparison used in equation (6.40). -/
theorem boxRadiusDecayRate_div_log_le
    (d : ℕ) (hd : 0 < d) {a b : I}
    (ha0 : 0 < (a : ℝ)) (hab : (a : ℝ) ≤ (b : ℝ)) (hb1 : (b : ℝ) < 1) :
    boxRadiusDecayRate d a / Real.log (a : ℝ) ≤
      boxRadiusDecayRate d b / Real.log (b : ℝ) := by
  have hb0 : 0 < (b : ℝ) := ha0.trans_le hab
  have hla : Real.log (a : ℝ) ≠ 0 :=
    ne_of_lt (Real.log_neg ha0 (hab.trans_lt hb1))
  have hlb : Real.log (b : ℝ) ≠ 0 := ne_of_lt (Real.log_neg hb0 hb1)
  have haLim := (boxRadiusTail_logRate_tendsto d hd a ha0).div_const (Real.log (a : ℝ))
  have hbLim := (boxRadiusTail_logRate_tendsto d hd b hb0).div_const (Real.log (b : ℝ))
  apply le_of_tendsto_of_tendsto haLim hbLim
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hrel := DependsOn.bernoulliBondMeasure_real_logRatio_antitone
      (dependsOn_boxRadiusConnectionEvent d cubicOrigin n)
      (isIncreasingEvent_boxRadiusConnectionEvent d cubicOrigin n) ha0 hab hb1
  have hnreal : (0 : ℝ) < n := by exact_mod_cast (zero_lt_one.trans_le hn)
  have hscale : (-1 / (n : ℝ)) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by norm_num) hnreal.le
  have hmul := mul_le_mul_of_nonpos_left hrel hscale
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul

/-- Grimmett's comparison inequality (6.40), on the meaningful domain `b < 1`. -/
theorem boxRadiusDecayRate_log_ratio_comparison
    (d : ℕ) (hd : 0 < d) {a b : I}
    (ha0 : 0 < (a : ℝ)) (hab : (a : ℝ) ≤ (b : ℝ)) (hb1 : (b : ℝ) < 1) :
    boxRadiusDecayRate d b *
        (Real.log (1 / (a : ℝ)) / Real.log (1 / (b : ℝ))) ≤
      boxRadiusDecayRate d a := by
  have hb0 : 0 < (b : ℝ) := ha0.trans_le hab
  have hloga : Real.log (1 / (a : ℝ)) = -Real.log (a : ℝ) := by
    rw [Real.log_div (by norm_num) ha0.ne', Real.log_one, zero_sub]
  have hlogb : Real.log (1 / (b : ℝ)) = -Real.log (b : ℝ) := by
    rw [Real.log_div (by norm_num) hb0.ne', Real.log_one, zero_sub]
  have hratio := boxRadiusDecayRate_div_log_le d hd ha0 hab hb1
  have hlaNeg : Real.log (a : ℝ) < 0 := Real.log_neg ha0 (hab.trans_lt hb1)
  have hlbNeg : Real.log (b : ℝ) < 0 := Real.log_neg hb0 hb1
  have hcross := (div_le_iff_of_neg hlaNeg).mp hratio
  rw [hloga, hlogb]
  convert hcross using 1
  field_simp [hlbNeg.ne]

/-- The decay rate is strictly decreasing throughout the subcritical interval. -/
theorem boxRadiusDecayRate_strictAntiOn_subcritical
    (d : ℕ) (hd : 2 ≤ d) :
    StrictAntiOn (boxRadiusDecayRate d)
      {p : I | 0 < (p : ℝ) ∧ (p : ℝ) < cubicCriticalProbability d} := by
  intro a ha b hb hab
  have hpc1 : cubicCriticalProbability d < 1 :=
    (cubicCriticalProbability_pos_lt_one hd).2
  have hb1 : (b : ℝ) < 1 := hb.2.trans hpc1
  have hcomp := boxRadiusDecayRate_log_ratio_comparison d (by omega)
    ha.1 hab.le hb1
  have hloga : Real.log (1 / (a : ℝ)) = -Real.log (a : ℝ) := by
    rw [Real.log_div (by norm_num) ha.1.ne', Real.log_one, zero_sub]
  have hlogb : Real.log (1 / (b : ℝ)) = -Real.log (b : ℝ) := by
    rw [Real.log_div (by norm_num) (ha.1.trans hab).ne', Real.log_one, zero_sub]
  have hlogbPos : 0 < Real.log (1 / (b : ℝ)) := by
    rw [hlogb]
    exact neg_pos.mpr (Real.log_neg (ha.1.trans hab) hb1)
  have hlogStrict : Real.log (1 / (b : ℝ)) < Real.log (1 / (a : ℝ)) := by
    rw [hloga, hlogb]
    exact neg_lt_neg (Real.log_lt_log ha.1 hab)
  have hratio : 1 < Real.log (1 / (a : ℝ)) / Real.log (1 / (b : ℝ)) :=
    (one_lt_div hlogbPos).2 hlogStrict
  have hphiB : 0 < boxRadiusDecayRate d b :=
    boxRadiusDecayRate_pos_of_lt_critical d hd b hb.1 hb.2
  calc
    boxRadiusDecayRate d b < boxRadiusDecayRate d b *
        (Real.log (1 / (a : ℝ)) / Real.log (1 / (b : ℝ))) :=
      by nlinarith [mul_pos hphiB (sub_pos.mpr hratio)]
    _ ≤ boxRadiusDecayRate d a := hcomp

#print axioms boxRadiusDecayRate_nonneg
#print axioms boxRadiusDecayRate_antitoneOn_pos
#print axioms boxRadiusDecayRate_pos_of_lt_critical
#print axioms boxRadiusDecayRate_log_ratio_comparison
#print axioms boxRadiusDecayRate_strictAntiOn_subcritical

end Percolation
