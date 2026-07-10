import Percolation.Critical.BoxRadiusRate
import Percolation.Critical.ThetaContinuity
import Percolation.Bernoulli.Reliability

/-!
# Basic properties of the box-radius decay rate

This file starts Grimmett's Theorem 6.14 with the order and subcritical-positivity statements.
-/

namespace Percolation

open Filter Set Topology MeasureTheory
open scoped unitInterval ENNReal

/-- Every finite box-radius probability is a polynomial, hence continuous in the density. -/
theorem continuous_boxRadiusTail_density (d n : ℕ) :
    Continuous (fun p : I ↦ boxRadiusTail d p n) := by
  have heq : (fun p : I ↦ boxRadiusTail d p n) = fun p : I ↦
      finiteBernoulliProbability (cubicBoxEdges d cubicOrigin n) p
        (eventTrace (boxRadiusConnectionEvent d cubicOrigin n)) := by
    funext p
    exact DependsOn.bernoulliBondMeasure_real_eq_finiteBernoulliProbability
      (dependsOn_boxRadiusConnectionEvent d cubicOrigin n) p
  rw [heq]
  unfold finiteBernoulliProbability finiteBernoulliExpectation finiteBernoulliWeight
  fun_prop

/-- The continuous finite-radius approximation to the logarithmic rate.  The index is shifted
by one so that division by the radius never encounters a totalized zero denominator. -/
noncomputable def boxRadiusDecayRateApprox (d n : ℕ) (p : I) : ℝ :=
  -Real.log (boxRadiusTail d p (n + 1)) / (n + 1 : ℕ)

theorem continuousOn_boxRadiusDecayRateApprox_pos
    (d n : ℕ) (hd : 0 < d) :
    ContinuousOn (boxRadiusDecayRateApprox d n) {p : I | 0 < (p : ℝ)} := by
  intro p hp
  have htail : boxRadiusTail d p (n + 1) ≠ 0 :=
    (boxRadiusTail_pos_of_pos_density hd hp).ne'
  exact (((continuous_boxRadiusTail_density d (n + 1)).continuousAt.log htail).neg.div_const
    (n + 1 : ℕ)).continuousWithinAt

/-- The exact 6.10 error estimate, normalized into a uniform bound between the rate and its
finite-radius approximation. -/
theorem dist_boxRadiusDecayRate_approx_le
    (d : ℕ) (hd : 0 < d) (p : I) (hp : 0 < (p : ℝ)) (n : ℕ) :
    dist (boxRadiusDecayRate d p) (boxRadiusDecayRateApprox d n p) ≤
      (boxRadiusLogCorrection d (n + 1) +
        ((d - 1 : ℕ) : ℝ) * Real.log 2) / (n + 1 : ℕ) := by
  have hn : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  have hbound := abs_natCast_mul_boxRadiusDecayRate_add_log_tail_le
    d hd p hp (Nat.succ_pos n)
  rw [Real.dist_eq, boxRadiusDecayRateApprox]
  have heq : boxRadiusDecayRate d p -
      -Real.log (boxRadiusTail d p (n + 1)) / ((n + 1 : ℕ) : ℝ) =
      (((n + 1 : ℕ) : ℝ) * boxRadiusDecayRate d p +
        Real.log (boxRadiusTail d p (n + 1))) / ((n + 1 : ℕ) : ℝ) := by
    field_simp
    ring
  calc
    |boxRadiusDecayRate d p - -Real.log (boxRadiusTail d p (n + 1)) / ↑(n + 1)| =
        |((n + 1 : ℕ) : ℝ) * boxRadiusDecayRate d p +
          Real.log (boxRadiusTail d p (n + 1))| / (n + 1 : ℕ) := by
      rw [heq, abs_div, abs_of_pos hn]
    _ ≤ (boxRadiusLogCorrection d (n + 1) +
          ((d - 1 : ℕ) : ℝ) * Real.log 2) / (n + 1 : ℕ) :=
      div_le_div_of_nonneg_right hbound hn.le

/-- The finite-radius logarithmic approximations converge uniformly on all positive densities. -/
theorem boxRadiusDecayRateApprox_tendstoUniformlyOn_pos
    (d : ℕ) (hd : 0 < d) :
    TendstoUniformlyOn (boxRadiusDecayRateApprox d) (boxRadiusDecayRate d)
      atTop {p : I | 0 < (p : ℝ)} := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have herr :=
    (boxRadiusLogCorrection_add_const_div_tendsto_zero hd
      (((d - 1 : ℕ) : ℝ) * Real.log 2)).comp (tendsto_add_atTop_nat 1)
  have hevent : ∀ᶠ n : ℕ in atTop,
      (boxRadiusLogCorrection d (n + 1) +
        ((d - 1 : ℕ) : ℝ) * Real.log 2) / (n + 1 : ℕ) < ε :=
    herr (Iio_mem_nhds hε)
  filter_upwards [hevent] with n hn p hp
  exact (dist_boxRadiusDecayRate_approx_le d hd p hp n).trans_lt hn

/-- Continuity part of Grimmett's Theorem 6.14 on the meaningful positive-density domain. -/
theorem boxRadiusDecayRate_continuousOn (d : ℕ) (hd : 0 < d) :
    ContinuousOn (boxRadiusDecayRate d) {p : I | 0 < (p : ℝ)} := by
  exact (boxRadiusDecayRateApprox_tendstoUniformlyOn_pos d hd).continuousOn
    (Frequently.of_forall fun n ↦ continuousOn_boxRadiusDecayRateApprox_pos d n hd)

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

/-- The crude self-avoiding-walk estimate gives the useful lower bound
`-log ((2d)p) ≤ φ(p)`.  It is intentionally stated without assuming `(2d)p < 1`;
that additional inequality is needed only when positivity is inferred from the bound. -/
theorem neg_log_direction_count_mul_density_le_boxRadiusDecayRate
    (d : ℕ) (hd : 0 < d) (p : I) (hp : 0 < (p : ℝ)) :
    -Real.log (((2 * d : ℕ) : ℝ) * (p : ℝ)) ≤ boxRadiusDecayRate d p := by
  have hlimit := boxRadiusTail_logRate_tendsto d hd p hp
  have hconst : Tendsto
      (fun _n : ℕ ↦ -Real.log (((2 * d : ℕ) : ℝ) * (p : ℝ)))
      atTop (𝓝 (-Real.log (((2 * d : ℕ) : ℝ) * (p : ℝ)))) :=
    tendsto_const_nhds
  apply le_of_tendsto_of_tendsto hconst hlimit
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (zero_lt_one.trans_le hn)
  have htailPos := boxRadiusTail_pos_of_pos_density (d := d) (n := n) hd hp
  have hbasePos : 0 < (((2 * d : ℕ) : ℝ) * (p : ℝ)) := by positivity
  have hlog := Real.log_le_log htailPos
    (boxRadiusTail_le_direction_count_mul_density_pow d p n)
  rw [Real.log_pow] at hlog
  apply (le_div_iff₀ hnpos).2
  have hneg := neg_le_neg hlog
  nlinarith

/-- Real-density extension used to state the zero-density endpoint of Theorem 6.14. -/
noncomputable def clampedBoxRadiusDecayRate (d : ℕ) (x : ℝ) : ℝ :=
  boxRadiusDecayRate d (Set.projIcc 0 1 zero_le_one x)

/-- The zero-density assertion in Grimmett's Theorem 6.14: `φ(p) → +∞` as `p ↓ 0`. -/
theorem boxRadiusDecayRate_tendsto_top_at_zero (d : ℕ) (hd : 0 < d) :
    Tendsto (clampedBoxRadiusDecayRate d) (𝓝[>] (0 : ℝ)) atTop := by
  have hlog := Real.tendsto_log_nhdsGT_zero
  have hnegLog : Tendsto (fun x : ℝ ↦ -Real.log x)
      (𝓝[>] (0 : ℝ)) atTop := by
    simpa [Function.comp_def] using tendsto_neg_atBot_atTop.comp hlog
  have hmodel : Tendsto
      (fun x : ℝ ↦ -Real.log (((2 * d : ℕ) : ℝ) * x))
      (𝓝[>] (0 : ℝ)) atTop := by
    have hshift := tendsto_atTop_add_const_left (𝓝[>] (0 : ℝ))
      (-Real.log (((2 * d : ℕ) : ℝ))) hnegLog
    apply hshift.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : 0 < x := hx
    have hC : (0 : ℝ) < ((2 * d : ℕ) : ℝ) := by positivity
    rw [Real.log_mul hC.ne' hx0.ne']
    ring
  apply tendsto_atTop_mono' (𝓝[>] (0 : ℝ)) ?_ hmodel
  filter_upwards [self_mem_nhdsWithin,
    Filter.Eventually.filter_mono inf_le_left
      (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with x hx0 hx1
  have hxmem : x ∈ Set.Icc (0 : ℝ) 1 := ⟨hx0.le, hx1.le⟩
  have hproj : Set.projIcc 0 1 zero_le_one x =
      (⟨x, hxmem⟩ : I) := Set.projIcc_of_mem zero_le_one hxmem
  simpa [clampedBoxRadiusDecayRate, hproj] using
    neg_log_direction_count_mul_density_le_boxRadiusDecayRate
      d hd (⟨x, hxmem⟩ : I) hx0

/-- Whenever percolation already occurs with positive probability, the finite box-connection
probabilities stay bounded away from zero and their logarithmic decay rate vanishes. -/
theorem boxRadiusDecayRate_eq_zero_of_theta_pos
    (d : ℕ) (hd : 0 < d) (p : I) (hθ : 0 < theta d p) :
    boxRadiusDecayRate d p = 0 := by
  have hp : 0 < (p : ℝ) := by
    by_contra hpnot
    have hp0 : p = 0 := Subtype.ext (le_antisymm (le_of_not_gt hpnot) p.property.1)
    subst p
    have hθ0 : theta d (0 : I) = 0 := le_antisymm
      (by simpa using theta_le_selfAvoidingWalkCount_mul_pow d 1 (0 : I))
      measureReal_nonneg
    rw [hθ0] at hθ
    exact (lt_irrefl 0 hθ)
  have htail := boxRadiusTail_tendsto_theta hd p
  have hlog : Tendsto (fun n : ℕ ↦ Real.log (boxRadiusTail d p n)) atTop
      (𝓝 (Real.log (theta d p))) :=
    (Real.continuousAt_log hθ.ne').tendsto.comp htail
  have hzero : Tendsto
      (fun n : ℕ ↦ -Real.log (boxRadiusTail d p n) / (n : ℝ))
      atTop (𝓝 0) := by
    have hprod := hlog.neg.mul
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa [div_eq_mul_inv] using hprod
  exact tendsto_nhds_unique
    (boxRadiusTail_logRate_tendsto d hd p hp) hzero

/-- Above the percolation threshold the box-radius decay rate is zero. -/
theorem boxRadiusDecayRate_eq_zero_of_critical_lt
    (d : ℕ) (hd : 0 < d) (p : I)
    (hp : cubicCriticalProbability d < (p : ℝ)) :
    boxRadiusDecayRate d p = 0 :=
  boxRadiusDecayRate_eq_zero_of_theta_pos d hd p
    (theta_pos_of_criticalProbability_lt hp)

/-- The critical-point assertion in Grimmett's Theorem 6.14.  Continuity of the finite-volume
logarithmic approximations and the vanishing rate immediately above `p_c` force `φ(p_c)=0`;
no assumption that `θ(p_c)=0` is used. -/
theorem boxRadiusDecayRate_critical_eq_zero
    (d : ℕ) (hd : 2 ≤ d) :
    boxRadiusDecayRate d (cubicCriticalProbabilityUnit d hd) = 0 := by
  let pc : I := cubicCriticalProbabilityUnit d hd
  have hpc0 : 0 < (pc : ℝ) := by
    simpa [pc] using (cubicCriticalProbability_pos_lt_one hd).1
  have hpc1 : (pc : ℝ) < 1 := by
    simpa [pc] using (cubicCriticalProbability_pos_lt_one hd).2
  let qr : ℝ := ((pc : ℝ) + 1) / 2
  have hpcq : (pc : ℝ) < qr := by dsimp [qr]; linarith
  have hq1 : qr < 1 := by dsimp [qr]; linarith
  let q : I := ⟨qr, hpc0.le.trans hpcq.le, hq1.le⟩
  have hpcqI : pc < q := by exact_mod_cast hpcq
  letI : NeBot (𝓝[>] pc) := nhdsGT_neBot_of_exists_gt ⟨q, hpcqI⟩
  have hcont : ContinuousWithinAt (boxRadiusDecayRate d) (Set.Ioi pc) pc :=
    ((boxRadiusDecayRate_continuousOn d (by omega)) pc hpc0).mono fun r hr ↦
      hpc0.trans hr
  have hzero : Tendsto (boxRadiusDecayRate d) (𝓝[>] pc) (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact (boxRadiusDecayRate_eq_zero_of_critical_lt d (by omega) r
      (by simpa [pc] using (show (pc : ℝ) < (r : ℝ) by exact_mod_cast hr))).symm
  exact tendsto_nhds_unique hcont hzero

#print axioms boxRadiusDecayRate_nonneg
#print axioms boxRadiusDecayRate_antitoneOn_pos
#print axioms boxRadiusDecayRate_pos_of_lt_critical
#print axioms boxRadiusDecayRate_log_ratio_comparison
#print axioms boxRadiusDecayRate_strictAntiOn_subcritical
#print axioms boxRadiusDecayRate_tendsto_top_at_zero
#print axioms boxRadiusDecayRate_eq_zero_of_critical_lt
#print axioms boxRadiusDecayRate_critical_eq_zero

end Percolation
