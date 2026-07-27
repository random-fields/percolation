import Percolation.Critical.GhostDifferential
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# The square-root ghost-field lower bound

This file proves Grimmett's Proposition 5.49 from the ghost differential inequalities.
-/

namespace Percolation

open Set Filter
open scoped unitInterval Topology

noncomputable section

@[simp]
theorem ghostThetaSeries_zero (d : ℕ) (p : I) :
    ghostThetaSeries d p 0 = theta d p := by
  unfold ghostThetaSeries
  simp only [sub_zero, one_pow, one_mul]
  rw [tsum_finiteClusterSizeProbability_eq_one_sub_theta]
  ring

theorem ghostSusceptibilitySeries_ne_top {d : ℕ} {p : I} {y : ℝ}
    (hy0 : 0 < y) (hy1 : y < 1) :
    ghostSusceptibilitySeries d p y ≠ ⊤ := by
  have hr0 : 0 ≤ 1 - y := by linarith
  have hr1 : ‖1 - y‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hr0]
    linarith
  have hgeom : Summable (fun n : ℕ ↦ (n : ℝ) * (1 - y) ^ n) := by
    simpa [pow_one] using
      (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hr1)
  have hsum : Summable (fun n : ℕ ↦
      (n : ℝ) * (1 - y) ^ n * finiteClusterSizeProbability d p n) := by
    apply hgeom.of_norm_bounded
    intro n
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow,
      abs_of_nonneg (Nat.cast_nonneg n), abs_of_nonneg hr0,
      abs_of_nonneg (finiteClusterSizeProbability_nonneg d p n)]
    simpa [mul_assoc] using mul_le_mul_of_nonneg_left
      (mul_le_of_le_one_right (pow_nonneg hr0 n)
        (finiteClusterSizeProbability_le_one d p n)) (Nat.cast_nonneg n)
  rw [ghostSusceptibilitySeries_eq_ofReal_tsum hr0 hsum]
  exact ENNReal.ofReal_ne_top

/-- Under infinite finite-cluster susceptibility, the green-field derivative diverges at
zero from the right. -/
theorem ghostThetaSeries_deriv_tendsto_atTop_of_finiteSusceptibility_eq_top
    (d : ℕ) (p : I) (htop : finiteSusceptibility d p = ⊤) :
    Tendsto (deriv (ghostThetaSeries d p)) (nhdsWithin 0 (Ioi 0)) atTop := by
  have hchi := ghostSusceptibility_tendsto_finiteSusceptibility d p
  rw [htop] at hchi
  apply Filter.tendsto_atTop.mpr
  intro B
  obtain ⟨M : ℕ, hM⟩ := exists_nat_gt B
  have hevent : ∀ᶠ y : ℝ in nhdsWithin 0 (Ioi 0),
      (M : ENNReal) < ghostSusceptibilitySeries d p y :=
    hchi (Ioi_mem_nhds (ENNReal.natCast_lt_top M))
  filter_upwards [hevent,
    (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono inf_le_left,
    self_mem_nhdsWithin] with y hyChi hy1 hy0
  simp only [Set.mem_Ioi] at hy0
  let yI : I := ⟨y, hy0.le, hy1.le⟩
  have hne : ghostSusceptibility d p yI ≠ ⊤ := by
    rw [ghostSusceptibility_eq_ghostSusceptibilitySeries d p yI hy0]
    exact ghostSusceptibilitySeries_ne_top hy0 hy1
  have hchiReal : (M : ℝ) < (ghostSusceptibility d p yI).toReal := by
    rw [ghostSusceptibility_eq_ghostSusceptibilitySeries d p yI hy0]
    exact (ENNReal.toReal_lt_toReal (ENNReal.natCast_ne_top M)
      (ghostSusceptibilitySeries_ne_top hy0 hy1)).mpr hyChi
  rw [ghostSusceptibility_eq_deriv d p yI hy0 hy1] at hchiReal
  exact le_of_lt (hM.trans (lt_of_lt_of_le hchiReal (by
    have := ghostThetaSeries_hasDerivAt d p hy0 hy1
    have hderivNonneg : 0 ≤ deriv (ghostThetaSeries d p) y := by
      rw [this.deriv]
      exact tsum_nonneg fun n ↦ mul_nonneg
        (mul_nonneg (Nat.cast_nonneg n) (pow_nonneg (by linarith) _))
        (finiteClusterSizeProbability_nonneg d p n)
    nlinarith)))

/-- Equation (5.55), written in the reciprocal form used after inversion in the source. -/
theorem ghostThetaSeries_ratio_tendsto_zero_of_finiteSusceptibility_eq_top
    (d : ℕ) (p : I) (htop : finiteSusceptibility d p = ⊤)
    (htheta : theta d p = 0) :
    Tendsto (fun y : ℝ ↦ y / ghostThetaSeries d p y)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  let f := ghostThetaSeries d p
  have hf0 : f 0 = theta d p := ghostThetaSeries_zero d p
  have hright : ContinuousWithinAt f (Ici 0) 0 := by
    rw [← continuousWithinAt_Ioi_iff_Ici]
    change Tendsto f (nhdsWithin 0 (Ioi 0)) (nhds (f 0))
    rw [hf0]
    exact ghostTheta_tendsto_theta d p
  have hderiv :=
    ghostThetaSeries_deriv_tendsto_atTop_of_finiteSusceptibility_eq_top d p htop
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hevent : ∀ᶠ x : ℝ in nhdsWithin 0 (Ioi 0),
      2 / ε ≤ deriv f x :=
    hderiv (eventually_ge_atTop (2 / ε))
  have hevent' : ∀ᶠ x : ℝ in nhds 0, x ∈ Ioi (0 : ℝ) →
      2 / ε ≤ deriv f x :=
    eventually_nhdsWithin_iff.mp hevent
  obtain ⟨δ, hδ0, hδ⟩ := Metric.mem_nhds_iff.mp hevent'
  filter_upwards [Filter.Eventually.filter_mono inf_le_left
      (Metric.ball_mem_nhds 0 hδ0),
    (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono inf_le_left,
    self_mem_nhdsWithin] with y hyBall hy1 hy0
  simp only [Set.mem_Ioi] at hy0
  have hyδ : y < δ := by
    simpa [Real.dist_eq, abs_of_pos hy0] using hyBall
  have hcont : ContinuousOn f (Icc 0 y) := by
    intro x hx
    rcases eq_or_lt_of_le hx.1 with rfl | hx0
    · exact hright.mono Icc_subset_Ici_self
    · exact (ghostThetaSeries_hasDerivAt d p hx0 (hx.2.trans_lt hy1)).continuousAt
        |>.continuousWithinAt
  have hhasDeriv : ∀ x ∈ Ioo 0 y, HasDerivAt f (deriv f x) x := by
    intro x hx
    have h := ghostThetaSeries_hasDerivAt d p hx.1 (hx.2.trans hy1)
    convert h using 1
    exact h.deriv
  obtain ⟨c, hc, hcSlope⟩ :=
    exists_hasDerivAt_eq_slope f (deriv f) hy0 hcont hhasDeriv
  have hcBall : c ∈ Metric.ball (0 : ℝ) δ := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hc.1]
    exact hc.2.trans hyδ
  have hcDeriv : 2 / ε ≤ deriv f c := hδ hcBall hc.1
  have hslope : 2 / ε ≤ f y / y := by
    simpa [hf0, htheta] using
      (hcDeriv.trans_eq hcSlope)
  have hmul : 2 * y ≤ f y * ε :=
    (div_le_div_iff₀ hε hy0).mp hslope
  have hfy : 0 < f y := by nlinarith
  have hyε : y < ε * f y := by nlinarith [hmul]
  have hratio : y / f y < ε := (div_lt_iff₀ hfy).mpr hyε
  rw [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hy0.le hfy.le)]
  exact hratio

noncomputable def ghostSqrtComparisonConstant (d : ℕ) (p : I) : ℝ :=
  (2 * d : ℝ) * (p : ℝ) / (1 - (p : ℝ))

/-- Differential form of the inverse-function estimate in the proof of Proposition 5.49. -/
theorem ghostThetaSeries_ratio_deriv_le
    (d : ℕ) (p : I) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    {y : ℝ} (hy0 : 0 < y) (hy1 : y < 1)
    (hfy : 0 < ghostThetaSeries d p y) :
    deriv (fun x : ℝ ↦ x / ghostThetaSeries d p x) y ≤
      deriv (fun x : ℝ ↦ x + ghostSqrtComparisonConstant d p *
        ghostThetaSeries d p x) y := by
  let f := ghostThetaSeries d p
  let C := ghostSqrtComparisonConstant d p
  let yI : I := ⟨y, hy0.le, hy1.le⟩
  have hf := ghostThetaSeries_hasDerivAt d p hy0 hy1
  have hf' : 0 ≤ deriv f y := by
    rw [hf.deriv]
    exact tsum_nonneg fun n ↦ mul_nonneg
      (mul_nonneg (Nat.cast_nonneg n) (pow_nonneg (by linarith) _))
      (finiteClusterSizeProbability_nonneg d p n)
  have h51 := ghostTheta_p_deriv_le d p yI hp0 hp1 hy0 hy1
  have h53 := ghostTheta_le_differential d p yI hp0 hp1 hy0 hy1
  rw [ghostTheta_eq_ghostThetaSeries d p yI hy0] at h51 h53
  have hq : 0 < 1 - (p : ℝ) := sub_pos.mpr hp1
  have hscale : 0 ≤ (p : ℝ) * f y / (1 - (p : ℝ)) :=
    div_nonneg (mul_nonneg hp0.le hfy.le) hq.le
  have hpBound : (p : ℝ) * f y * deriv (ghostThetaPSeries d yI) p ≤
      C * (1 - y) * f y ^ 2 * deriv f y := by
    calc
      (p : ℝ) * f y * deriv (ghostThetaPSeries d yI) p =
          ((p : ℝ) * f y / (1 - (p : ℝ))) *
            ((1 - (p : ℝ)) * deriv (ghostThetaPSeries d yI) p) := by
        field_simp
      _ ≤ ((p : ℝ) * f y / (1 - (p : ℝ))) *
          ((2 * d : ℕ) * (1 - y) * f y * deriv f y) :=
        mul_le_mul_of_nonneg_left h51 hscale
      _ = C * (1 - y) * f y ^ 2 * deriv f y := by
        unfold C ghostSqrtComparisonConstant
        field_simp
        push_cast
        ring
  have hC : 0 ≤ C := by
    unfold C ghostSqrtComparisonConstant
    exact div_nonneg (mul_nonneg (by positivity) hp0.le) hq.le
  have hcombined : f y ≤
      y * deriv f y + f y ^ 2 + C * f y ^ 2 * deriv f y := by
    have hdrop : C * (1 - y) * f y ^ 2 * deriv f y ≤
        C * f y ^ 2 * deriv f y := by
      nlinarith [mul_nonneg hC (mul_nonneg (sq_nonneg (f y)) hf')]
    nlinarith [h53, hpBound]
  have hratio := (hasDerivAt_id y).div hf hfy.ne'
  have hcomparison := (hasDerivAt_id y).add (hf.const_mul C)
  change deriv (id / f) y ≤ deriv (id + fun x ↦ C * f x) y
  rw [hratio.deriv, hcomparison.deriv, ← hf.deriv]
  apply (div_le_iff₀ (sq_pos_of_pos hfy)).mpr
  simp only [one_mul, id_eq]
  change f y - y * deriv f y ≤ (1 + C * deriv f y) * f y ^ 2
  ring_nf at hcombined ⊢
  linarith

theorem exists_ghostThetaSeries_pos_of_finiteSusceptibility_eq_top
    (d : ℕ) (p : I) (htop : finiteSusceptibility d p = ⊤)
    (htheta : theta d p = 0) :
    ∃ δ > 0, δ ≤ 1 ∧ ∀ y, 0 < y → y < δ → 0 < ghostThetaSeries d p y := by
  let f := ghostThetaSeries d p
  have hf0 : f 0 = 0 := by simp [f, htheta]
  have hright : ContinuousWithinAt f (Ici 0) 0 := by
    rw [← continuousWithinAt_Ioi_iff_Ici]
    change Tendsto f (nhdsWithin 0 (Ioi 0)) (nhds (f 0))
    rw [hf0]
    simpa [htheta] using ghostTheta_tendsto_theta d p
  have hderiv :=
    ghostThetaSeries_deriv_tendsto_atTop_of_finiteSusceptibility_eq_top d p htop
  have hevent : ∀ᶠ x : ℝ in nhdsWithin 0 (Ioi 0), 1 ≤ deriv f x :=
    hderiv (eventually_ge_atTop 1)
  have hevent' : ∀ᶠ x : ℝ in nhds 0, x ∈ Ioi (0 : ℝ) →
      1 ≤ deriv f x := eventually_nhdsWithin_iff.mp hevent
  obtain ⟨ε, hε0, hε⟩ := Metric.mem_nhds_iff.mp hevent'
  let δ := min ε 1
  have hδ0 : 0 < δ := lt_min hε0 zero_lt_one
  refine ⟨δ, hδ0, min_le_right _ _, ?_⟩
  intro y hy0 hyδ
  have hy1 : y < 1 := hyδ.trans_le (min_le_right _ _)
  have hcont : ContinuousOn f (Icc 0 y) := by
    intro x hx
    rcases eq_or_lt_of_le hx.1 with rfl | hx0
    · exact hright.mono Icc_subset_Ici_self
    · exact (ghostThetaSeries_hasDerivAt d p hx0 (hx.2.trans_lt hy1)).continuousAt
        |>.continuousWithinAt
  have hdiff : DifferentiableOn ℝ f (interior (Icc 0 y)) := by
    rw [interior_Icc]
    intro x hx
    exact (ghostThetaSeries_hasDerivAt d p hx.1 (hx.2.trans hy1)).differentiableAt
      |>.differentiableWithinAt
  have hderivOne : ∀ x ∈ interior (Icc 0 y), 1 ≤ deriv f x := by
    rw [interior_Icc]
    intro x hx
    apply hε
    · rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hx.1]
      exact hx.2.trans (hyδ.trans_le (min_le_left _ _))
    · exact hx.1
  have hgrowth := (convex_Icc 0 y).mul_sub_le_image_sub_of_le_deriv
    hcont hdiff hderivOne 0 (left_mem_Icc.mpr hy0.le) y
    (right_mem_Icc.mpr hy0.le) hy0.le
  rw [hf0] at hgrowth
  nlinarith

/-- Integrated form of the inverse-function estimate in Proposition 5.49.  Working with
`y / theta(p,y)` is equivalent to the inverse-function calculation in Grimmett, but avoids
choosing a local inverse as additional data. -/
theorem ghostThetaSeries_ratio_le_comparison
    (d : ℕ) (p : I) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (htop : finiteSusceptibility d p = ⊤) (htheta : theta d p = 0)
    {δ y : ℝ} (hδpos : ∀ x, 0 < x → x < δ → 0 < ghostThetaSeries d p x)
    (hy0 : 0 < y) (hyδ : y < δ) (hy1 : y < 1) :
    y / ghostThetaSeries d p y ≤
      y + ghostSqrtComparisonConstant d p * ghostThetaSeries d p y := by
  let f := ghostThetaSeries d p
  let C := ghostSqrtComparisonConstant d p
  let ratio := fun x : ℝ ↦ x / f x
  let comparison := fun x : ℝ ↦ x + C * f x
  have hratioT : Tendsto ratio (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    simpa [ratio, f] using
      ghostThetaSeries_ratio_tendsto_zero_of_finiteSusceptibility_eq_top d p htop htheta
  have hfT : Tendsto f (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    simpa [f, htheta] using ghostTheta_tendsto_theta d p
  have hidT : Tendsto (fun x : ℝ ↦ x) (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    have hid : Tendsto (id : ℝ → ℝ) (nhds 0) (nhds 0) := tendsto_id
    simpa using hid.mono_left inf_le_left
  have hcomparisonT : Tendsto comparison (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    simpa [comparison] using hidT.add (hfT.const_mul C)
  have hevent : ∀ᶠ z : ℝ in nhdsWithin 0 (Ioi 0),
      ratio y - ratio z ≤ comparison y - comparison z := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hy0).filter_mono inf_le_left] with z hz0 hzy
    simp only [mem_Ioi] at hz0
    have hzδ : z < δ := hzy.trans hyδ
    have hzyLe : z ≤ y := hzy.le
    have hHcont : ContinuousOn (fun x ↦ comparison x - ratio x) (Icc z y) := by
      intro x hx
      have hx0 : 0 < x := hz0.trans_le hx.1
      have hxδ : x < δ := hx.2.trans_lt hyδ
      have hfx : 0 < f x := hδpos x hx0 hxδ
      have hf := ghostThetaSeries_hasDerivAt d p hx0 (hx.2.trans_lt hy1)
      exact ((hasDerivAt_id x).add (hf.const_mul C)).sub
        ((hasDerivAt_id x).div hf hfx.ne') |>.continuousAt.continuousWithinAt
    have hHdiff : DifferentiableOn ℝ (fun x ↦ comparison x - ratio x)
        (interior (Icc z y)) := by
      rw [interior_Icc]
      intro x hx
      have hx0 : 0 < x := hz0.trans hx.1
      have hxδ : x < δ := hx.2.trans hyδ
      have hfx : 0 < f x := hδpos x hx0 hxδ
      have hf := ghostThetaSeries_hasDerivAt d p hx0 (hx.2.trans hy1)
      exact (((hasDerivAt_id x).add (hf.const_mul C)).sub
        ((hasDerivAt_id x).div hf hfx.ne')).differentiableAt.differentiableWithinAt
    have hHderiv : ∀ x ∈ interior (Icc z y),
        0 ≤ deriv (fun x ↦ comparison x - ratio x) x := by
      rw [interior_Icc]
      intro x hx
      have hx0 : 0 < x := hz0.trans hx.1
      have hxδ : x < δ := hx.2.trans hyδ
      have hfx : 0 < f x := hδpos x hx0 hxδ
      have hf := ghostThetaSeries_hasDerivAt d p hx0 (hx.2.trans hy1)
      have hratio := (hasDerivAt_id x).div hf hfx.ne'
      have hcomparison := (hasDerivAt_id x).add (hf.const_mul C)
      have hH := hcomparison.sub hratio
      change HasDerivAt (fun x ↦ comparison x - ratio x) _ x at hH
      rw [hH.deriv]
      have hle :=
        ghostThetaSeries_ratio_deriv_le d p hp0 hp1 hx0 (hx.2.trans hy1) hfx
      have hle' : deriv ratio x ≤ deriv comparison x := by
        simpa [ratio, comparison, f, C] using hle
      have hratioDeriv := hratio.deriv
      change deriv ratio x = _ at hratioDeriv
      have hcomparisonDeriv := hcomparison.deriv
      change deriv comparison x = _ at hcomparisonDeriv
      rw [hratioDeriv, hcomparisonDeriv] at hle'
      exact sub_nonneg.mpr hle'
    have hgrowth := (convex_Icc z y).mul_sub_le_image_sub_of_le_deriv
      hHcont hHdiff hHderiv z (left_mem_Icc.mpr hzyLe) y
      (right_mem_Icc.mpr hzyLe) hzyLe
    simp only [zero_mul] at hgrowth
    linarith
  have hlim := le_of_tendsto_of_tendsto
    (tendsto_const_nhds.sub hratioT) (tendsto_const_nhds.sub hcomparisonT) hevent
  simpa [ratio, comparison, f, C] using hlim

/-- Grimmett, Proposition 5.49.  If the finite-cluster susceptibility is infinite, then the
ghost-field order parameter is bounded below by a positive multiple of `sqrt γ` for all
sufficiently small positive ghost densities. -/
theorem ghostTheta_ge_sqrt
    (d : ℕ) (hd : 2 ≤ d) (p : I) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (htop : finiteSusceptibility d p = ⊤) :
    ∃ α > 0, ∃ γ₀ > 0, γ₀ ≤ 1 ∧ ∀ γ : I,
      0 < (γ : ℝ) → (γ : ℝ) < γ₀ →
        α * Real.sqrt (γ : ℝ) ≤ ghostTheta d p γ := by
  let f := ghostThetaSeries d p
  have hthetaNonneg : 0 ≤ theta d p := MeasureTheory.measureReal_nonneg
  rcases hthetaNonneg.eq_or_lt with htheta | htheta
  · have htheta0 : theta d p = 0 := htheta.symm
    obtain ⟨δ, hδ0, hδ1, hδpos⟩ :=
      exists_ghostThetaSeries_pos_of_finiteSusceptibility_eq_top d p htop htheta0
    let C := ghostSqrtComparisonConstant d p
    have hd0 : 0 < (d : ℝ) := by positivity
    have hC : 0 < C := by
      dsimp [C, ghostSqrtComparisonConstant]
      exact div_pos (mul_pos (mul_pos (by norm_num) hd0) hp0) (sub_pos.mpr hp1)
    have hfT : Tendsto f (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
      simpa [f, htheta0] using ghostTheta_tendsto_theta d p
    have hsmall : ∀ᶠ y : ℝ in nhdsWithin 0 (Ioi 0), f y < 1 / 2 :=
      hfT (Iio_mem_nhds (by norm_num))
    have hsmall' : ∀ᶠ y : ℝ in nhds 0, y ∈ Ioi (0 : ℝ) → f y < 1 / 2 :=
      eventually_nhdsWithin_iff.mp hsmall
    obtain ⟨ε, hε0, hε⟩ := Metric.mem_nhds_iff.mp hsmall'
    let γ₀ := min δ (min ε 1)
    have hγ₀0 : 0 < γ₀ := lt_min hδ0 (lt_min hε0 zero_lt_one)
    let α := (Real.sqrt (2 * C))⁻¹
    have hroot : 0 < Real.sqrt (2 * C) := Real.sqrt_pos.2 (mul_pos (by norm_num) hC)
    have hα : 0 < α := inv_pos.mpr hroot
    refine ⟨α, hα, γ₀, hγ₀0, (min_le_right _ _).trans (min_le_right _ _), ?_⟩
    intro γ hγ0 hγγ₀
    have hγδ : (γ : ℝ) < δ := hγγ₀.trans_le (min_le_left _ _)
    have hγε : (γ : ℝ) < ε :=
      hγγ₀.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    have hfpos : 0 < f γ := hδpos γ hγ0 hγδ
    have hball : (γ : ℝ) ∈ Metric.ball (0 : ℝ) ε := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hγ0]
      exact hγε
    have hfsmall : f γ < 1 / 2 := hε hball hγ0
    have hratio := ghostThetaSeries_ratio_le_comparison d p hp0 hp1 htop htheta0
      hδpos hγ0 hγδ (hγγ₀.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
    change (γ : ℝ) / f γ ≤ (γ : ℝ) + C * f γ at hratio
    have hmul : (γ : ℝ) ≤ ((γ : ℝ) + C * f γ) * f γ :=
      (div_le_iff₀ hfpos).mp hratio
    have hybound : (γ : ℝ) ≤ 2 * C * f γ ^ 2 := by
      nlinarith [mul_pos hC hfpos]
    have hK : 0 < 2 * C := mul_pos (by norm_num) hC
    have hydiv : (γ : ℝ) / (2 * C) ≤ f γ ^ 2 :=
      (div_le_iff₀ hK).mpr (by
        simpa [mul_assoc, mul_left_comm, mul_comm] using hybound)
    have hsq : (α * Real.sqrt (γ : ℝ)) ^ 2 ≤ f γ ^ 2 := by
      calc
        (α * Real.sqrt (γ : ℝ)) ^ 2 = (γ : ℝ) / (2 * C) := by
          dsimp [α]
          rw [mul_pow, inv_pow, Real.sq_sqrt hγ0.le, Real.sq_sqrt hK.le]
          simp [div_eq_mul_inv, mul_comm]
        _ ≤ f γ ^ 2 := hydiv
    have hαsqrt : α * Real.sqrt (γ : ℝ) ≤ f γ :=
      (sq_le_sq₀ (mul_nonneg hα.le (Real.sqrt_nonneg _)) hfpos.le).mp hsq
    rw [ghostTheta_eq_ghostThetaSeries d p γ hγ0]
    exact hαsqrt
  · have hT := ghostTheta_tendsto_theta d p
    have hlarge : ∀ᶠ y : ℝ in nhdsWithin 0 (Ioi 0),
        theta d p / 2 < ghostThetaSeries d p y :=
      hT (Ioi_mem_nhds (by linarith))
    have hlarge' : ∀ᶠ y : ℝ in nhds 0, y ∈ Ioi (0 : ℝ) →
        theta d p / 2 < ghostThetaSeries d p y :=
      eventually_nhdsWithin_iff.mp hlarge
    obtain ⟨ε, hε0, hε⟩ := Metric.mem_nhds_iff.mp hlarge'
    let γ₀ := min ε 1
    have hγ₀0 : 0 < γ₀ := lt_min hε0 zero_lt_one
    refine ⟨theta d p / 2, by positivity, γ₀, hγ₀0, min_le_right _ _, ?_⟩
    intro γ hγ0 hγγ₀
    have hγε : (γ : ℝ) < ε := hγγ₀.trans_le (min_le_left _ _)
    have hball : (γ : ℝ) ∈ Metric.ball (0 : ℝ) ε := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hγ0]
      exact hγε
    have hfield : theta d p / 2 < ghostThetaSeries d p γ := hε hball hγ0
    have hsqrt : Real.sqrt (γ : ℝ) ≤ 1 := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt γ.property.2
    rw [ghostTheta_eq_ghostThetaSeries d p γ hγ0]
    nlinarith [mul_le_mul_of_nonneg_left hsqrt (by positivity : 0 ≤ theta d p / 2)]

end

end Percolation
