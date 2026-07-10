/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import Percolation.Critical.OpenClusterDensity
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Convex.Deriv

/-!
# Lattice animals and large deviations

Source: Grimmett, *Percolation* (2nd ed., 1999), §4.2, pp. 79–83
(source id `grimmett-percolation-1999`).

This file formalizes the entropy estimate underlying Grimmett's lattice-animal large-deviation
Theorem 4.20. The scalar proof uses a uniform elementary lower bound for binary relative entropy.
It gives the same exponential-in-`n` conclusion needed for differentiability, with exponent
`-n x² p² q² / 18`; Grimmett's sharper displayed exponent is `-n x² p² q / 3`.

## Main results

* `binaryRelativeEntropy_ge_half_sq`: a self-contained Bernoulli entropy lower bound.
* `weightedTerm_le_exp_neg_entropy`: comparison of an animal weight at `p` with its maximizing
  parameter.
* `animalWeight_le_exp_of_deviation`: the pointwise large-deviation estimate used in the finite
  lattice-animal sum.
* `latticeAnimal_largeDeviation`: the coefficient-table form of Theorem 4.20.
-/

open scoped BigOperators Topology

namespace Percolation

noncomputable section

open Set

/-- Binary relative entropy `D(r ‖ p)`. -/
def binaryRelativeEntropy (r p : ℝ) : ℝ :=
  r * Real.log (r / p) + (1 - r) * Real.log ((1 - r) / (1 - p))

/-- A uniform quadratic lower bound for binary relative entropy. The constant `1/2` is weaker
than Pinsker's sharp constant `2`, but is sufficient for the Chapter 4 large-deviation argument
and follows directly from Mathlib's elementary bounds for `log (1+x)`. -/
theorem binaryRelativeEntropy_ge_half_sq {r p : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1) (hp0 : 0 < p) (hp1 : p < 1) :
    (r - p) ^ 2 / 2 ≤ binaryRelativeEntropy r p := by
  by_cases hpr : p ≤ r
  · have ha0 : 0 ≤ r - p := sub_nonneg.mpr hpr
    have hlog1 :
        2 * (r - p) / ((r - p) + 2 * p) ≤ Real.log (r / p) := by
      have hx : 0 ≤ (r - p) / p := div_nonneg ha0 hp0.le
      have h := Real.le_log_one_add_of_nonneg hx
      convert h using 1 <;> field_simp [hp0.ne']
      ring_nf
    have hlog2 :
        -(r - p) / (1 - r) ≤ Real.log ((1 - r) / (1 - p)) := by
      have hpos : 0 < (1 - r) / (1 - p) :=
        div_pos (sub_pos.mpr hr1) (sub_pos.mpr hp1)
      have h := Real.one_sub_inv_le_log_of_pos hpos
      rw [inv_div] at h
      convert h using 1
      all_goals field_simp [sub_ne_zero.mpr hr1.ne', sub_ne_zero.mpr hp1.ne']
      ring_nf
    have hlower :
        r * (2 * (r - p) / ((r - p) + 2 * p)) +
            (1 - r) * (-(r - p) / (1 - r)) ≤ binaryRelativeEntropy r p := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hlog1 hr0.le)
        (mul_le_mul_of_nonneg_left hlog2 (sub_nonneg.mpr hr1.le))
    have hdenpos : 0 < (r - p) + 2 * p := by linarith
    have hdenle : (r - p) + 2 * p ≤ 2 := by linarith
    have hinv : (1 : ℝ) / 2 ≤ 1 / ((r - p) + 2 * p) :=
      one_div_le_one_div_of_le hdenpos hdenle
    have hfrac : (r - p) ^ 2 / 2 ≤ (r - p) ^ 2 / ((r - p) + 2 * p) := by
      simpa [div_eq_mul_inv] using
        mul_le_mul_of_nonneg_left hinv (sq_nonneg (r - p))
    calc
      (r - p) ^ 2 / 2 ≤ (r - p) ^ 2 / ((r - p) + 2 * p) := hfrac
      _ = r * (2 * (r - p) / ((r - p) + 2 * p)) +
            (1 - r) * (-(r - p) / (1 - r)) := by
        field_simp [sub_ne_zero.mpr hr1.ne', hdenpos.ne']
        ring
      _ ≤ binaryRelativeEntropy r p := hlower
  · have hrp : r ≤ p := le_of_not_ge hpr
    have ha0 : 0 ≤ p - r := sub_nonneg.mpr hrp
    have hlog1 : -(p - r) / r ≤ Real.log (r / p) := by
      have hpos : 0 < r / p := div_pos hr0 hp0
      have h := Real.one_sub_inv_le_log_of_pos hpos
      rw [inv_div] at h
      convert h using 1
      all_goals field_simp [hr0.ne', hp0.ne']
      ring_nf
    have hlog2 :
        2 * (p - r) / ((p - r) + 2 * (1 - p)) ≤
          Real.log ((1 - r) / (1 - p)) := by
      have hx : 0 ≤ (p - r) / (1 - p) :=
        div_nonneg ha0 (sub_nonneg.mpr hp1.le)
      have h := Real.le_log_one_add_of_nonneg hx
      convert h using 1 <;> field_simp [sub_ne_zero.mpr hp1.ne']
      ring_nf
    have hlower :
        r * (-(p - r) / r) +
            (1 - r) * (2 * (p - r) / ((p - r) + 2 * (1 - p))) ≤
          binaryRelativeEntropy r p := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hlog1 hr0.le)
        (mul_le_mul_of_nonneg_left hlog2 (sub_nonneg.mpr hr1.le))
    have hdenpos : 0 < (p - r) + 2 * (1 - p) := by linarith
    have hdenle : (p - r) + 2 * (1 - p) ≤ 2 := by linarith
    have hinv : (1 : ℝ) / 2 ≤ 1 / ((p - r) + 2 * (1 - p)) :=
      one_div_le_one_div_of_le hdenpos hdenle
    have hfrac :
        (p - r) ^ 2 / 2 ≤ (p - r) ^ 2 / ((p - r) + 2 * (1 - p)) := by
      simpa [div_eq_mul_inv] using
        mul_le_mul_of_nonneg_left hinv (sq_nonneg (p - r))
    calc
      (r - p) ^ 2 / 2 = (p - r) ^ 2 / 2 := by ring
      _ ≤ (p - r) ^ 2 / ((p - r) + 2 * (1 - p)) := hfrac
      _ = r * (-(p - r) / r) +
            (1 - r) * (2 * (p - r) / ((p - r) + 2 * (1 - p))) := by
        field_simp [hr0.ne', hdenpos.ne']
        ring
      _ ≤ binaryRelativeEntropy r p := hlower

/-- Exponentiating binary relative entropy recovers the likelihood ratio between the parameters
`r` and `p`. -/
theorem exp_neg_mul_binaryRelativeEntropy {s r p : ℝ} (m b : ℕ)
    (hr0 : 0 < r) (hr1 : r < 1) (hp0 : 0 < p) (hp1 : p < 1)
    (hsr : s * r = m) (hsr' : s * (1 - r) = b) :
    Real.exp (-s * binaryRelativeEntropy r p) =
      (p / r) ^ m * ((1 - p) / (1 - r)) ^ b := by
  have hlog1 : -Real.log (r / p) = Real.log (p / r) := by
    rw [Real.log_div hr0.ne' hp0.ne', Real.log_div hp0.ne' hr0.ne']
    ring
  have hlog2 :
      -Real.log ((1 - r) / (1 - p)) = Real.log ((1 - p) / (1 - r)) := by
    rw [Real.log_div (sub_pos.mpr hr1).ne' (sub_pos.mpr hp1).ne',
      Real.log_div (sub_pos.mpr hp1).ne' (sub_pos.mpr hr1).ne']
    ring
  calc
    Real.exp (-s * binaryRelativeEntropy r p) =
        Real.exp ((m : ℝ) * Real.log (p / r) +
          (b : ℝ) * Real.log ((1 - p) / (1 - r))) := by
      congr 1
      unfold binaryRelativeEntropy
      rw [← hlog1, ← hlog2, ← hsr, ← hsr']
      ring
    _ = Real.exp ((m : ℝ) * Real.log (p / r)) *
        Real.exp ((b : ℝ) * Real.log ((1 - p) / (1 - r))) := by
      rw [Real.exp_add]
    _ = (p / r) ^ m * ((1 - p) / (1 - r)) ^ b := by
      rw [Real.exp_nat_mul, Real.exp_nat_mul, Real.exp_log (div_pos hp0 hr0),
        Real.exp_log (div_pos (sub_pos.mpr hp1) (sub_pos.mpr hr1))]

/-- A coefficient whose weight at its maximizing parameter is at most one has exponentially
small weight at a different parameter, with exponent given by binary relative entropy. -/
theorem weightedTerm_le_exp_neg_entropy {a s r p : ℝ} (m b : ℕ)
    (hr0 : 0 < r) (hr1 : r < 1) (hp0 : 0 < p) (hp1 : p < 1)
    (hsr : s * r = m) (hsr' : s * (1 - r) = b)
    (href : a * r ^ m * (1 - r) ^ b ≤ 1) :
    a * p ^ m * (1 - p) ^ b ≤ Real.exp (-s * binaryRelativeEntropy r p) := by
  have hratio0 : 0 ≤ (p / r) ^ m * ((1 - p) / (1 - r)) ^ b := by positivity
  have hfactor :
      a * p ^ m * (1 - p) ^ b =
        (a * r ^ m * (1 - r) ^ b) *
          ((p / r) ^ m * ((1 - p) / (1 - r)) ^ b) := by
    rw [div_pow, div_pow]
    field_simp [hr0.ne', sub_ne_zero.mpr hr1.ne']
  rw [hfactor, exp_neg_mul_binaryRelativeEntropy m b hr0 hr1 hp0 hp1 hsr hsr']
  simpa using mul_le_mul_of_nonneg_right href hratio0

/-- The fraction `m / (m + b)` at which the binomial-style weight with `m` occupied and `b`
boundary bonds is maximized. This is the parameter `r` in Grimmett's equation (4.24). -/
def animalOpenFraction (m b : ℕ) : ℝ :=
  (m : ℝ) / (m + b : ℕ)

/-- Minus the logarithm, per occupied bond, of the likelihood ratio appearing in
Grimmett's equation (4.28).  Here `z=b/m`; its unique minimum is at
`z=(1-p)/p`. -/
def animalLogPenalty (p z : ℝ) : ℝ :=
  -Real.log (p * (1 + z)) - z * Real.log ((1 - p) * (1 + z) / z)

theorem animalLogPenalty_hasDerivAt {p z : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (hz : 0 < z) :
    HasDerivAt (animalLogPenalty p) (-Real.log ((1 - p) * (1 + z) / z)) z := by
  have hz1 : 1 + z ≠ 0 := by positivity
  have hfirst : HasDerivAt (fun y : ℝ ↦ p * (1 + y)) p z := by
    convert (hasDerivAt_const z p).mul ((hasDerivAt_const z 1).add (hasDerivAt_id z)) using 1 <;>
      simp
  have hratio : HasDerivAt (fun y : ℝ ↦ (1 - p) * (1 + y) / y)
      (-(1 - p) / z ^ 2) z := by
    convert (((hasDerivAt_const z (1 - p)).mul
      ((hasDerivAt_const z 1).add (hasDerivAt_id z))).div (hasDerivAt_id z) hz.ne') using 1
    all_goals simp only [Function.id_def, Pi.mul_apply, Pi.add_apply]
    all_goals field_simp [hz.ne'] <;> ring
  have hlogFirst : HasDerivAt (fun y : ℝ ↦ -Real.log (p * (1 + y)))
      (-1 / (1 + z)) z := by
    convert (hfirst.log (mul_ne_zero hp0.ne' hz1)).neg using 1
    field_simp [hp0.ne', hz1]
  have hlogRatio : HasDerivAt (fun y : ℝ ↦ Real.log ((1 - p) * (1 + y) / y))
      (-1 / (z * (1 + z))) z := by
    convert hratio.log (by positivity) using 1
    field_simp [sub_ne_zero.mpr hp1.ne', hz.ne', hz1]
  have hsecond := (hasDerivAt_id z).mul hlogRatio
  convert hlogFirst.sub hsecond using 1
  all_goals simp only [animalLogPenalty, Function.id_def, Pi.mul_apply]
  all_goals field_simp [hz.ne', hz1] <;> ring

theorem animalLogPenalty_deriv {p z : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hz : 0 < z) :
    deriv (animalLogPenalty p) z = -Real.log ((1 - p) * (1 + z) / z) := by
  exact (animalLogPenalty_hasDerivAt hp0 hp1 hz).deriv

theorem animalLogPenaltySlope_hasDerivAt {p z : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (hz : 0 < z) :
    HasDerivAt (fun y : ℝ ↦ -Real.log ((1 - p) * (1 + y) / y))
      (1 / (z * (1 + z))) z := by
  have hz1 : 1 + z ≠ 0 := by positivity
  have hratio : HasDerivAt (fun y : ℝ ↦ (1 - p) * (1 + y) / y)
      (-(1 - p) / z ^ 2) z := by
    convert (((hasDerivAt_const z (1 - p)).mul
      ((hasDerivAt_const z 1).add (hasDerivAt_id z))).div (hasDerivAt_id z) hz.ne') using 1
    all_goals simp only [Function.id_def, Pi.mul_apply, Pi.add_apply]
    all_goals field_simp [hz.ne'] <;> ring
  have hlog := (hratio.log (by positivity)).neg
  convert hlog using 1
  field_simp [hz.ne', hz1, sub_ne_zero.mpr hp1.ne']

theorem animalLogPenalty_deriv_hasDerivAt {p z : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (hz : 0 < z) :
    HasDerivAt (deriv (animalLogPenalty p)) (1 / (z * (1 + z))) z := by
  have hlog' := animalLogPenaltySlope_hasDerivAt hp0 hp1 hz
  have heq : deriv (animalLogPenalty p) =ᶠ[𝓝 z]
      (fun y : ℝ ↦ -Real.log ((1 - p) * (1 + y) / y)) := by
    filter_upwards [eventually_gt_nhds hz] with y hy
    exact animalLogPenalty_deriv hp0 hp1 hy
  exact hlog'.congr_of_eventuallyEq heq

theorem animalLogPenalty_at_mode {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    animalLogPenalty p ((1 - p) / p) = 0 := by
  have hq : 0 < 1 - p := sub_pos.mpr hp1
  have hfirst : p * (1 + (1 - p) / p) = 1 := by field_simp [hp0.ne'] <;> ring
  have hsecond : (1 - p) * (1 + (1 - p) / p) / ((1 - p) / p) = 1 := by
    field_simp [hp0.ne', hq.ne'] <;> ring
  simp [animalLogPenalty, hfirst, hsecond]

theorem animalLogPenalty_deriv_at_mode {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    deriv (animalLogPenalty p) ((1 - p) / p) = 0 := by
  have hz : 0 < (1 - p) / p := div_pos (sub_pos.mpr hp1) hp0
  rw [animalLogPenalty_deriv hp0 hp1 hz]
  have h : (1 - p) * (1 + (1 - p) / p) / ((1 - p) / p) = 1 := by
    field_simp [hp0.ne', sub_ne_zero.mpr hp1.ne'] <;> ring
  simp [h]

/-- Uniform curvature bound on the `x`-neighbourhood of the maximizing boundary-to-edge ratio.
The explicit `1/100` is one source-faithful witness for Grimmett's unspecified constant `s`. -/
theorem animalLogPenalty_curvature_lower {p x z : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (hx : x ≤ 1 / 100)
    (hzlo : (1 - p) / p * (1 - x * p) ≤ z)
    (hzhi : z ≤ (1 - p) / p * (1 + x * p)) :
    8 * p ^ 2 / (9 * (1 - p)) ≤ 1 / (z * (1 + z)) := by
  have hq0 : 0 < 1 - p := sub_pos.mpr hp1
  have hp_le : p ≤ 1 := hp1.le
  have hxp : x * p ≤ 1 / 100 := by nlinarith
  have hfac : 0 < 1 - x * p := by nlinarith
  have hz0 : 0 < z := lt_of_lt_of_le (mul_pos (div_pos hq0 hp0) hfac) hzlo
  have hz_upper : z ≤ 101 * (1 - p) / (100 * p) := by
    calc
      z ≤ (1 - p) / p * (1 + x * p) := hzhi
      _ ≤ (1 - p) / p * (101 / 100) := by
        gcongr
        nlinarith
      _ = 101 * (1 - p) / (100 * p) := by ring
  have hz1_upper : 1 + z ≤ 101 / (100 * p) := by
    calc
      1 + z ≤ 1 + 101 * (1 - p) / (100 * p) := by linarith
      _ ≤ 101 / (100 * p) := by
        apply (le_div_iff₀ (by positivity : 0 < 100 * p)).2
        field_simp [hp0.ne']
        nlinarith
  have hprod : z * (1 + z) ≤ 10201 * (1 - p) / (10000 * p ^ 2) := by
    calc
      z * (1 + z) ≤ (101 * (1 - p) / (100 * p)) * (101 / (100 * p)) := by
        gcongr
      _ = 10201 * (1 - p) / (10000 * p ^ 2) := by ring
  have hprod' : z * (1 + z) ≤ 9 * (1 - p) / (8 * p ^ 2) := by
    calc
      z * (1 + z) ≤ 10201 * (1 - p) / (10000 * p ^ 2) := hprod
      _ ≤ 9 * (1 - p) / (8 * p ^ 2) := by
        apply (div_le_div_iff₀ (by positivity : 0 < 10000 * p ^ 2)
          (by positivity : 0 < 8 * p ^ 2)).2
        nlinarith
  have hinv := one_div_le_one_div_of_le (by positivity : 0 < z * (1 + z)) hprod'
  convert hinv using 1 <;> field_simp [hp0.ne', hq0.ne'] <;> ring

/-- Strong-convexity form of the uniform Taylor estimate in the proof of Theorem 4.20. -/
theorem animalLogPenalty_ge_quadratic {p x z : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (hx0 : 0 ≤ x) (hx : x ≤ 1 / 100)
    (hzlo : (1 - p) / p * (1 - x * p) ≤ z)
    (hzhi : z ≤ (1 - p) / p * (1 + x * p)) :
    4 * p ^ 2 / (9 * (1 - p)) * (z - (1 - p) / p) ^ 2 ≤ animalLogPenalty p z := by
  let z₀ : ℝ := (1 - p) / p
  let K : ℝ := 8 * p ^ 2 / (9 * (1 - p))
  let S : Set ℝ := Icc (z₀ * (1 - x * p)) (z₀ * (1 + x * p))
  let H : ℝ → ℝ := fun y ↦ animalLogPenalty p y - K / 2 * (y - z₀) ^ 2
  let L : ℝ → ℝ := fun y ↦ -Real.log ((1 - p) * (1 + y) / y) - K * (y - z₀)
  have hq0 : 0 < 1 - p := sub_pos.mpr hp1
  have hxp : x * p ≤ 1 / 100 := by nlinarith [hp1.le]
  have hfac : 0 < 1 - x * p := by nlinarith
  have hz₀ : 0 < z₀ := div_pos hq0 hp0
  have hSpos : ∀ y ∈ S, 0 < y := by
    intro y hy
    exact lt_of_lt_of_le (mul_pos hz₀ hfac) hy.1
  have hHderiv : ∀ y ∈ S, HasDerivAt H (L y) y := by
    intro y hy
    have hy0 := hSpos y hy
    have hquad := (((hasDerivAt_id y).sub_const z₀).pow 2).const_mul (K / 2)
    convert (animalLogPenalty_hasDerivAt hp0 hp1 hy0).sub hquad using 1
    all_goals simp only [H, L, Function.id_def]
    all_goals ring
  have hLderiv : ∀ y ∈ S,
      HasDerivAt L (1 / (y * (1 + y)) - K) y := by
    intro y hy
    have hy0 := hSpos y hy
    have hk : HasDerivAt (fun t : ℝ ↦ K * (t - z₀)) K y := by
      convert ((hasDerivAt_id y).sub_const z₀).const_mul K using 1 <;> simp
    simpa only [L] using (animalLogPenaltySlope_hasDerivAt hp0 hp1 hy0).sub hk
  have hconvex : ConvexOn ℝ S H := by
    have hSconvex : Convex ℝ S := by
      dsimp only [S]
      exact convex_Icc _ _
    apply convexOn_of_hasDerivWithinAt2_nonneg hSconvex
    · intro y hy
      exact (hHderiv y hy).continuousAt.continuousWithinAt
    · intro y hy
      exact (hHderiv y (interior_subset hy)).hasDerivWithinAt
    · intro y hy
      exact (hLderiv y (interior_subset hy)).hasDerivWithinAt
    · intro y hy
      have hyS := interior_subset hy
      exact sub_nonneg.mpr (animalLogPenalty_curvature_lower hp0 hp1 hx hyS.1 hyS.2)
  have hz₀S : z₀ ∈ S := by
    constructor <;> dsimp only [S] <;> nlinarith [mul_nonneg hx0 hp0.le]
  have hzS : z ∈ S := ⟨hzlo, hzhi⟩
  have hH₀ : H z₀ = 0 := by
    dsimp only [H]
    rw [animalLogPenalty_at_mode hp0 hp1]
    ring
  have hderivH₀ : HasDerivAt H 0 z₀ := by
    convert hHderiv z₀ hz₀S using 1
    dsimp only [L, z₀]
    have h : (1 - p) * (1 + (1 - p) / p) / ((1 - p) / p) = 1 := by
      field_simp [hp0.ne', sub_ne_zero.mpr hp1.ne'] <;> ring
    simp [h]
  have hmin : H z₀ ≤ H z := by
    rcases lt_trichotomy z₀ z with hlt | heq | hgt
    · have hslope := hconvex.le_slope_of_hasDerivAt hz₀S hzS hlt hderivH₀
      rw [slope_def_field, hH₀] at hslope
      rcases div_nonneg_iff.mp hslope with hslope | hslope
      · rw [hH₀]
        simpa using hslope.1
      · exact (not_lt_of_ge hslope.2 (sub_pos.mpr hlt)).elim
    · simpa [heq]
    · have hslope := hconvex.slope_le_of_hasDerivAt hzS hz₀S hgt hderivH₀
      rw [slope_def_field, hH₀, div_nonpos_iff] at hslope
      rcases hslope with hslope | hslope
      · linarith
      · rw [hH₀]
        linarith [hslope.1]
  rw [hH₀] at hmin
  dsimp only [H, K, z₀] at hmin ⊢
  have hcoef : 4 * p ^ 2 / (9 * (1 - p)) =
      (8 * p ^ 2 / (9 * (1 - p))) / 2 := by ring
  rw [hcoef]
  linarith

theorem animalLogPenalty_convexOn_pos {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    ConvexOn ℝ (Ioi 0) (animalLogPenalty p) := by
  let L : ℝ → ℝ := fun y ↦ -Real.log ((1 - p) * (1 + y) / y)
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Ioi 0)
  · intro y hy
    exact (animalLogPenalty_hasDerivAt hp0 hp1 hy).continuousAt.continuousWithinAt
  · intro y hy
    have hy' : 0 < y := interior_subset hy
    exact (animalLogPenalty_hasDerivAt hp0 hp1 hy').hasDerivWithinAt
  · intro y hy
    have hy' : 0 < y := interior_subset hy
    exact (animalLogPenaltySlope_hasDerivAt hp0 hp1 hy').hasDerivWithinAt
  · intro y hy
    have hy' : 0 < y := interior_subset hy
    exact one_div_nonneg.mpr (mul_nonneg hy'.le (by linarith))

theorem animalLogPenalty_anti_left_of_mode {p z y : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (hz : 0 < z) (hzy : z ≤ y)
    (hy : y ≤ (1 - p) / p) :
    animalLogPenalty p y ≤ animalLogPenalty p z := by
  rcases hzy.eq_or_lt with rfl | hzy
  · rfl
  have hy0 : 0 < y := hz.trans_le hzy.le
  have hratio : 1 ≤ (1 - p) * (1 + y) / y := by
    apply (le_div_iff₀ hy0).2
    apply (le_div_iff₀ hp0).mp at hy
    nlinarith
  have hderiv : -Real.log ((1 - p) * (1 + y) / y) ≤ 0 :=
    neg_nonpos.mpr (Real.log_nonneg hratio)
  have hslope := (animalLogPenalty_convexOn_pos hp0 hp1).slope_le_of_hasDerivAt
    hz hy0 hzy (animalLogPenalty_hasDerivAt hp0 hp1 hy0)
  rw [slope_def_field] at hslope
  have hslope0 : (animalLogPenalty p y - animalLogPenalty p z) / (y - z) ≤ 0 :=
    hslope.trans hderiv
  exact sub_nonpos.mp ((div_nonpos_iff.mp hslope0).resolve_left (fun h ↦
    (not_le_of_gt (sub_pos.mpr hzy)) h.2) |>.1)

theorem animalLogPenalty_mono_right_of_mode {p y z : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (hy : (1 - p) / p ≤ y)
    (hyz : y ≤ z) :
    animalLogPenalty p y ≤ animalLogPenalty p z := by
  have hy0 : 0 < y := (div_pos (sub_pos.mpr hp1) hp0).trans_le hy
  have hz0 : 0 < z := hy0.trans_le hyz
  rcases hyz.eq_or_lt with rfl | hyz
  · rfl
  have hratioPos : 0 < (1 - p) * (1 + y) / y := by positivity
  have hratio : (1 - p) * (1 + y) / y ≤ 1 := by
    apply (div_le_one hy0).2
    apply (div_le_iff₀ hp0).mp at hy
    nlinarith
  have hderiv : 0 ≤ -Real.log ((1 - p) * (1 + y) / y) :=
    neg_nonneg.mpr (Real.log_nonpos hratioPos.le hratio)
  have hslope := (animalLogPenalty_convexOn_pos hp0 hp1).le_slope_of_hasDerivAt
    hy0 hz0 hyz (animalLogPenalty_hasDerivAt hp0 hp1 hy0)
  rw [slope_def_field] at hslope
  have hslope0 : 0 ≤ (animalLogPenalty p z - animalLogPenalty p y) / (z - y) :=
    hderiv.trans hslope
  exact sub_nonneg.mp ((div_nonneg_iff.mp hslope0).resolve_right (fun h ↦
    (not_le_of_gt (sub_pos.mpr hyz)) h.2) |>.1)

theorem exp_neg_mul_animalLogPenalty {p : ℝ} (m b : ℕ)
    (hp0 : 0 < p) (hp1 : p < 1) (hm : 0 < m) (hb : 0 < b) :
    Real.exp (-(m : ℝ) * animalLogPenalty p ((b : ℝ) / m)) =
      (p / animalOpenFraction m b) ^ m *
        ((1 - p) / (1 - animalOpenFraction m b)) ^ b := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hsR : (0 : ℝ) < m + b := by positivity
  have hz : 0 < (b : ℝ) / m := div_pos hbR hmR
  have hr0 : 0 < animalOpenFraction m b := by
    exact div_pos hmR (by simpa using hsR)
  have hr1 : animalOpenFraction m b < 1 := by
    rw [animalOpenFraction, div_lt_one (by simpa using hsR)]
    exact_mod_cast (show m < m + b by omega)
  have hfirst : p * (1 + (b : ℝ) / m) = p / animalOpenFraction m b := by
    simp only [animalOpenFraction, Nat.cast_add]
    field_simp [hmR.ne', hsR.ne']
  have hsecond : (1 - p) * (1 + (b : ℝ) / m) / ((b : ℝ) / m) =
      (1 - p) / (1 - animalOpenFraction m b) := by
    simp only [animalOpenFraction, Nat.cast_add]
    field_simp [hmR.ne', hbR.ne', hsR.ne']
    ring
  rw [animalLogPenalty, hfirst, hsecond]
  have hA : 0 < p / animalOpenFraction m b := div_pos hp0 hr0
  have hB : 0 < (1 - p) / (1 - animalOpenFraction m b) :=
    div_pos (sub_pos.mpr hp1) (sub_pos.mpr hr1)
  have hexponent : -(m : ℝ) *
      (-Real.log (p / animalOpenFraction m b) -
        ((b : ℝ) / m) * Real.log ((1 - p) / (1 - animalOpenFraction m b))) =
      (m : ℝ) * Real.log (p / animalOpenFraction m b) +
        (b : ℝ) * Real.log ((1 - p) / (1 - animalOpenFraction m b)) := by
    field_simp [hmR.ne']
    ring
  rw [hexponent,
    Real.exp_add, Real.exp_nat_mul, Real.exp_nat_mul, Real.exp_log hA, Real.exp_log hB]

/-- Sharp pointwise estimate from Grimmett's equations (4.26)–(4.30).  The restriction
`x ≤ 1/100` is the explicit witness chosen above for the book's unspecified small constant. -/
theorem animalWeight_le_exp_of_deviation_sharp {d n m b : ℕ} {p x a : ℝ}
    (hd : 0 < d) (hn : 4 ≤ n)
    (hmlo : n - 1 ≤ m) (hmhi : m ≤ d * n)
    (hblo : 1 ≤ b) (hbhi : b ≤ 2 * d * n)
    (hp0 : 0 < p) (hp1 : p < 1) (hx0 : 0 < x) (hx : x ≤ 1 / 100)
    (hdev : (d : ℝ) * x * n < |(m : ℝ) / p - (b : ℝ) / (1 - p)|)
    (href : a * animalOpenFraction m b ^ m * (1 - animalOpenFraction m b) ^ b ≤ 1) :
    a * p ^ m * (1 - p) ^ b ≤
      Real.exp (-((n : ℝ) * x ^ 2 * p ^ 2 * (1 - p) / 3)) := by
  have hm : 0 < m := lt_of_lt_of_le (by omega : 0 < n - 1) hmlo
  have hb : 0 < b := hblo
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  let z : ℝ := (b : ℝ) / m
  let z₀ : ℝ := (1 - p) / p
  let zminus : ℝ := z₀ * (1 - x * p)
  let zplus : ℝ := z₀ * (1 + x * p)
  have hz : 0 < z := div_pos hbR hmR
  have hz₀ : 0 < z₀ := div_pos (sub_pos.mpr hp1) hp0
  have hxp : x * p ≤ 1 / 100 := by nlinarith [hp1.le]
  have hzminus : 0 < zminus := by
    change 0 < z₀ * (1 - x * p)
    exact mul_pos hz₀ (by nlinarith)
  have hmhiR : (m : ℝ) ≤ (d : ℝ) * n := by exact_mod_cast hmhi
  have hscore : |(m : ℝ) / p - (b : ℝ) / (1 - p)| =
      (m : ℝ) * |z₀ - z| / (1 - p) := by
    have hraw : (m : ℝ) / p - (b : ℝ) / (1 - p) =
        (m : ℝ) * (z₀ - z) / (1 - p) := by
      dsimp only [z, z₀]
      field_simp [hp0.ne', sub_ne_zero.mpr hp1.ne', hmR.ne']
    rw [hraw, abs_div, abs_mul, abs_of_pos hmR, abs_of_pos (sub_pos.mpr hp1)]
  have hfar : x * (1 - p) < |z₀ - z| := by
    have hdn : (0 : ℝ) < (d : ℝ) * n := by positivity
    have hmain : (m : ℝ) * (x * (1 - p)) < (m : ℝ) * |z₀ - z| := by
      calc
        (m : ℝ) * (x * (1 - p)) ≤
            ((d : ℝ) * n) * (x * (1 - p)) := by gcongr
        _ = ((d : ℝ) * x * n) * (1 - p) := by ring
        _ < |(m : ℝ) / p - (b : ℝ) / (1 - p)| * (1 - p) := by
          gcongr
        _ = (m : ℝ) * |z₀ - z| := by
          rw [hscore]
          field_simp [sub_ne_zero.mpr hp1.ne']
    nlinarith [hmain]
  have hpenalty : 4 * x ^ 2 * p ^ 2 * (1 - p) / 9 ≤ animalLogPenalty p z := by
    rcases lt_or_ge z z₀ with hleft | hright
    · have hzm : z ≤ zminus := by
        have hzminus_eq : zminus = z₀ - x * (1 - p) := by
          dsimp only [zminus, z₀]
          field_simp [hp0.ne']
        rw [abs_of_pos (sub_pos.mpr hleft)] at hfar
        rw [hzminus_eq]
        nlinarith
      have hboundary := animalLogPenalty_ge_quadratic hp0 hp1 hx0.le hx
        (z := zminus) le_rfl (by
          dsimp only [zminus, zplus]
          gcongr
          nlinarith)
      have hquad : 4 * x ^ 2 * p ^ 2 * (1 - p) / 9 ≤
          4 * p ^ 2 / (9 * (1 - p)) * (zminus - z₀) ^ 2 := by
        dsimp only [zminus, z₀]
        field_simp [sub_ne_zero.mpr hp1.ne']
        ring_nf
        exact le_rfl
      exact hquad.trans (hboundary.trans
        (animalLogPenalty_anti_left_of_mode hp0 hp1 hz hzm (by
          dsimp only [zminus]
          exact mul_le_of_le_one_right hz₀.le (by nlinarith [mul_pos hx0 hp0]))))
    · have hzp : zplus ≤ z := by
        have hzplus_eq : zplus = z₀ + x * (1 - p) := by
          dsimp only [zplus, z₀]
          field_simp [hp0.ne']
        rw [abs_of_nonpos (sub_nonpos.mpr hright)] at hfar
        rw [hzplus_eq]
        nlinarith
      have hboundary := animalLogPenalty_ge_quadratic hp0 hp1 hx0.le hx
        (z := zplus) (by
          dsimp only [zminus, zplus]
          gcongr
          nlinarith) le_rfl
      have hquad : 4 * x ^ 2 * p ^ 2 * (1 - p) / 9 ≤
          4 * p ^ 2 / (9 * (1 - p)) * (zplus - z₀) ^ 2 := by
        dsimp only [zplus, z₀]
        field_simp [sub_ne_zero.mpr hp1.ne']
        ring_nf
        exact le_rfl
      exact hquad.trans (hboundary.trans
        (animalLogPenalty_mono_right_of_mode hp0 hp1
          (by
            dsimp only [zplus]
            exact le_mul_of_one_le_right hz₀.le (by nlinarith [mul_pos hx0 hp0])) hzp))
  have hweight : a * p ^ m * (1 - p) ^ b ≤
      Real.exp (-(m : ℝ) * animalLogPenalty p z) := by
    have hsR : (0 : ℝ) < (m + b : ℕ) := by exact_mod_cast (show 0 < m + b by omega)
    have hrop : 0 < animalOpenFraction m b := by
      exact div_pos hmR hsR
    have hrlt : animalOpenFraction m b < 1 := by
      rw [animalOpenFraction, div_lt_one hsR]
      exact_mod_cast (show m < m + b by omega)
    have hrq : 0 < 1 - animalOpenFraction m b := sub_pos.mpr hrlt
    have hratio0 : 0 ≤ (p / animalOpenFraction m b) ^ m *
        ((1 - p) / (1 - animalOpenFraction m b)) ^ b :=
      mul_nonneg (pow_nonneg (div_nonneg hp0.le hrop.le) _)
        (pow_nonneg (div_nonneg (sub_nonneg.mpr hp1.le) hrq.le) _)
    have hfactor : a * p ^ m * (1 - p) ^ b =
        (a * animalOpenFraction m b ^ m * (1 - animalOpenFraction m b) ^ b) *
          ((p / animalOpenFraction m b) ^ m *
            ((1 - p) / (1 - animalOpenFraction m b)) ^ b) := by
      have hr0 : animalOpenFraction m b ≠ 0 := by
        exact hrop.ne'
      have hr1 : 1 - animalOpenFraction m b ≠ 0 := by
        exact hrq.ne'
      rw [div_pow, div_pow]
      field_simp [hr0, hr1]
    rw [hfactor, exp_neg_mul_animalLogPenalty m b hp0 hp1 hm hb]
    simpa using mul_le_mul_of_nonneg_right href hratio0
  have hmge : (3 : ℝ) * n ≤ 4 * m := by exact_mod_cast (show 3 * n ≤ 4 * m by omega)
  have hexp : (n : ℝ) * x ^ 2 * p ^ 2 * (1 - p) / 3 ≤
      (m : ℝ) * animalLogPenalty p z := by
    calc
      (n : ℝ) * x ^ 2 * p ^ 2 * (1 - p) / 3 ≤
          (m : ℝ) * (4 * x ^ 2 * p ^ 2 * (1 - p) / 9) := by
        have hnonneg : 0 ≤ x ^ 2 * p ^ 2 * (1 - p) := by positivity
        nlinarith
      _ ≤ (m : ℝ) * animalLogPenalty p z :=
        mul_le_mul_of_nonneg_left hpenalty hmR.le
  exact hweight.trans (Real.exp_le_exp.mpr (by linarith))

/-- Pointwise analytic core of Grimmett's lattice-animal large-deviation Theorem 4.20.

The hypotheses `n - 1 ≤ m ≤ d n` and `1 ≤ b ≤ 2 d n` are the geometric ranges (4.14)–(4.15).
The hypothesis `href` is the coefficient estimate (4.25), evaluated at the maximizing parameter
`m / (m + b)`. Summing this estimate over the exceptional pairs gives the finite-sum theorem
below. The elementary entropy bound used here yields exponent `-n x² p² (1-p)² / 18`. -/
theorem animalWeight_le_exp_of_deviation {d n m b : ℕ} {p x a : ℝ}
    (hd : 0 < d) (hn : 2 ≤ n)
    (hmlo : n - 1 ≤ m) (hmhi : m ≤ d * n)
    (hblo : 1 ≤ b) (hbhi : b ≤ 2 * d * n)
    (hp0 : 0 < p) (hp1 : p < 1) (hx : 0 < x)
    (hdev : (d : ℝ) * x * n < |(m : ℝ) / p - (b : ℝ) / (1 - p)|)
    (href : a * animalOpenFraction m b ^ m * (1 - animalOpenFraction m b) ^ b ≤ 1) :
    a * p ^ m * (1 - p) ^ b ≤
      Real.exp (-((n : ℝ) * x ^ 2 * p ^ 2 * (1 - p) ^ 2 / 18)) := by
  let s : ℝ := (m + b : ℕ)
  let r : ℝ := animalOpenFraction m b
  have hbc : (0 : ℝ) < b := by exact_mod_cast hblo
  have hs : s = (m : ℝ) + b := by simp [s]
  have hspos : 0 < s := by rw [hs]; positivity
  have hr0 : 0 < r := by
    dsimp only [r, animalOpenFraction]
    exact div_pos (by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < n - 1) hmlo)) hspos
  have hr1 : r < 1 := by
    dsimp only [r, animalOpenFraction]
    rw [div_lt_one hspos]
    simpa [hs] using hbc
  have hsr : s * r = m := by
    have hsumne : (m : ℝ) + b ≠ 0 := by rw [← hs]; positivity
    dsimp only [r, animalOpenFraction]
    rw [Nat.cast_add, hs]
    field_simp [hsumne]
  have hsr' : s * (1 - r) = b := by
    dsimp only [r, animalOpenFraction]
    field_simp [hspos.ne']
    simp [s]
  have hscore : (m : ℝ) / p - (b : ℝ) / (1 - p) =
      s * (r - p) / (p * (1 - p)) := by
    rw [← hsr, ← hsr']
    field_simp [hp0.ne', sub_ne_zero.mpr hp1.ne']
    ring
  have hpq : 0 < p * (1 - p) := mul_pos hp0 (sub_pos.mpr hp1)
  have hscoreAbs : |(m : ℝ) / p - (b : ℝ) / (1 - p)| =
      s * |r - p| / (p * (1 - p)) := by
    rw [hscore, abs_div, abs_mul, abs_of_pos hspos, abs_of_pos hpq]
  have hdev' : (d : ℝ) * x * n * (p * (1 - p)) < s * |r - p| := by
    apply (lt_div_iff₀ hpq).mp
    rw [← hscoreAbs]
    exact hdev
  have hmhiR : (m : ℝ) ≤ (d : ℝ) * n := by exact_mod_cast hmhi
  have hbhiR : (b : ℝ) ≤ 2 * (d : ℝ) * n := by exact_mod_cast hbhi
  have hsupper : s ≤ 3 * (d : ℝ) * n := by rw [hs]; linarith
  have hright : s * |r - p| ≤ (3 * (d : ℝ) * n) * |r - p| :=
    mul_le_mul_of_nonneg_right hsupper (abs_nonneg _)
  have hdnpos : 0 < (d : ℝ) * n := by positivity
  have hmul : (d : ℝ) * n * (x * (p * (1 - p))) <
      (d : ℝ) * n * (3 * |r - p|) := by
    calc
      (d : ℝ) * n * (x * (p * (1 - p))) =
          (d : ℝ) * x * n * (p * (1 - p)) := by ring
      _ < s * |r - p| := hdev'
      _ ≤ (3 * (d : ℝ) * n) * |r - p| := hright
      _ = (d : ℝ) * n * (3 * |r - p|) := by ring
  have hsep : x * (p * (1 - p)) < 3 * |r - p| :=
    lt_of_mul_lt_mul_left hmul hdnpos.le
  have hxprod : 0 ≤ x * (p * (1 - p)) := by positivity
  have hsq : (x * (p * (1 - p))) ^ 2 < (3 * |r - p|) ^ 2 := by
    simpa [pow_two] using mul_self_lt_mul_self hxprod hsep
  have hbase : x ^ 2 * p ^ 2 * (1 - p) ^ 2 / 18 ≤ (r - p) ^ 2 / 2 := by
    nlinarith [sq_abs (r - p)]
  have hsge : (n : ℝ) ≤ s := by
    rw [hs]
    exact_mod_cast (show n ≤ m + b by omega)
  have hnbase := mul_le_mul_of_nonneg_left hbase (show (0 : ℝ) ≤ n by positivity)
  have hsbase :=
    mul_le_mul_of_nonneg_right hsge (show 0 ≤ (r - p) ^ 2 / 2 by positivity)
  have hentropy : (n : ℝ) * (x ^ 2 * p ^ 2 * (1 - p) ^ 2 / 18) ≤
      s * binaryRelativeEntropy r p := by
    calc
      (n : ℝ) * (x ^ 2 * p ^ 2 * (1 - p) ^ 2 / 18) ≤
          (n : ℝ) * ((r - p) ^ 2 / 2) := hnbase
      _ ≤ s * ((r - p) ^ 2 / 2) := hsbase
      _ ≤ s * binaryRelativeEntropy r p :=
        mul_le_mul_of_nonneg_left
          (binaryRelativeEntropy_ge_half_sq hr0 hr1 hp0 hp1) hspos.le
  calc
    a * p ^ m * (1 - p) ^ b ≤ Real.exp (-s * binaryRelativeEntropy r p) :=
      weightedTerm_le_exp_neg_entropy m b hr0 hr1 hp0 hp1 hsr hsr' href
    _ ≤ Real.exp (-((n : ℝ) * x ^ 2 * p ^ 2 * (1 - p) ^ 2 / 18)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [hentropy]

/-- The finite range of the occupied-bond and boundary-bond counts in (4.14)–(4.15). -/
def animalParameterPairs (d n : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Icc (n - 1) (d * n)).product (Finset.Icc 1 (2 * d * n))

/-- Parameter pairs in the exceptional set of Grimmett's Theorem 4.20. -/
def exceptionalAnimalPairs (d n : ℕ) (p x : ℝ) : Finset (ℕ × ℕ) :=
  (animalParameterPairs d n).filter fun z =>
    (d : ℝ) * x * n < |(z.1 : ℝ) / p - (z.2 : ℝ) / (1 - p)|

/-- The number of admissible `(m,b)` pairs is at most `2 d² n²`, slightly better than the
`3 d² n²` prefactor retained in the statement of the large-deviation estimate. -/
theorem animalParameterPairs_card_le {d n : ℕ} (hn : 2 ≤ n) :
    (animalParameterPairs d n).card ≤ 2 * d ^ 2 * n ^ 2 := by
  have hfirst : (Finset.Icc (n - 1) (d * n)).card ≤ d * n := by
    rw [Nat.card_Icc]
    omega
  have hsecond : (Finset.Icc 1 (2 * d * n)).card ≤ 2 * d * n := by
    rw [Nat.card_Icc]
    omega
  calc
    (animalParameterPairs d n).card =
        (Finset.Icc (n - 1) (d * n)).card *
          (Finset.Icc 1 (2 * d * n)).card := by
      simp [animalParameterPairs]
    _ ≤ (d * n) * (2 * d * n) := Nat.mul_le_mul hfirst hsecond
    _ = 2 * d ^ 2 * n ^ 2 := by ring

/-- **Grimmett, Theorem 4.20 (coefficient-table form).**

For an abstract table `a n m b` of lattice-animal counts, assume the coefficient estimate (4.25):
at the maximizing parameter `m/(m+b)`, every weighted coefficient is at most one. Then the total
weight of pairs for which `|m/p - b/(1-p)| > d x n` is exponentially small in `n`.

This theorem isolates exactly the analytic and finite-counting content of the book proof. The
construction of `a` from geometric cubic-lattice animals, and hence the proof of (4.25) for that
specific table, is deliberately an explicit hypothesis. The exponent is the weaker but uniform
`-n x² p² (1-p)² / 18` supplied by `binaryRelativeEntropy_ge_half_sq`; the polynomial prefactor
is the book's `3 d² n²`. -/
theorem latticeAnimal_largeDeviation {d n : ℕ} {p x : ℝ} (a : ℕ → ℕ → ℕ)
    (hd : 0 < d) (hn : 2 ≤ n)
    (hp0 : 0 < p) (hp1 : p < 1) (hx : 0 < x)
    (href : ∀ m b, (m, b) ∈ animalParameterPairs d n →
      (a m b : ℝ) * animalOpenFraction m b ^ m *
          (1 - animalOpenFraction m b) ^ b ≤ 1) :
    ∑ z ∈ exceptionalAnimalPairs d n p x,
        (a z.1 z.2 : ℝ) * p ^ z.1 * (1 - p) ^ z.2 ≤
      (3 * d ^ 2 * n ^ 2 : ℕ) *
        Real.exp (-((n : ℝ) * x ^ 2 * p ^ 2 * (1 - p) ^ 2 / 18)) := by
  let E := Real.exp (-((n : ℝ) * x ^ 2 * p ^ 2 * (1 - p) ^ 2 / 18))
  have hpoint : ∀ z ∈ exceptionalAnimalPairs d n p x,
      (a z.1 z.2 : ℝ) * p ^ z.1 * (1 - p) ^ z.2 ≤ E := by
    intro z hz
    have hpair : z ∈ animalParameterPairs d n := (Finset.mem_filter.mp hz).1
    have hdev := (Finset.mem_filter.mp hz).2
    have hm := (Finset.mem_product.mp hpair).1
    have hb := (Finset.mem_product.mp hpair).2
    exact animalWeight_le_exp_of_deviation hd hn
      (Finset.mem_Icc.mp hm).1 (Finset.mem_Icc.mp hm).2
      (Finset.mem_Icc.mp hb).1 (Finset.mem_Icc.mp hb).2
      hp0 hp1 hx hdev (href z.1 z.2 hpair)
  have hcard : (exceptionalAnimalPairs d n p x).card ≤ 3 * d ^ 2 * n ^ 2 := by
    calc
      (exceptionalAnimalPairs d n p x).card ≤ (animalParameterPairs d n).card := by
        simpa [exceptionalAnimalPairs] using
          Finset.card_filter_le (animalParameterPairs d n)
            (fun z => (d : ℝ) * x * n <
              |(z.1 : ℝ) / p - (z.2 : ℝ) / (1 - p)|)
      _ ≤ 2 * d ^ 2 * n ^ 2 := animalParameterPairs_card_le hn
      _ ≤ 3 * d ^ 2 * n ^ 2 := by
        nlinarith [Nat.zero_le (d ^ 2 * n ^ 2)]
  calc
    ∑ z ∈ exceptionalAnimalPairs d n p x,
        (a z.1 z.2 : ℝ) * p ^ z.1 * (1 - p) ^ z.2 ≤
        ∑ _z ∈ exceptionalAnimalPairs d n p x, E := by
      exact Finset.sum_le_sum fun z hz => hpoint z hz
    _ = ((exceptionalAnimalPairs d n p x).card : ℝ) * E := by simp
    _ ≤ (3 * d ^ 2 * n ^ 2 : ℕ) * E := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      exact_mod_cast hcard

/-- **Grimmett, Theorem 4.20, with the source exponent.**

For the explicit source-faithful witness `0 < x ≤ 1/100`, the exceptional animal weight has
the displayed bound `3 d² n² exp (-n x² p² (1-p) / 3)`.  Unlike the earlier all-`x` Pinsker
corollary, this is the small-deviation Taylor estimate actually used in §4.3. -/
theorem latticeAnimal_largeDeviation_sharp {d n : ℕ} {p x : ℝ} (a : ℕ → ℕ → ℕ)
    (hd : 0 < d) (hn : 2 ≤ n)
    (hp0 : 0 < p) (hp1 : p < 1) (hx0 : 0 < x) (hx : x ≤ 1 / 100)
    (href : ∀ m b, (m, b) ∈ animalParameterPairs d n →
      (a m b : ℝ) * animalOpenFraction m b ^ m *
          (1 - animalOpenFraction m b) ^ b ≤ 1) :
    ∑ z ∈ exceptionalAnimalPairs d n p x,
        (a z.1 z.2 : ℝ) * p ^ z.1 * (1 - p) ^ z.2 ≤
      (3 * d ^ 2 * n ^ 2 : ℕ) *
        Real.exp (-((n : ℝ) * x ^ 2 * p ^ 2 * (1 - p) / 3)) := by
  by_cases hn4 : 4 ≤ n
  · let E := Real.exp (-((n : ℝ) * x ^ 2 * p ^ 2 * (1 - p) / 3))
    have hpoint : ∀ z ∈ exceptionalAnimalPairs d n p x,
        (a z.1 z.2 : ℝ) * p ^ z.1 * (1 - p) ^ z.2 ≤ E := by
      intro z hz
      have hpair : z ∈ animalParameterPairs d n := (Finset.mem_filter.mp hz).1
      have hdev := (Finset.mem_filter.mp hz).2
      have hm := (Finset.mem_product.mp hpair).1
      have hb := (Finset.mem_product.mp hpair).2
      exact animalWeight_le_exp_of_deviation_sharp hd hn4
        (Finset.mem_Icc.mp hm).1 (Finset.mem_Icc.mp hm).2
        (Finset.mem_Icc.mp hb).1 (Finset.mem_Icc.mp hb).2
        hp0 hp1 hx0 hx hdev (href z.1 z.2 hpair)
    have hcard : (exceptionalAnimalPairs d n p x).card ≤ 3 * d ^ 2 * n ^ 2 := by
      calc
        (exceptionalAnimalPairs d n p x).card ≤ (animalParameterPairs d n).card := by
          simpa [exceptionalAnimalPairs] using
            Finset.card_filter_le (animalParameterPairs d n)
              (fun z => (d : ℝ) * x * n <
                |(z.1 : ℝ) / p - (z.2 : ℝ) / (1 - p)|)
        _ ≤ 2 * d ^ 2 * n ^ 2 := animalParameterPairs_card_le hn
        _ ≤ 3 * d ^ 2 * n ^ 2 := by nlinarith [Nat.zero_le (d ^ 2 * n ^ 2)]
    calc
      ∑ z ∈ exceptionalAnimalPairs d n p x,
          (a z.1 z.2 : ℝ) * p ^ z.1 * (1 - p) ^ z.2 ≤
          ∑ _z ∈ exceptionalAnimalPairs d n p x, E := by
        exact Finset.sum_le_sum fun z hz => hpoint z hz
      _ = ((exceptionalAnimalPairs d n p x).card : ℝ) * E := by simp
      _ ≤ (3 * d ^ 2 * n ^ 2 : ℕ) * E := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        exact_mod_cast hcard
  · have hn3 : n ≤ 3 := by omega
    have hpointOne : ∀ z ∈ exceptionalAnimalPairs d n p x,
        (a z.1 z.2 : ℝ) * p ^ z.1 * (1 - p) ^ z.2 ≤ 1 := by
      intro z hz
      have hpair : z ∈ animalParameterPairs d n := (Finset.mem_filter.mp hz).1
      have hdev := (Finset.mem_filter.mp hz).2
      have hm := (Finset.mem_product.mp hpair).1
      have hb := (Finset.mem_product.mp hpair).2
      refine (animalWeight_le_exp_of_deviation hd hn
        (Finset.mem_Icc.mp hm).1 (Finset.mem_Icc.mp hm).2
        (Finset.mem_Icc.mp hb).1 (Finset.mem_Icc.mp hb).2
        hp0 hp1 hx0 hdev (href z.1 z.2 hpair)).trans ?_
      exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
    have hsumCard :
        ∑ z ∈ exceptionalAnimalPairs d n p x,
            (a z.1 z.2 : ℝ) * p ^ z.1 * (1 - p) ^ z.2 ≤
          (2 * d ^ 2 * n ^ 2 : ℕ) := by
      calc
        ∑ z ∈ exceptionalAnimalPairs d n p x,
            (a z.1 z.2 : ℝ) * p ^ z.1 * (1 - p) ^ z.2 ≤
            ∑ _z ∈ exceptionalAnimalPairs d n p x, (1 : ℝ) := by
          exact Finset.sum_le_sum fun z hz => hpointOne z hz
        _ = (exceptionalAnimalPairs d n p x).card := by simp
        _ ≤ (animalParameterPairs d n).card := by
          exact_mod_cast Finset.card_filter_le (animalParameterPairs d n)
            (fun z => (d : ℝ) * x * n <
              |(z.1 : ℝ) / p - (z.2 : ℝ) / (1 - p)|)
        _ ≤ (2 * d ^ 2 * n ^ 2 : ℕ) := by exact_mod_cast animalParameterPairs_card_le hn
    let A : ℝ := (n : ℝ) * x ^ 2 * p ^ 2 * (1 - p) / 3
    have hxSq : x ^ 2 ≤ 1 / 10000 := by nlinarith [sq_nonneg (x - 1 / 100)]
    have hpSq : p ^ 2 ≤ 1 := by nlinarith [sq_nonneg (p - 1)]
    have hq : 1 - p ≤ 1 := by linarith
    have hA : A ≤ 1 / 10000 := by
      dsimp only [A]
      calc
        (n : ℝ) * x ^ 2 * p ^ 2 * (1 - p) / 3 ≤
            3 * (1 / 10000) * 1 * 1 / 3 := by gcongr <;> exact_mod_cast hn3
        _ = 1 / 10000 := by norm_num
    have hExp : 1 - A ≤ Real.exp (-A) := by
      linarith [Real.add_one_le_exp (-A)]
    have hthree : (2 : ℝ) ≤ 3 * Real.exp (-A) := by nlinarith
    have hB : 0 ≤ (d ^ 2 * n ^ 2 : ℕ) := by positivity
    calc
      ∑ z ∈ exceptionalAnimalPairs d n p x,
          (a z.1 z.2 : ℝ) * p ^ z.1 * (1 - p) ^ z.2 ≤
          (2 * d ^ 2 * n ^ 2 : ℕ) := hsumCard
      _ = 2 * (d ^ 2 * n ^ 2 : ℕ) := by push_cast; ring
      _ ≤ 3 * Real.exp (-A) * (d ^ 2 * n ^ 2 : ℕ) := by
        exact mul_le_mul_of_nonneg_right hthree (by exact_mod_cast hB)
      _ = (3 * d ^ 2 * n ^ 2 : ℕ) *
          Real.exp (-((n : ℝ) * x ^ 2 * p ^ 2 * (1 - p) / 3)) := by
        dsimp only [A]
        push_cast
        ring

end

end Percolation
