/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import Percolation.Critical.OpenClusterDensity
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

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

open scoped BigOperators

namespace Percolation

noncomputable section

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

end

end Percolation
