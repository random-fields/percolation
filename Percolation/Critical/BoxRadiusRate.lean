import Percolation.Critical.BoxRadiusBlock
import Percolation.Critical.QuasiSubadditive
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The logarithmic box-radius decay rate

This file converts Grimmett's BK/FKG block inequalities into the two logarithmic
quasi-additivity inequalities used in Theorem 6.10.
-/

namespace Percolation

open MeasureTheory
open Filter Set Topology
open scoped unitInterval

/-- A common polynomial error factor dominating both sides of the box block comparison. -/
noncomputable def boxRadiusPolynomialFactor (d n : ℕ) : ℝ :=
  4 * (d : ℝ) ^ 2 * (2 * (n : ℝ) + 1) ^ (d - 1)

/-- Logarithm of the common polynomial error factor. -/
noncomputable def boxRadiusLogCorrection (d n : ℕ) : ℝ :=
  Real.log (boxRadiusPolynomialFactor d n)

theorem boxRadiusPolynomialFactor_pos {d n : ℕ} (hd : 0 < d) :
    0 < boxRadiusPolynomialFactor d n := by
  unfold boxRadiusPolynomialFactor
  positivity

/-- The BK upper block inequality with the same factor used for the FKG lower inequality. -/
theorem boxRadiusTail_add_le_commonPolynomial_mul
    {d : ℕ} (hd : 0 < d) (p : I) (m n : ℕ) :
    boxRadiusTail d p (m + n) ≤
      boxRadiusPolynomialFactor d m * (boxRadiusTail d p m * boxRadiusTail d p n) := by
  calc
    boxRadiusTail d p (m + n) ≤
        (2 * d * (2 * m + 1) ^ (d - 1)) *
          (boxRadiusTail d p m * boxRadiusTail d p n) :=
      boxRadiusTail_add_le_polynomial_mul hd p m n
    _ ≤ boxRadiusPolynomialFactor d m *
          (boxRadiusTail d p m * boxRadiusTail d p n) := by
      apply mul_le_mul_of_nonneg_right
      · unfold boxRadiusPolynomialFactor
        have hA : 0 < (2 * (m : ℝ) + 1) ^ (d - 1) := by positivity
        have hdreal : (1 : ℝ) ≤ d := by exact_mod_cast hd
        have hcoeff : (2 : ℝ) * d ≤ 4 * d ^ 2 := by nlinarith [sq_nonneg (d : ℝ)]
        exact mul_le_mul_of_nonneg_right hcoeff hA.le
      · exact mul_nonneg measureReal_nonneg measureReal_nonneg

/-- The FKG lower block inequality using the common polynomial factor. -/
theorem boxRadiusTail_mul_le_commonPolynomial_mul_add
    {d : ℕ} (hd : 0 < d) (p : I) (m n : ℕ) (i0 : Fin d) :
    boxRadiusTail d p m * boxRadiusTail d p n ≤
      boxRadiusPolynomialFactor d m * boxRadiusTail d p (m + n) := by
  simpa [boxRadiusPolynomialFactor] using
    boxRadiusTail_mul_le_polynomial_mul_add hd p m n i0

/-- The logarithmic upper quasi-additivity inequality (6.29). -/
theorem log_boxRadiusTail_add_le
    {d : ℕ} (hd : 0 < d) {p : I} (hp : 0 < (p : ℝ))
    (m n : ℕ) :
    Real.log (boxRadiusTail d p (m + n)) ≤
      Real.log (boxRadiusTail d p m) + Real.log (boxRadiusTail d p n) +
        boxRadiusLogCorrection d m := by
  have hout := boxRadiusTail_pos_of_pos_density hd (n := m + n) hp
  have hmpos := boxRadiusTail_pos_of_pos_density hd (n := m) hp
  have hnpos := boxRadiusTail_pos_of_pos_density hd (n := n) hp
  have hK := boxRadiusPolynomialFactor_pos (n := m) hd
  have hmul := boxRadiusTail_add_le_commonPolynomial_mul hd p m n
  have hlog := Real.log_le_log hout hmul
  rw [Real.log_mul hK.ne' (mul_pos hmpos hnpos).ne',
    Real.log_mul hmpos.ne' hnpos.ne'] at hlog
  dsimp only [boxRadiusLogCorrection]
  linarith

/-- The logarithmic lower quasi-additivity inequality (6.30). -/
theorem log_boxRadiusTail_add_ge
    {d : ℕ} (hd : 0 < d) {p : I} (hp : 0 < (p : ℝ))
    (m n : ℕ) (i0 : Fin d) :
    Real.log (boxRadiusTail d p m) + Real.log (boxRadiusTail d p n) -
        boxRadiusLogCorrection d m ≤
      Real.log (boxRadiusTail d p (m + n)) := by
  have hout := boxRadiusTail_pos_of_pos_density hd (n := m + n) hp
  have hmpos := boxRadiusTail_pos_of_pos_density hd (n := m) hp
  have hnpos := boxRadiusTail_pos_of_pos_density hd (n := n) hp
  have hK := boxRadiusPolynomialFactor_pos (n := m) hd
  have hmul := boxRadiusTail_mul_le_commonPolynomial_mul_add hd p m n i0
  have hlog := Real.log_le_log (mul_pos hmpos hnpos) hmul
  rw [Real.log_mul hmpos.ne' hnpos.ne', Real.log_mul hK.ne' hout.ne'] at hlog
  dsimp only [boxRadiusLogCorrection]
  linarith

/-- The polynomial correction grows by at most the factor `2^(d-1)` under addition. -/
theorem boxRadiusPolynomialFactor_add_le
    {d : ℕ} (hd : 0 < d) (m n : ℕ) :
    boxRadiusPolynomialFactor d (m + n) ≤
      (2 : ℝ) ^ (d - 1) * boxRadiusPolynomialFactor d (max m n) := by
  have hm : m ≤ max m n := le_max_left _ _
  have hn : n ≤ max m n := le_max_right _ _
  have hbase : 2 * ((m + n : ℕ) : ℝ) + 1 ≤
      2 * (2 * ((max m n : ℕ) : ℝ) + 1) := by
    norm_cast
    omega
  have hpow : (2 * ((m + n : ℕ) : ℝ) + 1) ^ (d - 1) ≤
      (2 * (2 * ((max m n : ℕ) : ℝ) + 1)) ^ (d - 1) := by
    exact pow_le_pow_left₀ (by positivity) hbase _
  unfold boxRadiusPolynomialFactor
  calc
    4 * (d : ℝ) ^ 2 * (2 * ((m + n : ℕ) : ℝ) + 1) ^ (d - 1) ≤
        4 * (d : ℝ) ^ 2 *
          (2 * (2 * ((max m n : ℕ) : ℝ) + 1)) ^ (d - 1) := by gcongr
    _ = (2 : ℝ) ^ (d - 1) *
        (4 * (d : ℝ) ^ 2 *
          (2 * ((max m n : ℕ) : ℝ) + 1) ^ (d - 1)) := by
      rw [mul_pow]
      ring

/-- The logarithmic correction satisfies Grimmett's doubling estimate (6.32). -/
theorem boxRadiusLogCorrection_add_le
    {d : ℕ} (hd : 0 < d) (m n : ℕ) :
    boxRadiusLogCorrection d (m + n) ≤
      boxRadiusLogCorrection d (max m n) + ((d - 1 : ℕ) : ℝ) * Real.log 2 := by
  have hleft := boxRadiusPolynomialFactor_pos (d := d) (n := m + n) hd
  have hright := boxRadiusPolynomialFactor_pos (d := d) (n := max m n) hd
  have hfactor := boxRadiusPolynomialFactor_add_le hd m n
  have hlog := Real.log_le_log hleft hfactor
  rw [Real.log_mul (pow_pos (by norm_num : (0 : ℝ) < 2) _).ne' hright.ne',
    Real.log_pow] at hlog
  simpa [boxRadiusLogCorrection, add_comm] using hlog

/-- The logarithmic polynomial correction is sublinear. -/
theorem boxRadiusLogCorrection_add_const_div_tendsto_zero
    {d : ℕ} (hd : 0 < d) (c : ℝ) :
    Tendsto (fun n : ℕ ↦ (boxRadiusLogCorrection d n + c) / n)
      atTop (𝓝 0) := by
  let C : ℝ := 4 * (d : ℝ) ^ 2
  have hC : 0 < C := by dsimp [C]; positivity
  have hrepr : ∀ n : ℕ,
      boxRadiusLogCorrection d n =
        Real.log C + (d - 1 : ℕ) * Real.log (2 * (n : ℝ) + 1) := by
    intro n
    rw [boxRadiusLogCorrection, boxRadiusPolynomialFactor,
      Real.log_mul hC.ne' (pow_pos (by positivity) _).ne', Real.log_pow]
  have hconst : Tendsto (fun n : ℕ ↦ (Real.log C + c) / (n : ℝ))
      atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hinput : Tendsto (fun n : ℕ ↦ 2 * (n : ℝ) + 1) atTop atTop := by
    exact tendsto_atTop_add_const_right atTop 1
      (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num))
  have hlogAffineReal : Tendsto
      (fun x : ℝ ↦ Real.log x ^ 1 / ((1 / 2 : ℝ) * x + (-1 / 2)))
      atTop (𝓝 0) := by
    exact Real.tendsto_pow_log_div_mul_add_atTop
      (1 / 2 : ℝ) (-1 / 2) 1 (by norm_num)
  have hlogAffine : Tendsto
      (fun n : ℕ ↦ Real.log (2 * (n : ℝ) + 1) / (n : ℝ))
      atTop (𝓝 0) := by
    have hcomp := hlogAffineReal.comp hinput
    convert hcomp using 1
    · funext n
      congr 1
      · simp
      · ring
  have hsum := hconst.add (hlogAffine.const_mul ((d - 1 : ℕ) : ℝ))
  convert hsum using 1
  · funext n
    rw [hrepr]
    ring
  · norm_num

private theorem log_boxRadiusTail_add_le_min
    {d : ℕ} (hd : 0 < d) {p : I} (hp : 0 < (p : ℝ))
    (m n : ℕ) (_hm : 0 < m) (_hn : 0 < n) :
    Real.log (boxRadiusTail d p (m + n)) ≤
      Real.log (boxRadiusTail d p m) + Real.log (boxRadiusTail d p n) +
        boxRadiusLogCorrection d (min m n) := by
  rcases le_total m n with hmn | hnm
  · simpa [Nat.min_eq_left hmn] using log_boxRadiusTail_add_le hd hp m n
  · simpa [Nat.min_eq_right hnm, add_comm] using log_boxRadiusTail_add_le hd hp n m

private theorem log_boxRadiusTail_add_ge_min
    {d : ℕ} (hd : 0 < d) {p : I} (hp : 0 < (p : ℝ))
    (i0 : Fin d) (m n : ℕ) (_hm : 0 < m) (_hn : 0 < n) :
    Real.log (boxRadiusTail d p m) + Real.log (boxRadiusTail d p n) -
        boxRadiusLogCorrection d (min m n) ≤
      Real.log (boxRadiusTail d p (m + n)) := by
  rcases le_total m n with hmn | hnm
  · simpa [Nat.min_eq_left hmn] using log_boxRadiusTail_add_ge hd hp m n i0
  · simpa [Nat.min_eq_right hnm, add_comm] using log_boxRadiusTail_add_ge hd hp n m i0

private theorem boxRadiusCorrectedLog_subadditive
    {d : ℕ} (hd : 0 < d) {p : I} (hp : 0 < (p : ℝ)) :
    Subadditive (correctedLogSequence
      (fun n ↦ Real.log (boxRadiusTail d p n))
      (boxRadiusLogCorrection d)
      (((d - 1 : ℕ) : ℝ) * Real.log 2)) := by
  apply correctedLogSequence_subadditive
  · exact log_boxRadiusTail_add_le_min hd hp
  · intro m n _hm _hn
    exact boxRadiusLogCorrection_add_le hd m n

private theorem boxRadiusCorrectedNegLog_subadditive
    {d : ℕ} (hd : 0 < d) {p : I} (hp : 0 < (p : ℝ)) (i0 : Fin d) :
    Subadditive (correctedNegLogSequence
      (fun n ↦ Real.log (boxRadiusTail d p n))
      (boxRadiusLogCorrection d)
      (((d - 1 : ℕ) : ℝ) * Real.log 2)) := by
  apply correctedNegLogSequence_subadditive
  · exact log_boxRadiusTail_add_ge_min hd hp i0
  · intro m n _hm _hn
    exact boxRadiusLogCorrection_add_le hd m n

private theorem boxRadiusLogCorrection_nonneg {d n : ℕ} (hd : 0 < d) :
    0 ≤ boxRadiusLogCorrection d n := by
  apply Real.log_nonneg
  unfold boxRadiusPolynomialFactor
  have hdreal : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hbase : (1 : ℝ) ≤ 2 * (n : ℝ) + 1 := by
    have hn : (0 : ℝ) ≤ n := by positivity
    linarith
  have hpow : (1 : ℝ) ≤ (2 * (n : ℝ) + 1) ^ (d - 1) := one_le_pow₀ hbase
  nlinarith [sq_nonneg (d : ℝ)]

private theorem boxRadiusCorrectedNegLog_bddBelow
    {d : ℕ} (hd : 0 < d) {p : I} (hp : 0 < (p : ℝ)) :
    BddBelow (range fun n ↦
      correctedNegLogSequence
        (fun k ↦ Real.log (boxRadiusTail d p k))
        (boxRadiusLogCorrection d)
        (((d - 1 : ℕ) : ℝ) * Real.log 2) n / n) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨n, rfl⟩
  by_cases hn : n = 0
  · subst n
    simp
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    change 0 ≤ correctedNegLogSequence
      (fun k ↦ Real.log (boxRadiusTail d p k))
      (boxRadiusLogCorrection d)
      (((d - 1 : ℕ) : ℝ) * Real.log 2) n / (n : ℝ)
    rw [correctedNegLogSequence_apply_of_pos hnpos]
    apply div_nonneg
    · have hlog : Real.log (boxRadiusTail d p n) ≤ 0 :=
        Real.log_nonpos (boxRadiusTail_pos_of_pos_density hd hp).le measureReal_le_one
      have hc : 0 ≤ ((d - 1 : ℕ) : ℝ) * Real.log 2 := by positivity
      linarith [boxRadiusLogCorrection_nonneg (n := n) hd]
    · positivity

private theorem boxRadiusCorrectedLog_bddBelow
    {d : ℕ} (hd : 0 < d) {p : I} (hp : 0 < (p : ℝ)) :
    BddBelow (range fun n ↦
      correctedLogSequence
        (fun k ↦ Real.log (boxRadiusTail d p k))
        (boxRadiusLogCorrection d)
        (((d - 1 : ℕ) : ℝ) * Real.log 2) n / n) := by
  refine ⟨Real.log (p : ℝ), ?_⟩
  rintro _ ⟨n, rfl⟩
  by_cases hn : n = 0
  · subst n
    simp [Real.log_nonpos hp.le p.property.2]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    change Real.log (p : ℝ) ≤ correctedLogSequence
      (fun k ↦ Real.log (boxRadiusTail d p k))
      (boxRadiusLogCorrection d)
      (((d - 1 : ℕ) : ℝ) * Real.log 2) n / (n : ℝ)
    rw [correctedLogSequence_apply_of_pos hnpos]
    have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
    apply (le_div_iff₀ hnreal).2
    have hpow := pow_le_boxRadiusTail (n := n) hd p
    have hlog := Real.log_le_log (pow_pos hp n) hpow
    rw [Real.log_pow] at hlog
    have hcorr := boxRadiusLogCorrection_nonneg (n := n) hd
    have hc : 0 ≤ ((d - 1 : ℕ) : ℝ) * Real.log 2 := by positivity
    nlinarith

/-- Grimmett's box-radius exponential rate.  The endpoint values outside the source domain
`0 < d` and `0 < p` are totalized to zero; all source-facing theorems carry those hypotheses. -/
noncomputable def boxRadiusDecayRate (d : ℕ) (p : I) : ℝ :=
  if hd : 0 < d then
    if hp : 0 < (p : ℝ) then
      correctedSubadditiveRate
        (boxRadiusCorrectedNegLog_subadditive hd hp (⟨0, hd⟩ : Fin d))
    else 0
  else 0

theorem boxRadiusDecayRate_eq_correctedSubadditiveRate
    {d : ℕ} (hd : 0 < d) {p : I} (hp : 0 < (p : ℝ)) :
    boxRadiusDecayRate d p = correctedSubadditiveRate
      (boxRadiusCorrectedNegLog_subadditive hd hp (⟨0, hd⟩ : Fin d)) := by
  simp [boxRadiusDecayRate, hd, hp]

/-- The rate is the limit in Grimmett's equation (6.33). -/
theorem boxRadiusTail_logRate_tendsto
    (d : ℕ) (hd : 0 < d) (p : I) (hp : 0 < (p : ℝ)) :
    Tendsto (fun n : ℕ ↦ -Real.log (boxRadiusTail d p n) / n)
      atTop (𝓝 (boxRadiusDecayRate d p)) := by
  let i0 : Fin d := ⟨0, hd⟩
  let f : ℕ → ℝ := fun n ↦ Real.log (boxRadiusTail d p n)
  let g : ℕ → ℝ := boxRadiusLogCorrection d
  let c : ℝ := ((d - 1 : ℕ) : ℝ) * Real.log 2
  have hminus : Subadditive (correctedNegLogSequence f g c) := by
    simpa [f, g, c, i0] using boxRadiusCorrectedNegLog_subadditive hd hp i0
  have hminusBdd : BddBelow (range fun n ↦ correctedNegLogSequence f g c n / n) := by
    simpa [f, g, c] using boxRadiusCorrectedNegLog_bddBelow hd hp
  have herror : Tendsto (fun n : ℕ ↦ (g n + c) / n) atTop (𝓝 0) := by
    simpa [g, c] using boxRadiusLogCorrection_add_const_div_tendsto_zero hd c
  have hlimit := tendsto_neg_div_correctedSubadditiveRate hminus hminusBdd herror
  rw [boxRadiusDecayRate_eq_correctedSubadditiveRate hd hp]
  simpa [f, g, c, i0] using hlimit

/-- Uniform finite-index control around the logarithmic rate, the exact abstract content of
equation (6.36). -/
theorem abs_natCast_mul_boxRadiusDecayRate_add_log_tail_le
    (d : ℕ) (hd : 0 < d) (p : I) (hp : 0 < (p : ℝ))
    {n : ℕ} (hn : 0 < n) :
    |(n : ℝ) * boxRadiusDecayRate d p + Real.log (boxRadiusTail d p n)| ≤
      boxRadiusLogCorrection d n + ((d - 1 : ℕ) : ℝ) * Real.log 2 := by
  let i0 : Fin d := ⟨0, hd⟩
  let f : ℕ → ℝ := fun n ↦ Real.log (boxRadiusTail d p n)
  let g : ℕ → ℝ := boxRadiusLogCorrection d
  let c : ℝ := ((d - 1 : ℕ) : ℝ) * Real.log 2
  have hplus : Subadditive (correctedLogSequence f g c) := by
    simpa [f, g, c] using boxRadiusCorrectedLog_subadditive hd hp
  have hminus : Subadditive (correctedNegLogSequence f g c) := by
    simpa [f, g, c, i0] using boxRadiusCorrectedNegLog_subadditive hd hp i0
  have hplusBdd : BddBelow (range fun n ↦ correctedLogSequence f g c n / n) := by
    simpa [f, g, c] using boxRadiusCorrectedLog_bddBelow hd hp
  have hminusBdd : BddBelow (range fun n ↦ correctedNegLogSequence f g c n / n) := by
    simpa [f, g, c] using boxRadiusCorrectedNegLog_bddBelow hd hp
  have herror : Tendsto (fun n : ℕ ↦ (g n + c) / n) atTop (𝓝 0) := by
    simpa [g, c] using boxRadiusLogCorrection_add_const_div_tendsto_zero hd c
  have hbound := abs_natCast_mul_correctedSubadditiveRate_add_le
    hplus hminus hplusBdd hminusBdd herror hn
  rw [boxRadiusDecayRate_eq_correctedSubadditiveRate hd hp]
  simpa [f, g, c, i0] using hbound

theorem boxRadiusTail_twoSided_with_logCorrection
    (d : ℕ) (hd : 0 < d) (p : I) (hp : 0 < (p : ℝ))
    {n : ℕ} (hn : 0 < n) :
    Real.exp (-(boxRadiusLogCorrection d n + ((d - 1 : ℕ) : ℝ) * Real.log 2)) *
        Real.exp (-(n : ℝ) * boxRadiusDecayRate d p) ≤
      boxRadiusTail d p n ∧
      boxRadiusTail d p n ≤
        Real.exp (boxRadiusLogCorrection d n + ((d - 1 : ℕ) : ℝ) * Real.log 2) *
          Real.exp (-(n : ℝ) * boxRadiusDecayRate d p) := by
  have hbound := abs_natCast_mul_boxRadiusDecayRate_add_log_tail_le d hd p hp hn
  rw [abs_le] at hbound
  have htail := boxRadiusTail_pos_of_pos_density hd (n := n) hp
  constructor
  · rw [← Real.exp_add, ← Real.exp_log htail]
    apply Real.exp_le_exp.mpr
    linarith
  · rw [← Real.exp_add, ← Real.exp_log htail]
    apply Real.exp_le_exp.mpr
    linarith

theorem exp_boxRadiusLogCorrection_add_eq
    {d n : ℕ} (hd : 0 < d) :
    Real.exp (boxRadiusLogCorrection d n + ((d - 1 : ℕ) : ℝ) * Real.log 2) =
      (2 : ℝ) ^ (d - 1) * boxRadiusPolynomialFactor d n := by
  have hK := boxRadiusPolynomialFactor_pos (d := d) (n := n) hd
  rw [Real.exp_add, boxRadiusLogCorrection, Real.exp_log hK,
    Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  ring

theorem exp_neg_boxRadiusLogCorrection_add_eq
    {d n : ℕ} (hd : 0 < d) :
    Real.exp (-(boxRadiusLogCorrection d n + ((d - 1 : ℕ) : ℝ) * Real.log 2)) =
      1 / ((2 : ℝ) ^ (d - 1) * boxRadiusPolynomialFactor d n) := by
  rw [Real.exp_neg, exp_boxRadiusLogCorrection_add_eq hd]
  exact inv_eq_one_div _

/-- Dimension-only prefactor used in the public form of Theorem 6.10. -/
noncomputable def boxRadiusDecayPrefactor (d : ℕ) : ℝ :=
  (2 : ℝ) ^ (d - 1) * (4 * (d : ℝ) ^ 2) * (3 : ℝ) ^ (d - 1)

theorem boxRadiusDecayPrefactor_pos {d : ℕ} (hd : 0 < d) :
    0 < boxRadiusDecayPrefactor d := by
  unfold boxRadiusDecayPrefactor
  positivity

private theorem exp_logCorrection_le_prefactor_mul_pow
    {d n : ℕ} (hd : 0 < d) (hn : 0 < n) :
    Real.exp (boxRadiusLogCorrection d n + ((d - 1 : ℕ) : ℝ) * Real.log 2) ≤
      boxRadiusDecayPrefactor d * (n : ℝ) ^ (d - 1) := by
  rw [exp_boxRadiusLogCorrection_add_eq hd]
  have hbase : 2 * (n : ℝ) + 1 ≤ 3 * (n : ℝ) := by
    have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hpow : (2 * (n : ℝ) + 1) ^ (d - 1) ≤
      (3 * (n : ℝ)) ^ (d - 1) := pow_le_pow_left₀ (by positivity) hbase _
  unfold boxRadiusPolynomialFactor boxRadiusDecayPrefactor
  calc
    (2 : ℝ) ^ (d - 1) *
        (4 * (d : ℝ) ^ 2 * (2 * (n : ℝ) + 1) ^ (d - 1)) ≤
      (2 : ℝ) ^ (d - 1) *
        (4 * (d : ℝ) ^ 2 * (3 * (n : ℝ)) ^ (d - 1)) := by gcongr
    _ = (2 : ℝ) ^ (d - 1) * (4 * (d : ℝ) ^ 2) *
        (3 : ℝ) ^ (d - 1) * (n : ℝ) ^ (d - 1) := by
      rw [mul_pow]
      ring

private theorem one_div_prefactor_div_pow_le_exp_neg_logCorrection
    {d n : ℕ} (hd : 0 < d) (hn : 0 < n) :
    (1 / boxRadiusDecayPrefactor d) / (n : ℝ) ^ (d - 1) ≤
      Real.exp (-(boxRadiusLogCorrection d n + ((d - 1 : ℕ) : ℝ) * Real.log 2)) := by
  rw [exp_neg_boxRadiusLogCorrection_add_eq hd]
  have hden := exp_logCorrection_le_prefactor_mul_pow hd hn
  rw [exp_boxRadiusLogCorrection_add_eq hd] at hden
  have hsmallPos : 0 < (2 : ℝ) ^ (d - 1) * boxRadiusPolynomialFactor d n :=
    mul_pos (pow_pos (by norm_num) _) (boxRadiusPolynomialFactor_pos hd)
  have hinv := one_div_le_one_div_of_le hsmallPos hden
  calc
    (1 / boxRadiusDecayPrefactor d) / (n : ℝ) ^ (d - 1) =
        1 / (boxRadiusDecayPrefactor d * (n : ℝ) ^ (d - 1)) := by
      rw [div_div]
    _ ≤ 1 / ((2 : ℝ) ^ (d - 1) * boxRadiusPolynomialFactor d n) := hinv

/-- **Grimmett, Theorem 6.10.** The dimension-only constants are quantified before the density,
and the bounds are stated with ordinary positive powers rather than negative-power junk values. -/
theorem boxRadiusTail_twoSided_decay
    (d : ℕ) (hd : 0 < d) :
    ∃ rho sigma : ℝ, 0 < rho ∧ 0 < sigma ∧
      ∀ (p : I), 0 < (p : ℝ) → ∀ n : ℕ, 0 < n →
        rho / (n : ℝ) ^ (d - 1) *
              Real.exp (-(n : ℝ) * boxRadiusDecayRate d p) ≤ boxRadiusTail d p n ∧
          boxRadiusTail d p n ≤
            sigma * (n : ℝ) ^ (d - 1) *
              Real.exp (-(n : ℝ) * boxRadiusDecayRate d p) := by
  refine ⟨1 / boxRadiusDecayPrefactor d, boxRadiusDecayPrefactor d,
    one_div_pos.mpr (boxRadiusDecayPrefactor_pos hd), boxRadiusDecayPrefactor_pos hd, ?_⟩
  intro p hp n hn
  rcases boxRadiusTail_twoSided_with_logCorrection d hd p hp hn with ⟨hlower, hupper⟩
  constructor
  · exact (mul_le_mul_of_nonneg_right
      (one_div_prefactor_div_pow_le_exp_neg_logCorrection hd hn)
      (Real.exp_pos _).le).trans hlower
  · exact hupper.trans <| by
      calc
        Real.exp (boxRadiusLogCorrection d n + ((d - 1 : ℕ) : ℝ) * Real.log 2) *
            Real.exp (-(n : ℝ) * boxRadiusDecayRate d p) ≤
          (boxRadiusDecayPrefactor d * (n : ℝ) ^ (d - 1)) *
            Real.exp (-(n : ℝ) * boxRadiusDecayRate d p) := by
              gcongr
              exact exp_logCorrection_le_prefactor_mul_pow hd hn
        _ = boxRadiusDecayPrefactor d * (n : ℝ) ^ (d - 1) *
            Real.exp (-(n : ℝ) * boxRadiusDecayRate d p) := rfl

#print axioms log_boxRadiusTail_add_le
#print axioms log_boxRadiusTail_add_ge
#print axioms boxRadiusTail_logRate_tendsto
#print axioms abs_natCast_mul_boxRadiusDecayRate_add_log_tail_le
#print axioms boxRadiusTail_twoSided_decay

end Percolation
