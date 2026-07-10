import Percolation.Critical.RadiusDecay

/-!
# Inverse-square-root radius bound

This file records the conclusion of Grimmett's Lemma 5.24.  The present proof
extracts it from the already established (stronger) exponential estimate; the
source-order recursive proof from (5.27)--(5.35) will be retained separately as
the Menshikov bootstrap once the conditional sausage comparison is connected to
the master inequality.
-/

namespace Percolation

open scoped unitInterval

/-- Grimmett, Lemma 5.24: below `p_c`, `g_p(n)` is bounded by a constant
times `n^{-1/2}`. -/
theorem radiusTail_le_inv_sqrt_of_lt_critical
    (d : ℕ) (hd : 2 ≤ d) (p : I)
    (hp : (p : ℝ) < cubicCriticalProbability d) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ n : ℕ, 1 ≤ n →
      radiusTail d p n ≤ delta / Real.sqrt n := by
  obtain ⟨c, hc, hdecay⟩ := radiusTail_exponential_decay_of_lt_critical d hd p hp
  refine ⟨c⁻¹, inv_pos.mpr hc, ?_⟩
  intro n hn
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := zero_lt_one.trans_le hnreal
  have hsqrtPos : 0 < Real.sqrt n := Real.sqrt_pos.2 hnpos
  have hsqrtLe : Real.sqrt n ≤ n := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · nlinarith [Real.sq_sqrt hnpos.le]
  have hcn : 0 < c * (n : ℝ) := mul_pos hc hnpos
  have hexpLower : c * (n : ℝ) ≤ Real.exp (c * n) := by
    linarith [Real.add_one_le_exp (c * (n : ℝ))]
  have hinvExp : Real.exp (-c * (n : ℝ)) ≤ 1 / (c * n) := by
    rw [show -c * (n : ℝ) = -(c * n) by ring, Real.exp_neg]
    simpa [one_div] using one_div_le_one_div_of_le hcn hexpLower
  have hrecip : 1 / (c * (n : ℝ)) ≤ c⁻¹ / Real.sqrt n := by
    rw [one_div, mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left
      (by simpa [one_div] using one_div_le_one_div_of_le hsqrtPos hsqrtLe)
      (inv_pos.mpr hc).le
  exact (hdecay n).trans (hinvExp.trans hrecip)

#print axioms radiusTail_le_inv_sqrt_of_lt_critical

end Percolation
