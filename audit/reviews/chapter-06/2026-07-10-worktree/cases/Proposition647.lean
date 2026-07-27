import Percolation.Critical.TwoPoint

/-! Application and junk-value tests for Grimmett, Proposition 6.47. -/

namespace Chapter6Review

open Percolation
open scoped unitInterval

/-- Faithful quantifier order and the corrected `x ≠ 0` domain for the printed lower bound. -/
example (d : ℕ) (hd : 2 ≤ d) :
    ∃ lambda : ℝ, 0 < lambda ∧ ∀ (p : I), 0 < (p : ℝ) → ∀ x : Cubic d,
      (x ≠ cubicOrigin →
        lambda * (p : ℝ) ^ (d * cubicL1Dist cubicOrigin x) /
            (cubicL1Dist cubicOrigin x : ℝ) ^ (4 * d * (d - 1)) *
            Real.exp (-(cubicL1Dist cubicOrigin x : ℝ) * boxRadiusDecayRate d p) ≤
          twoPointConnectivity d p cubicOrigin x) ∧
      twoPointConnectivity d p cubicOrigin x ≤
        Real.exp (-(cubicLInfDist cubicOrigin x : ℝ) * boxRadiusDecayRate d p) := by
  exact twoPointConnectivity_twoSided_decay d (by omega)

/-- The upper inequality handles `x=0` as equality, rather than relying on a totalized negative
power at zero. -/
example (d : ℕ) (hd : 2 ≤ d) (p : I) (hp : 0 < (p : ℝ)) :
    twoPointConnectivity d p (cubicOrigin : Cubic d) cubicOrigin = 1 ∧
      twoPointConnectivity d p (cubicOrigin : Cubic d) cubicOrigin ≤
        Real.exp (-(cubicLInfDist (cubicOrigin : Cubic d) cubicOrigin : ℝ) *
          boxRadiusDecayRate d p) := by
  constructor
  · exact twoPointConnectivity_self d p cubicOrigin
  · exact twoPointConnectivity_le_exp_neg_lInfDist_mul_rate (by omega) hp cubicOrigin

/-- The omitted hypothesis in the printed lower expression is genuinely needed: its denominator
at the origin is zero in positive dimensions. -/
example (d : ℕ) (hd : 2 ≤ d) :
    ((cubicL1Dist cubicOrigin (cubicOrigin : Cubic d) : ℝ) ^
      (4 * d * (d - 1))) = 0 := by
  rw [cubicL1Dist_self]
  simp only [Nat.cast_zero]
  exact zero_pow (mul_ne_zero (mul_ne_zero (by norm_num) (by omega)) (by omega))

end Chapter6Review
