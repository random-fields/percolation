import Percolation.Critical.BoxRadiusRate

/-! Application and boundary tests for Grimmett, Theorem 6.10. -/

namespace Chapter6Review

open Percolation Filter
open scoped unitInterval

/-- Quantifier order forces both constants to depend only on the dimension. -/
example (d : ℕ) (hd : 2 ≤ d) :
    ∃ rho sigma : ℝ, 0 < rho ∧ 0 < sigma ∧
      ∀ (p : I), 0 < (p : ℝ) → ∀ n : ℕ, 0 < n →
        rho / (n : ℝ) ^ (d - 1) *
              Real.exp (-(n : ℝ) * boxRadiusDecayRate d p) ≤ boxRadiusTail d p n ∧
          boxRadiusTail d p n ≤
            sigma * (n : ℝ) ^ (d - 1) *
              Real.exp (-(n : ℝ) * boxRadiusDecayRate d p) := by
  exact boxRadiusTail_twoSided_decay d (by omega)

/-- The exact logarithmic limit uses the same rate as the two-sided bounds. -/
example (d : ℕ) (hd : 2 ≤ d) (p : I) (hp : 0 < (p : ℝ)) :
    Tendsto (fun n : ℕ ↦ -Real.log (boxRadiusTail d p n) / n)
      Filter.atTop (nhds (boxRadiusDecayRate d p)) := by
  exact boxRadiusTail_logRate_tendsto d (by omega) p hp

/-- The smallest source-valid radius avoids all negative-power and division-by-zero junk. -/
example (d : ℕ) (hd : 2 ≤ d) (p : I) (hp : 0 < (p : ℝ)) :
    ∃ rho sigma : ℝ, 0 < rho ∧ 0 < sigma ∧
      rho * Real.exp (-boxRadiusDecayRate d p) ≤ boxRadiusTail d p 1 ∧
        boxRadiusTail d p 1 ≤ sigma * Real.exp (-boxRadiusDecayRate d p) := by
  obtain ⟨rho, sigma, hrho, hsigma, h⟩ := boxRadiusTail_twoSided_decay d (by omega)
  refine ⟨rho, sigma, hrho, hsigma, ?_⟩
  simpa using h p hp 1 (by omega)

end Chapter6Review
