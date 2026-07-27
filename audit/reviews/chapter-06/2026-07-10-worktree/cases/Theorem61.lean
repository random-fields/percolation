import Percolation.Critical.BoxRadius

/-! Application and endpoint tests for Grimmett, Theorem 6.1. -/

namespace Chapter6Review

open Percolation
open scoped ENNReal unitInterval

/-- The public theorem has exactly the chapter's dimension and finite-susceptibility inputs. -/
example (d : ℕ) (hd : 2 ≤ d) (p : I) (hchi : susceptibility d p < ⊤) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ,
      boxRadiusTail d p n ≤ Real.exp (-c * n) := by
  exact boxRadiusTail_exponential_decay_of_susceptibility_lt_top d hd p hchi

/-- Radius zero is a genuine equality case of the non-strict exponential estimate. -/
example (d : ℕ) (p : I) : boxRadiusTail d p 0 = 1 := by
  exact boxRadiusTail_zero d p

/-- The tempting strict inequality at radius zero is impossible. -/
example (d : ℕ) (p : I) :
    ¬∃ c : ℝ, 0 < c ∧ boxRadiusTail d p 0 < Real.exp (-c * (0 : ℕ)) := by
  simp

/-- The box event really is controlled by the already audited graph-radius event. -/
example (d : ℕ) (p : I) (n : ℕ) : boxRadiusTail d p n ≤ radiusTail d p n := by
  exact boxRadiusTail_le_radiusTail d p n

end Chapter6Review

