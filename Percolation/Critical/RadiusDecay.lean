import Percolation.Critical.RadiusBlock
import Percolation.Critical.SusceptibilityThreshold

/-!
# Exponential decay of the radius tail

This file first records the block proof of exponential decay from finite
susceptibility.  It supplies the exact conclusion of Grimmett's Theorem 5.4 and
will remain as an independent cross-check when the Menshikov derivation through
Lemmas 5.12, 5.17, 5.22, and 5.24 is closed.
-/

namespace Percolation

open scoped unitInterval

/-- Exponential radius decay obtained from finite susceptibility by the
translation-invariant BK block argument. -/
theorem radiusTail_exponential_decay_of_lt_critical_via_susceptibility
    (d : ℕ) (hd : 2 ≤ d) (p : I)
    (hp : (p : ℝ) < cubicCriticalProbability d) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ,
      radiusTail d p n ≤ Real.exp (-c * n) := by
  have hp1 : (p : ℝ) < 1 := hp.trans_le (cubicCriticalProbability_le_one d)
  exact radiusTail_exponential_decay_of_susceptibility_lt_top hp1
    (susceptibility_lt_top_of_lt_critical d hd p hp)

/-- Grimmett, Theorem 5.4: below `p_c`, the radius tail decays
exponentially.  The non-strict inequality is valid also at `n = 0`. -/
theorem radiusTail_exponential_decay_of_lt_critical
    (d : ℕ) (hd : 2 ≤ d) (p : I)
    (hp : (p : ℝ) < cubicCriticalProbability d) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ,
      radiusTail d p n ≤ Real.exp (-c * n) :=
  radiusTail_exponential_decay_of_lt_critical_via_susceptibility d hd p hp

#print axioms radiusTail_exponential_decay_of_lt_critical

end Percolation
