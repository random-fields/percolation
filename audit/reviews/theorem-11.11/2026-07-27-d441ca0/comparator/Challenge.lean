import Percolation.Critical.Basic

/-! Source-facing Comparator challenge for Grimmett, Theorem 11.11. The open proof is
intentional and this module must never be imported by production code. -/

namespace ComparatorChallenge

/-- Grimmett, *Percolation* (2nd ed.), Theorem 11.11, p. 287. -/
theorem grimmett_theorem_11_11 :
    Percolation.cubicCriticalProbability 2 = (1 : ℝ) / 2 := by
  sorry

end ComparatorChallenge
