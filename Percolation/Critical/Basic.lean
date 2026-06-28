import Percolation.Bernoulli.Basic

/-!
# Critical probability scaffold

Critical-point work should separate definition-level monotonicity from lattice-specific theorem
statements such as the square-lattice value `p_c = 1/2`.
-/

namespace Percolation

/-- A named package for a critical parameter attached to a Bernoulli bond model. -/
structure CriticalParameter (V : Type u) where
  model : BernoulliBond V
  pc : ℝ
  pc_nonneg : 0 ≤ pc
  pc_le_one : pc ≤ 1

end Percolation
