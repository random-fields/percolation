import Percolation.Core.Configuration

/-!
# Random-cluster model scaffold

This layer follows Grimmett's finite-volume random-cluster measures first, then boundary
conditions, stochastic ordering, infinite-volume limits, and Edwards-Sokal coupling.
-/

namespace Percolation

/-- Parameters `(p,q)` for the random-cluster model. -/
structure RandomClusterParameters where
  p : ℝ
  q : ℝ
  hp_nonneg : 0 ≤ p
  hp_le_one : p ≤ 1
  hq_pos : 0 < q

/-- A finite-volume random-cluster model scaffold on a base graph. -/
structure RandomClusterModel (V : Type u) where
  graph : BaseGraph V
  params : RandomClusterParameters

end Percolation
