import Percolation.Core.Configuration

/-!
# Bernoulli percolation scaffold

The first production target here is the finite-edge product measure, followed by increasing
events, FKG, BK/Reimer, and Russo's formula.
-/

namespace Percolation

/-- Parameters for Bernoulli bond percolation on a graph. -/
structure BernoulliBond (V : Type u) where
  graph : BaseGraph V
  p : ℝ
  hp_nonneg : 0 ≤ p
  hp_le_one : p ≤ 1

/-- Placeholder for the percolation probability `θ(p)`. The production definition should use
the probability that the origin cluster is infinite on the chosen lattice. -/
structure PercolationProbability (V : Type u) where
  model : BernoulliBond V
  theta : ℝ

end Percolation
