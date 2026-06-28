import Percolation.Core.Configuration

/-!
# Planar percolation scaffold

The planar layer will host dual graphs, crossing events, RSW-style inputs, and the square-lattice
bond-percolation threshold theorem.
-/

namespace Percolation

/-- A scaffold for planar dual graph data. Production work should use Mathlib graph embeddings
or a project-specific planar-lattice API after design review. -/
structure PlanarDualPair (V Vd : Type u) where
  primal : BaseGraph V
  dual : BaseGraph Vd
  Crosses : V → V → Vd → Vd → Prop

end Percolation
