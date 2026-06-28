import Mathlib.Data.Real.Basic

/-!
# Core percolation vocabulary

This file intentionally starts with light, dependency-free scaffolding. As source targets land,
replace these planning objects with Mathlib-native graph, path, finite-support, and probability
APIs rather than growing a parallel graph library.
-/

namespace Percolation

/-- A simple undirected graph shape used as an early scaffold for lattice and finite-graph
percolation targets. Later modules should bridge this to Mathlib graph APIs. -/
structure BaseGraph (V : Type u) where
  Adj : V → V → Prop
  symm : ∀ {x y : V}, Adj x y → Adj y x
  loopless : ∀ x : V, ¬ Adj x x

/-- A bond configuration records which unordered graph-adjacent bonds are open. -/
structure BondConfiguration (V : Type u) where
  IsOpen : V → V → Prop
  symm : ∀ {x y : V}, IsOpen x y → IsOpen y x
  loopless : ∀ x : V, ¬ IsOpen x x

/-- A configuration is supported by a base graph if every open edge is a graph edge. -/
def BondConfiguration.Respects {V : Type u} (G : BaseGraph V) (ω : BondConfiguration V) : Prop :=
  ∀ x y : V, ω.IsOpen x y → G.Adj x y

/-- Event-level monotonicity for bond configurations. -/
def IncreasingEvent {V : Type u} (A : Set (BondConfiguration V)) : Prop :=
  ∀ ⦃ω η : BondConfiguration V⦄,
    (∀ x y : V, ω.IsOpen x y → η.IsOpen x y) → ω ∈ A → η ∈ A

/-- The event that two vertices are connected by an open path. Kept as a placeholder predicate
until the Mathlib graph-walk representation is selected. -/
def OpenConnection {V : Type u} (_ω : BondConfiguration V) (_x _y : V) : Prop :=
  ∃ _ : Unit, True

/-- The cluster of a vertex in a configuration, represented extensionally. -/
def openCluster {V : Type u} (ω : BondConfiguration V) (x : V) : Set V :=
  {y | OpenConnection ω x y}

end Percolation
