import Percolation.Critical.TreeGraph

/-! Application and source-domain tests for Grimmett, Lemmas 6.87 and 6.89. -/

namespace Chapter6Review

open Percolation Set SimpleGraph
open scoped ENNReal unitInterval BigOperators

/-- The ambient graph may be infinite; only the terminal family is required to be finite and
nonempty. -/
example {V : Type*} (G : SimpleGraph V) (hG : G.Connected)
    (W : Finset V) (hW : W.Nonempty) :
    ∃ w ∈ W, ∀ x, x ∈ W → x ≠ w → ∀ y, y ∈ W → y ≠ w →
      (G.deleteIncidenceSet w).Reachable x y := by
  exact exists_terminal_deletion_preserves_connected G hG W hW

/-- Lemma 6.89 is deliberately ENNReal-valued, so a nonsummable endpoint series is not assigned
Lean's real-`tsum` junk value zero. -/
example (d : ℕ) (p : I) (x₀ x₁ x₂ : Cubic d) :
    bernoulliBondMeasure d p (threePointConnectionEvent d x₀ x₁ x₂) ≤
      ∑' u : Cubic d,
        twoPointConnectivityENNReal d p u x₀ *
          twoPointConnectivityENNReal d p u x₁ *
            twoPointConnectivityENNReal d p u x₂ := by
  exact threePointConnectivity_le_tsum_prod d p x₀ x₁ x₂

/-- Repeated terminals are handled by zero-length tripod branches. -/
example {V : Type*} [DecidableEq V] (G : SimpleGraph V) (hG : G.Connected) (x y : V) :
    ∃ u : V, ∃ w₀ : G.Walk u x, ∃ w₁ : G.Walk u x, ∃ w₂ : G.Walk u y,
      w₀.edges.Disjoint w₁.edges ∧ w₀.edges.Disjoint w₂.edges ∧
        w₁.edges.Disjoint w₂.edges := by
  exact exists_three_pairwise_edgeDisjoint_walks G hG x x y

end Chapter6Review
