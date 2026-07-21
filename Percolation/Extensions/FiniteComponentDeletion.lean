import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
# Component counts after deleting one vertex

These finite-graph lemmas isolate the combinatorial input in Kalikow's proof of Grimmett's
Theorem 12.3.  Deleting a vertex can lower the component count by at most one; if the deleted
vertex has a neighbour, it does not lower it at all.
-/

namespace Percolation

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

private def deleteVertexInclusionHom (G : SimpleGraph V) (v : V) :
    G.induce ({v}ᶜ : Set V) →g G where
  toFun := Subtype.val
  map_rel' := fun h ↦ h

private theorem map_deleteVertex_componentMk (G : SimpleGraph V) (v : V)
    (x : {x : V // x ∈ ({v}ᶜ : Set V)}) :
    SimpleGraph.ConnectedComponent.map (deleteVertexInclusionHom G v)
        ((G.induce ({v}ᶜ : Set V)).connectedComponentMk x) =
      G.connectedComponentMk x.1 := by
  rfl

/-- Deleting one vertex lowers the number of connected components by at most one. -/
theorem connectedComponent_card_le_deleteVertex_add_one
    (G : SimpleGraph V) (v : V) :
    Nat.card G.ConnectedComponent ≤
      Nat.card (G.induce ({v}ᶜ : Set V)).ConnectedComponent + 1 := by
  classical
  let H := G.induce ({v}ᶜ : Set V)
  let phi : H.ConnectedComponent → G.ConnectedComponent :=
    SimpleGraph.ConnectedComponent.map (deleteVertexInclusionHom G v)
  let f : Option H.ConnectedComponent → G.ConnectedComponent
    | none => G.connectedComponentMk v
    | some c => phi c
  have hsurj : Function.Surjective f := by
    intro C
    rcases C.exists_rep with ⟨x, hx⟩
    by_cases hxv : x = v
    · subst x
      refine ⟨none, ?_⟩
      change G.connectedComponentMk v = C
      exact hx
    · let xH : {x : V // x ∈ ({v}ᶜ : Set V)} := ⟨x, by simpa using hxv⟩
      refine ⟨some (H.connectedComponentMk xH), ?_⟩
      change G.connectedComponentMk x = C
      exact hx
  have hcard := Nat.card_le_card_of_surjective f hsurj
  simpa [f, H, Nat.card_eq_fintype_card] using hcard

/-- If the deleted vertex has a neighbour, every component still has a representative away
from that vertex, so deletion cannot have fewer components. -/
theorem connectedComponent_card_le_deleteVertex_of_exists_adj
    (G : SimpleGraph V) (v : V) (hneighbor : ∃ u, G.Adj v u) :
    Nat.card G.ConnectedComponent ≤
      Nat.card (G.induce ({v}ᶜ : Set V)).ConnectedComponent := by
  classical
  let H := G.induce ({v}ᶜ : Set V)
  let phi : H.ConnectedComponent → G.ConnectedComponent :=
    SimpleGraph.ConnectedComponent.map (deleteVertexInclusionHom G v)
  obtain ⟨u, hvu⟩ := hneighbor
  have huv : u ≠ v := hvu.ne'
  have hsurj : Function.Surjective phi := by
    intro C
    rcases C.exists_rep with ⟨x, hx⟩
    by_cases hxv : x = v
    · subst x
      let uH : {x : V // x ∈ ({v}ᶜ : Set V)} := ⟨u, by simpa using huv⟩
      refine ⟨H.connectedComponentMk uH, ?_⟩
      change G.connectedComponentMk u = C
      rw [← hx]
      exact SimpleGraph.ConnectedComponent.eq.mpr hvu.symm.reachable
    · let xH : {x : V // x ∈ ({v}ᶜ : Set V)} := ⟨x, by simpa using hxv⟩
      refine ⟨H.connectedComponentMk xH, ?_⟩
      change G.connectedComponentMk x = C
      exact hx
  exact Nat.card_le_card_of_surjective phi hsurj

/-- If two neighbours of `v` lie in different components after `v` is deleted, then deleting
`v` strictly increases the number of connected components.  This is the strict form of the
one-vertex deletion estimate used in Kalikow's insertion argument. -/
theorem connectedComponent_card_lt_deleteVertex_of_two_neighbors
    (G : SimpleGraph V) (v u w : V) (hvu : G.Adj v u) (hvw : G.Adj v w)
    (huw : ¬(G.induce ({v}ᶜ : Set V)).Reachable
      ⟨u, by simpa using hvu.ne'⟩ ⟨w, by simpa using hvw.ne'⟩) :
    Nat.card G.ConnectedComponent <
      Nat.card (G.induce ({v}ᶜ : Set V)).ConnectedComponent := by
  classical
  let H := G.induce ({v}ᶜ : Set V)
  let phi : H.ConnectedComponent → G.ConnectedComponent :=
    SimpleGraph.ConnectedComponent.map (deleteVertexInclusionHom G v)
  let uH : {x : V // x ∈ ({v}ᶜ : Set V)} := ⟨u, by simpa using hvu.ne'⟩
  let wH : {x : V // x ∈ ({v}ᶜ : Set V)} := ⟨w, by simpa using hvw.ne'⟩
  have hsurj : Function.Surjective phi := by
    intro C
    rcases C.exists_rep with ⟨x, hx⟩
    by_cases hxv : x = v
    · subst x
      refine ⟨H.connectedComponentMk uH, ?_⟩
      change G.connectedComponentMk u = C
      rw [← hx]
      exact SimpleGraph.ConnectedComponent.eq.mpr hvu.symm.reachable
    · let xH : {x : V // x ∈ ({v}ᶜ : Set V)} := ⟨x, by simpa using hxv⟩
      refine ⟨H.connectedComponentMk xH, ?_⟩
      change G.connectedComponentMk x = C
      exact hx
  have hcomponents_ne : H.connectedComponentMk uH ≠ H.connectedComponentMk wH := by
    intro h
    apply huw
    exact SimpleGraph.ConnectedComponent.eq.mp h
  have himages_eq : phi (H.connectedComponentMk uH) =
      phi (H.connectedComponentMk wH) := by
    change G.connectedComponentMk u = G.connectedComponentMk w
    exact SimpleGraph.ConnectedComponent.eq.mpr
      (hvu.symm.reachable.trans hvw.reachable)
  have hnotinj : ¬Function.Injective phi := by
    intro hinj
    exact hcomponents_ne (hinj himages_eq)
  simpa [H, Nat.card_eq_fintype_card] using
    (Fintype.card_lt_of_surjective_not_injective phi hsurj hnotinj)

/-- If deleting `v` strictly decreases the component count, then `v` was isolated. -/
theorem no_adj_of_deleteVertex_card_lt (G : SimpleGraph V) (v : V)
    (hcard : Nat.card (G.induce ({v}ᶜ : Set V)).ConnectedComponent <
      Nat.card G.ConnectedComponent) :
    ∀ u, ¬G.Adj v u := by
  intro u hvu
  exact (not_le_of_gt hcard)
    (connectedComponent_card_le_deleteVertex_of_exists_adj G v ⟨u, hvu⟩)

end Percolation
