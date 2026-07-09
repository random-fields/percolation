/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import Percolation.Bernoulli.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Finite.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.Interval
import Mathlib.Topology.Order.Basic

/-!
# The number of open clusters per vertex

Source: Grimmett, *Percolation* (2nd ed., 1999), Chapter 4, pp. 77–86
(source id `grimmett-percolation-1999`).

This file starts the formalization of Grimmett's number `κ(p)` of open clusters per vertex.
The graph-theoretic declarations are stated for an arbitrary simple graph. They formalize the
finite-component identity (4.7), the comparison (4.6), the lower half of the sandwich (4.8), and
the deterministic convergence argument used in Theorem 4.2.

Mathlib currently has definitions for ergodic maps and actions but no multiparameter pointwise
ergodic theorem for box averages. Consequently, `normalizedComponentCount_tendsto_of_sandwich`
isolates the exact convergence input used at (4.9), rather than introducing a project axiom.

## Main results

* `sum_componentWeight_eq_componentCount`: the sum of reciprocal component sizes on a finite
  graph is the number of connected components, Grimmett's identity (4.7).
* `componentWeight_le_induce`: an ambient component has no larger reciprocal size than its
  component in a finite induced graph, the comparison (4.6).
* `componentWeightAverage_le_normalizedComponentCount`: the lower sandwich bound (4.8).
* `normalizedComponentCount_tendsto_of_sandwich`: the deterministic limit step in Theorem 4.2.
-/

open scoped BigOperators unitInterval

namespace Percolation

open Filter Set

noncomputable section

universe u

variable {V : Type u}

/-- The number of vertices in the connected component of `v`. Following the convention in
Grimmett's (4.4), this is `0` when the component is infinite. -/
noncomputable def componentSize (G : SimpleGraph V) (v : V) : ℕ :=
  Nat.card (G.connectedComponentMk v).supp

/-- The reciprocal size of the component of `v`, with value `0` for an infinite component.
This is Grimmett's random variable `Γ(v)` from (4.4). -/
noncomputable def componentWeight (G : SimpleGraph V) (v : V) : ℝ :=
  1 / (componentSize G v : ℝ)

theorem componentWeight_nonneg (G : SimpleGraph V) (v : V) :
    0 ≤ componentWeight G v := by
  simp [componentWeight]

/-- On a finite graph, summing reciprocal component sizes counts connected components.
This is the abstract finite-graph form of Grimmett's identity (4.7). -/
theorem sum_componentWeight_eq_componentCount [Fintype V] (G : SimpleGraph V) :
    ∑ v : V, componentWeight G v = Nat.card G.ConnectedComponent := by
  classical
  letI := Fintype.ofFinite G.ConnectedComponent
  rw [← Fintype.sum_fiberwise G.connectedComponentMk (componentWeight G)]
  calc
    ∑ c : G.ConnectedComponent,
        ∑ v : {v : V // G.connectedComponentMk v = c}, componentWeight G v =
        ∑ _c : G.ConnectedComponent, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro c _hc
      letI := Fintype.ofFinite c.supp
      let e : {v : V // G.connectedComponentMk v = c} ≃ c.supp := {
        toFun := fun v ↦ ⟨v, (c.mem_supp_iff v).2 v.property⟩
        invFun := fun v ↦ ⟨v, (c.mem_supp_iff v).1 v.property⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
      }
      have hcard :
          Fintype.card {v : V // G.connectedComponentMk v = c} =
            Fintype.card c.supp :=
        Fintype.card_congr e
      have hpos : 0 < Fintype.card c.supp := by
        rw [Fintype.card_pos_iff]
        exact Set.nonempty_coe_sort.mpr c.nonempty_supp
      simp only [componentWeight, componentSize]
      simp_rw [show ∀ v : {v : V // G.connectedComponentMk v = c},
          G.connectedComponentMk (v : V) = c from fun v ↦ v.property]
      simp only [Nat.card_eq_fintype_card, Finset.sum_const, nsmul_eq_mul, one_div]
      rw [Finset.card_univ, hcard]
      exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hpos.ne')
    _ = Nat.card G.ConnectedComponent := by
      simp [Nat.card_eq_fintype_card]

/-- The vertices in one connected component contribute exactly one to the reciprocal-size sum. -/
theorem sum_componentWeight_fiber_eq_one [Fintype V] (G : SimpleGraph V)
    (c : G.ConnectedComponent) [DecidableEq G.ConnectedComponent] :
    ∑ v : {v : V // G.connectedComponentMk v = c}, componentWeight G v = 1 := by
  classical
  letI := Fintype.ofFinite c.supp
  let e : {v : V // G.connectedComponentMk v = c} ≃ c.supp := {
    toFun := fun v ↦ ⟨v, (c.mem_supp_iff v).2 v.property⟩
    invFun := fun v ↦ ⟨v, (c.mem_supp_iff v).1 v.property⟩
    left_inv := fun _ ↦ rfl
    right_inv := fun _ ↦ rfl
  }
  have hcard :
      Fintype.card {v : V // G.connectedComponentMk v = c} = Fintype.card c.supp :=
    Fintype.card_congr e
  have hpos : 0 < Fintype.card c.supp := by
    rw [Fintype.card_pos_iff]
    exact Set.nonempty_coe_sort.mpr c.nonempty_supp
  simp only [componentWeight, componentSize]
  simp_rw [show ∀ v : {v : V // G.connectedComponentMk v = c},
      G.connectedComponentMk (v : V) = c from fun v ↦ v.property]
  simp only [Nat.card_eq_fintype_card, Finset.sum_const, nsmul_eq_mul, one_div]
  rw [Finset.card_univ, hcard]
  exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hpos.ne')

/-- Passing from an ambient graph to the graph induced on a finite vertex set can only decrease
component sizes, and hence can only increase reciprocal component sizes. This is (4.6). -/
theorem componentWeight_le_induce (G : SimpleGraph V) (B : Finset V) (x : B) :
    componentWeight G x ≤ componentWeight (G.induce (B : Set V)) x := by
  classical
  let H := G.induce (B : Set V)
  let cB := H.connectedComponentMk x
  let c := G.connectedComponentMk (x : V)
  by_cases hfin : Finite c.supp
  · letI : Finite c.supp := hfin
    let f : cB.supp → c.supp := fun y ↦ by
      have hyEq : H.connectedComponentMk (y : B) = H.connectedComponentMk x := by
        simpa [cB] using (cB.mem_supp_iff (y : B)).1 y.property
      have hyReach : H.Reachable (y : B) x :=
        SimpleGraph.ConnectedComponent.eq.mp hyEq
      have hyReach' : G.Reachable (y : B) x :=
        hyReach.map (SimpleGraph.Embedding.induce (G := G) (B : Set V)).toHom
      exact ⟨(y : B), (c.mem_supp_iff ((y : B) : V)).2 <| by
        simpa [c] using SimpleGraph.ConnectedComponent.eq.mpr hyReach'⟩
    have hf : Function.Injective f := by
      intro y z h
      have hv : ((f y : c.supp) : V) = ((f z : c.supp) : V) :=
        congrArg (fun w : c.supp ↦ (w : V)) h
      exact Subtype.ext (Subtype.ext hv)
    have hcard : Nat.card cB.supp ≤ Nat.card c.supp :=
      Finite.card_le_of_embedding ⟨f, hf⟩
    haveI : Nonempty cB.supp := Set.nonempty_coe_sort.mpr cB.nonempty_supp
    have hpos : 0 < Nat.card cB.supp := Finite.card_pos
    exact one_div_le_one_div_of_le (Nat.cast_pos.mpr hpos) (Nat.cast_le.mpr hcard)
  · letI : Infinite c.supp := not_finite_iff_infinite.mp hfin
    simp [componentWeight, componentSize, c, Nat.card_eq_zero_of_infinite]

/-- The mean ambient component weight over a finite vertex set. -/
noncomputable def componentWeightAverage (G : SimpleGraph V) (B : Finset V) : ℝ :=
  (∑ x : B, componentWeight G x) / B.card

/-- The number of components in the graph induced on `B`, normalized by the volume of `B`.
This is the finite-volume random variable `Kₙ / |B(n)|` in Theorem 4.2. -/
noncomputable def normalizedComponentCount (G : SimpleGraph V) (B : Finset V) : ℝ :=
  (Nat.card (G.induce (B : Set V)).ConnectedComponent : ℝ) / B.card

/-- The ambient component-weight average is bounded above by the normalized number of
components in the induced graph. This is Grimmett's lower sandwich estimate (4.8). -/
theorem componentWeightAverage_le_normalizedComponentCount (G : SimpleGraph V)
    (B : Finset V) :
    componentWeightAverage G B ≤ normalizedComponentCount G B := by
  classical
  unfold componentWeightAverage normalizedComponentCount
  by_cases hB : B.Nonempty
  · have hcard : (0 : ℝ) < B.card :=
      Nat.cast_pos.mpr (Finset.card_pos.mpr hB)
    apply div_le_div_of_nonneg_right _ hcard.le
    calc
      ∑ x : B, componentWeight G x ≤
          ∑ x : B, componentWeight (G.induce (B : Set V)) x :=
        Finset.sum_le_sum fun x _hx ↦ componentWeight_le_induce G B x
      _ = Nat.card (G.induce (B : Set V)).ConnectedComponent :=
        sum_componentWeight_eq_componentCount _
  · simp [Finset.not_nonempty_iff_eq_empty.mp hB]

/-- Components of the induced graph on `B` for which the ambient reciprocal component weight
differs from the finite-volume weight. These are exactly the components responsible for the
boundary correction in Grimmett's (4.11). -/
noncomputable def escapingComponents (G : SimpleGraph V) (B : Finset V) :
    Finset (G.induce (B : Set V)).ConnectedComponent := by
  classical
  exact Finset.univ.filter fun c ↦
    ∃ x : B, (G.induce (B : Set V)).connectedComponentMk x = c ∧
      componentWeight G x ≠ componentWeight (G.induce (B : Set V)) x

/-- The finite-volume component count is at most the sum of ambient reciprocal component
weights plus one for every component affected by the boundary. This is the abstract counting
content of Grimmett's (4.11). -/
theorem componentCount_le_weightSum_add_escaping (G : SimpleGraph V) (B : Finset V) :
    (Nat.card (G.induce (B : Set V)).ConnectedComponent : ℝ) ≤
      (∑ x : B, componentWeight G x) + (escapingComponents G B).card := by
  classical
  let H := G.induce (B : Set V)
  letI := Fintype.ofFinite H.ConnectedComponent
  let E := escapingComponents G B
  calc
    (Nat.card H.ConnectedComponent : ℝ) =
        ∑ _c : H.ConnectedComponent, (1 : ℝ) := by
      simp [Nat.card_eq_fintype_card]
    _ ≤ ∑ c : H.ConnectedComponent,
        ((∑ x : {x : B // H.connectedComponentMk x = c}, componentWeight G x) +
          if c ∈ E then 1 else 0) := by
      apply Finset.sum_le_sum
      intro c _hc
      by_cases hcE : c ∈ E
      · simp only [hcE, if_true]
        have hnonneg :
            0 ≤ ∑ x : {x : B // H.connectedComponentMk x = c}, componentWeight G x :=
          Finset.sum_nonneg fun x _hx ↦ componentWeight_nonneg G x
        linarith
      · simp only [hcE, if_false, add_zero]
        have heq : ∀ x : {x : B // H.connectedComponentMk x = c},
            componentWeight G x = componentWeight H x := by
          intro x
          by_contra hx
          apply hcE
          simp only [E, escapingComponents, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨x, x.property, hx⟩
        calc
          (1 : ℝ) = ∑ x : {x : B // H.connectedComponentMk x = c},
              componentWeight H x := (sum_componentWeight_fiber_eq_one H c).symm
          _ = ∑ x : {x : B // H.connectedComponentMk x = c},
              componentWeight G x := by
            apply Finset.sum_congr rfl
            intro x _hx
            exact (heq x).symm
          _ ≤ ∑ x : {x : B // H.connectedComponentMk x = c},
              componentWeight G x := le_rfl
    _ = (∑ x : B, componentWeight G x) + (escapingComponents G B).card := by
      rw [Finset.sum_add_distrib]
      have hfiber :
          (∑ c : H.ConnectedComponent,
            ∑ x : {x : B // H.connectedComponentMk x = c}, componentWeight G x) =
            ∑ x : B, componentWeight G x :=
        Fintype.sum_fiberwise H.connectedComponentMk (fun x : B ↦ componentWeight G x)
      rw [hfiber]
      simp [E]

/-- If every boundary-affected component can be charged injectively to a boundary vertex, then
the correction in (4.11) is at most the cardinality of that boundary. -/
theorem componentCount_le_weightSum_add_boundary (G : SimpleGraph V) (B : Finset V)
    (boundary : Finset B) (hcard : (escapingComponents G B).card ≤ boundary.card) :
    (Nat.card (G.induce (B : Set V)).ConnectedComponent : ℝ) ≤
      (∑ x : B, componentWeight G x) + boundary.card := by
  exact (componentCount_le_weightSum_add_escaping G B).trans <|
    add_le_add le_rfl (Nat.cast_le.mpr hcard)

/-- The deterministic squeeze step in Grimmett's proof of Theorem 4.2.

The lower bound is (4.8). The hypothesis `hupper` is the boundary estimate (4.11)–(4.12),
with `boundaryError n` standing for `|∂B(n)| / |B(n)|`. The convergence hypothesis `haverage`
is precisely the multiparameter ergodic-theorem input (4.9). -/
theorem normalizedComponentCount_tendsto_of_sandwich (G : SimpleGraph V)
    (B : ℕ → Finset V) (boundaryError : ℕ → ℝ) (κ : ℝ)
    (haverage : Tendsto (fun n ↦ componentWeightAverage G (B n)) atTop (nhds κ))
    (hboundary : Tendsto boundaryError atTop (nhds 0))
    (hupper : ∀ n, normalizedComponentCount G (B n) ≤
      componentWeightAverage G (B n) + boundaryError n) :
    Tendsto (fun n ↦ normalizedComponentCount G (B n)) atTop (nhds κ) := by
  have hupp : Tendsto
      (fun n ↦ componentWeightAverage G (B n) + boundaryError n) atTop (nhds κ) := by
    simpa using haverage.add hboundary
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le haverage hupp
  · exact fun n ↦ componentWeightAverage_le_normalizedComponentCount G (B n)
  · exact hupper

/-! ### Cubic boxes -/

/-- The vertex box `B(n) = [-n,n]^d ∩ ℤ^d` used throughout Grimmett's Chapter 4. -/
noncomputable def cubicBoxVertices (d n : ℕ) : Finset (Cubic d) :=
  Fintype.piFinset fun _ : Fin d ↦ Finset.Icc (-(n : ℤ)) n

@[simp]
theorem mem_cubicBoxVertices {d n : ℕ} {x : Cubic d} :
    x ∈ cubicBoxVertices d n ↔ ∀ i, -(n : ℤ) ≤ x i ∧ x i ≤ n := by
  simp [cubicBoxVertices]

/-- The cubic box `B(n)` has `(2n+1)^d` vertices. -/
theorem cubicBoxVertices_card (d n : ℕ) :
    (cubicBoxVertices d n).card = (2 * n + 1) ^ d := by
  classical
  rw [cubicBoxVertices, Fintype.card_piFinset_const, Int.card_Icc]
  congr 1
  omega

/-! ### Open subgraphs of the cubic lattice -/

/-- The random open subgraph of the cubic lattice determined by the configuration `ω`. -/
def cubicOpenGraph (d : ℕ) (ω : EdgeConfiguration d) : SimpleGraph (Cubic d) :=
  SimpleGraph.fromEdgeSet
    {e | ∃ h : e ∈ (cubicGraph d).edgeSet, (⟨e, h⟩ : CubicEdge d) ∈ ω}

/-- Adjacency in `cubicOpenGraph` means cubic adjacency through an edge declared open by `ω`. -/
theorem cubicOpenGraph_adj {d : ℕ} {ω : EdgeConfiguration d} {x y : Cubic d} :
    (cubicOpenGraph d ω).Adj x y ↔
      ∃ h : (cubicGraph d).Adj x y,
        (⟨s(x, y), (SimpleGraph.mem_edgeSet (cubicGraph d)).mpr h⟩ : CubicEdge d) ∈ ω := by
  simp only [cubicOpenGraph, SimpleGraph.fromEdgeSet_adj, Set.mem_setOf_eq, ne_eq]
  constructor
  · rintro ⟨⟨h, hopen⟩, _hxy⟩
    exact ⟨(SimpleGraph.mem_edgeSet (cubicGraph d)).mp h, hopen⟩
  · rintro ⟨h, hopen⟩
    exact ⟨⟨(SimpleGraph.mem_edgeSet (cubicGraph d)).mpr h, hopen⟩, h.ne⟩

/-- The identity-on-vertices graph homomorphism from the open graph to the cubic lattice. -/
def cubicOpenGraphHom (d : ℕ) (ω : EdgeConfiguration d) :
    cubicOpenGraph d ω →g cubicGraph d where
  toFun := id
  map_rel' := fun h ↦ (cubicOpenGraph_adj.mp h).choose

/-- Mapping an open-graph walk to the cubic graph gives a walk whose edges are open in `ω`. -/
theorem walkIsOpen_map_cubicOpenGraphHom {d : ℕ} {ω : EdgeConfiguration d}
    {x y : Cubic d} (w : (cubicOpenGraph d ω).Walk x y) :
    walkIsOpen ω (w.map (cubicOpenGraphHom d ω)) := by
  induction w with
  | nil =>
      intro e he
      simp at he
  | @cons u v y huv p ih =>
      intro e he
      simp only [SimpleGraph.Walk.map_cons, SimpleGraph.Walk.edges_cons,
        List.mem_cons] at he
      rcases he with he | he
      · subst e
        simpa [cubicOpenGraphHom] using (cubicOpenGraph_adj.mp huv).choose_spec
      · exact ih e he

/-- A cubic-lattice walk all of whose edges are open can be regarded as a walk in the open
subgraph. -/
theorem nonempty_cubicOpenGraph_walk_of_walkIsOpen {d : ℕ} {ω : EdgeConfiguration d}
    {x y : Cubic d} (w : (cubicGraph d).Walk x y) (hopen : walkIsOpen ω w) :
    Nonempty ((cubicOpenGraph d ω).Walk x y) := by
  induction w with
  | nil =>
      exact ⟨SimpleGraph.Walk.nil⟩
  | @cons u v y huv p ih =>
      have hopenTail : walkIsOpen ω p := by
        intro e he
        exact hopen e (by simp [SimpleGraph.Walk.edges_cons, he])
      rcases ih hopenTail with ⟨q⟩
      have hopenHead :
          (⟨s(u, v), (SimpleGraph.mem_edgeSet (cubicGraph d)).mpr huv⟩ : CubicEdge d) ∈
            ω := by
        apply hopen
        simp [SimpleGraph.Walk.edges_cons]
      exact ⟨SimpleGraph.Walk.cons (cubicOpenGraph_adj.mpr ⟨huv, hopenHead⟩) q⟩

/-- Reachability in the random open graph is exactly the existence of an open cubic walk. -/
theorem cubicOpenGraph_reachable_iff {d : ℕ} {ω : EdgeConfiguration d}
    {x y : Cubic d} :
    (cubicOpenGraph d ω).Reachable x y ↔
      ∃ w : (cubicGraph d).Walk x y, walkIsOpen ω w := by
  constructor
  · rintro ⟨w⟩
    exact ⟨w.map (cubicOpenGraphHom d ω), walkIsOpen_map_cubicOpenGraphHom w⟩
  · rintro ⟨w, hopen⟩
    exact nonempty_cubicOpenGraph_walk_of_walkIsOpen w hopen

/-- The support of a connected component of the open graph is the production open-cluster set
`cubicOpenClusterFrom`. -/
theorem cubicOpenGraph_component_supp {d : ℕ} {ω : EdgeConfiguration d} (x : Cubic d) :
    ((cubicOpenGraph d ω).connectedComponentMk x).supp =
      cubicOpenClusterFrom d ω x := by
  ext y
  rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
  constructor
  · intro h
    have hyx : (cubicOpenGraph d ω).Reachable y x :=
      SimpleGraph.ConnectedComponent.eq.mp h
    exact cubicOpenGraph_reachable_iff.mp hyx.symm
  · intro h
    have hxy : (cubicOpenGraph d ω).Reachable x y :=
      cubicOpenGraph_reachable_iff.mpr h
    exact SimpleGraph.ConnectedComponent.eq.mpr hxy.symm

/-- Component size in the open graph agrees with the cardinality of the production open cluster. -/
theorem componentSize_cubicOpenGraph {d : ℕ} {ω : EdgeConfiguration d} (x : Cubic d) :
    componentSize (cubicOpenGraph d ω) x = (cubicOpenClusterFrom d ω x).ncard := by
  rw [componentSize, Nat.card_coe_set_eq, cubicOpenGraph_component_supp]

/-- The number of open clusters per vertex, Grimmett's `κ(p)` from (4.1), defined as the
expectation of the reciprocal size of the open cluster at the origin. -/
noncomputable def openClustersPerVertex (d : ℕ) (p : I) : ℝ :=
  ∫ ω, componentWeight (cubicOpenGraph d ω) (cubicOrigin : Cubic d) ∂
    bernoulliBondMeasure d p

/-- The integrand defining `openClustersPerVertex` is literally `|C|⁻¹`, with the convention
that an infinite cluster contributes zero. -/
theorem openClustersPerVertex_eq_integral_inv_ncard (d : ℕ) (p : I) :
    openClustersPerVertex d p =
      ∫ ω, 1 / ((cubicOpenCluster d ω).ncard : ℝ) ∂bernoulliBondMeasure d p := by
  unfold openClustersPerVertex componentWeight cubicOpenCluster
  simp_rw [componentSize_cubicOpenGraph]

/-- The finite-volume number of open clusters in an arbitrary finite cubic-lattice region. -/
noncomputable def cubicOpenClusterCountIn (d : ℕ) (B : Finset (Cubic d))
    (ω : EdgeConfiguration d) : ℕ :=
  Nat.card ((cubicOpenGraph d ω).induce (B : Set (Cubic d))).ConnectedComponent

/-- The normalized finite-volume open-cluster count in a cubic-lattice region. -/
noncomputable def normalizedCubicOpenClusterCountIn (d : ℕ) (B : Finset (Cubic d))
    (ω : EdgeConfiguration d) : ℝ :=
  normalizedComponentCount (cubicOpenGraph d ω) B

/-- The almost-sure part of Grimmett's Theorem 4.2, with its two analytic/geometric inputs made
explicit. `haverage` is the box ergodic theorem (4.9), and `hupper` is the boundary correction
(4.11)–(4.12). The remaining squeeze argument is fully discharged here. -/
theorem normalizedCubicOpenClusterCountIn_tendsto_ae_of_ergodicAverage
    (d : ℕ) (p : I) (B : ℕ → Finset (Cubic d)) (boundaryError : ℕ → ℝ)
    (haverage : ∀ᵐ ω ∂bernoulliBondMeasure d p,
      Tendsto (fun n ↦ componentWeightAverage (cubicOpenGraph d ω) (B n)) atTop
        (nhds (openClustersPerVertex d p)))
    (hboundary : Tendsto boundaryError atTop (nhds 0))
    (hupper : ∀ᵐ ω ∂bernoulliBondMeasure d p, ∀ n,
      normalizedCubicOpenClusterCountIn d (B n) ω ≤
        componentWeightAverage (cubicOpenGraph d ω) (B n) + boundaryError n) :
    ∀ᵐ ω ∂bernoulliBondMeasure d p,
      Tendsto (fun n ↦ normalizedCubicOpenClusterCountIn d (B n) ω) atTop
        (nhds (openClustersPerVertex d p)) := by
  filter_upwards [haverage, hupper] with ω havg hupp
  exact normalizedComponentCount_tendsto_of_sandwich
    (cubicOpenGraph d ω) B boundaryError (openClustersPerVertex d p) havg hboundary hupp

end

end Percolation
