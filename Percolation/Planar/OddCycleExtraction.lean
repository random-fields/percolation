import Percolation.Planar.AlternatingPaths
import Percolation.Planar.Peierls

/-!
# Extracting an odd-index cycle from a closed square walk

The union of several glued crossings naturally gives a closed walk, which may repeat edges and
vertices.  This file takes the mod-two edge support of that walk.  Its degree is even at every
vertex, so the finite even-graph cycle-selection theorem extracts a simple cycle carrying odd
horizontal-ray parity.
-/

namespace SimpleGraph

universe u

variable {V : Type u} [DecidableEq V] {G : SimpleGraph V}

/-- The incidence count of an arbitrary walk has the usual endpoint parity.  Unlike the
`IsTrail` version in Mathlib, repetitions are allowed. -/
theorem Walk.even_countP_edges_iff' {u v : V} (p : G.Walk u v) (x : V) :
    Even (p.edges.countP fun e ↦ x ∈ e) ↔ u ≠ v → x ≠ u ∧ x ≠ v := by
  induction p with
  | nil => simp
  | cons huv p ih =>
      simp only [List.countP_cons, Walk.edges_cons, Sym2.mem_iff]
      split_ifs with h
      · rw [decide_eq_true_eq] at h
        obtain (rfl | rfl) := h
        · rw [Nat.even_add_one, ih]
          simp only [huv.ne, imp_false, Ne, not_false_eq_true, true_and, not_forall,
            Classical.not_not, exists_prop, not_true, false_and,
            and_iff_right_iff_imp]
          rintro rfl rfl
          exact G.loopless.irrefl _ huv
        · have := huv.ne
          grind
      · grind

end SimpleGraph

namespace Percolation

open scoped BigOperators

/-- Edges used an odd number of times by a walk. -/
noncomputable def walkOddMultiplicityEdges {u v : SquareVertex}
    (w : squareGraph.Walk u v) : Finset (Sym2 SquareVertex) :=
  w.edges.toFinset.filter fun e ↦ Odd (w.edges.count e)

private theorem walkOddMultiplicityEdges_subset_edges {u v : SquareVertex}
    (w : squareGraph.Walk u v) :
    ∀ e ∈ walkOddMultiplicityEdges w, e ∈ w.edges := by
  intro e he
  exact List.mem_toFinset.mp (Finset.mem_filter.mp he).1

@[reducible]
private noncomputable def walkOddMultiplicityGraphLocallyFinite {u v : SquareVertex}
    (w : squareGraph.Walk u v) :
    (SimpleGraph.fromEdgeSet (walkOddMultiplicityEdges w : Set (Sym2 SquareVertex))).LocallyFinite := by
  classical
  let E := walkOddMultiplicityEdges w
  let H : SimpleGraph SquareVertex := SimpleGraph.fromEdgeSet (E : Set (Sym2 SquareVertex))
  intro x
  let embed : H.neighborSet x ↪ E :=
    { toFun := fun y ↦ ⟨s(x, (y : SquareVertex)), by
          have hy := y.property
          change s(x, (y : SquareVertex)) ∈ (E : Set (Sym2 SquareVertex)) ∧
            x ≠ (y : SquareVertex) at hy
          exact hy.1⟩
      inj' := by
        intro y z hyz
        apply Subtype.ext
        have hyz' : s(x, (y : SquareVertex)) = s(x, (z : SquareVertex)) :=
          congrArg Subtype.val hyz
        rw [Sym2.eq_iff] at hyz'
        rcases hyz' with ⟨_, hyz'⟩ | ⟨_, hyx⟩
        · exact hyz'
        · have hxy : H.Adj x (y : SquareVertex) := y.property
          exact False.elim (hxy.ne hyx.symm) }
  exact Fintype.ofInjective embed embed.injective

private theorem walkOddMultiplicityGraph_edgeSet_eq {u v : SquareVertex}
    (w : squareGraph.Walk u v) :
    (SimpleGraph.fromEdgeSet
      (walkOddMultiplicityEdges w : Set (Sym2 SquareVertex))).edgeSet =
        (walkOddMultiplicityEdges w : Set (Sym2 SquareVertex)) := by
  classical
  rw [SimpleGraph.edgeSet_fromEdgeSet]
  ext e
  constructor
  · exact fun he ↦ he.1
  · intro he
    exact ⟨he, squareGraph.not_isDiag_of_mem_edgeSet
      (w.edges_subset_edgeSet (walkOddMultiplicityEdges_subset_edges w e he))⟩

private theorem even_degree_walkOddMultiplicityGraph {x : SquareVertex}
    (w : squareGraph.Walk x x)
    [(SimpleGraph.fromEdgeSet
      (walkOddMultiplicityEdges w : Set (Sym2 SquareVertex))).LocallyFinite] :
    ∀ z, Even ((SimpleGraph.fromEdgeSet
      (walkOddMultiplicityEdges w : Set (Sym2 SquareVertex))).degree z) := by
  classical
  let E := walkOddMultiplicityEdges w
  let H : SimpleGraph SquareVertex := SimpleGraph.fromEdgeSet (E : Set (Sym2 SquareVertex))
  intro z
  change Even (H.degree z)
  have hinc : H.incidenceFinset z = E.filter fun e ↦ z ∈ e := by
    ext e
    rw [SimpleGraph.mem_incidenceFinset, Finset.mem_filter]
    change (e ∈ H.edgeSet ∧ z ∈ e) ↔ e ∈ E ∧ z ∈ e
    rw [show H.edgeSet = (E : Set (Sym2 SquareVertex)) by
      simpa [H, E] using walkOddMultiplicityGraph_edgeSet_eq w]
    simp
  rw [← SimpleGraph.card_incidenceFinset_eq_degree, hinc]
  have hraw : Even (w.edges.countP fun e ↦ z ∈ e) := by
    exact (w.even_countP_edges_iff' z).mpr (by simp)
  have hsum :
      (∑ e ∈ w.edges.toFinset with z ∈ e, w.edges.count e) =
        w.edges.countP fun e ↦ z ∈ e :=
    Finset.sum_filter_count_eq_countP (fun e : Sym2 SquareVertex ↦ z ∈ e) w.edges
  have hcard : Even ((w.edges.toFinset.filter fun e ↦ z ∈ e).filter
      fun e ↦ Odd (w.edges.count e)).card := by
    rw [← Finset.even_sum_iff_even_card_odd]
    rw [hsum]
    exact hraw
  simpa [E, walkOddMultiplicityEdges, Finset.filter_filter, and_comm,
    and_left_comm, and_assoc] using hcard

/-- Every closed square-lattice walk of odd face parity contains a simple cycle of odd face
parity.  The extracted cycle uses only edges and vertices of the original walk. -/
theorem exists_oddFaceParityCycle_of_closedWalk {x f : SquareVertex}
    (w : squareGraph.Walk x x) (hparity : closedSquareWalkFaceParity w f = 1) :
    ∃ y : SquareVertex, ∃ c : squareGraph.Walk y y,
      c.IsCycle ∧ c.edges ⊆ w.edges ∧ c.support ⊆ w.support ∧
        closedSquareWalkFaceParity c f = 1 := by
  classical
  let E := walkOddMultiplicityEdges w
  let H : SimpleGraph SquareVertex := SimpleGraph.fromEdgeSet (E : Set (Sym2 SquareVertex))
  letI : H.LocallyFinite := walkOddMultiplicityGraphLocallyFinite w
  have hHEdges : H.edgeSet = (E : Set (Sym2 SquareVertex)) := by
    simpa [H, E] using walkOddMultiplicityGraph_edgeSet_eq w
  have hfinite : H.support.Finite := by
    apply SimpleGraph.support_finite_of_edgeSet_finite
    rw [hHEdges]
    exact E.finite_toSet
  have hdeg : ∀ z, Even (H.degree z) := by
    simpa [H, E] using even_degree_walkOddMultiplicityGraph w
  let ray : Sym2 SquareVertex → Prop :=
    fun e ↦ squareEdgeCrossesFaceHorizontalRayBool f e = true
  let X : Finset (Sym2 SquareVertex) := E.filter ray
  have hcountOdd : Odd (w.edges.countP ray) := by
    rw [Nat.odd_iff]
    simpa [closedSquareWalkFaceParity, ray] using hparity
  have hsum :
      (∑ e ∈ w.edges.toFinset with ray e, w.edges.count e) = w.edges.countP ray :=
    Finset.sum_filter_count_eq_countP ray w.edges
  have hXodd : Odd X.card := by
    have hcard : Odd ((w.edges.toFinset.filter ray).filter
        fun e ↦ Odd (w.edges.count e)).card := by
      rw [← Finset.odd_sum_iff_odd_card_odd]
      rw [hsum]
      exact hcountOdd
    simpa [X, E, walkOddMultiplicityEdges, Finset.filter_filter, and_comm,
      and_left_comm, and_assoc] using hcard
  have hXedge : ∀ e ∈ X, e ∈ H.edgeSet := by
    intro e he
    rw [hHEdges]
    exact (Finset.mem_filter.mp he).1
  obtain ⟨y, cH, hcCycle, hcOdd⟩ :=
    SimpleGraph.exists_isCycle_odd_card_filter_of_odd_edge_finset
      H hfinite hdeg X hXedge hXodd
  have hHle : H ≤ squareGraph := by
    intro u v huv
    have heE : s(u, v) ∈ E := by
      have heH : s(u, v) ∈ H.edgeSet := by
        simpa [SimpleGraph.mem_edgeSet] using huv
      simpa only [hHEdges, Finset.mem_coe] using heH
    exact w.adj_of_mem_edges (walkOddMultiplicityEdges_subset_edges w _ heE)
  let c : squareGraph.Walk y y := cH.mapLe hHle
  have hcEdges : c.edges ⊆ w.edges := by
    intro e he
    have heH : e ∈ cH.edges := by simpa [c, SimpleGraph.Walk.edges_mapLe_eq_edges] using he
    have heHset : e ∈ H.edgeSet := cH.edges_subset_edgeSet heH
    rw [hHEdges] at heHset
    exact walkOddMultiplicityEdges_subset_edges w e heHset
  have hcSupport : c.support ⊆ w.support := by
    intro z hz
    have hzH : z ∈ cH.support := by
      simpa only [c, SimpleGraph.Walk.support_mapLe_eq_support] using hz
    have hzHsupport : z ∈ H.support :=
      SimpleGraph.mem_support_of_mem_walk_support cH
        (fun hnil ↦ hcCycle.ne_nil hnil.eq_nil) hzH
    rw [SimpleGraph.mem_support] at hzHsupport
    rcases hzHsupport with ⟨q, hzq⟩
    have heE : s(z, q) ∈ E := by
      have heH : s(z, q) ∈ H.edgeSet := by
        simpa [SimpleGraph.mem_edgeSet] using hzq
      simpa only [hHEdges, Finset.mem_coe] using heH
    exact w.fst_mem_support_of_mem_edges
      (walkOddMultiplicityEdges_subset_edges w _ heE)
  have hcRayFinset :
      X.filter (fun e ↦ e ∈ cH.edges.toFinset) = cH.edges.toFinset.filter ray := by
    ext e
    simp only [X, Finset.mem_filter]
    constructor
    · rintro ⟨⟨_heE, heRay⟩, heC⟩
      exact ⟨heC, heRay⟩
    · rintro ⟨heC, heRay⟩
      have heH : e ∈ cH.edges := List.mem_toFinset.mp heC
      have heE : e ∈ E := by
        have heHset : e ∈ H.edgeSet := cH.edges_subset_edgeSet heH
        simpa only [hHEdges, Finset.mem_coe] using heHset
      exact ⟨⟨heE, heRay⟩, heC⟩
  have hcCountOdd : Odd (cH.edges.countP ray) := by
    have hcCardOdd : Odd ((cH.edges.filter fun e ↦ decide (ray e)).toFinset.card) := by
      rw [List.toFinset_filter]
      simp only [decide_eq_true_eq]
      rw [← hcRayFinset]
      exact hcOdd
    rw [List.toFinset_card_of_nodup (hcCycle.isTrail.edges_nodup.filter _)] at hcCardOdd
    simpa [List.countP_eq_length_filter] using hcCardOdd
  have hcParity : closedSquareWalkFaceParity c f = 1 := by
    unfold closedSquareWalkFaceParity
    rw [show c.edges = cH.edges by simp [c, SimpleGraph.Walk.edges_mapLe_eq_edges]]
    rw [← Nat.odd_iff]
    simpa [ray] using hcCountOdd
  exact ⟨y, c, hcCycle.mapLe hHle, hcEdges, hcSupport, hcParity⟩

end Percolation
