import Percolation.Planar.RSWStoppedFresh

/-!
# Lowest-interface comparison for the stopped RSW exploration

This file isolates the finite parity comparison needed to identify the filled stopped interface
with the lowest crossing at a horizontal cut.  The first lemmas are deliberately stated for an
arbitrary normalized bottom--top walk: a dual face on the bottom row, at or to the right of the
walk's unique bottom endpoint, has zero horizontal-ray index with respect to that walk.
-/

namespace Percolation

open SimpleGraph
open MeasureTheory ProbabilityTheory
open scoped Sym2
open scoped unitInterval

noncomputable section

/-! ### Local degree of the filled outer interface -/

local instance instDecidablePredBRFilledReachedDualFace
    (n : ℕ) (R : Finset (BRLeftmostDualVertex n)) :
    DecidablePred (brReachedDualFace n (brFilledReachableHull n R)) :=
  Classical.decPred _

private theorem squareEdgeDualCrossingEquiv_symm_dualPositiveEdge_toEdge_local
    (d : DualSquarePositiveEdge) :
    squareEdgeDualCrossingEquiv.symm d.toEdge =
      (dualToPrimalCrossingPositiveEdge d).toEdge := by
  have horient : SquarePositiveEdge.edgeEquiv.symm d.toEdge = d := by
    apply SquarePositiveEdge.edgeEquiv.injective
    simp [SquarePositiveEdge.edgeEquiv_apply]
  simp [squareEdgeDualCrossingEquiv, squarePositiveEdgeDualCrossingEquiv,
    SquarePositiveEdge.edgeEquiv_apply, horient]

/-- A simple path uses at most two edges incident to any fixed vertex. -/
private theorem ncard_neighborSet_toSubgraph_le_two_of_isPath
    {V : Type*} {G : SimpleGraph V} {u v x : V}
    {p : G.Walk u v} (hp : p.IsPath) :
    (p.toSubgraph.neighborSet x).ncard ≤ 2 := by
  by_cases hx : x ∈ p.support
  · rw [SimpleGraph.Walk.mem_support_iff_exists_getVert] at hx
    obtain ⟨i, rfl, hi⟩ := hx
    by_cases hi0 : i = 0
    · subst i
      rw [p.getVert_zero]
      by_cases hnil : p.Nil
      · have hempty : p.toSubgraph.neighborSet u = ∅ := by
          ext y
          rw [SimpleGraph.Subgraph.mem_neighborSet,
            SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges,
            SimpleGraph.Walk.edges_eq_nil.mpr hnil]
          simp
        rw [hempty]
        simp
      · rw [hp.neighborSet_toSubgraph_startpoint hnil]
        simp
    · by_cases hilast : i = p.length
      · subst i
        rw [p.getVert_length]
        by_cases hnil : p.Nil
        · have hempty : p.toSubgraph.neighborSet v = ∅ := by
            ext y
            rw [SimpleGraph.Subgraph.mem_neighborSet,
              SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges,
              SimpleGraph.Walk.edges_eq_nil.mpr hnil]
            simp
          rw [hempty]
          simp
        · rw [hp.neighborSet_toSubgraph_endpoint hnil]
          simp
      · rw [hp.ncard_neighborSet_toSubgraph_internal_eq_two hi0 (by omega)]
  · have hempty : p.toSubgraph.neighborSet x = ∅ := by
      ext y
      constructor
      · intro hy
        exact (hx (SimpleGraph.Walk.mem_support_of_adj_toSubgraph hy)).elim
      · simp
    rw [hempty]
    simp

/-- Every side of a retained cell on the filled-hull cut crosses an edge of the selected
outer primal path. -/
private theorem filledHullCellBoundary_crossedPrimalEdge_mem_selectedWalk
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R)
    {z : DualSquareVertex} (hz : z ∈ brTruncatedBoundaryCells n)
    {d : DualSquarePositiveEdge}
    (hd : d ∈ squareCellBoundaryPositiveEdges
      (brReachedDualFace n (brFilledReachableHull n R)) z) :
    (dualToPrimalCrossingPositiveEdge d).toEdge ∈
      walkEdgeFinset (brSelectedPrimalWalk hn hR.filledHull) := by
  classical
  have hdCell : d ∈ squareCellPositiveEdges z :=
    (Finset.mem_filter.mp hd).1
  have hdFrame :=
    squareCellPositiveEdge_endpoints_mem_brLeftmostDualFaces hz hdCell
  let x : BRLeftmostDualVertex n := ⟨d.base, hdFrame.1⟩
  let y : BRLeftmostDualVertex n :=
    ⟨cubicStepFrom d.base (d.axis, true), hdFrame.2⟩
  have hxy : (brLeftmostDualGraph n).Adj x y := by
    rw [brLeftmostDualGraph_adj_iff]
    exact cubicGraph_adj_stepFrom d.base (d.axis, true)
  have hxHull : brReachedDualFace n (brFilledReachableHull n R) d.base ↔
      x ∈ brFilledReachableHull n R := by
    simpa [x] using
      (brReachedDualFace_subtype_iff
        (R := brFilledReachableHull n R) (z := x))
  have hyHull : brReachedDualFace n (brFilledReachableHull n R)
      (cubicStepFrom d.base (d.axis, true)) ↔
      y ∈ brFilledReachableHull n R := by
    simpa [y] using
      (brReachedDualFace_subtype_iff
        (R := brFilledReachableHull n R) (z := y))
  have hchange : ¬(x ∈ brFilledReachableHull n R ↔
      y ∈ brFilledReachableHull n R) := by
    simpa [squareCellBoundaryPositiveEdges, hxHull, hyHull] using
      (Finset.mem_filter.mp hd).2
  by_cases hx : x ∈ brFilledReachableHull n R
  · have hy : y ∉ brFilledReachableHull n R := by
      intro hy
      exact hchange ⟨fun _ ↦ hy, fun _ ↦ hx⟩
    have houter :=
      brFilledHullCutCrossedPrimalEdge_mem_selectedWalk hn hR hx hy hxy
    change squareEdgeDualCrossingEquiv.symm
        (brLeftmostDualEdgeEmbedding n
          ⟨s(x, y), (brLeftmostDualGraph n).mem_edgeSet.mpr hxy⟩) ∈
      walkEdgeFinset (brSelectedPrimalWalk hn hR.filledHull) at houter
    have hembed :
        brLeftmostDualEdgeEmbedding n
          ⟨s(x, y), (brLeftmostDualGraph n).mem_edgeSet.mpr hxy⟩ = d.toEdge := by
      apply Subtype.ext
      rfl
    rw [hembed,
      squareEdgeDualCrossingEquiv_symm_dualPositiveEdge_toEdge_local] at houter
    exact houter
  · have hy : y ∈ brFilledReachableHull n R := by
      by_contra hy
      exact hchange ⟨fun hx' ↦ (hx hx').elim, fun hy' ↦ (hy hy').elim⟩
    have houter :=
      brFilledHullCutCrossedPrimalEdge_mem_selectedWalk hn hR hy hx hxy.symm
    change squareEdgeDualCrossingEquiv.symm
        (brLeftmostDualEdgeEmbedding n
          ⟨s(y, x), (brLeftmostDualGraph n).mem_edgeSet.mpr hxy.symm⟩) ∈
      walkEdgeFinset (brSelectedPrimalWalk hn hR.filledHull) at houter
    have hembed :
        brLeftmostDualEdgeEmbedding n
          ⟨s(y, x), (brLeftmostDualGraph n).mem_edgeSet.mpr hxy.symm⟩ = d.toEdge := by
      apply Subtype.ext
      change s(y.1, x.1) = d.toEdge
      simp [x, y, SquarePositiveEdge.toEdge]
    rw [hembed,
      squareEdgeDualCrossingEquiv_symm_dualPositiveEdge_toEdge_local] at houter
    exact houter

/-- The cut of a filled stopped hull has no checkerboard cell inside the retained strip.  Four
cut sides would give four distinct selected-path edges at the cell's northeast primal corner,
contradicting simplicity of the selected path. -/
theorem card_filledHullCellBoundaryPositiveEdges_ne_four
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R)
    {z : DualSquareVertex} (hz : z ∈ brTruncatedBoundaryCells n) :
    (squareCellBoundaryPositiveEdges
      (brReachedDualFace n (brFilledReachableHull n R)) z).card ≠ 4 := by
  classical
  intro hfour
  let bottom : DualSquarePositiveEdge := ⟨z, (0 : Fin 2)⟩
  let se : DualSquareVertex := squareVertex (z 0 + 1) (z 1)
  let right : DualSquarePositiveEdge := ⟨se, (1 : Fin 2)⟩
  let nw : DualSquareVertex := squareVertex (z 0) (z 1 + 1)
  let top : DualSquarePositiveEdge := ⟨nw, (0 : Fin 2)⟩
  let left : DualSquarePositiveEdge := ⟨z, (1 : Fin 2)⟩
  have hsubset : squareCellBoundaryPositiveEdges
      (brReachedDualFace n (brFilledReachableHull n R)) z ⊆
      squareCellPositiveEdges z := by
    intro d hd
    exact (Finset.mem_filter.mp hd).1
  have hboundary : squareCellBoundaryPositiveEdges
      (brReachedDualFace n (brFilledReachableHull n R)) z =
      squareCellPositiveEdges z := by
    apply Finset.eq_of_subset_of_card_le hsubset
    rw [card_squareCellPositiveEdges_eq_four, hfour]
  have hbottom : bottom ∈ squareCellBoundaryPositiveEdges
      (brReachedDualFace n (brFilledReachableHull n R)) z := by
    rw [hboundary]
    simp [bottom, squareCellPositiveEdges, squareCellPositiveEdgeList]
  have hright : right ∈ squareCellBoundaryPositiveEdges
      (brReachedDualFace n (brFilledReachableHull n R)) z := by
    rw [hboundary]
    simp [right, se, squareCellPositiveEdges, squareCellPositiveEdgeList]
  have htop : top ∈ squareCellBoundaryPositiveEdges
      (brReachedDualFace n (brFilledReachableHull n R)) z := by
    rw [hboundary]
    simp [top, nw, squareCellPositiveEdges, squareCellPositiveEdgeList]
  have hleft : left ∈ squareCellBoundaryPositiveEdges
      (brReachedDualFace n (brFilledReachableHull n R)) z := by
    rw [hboundary]
    simp [left, squareCellPositiveEdges, squareCellPositiveEdgeList]
  let p := brSelectedPrimalWalk hn hR.filledHull
  have hbottomEdge :=
    filledHullCellBoundary_crossedPrimalEdge_mem_selectedWalk hn hR hz hbottom
  have hrightEdge :=
    filledHullCellBoundary_crossedPrimalEdge_mem_selectedWalk hn hR hz hright
  have htopEdge :=
    filledHullCellBoundary_crossedPrimalEdge_mem_selectedWalk hn hR hz htop
  have hleftEdge :=
    filledHullCellBoundary_crossedPrimalEdge_mem_selectedWalk hn hR hz hleft
  rw [mem_walkEdgeFinset_iff] at hbottomEdge hrightEdge htopEdge hleftEdge
  let c : SquareVertex := brPairingPrimalVertex z
  let bottomI : BRStoppedInterfaceEdge n (brFilledReachableHull n R) :=
    ⟨bottom, (Finset.mem_filter.mp hbottom).2⟩
  let rightI : BRStoppedInterfaceEdge n (brFilledReachableHull n R) :=
    ⟨right, (Finset.mem_filter.mp hright).2⟩
  let topI : BRStoppedInterfaceEdge n (brFilledReachableHull n R) :=
    ⟨top, (Finset.mem_filter.mp htop).2⟩
  let leftI : BRStoppedInterfaceEdge n (brFilledReachableHull n R) :=
    ⟨left, (Finset.mem_filter.mp hleft).2⟩
  have hcBottom : c ∈
      ((dualToPrimalCrossingPositiveEdge bottom).toEdge : Sym2 SquareVertex) := by
    simpa [c, bottomI, brStoppedInterfacePrimalPositiveEdge] using
      (brPairingPrimalVertex_mem_crossedPrimalEdge_of_incidentAt
        (d := bottomI) hbottom)
  have hcRight : c ∈
      ((dualToPrimalCrossingPositiveEdge right).toEdge : Sym2 SquareVertex) := by
    simpa [c, rightI, brStoppedInterfacePrimalPositiveEdge] using
      (brPairingPrimalVertex_mem_crossedPrimalEdge_of_incidentAt
        (d := rightI) hright)
  have hcTop : c ∈
      ((dualToPrimalCrossingPositiveEdge top).toEdge : Sym2 SquareVertex) := by
    simpa [c, topI, brStoppedInterfacePrimalPositiveEdge] using
      (brPairingPrimalVertex_mem_crossedPrimalEdge_of_incidentAt
        (d := topI) htop)
  have hcLeft : c ∈
      ((dualToPrimalCrossingPositiveEdge left).toEdge : Sym2 SquareVertex) := by
    simpa [c, leftI, brStoppedInterfacePrimalPositiveEdge] using
      (brPairingPrimalVertex_mem_crossedPrimalEdge_of_incidentAt
        (d := leftI) hleft)
  let south := Sym2.Mem.other hcBottom
  let east := Sym2.Mem.other hcRight
  let north := Sym2.Mem.other hcTop
  let west := Sym2.Mem.other hcLeft
  have hsouth : p.toSubgraph.Adj c south := by
    rw [SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges]
    rw [Sym2.other_spec hcBottom]
    exact hbottomEdge
  have heast : p.toSubgraph.Adj c east := by
    rw [SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges]
    rw [Sym2.other_spec hcRight]
    exact hrightEdge
  have hnorth : p.toSubgraph.Adj c north := by
    rw [SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges]
    rw [Sym2.other_spec hcTop]
    exact htopEdge
  have hwest : p.toSubgraph.Adj c west := by
    rw [SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges]
    rw [Sym2.other_spec hcLeft]
    exact hleftEdge
  have hsideNodup : [bottom, right, top, left].Nodup := by
    simpa only [bottom, right, top, left, se, nw,
      squareCellPositiveEdgeList] using
      (squareCellPositiveEdgeList_nodup z)
  have hother_ne {a b : DualSquarePositiveEdge}
      (hab : a ≠ b)
      (ha : c ∈ ((dualToPrimalCrossingPositiveEdge a).toEdge : Sym2 SquareVertex))
      (hb : c ∈ ((dualToPrimalCrossingPositiveEdge b).toEdge : Sym2 SquareVertex)) :
      Sym2.Mem.other ha ≠ Sym2.Mem.other hb := by
    intro hother
    apply hab
    have hprimal : dualToPrimalCrossingPositiveEdge a =
        dualToPrimalCrossingPositiveEdge b := by
      apply SquarePositiveEdge.toEdge_injective
      apply Subtype.ext
      rw [← Sym2.other_spec ha, ← Sym2.other_spec hb, hother]
    have hdual := congrArg primalToDualCrossingPositiveEdge hprimal
    simpa using hdual
  have hotherNodup : [south, east, north, west].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, not_or,
      List.not_mem_nil, List.nodup_nil, not_false_eq_true, and_true]
    simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, not_or,
      List.not_mem_nil, List.nodup_nil, not_false_eq_true, and_true] at hsideNodup
    rcases hsideNodup with
      ⟨⟨hbr, hbt, hbl⟩, ⟨⟨hrt, hrl⟩, htl⟩⟩
    exact ⟨
      ⟨hother_ne hbr hcBottom hcRight,
        hother_ne hbt hcBottom hcTop,
        hother_ne hbl hcBottom hcLeft⟩,
      ⟨⟨hother_ne hrt hcRight hcTop,
        hother_ne hrl hcRight hcLeft⟩,
        hother_ne htl hcTop hcLeft⟩⟩
  have hfourNeighbors : ({south, east, north, west} : Set SquareVertex) ⊆
      p.toSubgraph.neighborSet c := by
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl | rfl
    · exact hsouth
    · exact heast
    · exact hnorth
    · exact hwest
  have hfinite : (p.toSubgraph.neighborSet c).Finite :=
    SimpleGraph.Walk.finite_neighborSet_toSubgraph p
  have hfourLe := Set.ncard_le_ncard hfourNeighbors hfinite
  have hfourCard : ({south, east, north, west} : Set SquareVertex).ncard = 4 := by
    have hlistCard : [south, east, north, west].toFinset.card = 4 := by
      simpa using List.toFinset_card_of_nodup hotherNodup
    have hsetEq : ({south, east, north, west} : Set SquareVertex) =
        ([south, east, north, west].toFinset : Set SquareVertex) := by
      ext w
      simp
    rw [hsetEq, Set.ncard_coe_finset, hlistCard]
  have hdegree : (p.toSubgraph.neighborSet c).ncard ≤ 2 := by
    simpa [p] using ncard_neighborSet_toSubgraph_le_two_of_isPath
      (brSelectedPrimalWalk_isPath hn hR.filledHull) (x := c)
  rw [hfourCard] at hfourLe
  omega

/-- A boundary side's selected endpoint is the endpoint satisfying the defining predicate. -/
private theorem squareCellBoundaryTrueEndpoint_property_of_change
    (P : SquareVertex → Prop) [DecidablePred P]
    (b : SquarePositiveEdge)
    (hchange : ¬(P b.base ↔ P (cubicStepFrom b.base (b.axis, true)))) :
    P (squareCellBoundaryTrueEndpoint P b) := by
  by_cases hbase : P b.base
  · simpa [squareCellBoundaryTrueEndpoint, hbase]
  · have hstep : P (cubicStepFrom b.base (b.axis, true)) := by
      by_contra hnot
      exact hchange (iff_of_false hbase hnot)
    simpa [squareCellBoundaryTrueEndpoint, hbase] using hstep

/-- A boundary side's selected endpoint is the endpoint satisfying the defining predicate. -/
private theorem squareCellBoundaryTrueEndpoint_property
    (P : SquareVertex → Prop) [DecidablePred P]
    {z : DualSquareVertex} {b : SquarePositiveEdge}
    (hb : b ∈ squareCellBoundaryPositiveEdges P z) :
    P (squareCellBoundaryTrueEndpoint P b) := by
  exact squareCellBoundaryTrueEndpoint_property_of_change P b
    (Finset.mem_filter.mp hb).2

/-! The following four-element model keeps the local cell argument computational and prevents
the surrounding coordinate expressions from being duplicated across a large tactic case split. -/

/-- Adjacency in the cyclic ordering `southwest, southeast, northeast, northwest`. -/
private def fourCycleAdj (i j : Fin 4) : Prop :=
  (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 2) ∨
  (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 0) ∨
  (j = 0 ∧ i = 1) ∨ (j = 1 ∧ i = 2) ∨
  (j = 2 ∧ i = 3) ∨ (j = 3 ∧ i = 0)

private instance instDecidableFourCycleAdj : DecidableRel fourCycleAdj := by
  intro i j
  unfold fourCycleAdj
  infer_instance

private def fourSideBase : Fin 4 → Fin 4 := ![0, 1, 3, 0]

private def fourSideTip : Fin 4 → Fin 4 := ![1, 2, 2, 3]

private def fourSideToggle (v : Fin 4 → Bool) (i : Fin 4) : Bool :=
  decide (v (fourSideBase i) ≠ v (fourSideTip i))

private def fourSideTrueCorner (v : Fin 4 → Bool) (i : Fin 4) : Fin 4 :=
  if v (fourSideBase i) = true then fourSideBase i else fourSideTip i

/-- Exhaustive finite core of the local inside-corner connection. -/
private theorem fourCycle_trueCorner_connection :
    ∀ (a b c d : Bool) (i j : Fin 4),
      let v : Fin 4 → Bool := ![a, b, c, d]
      fourSideToggle v i = true → fourSideToggle v j = true →
      ¬(∀ k : Fin 4, fourSideToggle v k = true) →
      let x := fourSideTrueCorner v i
      let y := fourSideTrueCorner v j
      x = y ∨ fourCycleAdj x y ∨
        ∃ m, v m = true ∧ fourCycleAdj x m ∧ fourCycleAdj m y := by
  native_decide

/-- The four corners of a square cell in cyclic order. -/
private def squareCellIndexedCorner (z : DualSquareVertex) : Fin 4 → SquareVertex :=
  ![z, squareVertex (z 0 + 1) (z 1),
    squareVertex (z 0 + 1) (z 1 + 1), squareVertex (z 0) (z 1 + 1)]

/-- The four positively oriented cell sides in the matching cyclic order. -/
private def squareCellIndexedPositiveEdge
    (z : DualSquareVertex) : Fin 4 → SquarePositiveEdge :=
  ![⟨z, (0 : Fin 2)⟩,
    ⟨squareVertex (z 0 + 1) (z 1), (1 : Fin 2)⟩,
    ⟨squareVertex (z 0) (z 1 + 1), (0 : Fin 2)⟩,
    ⟨z, (1 : Fin 2)⟩]

private def squareCellTruth
    (P : SquareVertex → Prop) [DecidablePred P]
    (z : DualSquareVertex) (i : Fin 4) : Bool :=
  decide (P (squareCellIndexedCorner z i))

private theorem squareCellIndexedCorner_adj
    (z : DualSquareVertex) {i j : Fin 4} (hij : fourCycleAdj i j) :
    dualSquareGraph.Adj (squareCellIndexedCorner z i)
      (squareCellIndexedCorner z j) := by
  have h01 : dualSquareGraph.Adj z (squareVertex (z 0 + 1) (z 1)) := by
    convert cubicGraph_adj_stepFrom z ((0 : Fin 2), true) using 1
    ext k
    fin_cases k <;> simp [cubicStepFrom, cubicDirectionIncrement]
  have h12 : dualSquareGraph.Adj (squareVertex (z 0 + 1) (z 1))
      (squareVertex (z 0 + 1) (z 1 + 1)) := by
    convert cubicGraph_adj_stepFrom (squareVertex (z 0 + 1) (z 1))
      ((1 : Fin 2), true) using 1
    ext k
    fin_cases k <;> simp [cubicStepFrom, cubicDirectionIncrement]
  have h10 : dualSquareGraph.Adj (squareVertex (z 0 + 1) (z 1)) z := h01.symm
  have h21 : dualSquareGraph.Adj (squareVertex (z 0 + 1) (z 1 + 1))
      (squareVertex (z 0 + 1) (z 1)) := h12.symm
  have h32 : dualSquareGraph.Adj (squareVertex (z 0) (z 1 + 1))
      (squareVertex (z 0 + 1) (z 1 + 1)) := by
    convert cubicGraph_adj_stepFrom (squareVertex (z 0) (z 1 + 1))
      ((0 : Fin 2), true) using 1
    ext k
    fin_cases k <;> simp [cubicStepFrom, cubicDirectionIncrement]
  have h23 : dualSquareGraph.Adj (squareVertex (z 0 + 1) (z 1 + 1))
      (squareVertex (z 0) (z 1 + 1)) := h32.symm
  have h03 : dualSquareGraph.Adj z (squareVertex (z 0) (z 1 + 1)) := by
    convert cubicGraph_adj_stepFrom z ((1 : Fin 2), true) using 1
    ext k
    fin_cases k <;> simp [cubicStepFrom, cubicDirectionIncrement]
  have h30 : dualSquareGraph.Adj (squareVertex (z 0) (z 1 + 1)) z := h03.symm
  fin_cases i <;> fin_cases j <;>
    simp_all [fourCycleAdj, squareCellIndexedCorner]

private theorem squareCellIndexedPositiveEdge_mem
    (z : DualSquareVertex) (i : Fin 4) :
    squareCellIndexedPositiveEdge z i ∈ squareCellPositiveEdges z := by
  fin_cases i <;>
    simp [squareCellIndexedPositiveEdge, squareCellPositiveEdges,
      squareCellPositiveEdgeList]

private theorem exists_squareCellIndexedPositiveEdge_eq_of_mem
    {z : DualSquareVertex} {b : SquarePositiveEdge}
    (hb : b ∈ squareCellPositiveEdges z) :
    ∃ i : Fin 4, squareCellIndexedPositiveEdge z i = b := by
  simp [squareCellPositiveEdges, squareCellPositiveEdgeList] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩

private theorem squareCellIndexedPositiveEdge_step
    (z : DualSquareVertex) (i : Fin 4) :
    cubicStepFrom (squareCellIndexedPositiveEdge z i).base
        ((squareCellIndexedPositiveEdge z i).axis, true) =
      squareCellIndexedCorner z (fourSideTip i) := by
  fin_cases i <;> ext k <;> fin_cases k <;>
    simp [squareCellIndexedPositiveEdge, squareCellIndexedCorner, fourSideTip,
      cubicStepFrom, cubicDirectionIncrement]

private theorem squareCellIndexedPositiveEdge_base
    (z : DualSquareVertex) (i : Fin 4) :
    (squareCellIndexedPositiveEdge z i).base =
      squareCellIndexedCorner z (fourSideBase i) := by
  fin_cases i <;>
    simp [squareCellIndexedPositiveEdge, squareCellIndexedCorner, fourSideBase]

private theorem squareCellIndexedPositiveEdge_mem_boundary_iff
    (P : SquareVertex → Prop) [DecidablePred P]
    (z : DualSquareVertex) (i : Fin 4) :
    squareCellIndexedPositiveEdge z i ∈ squareCellBoundaryPositiveEdges P z ↔
      fourSideToggle (squareCellTruth P z) i = true := by
  rw [squareCellBoundaryPositiveEdges, Finset.mem_filter]
  rw [squareCellIndexedPositiveEdge_step, squareCellIndexedPositiveEdge_base]
  simp only [squareCellIndexedPositiveEdge_mem, true_and]
  simp [fourSideToggle, squareCellTruth]

private theorem squareCellBoundaryTrueEndpoint_indexed
    (P : SquareVertex → Prop) [DecidablePred P]
    (z : DualSquareVertex) (i : Fin 4) :
    squareCellBoundaryTrueEndpoint P (squareCellIndexedPositiveEdge z i) =
      squareCellIndexedCorner z
        (fourSideTrueCorner (squareCellTruth P z) i) := by
  rw [squareCellBoundaryTrueEndpoint, squareCellIndexedPositiveEdge_step,
    squareCellIndexedPositiveEdge_base]
  by_cases h : P (squareCellIndexedCorner z (fourSideBase i)) <;>
    simp [fourSideTrueCorner, squareCellTruth, h]

private theorem squareCellIndexedCorner_coordinates
    (z : DualSquareVertex) (i : Fin 4) :
    z 0 ≤ squareCellIndexedCorner z i 0 ∧
      squareCellIndexedCorner z i 0 ≤ z 0 + 1 ∧
      z 1 ≤ squareCellIndexedCorner z i 1 ∧
      squareCellIndexedCorner z i 1 ≤ z 1 + 1 := by
  fin_cases i <;> simp [squareCellIndexedCorner, squareVertex]

private theorem squareCellBoundaryTrueEndpoint_coordinates
    (P : SquareVertex → Prop) [DecidablePred P]
    {z : DualSquareVertex} {b : SquarePositiveEdge}
    (hb : b ∈ squareCellPositiveEdges z) :
    z 0 ≤ squareCellBoundaryTrueEndpoint P b 0 ∧
      squareCellBoundaryTrueEndpoint P b 0 ≤ z 0 + 1 ∧
      z 1 ≤ squareCellBoundaryTrueEndpoint P b 1 ∧
      squareCellBoundaryTrueEndpoint P b 1 ≤ z 1 + 1 := by
  rcases exists_squareCellIndexedPositiveEdge_eq_of_mem hb with ⟨i, rfl⟩
  rw [squareCellBoundaryTrueEndpoint_indexed]
  exact squareCellIndexedCorner_coordinates z _

/-- The selected endpoint of a boundary side is one of the two endpoints of that side. -/
private theorem squareCellBoundaryTrueEndpoint_mem_toEdge
    (P : SquareVertex → Prop) [DecidablePred P]
    (d : SquarePositiveEdge) :
    squareCellBoundaryTrueEndpoint P d ∈
      (d.toEdge : Sym2 SquareVertex) := by
  by_cases h : P d.base <;>
    simp [squareCellBoundaryTrueEndpoint, SquarePositiveEdge.toEdge, h]

/-- If a retained dual side crosses the vertical primal bond from `(x,y)` to `(x,y+1)`,
its selected endpoint lies on the dual horizontal bond from `(x-1,y)` to `(x,y)`. -/
private theorem squareCellBoundaryTrueEndpoint_crossedVertical_coordinates
    (P : SquareVertex → Prop) [DecidablePred P]
    (d : DualSquarePositiveEdge) {x y : ℤ}
    (hcross : ((dualToPrimalCrossingPositiveEdge d).toEdge : Sym2 SquareVertex) =
      s(squareVertex x (y + 1), squareVertex x y)) :
    let f := squareCellBoundaryTrueEndpoint P d
    f 1 = y ∧ x - 1 ≤ f 0 ∧ f 0 ≤ x := by
  dsimp only
  let e : SquarePositiveEdge := ⟨squareVertex x y, (1 : Fin 2)⟩
  have hedge : (dualToPrimalCrossingPositiveEdge d).toEdge = e.toEdge := by
    apply Subtype.ext
    have hecoe : (e.toEdge : Sym2 SquareVertex) =
        s(squareVertex x (y + 1), squareVertex x y) := by
      change s(squareVertex x y,
          cubicStepFrom (squareVertex x y) ((1 : Fin 2), true)) =
        s(squareVertex x (y + 1), squareVertex x y)
      have hstep : cubicStepFrom (squareVertex x y) ((1 : Fin 2), true) =
          squareVertex x (y + 1) := by
        ext i
        fin_cases i <;>
          simp [cubicStepFrom, cubicDirectionIncrement, squareVertex]
      rw [hstep]
      exact Sym2.eq_swap
    exact hcross.trans hecoe.symm
  have hpositive : dualToPrimalCrossingPositiveEdge d = e :=
    SquarePositiveEdge.toEdge_injective hedge
  have hd : d = primalToDualCrossingPositiveEdge e := by
    rw [← hpositive]
    exact (primalToDual_dualToPrimalCrossingPositiveEdge d).symm
  have hf := squareCellBoundaryTrueEndpoint_mem_toEdge P d
  rw [hd] at hf ⊢
  simp only [SquarePositiveEdge.toEdge_coe, Sym2.mem_iff] at hf
  rcases hf with hf | hf
  · rw [hf]
    simp [primalToDualCrossingPositiveEdge, e, squarePerp,
      cubicStepFrom, cubicDirectionIncrement, squareVertex]
  · rw [hf]
    simp [primalToDualCrossingPositiveEdge, e, squarePerp,
      cubicStepFrom, cubicDirectionIncrement, squareVertex]

/-- In a non-checkerboard cell, two true boundary endpoints are equal, adjacent, or joined by
two square steps through another true corner of the same cell. -/
theorem squareCellBoundaryTrueEndpoint_local_connection
    (P : SquareVertex → Prop) [DecidablePred P]
    {z : DualSquareVertex} {b d : SquarePositiveEdge}
    (hb : b ∈ squareCellBoundaryPositiveEdges P z)
    (hd : d ∈ squareCellBoundaryPositiveEdges P z)
    (hfour : (squareCellBoundaryPositiveEdges P z).card ≠ 4) :
    let x := squareCellBoundaryTrueEndpoint P b
    let y := squareCellBoundaryTrueEndpoint P d
    x = y ∨ dualSquareGraph.Adj x y ∨
      ∃ m, P m ∧ dualSquareGraph.Adj x m ∧ dualSquareGraph.Adj m y ∧
        z 0 ≤ m 0 ∧ m 0 ≤ z 0 + 1 ∧ z 1 ≤ m 1 ∧ m 1 ≤ z 1 + 1 := by
  classical
  dsimp only
  rcases exists_squareCellIndexedPositiveEdge_eq_of_mem
      (Finset.mem_of_mem_filter b hb) with ⟨i, hi⟩
  rcases exists_squareCellIndexedPositiveEdge_eq_of_mem
      (Finset.mem_of_mem_filter d hd) with ⟨j, hj⟩
  subst b
  subst d
  let v : Fin 4 → Bool := squareCellTruth P z
  have hiToggle : fourSideToggle v i = true := by
    exact (squareCellIndexedPositiveEdge_mem_boundary_iff P z i).mp hb
  have hjToggle : fourSideToggle v j = true := by
    exact (squareCellIndexedPositiveEdge_mem_boundary_iff P z j).mp hd
  have hnotAll : ¬(∀ k : Fin 4, fourSideToggle v k = true) := by
    intro hall
    apply hfour
    have hboundary : squareCellBoundaryPositiveEdges P z =
        squareCellPositiveEdges z := by
      apply Finset.Subset.antisymm
      · exact Finset.filter_subset _ _
      · intro e he
        rcases exists_squareCellIndexedPositiveEdge_eq_of_mem he with ⟨k, rfl⟩
        exact (squareCellIndexedPositiveEdge_mem_boundary_iff P z k).mpr (hall k)
    rw [hboundary, card_squareCellPositiveEdges_eq_four]
  have hvArray : (![v 0, v 1, v 2, v 3] : Fin 4 → Bool) = v := by
    funext k
    fin_cases k <;> rfl
  have hfinite := fourCycle_trueCorner_connection
    (v 0) (v 1) (v 2) (v 3) i j
  rw [hvArray] at hfinite
  rcases hfinite hiToggle hjToggle hnotAll with hxy | hxy | ⟨m, hm, hxm, hmy⟩
  · left
    simpa [squareCellBoundaryTrueEndpoint_indexed] using
      congrArg (squareCellIndexedCorner z) hxy
  · right
    left
    simpa [squareCellBoundaryTrueEndpoint_indexed] using
      squareCellIndexedCorner_adj z hxy
  · right
    right
    refine ⟨squareCellIndexedCorner z m, ?_, ?_, ?_,
      squareCellIndexedCorner_coordinates z m⟩
    · simpa [v, squareCellTruth] using hm
    · simpa [squareCellBoundaryTrueEndpoint_indexed] using
        squareCellIndexedCorner_adj z hxm
    · simpa [squareCellBoundaryTrueEndpoint_indexed] using
        squareCellIndexedCorner_adj z hmy

/-- The true endpoints of two sides of a non-checkerboard boundary cell are joined inside the
predicate by a dual-square walk of length at most two. -/
theorem exists_squareCellBoundaryTrueEndpoint_walk
    (P : SquareVertex → Prop) [DecidablePred P]
    {z : DualSquareVertex} {b d : SquarePositiveEdge}
    (hb : b ∈ squareCellBoundaryPositiveEdges P z)
    (hd : d ∈ squareCellBoundaryPositiveEdges P z)
    (hfour : (squareCellBoundaryPositiveEdges P z).card ≠ 4) :
    ∃ q : dualSquareGraph.Walk
        (squareCellBoundaryTrueEndpoint P b)
        (squareCellBoundaryTrueEndpoint P d),
      q.length ≤ 2 ∧ (∀ x ∈ q.support, P x) ∧
        ∀ x ∈ q.support,
          z 0 ≤ x 0 ∧ x 0 ≤ z 0 + 1 ∧ z 1 ≤ x 1 ∧ x 1 ≤ z 1 + 1 := by
  have hx := squareCellBoundaryTrueEndpoint_property P hb
  have hy := squareCellBoundaryTrueEndpoint_property P hd
  have hxCoords := squareCellBoundaryTrueEndpoint_coordinates P
    (Finset.mem_of_mem_filter b hb)
  have hyCoords := squareCellBoundaryTrueEndpoint_coordinates P
    (Finset.mem_of_mem_filter d hd)
  rcases squareCellBoundaryTrueEndpoint_local_connection P hb hd hfour with
    hxy | hxy | ⟨m, hm, hxm, hmy, hmCoords⟩
  · let q := (SimpleGraph.Walk.nil : dualSquareGraph.Walk
        (squareCellBoundaryTrueEndpoint P b)
        (squareCellBoundaryTrueEndpoint P b)).copy rfl hxy
    refine ⟨q, by simp [q], ?_, ?_⟩
    · intro w hw
      have hwEq : w = squareCellBoundaryTrueEndpoint P b := by
        simpa [q] using hw
      exact hwEq ▸ hx
    · intro w hw
      have hwEq : w = squareCellBoundaryTrueEndpoint P b := by
        simpa [q] using hw
      exact hwEq ▸ hxCoords
  · refine ⟨.cons hxy .nil, by simp, ?_, ?_⟩
    · intro w hw
      simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
        List.mem_cons, List.not_mem_nil, or_false] at hw
      exact hw.elim (fun h ↦ h ▸ hx) (fun h ↦ h ▸ hy)
    · intro w hw
      simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
        List.mem_cons, List.not_mem_nil, or_false] at hw
      exact hw.elim (fun h ↦ h ▸ hxCoords) (fun h ↦ h ▸ hyCoords)
  · refine ⟨.cons hxm (.cons hmy .nil), by simp, ?_, ?_⟩
    · intro w hw
      simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
        List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with h | h | h
      · exact h ▸ hx
      · exact h ▸ hm
      · exact h ▸ hy
    · intro w hw
      simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
        List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with h | h | h
      · exact h ▸ hxCoords
      · exact h ▸ hmCoords
      · exact h ▸ hyCoords

/-! ### Lifting a primal interface path to its filled side -/

/-- The dual-coordinate cell whose northeast primal corner is `v`. -/
private def brCellAtPrimalVertex (v : SquareVertex) : DualSquareVertex :=
  squareVertex (v 0 - 1) (v 1 - 1)

@[simp]
private theorem brPairingPrimalVertex_brCellAtPrimalVertex (v : SquareVertex) :
    brPairingPrimalVertex (brCellAtPrimalVertex v) = v := by
  ext i
  fin_cases i <;> simp [brPairingPrimalVertex, brCellAtPrimalVertex, squareVertex]

/-- If a primal positive edge contains `v`, its crossed dual side is incident to the cell whose
northeast primal corner is `v`. -/
private theorem primalToDualCrossingPositiveEdge_mem_cellAt_of_mem
    (a : SquarePositiveEdge) {v : SquareVertex}
    (hv : v ∈ (a.toEdge : Sym2 SquareVertex)) :
    primalToDualCrossingPositiveEdge a ∈
      squareCellPositiveEdges (brCellAtPrimalVertex v) := by
  rcases a with ⟨base, axis⟩
  fin_cases axis
  · simp only [SquarePositiveEdge.toEdge, Sym2.mem_iff] at hv
    rcases hv with rfl | rfl
    · simp [primalToDualCrossingPositiveEdge, brCellAtPrimalVertex,
        squareCellPositiveEdges, squareCellPositiveEdgeList, squarePerp,
        cubicStepFrom, cubicDirectionIncrement, squareVertex]
      left
      ext i
      fin_cases i <;> simp [squareVertex] <;> omega
    · simp [primalToDualCrossingPositiveEdge, brCellAtPrimalVertex,
        squareCellPositiveEdges, squareCellPositiveEdgeList, squarePerp,
        cubicStepFrom, cubicDirectionIncrement, squareVertex]
      right
      ext i
      fin_cases i <;> simp [squareVertex] <;> omega
  · simp only [SquarePositiveEdge.toEdge, Sym2.mem_iff] at hv
    rcases hv with rfl | rfl
    · simp [primalToDualCrossingPositiveEdge, brCellAtPrimalVertex,
        squareCellPositiveEdges, squareCellPositiveEdgeList, squarePerp,
        cubicStepFrom, cubicDirectionIncrement, squareVertex]
      right
      ext i
      fin_cases i <;> simp [squareVertex] <;> omega
    · simp [primalToDualCrossingPositiveEdge, brCellAtPrimalVertex,
        squareCellPositiveEdges, squareCellPositiveEdgeList, squarePerp,
        cubicStepFrom, cubicDirectionIncrement, squareVertex]
      left
      ext i
      fin_cases i <;> simp [squareVertex] <;> omega

/-- Upper-half vertices of the selected square interface have non-checkerboard filled-hull
cells.  Interior vertices use the simple-path degree obstruction; at height `n`, the two top
corners lie outside the exploration frame and hence have the same (false) hull value. -/
theorem card_filledHullCellAtUpperVertex_ne_four
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R)
    {v : SquareVertex}
    (hv : 0 ≤ v 0 ∧ v 0 ≤ 2 * (n : ℤ) ∧ 0 ≤ v 1 ∧ v 1 ≤ (n : ℤ)) :
    (squareCellBoundaryPositiveEdges
      (brReachedDualFace n (brFilledReachableHull n R))
      (brCellAtPrimalVertex v)).card ≠ 4 := by
  classical
  by_cases hvTop : v 1 = (n : ℤ)
  · intro hfour
    let z := brCellAtPrimalVertex v
    let nw : DualSquareVertex := squareVertex (z 0) (z 1 + 1)
    let top : DualSquarePositiveEdge := ⟨nw, (0 : Fin 2)⟩
    have hsubset : squareCellBoundaryPositiveEdges
        (brReachedDualFace n (brFilledReachableHull n R)) z ⊆
        squareCellPositiveEdges z := Finset.filter_subset _ _
    have hboundary : squareCellBoundaryPositiveEdges
        (brReachedDualFace n (brFilledReachableHull n R)) z =
        squareCellPositiveEdges z := by
      apply Finset.eq_of_subset_of_card_le hsubset
      rw [card_squareCellPositiveEdges_eq_four, hfour]
    have htop : top ∈ squareCellBoundaryPositiveEdges
        (brReachedDualFace n (brFilledReachableHull n R)) z := by
      rw [hboundary]
      simp [top, nw, squareCellPositiveEdges, squareCellPositiveEdgeList]
    have hnwOne : nw 1 = (n : ℤ) := by
      simp [nw, z, brCellAtPrimalVertex, squareVertex, hvTop]
    have hneOne : cubicStepFrom nw ((0 : Fin 2), true) 1 = (n : ℤ) := by
      simp [cubicStepFrom, cubicDirectionIncrement, hnwOne]
    have hnwOutside : ¬ brReachedDualFace n (brFilledReachableHull n R) nw := by
      intro hnwHull
      have hnwFrame := brReachedFaceCoordinates_subset_brLeftmostDualFaces hnwHull
      have hnwCoords := mem_brLeftmostDualFaces_iff.mp hnwFrame
      omega
    have hneOutside : ¬ brReachedDualFace n (brFilledReachableHull n R)
        (cubicStepFrom nw ((0 : Fin 2), true)) := by
      intro hneHull
      have hneFrame := brReachedFaceCoordinates_subset_brLeftmostDualFaces hneHull
      have hneCoords := mem_brLeftmostDualFaces_iff.mp hneFrame
      omega
    have hchange := (Finset.mem_filter.mp htop).2
    exact hchange (iff_of_false hnwOutside hneOutside)
  · apply card_filledHullCellBoundaryPositiveEdges_ne_four hn hR
    rw [mem_brTruncatedBoundaryCells_iff]
    simp only [brCellAtPrimalVertex, squareVertex]
    omega

/-- A nonempty upper-half primal walk carried by the truncated filled interface lifts to a
dual-square walk along the filled side.  Its endpoints are the filled endpoints of the first
and last crossed sides of the primal walk. -/
private theorem exists_filledSideWalk_of_primalWalk
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R)
    {x y : SquareVertex} (w : squareGraph.Walk x y)
    (hnil : ¬w.Nil)
    (hpath : w.IsPath)
    (hzero : ∀ v ∈ w.support, v 1 = 0 → v = y)
    (hw : walkEdgeFinset w ⊆
      brTruncatedInterfacePrimalEdges n (brFilledReachableHull n R))
    (hcoords : ∀ v ∈ w.support,
      0 ≤ v 0 ∧ v 0 ≤ 2 * (n : ℤ) ∧ 0 ≤ v 1 ∧ v 1 ≤ (n : ℤ)) :
    ∃ d e : BRTruncatedInterfaceEdge n (brFilledReachableHull n R),
      (brTruncatedInterfacePrimalEdge d : Sym2 SquareVertex) = s(x, w.snd) ∧
      (brTruncatedInterfacePrimalEdge e : Sym2 SquareVertex) = s(w.penultimate, y) ∧
      ∃ q : dualSquareGraph.Walk
          (squareCellBoundaryTrueEndpoint
            (brReachedDualFace n (brFilledReachableHull n R)) d.1)
          (squareCellBoundaryTrueEndpoint
            (brReachedDualFace n (brFilledReachableHull n R)) e.1),
        ∀ v ∈ q.support,
          brReachedDualFace n (brFilledReachableHull n R) v ∧ 0 ≤ v 1 := by
  classical
  induction w with
  | nil => exact (hnil .nil).elim
  | @cons x u y hxu tail ih =>
      let headEdge : SquareEdge :=
        ⟨s(x, u), squareGraph.mem_edgeSet.mpr hxu⟩
      have hheadWalk : headEdge ∈ walkEdgeFinset (.cons hxu tail) := by
        rw [mem_walkEdgeFinset_iff]
        simp [headEdge]
      have hheadInterface := hw hheadWalk
      rcases mem_brTruncatedInterfacePrimalEdges_iff.mp hheadInterface with
        ⟨d, hdEdge⟩
      have hdUnderlying :
          (brTruncatedInterfacePrimalEdge d : Sym2 SquareVertex) = s(x, u) := by
        exact congrArg Subtype.val hdEdge
      cases tail with
      | nil =>
          refine ⟨d, d, by simpa using hdUnderlying, by simpa using hdUnderlying, ?_⟩
          let q : dualSquareGraph.Walk
              (squareCellBoundaryTrueEndpoint
                (brReachedDualFace n (brFilledReachableHull n R)) d.1)
              (squareCellBoundaryTrueEndpoint
                (brReachedDualFace n (brFilledReachableHull n R)) d.1) := .nil
          refine ⟨q, ?_⟩
          intro v hv
          have hvEq : v = squareCellBoundaryTrueEndpoint
              (brReachedDualFace n (brFilledReachableHull n R)) d.1 := by
            simpa [q] using hv
          subst v
          refine ⟨squareCellBoundaryTrueEndpoint_property_of_change
            (brReachedDualFace n (brFilledReachableHull n R)) d.1 d.toStopped.2, ?_⟩
          let z := brCellAtPrimalVertex x
          have hxMem : x ∈
              (brTruncatedInterfacePrimalEdge d : Sym2 SquareVertex) := by
            rw [hdUnderlying]
            simp
          have hdCellPositive : d.1 ∈ squareCellPositiveEdges z := by
            have hinc := primalToDualCrossingPositiveEdge_mem_cellAt_of_mem
              (brStoppedInterfacePrimalPositiveEdge d.toStopped)
              (v := x) (by
                simpa [brTruncatedInterfacePrimalEdge] using hxMem)
            simpa [z, brStoppedInterfacePrimalPositiveEdge] using hinc
          have htrueCoords := squareCellBoundaryTrueEndpoint_coordinates
            (brReachedDualFace n (brFilledReachableHull n R)) hdCellPositive
          have hxCoords := hcoords x (by simp)
          have hxPos : 0 < x 1 := by
            have hxNe : x ≠ u := hxu.ne
            by_contra hxNot
            have hxZero : x 1 = 0 := by omega
            exact hxNe (hzero x (by simp) hxZero)
          simp only [z, brCellAtPrimalVertex, squareVertex] at htrueCoords
          omega
      | @cons u v y huv rest =>
          let tail' : squareGraph.Walk u y := .cons huv rest
          have htailNil : ¬ tail'.Nil := by simp [tail']
          have htailPath : tail'.IsPath := by
            simpa [tail'] using hpath.of_cons
          have htailZero : ∀ t ∈ tail'.support, t 1 = 0 → t = y := by
            intro t ht ht0
            apply hzero t
            · simp only [tail', SimpleGraph.Walk.support_cons, List.mem_cons] at ht ⊢
              exact Or.inr ht
            · exact ht0
          have htailEdges : walkEdgeFinset tail' ⊆
              brTruncatedInterfacePrimalEdges n (brFilledReachableHull n R) := by
            intro f hf
            apply hw
            rw [mem_walkEdgeFinset_iff] at hf ⊢
            simp only [tail', SimpleGraph.Walk.edges_cons, List.mem_cons] at hf ⊢
            exact Or.inr hf
          have htailCoords : ∀ t ∈ tail'.support,
              0 ≤ t 0 ∧ t 0 ≤ 2 * (n : ℤ) ∧
                0 ≤ t 1 ∧ t 1 ≤ (n : ℤ) := by
            intro t ht
            apply hcoords t
            simp only [tail', SimpleGraph.Walk.support_cons, List.mem_cons] at ht ⊢
            exact Or.inr ht
          rcases ih htailNil htailPath htailZero htailEdges htailCoords with
            ⟨d', e, hd'First, heLast, qTail, hqTail⟩
          let z := brCellAtPrimalVertex u
          have huHead : u ∈ (brTruncatedInterfacePrimalEdge d : Sym2 SquareVertex) := by
            rw [hdUnderlying]
            simp
          have huTail : u ∈ (brTruncatedInterfacePrimalEdge d' : Sym2 SquareVertex) := by
            rw [hd'First]
            simp [tail']
          have hdCellPositive : d.1 ∈ squareCellPositiveEdges z := by
            have hinc := primalToDualCrossingPositiveEdge_mem_cellAt_of_mem
              (brStoppedInterfacePrimalPositiveEdge d.toStopped)
              (v := u) (by
                simpa [brTruncatedInterfacePrimalEdge] using huHead)
            simpa [z, brStoppedInterfacePrimalPositiveEdge] using hinc
          have hd'CellPositive : d'.1 ∈ squareCellPositiveEdges z := by
            have hinc := primalToDualCrossingPositiveEdge_mem_cellAt_of_mem
              (brStoppedInterfacePrimalPositiveEdge d'.toStopped)
              (v := u) (by
                simpa [brTruncatedInterfacePrimalEdge] using huTail)
            simpa [z, brStoppedInterfacePrimalPositiveEdge] using hinc
          have hdCell : d.1 ∈ squareCellBoundaryPositiveEdges
              (brReachedDualFace n (brFilledReachableHull n R)) z :=
            Finset.mem_filter.mpr ⟨hdCellPositive, d.toStopped.2⟩
          have hd'Cell : d'.1 ∈ squareCellBoundaryPositiveEdges
              (brReachedDualFace n (brFilledReachableHull n R)) z :=
            Finset.mem_filter.mpr ⟨hd'CellPositive, d'.toStopped.2⟩
          have huCoords : 0 ≤ u 0 ∧ u 0 ≤ 2 * (n : ℤ) ∧
              0 ≤ u 1 ∧ u 1 ≤ (n : ℤ) := by
            apply hcoords u
            simp
          have hzFour : (squareCellBoundaryPositiveEdges
              (brReachedDualFace n (brFilledReachableHull n R)) z).card ≠ 4 := by
            simpa [z] using card_filledHullCellAtUpperVertex_ne_four hn hR huCoords
          rcases exists_squareCellBoundaryTrueEndpoint_walk
              (brReachedDualFace n (brFilledReachableHull n R))
              hdCell hd'Cell hzFour with
            ⟨qLocal, _hqLength, hqLocal, hqLocalCoords⟩
          have huNe : u ≠ y := by
            intro huy
            subst y
            exact htailNil (SimpleGraph.Walk.eq_nil_iff_nil.mp
              ((SimpleGraph.Walk.isPath_iff_eq_nil tail').mp htailPath))
          have huPos : 0 < u 1 := by
            by_contra huNot
            have huZero : u 1 = 0 := by omega
            exact huNe (hzero u (by simp) huZero)
          refine ⟨d, e, by simpa using hdUnderlying, ?_,
            qLocal.append qTail, ?_⟩
          · simpa [tail'] using heLast
          · intro t ht
            rw [SimpleGraph.Walk.support_append] at ht
            rcases List.mem_append.mp ht with ht | ht
            · refine ⟨hqLocal t ht, ?_⟩
              have htCoords := hqLocalCoords t ht
              simp only [z, brCellAtPrimalVertex, squareVertex] at htCoords
              omega
            · exact hqTail t (List.mem_of_mem_tail ht)

/-- The stopped upper tail has a connected chain of filled faces on its filled side.  The chain
stays weakly above the midline, which later keeps it disjoint from the artificial lower
extension used to close a comparison path. -/
private theorem exists_filledSideWalk_of_selectedUpperTail
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    ∃ d e : BRTruncatedInterfaceEdge n (brFilledReachableHull n R),
      (brTruncatedInterfacePrimalEdge d : Sym2 SquareVertex) =
        s(brSelectedTopPrimalVertex hn hR.filledHull,
          (brFilledHullSelectedUpperTailPath hn hR).snd) ∧
      (brTruncatedInterfacePrimalEdge e : Sym2 SquareVertex) =
        s((brFilledHullSelectedUpperTailPath hn hR).penultimate,
          brFilledHullLastMidlineVertex hn hR) ∧
      ∃ q : dualSquareGraph.Walk
          (squareCellBoundaryTrueEndpoint
            (brReachedDualFace n (brFilledReachableHull n R)) d.1)
          (squareCellBoundaryTrueEndpoint
            (brReachedDualFace n (brFilledReachableHull n R)) e.1),
        ∀ v ∈ q.support,
          brReachedDualFace n (brFilledReachableHull n R) v ∧ 0 ≤ v 1 := by
  let w := brFilledHullSelectedUpperTailPath hn hR
  have htop := mem_brSquareTopSide_iff.mp
    (brSelectedTopPrimalVertex_mem_topSide hn hR.filledHull)
  have hlast := brFilledHullLastMidlineVertex_one hn hR
  have hne : brSelectedTopPrimalVertex hn hR.filledHull ≠
      brFilledHullLastMidlineVertex hn hR := by
    intro h
    have := congrFun h 1
    omega
  have hnil : ¬w.Nil := SimpleGraph.Walk.not_nil_of_ne hne
  have hwInterface : walkEdgeFinset w ⊆
      brTruncatedInterfacePrimalEdges n (brFilledReachableHull n R) := by
    intro f hf
    rw [mem_walkEdgeFinset_iff] at hf
    have hfTail : (f : Sym2 SquareVertex) ∈
        (brFilledHullSelectedUpperTail hn hR).edges :=
      (brFilledHullSelectedUpperTail hn hR).edges_toPath_subset hf
    have hfReverse : (f : Sym2 SquareVertex) ∈
        (brSelectedPrimalWalk hn hR.filledHull).reverse.edges :=
      (brFilledHullSelectedUpperTail_edges_prefix_reverse hn hR).sublist.subset hfTail
    have hfSelected : (f : Sym2 SquareVertex) ∈
        (brSelectedPrimalWalk hn hR.filledHull).edges := by
      simpa only [SimpleGraph.Walk.edges_reverse, List.mem_reverse] using hfReverse
    exact walkEdgeFinset_brSelectedPrimalWalk_subset_interface hn hR.filledHull
      ((mem_walkEdgeFinset_iff _ f).mpr hfSelected)
  have hwCoords : ∀ v ∈ w.support,
      0 ≤ v 0 ∧ v 0 ≤ 2 * (n : ℤ) ∧ 0 ≤ v 1 ∧ v 1 ≤ (n : ℤ) := by
    intro v hv
    have hvSelected := brFilledHullSelectedUpperTailPath_support_subset_selected
      hn hR v hv
    have hvCoords := brSelectedPrimalWalk_support_coordinates hn hR.filledHull hvSelected
    exact ⟨hvCoords.1, hvCoords.2.1,
      brFilledHullSelectedUpperTailPath_support_nonnegative hn hR hv,
      hvCoords.2.2.2⟩
  have hwZero : ∀ v ∈ w.support, v 1 = 0 →
      v = brFilledHullLastMidlineVertex hn hR := by
    intro v hv hv0
    exact brFilledHullSelectedUpperTailPath_midline_unique hn hR hv hv0
  simpa [w] using exists_filledSideWalk_of_primalWalk hn hR w hnil
    (brFilledHullSelectedUpperTailPath_isPath hn hR) hwZero hwInterface hwCoords

/-- A simple walk which starts with another simple walk's starting vertex and uses only its
edges is an initial segment of that walk.  This elementary path-uniqueness lemma is useful when
the comparison configuration declares precisely the edges of one normalized crossing open. -/
private theorem exists_append_of_isPath_of_edges_subset
    {V : Type*} {G : SimpleGraph V} {u v w : V}
    {p : G.Walk u v} {q : G.Walk u w}
    (hp : p.IsPath) (hq : q.IsPath) (hedges : p.edges ⊆ q.edges) :
    ∃ r : G.Walk v w, q = p.append r := by
  induction p generalizing w with
  | nil =>
      exact ⟨q, by simp⟩
  | @cons u v x huv p ih =>
      cases q with
      | nil =>
          have : s(u, v) ∈ (SimpleGraph.Walk.nil : G.Walk u u).edges :=
            hedges (by simp)
          simp at this
      | @cons _ y w huy q =>
          have hhead : s(u, v) ∈ (SimpleGraph.Walk.cons huy q).edges :=
            hedges (by simp)
          have huNot : u ∉ q.support :=
            (SimpleGraph.Walk.cons_isPath_iff huy q).mp hq |>.2
          have hvy : v = y := by
            simp only [SimpleGraph.Walk.edges_cons, List.mem_cons] at hhead
            rcases hhead with heq | htail
            · rcases Sym2.eq_iff.mp heq with hsame | hswap
              · exact hsame.2
              · exact (huv.ne hswap.2.symm).elim
            · exfalso
              apply huNot
              exact q.mem_support_of_mem_edges htail (Sym2.mem_iff.mpr (Or.inl rfl))
          subst y
          have hpTail : p.IsPath := hp.of_cons
          have hqTail : q.IsPath := hq.of_cons
          have htail : p.edges ⊆ q.edges := by
            intro e he
            have he' : e ∈ (SimpleGraph.Walk.cons huv p).edges := by
              simp [he]
            have heq := hedges he'
            simp only [SimpleGraph.Walk.edges_cons, List.mem_cons] at heq
            rcases heq with heHead | heTail
            · have huNot : u ∉ p.support :=
                (SimpleGraph.Walk.cons_isPath_iff huv p).mp hp |>.2
              exfalso
              apply huNot
              apply p.mem_support_of_mem_edges he
              rw [heHead]
              simp
            · exact heTail
          obtain ⟨r, hr⟩ := ih hpTail hqTail htail
          exact ⟨r, by simp [hr]⟩

/-- An edge-list prefix of a simple walk, with the same starting vertex, is itself the
corresponding simple initial segment. -/
private theorem isPath_and_support_subset_of_edges_prefix
    {V : Type*} {G : SimpleGraph V} {u v w : V}
    (p : G.Walk u v) (q : G.Walk u w)
    (hq : q.IsPath) (hprefix : p.edges <+: q.edges) :
    p.IsPath ∧ ∀ z ∈ p.support, z ∈ q.support := by
  induction p generalizing w with
  | nil =>
      refine ⟨SimpleGraph.Walk.IsPath.nil, fun z hz ↦ ?_⟩
      simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
      simpa only [hz] using q.start_mem_support
  | @cons u v x huv p ih =>
      cases q with
      | nil => simp at hprefix
      | @cons _ y w huy q =>
          simp only [SimpleGraph.Walk.edges_cons, List.cons_prefix_cons] at hprefix
          have hvy : v = y := by
            rcases Sym2.eq_iff.mp hprefix.1 with hsame | hswap
            · exact hsame.2
            · exact (huv.ne hswap.2.symm).elim
          subst y
          have hqTail : q.IsPath := hq.of_cons
          obtain ⟨hpPath, hpSupport⟩ := ih q hqTail hprefix.2
          have huNotQ : u ∉ q.support :=
            (SimpleGraph.Walk.cons_isPath_iff huy q).mp hq |>.2
          refine ⟨hpPath.cons (fun huP ↦ huNotQ (hpSupport u huP)), ?_⟩
          intro z hz
          simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hz ⊢
          exact hz.elim (fun h ↦ Or.inl h) (fun h ↦ Or.inr (hpSupport z h))

/-- Two prefixes of one list are comparable by the prefix relation. -/
private theorem prefix_or_prefix_of_common_prefix
    {α : Type*} {A B C : List α}
    (hA : A <+: C) (hB : B <+: C) : A <+: B ∨ B <+: A := by
  induction C generalizing A B with
  | nil =>
      have hAe : A = [] := by simpa using hA
      have hBe : B = [] := by simpa using hB
      subst A
      subst B
      exact Or.inl (by simp)
  | cons c C ih =>
      cases A with
      | nil => exact Or.inl (by simp)
      | cons a A =>
          cases B with
          | nil => exact Or.inr (by simp)
          | cons b B =>
              simp only [List.cons_prefix_cons] at hA hB
              rcases hA with ⟨hac, hA⟩
              rcases hB with ⟨hbc, hB⟩
              subst a
              subst b
              rcases ih hA hB with hAB | hBA
              · exact Or.inl (by simpa using hAB)
              · exact Or.inr (by simpa using hBA)

/-- The endpoints of two simple initial segments of the same simple walk occur on one another. -/
private theorem endpoint_mem_support_or_endpoint_mem_support_of_prefixes
    {V : Type*} {G : SimpleGraph V} {u v w x : V}
    (p : G.Walk u v) (r : G.Walk u w) (q : G.Walk u x)
    (hq : q.IsPath) (hp : p.edges <+: q.edges) (hr : r.edges <+: q.edges) :
    v ∈ r.support ∨ w ∈ p.support := by
  have hpPath := (isPath_and_support_subset_of_edges_prefix p q hq hp).1
  have hrPath := (isPath_and_support_subset_of_edges_prefix r q hq hr).1
  rcases prefix_or_prefix_of_common_prefix hp hr with hpr | hrp
  · left
    exact (isPath_and_support_subset_of_edges_prefix p r hrPath hpr).2
      v p.end_mem_support
  · right
    exact (isPath_and_support_subset_of_edges_prefix r p hpPath hrp).2
      w r.end_mem_support

/-- In the configuration containing exactly the bonds of a normalized simple crossing, the
filled stopped interface is that crossing.  This is the finite comparison configuration used
to reduce lowest-interface monotonicity to inclusion of filled reached regions. -/
private theorem brSelectedPrimalWalk_filledHull_eq_of_exact_crossing
    {n a b : ℕ} (hn : 0 < n)
    (q : squareGraph.Walk (squareVertex (a : ℤ) (-(n : ℤ)))
      (squareVertex (b : ℤ) (n : ℤ)))
    (hqPath : q.IsPath)
    (hqAllowed : walkEdgeFinset q ⊆
      squareBoundaryFreeRectangleEdges (2 * n) n)
    (hbox : ∀ z ∈ q.support,
      0 ≤ z 0 ∧ z 0 ≤ 2 * (n : ℤ) ∧
        -(n : ℤ) ≤ z 1 ∧ z 1 ≤ (n : ℤ))
    (hbottomUnique : ∀ z ∈ q.support, z 1 = -(n : ℤ) →
      z = squareVertex (a : ℤ) (-(n : ℤ)))
    (htopUnique : ∀ z ∈ q.support, z 1 = (n : ℤ) →
      z = squareVertex (b : ℤ) (n : ℤ)) :
    let eta : EdgeConfiguration 2 := {e | e ∈ walkEdgeFinset q}
    let R := brLeftReachableFaces n eta
    ∃ hR : BRAdmissibleSeparatingFiber n R,
      brSelectedBottomPrimalVertex hn hR.filledHull =
          squareVertex (a : ℤ) (-(n : ℤ)) ∧
        brSelectedTopPrimalVertex hn hR.filledHull =
          squareVertex (b : ℤ) (n : ℤ) ∧
        (brSelectedPrimalWalk hn hR.filledHull).edges = q.edges := by
  classical
  let eta : EdgeConfiguration 2 := {e | e ∈ walkEdgeFinset q}
  let R := brLeftReachableFaces n eta
  have hqOpenEta : walkIsOpen eta q := by
    intro e he
    let ee : SquareEdge := ⟨e, q.edges_subset_edgeSet he⟩
    exact (mem_walkEdgeFinset_iff q ee).mpr he
  have hetaVertical : eta ∈ brSquareVerticalCrossingEvent n := by
    simp only [brSquareVerticalCrossingEvent, Set.mem_iUnion]
    refine ⟨squareVertex (a : ℤ) (-(n : ℤ)), ?_,
      squareVertex (b : ℤ) (n : ℤ), ?_, q, hqOpenEta, hqAllowed⟩
    · rw [mem_brSquareBottomSide_iff]
      have ha := hbox _ q.start_mem_support
      simp only [squareVertex] at ha ⊢
      exact ⟨ha.1, ha.2.1, rfl⟩
    · rw [mem_brSquareTopSide_iff]
      have hb := hbox _ q.end_mem_support
      simp only [squareVertex] at hb ⊢
      exact ⟨hb.1, hb.2.1, rfl⟩
  have hetaGood : eta ∈ brRightTargetsUnreachedEvent n :=
    brSquareVerticalCrossingEvent_subset_brRightTargetsUnreachedEvent n hetaVertical
  have hRgood : R ∈ brGoodReachableFaceFiberIndices n := by
    rw [mem_brGoodReachableFaceFiberIndices_iff]
    exact hetaGood
  have hetaFiber : eta ∈ brReachableFaceFiber n R :=
    mem_brReachableFaceFiber_self n eta
  let hR : BRAdmissibleSeparatingFiber n R :=
    brAdmissibleSeparatingFiber_of_mem_good_of_mem_fiber hRgood hetaFiber
  refine ⟨hR, ?_⟩
  let p := brSelectedPrimalWalk hn hR.filledHull
  have hpPath : p.IsPath := brSelectedPrimalWalk_isPath hn hR.filledHull
  have hpOpenEta : walkIsOpen eta p :=
    walkIsOpen_brSelectedPrimalWalk_filledHull_of_mem_fiber hn hR hetaFiber
  have hpEdges : p.edges ⊆ q.edges := by
    intro e he
    have heEta := hpOpenEta e he
    let ee : SquareEdge := ⟨e, p.edges_subset_edgeSet he⟩
    have heqFin : ee ∈ walkEdgeFinset q := heEta
    exact (mem_walkEdgeFinset_iff q ee).mp heqFin
  have hpStartNeEnd : brSelectedBottomPrimalVertex hn hR.filledHull ≠
      brSelectedTopPrimalVertex hn hR.filledHull := by
    intro heq
    have hbottom := mem_brSquareBottomSide_iff.mp
      (brSelectedBottomPrimalVertex_mem_bottomSide hn hR.filledHull)
    have htop := mem_brSquareTopSide_iff.mp
      (brSelectedTopPrimalVertex_mem_topSide hn hR.filledHull)
    change brSelectedBottomPrimalVertex hn hR.filledHull =
      brSelectedTopPrimalVertex hn hR.filledHull at heq
    have := congrFun heq 1
    omega
  have hpNotNil : ¬p.Nil := SimpleGraph.Walk.not_nil_of_ne hpStartNeEnd
  have hpSupport : ∀ z ∈ p.support, z ∈ q.support := by
    intro z hz
    rw [p.mem_support_iff_exists_mem_edges_of_not_nil hpNotNil] at hz
    rcases hz with ⟨e, hep, hze⟩
    exact q.mem_support_of_mem_edges (hpEdges hep) hze
  have hstart : brSelectedBottomPrimalVertex hn hR.filledHull =
      squareVertex (a : ℤ) (-(n : ℤ)) := by
    apply hbottomUnique _ (hpSupport _ p.start_mem_support)
    simpa [p] using (mem_brSquareBottomSide_iff.mp
      (brSelectedBottomPrimalVertex_mem_bottomSide hn hR.filledHull)).2.2
  have hend : brSelectedTopPrimalVertex hn hR.filledHull =
      squareVertex (b : ℤ) (n : ℤ) := by
    apply htopUnique _ (hpSupport _ p.end_mem_support)
    simpa [p] using (mem_brSquareTopSide_iff.mp
      (brSelectedTopPrimalVertex_mem_topSide hn hR.filledHull)).2.2
  let p' : squareGraph.Walk (squareVertex (a : ℤ) (-(n : ℤ)))
      (squareVertex (b : ℤ) (n : ℤ)) := p.copy hstart hend
  have hp'Path : p'.IsPath := by
    simpa [p'] using hpPath
  have hp'Edges : p'.edges ⊆ q.edges := by
    simpa [p'] using hpEdges
  have hpq : p' = q := by
    obtain ⟨r, hr⟩ :=
      exists_append_of_isPath_of_edges_subset hp'Path hqPath hp'Edges
    have hrPath : r.IsPath := by
      rw [hr] at hqPath
      exact hqPath.of_append_right
    have hrNil : r = .nil :=
      (SimpleGraph.Walk.isPath_iff_eq_nil r).mp hrPath
    subst r
    simpa using hr.symm
  exact ⟨hstart, hend,
    by simpa [p'] using congrArg SimpleGraph.Walk.edges hpq⟩

/-- In the exact-crossing configuration, the filled interface and the displayed crossing have
the same first visit to the midline when read backwards from the top. -/
private theorem brFilledHullLastMidlineVertex_eq_of_exact_crossing
    {n a b : ℕ} (hn : 0 < n)
    {R : Finset (BRLeftmostDualVertex n)}
    (hR : BRAdmissibleSeparatingFiber n R)
    (q : squareGraph.Walk (squareVertex (a : ℤ) (-(n : ℤ)))
      (squareVertex (b : ℤ) (n : ℤ)))
    (hqPath : q.IsPath)
    (htop : brSelectedTopPrimalVertex hn hR.filledHull =
      squareVertex (b : ℤ) (n : ℤ))
    (hedges : (brSelectedPrimalWalk hn hR.filledHull).edges = q.edges)
    {z : SquareVertex}
    (t : squareGraph.Walk (squareVertex (b : ℤ) (n : ℤ)) z)
    (htPrefix : t.edges <+: q.reverse.edges)
    (htUnique : ∀ x ∈ t.support, x 1 = 0 → x = z)
    (hz : z 1 = 0) :
    brFilledHullLastMidlineVertex hn hR = z := by
  let u := brFilledHullSelectedUpperTail hn hR
  let u' : squareGraph.Walk (squareVertex (b : ℤ) (n : ℤ))
      (brFilledHullLastMidlineVertex hn hR) := u.copy htop rfl
  have huPrefix : u'.edges <+: q.reverse.edges := by
    have h := brFilledHullSelectedUpperTail_edges_prefix_reverse hn hR
    simp only [SimpleGraph.Walk.edges_reverse] at h ⊢
    rw [hedges] at h
    simpa [u', u] using h
  have hqReversePath : q.reverse.IsPath := hqPath.reverse
  rcases endpoint_mem_support_or_endpoint_mem_support_of_prefixes
      u' t q.reverse hqReversePath huPrefix htPrefix with hlast | hztail
  · exact htUnique _ hlast (brFilledHullLastMidlineVertex_one hn hR)
  · symm
    apply brFilledHullSelectedUpperTail_midline_unique hn hR
    · simpa [u', u] using hztail
    · exact hz

private theorem walk_horizontalRayCount_eq_zero_of_unique_bottom_of_face_right
    {n : ℕ} {a b : SquareVertex}
    (q : squareGraph.Walk a b)
    (ha : a 1 = -(n : ℤ))
    (hlower : ∀ z ∈ q.support, -(n : ℤ) ≤ z 1)
    (hunique : ∀ z ∈ q.support, z 1 = -(n : ℤ) → z = a)
    (f : DualSquareVertex) (hf : f 1 = -(n : ℤ))
    (hfa : a 0 ≤ f 0) :
    q.edges.countP (squareEdgeCrossesFaceHorizontalRayBool f) = 0 := by
  classical
  rw [List.countP_eq_zero]
  intro e he
  induction e using Sym2.ind with
  | _ u v =>
      have huv : squareGraph.Adj u v := q.adj_of_mem_edges he
      have huSupport : u ∈ q.support := q.fst_mem_support_of_mem_edges he
      have hvSupport : v ∈ q.support := q.snd_mem_support_of_mem_edges he
      rcases (cubicGraph_adj_iff_exists_stepFrom u v).mp huv with ⟨⟨i, s⟩, rfl⟩
      fin_cases i <;> cases s
      · simp [squareEdgeCrossesFaceHorizontalRayBool,
          squareEdgeCrossesFaceHorizontalRay, cubicStepFrom,
          cubicDirectionIncrement]
      · simp [squareEdgeCrossesFaceHorizontalRayBool,
          squareEdgeCrossesFaceHorizontalRay, cubicStepFrom,
          cubicDirectionIncrement]
      · by_cases hvBottom :
            (cubicStepFrom u ((fun i => i) 1, false)) 1 = -(n : ℤ)
        · have hva := hunique
            (cubicStepFrom u ((fun i => i) 1, false)) hvSupport hvBottom
          have hv0 : (cubicStepFrom u ((fun i => i) 1, false)) 0 = a 0 :=
            congrFun hva 0
          simp [squareEdgeCrossesFaceHorizontalRayBool,
            squareEdgeCrossesFaceHorizontalRay, cubicStepFrom,
            cubicDirectionIncrement, hf] at hv0 ⊢
          omega
        · simp [squareEdgeCrossesFaceHorizontalRayBool,
            squareEdgeCrossesFaceHorizontalRay, cubicStepFrom,
            cubicDirectionIncrement, hf]
          simp [cubicStepFrom, cubicDirectionIncrement] at hvBottom
          omega
      · by_cases huBottom : u 1 = -(n : ℤ)
        · have hua : u = a := hunique u huSupport huBottom
          have hu0 : u 0 = a 0 := congrFun hua 0
          simp [squareEdgeCrossesFaceHorizontalRayBool,
            squareEdgeCrossesFaceHorizontalRay, cubicStepFrom,
            cubicDirectionIncrement, hf, huBottom]
          omega
        · simp [squareEdgeCrossesFaceHorizontalRayBool,
            squareEdgeCrossesFaceHorizontalRay, cubicStepFrom,
            cubicDirectionIncrement, hf, huBottom]

private theorem walk_horizontalRayCount_eq_zero_of_unique_top_of_face_right
    {n : ℕ} {a b : SquareVertex}
    (q : squareGraph.Walk a b)
    (hb : b 1 = (n : ℤ))
    (hupper : ∀ z ∈ q.support, z 1 ≤ (n : ℤ))
    (hunique : ∀ z ∈ q.support, z 1 = (n : ℤ) → z = b)
    (f : DualSquareVertex) (hf : f 1 = (n : ℤ) - 1)
    (hfb : b 0 ≤ f 0) :
    q.edges.countP (squareEdgeCrossesFaceHorizontalRayBool f) = 0 := by
  classical
  rw [List.countP_eq_zero]
  intro e he
  induction e using Sym2.ind with
  | _ u v =>
      have huv : squareGraph.Adj u v := q.adj_of_mem_edges he
      have huSupport : u ∈ q.support := q.fst_mem_support_of_mem_edges he
      have hvSupport : v ∈ q.support := q.snd_mem_support_of_mem_edges he
      rcases (cubicGraph_adj_iff_exists_stepFrom u v).mp huv with ⟨⟨i, s⟩, rfl⟩
      fin_cases i <;> cases s
      · simp [squareEdgeCrossesFaceHorizontalRayBool,
          squareEdgeCrossesFaceHorizontalRay, cubicStepFrom,
          cubicDirectionIncrement]
      · simp [squareEdgeCrossesFaceHorizontalRayBool,
          squareEdgeCrossesFaceHorizontalRay, cubicStepFrom,
          cubicDirectionIncrement]
      · by_cases huTop : u 1 = (n : ℤ)
        · have hub := hunique u huSupport huTop
          have hu0 : u 0 = b 0 := congrFun hub 0
          simp [squareEdgeCrossesFaceHorizontalRayBool,
            squareEdgeCrossesFaceHorizontalRay, cubicStepFrom,
            cubicDirectionIncrement, hf, huTop]
          omega
        · simp [squareEdgeCrossesFaceHorizontalRayBool,
            squareEdgeCrossesFaceHorizontalRay, cubicStepFrom,
            cubicDirectionIncrement, hf, huTop]
          have huUpper := hupper u huSupport
          omega
      · by_cases hvTop :
            (cubicStepFrom u ((fun i => i) 1, true)) 1 = (n : ℤ)
        · have hvb := hunique
            (cubicStepFrom u ((fun i => i) 1, true)) hvSupport hvTop
          have hv0 : (cubicStepFrom u ((fun i => i) 1, true)) 0 = b 0 :=
            congrFun hvb 0
          simp [squareEdgeCrossesFaceHorizontalRayBool,
            squareEdgeCrossesFaceHorizontalRay, cubicStepFrom,
            cubicDirectionIncrement, hf] at hv0 ⊢
          omega
        · simp [squareEdgeCrossesFaceHorizontalRayBool,
            squareEdgeCrossesFaceHorizontalRay, cubicStepFrom,
            cubicDirectionIncrement, hf]
          simp [cubicStepFrom, cubicDirectionIncrement] at hvTop
          have hvUpper := hupper
            (cubicStepFrom u ((fun i => i) 1, true)) hvSupport
          omega

/-- Immediately below a uniquely visited top endpoint, a ray starting strictly to its left
crosses a simple path exactly once. -/
private theorem walk_horizontalRayCount_eq_one_of_unique_top_of_face_left
    {n : ℕ} {a b : SquareVertex}
    (q : squareGraph.Walk a b)
    (hqPath : q.IsPath)
    (hnil : ¬q.Nil)
    (hb : b 1 = (n : ℤ))
    (hupper : ∀ z ∈ q.support, z 1 ≤ (n : ℤ))
    (hunique : ∀ z ∈ q.support, z 1 = (n : ℤ) → z = b)
    (f : DualSquareVertex) (hf : f 1 = (n : ℤ) - 1)
    (hfb : f 0 < b 0) :
    q.edges.countP (squareEdgeCrossesFaceHorizontalRayBool f) = 1 := by
  classical
  let last : Sym2 SquareVertex := s(q.penultimate, b)
  have hlastMem : last ∈ q.edges := q.mk_penultimate_end_mem_edges hnil
  have hpenSupport : q.penultimate ∈ q.support := by
    exact q.mem_support_of_mem_edges hlastMem (by simp [last])
  have hpenUpper := hupper q.penultimate hpenSupport
  have hpenAdj := q.adj_penultimate hnil
  have hpenOne : q.penultimate 1 = (n : ℤ) - 1 := by
    rcases (cubicGraph_adj_iff_exists_stepFrom q.penultimate b).mp hpenAdj with
      ⟨⟨i, s⟩, hbStep⟩
    fin_cases i <;> cases s
    · have hb1 := congrFun hbStep 1
      simp [cubicStepFrom, cubicDirectionIncrement] at hb1
      have hpenTop : q.penultimate 1 = (n : ℤ) := by omega
      exact (hpenAdj.ne (hunique q.penultimate hpenSupport hpenTop)).elim
    · have hb1 := congrFun hbStep 1
      simp [cubicStepFrom, cubicDirectionIncrement] at hb1
      have hpenTop : q.penultimate 1 = (n : ℤ) := by omega
      exact (hpenAdj.ne (hunique q.penultimate hpenSupport hpenTop)).elim
    · have hb1 := congrFun hbStep 1
      simp [cubicStepFrom, cubicDirectionIncrement] at hb1
      omega
    · have hb1 := congrFun hbStep 1
      simp [cubicStepFrom, cubicDirectionIncrement] at hb1
      omega
  have hpenZero : q.penultimate 0 = b 0 := by
    rcases (cubicGraph_adj_iff_exists_stepFrom q.penultimate b).mp hpenAdj with
      ⟨⟨i, s⟩, hbStep⟩
    fin_cases i <;> cases s <;>
      have hb0 := congrFun hbStep 0 <;>
      have hb1 := congrFun hbStep 1 <;>
      simp [cubicStepFrom, cubicDirectionIncrement] at hb0 hb1 <;> omega
  have hpred : ∀ e ∈ q.edges,
      squareEdgeCrossesFaceHorizontalRayBool f e = true ↔
        decide (e = last) = true := by
    intro e he
    induction e using Sym2.ind with
    | _ u v =>
        have huv := q.adj_of_mem_edges he
        have huSupport := q.fst_mem_support_of_mem_edges he
        have hvSupport := q.snd_mem_support_of_mem_edges he
        have huUpper := hupper u huSupport
        have hvUpper := hupper v hvSupport
        constructor <;> intro h
        · simp only [squareEdgeCrossesFaceHorizontalRayBool, decide_eq_true_eq] at h
          simp only [squareEdgeCrossesFaceHorizontalRay] at h
          have htop : u 1 = (n : ℤ) ∨ v 1 = (n : ℤ) := by
            rcases (cubicGraph_adj_iff_exists_stepFrom u v).mp huv with ⟨⟨i, s⟩, rfl⟩
            fin_cases i <;> cases s <;>
              simp [cubicStepFrom, cubicDirectionIncrement] at h ⊢ <;> omega
          rcases htop with huTop | hvTop
          · have hub := hunique u huSupport huTop
            subst u
            have hvPen : v = q.penultimate :=
              hqPath.eq_penultimate_of_mem_edges he
            simp [last, hvPen]
          · have hvb := hunique v hvSupport hvTop
            subst v
            have huPen : u = q.penultimate :=
              hqPath.eq_penultimate_of_mem_edges (Sym2.eq_swap ▸ he)
            simp [last, huPen]
        · simp only [decide_eq_true_eq] at h
          rw [h]
          simp [last, squareEdgeCrossesFaceHorizontalRayBool,
            squareEdgeCrossesFaceHorizontalRay, hf, hpenOne, hpenZero, hb, hfb]
  have hcount : q.edges.countP (fun e ↦ decide (e = last)) =
      q.edges.count last := by
    rw [List.count]
    apply List.countP_congr
    intro e _he
    simp only [decide_eq_true_eq, beq_iff_eq]
  calc
    q.edges.countP (squareEdgeCrossesFaceHorizontalRayBool f) =
        q.edges.countP (fun e ↦ decide (e = last)) :=
      List.countP_congr hpred
    _ = q.edges.count last := hcount
    _ = 1 := List.count_eq_one_of_mem hqPath.isTrail.edges_nodup hlastMem

/-- Straight lower extension which completes an upper-half comparison tail to a normalized
bottom--top walk. -/
private def brMidlineLowerExtensionWalk (n a : ℕ) :
    squareGraph.Walk (squareVertex (a : ℤ) (-(n : ℤ))) (squareVertex (a : ℤ) 0) :=
  (cubicWalkFrom (squareVertex (a : ℤ) (-(n : ℤ)))
    (List.replicate n ((1 : Fin 2), true))).copy rfl (by
      rw [cubicEndpointFrom_replicate_pos]
      ext i
      fin_cases i <;> simp [squareVertex, Function.update] <;> omega)

/-- A dual edge whose endpoints are weakly above the midline cannot cross the artificial
straight primal extension lying strictly below it. -/
private theorem squareEdgeDualCrossingEquiv_symm_not_mem_brMidlineLowerExtensionWalk
    {n a : ℕ} (ed : DualSquareEdge)
    (hedNonnegative : ∀ z ∈ (ed : Sym2 DualSquareVertex), 0 ≤ z 1) :
    squareEdgeDualCrossingEquiv.symm ed ∉
      walkEdgeFinset (brMidlineLowerExtensionWalk n a) := by
  classical
  intro hedExtension
  let pe := squareEdgeDualCrossingEquiv.symm ed
  let epos := SquarePositiveEdge.edgeEquiv.symm pe
  have hepos : epos.toEdge = pe := by
    change SquarePositiveEdge.edgeEquiv epos = pe
    exact SquarePositiveEdge.edgeEquiv.apply_symm_apply pe
  have hedRaw : (epos.toEdge : Sym2 SquareVertex) ∈
      (brMidlineLowerExtensionWalk n a).edges := by
    rw [hepos]
    exact (mem_walkEdgeFinset_iff _ _).mp hedExtension
  have hsupport : ∀ z ∈ (brMidlineLowerExtensionWalk n a).support,
      z 0 = (a : ℤ) ∧ z 1 ≤ 0 := by
    intro z hz
    have hzRaw : z ∈ cubicVerticesFrom (squareVertex (a : ℤ) (-(n : ℤ)))
        (List.replicate n ((1 : Fin 2), true)) := by
      simpa [brMidlineLowerExtensionWalk, SimpleGraph.Walk.support_copy,
        cubicWalkFrom_support] using hz
    have hz0 := cubicVerticesFrom_replicate_pos_coord_eq_of_ne
      (squareVertex (a : ℤ) (-(n : ℤ))) (1 : Fin 2) (0 : Fin 2) n
        (by decide) hzRaw
    have hz1 := cubicVerticesFrom_replicate_pos_coord_between
      (squareVertex (a : ℤ) (-(n : ℤ))) (1 : Fin 2) n hzRaw
    simp only [squareVertex_zero, squareVertex_one] at hz0 hz1
    omega
  have hbase := hsupport epos.base
    ((brMidlineLowerExtensionWalk n a).fst_mem_support_of_mem_edges hedRaw)
  have hstep := hsupport (cubicStepFrom epos.base (epos.axis, true))
    ((brMidlineLowerExtensionWalk n a).snd_mem_support_of_mem_edges hedRaw)
  rcases epos with ⟨base, axis⟩
  fin_cases axis
  · simp [cubicStepFrom, cubicDirectionIncrement] at hbase hstep
    omega
  · have hbaseNeg : base 1 < 0 := by
      simp [cubicStepFrom, cubicDirectionIncrement] at hstep
      omega
    have hedEq : ed = squarePositiveEdgeDualCrossingEmbedding
        (⟨base, (1 : Fin 2)⟩ : SquarePositiveEdge) := by
      rw [squarePositiveEdgeDualCrossingEmbedding_apply]
      calc
        ed = squareEdgeDualCrossingEquiv pe := by
          simpa [pe] using (squareEdgeDualCrossingEquiv.apply_symm_apply ed).symm
        _ = squareEdgeDualCrossingEquiv
            (⟨base, (1 : Fin 2)⟩ : SquarePositiveEdge).toEdge :=
          congrArg squareEdgeDualCrossingEquiv hepos.symm
    let f := (primalToDualCrossingPositiveEdge
      (⟨base, (1 : Fin 2)⟩ : SquarePositiveEdge)).base
    have hfMem : f ∈ (ed : Sym2 DualSquareVertex) := by
      rw [hedEq]
      have hembed : squarePositiveEdgeDualCrossingEmbedding
          (⟨base, (1 : Fin 2)⟩ : SquarePositiveEdge) =
          (primalToDualCrossingPositiveEdge
            (⟨base, (1 : Fin 2)⟩ : SquarePositiveEdge)).toEdge := by
        change (primalToDualCrossingPositiveEdge
          (SquarePositiveEdge.edgeEquiv.symm
            ((⟨base, (1 : Fin 2)⟩ : SquarePositiveEdge).toEdge))).toEdge =
          (primalToDualCrossingPositiveEdge
            (⟨base, (1 : Fin 2)⟩ : SquarePositiveEdge)).toEdge
        rw [show SquarePositiveEdge.edgeEquiv.symm
            ((⟨base, (1 : Fin 2)⟩ : SquarePositiveEdge).toEdge) =
              (⟨base, (1 : Fin 2)⟩ : SquarePositiveEdge) by
          simpa [squarePositiveEdgeEmbedding] using
            (SquarePositiveEdge.edgeEquiv_symm_squarePositiveEdgeEmbedding
              (⟨base, (1 : Fin 2)⟩ : SquarePositiveEdge))]
      rw [hembed]
      simp [f, SquarePositiveEdge.toEdge]
    have hfNonnegative := hedNonnegative f hfMem
    have hfOne : f 1 = base 1 := by
      simp [f, primalToDualCrossingPositiveEdge, squarePerp,
        cubicStepFrom, cubicDirectionIncrement]
    omega

/-- Close an upper-half tail by a straight segment below the midline and the standard left
exterior arc.  A top-row face left of the tail's unique top endpoint and a midline face right of
its unique bottom endpoint have opposite mod-two indices. -/
private theorem brCompletedUpperTail_faceParity_ne
    {n a b : ℕ} (hn : 0 < n)
    (t : squareGraph.Walk (squareVertex (b : ℤ) (n : ℤ))
      (squareVertex (a : ℤ) 0))
    (htPath : t.IsPath)
    (htBox : ∀ z ∈ t.support,
      0 ≤ z 0 ∧ z 0 ≤ 2 * (n : ℤ) ∧ 0 ≤ z 1 ∧ z 1 ≤ (n : ℤ))
    (htBottom : ∀ z ∈ t.support, z 1 = 0 → z = squareVertex (a : ℤ) 0)
    (htTop : ∀ z ∈ t.support, z 1 = (n : ℤ) →
      z = squareVertex (b : ℤ) (n : ℤ))
    {fTop fMid : DualSquareVertex}
    (hfTopLower : -1 ≤ fTop 0)
    (hfTop0 : fTop 0 < (b : ℤ)) (hfTop1 : fTop 1 = (n : ℤ) - 1)
    (hfMid0 : (a : ℤ) ≤ fMid 0) (hfMid1 : fMid 1 = 0) :
    let p := (brMidlineLowerExtensionWalk n a).append t.reverse
    let c := p.append (brLeftExteriorClosureWalk n a b)
    closedSquareWalkFaceParity c fTop ≠ closedSquareWalkFaceParity c fMid := by
  dsimp only
  let e := brMidlineLowerExtensionWalk n a
  let p := e.append t.reverse
  let c := p.append (brLeftExteriorClosureWalk n a b)
  have htNil : ¬t.reverse.Nil := by
    apply SimpleGraph.Walk.not_nil_of_ne
    intro h
    have h1 := congrFun h 1
    simp [squareVertex] at h1
    omega
  have htReverseBox : ∀ z ∈ t.reverse.support,
      0 ≤ z 0 ∧ z 0 ≤ 2 * (n : ℤ) ∧ 0 ≤ z 1 ∧ z 1 ≤ (n : ℤ) := by
    intro z hz
    apply htBox z
    simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hz
  have htReverseBottom : ∀ z ∈ t.reverse.support, z 1 = 0 →
      z = squareVertex (a : ℤ) 0 := by
    intro z hz hz0
    apply htBottom z
    · simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hz
    · exact hz0
  have htReverseTop : ∀ z ∈ t.reverse.support, z 1 = (n : ℤ) →
      z = squareVertex (b : ℤ) (n : ℤ) := by
    intro z hz hzn
    apply htTop z
    · simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hz
    · exact hzn
  have hExtTop : e.edges.countP
      (squareEdgeCrossesFaceHorizontalRayBool fTop) = 0 := by
    have h := horizontalRayCount_cubicWalkFrom_replicate_vertical_pos
      (squareVertex (a : ℤ) (-(n : ℤ))) fTop n
    simp only [e, brMidlineLowerExtensionWalk, SimpleGraph.Walk.edges_copy]
    have hsteps : List.replicate n ((1 : Fin 2), true) =
        List.replicate n ((⟨1, by decide⟩ : Fin 2), true) := by
      congr 2
    rw [hsteps, h]
    split_ifs with hc
    · simp only [squareVertex_zero, squareVertex_one] at hc
      omega
    · rfl
  have hTailTop : t.reverse.edges.countP
      (squareEdgeCrossesFaceHorizontalRayBool fTop) = 1 := by
    apply walk_horizontalRayCount_eq_one_of_unique_top_of_face_left
      (n := n) t.reverse htPath.reverse htNil
    · simp [squareVertex]
    · exact fun z hz ↦ (htReverseBox z hz).2.2.2
    · exact htReverseTop
    · exact hfTop1
    · exact hfTop0
  have hExtMid : e.edges.countP
      (squareEdgeCrossesFaceHorizontalRayBool fMid) = 0 := by
    have h := horizontalRayCount_cubicWalkFrom_replicate_vertical_pos
      (squareVertex (a : ℤ) (-(n : ℤ))) fMid n
    simp only [e, brMidlineLowerExtensionWalk, SimpleGraph.Walk.edges_copy]
    have hsteps : List.replicate n ((1 : Fin 2), true) =
        List.replicate n ((⟨1, by decide⟩ : Fin 2), true) := by
      congr 2
    rw [hsteps, h]
    split_ifs with hc
    · simp only [squareVertex_zero, squareVertex_one] at hc
      omega
    · rfl
  have hTailMid : t.reverse.edges.countP
      (squareEdgeCrossesFaceHorizontalRayBool fMid) = 0 := by
    apply walk_horizontalRayCount_eq_zero_of_unique_bottom_of_face_right
      (n := 0) t.reverse
    · simp [squareVertex]
    · exact fun z hz ↦ (htReverseBox z hz).2.2.1
    · exact htReverseBottom
    · exact hfMid1
    · simpa [squareVertex] using hfMid0
  have hClosureTop := brLeftExteriorClosureWalk_horizontalRayCount_eq_zero
    (n := n) (a := a) (b := b) fTop hfTopLower
  have hClosureMid := brLeftExteriorClosureWalk_horizontalRayCount_eq_zero
    (n := n) (a := a) (b := b) fMid (by
      have hMidBox := htBox _ t.end_mem_support
      omega)
  have hTopParity : closedSquareWalkFaceParity c fTop = 1 := by
    unfold closedSquareWalkFaceParity
    simp only [c, p, SimpleGraph.Walk.edges_append, List.countP_append,
      hExtTop, hTailTop, hClosureTop]
  have hMidParity : closedSquareWalkFaceParity c fMid = 0 := by
    unfold closedSquareWalkFaceParity
    simp only [c, p, SimpleGraph.Walk.edges_append, List.countP_append,
      hExtMid, hTailMid, hClosureMid]
  rw [hTopParity, hMidParity]
  norm_num

/-- Closing a normalized bottom--top path along the left exterior separates every left source
face from every bottom-row face at or to the right of the path's unique bottom endpoint. -/
private theorem brClosedBottomTopWalk_faceParity_ne_bottomFace_right
    {n a b : ℕ}
    (q : squareGraph.Walk (squareVertex (a : ℤ) (-(n : ℤ)))
      (squareVertex (b : ℤ) (n : ℤ)))
    (hbox : ∀ z ∈ q.support,
      0 ≤ z 0 ∧ z 0 ≤ 2 * (n : ℤ) ∧
        -(n : ℤ) ≤ z 1 ∧ z 1 ≤ (n : ℤ))
    (hunique : ∀ z ∈ q.support, z 1 = -(n : ℤ) →
      z = squareVertex (a : ℤ) (-(n : ℤ)))
    {x y : DualSquareVertex}
    (hx₀ : x 0 = -1) (hx₁ : -(n : ℤ) ≤ x 1) (hx₁' : x 1 < (n : ℤ))
    (hy₀ : (a : ℤ) ≤ y 0) (hy₁ : y 1 = -(n : ℤ)) :
    closedSquareWalkFaceParity
        (q.append (brLeftExteriorClosureWalk n a b)) x ≠
      closedSquareWalkFaceParity
        (q.append (brLeftExteriorClosureWalk n a b)) y := by
  let c := q.append (brLeftExteriorClosureWalk n a b)
  have hxOdd := odd_horizontalRayCount_of_bottom_top_walk
    q hbox x hx₀ hx₁ hx₁'
  have hxClosure := brLeftExteriorClosureWalk_horizontalRayCount_eq_zero
    (n := n) (a := a) (b := b) x (by omega)
  have hyPrimal : q.edges.countP
      (squareEdgeCrossesFaceHorizontalRayBool y) = 0 :=
    walk_horizontalRayCount_eq_zero_of_unique_bottom_of_face_right
      q (by simp [squareVertex]) (fun z hz ↦ (hbox z hz).2.2.1)
        hunique y hy₁ hy₀
  have hyClosure := brLeftExteriorClosureWalk_horizontalRayCount_eq_zero
    (n := n) (a := a) (b := b) y (by omega)
  have hxParity : closedSquareWalkFaceParity c x = 1 := by
    unfold closedSquareWalkFaceParity
    simp only [c, SimpleGraph.Walk.edges_append, List.countP_append,
      hxClosure, add_zero]
    exact Nat.odd_iff.mp hxOdd
  have hyParity : closedSquareWalkFaceParity c y = 0 := by
    unfold closedSquareWalkFaceParity
    simp only [c, SimpleGraph.Walk.edges_append, List.countP_append,
      hyPrimal, hyClosure, zero_add, Nat.zero_mod]
  rw [hxParity, hyParity]
  norm_num

/-- No bottom-row dual face weakly to the right of the unique bottom endpoint of an open
normalized crossing is reachable by the stopped closed-dual exploration. -/
theorem not_mem_brLeftReachableFaces_of_open_normalized_crossing_bottom_face_right
    {n a b : ℕ} {omega : EdgeConfiguration 2}
    (q : squareGraph.Walk (squareVertex (a : ℤ) (-(n : ℤ)))
      (squareVertex (b : ℤ) (n : ℤ)))
    (hqOpen : walkIsOpen omega q)
    (hqAllowed : walkEdgeFinset q ⊆
      squareBoundaryFreeRectangleEdges (2 * n) n)
    (hbox : ∀ z ∈ q.support,
      0 ≤ z 0 ∧ z 0 ≤ 2 * (n : ℤ) ∧
        -(n : ℤ) ≤ z 1 ∧ z 1 ≤ (n : ℤ))
    (hunique : ∀ z ∈ q.support, z 1 = -(n : ℤ) →
      z = squareVertex (a : ℤ) (-(n : ℤ)))
    (y : BRLeftmostDualVertex n)
    (hy₀ : (a : ℤ) ≤ y.1 0) (hy₁ : y.1 1 = -(n : ℤ)) :
    y ∉ brLeftReachableFaces n omega := by
  classical
  intro hyReach
  rw [brLeftReachableFaces, mem_finiteGraphReachableVertices_iff] at hyReach
  rcases hyReach with ⟨x, hxSource, w, hwOpen⟩
  let w' := w.map (brLeftmostDualToAmbientHom n)
  have hw'Frame : ∀ z ∈ w'.support, z ∈ brLeftmostDualFaces n := by
    intro z hz
    simp only [w', SimpleGraph.Walk.support_map, List.mem_map] at hz
    rcases hz with ⟨zFrame, _hzFrame, rfl⟩
    exact zFrame.2
  have hxFrame := mem_brLeftmostDualFaces_iff.mp x.2
  have hx₀ : x.1 0 = -1 := mem_brLeftmostDualSources_iff.mp hxSource
  let c := q.append (brLeftExteriorClosureWalk n a b)
  have hparity : closedSquareWalkFaceParity c x.1 ≠
      closedSquareWalkFaceParity c y.1 := by
    exact brClosedBottomTopWalk_faceParity_ne_bottomFace_right
      q hbox hunique hx₀ hxFrame.2.2.1 hxFrame.2.2.2 hy₀ hy₁
  obtain ⟨ed, hedw, hedc⟩ :=
    exists_dualWalk_edge_crossing_closedWalk_of_faceParity_ne c w' hparity
  have hedRaw : (ed : Sym2 DualSquareVertex) ∈ w'.edges :=
    (mem_walkEdgeFinset_iff w' ed).mp hedw
  have hedEndpoints : ∀ z ∈ (ed : Sym2 DualSquareVertex),
      z ∈ brLeftmostDualFaces n := by
    intro z hz
    exact hw'Frame z (w'.mem_support_of_mem_edges hedRaw hz)
  have hedNotClosure : squareEdgeDualCrossingEquiv.symm ed ∉
      walkEdgeFinset (brLeftExteriorClosureWalk n a b) :=
    squareEdgeDualCrossingEquiv_symm_not_mem_brLeftExteriorClosureWalk
      ed hedEndpoints
  have hedPrimal : squareEdgeDualCrossingEquiv.symm ed ∈ walkEdgeFinset q := by
    have hedc' : squareEdgeDualCrossingEquiv.symm ed ∈
        walkEdgeFinset (q.append (brLeftExteriorClosureWalk n a b)) := by
      simpa only [c] using hedc
    rw [mem_walkEdgeFinset_iff, SimpleGraph.Walk.edges_append,
      List.mem_append] at hedc'
    rcases hedc' with hq | hclosure
    · exact (mem_walkEdgeFinset_iff q _).mpr hq
    · exact (hedNotClosure ((mem_walkEdgeFinset_iff _ _).mpr hclosure)).elim
  have hedAllowed : squareEdgeDualCrossingEquiv.symm ed ∈
      squareBoundaryFreeRectangleEdges (2 * n) n := hqAllowed hedPrimal
  have hedOpen : squareEdgeDualCrossingEquiv.symm ed ∈ omega := by
    have hraw := (mem_walkEdgeFinset_iff q _).mp hedPrimal
    have hopen := hqOpen _ hraw
    simpa only [Subtype.ext_iff] using hopen
  have hedRawMap := hedRaw
  simp only [w', SimpleGraph.Walk.edges_map] at hedRawMap
  rw [List.mem_map] at hedRawMap
  rcases hedRawMap with ⟨eFrame, heFrame, hmap⟩
  have heFrameGraph : eFrame ∈ (brLeftmostDualGraph n).edgeSet :=
    w.edges_subset_edgeSet heFrame
  have heExplorationOpen : eFrame ∈
      brClosedDualExplorationConfiguration n omega := hwOpen eFrame heFrame
  have hopenAlternative :=
    (mem_brClosedDualExplorationConfiguration_iff_of_mem_edgeSet
      heFrameGraph).mp heExplorationOpen
  have heEmbedded : brLeftmostDualEdgeEmbedding n ⟨eFrame, heFrameGraph⟩ = ed := by
    apply Subtype.ext
    exact hmap
  rw [heEmbedded] at hopenAlternative
  exact hopenAlternative.elim (· hedAllowed) (· hedOpen)

/-- Filling finite complementary holes does not add a bottom-row face to the right of a
normalized open crossing: all such faces are joined horizontally to the right target through
faces which the crossing already proves unreached. -/
theorem not_mem_brFilledReachableHull_of_open_normalized_crossing_bottom_face_right
    {n a b : ℕ} {omega : EdgeConfiguration 2}
    (q : squareGraph.Walk (squareVertex (a : ℤ) (-(n : ℤ)))
      (squareVertex (b : ℤ) (n : ℤ)))
    (hqOpen : walkIsOpen omega q)
    (hqAllowed : walkEdgeFinset q ⊆
      squareBoundaryFreeRectangleEdges (2 * n) n)
    (hbox : ∀ z ∈ q.support,
      0 ≤ z 0 ∧ z 0 ≤ 2 * (n : ℤ) ∧
        -(n : ℤ) ≤ z 1 ∧ z 1 ≤ (n : ℤ))
    (hunique : ∀ z ∈ q.support, z 1 = -(n : ℤ) →
      z = squareVertex (a : ℤ) (-(n : ℤ)))
    {R : Finset (BRLeftmostDualVertex n)}
    (homega : omega ∈ brReachableFaceFiber n R)
    (y : BRLeftmostDualVertex n)
    (hy₀ : (a : ℤ) ≤ y.1 0) (hy₁ : y.1 1 = -(n : ℤ)) :
    y ∉ brFilledReachableHull n R := by
  intro hyHull
  let w := brHorizontalWalkToRightTarget n y
  have hwOutside : finiteGraphWalkIsOpen (brComplementEdgeConfiguration n R) w := by
    intro e he z hz
    have hzSupport : z ∈ w.support := w.mem_support_of_mem_edges he hz
    have hzCoords := brHorizontalWalkToRightTarget_support_coordinates n y hzSupport
    have hzNotReach : z ∉ brLeftReachableFaces n omega :=
      not_mem_brLeftReachableFaces_of_open_normalized_crossing_bottom_face_right
        q hqOpen hqAllowed hbox hunique z (by omega) (by omega)
    change brLeftReachableFaces n omega = R at homega
    simpa [homega] using hzNotReach
  have hyOutside : y ∈ brRightComplementReachableFaces n R := by
    rw [brRightComplementReachableFaces,
      mem_finiteGraphReachableVertices_iff]
    refine ⟨brRightTargetAtSameHeight n y,
      brRightTargetAtSameHeight_mem_targets n y, w.reverse, ?_⟩
    intro e he
    apply hwOutside e
    simpa only [SimpleGraph.Walk.edges_reverse, List.mem_reverse] using he
  exact (Finset.mem_sdiff.mp hyHull).2 hyOutside

/-- The selected filled-hull interface starts no farther right than the unique bottom endpoint
of any normalized open bottom--top crossing in the same square. -/
theorem brSelectedBottomPrimalVertex_le_of_open_normalized_crossing
    {n a b : ℕ}
    (hn : 0 < n) {R : Finset (BRLeftmostDualVertex n)}
    (hR : BRAdmissibleSeparatingFiber n R)
    (q : squareGraph.Walk (squareVertex (a : ℤ) (-(n : ℤ)))
      (squareVertex (b : ℤ) (n : ℤ)))
    (hbox : ∀ z ∈ q.support,
      0 ≤ z 0 ∧ z 0 ≤ 2 * (n : ℤ) ∧
        -(n : ℤ) ≤ z 1 ∧ z 1 ≤ (n : ℤ))
    (hunique : ∀ z ∈ q.support, z 1 = -(n : ℤ) →
      z = squareVertex (a : ℤ) (-(n : ℤ)))
    {omega : EdgeConfiguration 2} (homega : omega ∈ brReachableFaceFiber n R)
    (hqOpen : walkIsOpen omega q)
    (hqAllowed : walkEdgeFinset q ⊆
      squareBoundaryFreeRectangleEdges (2 * n) n) :
    brSelectedBottomPrimalVertex hn hR.filledHull 0 ≤ (a : ℤ) := by
  let d := (brSelectedBottomPort hn hR.filledHull).1
  have hdBottom : d ∈ brTruncatedBottomBoundaryEdges n
      (brFilledReachableHull n R) :=
    mem_brTruncatedBottomBoundaryVertices_iff.mp
      (brSelectedBottomPort_mem hn hR.filledHull)
  have hdData := mem_brTruncatedBottomBoundaryEdges_iff.mp hdBottom
  have hdTrunc := mem_brTruncatedDualBoundaryPositiveEdges_iff.mp hdData.1
  have hvertex : brSelectedBottomPrimalVertex hn hR.filledHull 0 = d.base 0 + 1 := by
    simp [brSelectedBottomPrimalVertex, brBottomPortPrimalVertex, d,
      dualToPrimalCrossingPositiveEdge, hdData.2.1,
      cubicStepFrom, cubicDirectionIncrement]
  by_contra hle
  have hbaseRight : (a : ℤ) ≤ d.base 0 := by omega
  let x : BRLeftmostDualVertex n := ⟨d.base, hdTrunc.2.1⟩
  let y : BRLeftmostDualVertex n :=
    ⟨cubicStepFrom d.base (d.axis, true), hdTrunc.2.2.1⟩
  have hxOutside : x ∉ brFilledReachableHull n R := by
    apply not_mem_brFilledReachableHull_of_open_normalized_crossing_bottom_face_right
      q hqOpen hqAllowed hbox hunique homega x
    · exact hbaseRight
    · simpa [x] using hdData.2.2
  have hyOutside : y ∉ brFilledReachableHull n R := by
    apply not_mem_brFilledReachableHull_of_open_normalized_crossing_bottom_face_right
      q hqOpen hqAllowed hbox hunique homega y
    · have hy0 : y.1 0 = d.base 0 + 1 := by
        change Function.update d.base d.axis (d.base d.axis + 1) 0 = d.base 0 + 1
        rw [hdData.2.1]
        simp
      omega
    · simp [y, hdData.2.1, cubicStepFrom, cubicDirectionIncrement, hdData.2.2]
  have hdChange : ¬(x ∈ brFilledReachableHull n R ↔
      y ∈ brFilledReachableHull n R) := by
    have hbaseHull : brReachedDualFace n (brFilledReachableHull n R) d.base ↔
        x ∈ brFilledReachableHull n R := by
      simpa [x] using
        (brReachedDualFace_subtype_iff
          (R := brFilledReachableHull n R) (z := x))
    have hstepHull : brReachedDualFace n (brFilledReachableHull n R)
        (cubicStepFrom d.base (d.axis, true)) ↔
        y ∈ brFilledReachableHull n R := by
      simpa [y] using
        (brReachedDualFace_subtype_iff
          (R := brFilledReachableHull n R) (z := y))
    rw [brStoppedDualBoundaryEdge, hbaseHull, hstepHull] at hdTrunc
    exact hdTrunc.1
  exact hdChange (iff_of_false hxOutside hyOutside)

/-! The analogous comparison at the top endpoint is useful when two simple crossings are
spliced at their first common vertex. -/

private theorem brClosedBottomTopWalk_faceParity_ne_topFace_right
    {n a b : ℕ}
    (q : squareGraph.Walk (squareVertex (a : ℤ) (-(n : ℤ)))
      (squareVertex (b : ℤ) (n : ℤ)))
    (hbox : ∀ z ∈ q.support,
      0 ≤ z 0 ∧ z 0 ≤ 2 * (n : ℤ) ∧
        -(n : ℤ) ≤ z 1 ∧ z 1 ≤ (n : ℤ))
    (hunique : ∀ z ∈ q.support, z 1 = (n : ℤ) →
      z = squareVertex (b : ℤ) (n : ℤ))
    {x y : DualSquareVertex}
    (hx₀ : x 0 = -1) (hx₁ : -(n : ℤ) ≤ x 1) (hx₁' : x 1 < (n : ℤ))
    (hy₀ : (b : ℤ) ≤ y 0) (hy₁ : y 1 = (n : ℤ) - 1) :
    closedSquareWalkFaceParity
        (q.append (brLeftExteriorClosureWalk n a b)) x ≠
      closedSquareWalkFaceParity
        (q.append (brLeftExteriorClosureWalk n a b)) y := by
  let c := q.append (brLeftExteriorClosureWalk n a b)
  have hxOdd := odd_horizontalRayCount_of_bottom_top_walk
    q hbox x hx₀ hx₁ hx₁'
  have hxClosure := brLeftExteriorClosureWalk_horizontalRayCount_eq_zero
    (n := n) (a := a) (b := b) x (by omega)
  have hyPrimal : q.edges.countP
      (squareEdgeCrossesFaceHorizontalRayBool y) = 0 :=
    walk_horizontalRayCount_eq_zero_of_unique_top_of_face_right
      q (by simp [squareVertex]) (fun z hz ↦ (hbox z hz).2.2.2)
        hunique y hy₁ hy₀
  have hyClosure := brLeftExteriorClosureWalk_horizontalRayCount_eq_zero
    (n := n) (a := a) (b := b) y (by omega)
  have hxParity : closedSquareWalkFaceParity c x = 1 := by
    unfold closedSquareWalkFaceParity
    simp only [c, SimpleGraph.Walk.edges_append, List.countP_append,
      hxClosure, add_zero]
    exact Nat.odd_iff.mp hxOdd
  have hyParity : closedSquareWalkFaceParity c y = 0 := by
    unfold closedSquareWalkFaceParity
    simp only [c, SimpleGraph.Walk.edges_append, List.countP_append,
      hyPrimal, hyClosure, zero_add, Nat.zero_mod]
  rw [hxParity, hyParity]
  norm_num

/-- No top-row dual face weakly to the right of the unique top endpoint of an open normalized
crossing is reachable by the stopped closed-dual exploration. -/
theorem not_mem_brLeftReachableFaces_of_open_normalized_crossing_top_face_right
    {n a b : ℕ} {omega : EdgeConfiguration 2}
    (q : squareGraph.Walk (squareVertex (a : ℤ) (-(n : ℤ)))
      (squareVertex (b : ℤ) (n : ℤ)))
    (hqOpen : walkIsOpen omega q)
    (hqAllowed : walkEdgeFinset q ⊆
      squareBoundaryFreeRectangleEdges (2 * n) n)
    (hbox : ∀ z ∈ q.support,
      0 ≤ z 0 ∧ z 0 ≤ 2 * (n : ℤ) ∧
        -(n : ℤ) ≤ z 1 ∧ z 1 ≤ (n : ℤ))
    (hunique : ∀ z ∈ q.support, z 1 = (n : ℤ) →
      z = squareVertex (b : ℤ) (n : ℤ))
    (y : BRLeftmostDualVertex n)
    (hy₀ : (b : ℤ) ≤ y.1 0) (hy₁ : y.1 1 = (n : ℤ) - 1) :
    y ∉ brLeftReachableFaces n omega := by
  classical
  intro hyReach
  rw [brLeftReachableFaces, mem_finiteGraphReachableVertices_iff] at hyReach
  rcases hyReach with ⟨x, hxSource, w, hwOpen⟩
  let w' := w.map (brLeftmostDualToAmbientHom n)
  have hw'Frame : ∀ z ∈ w'.support, z ∈ brLeftmostDualFaces n := by
    intro z hz
    simp only [w', SimpleGraph.Walk.support_map, List.mem_map] at hz
    rcases hz with ⟨zFrame, _hzFrame, rfl⟩
    exact zFrame.2
  have hxFrame := mem_brLeftmostDualFaces_iff.mp x.2
  have hx₀ : x.1 0 = -1 := mem_brLeftmostDualSources_iff.mp hxSource
  let c := q.append (brLeftExteriorClosureWalk n a b)
  have hparity : closedSquareWalkFaceParity c x.1 ≠
      closedSquareWalkFaceParity c y.1 := by
    exact brClosedBottomTopWalk_faceParity_ne_topFace_right
      q hbox hunique hx₀ hxFrame.2.2.1 hxFrame.2.2.2 hy₀ hy₁
  obtain ⟨ed, hedw, hedc⟩ :=
    exists_dualWalk_edge_crossing_closedWalk_of_faceParity_ne c w' hparity
  have hedRaw : (ed : Sym2 DualSquareVertex) ∈ w'.edges :=
    (mem_walkEdgeFinset_iff w' ed).mp hedw
  have hedEndpoints : ∀ z ∈ (ed : Sym2 DualSquareVertex),
      z ∈ brLeftmostDualFaces n := by
    intro z hz
    exact hw'Frame z (w'.mem_support_of_mem_edges hedRaw hz)
  have hedNotClosure : squareEdgeDualCrossingEquiv.symm ed ∉
      walkEdgeFinset (brLeftExteriorClosureWalk n a b) :=
    squareEdgeDualCrossingEquiv_symm_not_mem_brLeftExteriorClosureWalk
      ed hedEndpoints
  have hedPrimal : squareEdgeDualCrossingEquiv.symm ed ∈ walkEdgeFinset q := by
    have hedc' : squareEdgeDualCrossingEquiv.symm ed ∈
        walkEdgeFinset (q.append (brLeftExteriorClosureWalk n a b)) := by
      simpa only [c] using hedc
    rw [mem_walkEdgeFinset_iff, SimpleGraph.Walk.edges_append,
      List.mem_append] at hedc'
    rcases hedc' with hq | hclosure
    · exact (mem_walkEdgeFinset_iff q _).mpr hq
    · exact (hedNotClosure ((mem_walkEdgeFinset_iff _ _).mpr hclosure)).elim
  have hedAllowed : squareEdgeDualCrossingEquiv.symm ed ∈
      squareBoundaryFreeRectangleEdges (2 * n) n := hqAllowed hedPrimal
  have hedOpen : squareEdgeDualCrossingEquiv.symm ed ∈ omega := by
    have hraw := (mem_walkEdgeFinset_iff q _).mp hedPrimal
    have hopen := hqOpen _ hraw
    simpa only [Subtype.ext_iff] using hopen
  have hedRawMap := hedRaw
  simp only [w', SimpleGraph.Walk.edges_map] at hedRawMap
  rw [List.mem_map] at hedRawMap
  rcases hedRawMap with ⟨eFrame, heFrame, hmap⟩
  have heFrameGraph : eFrame ∈ (brLeftmostDualGraph n).edgeSet :=
    w.edges_subset_edgeSet heFrame
  have heExplorationOpen : eFrame ∈
      brClosedDualExplorationConfiguration n omega := hwOpen eFrame heFrame
  have hopenAlternative :=
    (mem_brClosedDualExplorationConfiguration_iff_of_mem_edgeSet
      heFrameGraph).mp heExplorationOpen
  have heEmbedded : brLeftmostDualEdgeEmbedding n ⟨eFrame, heFrameGraph⟩ = ed := by
    apply Subtype.ext
    exact hmap
  rw [heEmbedded] at hopenAlternative
  exact hopenAlternative.elim (· hedAllowed) (· hedOpen)

/-- Filling finite complementary holes does not add a top-row face to the right of a normalized
open crossing. -/
theorem not_mem_brFilledReachableHull_of_open_normalized_crossing_top_face_right
    {n a b : ℕ} {omega : EdgeConfiguration 2}
    (q : squareGraph.Walk (squareVertex (a : ℤ) (-(n : ℤ)))
      (squareVertex (b : ℤ) (n : ℤ)))
    (hqOpen : walkIsOpen omega q)
    (hqAllowed : walkEdgeFinset q ⊆
      squareBoundaryFreeRectangleEdges (2 * n) n)
    (hbox : ∀ z ∈ q.support,
      0 ≤ z 0 ∧ z 0 ≤ 2 * (n : ℤ) ∧
        -(n : ℤ) ≤ z 1 ∧ z 1 ≤ (n : ℤ))
    (hunique : ∀ z ∈ q.support, z 1 = (n : ℤ) →
      z = squareVertex (b : ℤ) (n : ℤ))
    {R : Finset (BRLeftmostDualVertex n)}
    (homega : omega ∈ brReachableFaceFiber n R)
    (y : BRLeftmostDualVertex n)
    (hy₀ : (b : ℤ) ≤ y.1 0) (hy₁ : y.1 1 = (n : ℤ) - 1) :
    y ∉ brFilledReachableHull n R := by
  intro hyHull
  let w := brHorizontalWalkToRightTarget n y
  have hwOutside : finiteGraphWalkIsOpen (brComplementEdgeConfiguration n R) w := by
    intro e he z hz
    have hzSupport : z ∈ w.support := w.mem_support_of_mem_edges he hz
    have hzCoords := brHorizontalWalkToRightTarget_support_coordinates n y hzSupport
    have hzNotReach : z ∉ brLeftReachableFaces n omega :=
      not_mem_brLeftReachableFaces_of_open_normalized_crossing_top_face_right
        q hqOpen hqAllowed hbox hunique z (by omega) (by omega)
    change brLeftReachableFaces n omega = R at homega
    simpa [homega] using hzNotReach
  have hyOutside : y ∈ brRightComplementReachableFaces n R := by
    rw [brRightComplementReachableFaces,
      mem_finiteGraphReachableVertices_iff]
    refine ⟨brRightTargetAtSameHeight n y,
      brRightTargetAtSameHeight_mem_targets n y, w.reverse, ?_⟩
    intro e he
    apply hwOutside e
    simpa only [SimpleGraph.Walk.edges_reverse, List.mem_reverse] using he
  exact (Finset.mem_sdiff.mp hyHull).2 hyOutside

/-- The selected filled-hull interface ends no farther right than the unique top endpoint of
any normalized open bottom--top crossing in the same square. -/
theorem brSelectedTopPrimalVertex_le_of_open_normalized_crossing
    {n a b : ℕ}
    (hn : 0 < n) {R : Finset (BRLeftmostDualVertex n)}
    (hR : BRAdmissibleSeparatingFiber n R)
    (q : squareGraph.Walk (squareVertex (a : ℤ) (-(n : ℤ)))
      (squareVertex (b : ℤ) (n : ℤ)))
    (hbox : ∀ z ∈ q.support,
      0 ≤ z 0 ∧ z 0 ≤ 2 * (n : ℤ) ∧
        -(n : ℤ) ≤ z 1 ∧ z 1 ≤ (n : ℤ))
    (hunique : ∀ z ∈ q.support, z 1 = (n : ℤ) →
      z = squareVertex (b : ℤ) (n : ℤ))
    {omega : EdgeConfiguration 2} (homega : omega ∈ brReachableFaceFiber n R)
    (hqOpen : walkIsOpen omega q)
    (hqAllowed : walkEdgeFinset q ⊆
      squareBoundaryFreeRectangleEdges (2 * n) n) :
    brSelectedTopPrimalVertex hn hR.filledHull 0 ≤ (b : ℤ) := by
  let d := (brSelectedTopPort hn hR.filledHull).1
  have hdTop : d ∈ brTruncatedTopBoundaryEdges n
      (brFilledReachableHull n R) :=
    mem_brTruncatedTopBoundaryVertices_iff.mp
      (brSelectedTopPort_mem hn hR.filledHull)
  have hdData := mem_brTruncatedTopBoundaryEdges_iff.mp hdTop
  have hdTrunc := mem_brTruncatedDualBoundaryPositiveEdges_iff.mp hdData.1
  have hvertex : brSelectedTopPrimalVertex hn hR.filledHull 0 = d.base 0 + 1 := by
    simp [brSelectedTopPrimalVertex, brTopPortPrimalVertex, d,
      dualToPrimalCrossingPositiveEdge, hdData.2.1,
      cubicStepFrom, cubicDirectionIncrement]
  by_contra hle
  have hbaseRight : (b : ℤ) ≤ d.base 0 := by omega
  let x : BRLeftmostDualVertex n := ⟨d.base, hdTrunc.2.1⟩
  let y : BRLeftmostDualVertex n :=
    ⟨cubicStepFrom d.base (d.axis, true), hdTrunc.2.2.1⟩
  have hxOutside : x ∉ brFilledReachableHull n R := by
    apply not_mem_brFilledReachableHull_of_open_normalized_crossing_top_face_right
      q hqOpen hqAllowed hbox hunique homega x
    · exact hbaseRight
    · simpa [x] using hdData.2.2
  have hyOutside : y ∉ brFilledReachableHull n R := by
    apply not_mem_brFilledReachableHull_of_open_normalized_crossing_top_face_right
      q hqOpen hqAllowed hbox hunique homega y
    · have hy0 : y.1 0 = d.base 0 + 1 := by
        change Function.update d.base d.axis (d.base d.axis + 1) 0 = d.base 0 + 1
        rw [hdData.2.1]
        simp
      omega
    · simp [y, hdData.2.1, cubicStepFrom, cubicDirectionIncrement, hdData.2.2]
  have hdChange : ¬(x ∈ brFilledReachableHull n R ↔
      y ∈ brFilledReachableHull n R) := by
    have hbaseHull : brReachedDualFace n (brFilledReachableHull n R) d.base ↔
        x ∈ brFilledReachableHull n R := by
      simpa [x] using
        (brReachedDualFace_subtype_iff
          (R := brFilledReachableHull n R) (z := x))
    have hstepHull : brReachedDualFace n (brFilledReachableHull n R)
        (cubicStepFrom d.base (d.axis, true)) ↔
        y ∈ brFilledReachableHull n R := by
      simpa [y] using
        (brReachedDualFace_subtype_iff
          (R := brFilledReachableHull n R) (z := y))
    rw [brStoppedDualBoundaryEdge, hbaseHull, hstepHull] at hdTrunc
    exact hdTrunc.1
  exact hdChange (iff_of_false hxOutside hyOutside)

/-- If the open configuration contains a normalized simple crossing with a specified upper
tail, then the last midline point of the filled stopped interface lies weakly to the left of
that tail endpoint. -/
private theorem brFilledHullLastMidlineVertex_le_of_nested_exact_crossing
    {n a b c : ℕ} (hn : 0 < n)
    {R : Finset (BRLeftmostDualVertex n)}
    (hR : BRAdmissibleSeparatingFiber n R)
    {omega : EdgeConfiguration 2}
    (homega : omega ∈ brReachableFaceFiber n R)
    (q : squareGraph.Walk (squareVertex (a : ℤ) (-(n : ℤ)))
      (squareVertex (b : ℤ) (n : ℤ)))
    (hqPath : q.IsPath)
    (hqOpen : walkIsOpen omega q)
    (hqAllowed : walkEdgeFinset q ⊆
      squareBoundaryFreeRectangleEdges (2 * n) n)
    (hqBox : ∀ z ∈ q.support,
      0 ≤ z 0 ∧ z 0 ≤ 2 * (n : ℤ) ∧
        -(n : ℤ) ≤ z 1 ∧ z 1 ≤ (n : ℤ))
    (hqBottom : ∀ z ∈ q.support, z 1 = -(n : ℤ) →
      z = squareVertex (a : ℤ) (-(n : ℤ)))
    (hqTop : ∀ z ∈ q.support, z 1 = (n : ℤ) →
      z = squareVertex (b : ℤ) (n : ℤ))
    (t : squareGraph.Walk (squareVertex (b : ℤ) (n : ℤ))
      (squareVertex (c : ℤ) 0))
    (htPath : t.IsPath)
    (htBox : ∀ z ∈ t.support,
      0 ≤ z 0 ∧ z 0 ≤ 2 * (n : ℤ) ∧ 0 ≤ z 1 ∧ z 1 ≤ (n : ℤ))
    (htBottom : ∀ z ∈ t.support, z 1 = 0 →
      z = squareVertex (c : ℤ) 0)
    (htTop : ∀ z ∈ t.support, z 1 = (n : ℤ) →
      z = squareVertex (b : ℤ) (n : ℤ))
    (htPrefix : t.edges <+: q.reverse.edges) :
    brFilledHullLastMidlineVertex hn hR 0 ≤ (c : ℤ) := by
  classical
  let eta : EdgeConfiguration 2 := {e | e ∈ walkEdgeFinset q}
  let K := brLeftReachableFaces n eta
  have hetaOpen : walkIsOpen eta q := by
    intro e he
    let ee : SquareEdge := ⟨e, q.edges_subset_edgeSet he⟩
    exact (mem_walkEdgeFinset_iff q ee).mpr he
  have hetaOmega : eta ⊆ omega := by
    intro e he
    have heFin : e ∈ walkEdgeFinset q := he
    exact hqOpen _ ((mem_walkEdgeFinset_iff q e).mp heFin)
  obtain ⟨hK, _hKBottom, hKTop, hKEdges⟩ :=
    brSelectedPrimalWalk_filledHull_eq_of_exact_crossing
      hn q hqPath hqAllowed hqBox hqBottom hqTop
  have hReach : R ⊆ K := by
    have hanti := brLeftReachableFaces_anti (n := n) hetaOmega
    change brLeftReachableFaces n omega = R at homega
    simpa [K, homega] using hanti
  have hHull : brFilledReachableHull n R ⊆ brFilledReachableHull n K :=
    brFilledReachableHull_mono hReach
  by_contra hle
  have hlastRight : (c : ℤ) < brFilledHullLastMidlineVertex hn hR 0 := by
    omega
  obtain ⟨dTop, dMid, hdTopCross, hdMidCross, w, hw⟩ :=
    exists_filledSideWalk_of_selectedUpperTail hn hR
  let u := brFilledHullSelectedUpperTailPath hn hR
  have htopSide := mem_brSquareTopSide_iff.mp
    (brSelectedTopPrimalVertex_mem_topSide hn hR.filledHull)
  have hlastCoords := brFilledHullLastMidlineVertex_coordinates hn hR
  have htopNeLast : brSelectedTopPrimalVertex hn hR.filledHull ≠
      brFilledHullLastMidlineVertex hn hR := by
    intro h
    have h1 := congrFun h 1
    omega
  have huNil : ¬u.Nil := SimpleGraph.Walk.not_nil_of_ne htopNeLast
  have huFirst : s(brSelectedTopPrimalVertex hn hR.filledHull, u.snd) ∈ u.edges :=
    u.mk_start_snd_mem_edges huNil
  have huSndSupport : u.snd ∈ u.support :=
    u.snd_mem_support_of_mem_edges huFirst
  have huSndSelected := brFilledHullSelectedUpperTailPath_support_subset_selected
    hn hR u.snd huSndSupport
  have huSndCoords := brSelectedPrimalWalk_support_coordinates
    hn hR.filledHull huSndSelected
  have huAdj : squareGraph.Adj (brSelectedTopPrimalVertex hn hR.filledHull) u.snd :=
    u.adj_snd huNil
  let first : SquareEdge :=
    ⟨s(brSelectedTopPrimalVertex hn hR.filledHull, u.snd),
      squareGraph.mem_edgeSet.mpr huAdj⟩
  have hfirstWalk : first ∈ walkEdgeFinset u :=
    (mem_walkEdgeFinset_iff u first).mpr huFirst
  have hfirstAllowed :=
    walkEdgeFinset_brFilledHullSelectedUpperTailPath_subset_boundaryFree
      hn hR hfirstWalk
  have huSndRect : u.snd ∈ squareRectangleVertices (2 * n) n := by
    rw [squareBoundaryFreeRectangleEdges, Finset.mem_filter] at hfirstAllowed
    exact endpoint_mem_squareRectangle_of_edge_mem hfirstAllowed.1 (by simp [first])
  have huSndNotBoundary : ¬ squareRectangleBoundaryVertex (2 * n) n u.snd := by
    intro hsndBoundary
    rw [squareBoundaryFreeRectangleEdges, Finset.mem_filter] at hfirstAllowed
    apply hfirstAllowed.2
    constructor
    · have hout := Sym2.out_fst_mem first.1
      simp only [first, Sym2.mem_iff] at hout
      rcases hout with hout | hout
      · rw [hout]
        exact Or.inr (Or.inr (Or.inr htopSide.2.2))
      · rw [hout]
        exact hsndBoundary
    · have hout := Sym2.out_snd_mem first.1
      simp only [first, Sym2.mem_iff] at hout
      rcases hout with hout | hout
      · rw [hout]
        exact Or.inr (Or.inr (Or.inr htopSide.2.2))
      · rw [hout]
        exact hsndBoundary
  have huSndNotTop : u.snd 1 ≠ (n : ℤ) := by
    intro hsndTop
    exact huSndNotBoundary (Or.inr (Or.inr (Or.inr hsndTop)))
  have huSndShape : u.snd =
      squareVertex (brSelectedTopPrimalVertex hn hR.filledHull 0) ((n : ℤ) - 1) := by
    rcases (cubicGraph_adj_iff_exists_stepFrom _ _).mp huAdj with ⟨⟨i, s⟩, hs⟩
    fin_cases i <;> cases s <;>
      have hs0 := congrFun hs 0 <;>
      have hs1 := congrFun hs 1 <;>
      simp [cubicStepFrom, cubicDirectionIncrement] at hs0 hs1 <;>
      ext j <;> fin_cases j <;> simp [squareVertex] <;> omega
  have htopShape : brSelectedTopPrimalVertex hn hR.filledHull =
      squareVertex (brSelectedTopPrimalVertex hn hR.filledHull 0) (n : ℤ) := by
    ext i
    fin_cases i <;> simp [htopSide.2.2]
  have hdTopVertical :
      ((dualToPrimalCrossingPositiveEdge dTop.1).toEdge : Sym2 SquareVertex) =
        s(squareVertex (brSelectedTopPrimalVertex hn hR.filledHull 0) (n : ℤ),
          squareVertex (brSelectedTopPrimalVertex hn hR.filledHull 0) ((n : ℤ) - 1)) := by
    change (brTruncatedInterfacePrimalEdge dTop : Sym2 SquareVertex) = _
    calc
      (brTruncatedInterfacePrimalEdge dTop : Sym2 SquareVertex) =
          s(brSelectedTopPrimalVertex hn hR.filledHull, u.snd) := hdTopCross
      _ = s(squareVertex (brSelectedTopPrimalVertex hn hR.filledHull 0) (n : ℤ),
          u.snd) := congrArg
            (fun z ↦ s(z, u.snd)) htopShape
      _ = s(squareVertex (brSelectedTopPrimalVertex hn hR.filledHull 0) (n : ℤ),
          squareVertex (brSelectedTopPrimalVertex hn hR.filledHull 0)
            ((n : ℤ) - 1)) := congrArg
              (fun z ↦ s(squareVertex
                (brSelectedTopPrimalVertex hn hR.filledHull 0) (n : ℤ), z)) huSndShape
  have hdTopVertical' :
      ((dualToPrimalCrossingPositiveEdge dTop.1).toEdge : Sym2 SquareVertex) =
        s(squareVertex (brSelectedTopPrimalVertex hn hR.filledHull 0)
            (((n : ℤ) - 1) + 1),
          squareVertex (brSelectedTopPrimalVertex hn hR.filledHull 0) ((n : ℤ) - 1)) := by
    have hy : ((n : ℤ) - 1) + 1 = (n : ℤ) := by omega
    simpa only [hy] using hdTopVertical
  let fTop := squareCellBoundaryTrueEndpoint
    (brReachedDualFace n (brFilledReachableHull n R)) dTop.1
  have hfTopCoords := squareCellBoundaryTrueEndpoint_crossedVertical_coordinates
    (brReachedDualFace n (brFilledReachableHull n R)) dTop.1 hdTopVertical'
  dsimp only [fTop] at hfTopCoords
  have huLast : s(u.penultimate, brFilledHullLastMidlineVertex hn hR) ∈ u.edges :=
    u.mk_penultimate_end_mem_edges huNil
  have huPenSupport : u.penultimate ∈ u.support :=
    u.fst_mem_support_of_mem_edges huLast
  have huPenNonnegative := brFilledHullSelectedUpperTailPath_support_nonnegative
    hn hR huPenSupport
  have huPenAdj : squareGraph.Adj u.penultimate
      (brFilledHullLastMidlineVertex hn hR) := u.adj_penultimate huNil
  have huPenPositive : 0 < u.penultimate 1 := by
    by_contra hnot
    have hzero : u.penultimate 1 = 0 := by omega
    have heq := brFilledHullSelectedUpperTailPath_midline_unique hn hR huPenSupport hzero
    exact huPenAdj.ne heq
  have huPenShape : u.penultimate =
      squareVertex (brFilledHullLastMidlineVertex hn hR 0) 1 := by
    rcases (cubicGraph_adj_iff_exists_stepFrom _ _).mp huPenAdj with ⟨⟨i, s⟩, hs⟩
    fin_cases i <;> cases s <;>
      have hs0 := congrFun hs 0 <;>
      have hs1 := congrFun hs 1 <;>
      simp [cubicStepFrom, cubicDirectionIncrement] at hs0 hs1 <;>
      ext j <;> fin_cases j <;> simp [squareVertex] <;> omega
  have hlastShape : brFilledHullLastMidlineVertex hn hR =
      squareVertex (brFilledHullLastMidlineVertex hn hR 0) 0 := by
    ext i
    fin_cases i <;> simp [brFilledHullLastMidlineVertex_one hn hR]
  have hdMidVertical :
      ((dualToPrimalCrossingPositiveEdge dMid.1).toEdge : Sym2 SquareVertex) =
        s(squareVertex (brFilledHullLastMidlineVertex hn hR 0) 1,
          squareVertex (brFilledHullLastMidlineVertex hn hR 0) 0) := by
    change (brTruncatedInterfacePrimalEdge dMid : Sym2 SquareVertex) = _
    calc
      (brTruncatedInterfacePrimalEdge dMid : Sym2 SquareVertex) =
          s(u.penultimate, brFilledHullLastMidlineVertex hn hR) := hdMidCross
      _ = s(squareVertex (brFilledHullLastMidlineVertex hn hR 0) 1,
          brFilledHullLastMidlineVertex hn hR) := congrArg
            (fun z ↦ s(z, brFilledHullLastMidlineVertex hn hR)) huPenShape
      _ = s(squareVertex (brFilledHullLastMidlineVertex hn hR 0) 1,
          squareVertex (brFilledHullLastMidlineVertex hn hR 0) 0) := congrArg
            (fun z ↦ s(squareVertex
              (brFilledHullLastMidlineVertex hn hR 0) 1, z)) hlastShape
  have hdMidVertical' :
      ((dualToPrimalCrossingPositiveEdge dMid.1).toEdge : Sym2 SquareVertex) =
        s(squareVertex (brFilledHullLastMidlineVertex hn hR 0) ((0 : ℤ) + 1),
          squareVertex (brFilledHullLastMidlineVertex hn hR 0) 0) := by
    simpa only [Int.zero_add] using hdMidVertical
  let fMid := squareCellBoundaryTrueEndpoint
    (brReachedDualFace n (brFilledReachableHull n R)) dMid.1
  have hfMidCoords := squareCellBoundaryTrueEndpoint_crossedVertical_coordinates
    (brReachedDualFace n (brFilledReachableHull n R)) dMid.1 hdMidVertical'
  dsimp only [fMid] at hfMidCoords
  have hfTopHStatus : brReachedDualFace n (brFilledReachableHull n R) fTop :=
    (hw fTop w.start_mem_support).1
  have hfTopFrame : fTop ∈ brLeftmostDualFaces n :=
    brReachedFaceCoordinates_subset_brLeftmostDualFaces hfTopHStatus
  let fTop' : BRLeftmostDualVertex n := ⟨fTop, hfTopFrame⟩
  have hfTopH : fTop' ∈ brFilledReachableHull n R := by
    simpa [fTop'] using
      (brReachedDualFace_subtype_iff
        (R := brFilledReachableHull n R) (z := fTop')).mp hfTopHStatus
  have htopLe : brSelectedTopPrimalVertex hn hR.filledHull 0 ≤ (b : ℤ) :=
    brSelectedTopPrimalVertex_le_of_open_normalized_crossing
      hn hR q hqBox hqTop homega hqOpen hqAllowed
  have hetaFiber : eta ∈ brReachableFaceFiber n K := by
    exact mem_brReachableFaceFiber_self n eta
  have hfTopLt : fTop 0 < (b : ℤ) := by
    by_contra hnot
    have hfTopNotK : fTop' ∉ brFilledReachableHull n K := by
      apply not_mem_brFilledReachableHull_of_open_normalized_crossing_top_face_right
        q hetaOpen hqAllowed hqBox hqTop hetaFiber fTop'
      · change (b : ℤ) ≤ fTop 0
        omega
      · exact hfTopCoords.1
    exact hfTopNotK (hHull hfTopH)
  have hfTopLower : -1 ≤ fTop 0 :=
    (mem_brLeftmostDualFaces_iff.mp hfTopFrame).1
  have hfMidRight : (c : ℤ) ≤ fMid 0 := by
    dsimp only [fMid]
    omega
  let lower := brMidlineLowerExtensionWalk n c
  let p := lower.append t.reverse
  let closed := p.append (brLeftExteriorClosureWalk n c b)
  have hparity : closedSquareWalkFaceParity closed fTop ≠
      closedSquareWalkFaceParity closed fMid := by
    simpa [closed, p, lower] using brCompletedUpperTail_faceParity_ne
      hn t htPath htBox htBottom htTop hfTopLower hfTopLt hfTopCoords.1
        hfMidRight hfMidCoords.1
  obtain ⟨ed, hedW, hedC⟩ :=
    exists_dualWalk_edge_crossing_closedWalk_of_faceParity_ne closed w hparity
  have hedRaw : (ed : Sym2 DualSquareVertex) ∈ w.edges :=
    (mem_walkEdgeFinset_iff w ed).mp hedW
  have hedNonnegative : ∀ z ∈ (ed : Sym2 DualSquareVertex), 0 ≤ z 1 := by
    intro z hz
    exact (hw z (w.mem_support_of_mem_edges hedRaw hz)).2
  have hedFrame : ∀ z ∈ (ed : Sym2 DualSquareVertex),
      z ∈ brLeftmostDualFaces n := by
    intro z hz
    exact brReachedFaceCoordinates_subset_brLeftmostDualFaces
      (hw z (w.mem_support_of_mem_edges hedRaw hz)).1
  have hedNotClosure : squareEdgeDualCrossingEquiv.symm ed ∉
      walkEdgeFinset (brLeftExteriorClosureWalk n c b) :=
    squareEdgeDualCrossingEquiv_symm_not_mem_brLeftExteriorClosureWalk ed hedFrame
  have hedNotLower : squareEdgeDualCrossingEquiv.symm ed ∉
      walkEdgeFinset lower := by
    simpa [lower] using
      squareEdgeDualCrossingEquiv_symm_not_mem_brMidlineLowerExtensionWalk
        ed hedNonnegative
  have hedTailRaw : (squareEdgeDualCrossingEquiv.symm ed : Sym2 SquareVertex) ∈
      t.reverse.edges := by
    have hedC' : squareEdgeDualCrossingEquiv.symm ed ∈ walkEdgeFinset closed := hedC
    rw [mem_walkEdgeFinset_iff] at hedC'
    change (squareEdgeDualCrossingEquiv.symm ed : Sym2 SquareVertex) ∈
      (p.append (brLeftExteriorClosureWalk n c b)).edges at hedC'
    rw [SimpleGraph.Walk.edges_append, List.mem_append] at hedC'
    rcases hedC' with hedP | hedClosure
    · change (squareEdgeDualCrossingEquiv.symm ed : Sym2 SquareVertex) ∈
        (lower.append t.reverse).edges at hedP
      rw [SimpleGraph.Walk.edges_append, List.mem_append] at hedP
      rcases hedP with hedLower | hedTail
      · exact (hedNotLower ((mem_walkEdgeFinset_iff lower _).mpr hedLower)).elim
      · exact hedTail
    · exact (hedNotClosure
        ((mem_walkEdgeFinset_iff (brLeftExteriorClosureWalk n c b) _).mpr
          hedClosure)).elim
  have hedQRaw : (squareEdgeDualCrossingEquiv.symm ed : Sym2 SquareVertex) ∈
      q.edges := by
    have hedTRaw : (squareEdgeDualCrossingEquiv.symm ed : Sym2 SquareVertex) ∈
        t.edges := by
      simpa only [SimpleGraph.Walk.edges_reverse, List.mem_reverse] using hedTailRaw
    have h := htPrefix.sublist.subset hedTRaw
    simpa only [SimpleGraph.Walk.edges_reverse, List.mem_reverse] using h
  have hedKSelected : squareEdgeDualCrossingEquiv.symm ed ∈
      walkEdgeFinset (brSelectedPrimalWalk hn hK.filledHull) := by
    rw [mem_walkEdgeFinset_iff, hKEdges]
    exact hedQRaw
  have hedKInterface :=
    walkEdgeFinset_brSelectedPrimalWalk_subset_interface hn hK.filledHull
      hedKSelected
  rcases mem_brTruncatedInterfacePrimalEdges_iff.mp hedKInterface with
    ⟨dK, hdKEq⟩
  have hcrossK : squareEdgeDualCrossingEquiv
      (brTruncatedInterfacePrimalEdge dK) = dK.1.toEdge := by
    simpa [squarePositiveEdgeDualCrossingEmbedding,
      brTruncatedInterfacePrimalEdge] using
      (squarePositiveEdgeDualCrossingEmbedding_brTruncatedInterfacePrimalEdge dK)
  have hedDualEq : ed = dK.1.toEdge := by
    calc
      ed = squareEdgeDualCrossingEquiv (squareEdgeDualCrossingEquiv.symm ed) :=
        (squareEdgeDualCrossingEquiv.apply_symm_apply ed).symm
      _ = squareEdgeDualCrossingEquiv (brTruncatedInterfacePrimalEdge dK) := by
        exact congrArg squareEdgeDualCrossingEquiv hdKEq.symm
      _ = dK.1.toEdge := hcrossK
  have hedKStatus : ∀ z ∈ (ed : Sym2 DualSquareVertex),
      brReachedDualFace n (brFilledReachableHull n K) z := by
    intro z hz
    have hzHStatus := (hw z (w.mem_support_of_mem_edges hedRaw hz)).1
    have hzFrame := brReachedFaceCoordinates_subset_brLeftmostDualFaces hzHStatus
    let z' : BRLeftmostDualVertex n := ⟨z, hzFrame⟩
    have hzH : z' ∈ brFilledReachableHull n R := by
      simpa [z'] using
        (brReachedDualFace_subtype_iff
          (R := brFilledReachableHull n R) (z := z')).mp hzHStatus
    have hzK := hHull hzH
    simpa [z'] using
      (brReachedDualFace_subtype_iff
        (R := brFilledReachableHull n K) (z := z')).mpr hzK
  have hbaseK : brReachedDualFace n (brFilledReachableHull n K) dK.1.base := by
    apply hedKStatus dK.1.base
    rw [hedDualEq]
    simp [SquarePositiveEdge.toEdge]
  have hstepK : brReachedDualFace n (brFilledReachableHull n K)
      (cubicStepFrom dK.1.base (dK.1.axis, true)) := by
    apply hedKStatus (cubicStepFrom dK.1.base (dK.1.axis, true))
    rw [hedDualEq]
    simp [SquarePositiveEdge.toEdge]
  exact dK.toStopped.2 (iff_of_true hbaseK hstepK)

/-! ### The endpoint-split event in stopped-exploration coordinates -/

/-- Quarter-turned lower-last-midline crossings, in the centered coordinates used by the
stopped BR exploration. -/
def brSquareLastMidlineLeftCrossingEvent (n : ℕ) : Set (EdgeConfiguration 2) :=
  cubicGraphIsoEvent (brSquareQuarterTurnIso n)
    (rswSquareLowerLastMidlineCrossingEvent n)

theorem measurableSet_brSquareLastMidlineLeftCrossingEvent (n : ℕ) :
    MeasurableSet (brSquareLastMidlineLeftCrossingEvent n) :=
  measurableSet_cubicGraphIsoEvent _
    (measurableSet_rswSquareLowerLastMidlineCrossingEvent n)

theorem isIncreasingEvent_brSquareLastMidlineLeftCrossingEvent (n : ℕ) :
    IsIncreasingEvent (brSquareLastMidlineLeftCrossingEvent n) :=
  isIncreasingEvent_cubicGraphIsoEvent _
    (isIncreasingEvent_rswSquareLowerLastMidlineCrossingEvent n)

theorem one_sub_sqrt_rswSquare_le_brSquareLastMidlineLeftCrossingProbability
    (p : I) (n : ℕ) :
    1 - Real.sqrt (1 - rswSquareCrossingProbability p n) ≤
      (bernoulliBondMeasure 2 p).real
        (brSquareLastMidlineLeftCrossingEvent n) := by
  rw [brSquareLastMidlineLeftCrossingEvent,
    bernoulliBondMeasure_real_cubicGraphIsoEvent p _
      (measurableSet_rswSquareLowerLastMidlineCrossingEvent n)]
  exact one_sub_sqrt_rswSquare_le_lowerLastMidlineCrossingProbability p n

/-- On every realized stopped fiber, a quarter-turned lower-last-midline crossing forces the
fiber-selected filled interface to make its last midline visit in the left half. -/
theorem brFilledHullLastMidlineLeft_of_mem_lastMidlineLeftCrossingEvent
    {n : ℕ} (hn : 0 < n)
    {R : Finset (BRLeftmostDualVertex n)}
    (hR : BRAdmissibleSeparatingFiber n R)
    {omega : EdgeConfiguration 2}
    (homegaFiber : omega ∈ brReachableFaceFiber n R)
    (homegaEvent : omega ∈ brSquareLastMidlineLeftCrossingEvent n) :
    BRFilledHullLastMidlineLeft hn hR := by
  classical
  let F := brSquareQuarterTurnIso n
  change cubicGraphIsoConfigurationPullback F omega ∈
    rswSquareLowerLastMidlineCrossingEvent n at homegaEvent
  simp only [rswSquareLowerLastMidlineCrossingEvent] at homegaEvent
  obtain ⟨x, hxRest⟩ := homegaEvent
  obtain ⟨hx, hxyRest⟩ := hxRest
  obtain ⟨y, hyRest⟩ := hxyRest
  obtain ⟨hy, hqExists⟩ := hyRest
  obtain ⟨q, hqData⟩ := hqExists
  obtain ⟨hqPath, hqRest⟩ := hqData
  obtain ⟨hqOpen, hqRest⟩ := hqRest
  obtain ⟨hqAllowed, hqRest⟩ := hqRest
  obtain ⟨hqLeft, hqRest⟩ := hqRest
  obtain ⟨hqRight, hzExists⟩ := hqRest
  obtain ⟨z, hzRest⟩ := hzExists
  obtain ⟨hz, htExists⟩ := hzRest
  obtain ⟨t, htData⟩ := htExists
  obtain ⟨htPrefix, htRest⟩ := htData
  obtain ⟨htSupport, htUnique⟩ := htRest
  have hx' := mem_squareRectangleLeft_iff.mp hx
  have hy' := mem_squareRectangleRight_iff.mp hy
  have hz' := mem_rswSquareLowerMidline_iff.mp hz
  have hyRect : y ∈ squareRectangleVertices (2 * n) n :=
    (Finset.mem_filter.mp hy).1
  have hqRect : ∀ v ∈ q.support, v ∈ squareRectangleVertices (2 * n) n :=
    walk_support_mem_squareRectangle_of_boundaryFree_edges q hyRect hqAllowed
  have hFxBounds : 0 ≤ F x 0 ∧ F x 0 ≤ 2 * (n : ℤ) := by
    simp only [F, brSquareQuarterTurnIso_zero]
    omega
  have hFyBounds : 0 ≤ F y 0 ∧ F y 0 ≤ 2 * (n : ℤ) := by
    simp only [F, brSquareQuarterTurnIso_zero]
    omega
  have hFzBounds : 0 ≤ F z 0 ∧ F z 0 ≤ (n : ℤ) := by
    simp only [F, brSquareQuarterTurnIso_zero]
    omega
  let a := Int.toNat (F x 0)
  let b := Int.toNat (F y 0)
  let c := Int.toNat (F z 0)
  have haCast : (a : ℤ) = F x 0 := by
    exact Int.toNat_of_nonneg hFxBounds.1
  have hbCast : (b : ℤ) = F y 0 := by
    exact Int.toNat_of_nonneg hFyBounds.1
  have hcCast : (c : ℤ) = F z 0 := by
    exact Int.toNat_of_nonneg hFzBounds.1
  have hFx : F x = squareVertex (a : ℤ) (-(n : ℤ)) := by
    ext i
    fin_cases i
    · exact haCast.symm
    · simp [F, hx'.1]
  have hFy : F y = squareVertex (b : ℤ) (n : ℤ) := by
    ext i
    fin_cases i
    · exact hbCast.symm
    · simp [F, hy'.1]
      omega
  have hFz : F z = squareVertex (c : ℤ) 0 := by
    ext i
    fin_cases i
    · exact hcCast.symm
    · simp [F, hz'.1]
  let qMap := q.map F.toHom
  let q' : squareGraph.Walk (squareVertex (a : ℤ) (-(n : ℤ)))
      (squareVertex (b : ℤ) (n : ℤ)) := qMap.copy hFx hFy
  have hq'Path : q'.IsPath := by
    simpa [q', qMap] using
      (SimpleGraph.Walk.map_isPath_iff_of_injective F.injective).2 hqPath
  have hq'Open : walkIsOpen omega q' := by
    have hmapOpen := walkIsOpen_map_cubicGraphIso F q hqOpen
    intro e he
    apply hmapOpen e
    simpa only [q', qMap, SimpleGraph.Walk.edges_copy] using he
  have hq'Allowed : walkEdgeFinset q' ⊆
      squareBoundaryFreeRectangleEdges (2 * n) n := by
    intro e he
    rw [mem_walkEdgeFinset_iff] at he
    simp only [q', qMap, SimpleGraph.Walk.edges_copy,
      SimpleGraph.Walk.edges_map, List.mem_map] at he
    rcases he with ⟨f, hf, hfe⟩
    let fe : SquareEdge := ⟨f, q.edges_subset_edgeSet hf⟩
    have hfeAllowed := hqAllowed ((mem_walkEdgeFinset_iff q fe).mpr hf)
    rw [← brSquareQuarterTurnIso_image_boundaryFreeRectangleEdges n]
    refine Finset.mem_image.mpr ⟨fe, hfeAllowed, ?_⟩
    apply Subtype.ext
    exact hfe
  have hq'Box : ∀ v ∈ q'.support,
      0 ≤ v 0 ∧ v 0 ≤ 2 * (n : ℤ) ∧
        -(n : ℤ) ≤ v 1 ∧ v 1 ≤ (n : ℤ) := by
    intro v hv
    simp only [q', SimpleGraph.Walk.support_copy, qMap,
      SimpleGraph.Walk.support_map, List.mem_map] at hv
    rcases hv with ⟨r, hr, rfl⟩
    have hr' := mem_squareRectangleVertices_iff.mp (hqRect r hr)
    change 0 ≤ F r 0 ∧ F r 0 ≤ 2 * (n : ℤ) ∧
      -(n : ℤ) ≤ F r 1 ∧ F r 1 ≤ (n : ℤ)
    simp only [F, brSquareQuarterTurnIso_zero, brSquareQuarterTurnIso_one]
    omega
  have hq'Bottom : ∀ v ∈ q'.support, v 1 = -(n : ℤ) →
      v = squareVertex (a : ℤ) (-(n : ℤ)) := by
    intro v hv hvBottom
    simp only [q', SimpleGraph.Walk.support_copy, qMap,
      SimpleGraph.Walk.support_map, List.mem_map] at hv
    rcases hv with ⟨r, hr, rfl⟩
    have hr0 : r 0 = 0 := by
      change F r 1 = -(n : ℤ) at hvBottom
      simp only [F, brSquareQuarterTurnIso_one] at hvBottom
      omega
    rw [hqLeft r hr hr0]
    change F x = squareVertex (a : ℤ) (-(n : ℤ))
    exact hFx
  have hq'Top : ∀ v ∈ q'.support, v 1 = (n : ℤ) →
      v = squareVertex (b : ℤ) (n : ℤ) := by
    intro v hv hvTop
    simp only [q', SimpleGraph.Walk.support_copy, qMap,
      SimpleGraph.Walk.support_map, List.mem_map] at hv
    rcases hv with ⟨r, hr, rfl⟩
    have hr0 : r 0 = 2 * (n : ℤ) := by
      change F r 1 = (n : ℤ) at hvTop
      simp only [F, brSquareQuarterTurnIso_one] at hvTop
      omega
    rw [hqRight r hr hr0]
    change F y = squareVertex (b : ℤ) (n : ℤ)
    exact hFy
  have htPath : t.IsPath :=
    (isPath_and_support_subset_of_edges_prefix t q.reverse hqPath.reverse htPrefix).1
  obtain ⟨z₀, t₀, hz₀, ht₀Side, _ht₀Support, ht₀Prefix, _ht₀Unique⟩ :=
    exists_cubicWalk_edgePrefix_to_level_of_end_le_unique
      (G := squareGraph) le_rfl t (0 : Fin 2) (n : ℤ) (by omega) (by omega)
  have hz₀Eq : z₀ = z := htUnique z₀
    ((isPath_and_support_subset_of_edges_prefix t₀ t htPath ht₀Prefix).2
      z₀ t₀.end_mem_support) hz₀
  let t₀' : squareGraph.Walk y z := t₀.copy rfl hz₀Eq
  have ht₀'Path : t₀'.IsPath := by
    simpa [t₀'] using
      (isPath_and_support_subset_of_edges_prefix t₀ t htPath ht₀Prefix).1
  have ht₀'Edges : t₀'.edges ⊆ t.edges := by
    simpa only [t₀', SimpleGraph.Walk.edges_copy] using ht₀Prefix.sublist.subset
  obtain ⟨r, hr⟩ := exists_append_of_isPath_of_edges_subset
    ht₀'Path htPath ht₀'Edges
  have hrPath : r.IsPath := by
    rw [hr] at htPath
    exact htPath.of_append_right
  have hrNil : r = .nil := (SimpleGraph.Walk.isPath_iff_eq_nil r).mp hrPath
  subst r
  have htEq : t = t₀' := by simpa using hr
  have htSide : ∀ v ∈ t.support, (n : ℤ) ≤ v 0 := by
    intro v hv
    rw [htEq] at hv
    apply ht₀Side v
    simpa [t₀'] using hv
  let tMap := t.map F.toHom
  let t' : squareGraph.Walk (squareVertex (b : ℤ) (n : ℤ))
      (squareVertex (c : ℤ) 0) := tMap.copy hFy hFz
  have ht'Path : t'.IsPath := by
    simpa [t', tMap] using
      (SimpleGraph.Walk.map_isPath_iff_of_injective F.injective).2 htPath
  have ht'Box : ∀ v ∈ t'.support,
      0 ≤ v 0 ∧ v 0 ≤ 2 * (n : ℤ) ∧ 0 ≤ v 1 ∧ v 1 ≤ (n : ℤ) := by
    intro v hv
    simp only [t', SimpleGraph.Walk.support_copy, tMap,
      SimpleGraph.Walk.support_map, List.mem_map] at hv
    rcases hv with ⟨r, hr, rfl⟩
    have hrQReverse := htSupport r hr
    have hrQ : r ∈ q.support := by
      simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hrQReverse
    have hrRect := mem_squareRectangleVertices_iff.mp (hqRect r hrQ)
    have hrSide := htSide r hr
    change 0 ≤ F r 0 ∧ F r 0 ≤ 2 * (n : ℤ) ∧
      0 ≤ F r 1 ∧ F r 1 ≤ (n : ℤ)
    simp only [F, brSquareQuarterTurnIso_zero, brSquareQuarterTurnIso_one]
    omega
  have ht'Bottom : ∀ v ∈ t'.support, v 1 = 0 →
      v = squareVertex (c : ℤ) 0 := by
    intro v hv hvBottom
    simp only [t', SimpleGraph.Walk.support_copy, tMap,
      SimpleGraph.Walk.support_map, List.mem_map] at hv
    rcases hv with ⟨r, hr, rfl⟩
    have hr0 : r 0 = (n : ℤ) := by
      change F r 1 = 0 at hvBottom
      simp only [F, brSquareQuarterTurnIso_one] at hvBottom
      omega
    rw [htUnique r hr hr0]
    change F z = squareVertex (c : ℤ) 0
    exact hFz
  have ht'Top : ∀ v ∈ t'.support, v 1 = (n : ℤ) →
      v = squareVertex (b : ℤ) (n : ℤ) := by
    intro v hv hvTop
    simp only [t', SimpleGraph.Walk.support_copy, tMap,
      SimpleGraph.Walk.support_map, List.mem_map] at hv
    rcases hv with ⟨r, hr, rfl⟩
    have hr0 : r 0 = 2 * (n : ℤ) := by
      change F r 1 = (n : ℤ) at hvTop
      simp only [F, brSquareQuarterTurnIso_one] at hvTop
      omega
    have hrQReverse := htSupport r hr
    have hrQ : r ∈ q.support := by
      simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hrQReverse
    rw [hqRight r hrQ hr0]
    change F y = squareVertex (b : ℤ) (n : ℤ)
    exact hFy
  have ht'Prefix : t'.edges <+: q'.reverse.edges := by
    simp only [t', q', tMap, qMap, SimpleGraph.Walk.edges_copy,
      SimpleGraph.Walk.edges_map, SimpleGraph.Walk.edges_reverse, List.map_reverse]
    simpa only [SimpleGraph.Walk.edges_reverse, List.map_reverse] using
      (htPrefix.map (Sym2.map F.toHom))
  have hlastLeC := brFilledHullLastMidlineVertex_le_of_nested_exact_crossing
    hn hR homegaFiber q' hq'Path hq'Open hq'Allowed hq'Box hq'Bottom hq'Top
      t' ht'Path ht'Box ht'Bottom ht'Top ht'Prefix
  change brFilledHullLastMidlineVertex hn hR 0 ≤ (n : ℤ)
  calc
    brFilledHullLastMidlineVertex hn hR 0 ≤ (c : ℤ) := hlastLeC
    _ = F z 0 := hcCast
    _ ≤ (n : ℤ) := hFzBounds.2

/-! ### The left-last-midline fiber subpartition -/

/-- Realizable good stopped fibers whose filled selected interface makes its last midline visit
in the left half of the source square. -/
def brFilledHullLastMidlineLeftFiberIndices (n : ℕ) (hn : 0 < n) :
    Finset (Finset (BRLeftmostDualVertex n)) := by
  classical
  exact (brGoodReachableFaceFiberIndices n).filter fun R ↦
    ∃ hR : BRAdmissibleSeparatingFiber n R,
      BRFilledHullLastMidlineLeft hn hR

@[simp]
theorem mem_brFilledHullLastMidlineLeftFiberIndices_iff
    {n : ℕ} {hn : 0 < n} {R : Finset (BRLeftmostDualVertex n)} :
    R ∈ brFilledHullLastMidlineLeftFiberIndices n hn ↔
      R ∈ brGoodReachableFaceFiberIndices n ∧
        ∃ hR : BRAdmissibleSeparatingFiber n R,
          BRFilledHullLastMidlineLeft hn hR := by
  classical
  simp only [brFilledHullLastMidlineLeftFiberIndices, Finset.mem_filter]

/-- The finite union of stopped fibers selected by the left-last-midline condition. -/
def brFilledHullLastMidlineLeftFiberEvent (n : ℕ) (hn : 0 < n) :
    Set (EdgeConfiguration 2) :=
  ⋃ R ∈ brFilledHullLastMidlineLeftFiberIndices n hn,
    brReachableFaceFiber n R

theorem measurableSet_brFilledHullLastMidlineLeftFiberEvent
    (n : ℕ) (hn : 0 < n) :
    MeasurableSet (brFilledHullLastMidlineLeftFiberEvent n hn) := by
  unfold brFilledHullLastMidlineLeftFiberEvent
  exact (brFilledHullLastMidlineLeftFiberIndices n hn).measurableSet_biUnion
    fun R _hR ↦ measurableSet_brReachableFaceFiber n R

private theorem pairwiseDisjoint_brFilledHullLastMidlineLeftFiber
    (n : ℕ) (hn : 0 < n) :
    Set.PairwiseDisjoint
      (brFilledHullLastMidlineLeftFiberIndices n hn :
        Set (Finset (BRLeftmostDualVertex n)))
      (brReachableFaceFiber n) := by
  intro R hR S hS hRS
  apply pairwiseDisjoint_brGoodReachableFaceFiber n
  · exact (mem_brFilledHullLastMidlineLeftFiberIndices_iff.mp hR).1
  · exact (mem_brFilledHullLastMidlineLeftFiberIndices_iff.mp hS).1
  · exact hRS

/-- The quarter-turned lower-last-midline crossing event is covered by exactly the stopped
fibers whose filled interface has its last midline visit in the left half. -/
theorem brSquareLastMidlineLeftCrossingEvent_subset_leftFiberEvent
    {n : ℕ} (hn : 0 < n) :
    brSquareLastMidlineLeftCrossingEvent n ⊆
      brFilledHullLastMidlineLeftFiberEvent n hn := by
  classical
  intro omega homega
  let R := brLeftReachableFaces n omega
  have homegaSquare : omega ∈ brSquareVerticalCrossingEvent n := by
    rw [← rswVerticalPlacementEvent_square_eq_brSquareVerticalCrossingEvent]
    change cubicGraphIsoConfigurationPullback (brSquareQuarterTurnIso n) omega ∈
      rswSquareCrossingEvent n
    change cubicGraphIsoConfigurationPullback (brSquareQuarterTurnIso n) omega ∈
      rswSquareLowerLastMidlineCrossingEvent n at homega
    simp only [rswSquareLowerLastMidlineCrossingEvent] at homega
    obtain ⟨x, hx, y, hy, q, _hqPath, hqOpen, hqAllowed, _hqLeft,
      _hqRight, _hz⟩ := homega
    simp only [rswSquareCrossingEvent, rswRectangleCrossingEvent,
      squareBoundaryFreeRectangleCrossingEvent, Set.mem_iUnion]
    exact ⟨x, hx, y, hy, q, hqOpen, hqAllowed⟩
  have homegaGood : omega ∈ brRightTargetsUnreachedEvent n :=
    brSquareVerticalCrossingEvent_subset_brRightTargetsUnreachedEvent n homegaSquare
  have hRgood : R ∈ brGoodReachableFaceFiberIndices n := by
    rw [mem_brGoodReachableFaceFiberIndices_iff]
    exact homegaGood
  have homegaFiber : omega ∈ brReachableFaceFiber n R :=
    mem_brReachableFaceFiber_self n omega
  let hR : BRAdmissibleSeparatingFiber n R :=
    brAdmissibleSeparatingFiber_of_mem_good_of_mem_fiber hRgood homegaFiber
  have hleft : BRFilledHullLastMidlineLeft hn hR :=
    brFilledHullLastMidlineLeft_of_mem_lastMidlineLeftCrossingEvent
      hn hR homegaFiber homega
  simp only [brFilledHullLastMidlineLeftFiberEvent, Set.mem_iUnion]
  exact ⟨R,
    mem_brFilledHullLastMidlineLeftFiberIndices_iff.mpr
      ⟨hRgood, hR, hleft⟩,
    homegaFiber⟩

/-- The selected left-last-midline fibers retain the first square-root factor. -/
theorem one_sub_sqrt_rswSquare_le_leftFiberEventProbability
    (p : I) {n : ℕ} (hn : 0 < n) :
    1 - Real.sqrt (1 - rswSquareCrossingProbability p n) ≤
      (bernoulliBondMeasure 2 p).real
        (brFilledHullLastMidlineLeftFiberEvent n hn) := by
  exact (one_sub_sqrt_rswSquare_le_brSquareLastMidlineLeftCrossingProbability p n).trans
    (measureReal_mono
      (brSquareLastMidlineLeftCrossingEvent_subset_leftFiberEvent hn)
      (measure_ne_top _ _))

/-- Totalized stopped fresh-contact event. Empty candidate fibers use `Set.univ`; every index in
the left-last-midline subpartition is realizable, so the substantive branch is always selected
there. -/
private def brStoppedLowerFreshContactEventOrUniv
    (n : ℕ) (hn : 0 < n) (R : Finset (BRLeftmostDualVertex n)) :
    Set (EdgeConfiguration 2) := by
  classical
  exact if hR : BRAdmissibleSeparatingFiber n R then
      brStoppedLowerFreshContactEvent R hn hR
    else Set.univ

/-- Union of the left-last-midline stopped fibers with their genuinely fresh lower contact
events. -/
def brFilledHullLastMidlineLeftStoppedContactEvent
    (n : ℕ) (hn : 0 < n) : Set (EdgeConfiguration 2) :=
  ⋃ R ∈ brFilledHullLastMidlineLeftFiberIndices n hn,
    brReachableFaceFiber n R ∩
      brStoppedLowerFreshContactEventOrUniv n hn R

theorem measurableSet_brFilledHullLastMidlineLeftStoppedContactEvent
    (n : ℕ) (hn : 0 < n) :
    MeasurableSet (brFilledHullLastMidlineLeftStoppedContactEvent n hn) := by
  unfold brFilledHullLastMidlineLeftStoppedContactEvent
  apply (brFilledHullLastMidlineLeftFiberIndices n hn).measurableSet_biUnion
  intro R hR
  apply (measurableSet_brReachableFaceFiber n R).inter
  rcases (mem_brFilledHullLastMidlineLeftFiberIndices_iff.mp hR).2 with
    ⟨hRadm, _hleft⟩
  simpa only [brStoppedLowerFreshContactEventOrUniv, dif_pos hRadm] using
    measurableSet_brStoppedLowerFreshContactEvent R hn hRadm

/-- Summing the ratio-free stopped-contact estimate over the selected subpartition gives the
first two square-root factors. -/
theorem one_sub_sqrt_rswSquare_sq_le_leftStoppedContactProbability
    (p : I) {n : ℕ} (hn : 0 < n) :
    (1 - Real.sqrt (1 - rswSquareCrossingProbability p n)) ^ 2 ≤
      (bernoulliBondMeasure 2 p).real
        (brFilledHullLastMidlineLeftStoppedContactEvent n hn) := by
  classical
  let u := 1 - Real.sqrt (1 - rswSquareCrossingProbability p n)
  let mu := bernoulliBondMeasure 2 p
  have hu0 : 0 ≤ u := by
    have hr0 : 0 ≤ rswSquareCrossingProbability p n := measureReal_nonneg
    have hr1 : rswSquareCrossingProbability p n ≤ 1 := measureReal_le_one
    have hsqrt0 := Real.sqrt_nonneg (1 - rswSquareCrossingProbability p n)
    have hsqrtSq : Real.sqrt (1 - rswSquareCrossingProbability p n) ^ 2 =
        1 - rswSquareCrossingProbability p n :=
      Real.sq_sqrt (sub_nonneg.mpr hr1)
    dsimp [u]
    nlinarith
  have hmul : u * mu.real (brFilledHullLastMidlineLeftFiberEvent n hn) ≤
      mu.real (brFilledHullLastMidlineLeftStoppedContactEvent n hn) := by
    unfold brFilledHullLastMidlineLeftFiberEvent
    unfold brFilledHullLastMidlineLeftStoppedContactEvent
    apply mul_measureReal_biUnion_le_biUnion_inter mu
      (brFilledHullLastMidlineLeftFiberIndices n hn)
      (brReachableFaceFiber n)
      (brStoppedLowerFreshContactEventOrUniv n hn) u
      (pairwiseDisjoint_brFilledHullLastMidlineLeftFiber n hn)
    · exact fun R _hR ↦ measurableSet_brReachableFaceFiber n R
    · intro R hR
      rcases (mem_brFilledHullLastMidlineLeftFiberIndices_iff.mp hR).2 with
        ⟨hRadm, _hleft⟩
      simpa only [brStoppedLowerFreshContactEventOrUniv, dif_pos hRadm] using
        measurableSet_brStoppedLowerFreshContactEvent R hn hRadm
    · intro R hR
      rcases (mem_brFilledHullLastMidlineLeftFiberIndices_iff.mp hR).2 with
        ⟨hRadm, _hleft⟩
      simpa only [u, mu, brStoppedLowerFreshContactEventOrUniv,
        dif_pos hRadm] using
          one_sub_sqrt_rswSquare_mul_fiber_le_inter_stoppedFreshContact
            p R hn hRadm
  calc
    u ^ 2 = u * u := by ring
    _ ≤ u * mu.real (brFilledHullLastMidlineLeftFiberEvent n hn) :=
      mul_le_mul_of_nonneg_left
        (one_sub_sqrt_rswSquare_le_leftFiberEventProbability p hn) hu0
    _ ≤ mu.real (brFilledHullLastMidlineLeftStoppedContactEvent n hn) := hmul

end

end Percolation
