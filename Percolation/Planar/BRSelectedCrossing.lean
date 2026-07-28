import Percolation.Planar.BRBoundaryPrimalWalk
import Percolation.Planar.BRTruncatedDegree
import Percolation.Planar.BRVerticalEvents

/-!
# A fixed primal crossing selected from a separating BR fiber

For an admissible separating reached-face fiber, odd-degree parity supplies a bottom-to-top
component of the truncated resolved boundary.  This module chooses that component once, converts
its chosen boundary walk to a primal square-lattice walk using only retained interface bonds, and
therefore obtains one walk which is open in every configuration belonging to the fiber.
-/

namespace Percolation

open SimpleGraph
open scoped Sym2

noncomputable section

private theorem exists_brResolvedBoundaryPortPair
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    ∃ p : BRTruncatedInterfaceEdge n R × BRTruncatedInterfaceEdge n R,
      p.1 ∈ brTruncatedBottomBoundaryVertices n R ∧
        p.2 ∈ brTruncatedTopBoundaryVertices n R ∧
          (brTruncatedResolvedBoundaryGraph n R).Reachable p.1 p.2 := by
  rcases exists_brTruncatedResolvedBoundaryGraph_reachable_bottom_top hn hR with
    ⟨b, hb, t, ht, hbt⟩
  exact ⟨(b, t), hb, ht, hbt⟩

/-- The fixed pair of bottom and top ports selected from an admissible separating reached set. -/
def brSelectedResolvedBoundaryPortPair
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    BRTruncatedInterfaceEdge n R × BRTruncatedInterfaceEdge n R :=
  Classical.choose (exists_brResolvedBoundaryPortPair hn hR)

theorem brSelectedResolvedBoundaryPortPair_spec
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    (brSelectedResolvedBoundaryPortPair hn hR).1 ∈
        brTruncatedBottomBoundaryVertices n R ∧
      (brSelectedResolvedBoundaryPortPair hn hR).2 ∈
        brTruncatedTopBoundaryVertices n R ∧
      (brTruncatedResolvedBoundaryGraph n R).Reachable
        (brSelectedResolvedBoundaryPortPair hn hR).1
        (brSelectedResolvedBoundaryPortPair hn hR).2 :=
  Classical.choose_spec (exists_brResolvedBoundaryPortPair hn hR)

/-- The selected bottom port. -/
def brSelectedBottomPort
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    BRTruncatedInterfaceEdge n R :=
  (brSelectedResolvedBoundaryPortPair hn hR).1

/-- The selected top port. -/
def brSelectedTopPort
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    BRTruncatedInterfaceEdge n R :=
  (brSelectedResolvedBoundaryPortPair hn hR).2

theorem brSelectedBottomPort_mem
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    brSelectedBottomPort hn hR ∈ brTruncatedBottomBoundaryVertices n R :=
  (brSelectedResolvedBoundaryPortPair_spec hn hR).1

theorem brSelectedTopPort_mem
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    brSelectedTopPort hn hR ∈ brTruncatedTopBoundaryVertices n R :=
  (brSelectedResolvedBoundaryPortPair_spec hn hR).2.1

/-- The selected walk in the truncated resolved boundary. -/
def brSelectedResolvedBoundaryWalk
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    (brTruncatedResolvedBoundaryGraph n R).Walk
      (brSelectedBottomPort hn hR) (brSelectedTopPort hn hR) :=
  Classical.choice (brSelectedResolvedBoundaryPortPair_spec hn hR).2.2

/-- Primal bonds crossed by retained vertices of the truncated boundary graph. -/
def brTruncatedInterfacePrimalEdges
    (n : ℕ) (R : Finset (BRLeftmostDualVertex n)) : Finset SquareEdge :=
  Finset.univ.image fun d : BRTruncatedInterfaceEdge n R ↦
    brTruncatedInterfacePrimalEdge d

@[simp]
theorem mem_brTruncatedInterfacePrimalEdges_iff
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)} {e : SquareEdge} :
    e ∈ brTruncatedInterfacePrimalEdges n R ↔
      ∃ d : BRTruncatedInterfaceEdge n R,
        brTruncatedInterfacePrimalEdge d = e := by
  simp [brTruncatedInterfacePrimalEdges]

/-- Any two endpoints of one square-lattice bond can be joined using only that bond. -/
private theorem exists_primalWalk_of_mem_edge
    {e : SquareEdge} {x y : SquareVertex}
    (hx : x ∈ (e : Sym2 SquareVertex)) (hy : y ∈ (e : Sym2 SquareVertex)) :
    ∃ p : squareGraph.Walk x y, walkEdgeFinset p ⊆ {e} := by
  by_cases hxy : x = y
  · subst y
    refine ⟨SimpleGraph.Walk.nil, ?_⟩
    intro f hf
    rw [mem_walkEdgeFinset_iff] at hf
    simp at hf
  · have hedge : s(x, y) = (e : Sym2 SquareVertex) := by
      rw [← e.1.out_eq, Sym2.mem_iff] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact (hxy rfl).elim
      · exact e.1.out_eq
      · exact Sym2.eq_swap.trans e.1.out_eq
      · exact (hxy rfl).elim
    have hadj : squareGraph.Adj x y := by
      rw [← squareGraph.mem_edgeSet, hedge]
      exact e.2
    let step : squareGraph.Walk x y := hadj.toWalk
    refine ⟨step, ?_⟩
    intro f hf
    rw [Finset.mem_singleton]
    apply Subtype.ext
    have hfEdges : (f : Sym2 SquareVertex) ∈ step.edges :=
      (mem_walkEdgeFinset_iff step f).mp hf
    have hfxy : (f : Sym2 SquareVertex) = s(x, y) := by
      simpa [step, SimpleGraph.Adj.toWalk] using hfEdges
    exact hfxy.trans hedge

/-- Any two endpoints of a retained crossed bond can be joined using only retained crossed
bonds. -/
private theorem exists_primalWalk_in_truncatedInterfacePrimalEdges
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (d : BRTruncatedInterfaceEdge n R) {x y : SquareVertex}
    (hx : x ∈ (brTruncatedInterfacePrimalEdge d : Sym2 SquareVertex))
    (hy : y ∈ (brTruncatedInterfacePrimalEdge d : Sym2 SquareVertex)) :
    ∃ p : squareGraph.Walk x y,
      walkEdgeFinset p ⊆ brTruncatedInterfacePrimalEdges n R := by
  obtain ⟨p, hp⟩ := exists_primalWalk_of_mem_edge hx hy
  refine ⟨p, fun e he ↦ ?_⟩
  have hed : e = brTruncatedInterfacePrimalEdge d := by
    simpa using hp he
  subst e
  exact mem_brTruncatedInterfacePrimalEdges_iff.mpr ⟨d, rfl⟩

/-- Geometry-only conversion of a resolved-boundary walk to a primal walk.  Its support is
independent of any percolation configuration. -/
theorem brTruncatedBoundaryWalk_exists_primalWalk
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    {d e : BRTruncatedInterfaceEdge n R}
    (w : (brTruncatedResolvedBoundaryGraph n R).Walk d e)
    {x y : SquareVertex}
    (hx : x ∈ (brTruncatedInterfacePrimalEdge d : Sym2 SquareVertex))
    (hy : y ∈ (brTruncatedInterfacePrimalEdge e : Sym2 SquareVertex)) :
    ∃ p : squareGraph.Walk x y,
      walkEdgeFinset p ⊆ brTruncatedInterfacePrimalEdges n R := by
  induction w generalizing x with
  | @nil u =>
      exact exists_primalWalk_in_truncatedInterfacePrimalEdges u hx hy
  | @cons u v z huv tail ih =>
      rcases brTruncatedInterfacePrimalEdge_adj huv with
        ⟨_hne, common, hcommonU, hcommonV⟩
      obtain ⟨p, hp⟩ :=
        exists_primalWalk_in_truncatedInterfacePrimalEdges u hx hcommonU
      obtain ⟨q, hq⟩ := ih hcommonV hy
      refine ⟨p.append q, ?_⟩
      intro f hf
      rw [mem_walkEdgeFinset_iff, SimpleGraph.Walk.edges_append,
        List.mem_append] at hf
      rcases hf with hf | hf
      · exact hp ((mem_walkEdgeFinset_iff p f).mpr hf)
      · exact hq ((mem_walkEdgeFinset_iff q f).mpr hf)

/-! ### The selected primal crossing -/

/-- The primal bottom-side endpoint of the selected bottom port. -/
def brSelectedBottomPrimalVertex
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) : SquareVertex :=
  brBottomPortPrimalVertex (brSelectedBottomPort hn hR).1

/-- The primal top-side endpoint of the selected top port. -/
def brSelectedTopPrimalVertex
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) : SquareVertex :=
  brTopPortPrimalVertex (brSelectedTopPort hn hR).1

theorem brSelectedBottomPrimalVertex_mem_bottomSide
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    brSelectedBottomPrimalVertex hn hR ∈ brSquareBottomSide n := by
  rw [mem_brSquareBottomSide_iff]
  simpa [brSelectedBottomPrimalVertex] using
    (brTruncatedBottomBoundaryVertex_primalEndpoint
      (brSelectedBottomPort_mem hn hR)).2

theorem brSelectedTopPrimalVertex_mem_topSide
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    brSelectedTopPrimalVertex hn hR ∈ brSquareTopSide n := by
  rw [mem_brSquareTopSide_iff]
  simpa [brSelectedTopPrimalVertex] using
    (brTruncatedTopBoundaryVertex_primalEndpoint
      (brSelectedTopPort_mem hn hR)).2

private theorem exists_brSelectedPrimalWalk
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    ∃ p : squareGraph.Walk
        (brSelectedBottomPrimalVertex hn hR) (brSelectedTopPrimalVertex hn hR),
      walkEdgeFinset p ⊆ brTruncatedInterfacePrimalEdges n R := by
  apply brTruncatedBoundaryWalk_exists_primalWalk
    (brSelectedResolvedBoundaryWalk hn hR)
  · simpa [brSelectedBottomPrimalVertex] using
      (brTruncatedBottomBoundaryVertex_primalEndpoint
        (brSelectedBottomPort_mem hn hR)).1
  · simpa [brSelectedTopPrimalVertex] using
      (brTruncatedTopBoundaryVertex_primalEndpoint
        (brSelectedTopPort_mem hn hR)).1

/-- A fixed primal bottom-to-top walk selected from the reached set `R`.  No configuration is an
argument of this definition. -/
def brSelectedPrimalWalk
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    squareGraph.Walk
      (brSelectedBottomPrimalVertex hn hR) (brSelectedTopPrimalVertex hn hR) :=
  Classical.choose (exists_brSelectedPrimalWalk hn hR)

theorem walkEdgeFinset_brSelectedPrimalWalk_subset_interface
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    walkEdgeFinset (brSelectedPrimalWalk hn hR) ⊆
      brTruncatedInterfacePrimalEdges n R :=
  Classical.choose_spec (exists_brSelectedPrimalWalk hn hR)

/-- Every retained crossed primal bond lies in the boundary-free square support. -/
theorem brTruncatedInterfacePrimalEdges_subset_boundaryFree
    (n : ℕ) (R : Finset (BRLeftmostDualVertex n)) :
    brTruncatedInterfacePrimalEdges n R ⊆
      squareBoundaryFreeRectangleEdges (2 * n) n := by
  intro e he
  rcases mem_brTruncatedInterfacePrimalEdges_iff.mp he with ⟨d, rfl⟩
  change (dualToPrimalCrossingPositiveEdge d.1).toEdge ∈
    squareBoundaryFreeRectangleEdges (2 * n) n
  exact (mem_brTruncatedDualBoundaryPositiveEdges_iff.mp d.2).2.2.2

theorem walkEdgeFinset_brSelectedPrimalWalk_subset_boundaryFree
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    walkEdgeFinset (brSelectedPrimalWalk hn hR) ⊆
      squareBoundaryFreeRectangleEdges (2 * n) n :=
  (walkEdgeFinset_brSelectedPrimalWalk_subset_interface hn hR).trans
    (brTruncatedInterfacePrimalEdges_subset_boundaryFree n R)

/-- Every retained crossed primal bond is open in every configuration realizing the same
reached-face fiber. -/
theorem brTruncatedInterfacePrimalEdge_mem_configuration_of_mem_fiber
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    {omega : EdgeConfiguration 2}
    (homega : omega ∈ brReachableFaceFiber n R) {e : SquareEdge}
    (he : e ∈ brTruncatedInterfacePrimalEdges n R) : e ∈ omega := by
  rcases mem_brTruncatedInterfacePrimalEdges_iff.mp he with ⟨d, rfl⟩
  exact (brTruncatedInterfacePrimalEdge_mem_boundaryFree_and_configuration homega d).2

/-- The selected walk is open in every configuration in the reached-face fiber. -/
theorem walkIsOpen_brSelectedPrimalWalk_of_mem_fiber
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R)
    {omega : EdgeConfiguration 2} (homega : omega ∈ brReachableFaceFiber n R) :
    walkIsOpen omega (brSelectedPrimalWalk hn hR) := by
  intro e he
  let f : SquareEdge :=
    ⟨e, (brSelectedPrimalWalk hn hR).edges_subset_edgeSet he⟩
  have hfWalk : f ∈ walkEdgeFinset (brSelectedPrimalWalk hn hR) :=
    (mem_walkEdgeFinset_iff (brSelectedPrimalWalk hn hR) f).mpr he
  have hfInterface : f ∈ brTruncatedInterfacePrimalEdges n R :=
    walkEdgeFinset_brSelectedPrimalWalk_subset_interface hn hR hfWalk
  exact brTruncatedInterfacePrimalEdge_mem_configuration_of_mem_fiber homega hfInterface

end

end Percolation
