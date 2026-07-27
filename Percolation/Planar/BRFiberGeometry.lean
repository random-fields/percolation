import Percolation.Planar.BRDualExploration

/-!
# Elementary geometry of stopped dual-exploration fibers

This module records the finite flood-fill facts used to turn a reached/unreached frame edge into
an allowed open primal bond. It also packages the source and target conditions for separating
reached-face fibers. No global planar-separation or event-equivalence claim is made here.
-/

namespace Percolation

open SimpleGraph
open scoped Sym2

noncomputable section

/-- Framed dual faces in the exterior column immediately right of the primal square. -/
def brRightmostDualTargets (n : ℕ) : Finset (BRLeftmostDualVertex n) :=
  Finset.univ.filter fun z ↦ z.1 0 = 2 * (n : ℤ)

@[simp]
theorem mem_brRightmostDualTargets_iff {n : ℕ} {z : BRLeftmostDualVertex n} :
    z ∈ brRightmostDualTargets n ↔ z.1 0 = 2 * (n : ℤ) := by
  simp [brRightmostDualTargets]

/-- A reached-face set contains the left sources and avoids the right targets. -/
def BRSeparatingReachedSet (n : ℕ) (R : Finset (BRLeftmostDualVertex n)) : Prop :=
  brLeftmostDualSources n ⊆ R ∧ Disjoint R (brRightmostDualTargets n)

/-- A realizable reached-face fiber which avoids every right target. -/
def BRAdmissibleSeparatingFiber (n : ℕ) (R : Finset (BRLeftmostDualVertex n)) : Prop :=
  (∃ omega, omega ∈ brReachableFaceFiber n R) ∧
    Disjoint R (brRightmostDualTargets n)

/-- Every exploration source is reached. -/
theorem mem_brLeftReachableFaces_of_mem_source
    {n : ℕ} {omega : EdgeConfiguration 2} {z : BRLeftmostDualVertex n}
    (hz : z ∈ brLeftmostDualSources n) :
    z ∈ brLeftReachableFaces n omega := by
  rw [brLeftReachableFaces, mem_finiteGraphReachableVertices_iff]
  exact finiteGraphReachableFrom_source hz

/-- The left source column is contained in every reached-face set. -/
theorem brLeftmostDualSources_subset_brLeftReachableFaces
    (n : ℕ) (omega : EdgeConfiguration 2) :
    brLeftmostDualSources n ⊆ brLeftReachableFaces n omega :=
  fun _z hz ↦ mem_brLeftReachableFaces_of_mem_source hz

/-- A realized stopped-exploration fiber contains the left source column. -/
theorem brLeftmostDualSources_subset_of_mem_brReachableFaceFiber
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)} {omega : EdgeConfiguration 2}
    (homega : omega ∈ brReachableFaceFiber n R) :
    brLeftmostDualSources n ⊆ R := by
  change brLeftReachableFaces n omega = R at homega
  rw [← homega]
  exact brLeftmostDualSources_subset_brLeftReachableFaces n omega

/-- An admissible separating fiber supplies the source and target conditions of a separating
reached set. -/
theorem BRAdmissibleSeparatingFiber.separatingReachedSet
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hR : BRAdmissibleSeparatingFiber n R) :
    BRSeparatingReachedSet n R := by
  rcases hR.1 with ⟨omega, homega⟩
  exact ⟨brLeftmostDualSources_subset_of_mem_brReachableFaceFiber homega, hR.2⟩

/-- Reachability is closed under an adjacent exploration-open frame edge. -/
theorem mem_brLeftReachableFaces_of_adj_of_mem_exploration
    {n : ℕ} {omega : EdgeConfiguration 2} {x y : BRLeftmostDualVertex n}
    (hx : x ∈ brLeftReachableFaces n omega)
    (hxy : (brLeftmostDualGraph n).Adj x y)
    (hopen : s(x, y) ∈ brClosedDualExplorationConfiguration n omega) :
    y ∈ brLeftReachableFaces n omega := by
  rw [brLeftReachableFaces, mem_finiteGraphReachableVertices_iff] at hx ⊢
  exact finiteGraphReachableFrom_step hx hxy hopen

/-- The two endpoints of an exploration-open frame edge have the same reached status. -/
theorem mem_brLeftReachableFaces_iff_of_adj_of_mem_exploration
    {n : ℕ} {omega : EdgeConfiguration 2} {x y : BRLeftmostDualVertex n}
    (hxy : (brLeftmostDualGraph n).Adj x y)
    (hopen : s(x, y) ∈ brClosedDualExplorationConfiguration n omega) :
    x ∈ brLeftReachableFaces n omega ↔ y ∈ brLeftReachableFaces n omega := by
  constructor
  · intro hx
    exact mem_brLeftReachableFaces_of_adj_of_mem_exploration hx hxy hopen
  · intro hy
    apply mem_brLeftReachableFaces_of_adj_of_mem_exploration hy hxy.symm
    simpa only [Sym2.eq_swap] using hopen

/-- A frame edge from a reached face to an unreached face is not exploration-open. -/
theorem not_mem_brClosedDualExplorationConfiguration_of_reached_cut
    {n : ℕ} {omega : EdgeConfiguration 2} {x y : BRLeftmostDualVertex n}
    (hx : x ∈ brLeftReachableFaces n omega)
    (hy : y ∉ brLeftReachableFaces n omega)
    (hxy : (brLeftmostDualGraph n).Adj x y) :
    s(x, y) ∉ brClosedDualExplorationConfiguration n omega := by
  intro hopen
  exact hy (mem_brLeftReachableFaces_of_adj_of_mem_exploration hx hxy hopen)

/-- A reached/unreached frame cut crosses an allowed bond which is open in the primal
configuration. -/
theorem brCutCrossedPrimalEdge_mem_boundaryFree_and_configuration
    {n : ℕ} {omega : EdgeConfiguration 2} {x y : BRLeftmostDualVertex n}
    (hx : x ∈ brLeftReachableFaces n omega)
    (hy : y ∉ brLeftReachableFaces n omega)
    (hxy : (brLeftmostDualGraph n).Adj x y) :
    let crossed := squareEdgeDualCrossingEquiv.symm
      (brLeftmostDualEdgeEmbedding n
        ⟨s(x, y), (brLeftmostDualGraph n).mem_edgeSet.mpr hxy⟩)
    crossed ∈ squareBoundaryFreeRectangleEdges (2 * n) n ∧ crossed ∈ omega := by
  apply (not_mem_brClosedDualExplorationConfiguration_iff_of_mem_edgeSet
    ((brLeftmostDualGraph n).mem_edgeSet.mpr hxy)).mp
  exact not_mem_brClosedDualExplorationConfiguration_of_reached_cut hx hy hxy

/-- A frame edge crossing an excluded primal bond cannot change reached status. -/
theorem mem_brLeftReachableFaces_iff_of_adj_of_crossed_not_mem
    {n : ℕ} {omega : EdgeConfiguration 2} {x y : BRLeftmostDualVertex n}
    (hxy : (brLeftmostDualGraph n).Adj x y)
    (hcrossed : squareEdgeDualCrossingEquiv.symm
      (brLeftmostDualEdgeEmbedding n
        ⟨s(x, y), (brLeftmostDualGraph n).mem_edgeSet.mpr hxy⟩) ∉
          squareBoundaryFreeRectangleEdges (2 * n) n) :
    x ∈ brLeftReachableFaces n omega ↔ y ∈ brLeftReachableFaces n omega := by
  apply mem_brLeftReachableFaces_iff_of_adj_of_mem_exploration hxy
  rw [mem_brClosedDualExplorationConfiguration_iff_of_mem_edgeSet
    ((brLeftmostDualGraph n).mem_edgeSet.mpr hxy)]
  exact Or.inl hcrossed

end

end Percolation
