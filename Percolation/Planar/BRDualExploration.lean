import Percolation.Bernoulli.FiniteCube
import Percolation.Bernoulli.FiniteReachability
import Percolation.Planar.Basic
import Percolation.Planar.RSWEvents

/-!
# Stopped dual exploration for the Bollobás--Riordan crossing argument

This module builds the first finite stopping object used in the planned proof of
Bollobás--Riordan (2006), Lemma 6.  For the primal square `[0,2n] × [-n,n]`, the dual frame
consists of the unit faces with lower-left coordinates in
`[-1,2n] × [-n,n-1]`.  Its sources are the faces in the added column `x = -1`.

The exploration follows the dual complement of the boundary-free primal square: a frame edge is
open when its crossed primal bond is absent from the RSW edge set, or when that bond is present
and closed.  Treating absent perimeter bonds deterministically open is necessary for the reached
set to depend on exactly the same coordinates as `rswSquareCrossingEvent`.  A fiber fixing the
reached dual faces is therefore determined only by allowed primal bonds crossed by dual-frame
edges incident to the fixed reached set.  No crossing-event partition or boundary path extraction
is asserted here; those require the resolved-interface construction.
-/

namespace Percolation

open SimpleGraph
open scoped Sym2

noncomputable section

/-- Dual faces spanning `[0,2n] × [-n,n]`, including both vertical exterior columns. -/
def brLeftmostDualFaces (n : ℕ) : Finset DualSquareVertex :=
  Fintype.piFinset fun i : Fin 2 ↦
    if i = 0 then Finset.Icc (-1 : ℤ) (2 * (n : ℤ))
    else Finset.Icc (-(n : ℤ)) ((n : ℤ) - 1)

@[simp]
theorem mem_brLeftmostDualFaces_iff {n : ℕ} {z : DualSquareVertex} :
    z ∈ brLeftmostDualFaces n ↔
      -1 ≤ z 0 ∧ z 0 ≤ 2 * (n : ℤ) ∧
        -(n : ℤ) ≤ z 1 ∧ z 1 < (n : ℤ) := by
  classical
  simp only [brLeftmostDualFaces, Fintype.mem_piFinset]
  constructor
  · intro h
    have h0 : -1 ≤ z 0 ∧ z 0 ≤ 2 * (n : ℤ) := by
      simpa [Finset.mem_Icc] using h (0 : Fin 2)
    have h1 : -(n : ℤ) ≤ z 1 ∧ z 1 ≤ (n : ℤ) - 1 := by
      simpa [Finset.mem_Icc] using h (1 : Fin 2)
    omega
  · rintro ⟨hz0, hz0', hz1, hz1'⟩ i
    fin_cases i
    · simp [Finset.mem_Icc, hz0, hz0']
    · simp [Finset.mem_Icc]
      omega

/-- A vertex of the finite dual frame used by the stopped left exploration. -/
abbrev BRLeftmostDualVertex (n : ℕ) :=
  {z : DualSquareVertex // z ∈ brLeftmostDualFaces n}

/-- The shifted-dual square lattice induced on the finite left-exploration frame. -/
def brLeftmostDualGraph (n : ℕ) : SimpleGraph (BRLeftmostDualVertex n) :=
  dualSquareGraph.induce (brLeftmostDualFaces n : Set DualSquareVertex)

local instance instDecidableRelBRLeftmostDualGraph (n : ℕ) :
    DecidableRel (brLeftmostDualGraph n).Adj :=
  Classical.decRel _

@[simp]
theorem brLeftmostDualGraph_adj_iff {n : ℕ} {x y : BRLeftmostDualVertex n} :
    (brLeftmostDualGraph n).Adj x y ↔ dualSquareGraph.Adj x.1 y.1 :=
  Iff.rfl

/-- All framed dual faces in the exterior column immediately left of the primal square. -/
def brLeftmostDualSources (n : ℕ) : Finset (BRLeftmostDualVertex n) :=
  Finset.univ.filter fun z ↦ z.1 0 = -1

@[simp]
theorem mem_brLeftmostDualSources_iff {n : ℕ} {z : BRLeftmostDualVertex n} :
    z ∈ brLeftmostDualSources n ↔ z.1 0 = -1 := by
  simp [brLeftmostDualSources]

/-- Forget the finite-frame subtype and regard a frame walk as a shifted-dual walk. -/
def brLeftmostDualToAmbientHom (n : ℕ) :
    brLeftmostDualGraph n →g dualSquareGraph where
  toFun := fun z ↦ z.1
  map_rel' := by
    intro x y hxy
    exact hxy

theorem brLeftmostDualToAmbientHom_injective (n : ℕ) :
    Function.Injective (brLeftmostDualToAmbientHom n) := by
  intro x y hxy
  exact Subtype.ext hxy

/-- An actual edge of the finite dual frame, embedded into the ambient shifted-dual lattice. -/
def brLeftmostDualEdgeEmbedding (n : ℕ) :
    (brLeftmostDualGraph n).edgeSet ↪ DualSquareEdge where
  toFun e := ⟨Sym2.map (brLeftmostDualToAmbientHom n) e.1,
    (brLeftmostDualToAmbientHom n).map_mem_edgeSet e.2⟩
  inj' := by
    intro e f hef
    apply Subtype.ext
    apply Sym2.map.injective (brLeftmostDualToAmbientHom_injective n)
    exact congrArg Subtype.val hef

/-- Configuration explored in the finite dual frame.

A frame edge is declared open exactly when it is an actual edge of the induced frame graph and
its crossed primal bond is either excluded from the boundary-free RSW square or closed in the
given configuration.  Thus excluded perimeter bonds are deterministic dual-open edges.  The
existential edge proof makes this a configuration on all unordered frame-vertex pairs, as
required by `finiteGraphReachableVertices`; graph walks only query actual frame edges. -/
def brClosedDualExplorationConfiguration
    (n : ℕ) (omega : EdgeConfiguration 2) : Set (Sym2 (BRLeftmostDualVertex n)) :=
  {e | ∃ he : e ∈ (brLeftmostDualGraph n).edgeSet,
    let crossed := squareEdgeDualCrossingEquiv.symm
      (brLeftmostDualEdgeEmbedding n ⟨e, he⟩)
    crossed ∉ squareBoundaryFreeRectangleEdges (2 * n) n ∨ crossed ∉ omega}

theorem mem_brClosedDualExplorationConfiguration_iff_of_mem_edgeSet
    {n : ℕ} {omega : EdgeConfiguration 2} {e : Sym2 (BRLeftmostDualVertex n)}
    (he : e ∈ (brLeftmostDualGraph n).edgeSet) :
    e ∈ brClosedDualExplorationConfiguration n omega ↔
      let crossed := squareEdgeDualCrossingEquiv.symm
        (brLeftmostDualEdgeEmbedding n ⟨e, he⟩)
      crossed ∉ squareBoundaryFreeRectangleEdges (2 * n) n ∨ crossed ∉ omega := by
  change (∃ he' : e ∈ (brLeftmostDualGraph n).edgeSet,
      let crossed := squareEdgeDualCrossingEquiv.symm
        (brLeftmostDualEdgeEmbedding n ⟨e, he'⟩)
      crossed ∉ squareBoundaryFreeRectangleEdges (2 * n) n ∨ crossed ∉ omega) ↔ _
  constructor
  · rintro ⟨he', hopen⟩
    simpa only [Subsingleton.elim he' he] using hopen
  · exact fun hopen ↦ ⟨he, hopen⟩

/-- On a bond belonging to the boundary-free square, exploration openness is literally ambient
dual openness (equivalently, primal closedness). -/
theorem mem_brClosedDualExplorationConfiguration_iff_dual_open_of_crossed_mem
    {n : ℕ} {omega : EdgeConfiguration 2} {e : Sym2 (BRLeftmostDualVertex n)}
    (he : e ∈ (brLeftmostDualGraph n).edgeSet)
    (hcrossed : squareEdgeDualCrossingEquiv.symm
      (brLeftmostDualEdgeEmbedding n ⟨e, he⟩) ∈
        squareBoundaryFreeRectangleEdges (2 * n) n) :
    e ∈ brClosedDualExplorationConfiguration n omega ↔
      brLeftmostDualEdgeEmbedding n ⟨e, he⟩ ∈ dualSquareConfiguration omega := by
  rw [mem_brClosedDualExplorationConfiguration_iff_of_mem_edgeSet he]
  simp only [hcrossed, not_true, false_or]
  rfl

/-- A frame edge fails to be exploration-open exactly when its crossed primal bond is an allowed
boundary-free bond and is open in the primal configuration. -/
theorem not_mem_brClosedDualExplorationConfiguration_iff_of_mem_edgeSet
    {n : ℕ} {omega : EdgeConfiguration 2} {e : Sym2 (BRLeftmostDualVertex n)}
    (he : e ∈ (brLeftmostDualGraph n).edgeSet) :
    e ∉ brClosedDualExplorationConfiguration n omega ↔
      let crossed := squareEdgeDualCrossingEquiv.symm
        (brLeftmostDualEdgeEmbedding n ⟨e, he⟩)
      crossed ∈ squareBoundaryFreeRectangleEdges (2 * n) n ∧ crossed ∈ omega := by
  rw [mem_brClosedDualExplorationConfiguration_iff_of_mem_edgeSet he]
  simp

/-- Faces reachable from the left exterior column through dual-open (primal-closed) edges. -/
def brLeftReachableFaces
    (n : ℕ) (omega : EdgeConfiguration 2) : Finset (BRLeftmostDualVertex n) :=
  finiteGraphReachableVertices (brLeftmostDualGraph n) (brLeftmostDualSources n)
    (brClosedDualExplorationConfiguration n omega)

/-- Opening more primal bonds can only shrink the stopped closed-dual reachable set. -/
theorem brLeftReachableFaces_anti
    {n : ℕ} {omega eta : EdgeConfiguration 2}
    (hmono : omega ⊆ eta) :
    brLeftReachableFaces n eta ⊆ brLeftReachableFaces n omega := by
  intro x hx
  rw [brLeftReachableFaces, mem_finiteGraphReachableVertices_iff] at hx ⊢
  rcases hx with ⟨a, ha, w, hw⟩
  refine ⟨a, ha, w, ?_⟩
  intro e he
  have heGraph : e ∈ (brLeftmostDualGraph n).edgeSet :=
    w.edges_subset_edgeSet he
  have hwE := hw e he
  rw [mem_brClosedDualExplorationConfiguration_iff_of_mem_edgeSet heGraph] at hwE ⊢
  rcases hwE with houtside | hclosed
  · exact Or.inl houtside
  · exact Or.inr (fun hopen ↦ hclosed (hmono hopen))

/-- The stopping fiber on which the dual flood fill reaches exactly the prescribed faces. -/
def brReachableFaceFiber (n : ℕ) (R : Finset (BRLeftmostDualVertex n)) :
    Set (EdgeConfiguration 2) :=
  {omega | brLeftReachableFaces n omega = R}

private theorem brIncidentEdge_mem_edgeSet
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    {e : Sym2 (BRLeftmostDualVertex n)}
    (he : e ∈ finiteGraphIncidentEdges (brLeftmostDualGraph n) R) :
    e ∈ (brLeftmostDualGraph n).edgeSet := by
  rw [finiteGraphIncidentEdges, Finset.mem_biUnion] at he
  rcases he with ⟨z, _hz, he⟩
  rw [SimpleGraph.mem_incidenceFinset] at he
  exact (brLeftmostDualGraph n).incidenceSet_subset z he

/-- The ambient dual edge represented by an edge in the finite exploration support. -/
def brIncidentDualEdge (n : ℕ) (R : Finset (BRLeftmostDualVertex n))
    (e : {e // e ∈ finiteGraphIncidentEdges (brLeftmostDualGraph n) R}) :
    DualSquareEdge :=
  brLeftmostDualEdgeEmbedding n ⟨e.1, brIncidentEdge_mem_edgeSet e.2⟩

/-- The primal bond crossed by an incident edge in the finite dual exploration support. -/
def brIncidentCrossedPrimalEdge (n : ℕ) (R : Finset (BRLeftmostDualVertex n))
    (e : {e // e ∈ finiteGraphIncidentEdges (brLeftmostDualGraph n) R}) : SquareEdge :=
  squareEdgeDualCrossingEquiv.symm (brIncidentDualEdge n R e)

/-- Primal coordinates exposed when the stopped dual exploration has reached-face set `R`.

These are exactly the *allowed boundary-free* primal bonds crossed by dual-frame edges incident to
a face in `R`.  Deterministically open perimeter edges are omitted, and an edge joining two faces
outside `R` is not included. -/
def brReachableFaceFiberSupport
    (n : ℕ) (R : Finset (BRLeftmostDualVertex n)) : Finset SquareEdge :=
  ((finiteGraphIncidentEdges (brLeftmostDualGraph n) R).attach.image
    (brIncidentCrossedPrimalEdge n R)).filter fun e ↦
      e ∈ squareBoundaryFreeRectangleEdges (2 * n) n

theorem brIncidentCrossedPrimalEdge_mem_fiberSupport
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    {e : Sym2 (BRLeftmostDualVertex n)}
    (he : e ∈ finiteGraphIncidentEdges (brLeftmostDualGraph n) R)
    (hallowed : brIncidentCrossedPrimalEdge n R ⟨e, he⟩ ∈
      squareBoundaryFreeRectangleEdges (2 * n) n) :
    brIncidentCrossedPrimalEdge n R ⟨e, he⟩ ∈ brReachableFaceFiberSupport n R := by
  rw [brReachableFaceFiberSupport, Finset.mem_filter]
  refine ⟨?_, hallowed⟩
  apply Finset.mem_image.mpr
  exact ⟨⟨e, he⟩, by simp, rfl⟩

/-- A fixed reached-face fiber is determined by the crossed primal bonds incident to that
reached set. -/
theorem dependsOn_brReachableFaceFiber
    (n : ℕ) (R : Finset (BRLeftmostDualVertex n)) :
    DependsOn (brReachableFaceFiberSupport n R) (brReachableFaceFiber n R) := by
  classical
  intro omega eta hagree
  change
    finiteGraphReachableVertices (brLeftmostDualGraph n) (brLeftmostDualSources n)
        (brClosedDualExplorationConfiguration n omega) = R ↔
      finiteGraphReachableVertices (brLeftmostDualGraph n) (brLeftmostDualSources n)
        (brClosedDualExplorationConfiguration n eta) = R
  apply dependsOn_finiteGraphReachableVertices_fiber
  intro e he
  have heGraph : e ∈ (brLeftmostDualGraph n).edgeSet :=
    brIncidentEdge_mem_edgeSet he
  rw [mem_brClosedDualExplorationConfiguration_iff_of_mem_edgeSet
        (omega := omega) heGraph,
    mem_brClosedDualExplorationConfiguration_iff_of_mem_edgeSet
        (omega := eta) heGraph]
  by_cases hallowed : brIncidentCrossedPrimalEdge n R ⟨e, he⟩ ∈
      squareBoundaryFreeRectangleEdges (2 * n) n
  · have hprimal := hagree (brIncidentCrossedPrimalEdge n R ⟨e, he⟩)
      (brIncidentCrossedPrimalEdge_mem_fiberSupport he hallowed)
    simp only [brIncidentCrossedPrimalEdge, brIncidentDualEdge] at hallowed ⊢
    simp only [hallowed, not_true, false_or]
    exact not_congr hprimal
  · simp only [brIncidentCrossedPrimalEdge, brIncidentDualEdge] at hallowed ⊢
    simp [hallowed]

/-- Every stopped-exploration fiber is a measurable finite-cylinder event. -/
theorem measurableSet_brReachableFaceFiber
    (n : ℕ) (R : Finset (BRLeftmostDualVertex n)) :
    MeasurableSet (brReachableFaceFiber n R) :=
  (dependsOn_brReachableFaceFiber n R).measurableSet

/-- The finite index set of all candidate reached-face sets in the framed dual graph. -/
def brReachableFaceFiberIndices (n : ℕ) : Finset (Finset (BRLeftmostDualVertex n)) :=
  Finset.univ

@[simp]
theorem mem_brReachableFaceFiberIndices
    {n : ℕ} (R : Finset (BRLeftmostDualVertex n)) :
    R ∈ brReachableFaceFiberIndices n := by
  simp [brReachableFaceFiberIndices]

/-- A configuration belongs to the fiber indexed by its own reached-face set. -/
theorem mem_brReachableFaceFiber_self (n : ℕ) (omega : EdgeConfiguration 2) :
    omega ∈ brReachableFaceFiber n (brLeftReachableFaces n omega) :=
  rfl

/-- Fibers indexed by distinct reached-face sets are disjoint. -/
theorem pairwiseDisjoint_brReachableFaceFiber (n : ℕ) :
    Set.PairwiseDisjoint (brReachableFaceFiberIndices n :
      Set (Finset (BRLeftmostDualVertex n))) (brReachableFaceFiber n) := by
  intro R _hR S _hS hRS
  change Disjoint (brReachableFaceFiber n R) (brReachableFaceFiber n S)
  rw [Set.disjoint_left]
  intro omega homegaR homegaS
  change brLeftReachableFaces n omega = R at homegaR
  change brLeftReachableFaces n omega = S at homegaS
  exact hRS (homegaR.symm.trans homegaS)

/-- The finite union of all reached-face fibers is the whole configuration space. -/
theorem biUnion_brReachableFaceFiber_eq_univ (n : ℕ) :
    (⋃ R ∈ brReachableFaceFiberIndices n, brReachableFaceFiber n R) =
      (Set.univ : Set (EdgeConfiguration 2)) := by
  ext omega
  simp [brReachableFaceFiberIndices, brReachableFaceFiber]

end

end Percolation
