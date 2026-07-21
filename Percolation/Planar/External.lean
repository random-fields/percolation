import Percolation.Planar.SquareCritical
import Percolation.Planar.RSWCircuitIncidence

/-!
# Externally sourced planar topology

This module is the single boundary for planar-topological results which Grimmett explicitly
delegates to sources outside the book. Keeping these declarations separate makes every downstream
axiom dependency visible to `#print axioms`.
-/

namespace Percolation

open scoped unitInterval

/-! ## Finite connected square subgraphs -/

/-- A concrete finite connected subgraph of the square lattice.  Connectivity is expressed by
walks from a chosen root, and `edge_endpoints` rules out dangling edges whose endpoints are not
vertices of the subgraph. -/
structure FiniteConnectedSquareSubgraph where
  vertices : Finset SquareVertex
  edges : Finset SquareEdge
  root : SquareVertex
  root_mem : root ∈ vertices
  edge_endpoints : ∀ e ∈ edges, ∀ x ∈ (e : Sym2 SquareVertex), x ∈ vertices
  connected : ∀ x ∈ vertices,
    ∃ w : squareGraph.Walk root x, walkEdgeFinset w ⊆ edges

namespace FiniteConnectedSquareSubgraph

/-- All ambient square-lattice edges incident to at least one vertex of a finite subgraph. -/
noncomputable def incidentEdges (G : FiniteConnectedSquareSubgraph) : Finset SquareEdge := by
  classical
  exact G.vertices.biUnion fun x ↦
    Finset.univ.image fun a : CubicDirection 2 ↦ cubicStepEdge x a

/-- Grimmett's edge boundary `ΔG`: ambient edges not in the subgraph but incident to one of
its vertices. -/
noncomputable def edgeBoundary (G : FiniteConnectedSquareSubgraph) : Finset SquareEdge :=
  G.incidentEdges \ G.edges

/-- A shifted-dual circuit contains the finite subgraph in its interior when every vertex of the
subgraph has odd mod-two face index with respect to the circuit. -/
def IsInteriorCircuit (G : FiniteConnectedSquareSubgraph) (c : DualCircuit) : Prop :=
  ∀ x ∈ G.vertices, closedSquareWalkFaceParity c.walk x = 1

/-- A circuit is the boundary circuit required by Proposition 11.2 when it surrounds the graph
and every crossed primal edge belongs to `ΔG`. -/
def IsBoundaryCircuit (G : FiniteConnectedSquareSubgraph) (c : DualCircuit) : Prop :=
  G.IsInteriorCircuit c ∧ c.crossedPrimalEdgeFinset ⊆ G.edgeBoundary

end FiniteConnectedSquareSubgraph

/-- **Grimmett, Proposition 11.2.**  Every finite connected square-lattice subgraph has a unique
surrounding shifted-dual boundary circuit, all of whose edges cross the edge boundary of the
subgraph.

The book explicitly delegates the rigorous planar-topological proof to Kesten (1982, p. 386), so
this is an axiom under the user's external-reference policy.  Uniqueness is stated for the
finite set of crossed primal edges: this is the extensional content of a circuit and deliberately
quotients away the choice of base point and orientation of its walk representation. -/
axiom existsUnique_boundaryCircuitCrossedEdges (G : FiniteConnectedSquareSubgraph) :
    ∃! E : Finset SquareEdge,
      ∃ c : DualCircuit,
        c.crossedPrimalEdgeFinset = E ∧ G.IsBoundaryCircuit c

/-- The finite crossing/noncrossing trace bijection behind Grimmett, Proposition 11.2 and
Equation 11.20. A rigorous planar-topological proof is delegated by Grimmett to Kesten,
*Percolation Theory for Mathematicians* (1982), p. 386. Rotation of the shifted dual rectangle
pairs every crossing trace with exactly one noncrossing trace. -/
noncomputable axiom grimmettRectangleDualTraceEquiv (n : ℕ) :
    {s // s ∈ grimmettRectangleCrossingTraces n} ≃
      {s // s ∈ grimmettRectangleNoncrossingTraces n}

/-- The dual trace paired with `s` has exactly the complementary set of edge states. This is the
weight-preserving part of the same externally delegated planar-duality bijection. -/
axiom card_grimmettRectangleDualTraceEquiv_apply (n : ℕ)
    (s : {s // s ∈ grimmettRectangleCrossingTraces n}) :
    ((grimmettRectangleDualTraceEquiv n s).1).card =
      (grimmettRectangleEdges n).card - s.1.card

/-- Crossing and noncrossing trace families have the same cardinality. -/
theorem card_grimmettRectangleCrossingTraces_eq_noncrossing (n : ℕ) :
    (grimmettRectangleCrossingTraces n).card =
      (grimmettRectangleNoncrossingTraces n).card := by
  simpa using Fintype.card_congr (grimmettRectangleDualTraceEquiv n)

/-- The lowest-crossing inequality in Grimmett, Lemma 11.73.  Grimmett explicitly notes that
the existence, uniqueness, and stopping-set property of the lowest crossing require topology not
proved in the book, and follows Russo (1981).  This declaration is exactly the probability
conclusion of that externally supplied step. -/
axiom rswThreeHalvesCrossingProbability_ge (p : I) (l : ℕ) :
    (1 - Real.sqrt (1 - rswSquareCrossingProbability p l)) ^ 3 ≤
      rswThreeHalvesCrossingProbability p l

/-- Self-dual planar circuit separation.  A primal open annular circuit has the same law at
density `1/2` as a shifted-dual closed circuit, and that dual circuit blocks a primal radial
crossing.  The topological separation is an instance of Grimmett, Proposition 11.2, whose
rigorous proof the book delegates to Kesten (1982), p. 386. -/
axiom rswAnnulusOpenCircuitProbability_le_half_barrier (l : ℕ) :
    rswAnnulusOpenCircuitProbability squareHalfDensity l ≤
      (bernoulliBondMeasure 2 squareHalfDensity).real
        (squareAnnulusBarrierEvent l (3 * l))

end Percolation
