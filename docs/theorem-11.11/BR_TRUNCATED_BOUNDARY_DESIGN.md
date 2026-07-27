# Finite truncated resolved boundary for the BR exploration

Status: API and proof design only. No declaration below has been checked by Lean. This document
was prepared without running Lean, Lake, or the Comparator.

## 1. Recommended model

Keep `brStoppedDualBoundaryEdge` as the ambient membership-change predicate, but do not use all
of its edges as the crossing interface. The crossing interface should contain only those boundary
dual bonds whose **two endpoints are faces of the finite exploration frame** and whose crossed
primal bond belongs to `squareBoundaryFreeRectangleEdges (2*n) n`. Its graph adjacency should use
only the dual-coordinate cells corresponding to primal vertices strictly between the bottom and
top sides of the square.

This gives three useful invariants.

1. Every retained dual bond is an actual edge of `brLeftmostDualGraph` crossing an allowed RSW
   coordinate, so a membership change across it can be converted into an open allowed primal
   bond.
2. A retained bond in the vertical interior is paired at two retained cells and has degree two.
   A retained bond crossing the bottom or top side is paired at one retained cell and has degree
   one.
3. Bonds between a reached face and a face outside the exploration frame are deleted. In
   particular, the artificial exterior-left arc caused by treating all outside faces as
   unreached is absent.

For the smallest implementation, define the graph as the full resolved graph induced on these
retained vertices. Immediately prove the stronger characterization that adjacency is witnessed by
a cell in `brTruncatedBoundaryCells`. That theorem is the semantic invariant: it verifies that a
partner supplied only by an excluded cell is not retained.

## 2. Coordinate dictionary

Write `Q_n = [0,2n] × [-n,n]` for the primal square. The existing exploration frame is

```text
F_n = { (x,y) : -1 <= x <= 2n and -n <= y < n }.
```

This is exactly `brLeftmostDualFaces n`. The column `x = -1` is the source column; `x = 2n` is
the right exterior column of faces.

For a positive dual bond `d`:

- if `d.axis = 0`, then `d` joins `(x,y)` to `(x+1,y)` and
  `dualToPrimalCrossingPositiveEdge d` is the vertical primal bond from `(x+1,y)` to
  `(x+1,y+1)`;
- if `d.axis = 1`, then `d` joins `(x,y)` to `(x,y+1)` and its crossed primal bond is the
  horizontal bond from `(x,y+1)` to `(x+1,y+1)`.

A dual-coordinate cell with lower-left corner `z` pairs the four dual bonds whose crossed primal
bonds meet the primal vertex `(z 0 + 1, z 1 + 1)`. Consequently the cells which may pair at a
primal vertex of `Q_n` but not at its bottom or top boundary are

```text
C_n = { z : -1 <= z 0 < 2n and -n <= z 1 < n-1 }.
```

Equivalently, `z ∈ C_n` iff `(z 0 + 1, z 1 + 1)` has horizontal coordinate in `[0,2n]` and
vertical coordinate strictly between `-n` and `n`.

The exact candidate finset is therefore:

```lean
noncomputable def brTruncatedBoundaryCells (n : ℕ) : Finset DualSquareVertex :=
  Fintype.piFinset fun i : Fin 2 ↦
    if i = 0 then
      Finset.Ico (-1 : ℤ) (2 * (n : ℤ))
    else
      Finset.Ico (-(n : ℤ)) ((n : ℤ) - 1)
```

Its first API theorem should be

```lean
@[simp] theorem mem_brTruncatedBoundaryCells_iff {z : DualSquareVertex} :
    z ∈ brTruncatedBoundaryCells n ↔
      -1 ≤ z 0 ∧ z 0 < 2 * (n : ℤ) ∧
        -(n : ℤ) ≤ z 1 ∧ z 1 < (n : ℤ) - 1
```

Using `Ico` avoids awkward `2*n-1` and `n-2` upper endpoints and makes the empty small cases
honest.

## 3. The exact truncated edge finset

The simplest implementation filters the already proved finite bounding set:

```lean
noncomputable def brTruncatedDualBoundaryPositiveEdges
    (n : ℕ) (R : Finset (BRLeftmostDualVertex n)) :
    Finset DualSquarePositiveEdge :=
  (brStoppedDualBoundaryBoundingPositiveEdges n).filter fun d ↦
    brStoppedDualBoundaryEdge n R d ∧
      d.base ∈ brLeftmostDualFaces n ∧
      cubicStepFrom d.base (d.axis, true) ∈ brLeftmostDualFaces n ∧
      (dualToPrimalCrossingPositiveEdge d).toEdge ∈
        squareBoundaryFreeRectangleEdges (2 * n) n
```

The bounding-set conjunct should disappear from the public membership theorem by using
`brStoppedDualBoundaryEdge_mem_boundingPositiveEdges`:

```lean
@[simp] theorem mem_brTruncatedDualBoundaryPositiveEdges_iff :
    d ∈ brTruncatedDualBoundaryPositiveEdges n R ↔
      brStoppedDualBoundaryEdge n R d ∧
      d.base ∈ brLeftmostDualFaces n ∧
      cubicStepFrom d.base (d.axis, true) ∈ brLeftmostDualFaces n ∧
      (dualToPrimalCrossingPositiveEdge d).toEdge ∈
        squareBoundaryFreeRectangleEdges (2 * n) n
```

There is an equivalent cell-local definition which should be proved, not used silently:

```lean
brTruncatedDualBoundaryPositiveEdges n R =
  ((brTruncatedBoundaryCells n).biUnion
    (squareCellBoundaryPositiveEdges (brReachedDualFace n R))).filter fun d ↦
      (dualToPrimalCrossingPositiveEdge d).toEdge ∈
        squareBoundaryFreeRectangleEdges (2 * n) n
```

The equivalence is an axis split. An internal horizontal dual bond has incident cells with
lower-left corners `(x,y)` and `(x,y-1)`; an internal vertical dual bond has incident cells
`(x,y)` and `(x-1,y)`. At least one is in `C_n`, and conversely every side of a cell in `C_n`
has both dual endpoints in `F_n`.

Use a nested subtype of the full stopped-interface type for graph vertices:

```lean
abbrev BRTruncatedInterfaceEdge
    (n : ℕ) (R : Finset (BRLeftmostDualVertex n)) :=
  {d : BRStoppedInterfaceEdge n R //
    d.1 ∈ brTruncatedDualBoundaryPositiveEdges n R}
```

The outer coercion `d.1` is then the inclusion into `BRStoppedInterfaceEdge`; no separately
defined embedding is needed. Constructing a vertex from a raw member uses the stopped-boundary
conjunct of `mem_brTruncatedDualBoundaryPositiveEdges_iff`. This choice makes the graph below
definitionally an induced subgraph and lets the truncated API apply
`brStoppedInterfaceIncidentAt`, `brResolvedBoundaryPairedAt`,
`brStoppedInterfacePrimalPositiveEdge`, and the full resolved-degree API directly to `d.1`.
If a raw subtype is useful for enumeration, define an equivalence to it as a secondary API; do
not make that raw subtype the graph's primary vertex type.

## 4. Valid separating reached sets

The degree theorem needs a hypothesis excluding changes along the two vertical face columns. Name
the right column first:

```lean
def brRightmostDualTargets (n : ℕ) : Finset (BRLeftmostDualVertex n) :=
  Finset.univ.filter fun z ↦ z.1 0 = 2 * (n : ℤ)

def BRSeparatingReachedSet
    (n : ℕ) (R : Finset (BRLeftmostDualVertex n)) : Prop :=
  brLeftmostDualSources n ⊆ R ∧ Disjoint R (brRightmostDualTargets n)
```

For the allowed-edge endpoint theorem, package actual fiber realizability as well:

```lean
def BRAdmissibleSeparatingFiber
    (n : ℕ) (R : Finset (BRLeftmostDualVertex n)) : Prop :=
  (∃ omega, omega ∈ brReachableFaceFiber n R) ∧
    Disjoint R (brRightmostDualTargets n)
```

For an actual fiber, source inclusion follows directly from `finiteGraphReachableFrom_source` and
`mem_finiteGraphReachableVertices_iff`. More importantly, every frame edge crossing a bond outside
`squareBoundaryFreeRectangleEdges (2*n) n` is deterministically exploration-open, so its two
faces have the same reached status. Hence every internal membership-change edge is automatically
allowed. The target disjointness is the genuine planar separation premise: a vertical
boundary-free open primal crossing prevents an effective-dual-open left-to-right frame walk.

Do not bake either predicate into the local boundary definitions. `BRSeparatingReachedSet` is
enough to eliminate left/right membership changes. `BRAdmissibleSeparatingFiber` is the correct
assumption when one must also know that every row change survives the explicit allowed-edge
filter and hence obtain odd bottom/top port sets.

## 5. Boundary ports

For the raw truncated edge finset define four side filters. These formulas are exact:

```lean
noncomputable def brTruncatedBottomBoundaryEdges (n : ℕ) (R : ...) :=
  (brTruncatedDualBoundaryPositiveEdges n R).filter fun d ↦
    d.axis = (0 : Fin 2) ∧ d.base 1 = -(n : ℤ)

noncomputable def brTruncatedTopBoundaryEdges (n : ℕ) (R : ...) :=
  (brTruncatedDualBoundaryPositiveEdges n R).filter fun d ↦
    d.axis = (0 : Fin 2) ∧ d.base 1 = (n : ℤ) - 1

noncomputable def brTruncatedLeftBoundaryEdges (n : ℕ) (R : ...) :=
  (brTruncatedDualBoundaryPositiveEdges n R).filter fun d ↦
    d.axis = (1 : Fin 2) ∧ d.base 0 = -1

noncomputable def brTruncatedRightBoundaryEdges (n : ℕ) (R : ...) :=
  (brTruncatedDualBoundaryPositiveEdges n R).filter fun d ↦
    d.axis = (1 : Fin 2) ∧ d.base 0 = 2 * (n : ℤ)
```

Lift these four finsets along the subtype equivalence when applying graph-degree lemmas. For a
separating reached set, the left finset is empty because both endpoints are sources and hence
reached; the right finset is empty because both endpoints are targets and hence unreached. For an
admissible fiber, every row membership change crosses an allowed bond, so the allowed-edge filter
does not remove a bottom or top change.

The bottom and top edges have the intended primal meaning:

- a bottom edge has dual base `(x-1,-n)`, axis `0`, and crosses the primal vertical bond
  `(x,-n)--(x,-n+1)`;
- a top edge has dual base `(x-1,n-1)`, axis `0`, and crosses
  `(x,n-1)--(x,n)`;
- in both cases `0 <= x <= 2n` follows from truncated-edge membership.

### 5.1 Adjacent-change descriptions

Use the already proved `adjacentChangeIndices` rather than reproving row parity. The correct scan
has `2*n+1` steps: it starts at face column `-1` and ends at face column `2n`.

```lean
noncomputable def brBottomBoundaryChangeIndices (n : ℕ) (R : ...) : Finset ℕ :=
  adjacentChangeIndices
    (fun x : ℤ ↦ brReachedDualFace n R
      (squareVertex x (-(n : ℤ))))
    (-1) (2 * n + 1)

noncomputable def brTopBoundaryChangeIndices (n : ℕ) (R : ...) : Finset ℕ :=
  adjacentChangeIndices
    (fun x : ℤ ↦ brReachedDualFace n R
      (squareVertex x ((n : ℤ) - 1)))
    (-1) (2 * n + 1)
```

Map the first set with `framedHorizontalPositiveEdgeEmbedding (-(n : ℤ))` and the second with
`framedHorizontalPositiveEdgeEmbedding ((n : ℤ) - 1)`. Prove that the resulting raw edge finsets
are exactly `brTruncatedBottomBoundaryEdges` and `brTruncatedTopBoundaryEdges`.

If `0 < n` and `BRAdmissibleSeparatingFiber n R`, the predicate at the left endpoint is true and
at the right endpoint false, and deterministic-open closure shows that every change is allowed.
Therefore `odd_card_adjacentChangeIndices_iff` gives

```lean
Odd (brTruncatedBottomBoundaryEdges n R).card
Odd (brTruncatedTopBoundaryEdges n R).card
```

This is the same finite parity mechanism used successfully in `SiteCrossingInterface.lean`.

### 5.2 Distinguished bottom and top edges

Do not define an unconditional singular endpoint: an arbitrary reached set may have several row
changes, and local pairing alone does not show which components join opposite sides.

For an admissible separating fiber, the source face in each row is reached and the right-column
face is not. The source-faithful distinguished port is the **rightmost reached face**, not the
first row change seen from `x=-1`. Row membership need not be an interval, so the first change may
merely bound a bay. Fiber realizability ensures the final change crosses an allowed bond.

Define the finite row sections

```lean
noncomputable def brReachedRowColumns
    (n : ℕ) (R : Finset (BRLeftmostDualVertex n)) (j : ℤ) : Finset ℤ :=
  (Finset.Icc (-1 : ℤ) (2 * (n : ℤ))).filter fun x ↦
    brReachedDualFace n R (squareVertex x j)
```

Under `BRSeparatingReachedSet n R`, each relevant row section is nonempty (it contains `-1`) and
its maximum is strictly below `2n`. Set

```text
b_bottom = max (brReachedRowColumns n R (-n))
b_top    = max (brReachedRowColumns n R (n-1)).
```

The exact distinguished raw edges are

```lean
brDistinguishedBottomBoundaryPositiveEdge =
  (⟨squareVertex b_bottom (-(n : ℤ)), (0 : Fin 2)⟩ : DualSquarePositiveEdge)

brDistinguishedTopBoundaryPositiveEdge =
  (⟨squareVertex b_top ((n : ℤ) - 1), (0 : Fin 2)⟩ : DualSquarePositiveEdge)
```

They are changes because the face at `b_*` is reached while the face at `b_* + 1` is not; the
latter follows from maximality. They cross the vertical primal ports at horizontal coordinates
`b_bottom + 1` and `b_top + 1`. Prove that they belong to the bottom and top port finsets and that
their bases are the largest elements of the corresponding adjacent-change sets.

The still-missing global theorem is that these two distinguished edges lie on the same resolved
outer/right component. Equivalently, orient the full outer boundary with `R` on the left, traverse
away from the fixed outside-left arc, and trim from the last bottom contact to the first subsequent
top contact. These traversal extrema give the same rightmost-row-change edges above. Hole
components are cycles with no side port and must not be advertised as the leftmost crossing.

As a smaller existence milestone, let `B` and `T` be the lifted port finsets and `G` the truncated
graph and define

```lean
noncomputable def brBottomTopReachablePairs (n : ℕ) (R : ...) :
    Finset (BRTruncatedInterfaceEdge n R × BRTruncatedInterfaceEdge n R) :=
  (B.product T).filter fun p ↦ G.Reachable p.1 p.2
```

Parity proves this finset nonempty, but an arbitrary or lexicographically least reachable pair is
only a bottom--top crossing witness. It is not a substitute for the distinguished outer/right
pair in the source-facing canonical-path theorem.

## 6. Truncated graph definition

Use the full resolved graph and induce it on the allowed, frame-internal boundary edges:

```lean
def brTruncatedResolvedBoundaryGraph
    (n : ℕ) (R : Finset (BRLeftmostDualVertex n)) :
    SimpleGraph (BRTruncatedInterfaceEdge n R) :=
  (brResolvedBoundaryGraph n R).induce
    {d | d.1 ∈ brTruncatedDualBoundaryPositiveEdges n R}
```

With the nested subtype of Section 3, the displayed return type is definitionally the vertex
type of this `induce`. This is the smallest implementation: symmetry, looplessness, and all full
pairing facts are inherited rather than reproved.

Immediately prove the geometric lemma which makes this induced graph semantically safe:

```lean
theorem mem_brTruncatedBoundaryCells_of_pairedAt_of_mem_truncated
    {d e : BRStoppedInterfaceEdge n R} {z : DualSquareVertex}
    (hd : d.1 ∈ brTruncatedDualBoundaryPositiveEdges n R)
    (he : e.1 ∈ brTruncatedDualBoundaryPositiveEdges n R)
    (hpair : brResolvedBoundaryPairedAt z d e) :
    z ∈ brTruncatedBoundaryCells n
```

The proof is a four-side coordinate split. A cell outside `C_n` but incident to a frame-internal
edge has exactly one side whose two endpoints lie in `F_n`; `hpair` supplies two distinct sides,
so both retained edges cannot be paired there. Package the result as the public adjacency API:

```lean
@[simp] theorem brTruncatedResolvedBoundaryGraph_adj_iff
    {d e : BRTruncatedInterfaceEdge n R} :
    (brTruncatedResolvedBoundaryGraph n R).Adj d e ↔
      ∃ z ∈ brTruncatedBoundaryCells n,
        brResolvedBoundaryPairedAt z d.1 e.1
```

Thus the graph is implemented by `induce`, while its proved invariant still says that every
adjacency is witnessed inside the truncation. This is preferable to maintaining a second custom
`SimpleGraph` and later proving an equivalence between the two.

## 7. Incident cells and degree

The current compiled `BRResolvedDegree.lean` supplies the hard local uniqueness work:
`brResolvedIncidentCells`, `BRResolvedIncidentCell`, `brResolvedBoundaryPartner`,
`brResolvedBoundaryPartner_pairedAt`, `brResolvedBoundaryPartner_injective`,
`brResolvedIncidentCellEquivNeighborSet`, and `brResolvedBoundaryGraph_degree_eq_two`.
Use the selected full-graph partner instead of reconstructing a partner for the induced graph.

For an arbitrary reached set, the exact incident-cell type for the induced graph is

```lean
abbrev BRTruncatedPartnerIncidentCell
    (d : BRTruncatedInterfaceEdge n R) :=
  {z : BRResolvedIncidentCell d.1 //
    (brResolvedBoundaryPartner d.1 z.1).1 ∈
      brTruncatedDualBoundaryPositiveEdges n R}
```

Map such a cell to the induced neighbor whose stopped-edge value is
`brResolvedBoundaryPartner d.1 z.1`. The membership field above constructs the nested vertex;
`brResolvedBoundaryPartner_pairedAt` constructs the adjacency. Injectivity is exactly
`brResolvedBoundaryPartner_injective`; surjectivity follows from
`brTruncatedResolvedBoundaryGraph_adj_iff` and fixed-cell right uniqueness. Package this as

```lean
noncomputable def brTruncatedPartnerIncidentCellEquivNeighborSet
    (d : BRTruncatedInterfaceEdge n R) :
    BRTruncatedPartnerIncidentCell d ≃
      (brTruncatedResolvedBoundaryGraph n R).neighborSet d
```

and first obtain the completely general formula

```lean
theorem degree_brTruncatedResolvedBoundaryGraph_eq_card_partner_cells :
    (brTruncatedResolvedBoundaryGraph n R).degree d =
      Fintype.card (BRTruncatedPartnerIncidentCell d)
```

For the geometric calculation, separately define the simpler finset

```lean
noncomputable def brTruncatedResolvedIncidentCells
    (d : BRTruncatedInterfaceEdge n R) : Finset DualSquareVertex :=
  (brResolvedIncidentCells d.1).filter fun z ↦
    z ∈ brTruncatedBoundaryCells n
```

The bridge between the two notions is where fiber realizability is used:

```lean
theorem brResolvedBoundaryPartner_mem_truncated_iff
    (hreal : ∃ omega, omega ∈ brReachableFaceFiber n R)
    (d : BRTruncatedInterfaceEdge n R) (z : BRResolvedIncidentCell d.1) :
    (brResolvedBoundaryPartner d.1 z).1 ∈
        brTruncatedDualBoundaryPositiveEdges n R ↔
      z.1 ∈ brTruncatedBoundaryCells n
```

The forward implication is the no-two-retained-sides-outside-`C_n` coordinate lemma. For the
reverse implication, pairing already gives the stopped-boundary predicate, `z ∈ C_n` gives both
endpoints in the frame, and actual fiber realizability plus
`not_mem_brClosedDualExplorationConfiguration_iff_of_mem_edgeSet` proves that the crossed bond is
allowed (and open). Consequently

```lean
theorem degree_brTruncatedResolvedBoundaryGraph
    (hreal : ∃ omega, omega ∈ brReachableFaceFiber n R)
    (d : BRTruncatedInterfaceEdge n R) :
    (brTruncatedResolvedBoundaryGraph n R).degree d =
      (brTruncatedResolvedIncidentCells d).card
```

Do not state this simpler formula for arbitrary `R`: the explicit allowed-edge filter can remove
the partner selected at an interior cell unless `R` is known to be an effective-exploration
fiber. The partner-cell formula above remains valid without hypotheses.

An axis split then gives the complete general classification for any truncated vertex `d`:

```text
card(truncated incident cells of d) = 1
  iff d is in Bottom ∪ Top ∪ Left ∪ Right;

card(truncated incident cells of d) = 2
  iff d is in none of those four port sets.
```

For a realizable fiber there are no degree-zero vertices, because membership in the truncated
edge finset gives an incident cell in `C_n` and the partner at that cell is retained. No such
claim is needed for an arbitrary artificial reached set.

Under `BRAdmissibleSeparatingFiber n R`, its separating-set consequence makes Left and Right
empty and its realizability consequence supplies the degree formula, so the public endpoint
theorem is

```lean
theorem degree_brTruncatedResolvedBoundaryGraph_eq_one_iff
    (hn : 0 < n) (hsep : BRAdmissibleSeparatingFiber n R) (d : ...) :
    (brTruncatedResolvedBoundaryGraph n R).degree d = 1 ↔
      d ∈ B ∨ d ∈ T
```

and every other vertex has degree two. Equivalently,

```lean
Odd ((brTruncatedResolvedBoundaryGraph n R).degree d) ↔ d ∈ B ∨ d ∈ T.
```

The vertex type is finite, so support finiteness is immediate. Apply
`SimpleGraph.exists_reachable_between_of_odd_degree_partition` with the odd bottom finset to get

```lean
∃ b ∈ B, ∃ t ∈ T,
  (brTruncatedResolvedBoundaryGraph n R).Reachable b t.
```

This parity route is the shortest safe milestone. It proves a bottom--top component exists but
does not, by itself, identify the outer/right component required by the BR stopping argument.

## 8. What the full-boundary model adds

`brReachedDualFace n R` is false outside `F_n`. If the source column is contained in `R`, every
edge

```text
d_y = <base = (-2,y), axis = 0>,  -n <= y < n,
```

is a full stopped-boundary edge: its left endpoint is outside the frame and unreached, while its
right endpoint `(-1,y)` is a reached source face. The two cap edges

```text
d_bottom = <base = (-1,-n-1), axis = 1>
d_top    = <base = (-1, n-1), axis = 1>
```

are boundary edges for the same reason. Cell-local pairing joins the `d_y` into a vertical
exterior-left strand and joins its ends to the two caps. Pairings in the exterior bottom and top
cell rows may enter and leave boundary bays. The source-facing trim uses the last bottom contact
and first subsequent top contact, equivalently the rightmost reached-face changes described in
Section 5.2. Thus the outer full-boundary component contains an exterior arc between bottom and
top contacts. Once the
distinct-cell-partner lemma is proved, the unrestricted graph is naturally two-regular, so its
components are cycles rather than graphs with distinguished boundary endpoints.

These exterior bonds are not harmless:

- they are not edges of `brLeftmostDualGraph`;
- the exploration never queried their primal crossings;
- their crossed primal bonds are therefore not forced open by membership in a reachable-face
  fiber;
- following the full graph can follow this artificial arc instead of the desired separator.

The truncation deletes every bond with an endpoint outside `F_n`. It also deletes pairings through
the cell rows `y=-n-1`, `y=n-1` and the cell columns `x=-2`, `x=2n`. A horizontal cut edge in row
`y=-n` or `y=n-1` retains exactly its interior pairing, so it becomes a degree-one bottom or top
port. This is the precise sense in which truncation cuts the exterior cycle into finite paths.

For a canonical outer separator, prove an explicit walk along the deleted exterior arc in the
full graph, identify the complementary part of that full component, and then trim the complement
from its last bottom contact to its first top contact. This finite cycle argument replaces a
Jordan-curve assertion; it is not a consequence of fixed-cell uniqueness alone.

## 9. Openness of retained boundary bonds

The retained-edge membership theorem supplies both endpoints in `F_n`, hence an edge of the
induced graph `brLeftmostDualGraph n`. If exactly one endpoint lies in the reached set `R`, that
frame edge cannot be open in the dual exploration: otherwise
`finiteGraphReachableFrom_step` would reach the other endpoint. With
`omega ∈ brReachableFaceFiber n R`, use

- `mem_finiteGraphReachableVertices_iff`,
- `finiteGraphReachableFrom_step`, and
- `not_mem_brClosedDualExplorationConfiguration_iff_of_mem_edgeSet`

to conclude simultaneously that the crossed primal edge is allowed by
`squareBoundaryFreeRectangleEdges (2*n) n` and is open.

The intended theorem is deliberately restricted to truncated edges:

```lean
theorem brStoppedInterfacePrimalPositiveEdge_mem_of_mem_fiber
    (hω : ω ∈ brReachableFaceFiber n R)
    (d : BRTruncatedInterfaceEdge n R) :
    (brStoppedInterfacePrimalPositiveEdge d.1).toEdge ∈ ω
```

There must be no corresponding theorem for arbitrary `BRStoppedInterfaceEdge`: it is false for
the exterior arc.

## 10. Boundary-free exploration correction and remaining event bridge

An earlier version of `BRDualExploration.lean` declared a frame dual edge open exactly when its
crossed primal bond was closed. That semantics mismatched
`squareBoundaryFreeRectangleCrossingEvent (2*n) n`, because that event removes bonds whose two
endpoints lie on the rectangle boundary. The mismatch is now corrected in the current module.

Writing `A_n = squareBoundaryFreeRectangleEdges (2*n) n`, the current declaration
`brClosedDualExplorationConfiguration` makes a frame edge exploration-open exactly when

```text
crossedPrimalEdge ∉ A_n OR crossedPrimalEdge ∉ omega.
```

Thus excluded perimeter bonds are deterministically dual-open. The exact public APIs are:

- `mem_brClosedDualExplorationConfiguration_iff_of_mem_edgeSet`, which exposes the disjunction;
- `mem_brClosedDualExplorationConfiguration_iff_dual_open_of_crossed_mem`, which reduces to
  ordinary primal-closed/dual-open semantics after an `A_n` membership proof;
- `not_mem_brClosedDualExplorationConfiguration_iff_of_mem_edgeSet`, which turns failure of
  exploration openness into `crossedPrimalEdge ∈ A_n ∧ crossedPrimalEdge ∈ omega`.

The current `brReachableFaceFiberSupport` is also filtered by `A_n`, and
`dependsOn_brReachableFaceFiber` has been reproved for that filtered support. These are landed
prerequisites of the truncated-boundary proof, not work still to be implemented.

The remaining gate is the global event bridge: prove that a boundary-free open bottom--top primal
crossing is complementary to effective-dual reachability of the right target column, then connect
the nonreaching fiber to the truncated resolved separator. This needs an explicit finite planar
separation argument; the local exploration definitions and support theorem do not prove it by
themselves.

Keep the `n=1` former-mismatch example as a regression test: opening only the two vertical bonds
on the left side of `Q_1` gives a bottom--top crossing if all perimeter bonds are admitted, but
those bonds are excluded from `squareBoundaryFreeRectangleEdges 2 1`. Under the corrected
exploration they are deterministic dual-open, so this configuration must not be classified as a
blocked boundary-free dual crossing. This test guards the eventual event bridge against silently
reverting to full-edge semantics.

The local truncation definitions remain valid for an arbitrary `R`. Fiber realizability is
needed precisely where allowed-partner closure, bottom/top parity, openness of retained bonds, or
the boundary-free event bridge is asserted.

## 11. Reusable declarations

### From `SiteCrossingInterface.lean`

- `adjacentChangeIndices` and `odd_card_adjacentChangeIndices_iff`: bottom/top port parity.
- `framedHorizontalPositiveEdgeEmbedding`: the exact index-to-horizontal-edge map needed for both
  port finsets; `DualSquarePositiveEdge` is definitionally the same coordinate type.
- `cubicStepFrom_squareVertex_horizontal_pos`: row-change membership calculations.
- `mem_cells_or_bottom_or_top_of_mem_interface_incident`: not directly applicable to the BR
  predicate, but its four-side coordinate proof is the template for the BR port classification.
- `degree_siteRectangleInterfaceDualGraph_eq_one_of_mem_bottom` and the top analogue: proof
  templates for singleton incidence at a truncated side.
- `odd_degree_siteRectangleInterfaceDualGraph_iff`: template for the final degree statement.
- `SimpleGraph.exists_reachable_between_of_odd_degree_partition`: reusable unchanged for the
  bottom--top component.

### From `BRDualExploration.lean`

- `mem_brLeftmostDualFaces_iff`, `brLeftmostDualGraph_adj_iff`, and
  `mem_brLeftmostDualSources_iff`: coordinate and induced-graph normalization.
- `brLeftmostDualEdgeEmbedding` and
  `not_mem_brClosedDualExplorationConfiguration_iff_of_mem_edgeSet`: convert a retained frame cut
  directly into an allowed, open crossed primal bond.
- `mem_brClosedDualExplorationConfiguration_iff_of_mem_edgeSet` and
  `mem_brClosedDualExplorationConfiguration_iff_dual_open_of_crossed_mem`: effective-exploration
  simplification before and after an allowed-edge proof.
- `brLeftReachableFaces`, `brReachableFaceFiber`, and
  `dependsOn_brReachableFaceFiber`: the stopped-set and locality layer.
- `brReachableFaceFiberSupport`, `pairwiseDisjoint_brReachableFaceFiber`, and
  `biUnion_brReachableFaceFiber_eq_univ`: later probability partitioning.

### From `BRResolvedBoundary.lean`

- `brReachedFaceCoordinates`, `brReachedDualFace`, and `brStoppedDualBoundaryEdge`: the ambient
  predicate being truncated.
- `brStoppedDualBoundaryBoundingPositiveEdges` and
  `brStoppedDualBoundaryEdge_mem_boundingPositiveEdges`: finiteness without a second coordinate
  enclosure proof.
- `BRStoppedInterfaceEdge` and `brStoppedInterfacePrimalPositiveEdge_injective`: conversion to
  primal bonds.
- `brStoppedInterfaceIncidentAt`, `brResolvedBoundaryPairedAt`,
  `brResolvedBoundaryPairedAt_comm`, and `not_brResolvedBoundaryPairedAt_self`: graph definition.
- `existsUnique_brResolvedBoundaryPartnerAt` and
  `brResolvedBoundaryPairedAt_right_unique`: unique partner at a **fixed** cell.
- `brResolvedBoundaryGraph` and `brResolvedBoundaryGraph_adj_iff`: the full graph to induce and
  its cell-witness characterization.

Use `brResolvedBoundaryGraph` only through `SimpleGraph.induce` on the retained set; the full
graph itself contains the exterior arc. Do not infer a global component theorem merely from
fixed-cell partner uniqueness.

### From `BRResolvedDegree.lean`

- `brResolvedIncidentCells`, `mem_brResolvedIncidentCells_iff`, and
  `card_brResolvedIncidentCells_eq_two`: the two cells around a stopped edge.
- `BRResolvedIncidentCell`, `brResolvedBoundaryPartner`, and
  `brResolvedBoundaryPartner_pairedAt`: a canonical partner at each incident cell.
- `brResolvedBoundaryPartner_injective`: distinct incident cells give distinct partners; this
  discharges the formerly missing local geometry bridge.
- `brResolvedIncidentCellToNeighbor_injective`,
  `brResolvedIncidentCellToNeighbor_surjective`, and
  `brResolvedIncidentCellEquivNeighborSet`: templates and reusable proofs for the induced-neighbor
  equivalence.
- `brResolvedBoundaryGraph_degree_eq_two`: confirms the unrestricted graph is two-regular.
- `squarePositiveEdge_eq_of_mem_two_brResolvedIncidentCells`: use only if the truncated
  coordinate proof needs the underlying two-cell intersection lemma explicitly.

### From `ResolvedRectangleInterface.lean` and the cell API

- `squareCellBoundaryPositiveEdges` and `squareCellBoundarySplitTag`.
- `existsUnique_squareCellBoundaryPositiveEdge_partner`.
- `card_squareCellBoundaryPositiveEdges_filter_splitTag_eq_two` when an explicit local card
  calculation is more convenient.
- `mem_squareCellPositiveEdges_iff_mem_crossing` and
  `squarePositiveEdgeDualCrossingEmbedding` for incident-cell coordinates.
- `primalToDual_dualToPrimalCrossingPositiveEdge` and its inverse for state transport.

The truncated-boundary module should import `BRResolvedDegree.lean` directly. Reusing its partner
map and injectivity is substantially smaller than reopening the split-tag uniqueness proof.

## 12. Implementation order and proof gates

1. Import and use the corrected effective-exploration API and `BRResolvedDegree.lean`; do not
   duplicate either local theory.
2. Define `brRightmostDualTargets`, `BRSeparatingReachedSet`, and
   `BRAdmissibleSeparatingFiber`; prove source inclusion for actual reachable sets.
3. Define `brTruncatedBoundaryCells` and its coordinate membership theorem.
4. Define `brTruncatedDualBoundaryPositiveEdges`; prove the public membership theorem and its
   equality with the allowed-filtered cell `biUnion`.
5. Define the nested finite edge subtype and define
   `brTruncatedResolvedBoundaryGraph` by inducing `brResolvedBoundaryGraph` on it.
6. Prove that a full pairing of two retained vertices is witnessed in a retained cell, then expose
   `brTruncatedResolvedBoundaryGraph_adj_iff`.
7. Restrict `brResolvedBoundaryPartner` to retained partners and prove the unconditional
   partner-cell/induced-neighbor equivalence.
8. Under fiber realizability, prove
   `brResolvedBoundaryPartner_mem_truncated_iff`; derive degree as the cardinality of incident
   cells filtered by `brTruncatedBoundaryCells`.
9. Define all four port finsets and prove the geometric one-cell/four-port classification.
10. Under `BRAdmissibleSeparatingFiber`, eliminate left/right ports, prove the bottom/top
    degree-one classification and oddness, and apply
    `exists_reachable_between_of_odd_degree_partition`.
11. Prove retained boundary bonds cross open allowed primal bonds on a fiber using
    `not_mem_brClosedDualExplorationConfiguration_iff_of_mem_edgeSet`. Do not generalize this to
    the full boundary subtype.
12. Prove the corrected boundary-free primal-crossing/effective-dual-target event bridge and add
    the `n=1` regression test described in Section 10.
13. Identify the outer component via the explicit exterior arc and trim it from the last bottom
    contact to the first top contact. Treat this as a separate global theorem.

The local degree milestone and the global outer-component milestone should remain separate. A
successful degree proof does not establish that the selected component is the BR leftmost
crossing, and the landed effective-exploration correction does not by itself establish the global
boundary-free event bridge.
