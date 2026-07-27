# Theorem 11.11: rigorous expansion of the pictorial steps

## Scope and evidence

This note expands the planar arguments needed to prove that bond percolation on the square
lattice has critical probability `1/2`.  It is written as a proof-engineering document: every
appeal to a picture is replaced by a finite graph, parity, reachability, or path-intersection
claim which can be stated in Lean.

The sources inspected were:

- Geoffrey Grimmett, *Percolation*, second edition (1999), Chapter 11, especially Proposition
  11.2 on printed p. 284; Theorem 11.11 and Lemmas 11.12 and 11.21 on pp. 287--294; and the RSW
  material, Theorem 11.70 and Lemmas 11.73 and 11.75, on pp. 315--323.  The relevant figures are
  11.4 and 11.6--11.10, then 11.19--11.27.
- Béla Bollobás and Oliver Riordan, "A Short Proof of the Harris--Kesten Theorem",
  *Bull. London Math. Soc.* 38 (2006), 470--484, especially Lemma 3 and Figure 2 on pp. 473--474,
  Lemma 6 and Corollary 7 with Figures 3--5 on pp. 475--477, Lemma 9 on pp. 477--479, and the
  three proofs of Theorem 10 on pp. 479--482.
- The historical Chapter 11 and Chapter 8 snapshots at commits
  `9481b37e8375b3c6ef55a503cd1a59735886a3f0` and
  `35b7d534500da15d37db764e8c80d6610dfed812`, followed by a fresh audit of the
  expanded Chapter 12 implementation at
  `fa865689167d867e63986dbc5f0d8c51ae1e841c`.

Declaration names below were rechecked against the expanded Chapter 12 implementation. Suggested
new lemmas are described by their mathematical statements and are explicitly labelled
**proposed** rather than presented as existing declarations.

## Recommendation about the proof source

Use Grimmett as the primary source, with Bollobás--Riordan as a supplementary source for two
finite planar constructions.

The complete Bollobás--Riordan route is shorter on paper, but its upper bound `p_c <= 1/2` uses
the Friedgut--Kalai sharp-threshold theorem (their Theorem 2), a torus symmetrization, and then a
renormalization argument.  No Friedgut--Kalai implementation was found in the inspected branch.
Formalizing that theorem would be a substantial new project unrelated to the planar geometry.
Grimmett's second proof of the upper bound instead uses the already formalized subcritical
exponential radius decay and one exact finite-rectangle crossing probability.  The existing Lean
proof `cubicCriticalProbability_two_le_half_of_crossingProbability` already implements the entire
analytic contradiction once the exact crossing lemma is supplied.

For the lower bound, Grimmett's printed proof of Lemma 11.12 uses uniqueness of the infinite
cluster and the four-arm picture in Figure 11.7.  The uniqueness theorem does exist on the Chapter
8 branch as `unique_infiniteOpenCluster_almostSure_of_theta_pos`, but Figure 11.7 hides a global
separation theorem about four infinite arms in a punctured plane.  That theorem is harder to
formalize safely than a finite annular argument.  Bollobás--Riordan's Theorem 8 gives the better
formalization route for this half: obtain a uniform long-rectangle crossing bound, place four
crossings in disjoint annuli, and use independent barriers.  This is also compatible with
Grimmett's later RSW material in Section 11.7.

Thus the recommended proof is:

1. Grimmett Lemma 11.21 plus the existing exponential-decay argument for `p_c <= 1/2`.
2. A finite lowest/leftmost-crossing lemma in the style of Bollobás--Riordan Lemma 6, followed by
   their Corollary 7 and Theorem 8, for `theta(1/2) = 0` and hence `p_c >= 1/2`.
3. Use Grimmett Section 11.7 only if the project also wants the full numerical RSW theorem.  The
   exact threshold itself needs only a positive scale-uniform annular barrier probability, not
   the explicit expression in (11.71).

This route preserves the source theorem while avoiding both the Friedgut--Kalai theorem and the
global four-infinite-arm separation hidden in Figure 11.7.

## Dependency skeleton

```text
finite primal/dual edge crossing equivalence
  |
  +-- finite rectangle alternative -- self-duality at p=1/2 -- P(crossing)=1/2
  |                                                    |
  |                                                    +-- subcritical exponential decay
  |                                                         gives p_c <= 1/2
  |
  +-- canonical leftmost/lowest crossing and stopping-set property
       |
       +-- uniform positive long-rectangle crossing probability at p=1/2
            |
            +-- four finite crossings give an annular dual barrier
                 |
                 +-- disjoint annular supports give independent barriers
                      |
                      +-- theta(1/2)=0, hence p_c >= 1/2
```

Only the two finite ideas implicit in the diagram--the rectangle alternative and the
canonical lowest-crossing stopping property--require new planar work.  Both admit finite
combinatorial proofs; neither requires a general Jordan curve theorem.

## Coordinate and state conventions

Work with primal vertices `Z^2` and shifted-dual face coordinates, encoded in the repository by
the same `Cubic 2` coordinate type.  A primal bond and its shifted-dual crossing bond are paired by
the verified equivalence `squareEdgeDualCrossingEquiv`.  The configuration
`dualSquareConfiguration omega` declares a dual bond open exactly when its crossed primal bond is
closed; this is the content of `dualSquareConfiguration_open_iff`.

All geometric objects used in a proof should be finite:

- replace a walk by `Walk.toPath` before reasoning about separation;
- represent a rectangle by a finite vertex finset, edge finset, and four side finsets;
- represent an alleged "inside" by a mod-two face index or by reachability in a finite framed
  cell graph;
- represent an infinite arm at scale `N` by a finite path to the boundary of a larger box and
  pass to all scales only after the deterministic finite lemma is proved.

The repository already contains the right edge/state layer: `squareEdgeDualCrossingEquiv`,
`dualSquareConfiguration`, `dualWalkIsOpen`, `DualCircuit`, and
`DualCircuit.crossedPrimalEdgeFinset` in `Percolation/Planar/Basic.lean`.

## 1. The finite rectangle crossing alternative

### Source claim

Grimmett pp. 292--294 and Figures 11.9--11.10 assert that a left--right open crossing of the
primal rectangle and a top--bottom closed crossing of its shifted dual are mutually exclusive and
collectively exhaustive.  Bollobás--Riordan Lemma 3, pp. 473--474 and Figure 2, gives a more
explicit "middle graph" construction and notes precisely where an easy Jordan argument is still
being used.

The formal statement should say: for every assignment of states to the finite rectangle edges,
exactly one of the following holds.

1. There is a primal path from the left side to the right side using open rectangle edges.
2. There is a shifted-dual path from the framed top side to the framed bottom side, every edge of
   which crosses a closed primal rectangle edge.

The offsets and omitted side-boundary edges must match the literal rectangle
`[0,n+1] x [0,n]`; an informal "same rectangle after rotation" is not enough.

### Exhaustiveness without topology: reachable frontier with two odd ports

Fix a configuration and let `D` be the set of rectangle vertices reachable from the left side by
open paths which stay in the rectangle.  If no left--right crossing exists, `D` is disjoint from
the right side.

Frame the rectangle by one layer of dual cells.  Put a dual edge in `F` exactly when its crossed
primal edge has one endpoint in `D` and one outside `D`.  Add the natural exterior dual boundary
segments, contract the exterior chain above the rectangle to one top port, and contract the
exterior chain below it to one bottom port.  Then:

1. Every primal edge crossed by an interior edge of `F` is closed.  Otherwise its endpoint outside
   `D` would be reachable by appending that open edge.
2. At each interior dual vertex, the degree in `F` is even.  Traverse the four primal vertices
   around the square cell cyclically and record their membership bits in `D`.  An edge of `F`
   occurs exactly at a bit change.  A cyclic Boolean word has an even number of changes.
3. Every framed boundary vertex other than the two ports also has even degree.  The left seed
   convention and the fact that `D` misses the right side leave exactly one odd top port and one
   odd bottom port.
4. In a finite graph, each connected component has an even number of odd-degree vertices.  Hence
   the two odd ports lie in the same component, and a finite walk between them exists.  Erase
   loops to obtain a top--bottom path.

This is the rectangle dual barrier.  It is a finite degree-parity argument, not a Jordan curve
argument.  The existing site-percolation development demonstrates the same implementation
pattern: `exists_closed_squareStar_path_bottom_top_of_not_crossing` in
`SiteCrossingInterface.lean` builds an interface from reachable vertices, proves local degree
parity, and extracts a bottom--top path.

### Mutual exclusion without topology: mod-two intersection

Suppose a primal left--right path `P` and a shifted-dual top--bottom path `Q` both exist.  Define a
bit on dual vertices by the parity of the number of edges of `P` crossing a fixed ray from that
face to the left exterior.  The bit is `0` at one framed vertical end and `1` at the other.  Along
one step of `Q`, the bit changes exactly when that dual step crosses an edge of `P`.  Therefore
some edge of `Q` crosses an edge of `P`.

The crossing correspondence is one-to-one: the crossed primal edge is open because it lies in
`P`, while it is closed because its dual edge lies in `Q`.  This is impossible.  This proof uses
only parity along a finite list of adjacent faces.

An equivalent implementation is to close `P` outside the rectangle and compare face parity at
the endpoints of `Q`.  The already proved APIs
`closedSquareWalkFaceParity_eq_of_adj_of_not_mem` and
`closedSquareWalkFaceParity_eq_along_disjoint_walk` show how to formalize "the index is constant
until a path crosses the closed walk".  The file `AlternatingPaths.lean` then uses that device to
prove `squareWalk_support_inter_of_bottomLeft_right_and_bottomRight_top` and its rotated variants,
without importing a topological Jordan theorem.

### From the alternative to an exact half probability

Do not axiomatize a mysterious trace bijection.  Define explicitly the finite configuration map:

1. send every primal rectangle edge to its crossing shifted-dual edge;
2. rotate and translate the framed dual rectangle onto the original rectangle;
3. complement all edge bits.

The map is an involution.  The rectangle alternative proves

```text
primal configuration crosses  <->  transformed configuration does not cross.
```

At density `1/2`, all finite traces have the same weight, so the involution pairs crossing and
noncrossing traces and the crossing probability is `1/2`.  At general density it gives Grimmett
(11.20), with `p` paired with `1-p`.

The expanded Chapter 12 implementation has discharged this former axiom. The finite
left-reachable interface is constructed in `BondCrossingInterface.lean`, dual openness is proved
in `BondCrossingDuality.lean`, and
`half_le_squareRectangleCrossingProbability_centered` supplies the self-dual half-density bound.
Consequently `cubicCriticalProbability_two_le_half_via_bond_interface` and the complete upper
bound use only Lean's standard axioms.

## 2. The easy upper bound `p_c <= 1/2`

This half is no longer pictorial once the exact finite crossing result is available.

Assume for contradiction that `1/2 < p_c`.  Subcritical exponential decay gives constants
`c > 0` such that the probability of an open connection from a fixed vertex to radius `n+1` is at
most `exp(-c(n+1))`.  A left--right crossing of `[0,n+1] x [0,n]` starts at one of its `n+1` left
side vertices and connects that vertex to radius at least `n+1`.  A union bound therefore gives

```text
P_{1/2}(rectangle crossing) <= (n+1) exp(-c(n+1)) -> 0.
```

This contradicts the exact value `1/2` for every `n`.  The existing declarations
`grimmettRectangleCrossingEvent_subset_biUnion_radiusConnectionEvent`,
`grimmettRectangleCrossingProbability_le`, and
`cubicCriticalProbability_two_le_half_of_crossingProbability` already formalize these steps.
No further planar theorem is hidden here.

## 3. Canonical lowest/leftmost crossings

### What must actually be proved

Both Grimmett Lemma 11.73 (pp. 316--322, Figures 11.21--11.24) and Bollobás--Riordan Lemma 6
(p. 475, Figure 3) use a canonical lowest or leftmost crossing.  Three properties are required:

1. existence whenever a crossing exists;
2. uniqueness as an actual normalized path, not merely existence of some minimal element;
3. the stopping-set property: the event that the canonical crossing equals a fixed path `P`
   depends only on the edges on the selected side of `P`, and not on fresh edges on the other
   side.

The third item is the probabilistic heart.  A lexicographically least open path does **not** work
unless its ordering is proved to have this locality property.

### Finite combinatorial definition of "below" or "left"

First replace every crossing by its self-avoiding path.  For a fixed horizontal path `P`, create a
finite face graph for the rectangle plus an exterior bottom vertex.  Delete every face-adjacency
edge whose primal crossing edge belongs to `P`.  Define `Below(P)` to be the faces reachable from
the bottom exterior vertex.  Define `Above(P)` similarly from the top.  For a vertical crossing,
use `Left(P)` and `Right(P)`.

These are ordinary finite reachability sets.  No use is made of a real planar region or of simple
connectedness.  The key deterministic lemmas are:

- `Below(P)` and `Above(P)` are disjoint for a self-avoiding left--right crossing `P`;
- every rectangle face not incident to `P` is in exactly one of them;
- for two crossings `P,Q`, the boundary of `Below(P) ∩ Below(Q)` contains a left--right crossing
  whose edges are drawn from `P ∪ Q` and which lies below both;
- the analogous statement holds for `Left(P) ∩ Left(Q)`.

The third statement is again proved by a finite boundary graph.  Local membership changes have
even parity; the two side ports are the only odd vertices; extract a port-to-port path.  Iterating
over the finite set of open self-avoiding crossings produces a least below-set.  Fix a deterministic
ordering only to select the unique normalized boundary path of that least set.  Equality of two
least below-sets then gives equality of the selected canonical boundary path by construction.

### Stopping-set property

For a candidate path `P`, define `LowerEdges(P)` to be the rectangle edges incident to `P` or to a
face in `Below(P)`.  Then

```text
lowest(omega) = P
```

is equivalent to all of the following finite assertions:

1. every edge of `P` is open;
2. there is no open left--right crossing with a strictly smaller below-set;
3. the fixed canonical boundary selection for the least below-set returns `P`.

Every competing path in item 2 uses only `LowerEdges(P)`.  Consequently changing edge states
strictly above `P` preserves the event `lowest = P`.  This yields a `DependsOn` theorem and,
because the relevant support is finite, measurability.  The corresponding upper-extension event
depends on a disjoint finite edge set, so Bernoulli independence applies directly.

This finite statement is the correct primitive to isolate if the whole development cannot be
completed at once.  The present axiom `rswThreeHalvesCrossingProbability_ge` is too large: it
assumes the entire probabilistic inequality.  The external boundary should instead be, at most,
the deterministic canonical-crossing existence/locality theorem.

## 4. A rigorous proof of Bollobás--Riordan Lemma 6

This is the recommended smaller replacement for proving all of Grimmett Lemma 11.73.

Let `S=[0,n] x [0,n]` lie in `R=[0,m] x [0,2n]`, with `m >= n`.  Condition on the event that the
canonical leftmost open vertical crossing of `S` is the fixed path `P_1`.

1. Reflect `P_1` in the line `y=n`.  The reflected path lies in the upper copy of `S`, and the
   concatenation `P=P_1 ∪ reflect(P_1)` is a top--bottom path in the left `n x 2n` strip of `R`.
2. Every right--left crossing of `R` intersects `P`.  Prove this with the finite alternating-path
   parity lemma, not with a drawn curve.
3. Traverse such a horizontal crossing from the right and retain the segment up to its first
   intersection with `P`.  It first meets either the lower half `P_1` or the reflected upper half.
4. Reflection in `y=n` swaps the two first-hit events and preserves the product measure.  Their
   union contains the horizontal crossing event, so each of the two symmetric events has
   probability at least `P(H(R))/2`.
5. Let `Y(P_1)` be the lower first-hit event, expressed as a connection from the right side of `R`
   to `P_1` using only edges in the finite right-side region of `P`.  It depends only on edges
   strictly right of the leftmost crossing.  The event `leftmost=P_1` depends only on `P_1` and
   edges to its left.  The supports are disjoint, hence these events are independent.
6. Therefore

   ```text
   P(Y(P_1) | leftmost=P_1) = P(Y(P_1)) >= P(H(R))/2.
   ```

7. Sum over the disjoint finite family of possible values of `P_1`.  This proves

   ```text
   P(X(R)) >= P(H(R)) * P(V(S)) / 2.
   ```

The only geometric lemmas here are the alternating intersection in item 2 and the stopping-set
property in item 5.  Both are finite.

## 5. Uniform long crossings and RSW gluing

### Bollobás--Riordan Corollary 7

At density `1/2`, square crossings have probability at least `1/2`.  Take two reflected,
overlapping copies of the event `X(R)` and one crossing of their overlap square, as in Figure 4 on
p. 476.  The three events are increasing.  Harris--FKG gives a lower bound by the product of their
probabilities.  On their intersection:

1. each horizontal arm meets the vertical crossing in the overlap square;
2. the overlap's horizontal crossing meets that same vertical crossing;
3. concatenate suitable subpaths at the intersection vertices and erase loops.

The result is a long horizontal crossing of the union rectangle.  Repeatedly applying this
inequality gives, for every fixed integer aspect ratio `rho > 1`, a constant `c(rho)>0`, uniform in
the scale, such that every `2 rho n` by `2n` rectangle has horizontal crossing probability at
least `c(rho)` at density `1/2`.

Each phrase "meets" above should be a finite alternating-side lemma.  For arbitrary side
endpoints, trim each walk to its first and last visit to the overlap square.  The resulting paths
have alternating endpoints.  The mod-two proof in `AlternatingPaths.lean` is reusable after
translations and quarter-turns.

### Grimmett Lemma 11.75, Figures 11.25--11.27

The same trimming procedure rigorizes the three source inclusions:

- two overlapping `3l x 2l` horizontal crossings plus one vertical crossing of their overlap
  give a `4l x 2l` horizontal crossing;
- two overlapping `4l x 2l` crossings plus one vertical crossing give a `6l x 2l` crossing;
- four long crossings placed around a square annulus form a cyclic barrier.

For the first two, choose intersections of the vertical path with the left and right horizontal
paths, take the corresponding subpaths, append, and call `toPath`. The expanded implementation
now carries out these arguments: `rswGluingTwoIntersection_subset` and
`rswGluingThreeIntersection_subset` are theorems in `RSWIncidence.lean`, while
`rswCircuitGluingIntersection_subset` is a theorem in `RSWCircuitIncidence.lean`. Their placement,
FKG, and probability consequences are standard-axiom-only. They are reusable infrastructure, not
remaining obligations for Theorem 11.11.

## 6. Annular circuits and barriers without a Jordan theorem

### Preferred direct-barrier formulation

For Theorem 11.11, do not first prove that four crossings contain a unique simple surrounding
cycle.  Define the barrier event directly as the simultaneous occurrence of four appropriately
placed shifted-dual closed crossings in the top, right, bottom, and left strips of an annulus.

Given an alleged primal open radial path from the inner to the outer square:

1. trim it between its last visit to the inner box and its first visit to the outer boundary;
2. inspect which outer side is hit first;
3. in the corresponding side strip, the radial subpath and the transverse dual crossing have
   alternating endpoints;
4. the finite mod-two intersection lemma supplies a crossed primal/dual edge;
5. that primal edge would be both open and closed, a contradiction.

Thus the four-crossing event is a subset of `squareAnnulusBarrierEvent inner outer`.  This one
event inclusion simultaneously replaces the pictorial "contains a surrounding circuit" and the
later "the circuit blocks a radial path" arguments.  It avoids both
`rswCircuitGluingIntersection_subset` and
`rswAnnulusOpenCircuitProbability_le_half_barrier` in the transitive proof of the threshold.

At density `1/2`, self-duality gives each shifted-dual closed crossing the same probability as
the corresponding primal open crossing.  The four dual-open events are decreasing when viewed as
events of the primal configuration, so the decreasing-event form of Harris--FKG gives a positive
fourth power lower bound for the four-crossing barrier event.  This is all that the
independent-annuli argument needs.

### If an actual surrounding simple cycle is wanted

There is still no need for a Jordan curve theorem.

1. Use alternating-path intersection to connect the four placed crossings cyclically.
2. Concatenate the selected subpaths to a finite closed walk `W` supported in the annulus.
3. Compute the number of crossings of the positive horizontal ray by `W` modulo two.  The four
   strip locations make this parity odd.
4. Decompose the finite closed walk, or its even-degree edge graph, into edge-disjoint simple
   cycles.
5. Parity is additive modulo two.  Since the total is odd, at least one constituent cycle has odd
   ray-crossing parity.  Select that cycle.

Odd ray parity is the formal meaning of "the origin is in the interior" already used by
`rswAnnulusOpenCircuitEvent`.  It remains meaningful even before any topological interior has
been defined.

The inspected branch already contains this technology in another context.  In
`Peierls.lean`, `even_degree_boxOpenReachableFrontierDualGraph` proves local parity,
`boxOpenReachableFrontierDualGraph_isEdgeReachable_two_of_adj` uses Mathlib's finite even-degree
criterion to put frontier edges on cycles,
`boxOpenReachableFrontierPositiveXAxisCrossingEdges_odd` proves odd total ray parity, and
`exists_dualCircuit_surroundsOriginByParity_of_frontier_decomposition` selects an odd component.
Those lemmas should be generalized or reused rather than reproving Jordan separation.

### General finite-cluster boundary circuit

The same method gives the part of Grimmett Proposition 11.2 actually needed by threshold proofs.
For a finite connected primal vertex set `D`, map its edge boundary to a finite dual graph.  Every
dual degree is even by the cyclic membership-change argument, so the graph decomposes into
cycles.  If the origin is in `D`, membership along the positive ray starts true and is eventually
false, hence the boundary crosses that ray an odd number of times.  One cycle therefore has odd
parity and separates the origin.

This proves **existence** of a surrounding boundary circuit.  It does not prove the source's
uniqueness of the outermost circuit, but uniqueness is unnecessary for Theorem 11.11.  The
existing axiom `existsUnique_boundaryCircuitCrossedEdges` should not be imported merely to obtain
the weaker existence fact.

## 7. Independent annuli force `theta(1/2)=0`

Choose annuli with inner radius `4^k` and outer radius `3*4^k`.  Consecutive supports are separated
because `3*4^k < 4^(k+1)`.  The verified theorem
`pairwiseDisjoint_criticalAnnulusEdges` states this for the existing edge supports, and
`iIndepSet_criticalAnnulusBarrierEvent` turns disjoint Bernoulli coordinate supports into mutual
independence.

An infinite origin cluster crosses every annulus.  The proof must not say only "obvious": take a
finite open path from the origin to a vertex outside the outer box, reverse it, find the last
vertex at inner radius, and take the segment to the first outer-surface vertex.  Every edge of
that segment lies in the annular support.  This argument is already proved as
`hasInfiniteOpenCluster_mem_squareAnnulusRadialCrossingEvent`.

If every barrier has probability at least a fixed `delta>0`, then for every `N`,

```text
P(infinite origin cluster) <= P(no barrier among the first N)
                           = product_{k<N} P(barrier_k^c)
                           <= (1-delta)^N.
```

Letting `N` tend to infinity gives zero.  This probability kernel is already theorem
`theta_eq_zero_of_iIndep_barriers`.  `theta_two_eq_zero_of_criticalAnnulusBarrier_probability`
packages it for the existing critical annuli.

Consequently `theta 2 squareHalfDensity = 0`, and
`half_le_cubicCriticalProbability_two_of_theta_half_eq_zero` gives `1/2 <= p_c`.

## 8. Full Grimmett lowest-crossing lemma, if retained

The current exact-threshold closure has only one remaining project axiom,
`rswThreeHalvesCrossingProbability_ge`. Discharging that general numerical statement requires
the stopping-set core of Grimmett Lemma 11.73. Alternatively, Theorem 11.11 can bypass the full
formula by proving only a scale-uniform positive three-halves crossing bound via
Bollobás--Riordan Lemma 6. Here is the finite proof structure behind the stronger Grimmett route,
pp. 317--322 and Figures 11.21--11.24.

Let `r=P(LR(l))` and `u=1-sqrt(1-r)`.  Let `Pi` be the canonical lowest left--right crossing of
the square.  Split crossings according to whether their last visit to the vertical axis is at
nonpositive or nonnegative height.  Reflection and the square-root trick show that each selected
half-event has probability at least `u`.

For a fixed possible value `pi` of `Pi`:

1. retain the subpath of `pi` from its last vertical-axis visit to the right side;
2. reflect that subpath to form the horizontal base used in Figure 11.22;
3. define a finite upper region by face reachability, not by the phrase "in or above";
4. let `M_pi` be the event that an open path in that upper region joins the top side to the base;
5. split `M_pi` according to whether the first contact is on the original or reflected half;
6. use reflection and the square-root trick to give one half probability at least `u`;
7. use the stopping-set property to make that extension independent of `{Pi=pi}`;
8. combine it by FKG with the appropriate right-square half-crossing event, also of probability
   at least `u`.

The union over all `pi` with the selected sign is increasing.  The disjoint decomposition by the
events `{Pi=pi}` lets the conditional estimates be summed.  The three factors `u` are: the sign
of the lowest square crossing, the fresh top-to-base connection, and the appropriate crossing of
the adjacent square.  Their simultaneous occurrence contains a `3l x 2l` crossing, proving

```text
u^3 <= P(3l x 2l crossing).
```

When `pi` meets the vertical axis more than once, Grimmett's sets `H` and `J` on pp. 321--322 are
only a device for restoring disjoint supports.  In Lean, define `H` as the base edges which enter
the upper reachable region and `J` as upper-region edges incident to a below-face.  Prove that
the extension event is unchanged after hiding the states in `J`; `{Pi=pi}` is determined by the
complementary lower support plus openness of `H`.  Apply FKG to the increasing event that
`J ∪ H` is open, then the same square-root estimate.  No claim of simple connectedness is needed.

Once this lemma is proved, the existing `RSWGluing.lean` and `RSWNumeric.lean` algebra yields
`rswAnnulusOpenCircuitProbability_ge`.  If only Theorem 11.11 is in scope, the smaller Lemma 6
route above is preferable.

## 9. The Figure 11.7 four-infinite-arm proof

For completeness, this is the rigorous obligation hidden in Grimmett's printed proof of Lemma
11.12 on pp. 289--291.

The square-root trick produces, with positive probability, infinite primal open arms attached to
the left and right sides of `T(N)` and infinite shifted-dual closed arms attached to the top and
bottom sides.  The picture then makes two claims:

1. the top and bottom dual arms separate the left and right primal arms in the exterior of
   `T(N)`;
2. after uniqueness connects the two primal arms somewhere in the full lattice, their union is a
   barrier which prevents the two dual arms from ever connecting.

A valid Lean replacement must be an exhaustion theorem.  For every sufficiently large outer box,
trim all four rays at their first hit of the outer boundary and trim the finite connecting path to
that box.  State a finite annular mod-two intersection theorem saying that two primal/dual
pairings with alternating inner endpoints cannot both be realized without a crossed edge.  If a
dual connection existed, choose one outer box containing both finite connectors and apply that
finite theorem.  Then pass back to infinite components.

This is not the full discrete Jordan curve theorem, but it is a substantial four-arm separation
lemma in an annulus.  No corresponding proved declaration was found on the inspected Chapter 11
branch.  Because the finite-barrier proof avoids it, this global route is not recommended for the
threshold theorem even though the required uniqueness theorem is available on the Chapter 8
branch.

## 10. Current verified Lean inventory

The following declarations were verified on the expanded Chapter 12 implementation and can be
reused directly.

| Role | Verified declarations |
|---|---|
| Primal/dual bonds and status | `squareEdgeDualCrossingEquiv`, `dualSquareConfiguration`, `dualSquareConfiguration_open_iff`, `dualWalkIsOpen`, `DualCircuit.IsOpen` |
| Literal source rectangle | `grimmettRectangleVertices`, `grimmettRectangleEdges`, `grimmettRectangleLeft`, `grimmettRectangleRight`, `grimmettRectangleCrossingEvent` |
| Exact crossing interface | `grimmettRectangleCrossingProbability_add_complement`, `bernoulliBondMeasure_real_grimmettRectangleCrossingEvent_half` |
| Upper-bound analysis | `grimmettRectangleCrossingProbability_le`, `cubicCriticalProbability_two_le_half_of_crossingProbability` |
| Boundary-free RSW events | `squareBoundaryFreeRectangleCrossingEvent`, `rswSquareCrossingEvent`, `rswThreeHalvesCrossingEvent`, `rswRectangleCrossingEvent` |
| Symmetric placements | `squareCrossingQuarterTurnIso`, `squareCrossingTranslateIso`, `bernoulliBondMeasure_real_rswHorizontalPlacementEvent`, `bernoulliBondMeasure_real_rswVerticalPlacementEvent` |
| FKG gluing algebra | `rswRectangleCrossingProbability_two_ge`, `rswRectangleCrossingProbability_three_ge`, `rswAnnulusOpenCircuitProbability_ge_rectanglePowFour`, `rsw_gluing_inequalities` |
| Face parity and alternating paths | `closedSquareWalkFaceParity`, `closedSquareWalkFaceParity_eq_along_disjoint_walk`, `squareWalk_support_inter_of_bottomLeft_right_and_bottomRight_top` and its rotated variants |
| Finite dual frontier | `even_degree_boxOpenReachableFrontierDualGraph`, `boxOpenReachableFrontierDualGraph_isEdgeReachable_two_of_adj`, `boxOpenReachableFrontierPositiveXAxisCrossingEdges_odd`, `exists_dualCircuit_surroundsOriginByParity_of_frontier_decomposition` |
| Annular supports | `squareAnnulusEdges`, `squareAnnulusRadialCrossingEvent`, `squareAnnulusBarrierEvent`, `pairwiseDisjoint_criticalAnnulusEdges`, `iIndepSet_criticalAnnulusBarrierEvent` |
| Infinite-to-finite annular crossing | `hasInfiniteOpenCluster_mem_squareAnnulusRadialCrossingEvent`, `hasInfiniteOpenCluster_subset_iInter_criticalAnnulusBarrierEvent_compl` |
| Independent barrier limit | `theta_eq_zero_of_iIndep_barriers`, `theta_two_eq_zero_of_criticalAnnulusBarrier_probability` |
| Threshold assembly | `half_le_cubicCriticalProbability_two_of_theta_half_eq_zero`, `cubicCriticalProbability_two_eq_half` |

Kernel auditing now shows that `cubicCriticalProbability_two_eq_half` and
`theta_two_half_eq_zero` depend on exactly the three standard axioms plus the single project axiom
`rswThreeHalvesCrossingProbability_ge`. The finite rectangle interface, all three deterministic
RSW gluing inclusions, annular duality, direct expanded barriers, barrier independence, and the
upper-bound analysis are already standard-axiom-only. Older six-axiom audit artifacts are retained
only as immutable historical records and must not be used as the current completion status.

## 11. Proposed implementation order

The labels in this section are work packages, not claims that declarations with these names
already exist.

1. **Completed finite framed rectangle interface.** Reuse `BondCrossingInterface` and
   `BondCrossingDuality`; the upper bound no longer has a project axiom.
2. **Completed RSW incidence and direct annular barriers.** Reuse `RSWIncidence`,
   `RSWCircuitIncidence`, `AnnulusDuality`, and the expanded-barrier independence stack.
3. **Proposed canonical-side API.** Define face reachability below/above and left/right of a
   self-avoiding crossing.  Prove meet, canonical minimal crossing, finite support, measurability,
   and the stopping-set `DependsOn` result.
4. **Proposed Lemma 6 event.**  Formalize reflection, first-hit trimming, the right-side extension
   event, its disjoint support, and the conditional probability estimate.
5. **Proposed long-crossing recurrence.**  Prove Bollobás--Riordan Corollary 7 with existing FKG
   and graph automorphism APIs.  Only a positive constant is needed.
6. Feed the resulting positive three-halves bound through the existing three gluing theorems to
   obtain a uniform positive expanded-barrier probability.
7. Reuse `theta_eq_zero_of_iIndep_barriers`; combine with the proved upper bound and run
   `#print axioms Percolation.cubicCriticalProbability_two_eq_half`.
8. Only after the threshold is assumption-free, optionally return to the stronger full numerical
   RSW theorem and surrounding-cycle APIs.

## 12. Rules for future pictorial arguments

When a source says "clear from the figure", use this escalation order:

1. **Trim to finite walks.**  Replace rays by first-hit or last-exit subpaths in a finite box.
2. **Normalize.**  Convert walks to paths and make endpoints/side membership explicit.
3. **Try reachability.**  Define the region by a finite flood fill from a boundary port.
4. **Try local parity.**  Boundary degrees are usually even because a cyclic bit string changes
   value an even number of times.
5. **Try mod-two intersection.**  Define a ray-crossing index and prove it is constant along a
   disjoint path.
6. **Extract graph-theoretically.**  Use finite even-degree graphs, non-bridge/cycle lemmas, path
   trimming, and cycle decomposition.
7. **Weaken to the needed consequence.**  A barrier event may be enough even when the source
   states existence or uniqueness of an outermost circuit.
8. **Isolate the smallest remaining primitive.**  If a genuine theorem is still missing, expose
   a deterministic finite incidence or stopping-set lemma, never the final probability inequality
   or the threshold theorem itself.

In particular, do not import a general Jordan curve theorem until finite reachability, even-degree
frontiers, alternating-path parity, and direct barrier formulations have all been ruled out.  For
Theorem 11.11 they are sufficient.
