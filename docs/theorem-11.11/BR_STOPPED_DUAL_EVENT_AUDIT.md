# Audit of the stopped-dual event used for Bollobás--Riordan Lemma 6

## Scope and verdict

This note audits the stopped-dual construction against Bollobás and Riordan,
*A short proof of the Harris--Kesten theorem*, Lemma 6 and Corollary 7
(printed pp. 475--476), and against the rectangle events currently used in this
repository.

The principal conclusion is:

> The frame and the left-source orientation are suitable for selecting a
> bottom--top primal crossing.  They are not, by themselves, tied to the
> repository's boundary-free RSW event.  To obtain that event, a crossed bond
> excluded from `squareBoundaryFreeRectangleEdges (2 * n) n` must be treated as
> deterministically primal-closed/dual-open, and the random fiber support must
> be filtered to the allowed edge set.

Equivalently, if `q(e)` is the primal bond crossed by a frame dual edge, the
exploration status has to be

```text
e is exploration-open  <->
  q(e) is not allowed by the boundary-free square OR q(e) is not in omega.
```

This is the complement of the effective primal configuration

```text
omega_eff = omega intersect squareBoundaryFreeRectangleEdges (2*n) n.
```

The corrected formula is now present in the integration version of
`BRDualExploration.lean`.  The earlier formula `q(e) ∉ omega` instead detects a
full-edge vertical crossing.  It cannot be used to claim a partition of
`rswSquareCrossingEvent n`.

There is a second, independent warning.  `brStoppedDualBoundaryEdge` regards
every face outside the finite frame as unreached.  Its ambient boundary
therefore contains artificial left, top, and bottom arcs whose crossed primal
bonds were never queried by the exploration.  Only cut edges with both dual
endpoints in the finite frame are forced to cross allowed open primal bonds.
The artificial arcs may select the outer component, but must be removed before
the component is called an open primal path.

No global boundary-path theorem is currently supplied by
`BRResolvedBoundary.lean`; its local resolved pairing is necessary but not
sufficient.  The global endpoint/component lemma described below remains a
real proof obligation.

## 1. Coordinate and event dictionary

Fix `n : Nat` and put

```text
Q_n = [0,2n] x [-n,n].
```

The relevant repository definitions are:

- `squareRectangleEdges (2 * n) n`: all square-lattice bonds contained in
  `Q_n`;
- `E_bf(n) = squareBoundaryFreeRectangleEdges (2 * n) n`: those bonds after
  deleting every bond whose two endpoints are boundary vertices of `Q_n`;
- `rswSquareCrossingEvent n`: the left--right crossing of `Q_n` using only
  `E_bf(n)`;
- `rswVerticalPlacementEvent` with the quarter-turn isomorphism: the correct
  way to turn that event into a bottom--top crossing of the same square.

For clarity, write:

```text
V_full(n) = bottom--top crossing of Q_n using squareRectangleEdges (2*n) n,
V_bf(n)   = quarter-turned rswSquareCrossingEvent n.
```

The stopped-dual frame is

```text
F_n = { (x,j) : -1 <= x <= 2n and -n <= j <= n-1 }.
```

A vertex `(x,j)` denotes the unit primal face with lower-left corner `(x,j)`.
The source set is the whole exterior column `x = -1`.  The column `x = 2n` is
the right exterior column.  Thus a dual left--right crossing is exactly a
frame path from a source face to some face with first coordinate `2n`.

The edge-coordinate dictionary is important:

- the horizontal dual edge from `(x,j)` to `(x+1,j)` crosses the vertical
  primal bond at abscissa `x+1`, from height `j` to height `j+1`;
- the vertical dual edge from `(x,j)` to `(x,j+1)` crosses the horizontal
  primal bond from `(x,j+1)` to `(x+1,j+1)`.

Consequences of this dictionary include:

- dual edges from column `-1` to column `0` cross the left-side vertical
  perimeter bonds of `Q_n`;
- dual edges from column `2n-1` to column `2n` cross the right-side vertical
  perimeter bonds;
- vertical dual edges inside either exterior column cross primal bonds partly
  outside `Q_n`;
- top and bottom horizontal perimeter bonds are not crossed by edges of the
  induced frame.  They occur only when the ambient boundary construction joins
  a frame face to a fictitious face above or below the frame.

The source choice is therefore oriented for a *vertical primal* crossing:
dual-open edges crossing effectively closed primal bonds are flooded from the
left, and the right-hand boundary of the flooded set is a bottom--top primal
interface.
It does not directly select the horizontal event
`squareBoundaryFreeRectangleCrossingEvent`; that event must first be
quarter-turned.

## 2. What the source actually conditions on

In Bollobás--Riordan Lemma 6 the source coordinates are

```text
S = [0,N] x [0,N],
R = [0,M] x [0,2N],
M >= N.
```

The event `V(S)` is partitioned according to its leftmost open vertical path
`P_1`.  The path is reflected across the *top side* `y = N`, producing a
geometric barrier from `y = 0` to `y = 2N`.  A horizontal crossing of `R` is
traversed from the right until its first encounter with that barrier.

The source uses ordinary rectangle crossings; it does not delete perimeter
bonds.  Hence the original, unfiltered exploration `q(e) ∉ omega` was faithful
to the source's full-edge event.  The boundary-free construction is a
repository adaptation and must be recorded as such in the Comparator trail.

The repository square `Q_n` has side length `2n`, so it corresponds to the
source square with `N = 2n`.  After translating the source square down by
`n`, the source reflection line `y = N` becomes `y = n`, the top edge of
`Q_n`, and the doubled rectangle becomes

```text
[0,M] x [-n,3n].
```

Thus the current parametrization directly implements the source lemma only at
even source side lengths.  This is enough for the repository's squares, whose
side is always `2n`, and in particular for the scales `4^(k+2)` used later.
It is not a formalization of the source's arbitrary integer `N` without a
parity or padding lemma.

## 3. The exact boundary-free correction

Let `q(e)` be the crossed primal edge of an actual induced-frame edge.  Define

```text
C_bf(n,omega)(e) <-> q(e) notin E_bf(n) OR q(e) notin omega.
```

This formula has four useful consequences.

1. If `q(e)` is allowed, exploration openness is ordinary dual openness:
   `e` is open exactly when `q(e)` is closed in `omega`.
2. If `q(e)` is excluded, `e` is open for every `omega`.  It is a deterministic
   edge, not a random coordinate.
3. An induced cut edge, one of whose endpoints is reached and the other
   unreached, cannot be exploration-open.  Therefore its crossed bond belongs
   to `E_bf(n)` and belongs to `omega`.
4. The exploration depends on exactly the effective configuration
   `omega ∩ E_bf(n)`, as the boundary-free crossing event does.

In particular, the left and right vertical perimeter bonds are excluded from
`E_bf(n)`, so their crossing dual edges are deterministic open.  Every face in
column `0` is consequently reached from its adjacent source face.  Conversely,
if a face in column `2n-1` were reached, its deterministic edge to the right
exterior face would reach column `2n`.  On a good fiber no face in column
`2n-1` is therefore reached.

The top and bottom perimeter bonds play a different role.  They do not occur
as induced-frame edges.  In the ambient resolved boundary they are crossed by
the transitions from the bottom frame row to an outside row, and from the top
frame row to an outside row.  Those transitions are *ports used to locate an
endpoint*, not explored dual edges.  Their primal bonds are excluded and are
not claimed to be open.  The actual first and last edges of the selected
primal crossing are inward vertical bonds with only one endpoint on the
top/bottom boundary; the deterministic side edges force their abscissae away
from the two corners, so these inward bonds belong to `E_bf(n)`.

For a proposed reached set `A`, a safe random-coordinate support is

```text
Supp_bf(n,A) =
  { q(e) : e is an induced-frame edge incident to A and q(e) in E_bf(n) }.
```

Filtering is required.  An excluded bond has constant effect on the
exploration and must not be treated as an exposed random coordinate.  The
filtered set may still overapproximate the truly queried coordinates (for
example, every face in the source column is seeded), but that is harmless for
`DependsOn` and preserves the needed disjointness with a fresh support.

### A concrete counterexample to the uncorrected formula

Take `n = 1`, so `Q_1 = [0,2] x [-1,1]`.  Let `omega` contain exactly the two
vertical bonds on the left side:

```text
(0,-1)--(0,0),  (0,0)--(0,1).
```

These bonds form a full-edge bottom--top crossing.  They block every
ordinary closed-dual path from the left exterior column to the right exterior
column.  But both bonds have both endpoints on the rectangle boundary, so
they are absent from `E_bf(1)`.  There is no boundary-free vertical crossing.

Thus, with status `q(e) ∉ omega`, "the right column is not reached" is true
while `V_bf(1)` is false.  This disproves the event equality that the original
plan asked the uncorrected fibers to establish.

## 4. Lemma-by-lemma stopped-exploration audit

The following order avoids a hidden Jordan-curve assumption.

### Lemma A: elementary reachability facts

For every configuration, let `Reach(n,omega)` be the set returned by
`brLeftReachableFaces` using `C_bf`.

Prove directly from finite reachability that:

1. every left source is in `Reach(n,omega)`;
2. if `u` is reached and an exploration-open induced edge joins `u` to `v`,
   then `v` is reached;
3. consequently, every induced edge with exactly one reached endpoint is
   exploration-closed;
4. by the complement formula, every such cut edge crosses an edge in
   `E_bf(n) ∩ omega`.

Item 4 is the only openness fact later path extraction may use.  It does not
apply to an ambient edge whose second endpoint lies outside `F_n`.

### Lemma B: the good reached sets

Define

```text
Good_n(A) <-> no z in A has z.x = 2n.
```

For a nonempty fiber `Reach(n,omega) = A`, all sources belong to `A`.
If `Good_n(A)` holds, all right exterior faces are outside `A`.  In the
boundary-free exploration the deterministic side edges strengthen this to:

```text
column 0 is contained in A,
column 2n-1 is disjoint from A.
```

No reference to a boundary path belongs in the definition of `Good_n`; the
path is derived from this coordinate condition.

### Lemma C: distinguished bottom and top cut edges

Assume `n >= 1`, `A` is a realizable good reached set, and put

```text
b = max { x : (x,-n)   belongs to A },
t = max { x : (x,n-1)  belongs to A }.
```

These maxima exist because the left sources are reached.  In the corrected
boundary-free exploration they satisfy

```text
0 <= b,t <= 2n-2.
```

The distinguished raw dual cut edges are

```text
e_bottom = {(b,-n),   (b+1,-n)},
e_top    = {(t,n-1),  (t+1,n-1)}.
```

They are horizontal dual edges directed from reached to unreached when read
west to east.  They cross the inward vertical primal bonds

```text
(b+1,-n)--(b+1,-n+1),
(t+1,n-1)--(t+1,n).
```

Both primal bonds are allowed and open.  The maxima, rather than the first
row changes from `x = -1`, are essential: membership of `A` along a row need
not be an interval.  A first change can bound a bay and need not lie on the
outer/right separator.

### Lemma D: the artificial outer arc

`brReachedDualFace` returns false outside the frame.  Hence
`brStoppedDualBoundaryEdge n A` contains, among other edges:

- the fixed left arc joining `(−2,j)` to `(−1,j)` for all source rows `j`;
- bottom transitions from `(x,−n−1)` to a reached `(x,−n)`;
- top transitions from a reached `(x,n−1)` to `(x,n)`.

The left arc crosses vertical primal bonds at `x = -1`, outside `Q_n`.  The
bottom and top transitions at `0 <= x < 2n` cross horizontal perimeter bonds;
the analogous transition at the source column crosses a bond outside `Q_n`.
None is an induced-frame edge, so the reachability-closure argument says
nothing about its state in `omega`.

The correct use of these edges is purely combinatorial.  They identify the
outer resolved boundary component.  They must then be trimmed away.  A lemma
stating that every `brStoppedDualBoundaryEdge` crosses an open primal bond is
false.

### Lemma E: select the outer/right resolved component

Use the local split tag from `ResolvedRectangleInterface.lean` to orient each
boundary state with the reached face on its left.  Local pairing gives a
unique successor and predecessor.  Since the boundary enclosure is finite,
the oriented states form disjoint directed cycles.

The desired cycle is the one containing the fixed exterior-left arc.  Its
description can be proved without a general discrete Jordan theorem:

1. following the cycle with `A` on the left traverses the left artificial arc
   from top to bottom;
2. it then traverses bottom artificial pieces from left to right, possibly
   making finite excursions around bays;
3. the last departure from the bottom is paired with `e_bottom`, the
   rightmost bottom-row change;
4. before the cycle can return to the top of the fixed left arc it must enter
   the top artificial boundary; its first such entry is paired with `e_top`,
   the rightmost top-row change;
5. the directed segment from `e_bottom` through `e_top` contains only cut
   edges whose two endpoints lie in `F_n`.

Step 4 is the global checkpoint.  Local degree two alone does not prove it.
A finite proof should use the deterministic successor and the order in which
an oriented contour meets the boundary of the enclosing coordinate box.  In
particular, it must show that a trace closing before the top contact would
separate the fixed left arc from its own continuation, contradicting the
unique local successor.  Equivalently, one may classify the component of the
ambient complement connected to the right exterior column and prove that
`e_bottom` and `e_top` are on its common resolved boundary with `A`.

Every other cycle is a hole boundary and must be ignored.  The implementation
should expose a theorem that the two distinguished raw edges lie on the same
resolved component; it should not choose an arbitrary boundary component.

### Lemma F: convert the component to an open primal path

Map each internal cut dual edge on the selected segment through
`squareEdgeDualCrossingEquiv.symm`.  The local resolved pairing says that
successive crossed primal bonds share the appropriate primal endpoint, even
at a checkerboard degree-four cell.  The first and last crossed bonds are the
inward bottom and top ports from Lemma C.

By Lemma A, every mapped bond is in `E_bf(n) ∩ omega`.  The resulting walk
therefore joins the bottom side of `Q_n` to the top side using only allowed
open bonds.  Erasing loops, if the target API requires a path rather than a
walk, preserves the endpoints and edge containment.

This gives a witness to `V_bf(n)`.  To compare with
`rswSquareCrossingEvent n`, either map this witness back through
`squareCrossingQuarterTurnIso`, or provide a vertical analogue of the finite
candidate bridge in `CanonicalCrossing.lean`.  The existing candidates are
horizontal; they are not definitionally this path.

### Lemma G: the exact primal/dual alternative

For `n >= 1`, prove that exactly one of the following holds:

1. `V_bf(n)`;
2. an exploration-open path in `F_n` joins the left source column to the
   right exterior column.

The implication from (2) to the failure of (1) is the finite crossing
intersection argument: a dual left--right path and a primal bottom--top path
must contain a crossed primal/dual edge pair.  On that pair the dual path says
the effective primal bond is closed, while the primal path says it is allowed
and open.

For the converse, if the right column is not reached, Lemmas C--F construct
the boundary-free vertical crossing.  Hence

```text
V_bf(n)(omega) <-> Good_n(Reach(n,omega)).
```

With the uncorrected status `q(e) ∉ omega`, exactly the same proof has
`V_full(n)` in place of `V_bf(n)`.  This is the precise event detected by the
original implementation.

### Lemma H: the fiber partition

For each finite `A`, let

```text
Fiber_n(A) = { omega : Reach(n,omega) = A }.
```

All fibers are pairwise disjoint, and their union over all `A` is the whole
configuration space.  Lemma G then gives the exact restricted partition

```text
V_bf(n) = disjoint union of Fiber_n(A) over Good_n(A).
```

Empty/nonrealizable fibers may remain in the finite index set; they contribute
zero.  This avoids having to characterize every abstract set that can arise as
a reachability set.

The existing theorem `dependsOn_brReachableFaceFiber` should use the filtered
support `Supp_bf(n,A)`.  Its proof splits an incident frame edge into two
cases: allowed crossed bonds are controlled by coordinate agreement; excluded
crossed bonds have constant exploration status.

## 5. Reflection and the fresh extension event

### The reflection line and its off-by-one dual formula

The current square is centered on `y = 0`.  Reflecting it across its horizontal
midline maps it to itself and does **not** produce the doubled barrier in
Bollobás--Riordan Lemma 6.  The required reflection is across the top side
`y = n`:

```text
primal vertex:       (x,y) -> (x, 2n-y),
dual face lower-left (x,j) -> (x, 2n-1-j).
```

The `-1` in the face formula is mandatory because a face occupies the strip
from `j` to `j+1`.  Likewise, reflection across `y = 0` would send a face row
`j` to `-j-1`, not to `-j`.

The reflected selected path or reached region is a deterministic geometric
copy.  It is not a second exploration in the actual configuration, and its
crossed primal bonds are not known to be open.  Only the original interface
extracted from the fiber is exposed-open.

### Direction of first contact

Take a horizontal crossing of the doubled rectangle and orient it from the
right boundary toward the left.  Stop at its first contact with the union of
the original barrier and its upper reflection.  The prefix before that contact
lies on the right of the barrier.  Reversing the prefix gives the arm from the
original interface to the right boundary required by the event `X(R)`.

Traversing from the left would expose the wrong part of the path and would not
produce a support disjoint from the left exploration.

For a fixed reached set `A`, let `B_A` be the original stopped region together
with its reflected geometric copy.  A safe fresh edge set contains only
primal bonds whose crossed dual edge has both incident faces outside `B_A`,
and which lie in the right component of the doubled rectangle.  It must also
be intersected with the allowed edge set of the *large* boundary-free
rectangle.

At a corner of the interface, the edge on which a horizontal crossing first
enters the barrier need not have both dual faces outside `B_A`.  Use the
following exhaustive trimming rule:

1. traverse the crossing from the right;
2. keep edges until just before the first edge that is not in the fresh set;
3. the retained prefix is a connection to the outside endpoint/contact set of
   a barrier edge;
4. in the lower case, append the corresponding original interface edge only
   when forming the final witness.  Its openness comes from the fiber, not
   from the fresh event;
5. in the upper reflected case, do not assert that the corresponding reflected
   edge is open.  The upper event is used only in the symmetry estimate.

Define `Y_A^lower` and `Y_A^upper` by these fresh-prefix connections.  Vertical
reflection exchanges them and preserves Bernoulli measure.  Every horizontal
crossing yields at least one of the two first-contact events.  The events need
not be disjoint; subadditivity is enough:

```text
P(H) <= P(Y_A^lower union Y_A^upper)
     <= P(Y_A^lower) + P(Y_A^upper)
      = 2 P(Y_A^lower).
```

Therefore `P(Y_A^lower) >= P(H)/2`.

The support of `Y_A^lower` is disjoint from `Supp_bf(n,A)`: every fiber
coordinate crosses a frame dual edge incident to `A`, whereas every fresh
coordinate has both relevant faces outside `B_A` and hence outside `A`.
The already-exposed interface edge used for splicing is intentionally absent
from the fresh event.  Product-measure independence then gives

```text
P(Fiber_n(A) intersect Y_A^lower)
  = P(Fiber_n(A)) * P(Y_A^lower).
```

On that intersection, the lower fresh prefix plus the exposed-open original
interface yields `X`.  Summing over good fibers proves the adapted Lemma 6
inequality without conditional probabilities or division by a possibly-zero
fiber mass:

```text
P(X) >= P(H) * P(V_bf) / 2.
```

## 6. Corollary 7: two different reflections

The reflection used inside Lemma 6 is vertical reflection across the top of
the selected square.  Corollary 7 uses a different symmetry.

In source coordinates, put

```text
R  = [0,M]   x [0,2N],
R' = [N-M,N] x [0,2N],
S  = [0,N]   x [0,N].
```

The map `x -> N-x` reflects `R` horizontally to `R'`.  It maps the event
`X(R)` to a left-extending copy `X(R')`.  Together with a horizontal crossing
of the overlap square `S`, the two events splice to a horizontal crossing of

```text
R union R' = [N-M,M] x [0,2N],
```

whose width is `2M-N`.  After translation this is the rectangle
`[0,2M-N] x [0,2N]`.

The three events are increasing, so Harris--FKG applies.  If `h` is the
crossing probability of `R` and `s` is the square crossing lower bound, Lemma
6 gives each arm probability at least `h*s/2`, and the overlap crossing has
probability at least `s`.  Consequently the adapted recurrence is

```text
h(2M-N,2N) >= h(M,2N)^2 * s^3 / 4.
```

The source denominator `2^5` uses `s = 1/2`.  It must not be copied unchanged
when the repository's boundary-free square estimate is used.  The existing
bound `s >= 1/8` for scales at least two gives denominator `2^11`; the weaker
`s >= 1/16` gives denominator `2^14`.  Either positive constant is sufficient
downstream, but the chosen constant must be derived explicitly.

The dimension assumption is `M >= N`.  Since the current stopped square has
`N = 2n`, this reads `M >= 2n`, not merely `M >= n`.  It also guarantees that
`2M-N` does not underflow when encoded with natural numbers.

For the boundary-free adaptation, the path-splicing inclusion must be checked
against the allowed edge set of the union rectangle.  It is not automatic from
the source's full-edge picture: each input arm and the overlap crossing must be
transported into the union, and every retained edge must remain allowed there.

## 7. Small scales and edge cases

### `n = 0`

The frame has no face rows, the source and reached sets are empty, and there is
no resolved interface.  Repository connection events may nevertheless be
universal because a zero-length walk connects a vertex to itself.  Lemma 6's
path extraction and its two-way first-contact split are therefore not valid at
`n = 0`.  State the stopped-interface lemmas for `1 <= n` and discharge any
zero-scale probability statement separately.

### `n = 1`

This is the smallest genuine `2 x 2` square.  The corrected deterministic side
edges force the selected bottom and top ports to have abscissa `1`; the two
inward vertical bonds through the middle column are allowed.  This scale is an
important executable/test-case model for the event equality.  It is also the
counterexample scale for the uncorrected full-edge exploration described
above.

### Parity and recurrence scales

The current centered square has even side `2n`.  This matches every
`rswSquareCrossingEvent n`, but corresponds only to even `N` in the source
notation.  A theorem advertised as all of Bollobás--Riordan Corollary 7 needs
an odd-size/padding argument.  A target-specific theorem at the expanded
annulus scales does not: `expandedCriticalAnnulusScale k = 4^(k+2)` is even.
This specialization must be stated in the Comparator notes.

## 8. Dependency order for implementation and review

The safe dependency order is:

```text
effective boundary-free dual status and filtered support
  -> finite reachability closure/cut-edge openness
  -> right-column good predicate and row-max terminal edges
  -> global outer resolved component theorem
  -> boundary-free vertical path extraction
  -> exact primal/dual alternative
  -> good-fiber partition
  -> reflected geometric barrier and fresh-prefix first-contact lemma
  -> support disjointness and per-fiber factorization
  -> sum over fibers (adapted Lemma 6)
  -> horizontal reflection, three-event FKG, and splicing (Corollary 7)
```

Do not prove the event partition before the global component theorem: doing so
would merely hide the pictorial step inside an asserted event equality.

## 9. Explicit audit findings against the current plan and modules

1. **Corrected in `BRDualExploration.lean`:** exploration openness now has the
   required formula `q ∉ E_bf OR q ∉ omega`, and the fiber support is filtered
   to `E_bf`.  Reverting either change restores the full-edge mismatch.
   The finite frame and the choice of the whole left exterior column as
   sources are otherwise sound.  Seeding the whole column makes its internal
   edge states redundant and creates the fixed artificial left arc used to
   identify the outer contour; it does not make that arc open in the primal
   configuration.
2. **Still open:** `BRResolvedBoundary.lean` proves local pairing only.  It does
   not yet prove that the row-max bottom and top edges lie on one distinguished
   outer component, nor does it extract the open vertical path.
3. **False if read literally:** the plan's statement that every edge on the
   ambient boundary of `A` crosses an open primal edge.  This holds only for
   induced-frame cut edges.  Outside-frame arcs are not explored.
4. **Wrong reflection if applied to current coordinates:** reflecting the
   current square/reached set across the horizontal midline `y = 0`.  The
   source reflection is across the top edge `y = n`; dual face rows require
   `j -> 2n-1-j`.
5. **Wrong component selector:** taking the first/minimum bottom or top row
   change from the left.  Use the maximum/rightmost change, or equivalently
   trim the oriented outer component after its last bottom contact and before
   its first top contact.
6. **Wrong openness claim:** treating the reflected barrier as open.  It is
   geometric only; only the original fiber boundary is exposed-open.
7. **Wrong extension direction:** trimming a horizontal crossing from the
   left.  It must be traversed from the right so the retained prefix is fresh.
8. **Potentially wrong Corollary 7 constant:** the paper's `2^5` denominator
   presupposes the source square bound `1/2`.  With the repository's
   boundary-free bound, derive the larger denominator rather than copying
   `2^5`.
9. **Coordinate mismatch to record:** the current construction has source
   square size `N = 2n`, doubled rectangle height `4n`, and assumption
   `M >= 2n`.
10. **Small-size guard required:** the interface theorem needs `1 <= n`; the
    zero case is degenerate.

With these corrections, the stopped-dual route is a plausible elementary
replacement for an appeal to a general discrete Jordan curve theorem.  The
load-bearing missing result is now sharply localized: a finite resolved
contour theorem for the distinguished outer component, followed by the exact
boundary-free primal/dual alternative.
