# Pictorial proof expansion for Duminil-Copin Proposition 2.14

## Source evidence

- Source id: `duminil-copin-graphical-representations-2016`.
- Source: Hugo Duminil-Copin, *Graphical Representations of Lattice Spin Models*,
  Chapter 2, Section 4, Proposition 2.14.
- Location: printed pp. 19--20, PDF pp. 27--28.
- Figure: Figure 2.3, both panels. The caption defines the left panel as the region
  `S(gamma)` bounded by the square, a crossing `gamma`, and its reflection; the right panel
  depicts the lower bridge `B_n`, its reflected upper bridge, and the central vertical
  square crossing.
- Source file SHA256 recorded by the existing independent review:
  `c29e39e3600e76530efcb150ba211d3b1ca5373f6b190b99495da84cc6630e1d`.

The rendered pages were checked, not merely OCR output. The proof invokes the figure in two
places. First, after conditioning on the highest horizontal crossing `Gamma` of `[0,n]^2`, it
uses the region below `Gamma` and its reflection to retain fresh Bernoulli coordinates and to
obtain a conditional lower-connection probability of `1/4`. Second, it uses the right panel to
assert that a central vertical crossing, a lower bridge, and its reflected upper bridge glue to
a vertical crossing of `[-n,n] x [-n,2n]`.

The theorem hypothesis is `n >= 1`. All rectangle boundaries are inclusive lattice-vertex
boundaries, and all crossing paths use nearest-neighbor primal bonds internal to the indicated
rectangle. At density `1/2`, open and closed bonds are interchanged by planar duality. Apparent
line thickness, path uniqueness, and exact path shapes in Figure 2.3 are artistic and supply no
formal hypotheses.

## Figure classification and transcription

Figure 2.3 is proof-bearing and has five separate roles:

- `DEFINITIONAL`: it fixes the lower and upper bridge placements relative to the central
  square and the large `2n`-by-`3n` rectangle.
- `SELECTION_OR_STOPPING`: the proof selects the highest open left-right crossing.
- `DEPENDENCY_SCHEMATIC`: the region below the selected crossing is claimed to remain fresh
  after its stopping fiber is fixed.
- `SYMMETRY_OR_TRANSPORT`: reflection across `{0} x Z` is used in `S(gamma)`, and vertical
  reflection/translation transports the lower bridge to the upper bridge.
- `INCIDENCE_OR_SEPARATION`: the two bridge crossings must each meet the central vertical
  crossing, after which the witnesses are concatenated.

The ambient vertex type is `SquareVertex = Z^2`, with coordinates read as `(x,y)`. The target
vertex region is

```text
R_n = { (x,y) | -n <= x <= n and -n <= y <= 2n }.
```

Its bottom and top sides are respectively `y = -n` and `y = 2n`. The central source square is
`Q_n = [0,n] x [0,n]`. The lower auxiliary square is `[-n,n]^2`; the upper auxiliary rectangle
is `[-n,n] x [0,2n]`. The source's reflection `sigma` maps `(x,y)` to `(-x,y)` and fixes the
vertical axis. The lower-to-upper transport maps `(x,y)` to `(x,n-y)` and sends `y=-n` to
`y=2n`. This is the correct integer-coordinate statement: for odd `n`, no lattice vertices lie
on the geometric line `y=n/2`. The map preserves `Q_n` as a set after reversing its vertical
orientation.

Paths may run along boundaries, bridge endpoints need not be unique, and the selected highest
crossing is required only as a finite stopping certificate. No claim of a unique geometric
region is inferred from the drawing without an explicit finite construction.

## Visual-obligation ledger

| Id | Explicit hypotheses | Exact conclusion | Downstream use | Status |
|---|---|---|---|---|
| `V1` | `n >= 2`; half-density bond percolation; full internal bonds of `Q_n` | The vertical crossing probability of `Q_n` is at least `1/2` | source factor `P(C_v(Q_n))` | proved with standard axioms by even/odd placement and first-hit truncation; the horizontal analogue and the translated lower-square input are also proved |
| `V2` | a good reached-face fiber | Its deterministic boundary contains a normalized highest left-right crossing: last left-side visit, first subsequent right-side visit, and strictly interior intermediate vertices | define an unambiguous barrier | blocked: deterministic outer-boundary extraction required |
| `V3` | all good reached-face indices `R` | `A_n` is the pairwise-disjoint finite union of fibers `F_R`; a deterministic normalized `gamma_R` is open on `F_R`; `F_R` depends on a sufficient exposed edge finset `E_R` | prove measurability and freshness below | partition/locality scaffolding exists; one-sided support and boundary extraction blocked |
| `V4a` | a fixed `gamma`; a full bottom-to-top crossing of `[-n,n]^2` | The crossing meets the reflected barrier `sigma(gamma)⁻¹ ++ gamma` | define the first contact | proved with standard axioms, both deterministically and as an event-witness extraction theorem |
| `V4b` | the crossing and its first barrier contact from `V4a` | The prefix edge finset, including the final contact edge, lies in an edgewise fresh support which excludes barrier edges and exposed above-side edges | justify one-sided freshness | blocked; must cover boundary runs, axis contacts, turns, and degree-four cells |
| `V4c` | the full-square crossing input and `V4a`--`V4b` | The full-square crossing event is included in the union of the two fresh contact events | transport the `1/2` bound to `S(gamma)` | proposed |
| `V4d` | the edgewise fresh support/contact events and reflection across the vertical axis | Reflection maps the supports and events exactly; the symmetric events have equal probabilities, so one has probability at least `1/4` | uniform per-fiber lower-bridge estimate | proposed after V2--V4b |
| `V5` | all selector fibers, their finite supports, and the per-fiber `1/4` estimate | `P(B_n) >= (1/4) P(A_n) >= 1/8` by a disjoint finite sum, without division by null fibers | lower bridge probability | proposed; ratio-free summation verified existing |
| `V6` | lower bridge event `B_n` | Vertical reflection/translation maps it into the upper bridge event and preserves the half-density law | upper bridge probability `>= 1/8` | proved as the sufficient event inclusion and probability comparison |
| `V7` | central vertical crossing, lower bridge, and upper bridge | Their three open connected witnesses concatenate to a bottom-to-top connection using only bonds of `R_n` | deterministic event inclusion | proved with standard axioms by two rectangle-incidence applications and explicit walk concatenation |
| `V8` | the three events in `V7` | Each event is measurable and increasing | apply two successive FKG inequalities | proved with standard axioms |
| `V9` | bounds `1/2`, `1/8`, `1/8` and `V7`--`V8` | `P(C_v(R_n)) >= 1/128` | source proposition | numerical assembly proved; only the uniform `1/8` lower-bridge input remains |

## Falsification record

- Scale `n=0` is excluded by the source and Lean hypothesis. At `n=0`, side sets coincide and
  the intended stopping and separation interpretation degenerates, so no extension of the
  public theorem to zero is proposed.
- Scale `n=1` was checked explicitly at the coordinate level: all four sides are nonempty, the
  two reflections preserve lattice vertices, and the target has three vertical bond layers.
  Boundary-running paths must therefore be admitted by every incidence statement.
- A lexicographically first open crossing was rejected. Its selector fiber may query bonds
  geometrically below the selected path, so it does not give the source's freshness claim.
- An arbitrary open crossing was rejected. Conditioning only on its open bonds does not specify
  a disjoint partition, while selecting it by an arbitrary order again destroys one-sided
  locality.
- The stronger claim that a lower-square vertical crossing must meet `gamma` itself was
  rejected: at `n=1`, the full vertical path on `x=-1` is disjoint from a horizontal path in
  `Q_1`. The correct barrier is `gamma ∪ sigma(gamma)`.
- The stronger claim that bridge components meet in an edge was rejected. Planar incidence
  supplies a common vertex; vertex intersection is sufficient for concatenating graph walks.
- A shortcut through the existing boundary-free RSW square event was tested on the smallest
  instances. At half density its exact probabilities for scales `1` and `2` are respectively
  `1/4` and `48449/131072` (finite enumeration of 4 and 24 bonds). Thus the tempting uniform
  input `r >= 3/8` is already false at scale `2`, and the existing numerical lowest-crossing
  axiom plus current `1/8` square bound cannot yield `1/128`.
- No disjointness of random-coordinate supports is inferred merely because two drawn regions
  look separated. The stopping fiber and its fresh event require explicit finsets and a proved
  `Disjoint` statement.

The finite enumeration above is falsification evidence only; it is not part of the proof.

## Checked direct small-scale witnesses

The source-facing implementation now discharges the first five legal scales without using the
missing highest-crossing selector:

- `n = 1` and `n = 2` use a fixed straight vertical path;
- `n = 3` uses a rotated four-fresh-edge Grimmett witness and the bound `1/32`;
- `n = 4` uses a rotated three-fresh-edge Grimmett witness and the bound `1/16`;
- `n = 5` uses a rotated four-fresh-edge Grimmett witness and the bound `1/32`.

Each placement has explicit coordinate, endpoint, support, event-inclusion, and Bernoulli
measure-transport proofs. These are genuine proofs of the indicated scales, not finite
enumeration. They do not replace the uniform stopping argument: the number of fresh horizontal
extension bonds needed by this construction grows with `n`, so its lower bound eventually falls
below `1/128`.

## Finite rigorous proof

### `V1`: square-crossing input

Reuse the existing full-rectangle self-duality theorem at density `1/2`, followed by explicit
translation/quarter-turn adapters to `Q_n`. The adapter must preserve the internal-edge finset
and the appropriate side finsets. No boundary-free RSW event is substituted for the source's
full crossing event.

### `V2`--`V3`: highest crossing and its stopping support

Use finite reached-face fibers of a stopped exploration from the top boundary. For each good
index `R`, deterministically extract a normalized boundary path `gamma_R`: trim it to the last
left-side visit and the first subsequent right-side visit, and prove that all intermediate
vertices have strictly interior first coordinate. The selected path must be the outer/top
boundary component, not an arbitrary component supplied by parity. Fibers are indexed only by
`R`; the path is a deterministic function of `R`.

Prove that the horizontal crossing event is the finite pairwise-disjoint union of these good
fibers, that `gamma_R` is open throughout `F_R`, and that `F_R` depends on a sufficient finite
exposed support `E_R`. Do not assert that `E_R` is the exact query trace.

The required locality statement is one-sided: changing bonds strictly below the selected
boundary must preserve the fiber. The more convenient two-sided incident-edge support would
expose the extension coordinates and is therefore too strong for this application.

### `V4`--`V5`: lower bridge probability

For each realizable stopping fiber, define `S(gamma_R)` edgewise using the selected boundary, its
reflection across the vertical axis, and the bottom side of `[-n,n]^2`. The support includes the
last below-to-barrier contact edge, but includes neither barrier edges nor exposed above-side
edges. The fresh-coordinate event is a bottom-to-boundary connection in this edge set. Prove:

1. the fresh support is disjoint from the stopping-fiber support;
2. the fiber and fresh event factor exactly under the finite Bernoulli product law;
3. rectangle incidence and a first-hit argument include the full-square vertical-crossing event
   in the union of the two fresh contact events, with the retained edge prefix in the declared
   support for all boundary and degree-four cases;
4. a separate standard-axiom placement of the exact-half Grimmett event supplies at least `1/2`
   for that full-square input;
5. reflection equates the two symmetric contact probabilities, so the required contact has
   least `1/4`;
6. on the fiber, that contact concretely implies `duminilCopinLowerBridgeEvent n`.

Sum the per-fiber inequalities using the verified ratio-free finite-fiber API. This avoids
conditional probabilities and remains valid for empty or measure-zero candidate fibers.

### `V6`: upper transport

Define the vertical reflection/translation as a square-graph automorphism, prove pointwise
coordinate formulas, prove the sufficient lower-to-upper event inclusion, and use Bernoulli
measure invariance. Event equality is not required for the one-sided probability comparison.

### `V7`: deterministic gluing

Extract finite walk witnesses from both bridge events and the central vertical crossing. Trim
the bridge witnesses to left-right paths in `Q_n`. Apply the verified discrete rectangle
intersection theorem twice to obtain a common vertex between the central path and each bridge
path. Append and reverse the corresponding walk segments to obtain one open walk from the
bottom side to the top side. Prove every traversed bond lies in `duminilCopinRectangleEdges n`.

### `V8`--`V9`: FKG and arithmetic

The bridge definitions are finite unions/intersections of `connectionEventIn`, hence measurable
and increasing. Apply `bernoulliBondMeasure_real_fkg` first to the two bridges and then to their
intersection and the central crossing. Use the deterministic inclusion and monotonicity of real
measure, then normalize `(1/2) * (1/8) * (1/8) = 1/128` by `norm_num` or `ring`.

## Lean interface

Verified existing declarations and modules:

- `half_le_squareRectangleCrossingProbability_centered` and
  `half_le_grimmettRectangleCrossingProbability_even` (`BondCrossingDuality`);
- the standard-axiom even/odd central-square placement and first-hit truncation now implemented
  in `TheoremsForExperiment` (its exact axiom closure is the standard three);
- `dependsOn_finiteGraphReachableVertices_fiber` (`FiniteReachability`);
- `mul_measureReal_biUnion_le_biUnion_inter` and
  `mul_measureReal_le_biUnion_inter_of_partition` (`FiniteFiberIndependence`);
- `bernoulliBondMeasure_real_fkg` (`FKGInfinite`);
- `squareWalk_support_inter_of_left_right_and_bottom_top`,
  `squareWalk_support_inter_of_left_right_and_bottom_top_of_le`, and
  `squareWalk_support_inter_of_left_right_and_bottom_top_of_le_int`
  (`RectangleIntersection`);
- cubic translations, reflections, quarter-turn graph isomorphisms, graph-iso event transport,
  and Bernoulli measure invariance used throughout `RSWPlacements`, `BRReflection`, and
  `BRVerticalSymmetry`;
- finite candidate-path and open-path union architecture in `CanonicalCrossing`;
- stopped dual exploration/fiber architecture in `BRDualExploration` and
  `BRFiberExtensionProbability`.
- public witness extraction and support bounds for the two-, three-, and four-fresh-edge
  Grimmett extensions in `RSWHalf` and `StrictDualCrossing`.

Proposed declarations will live in a dedicated planar module rather than inside the final
source-facing wrapper. Names remain provisional until their statements compile:

- full-square horizontal/vertical events and their placements for `Q_n`;
- lower and upper Duminil-Copin bridge events;
- a finite highest-crossing stopped exploration and fiber support;
- per-fiber fresh region/contact events and the `1/4` extension estimate;
- `one_eighth_le_duminilCopinLowerBridgeProbability`;
- the upper-bridge probability transport;
- the three-event deterministic gluing inclusion;
- bridge measurability and monotonicity wrappers.

## Dependency and implementation order

1. Coordinate and side membership lemmas, graph automorphisms, and square-crossing placements.
2. Full-square path candidates and stopped highest-crossing fibers.
3. One-sided support locality and fresh-region disjointness.
4. Deterministic contact and final three-path incidence/gluing.
5. Event support, measurability, and increasingness.
6. Per-fiber product estimates, finite summation, bridge symmetry, FKG, and arithmetic.
7. Source-facing wrapper, comparator, axiom audit, and full build.

The selected certificate is the smallest source-faithful one found. Pure square gluing is the
obstacle the source explicitly identifies; arbitrary selectors fail freshness; and importing a
general Jordan theorem would be substantially stronger than the finite stopped exploration and
two rectangle-incidence lemmas actually consumed downstream.

## Review and trust

Current gate status after the preserved independent review in
[`INDEPENDENT_PROOF_EXPANSION_REVIEW.md`](INDEPENDENT_PROOF_EXPANSION_REVIEW.md):

- `G0 Source`: passed.
- `G1 Obligations`: blocked until the normalized selector and edgewise first-contact conclusion
  are formalized exactly as V2--V4b.
- `G2 Falsification`: the source claim survives, but the unnormalized self-avoiding-barrier
  formulation was refuted by the explicit `n=2` path recorded in the review.
- `G3 API`: blocked; generic reachability supplies all-incident-edge dependence, and the current
  BR selector chooses an arbitrary component rather than the required outer boundary.
- `G4`--`G9`: pending implementation and validation.

No new axiom is proposed. Existing named project axioms may remain in unrelated imported RSW or
self-duality declarations, but the final `#print axioms` result must be recorded exactly; the
Duminil-Copin proof must not hide the decisive stopping or incidence step in a new axiom.

Before the proof is declared complete, freeze the implementation revision and obtain a fresh
read-only proof-expansion review. Preserve that first-pass report before applying repairs. Then
run the file build and root build, scan for `sorry`/`admit`, print the transitive axioms of the
public theorem, compile the source application, and update the comparator topic card.
