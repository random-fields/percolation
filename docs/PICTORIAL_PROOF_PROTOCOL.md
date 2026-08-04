# Pictorial proof protocol

This protocol applies whenever a theorem, definition, or proof refers to a figure or relies on
visual language such as “clearly surrounds”, “must cross”, “as in the picture”, “leftmost”,
“lowest”, “inside”, “outside”, “above”, or an unstated Jordan-curve argument.

The protocol is deliberately broader than planar separation. A figure may encode coordinates,
incidence, symmetry, a gluing construction, a stopping rule, coordinate independence, a
commutative diagram, or only intuition. The first task is to determine which role it plays.

The governing principle is:

> A picture may identify a conjectured finite certificate, but it is never itself a Lean proof
> object.

For a proof-bearing figure, replace every visual inference by an explicit statement about
coordinates, finite vertices or edges, walks, reachability, order, parity, maps, or disjoint
supports. Record that replacement in the source-to-formal comparator trail.

## Fast path for an autoformalizing agent

Run this decision procedure before editing Lean.

1. Locate every figure cited in the proof and the sentences that use it.
2. Classify each figure using the table below.
3. For every proof-bearing figure, create visual obligations `V1`, `V2`, and so on. Each
   obligation has explicit hypotheses, a precise conclusion, and one downstream use.
4. Freeze the coordinate and boundary conventions. Do not infer them from apparent scale,
   angle, spacing, color, or drawing accuracy.
5. Try to falsify each obligation on the smallest legal instances and on nearby degenerate
   instances.
6. Search Mathlib and the local repository for the exact deterministic API.
7. Choose the smallest certificate from the replacement ladder below.
8. Prove deterministic geometry before defining or estimating probabilities.
9. Compile the application that recovers the source step, audit axioms and sorries, and update
   the comparator record.

If a coordinate convention, boundary rule, or visual implication is genuinely ambiguous, stop
with status `BLOCKED_SOURCE_AMBIGUITY`. Do not silently select the interpretation that is easiest
to prove.

## Figure classification

Every figure in scope receives one of these classifications.

| Class | Meaning | Required action |
|---|---|---|
| `ILLUSTRATIVE_ONLY` | The prose proof is complete without the figure. | Record why no formal obligation comes from it. |
| `DEFINITIONAL` | The figure fixes notation, coordinates, orientation, or boundary pieces. | Transcribe those conventions and test them on concrete points. |
| `WITNESS_CONSTRUCTION` | The figure shows how to trim, concatenate, reflect, or select witnesses. | State the construction as a finite function or existence lemma with invariants. |
| `INCIDENCE_OR_SEPARATION` | The proof uses “meets”, “crosses”, “surrounds”, “blocks”, or “lies on one side”. | Replace it by reachability, a cut, parity, or a finite intersection lemma. |
| `SYMMETRY_OR_TRANSPORT` | The figure identifies objects after translation, rotation, reflection, duality, or complementation. | Define the map and prove its action on vertices, edges, events, and measure. |
| `SELECTION_OR_STOPPING` | The proof conditions on a lowest, leftmost, first, last, or outermost object. | Define the finite candidate family, deterministic selector, fibers, and support locality. |
| `DEPENDENCY_SCHEMATIC` | The picture suggests that events use separate randomness. | Prove exact coordinate supports and their disjointness; the drawn separation is insufficient. |
| `COMMUTATIVE_DIAGRAM` | The argument is equality of composites or a universal property. | State every object and arrow and prove the path equalities; geometry is irrelevant. |
| `PLOT_OR_SIMULATION` | The figure presents numerical or experimental evidence. | Do not extract an exact theorem unless the surrounding text states one. |

A single figure may have several classes. Split it into separate visual obligations rather than
giving the whole figure one vague interpretation.

## Producer and reviewer separation

For a substantial proof-bearing figure, use a fresh proof-expansion reviewer when the host
supports independent agents. Give the reviewer the source pages, theorem context, transcription
sheet, and proposed visual obligations, but do not prompt it to confirm the producer's intended
proof. Its first pass is read-only and must:

- restate the visual claim without using “obvious” geometric language;
- expose hidden boundary, simplicity, finiteness, and nondegeneracy hypotheses;
- try to falsify the claim on the smallest boxes;
- search for a smaller finite certificate;
- distinguish a false statement from a missing proof;
- return its report before suggesting repairs.

The producing agent may continue when no independent-agent facility exists, but must record
`independent review unavailable`; a producer's second reading is not independent. If
[`AUTOMATED_REVIEW.md`](../AUTOMATED_REVIEW.md) applies, its independent-review release gate still
has to be satisfied.

## Phase 1: freeze the source evidence

Record the following before proposing Lean declarations:

- source id, edition or revision, printed page, PDF page, figure number, and caption;
- the exact surrounding sentences that invoke the figure;
- the theorem hypotheses already in force at that point;
- which parts of the figure are defined by prose or a legend;
- which apparent features are merely artistic and must not be used;
- the precise later step that consumes the visual claim.

OCR is only a navigation aid. Verify symbols, strict inequalities, subscripts, open or closed
endpoints, and orientations against the rendered page. If the image conflicts with the prose,
record the conflict and treat the mathematical statement as ambiguous until resolved.

If a proof-bearing figure is unavailable, illegible, or missing a referenced panel, use status
`BLOCKED_SOURCE_AMBIGUITY`. Do not reconstruct it from memory or from a later author's redraw.
Treat every panel of a multi-panel figure separately when the proof uses different implications
from different panels.

### Figure transcription sheet

For a geometric or combinatorial figure, explicitly fill in:

- ambient type: for example `Z^2`, a finite graph, faces, primal edges, or shifted-dual edges;
- coordinate axes, origin, orientation, units, translation, and scaling;
- exact vertex region and edge region;
- all named sides, corners, ports, boxes, annuli, and overlap regions;
- inclusive versus exclusive boundaries;
- whether paths may use boundary edges and whether endpoints may coincide;
- open/closed, primal/dual, occupied/vacant, and orientation conventions;
- every symmetry map used and its fixed points;
- every asserted disjointness relation;
- the smallest permitted scale.

Never infer any of the following solely from a drawing:

- equality of lengths, angles, or probabilities;
- tangency, uniqueness, simplicity, or connectedness;
- disjointness of paths or coordinate supports;
- a path being inside a region between its endpoints;
- an exhaustive list of cases;
- preservation of an event under a visual symmetry;
- which side of a boundary is open or closed.

## Phase 2: extract atomic visual obligations

Start from the downstream theorem, not from the strongest claim suggested by the picture. Ask:

> What is the weakest deterministic statement that makes the next non-visual proof line valid?

Create a ledger with one row per atomic inference.

| Id | Source phrase or feature | Explicit hypotheses | Exact conclusion | Downstream use | Status |
|---|---|---|---|---|---|
| `V1` | “the paths must meet” | endpoints, regions, graph, boundary order | supports intersect | concatenate witnesses | target |
| `V2` | reflected placement in figure | exact affine map and region inequalities | mapped path stays in target region | apply symmetry | target |

Do not combine deterministic geometry, measurability, independence, FKG, and numerical algebra in
one obligation. A typical figure produces several declarations:

1. coordinate membership;
2. witness trimming or transport;
3. deterministic incidence or event inclusion;
4. finite support and measurability;
5. independence, FKG, or measure transport;
6. the numerical consequence.

### Statement-safety checks

For every proposed obligation, compare:

- all source quantifiers and all new Lean quantifiers;
- natural, integer, real, and unit-interval domains;
- strict and non-strict boundaries;
- paths versus walks, simple paths versus arbitrary walks, and vertices versus faces;
- finite versus infinite objects;
- primal versus dual edge states;
- existence versus uniqueness or canonical choice;
- an event inclusion versus an event equality;
- the source scale range and Lean behavior at scale zero.

If the source uses only existence, do not add uniqueness because the picture appears to show one
object. If the downstream argument uses only a barrier, do not formalize a unique surrounding
cycle merely because one is drawn.

## Phase 3: falsify before proving

Try to break the proposed deterministic statement before investing in its proof.

1. Check scale `0`, scale `1`, width-one rectangles, empty side sets, coincident corners, and
   touching inner and outer boundaries.
2. Reverse orientations and swap endpoints.
3. Allow a walk to repeat vertices or edges unless simplicity is an explicit hypothesis.
4. Put a path along the boundary and check whether the claimed intersection still follows.
5. Distinguish vertex intersection, edge intersection, and primal/dual geometric crossing.
6. Check whether “disjoint regions” actually implies disjoint edge-coordinate supports.
7. Enumerate all configurations on a very small finite edge set when this is cheap.

Prefer compiling Lean regression examples for discovered boundary behavior. Computation with
`decide` or `native_decide` may test a finite model, but passing examples never proves the general
claim. One checked counterexample is decisive and must be recorded.

Add source-compatible hypotheses only when the source genuinely supplies them. Otherwise weaken
or reject the proposed obligation.

## Phase 4: search before designing new geometry

Search Mathlib and the local repository before naming or implementing a lemma. Search by concept,
type signature, and neighboring declarations, not only by the source's terminology.

For this repository, inspect at least the relevant parts of:

- `Percolation/Planar/` for crossings, duality, parity, graph isomorphisms, and annuli;
- graph walk APIs for `takeUntil`, `dropUntil`, `append`, support, edges, and `toPath`;
- finite reachability, cuts, connected components, degree parity, and cycle extraction;
- `DependsOn`, finite-coordinate measurability, independence, and measure transport;
- translations, reflections, rotations, complementation, and primal/dual edge equivalences.

Useful local architectures include `AlternatingPaths.lean` for mod-two intersection and the
finite frontier construction used by the planar Peierls development. Reuse the architecture, not
unverified declaration names. Every name in the proof-expansion artifact must be marked either
`verified existing` or `proposed`.

## Phase 5: choose the smallest finite certificate

Use the first rung that proves the required downstream consequence.

### 1. Coordinate normalization and explicit maps

Many figures hide only arithmetic. Define the translation, quarter-turn, reflection, scaling, or
dual-edge map. Prove pointwise formulas, region membership, adjacency preservation, and the image
of each named side. Do not jump directly to a probability symmetry theorem.

### 2. First-hit and last-exit trimming

Replace a ray or loosely drawn path by a finite subwalk. Choose a finite endpoint outside the
relevant box, retain the segment from its last visit to the inner region to its first visit to the
outer boundary, and prove every retained vertex and edge lies in the intended support.

### 3. Finite reachability and flood fill

Define “inside”, “below”, “left of”, or “reachable from the boundary” using reachability in a
finite induced graph after deleting the proposed separator. Its edge boundary is a concrete
finite set. This is the preferred representation of a lowest or leftmost region.

### 4. Local even-degree parity

Around a square cell, membership in a vertex predicate changes zero, two, or four times. Use this
to show a finite frontier has even degree at interior dual vertices and explicit odd boundary
ports. Extract paths or cycles from the resulting finite graph.

### 5. Mod-two intersection

When paths have alternating boundary endpoints, define a parity index along one path. Show it
changes exactly when an edge crosses the other path. Different endpoint parities force an
intersection. Reuse the architecture in `Percolation/Planar/AlternatingPaths.lean`.

### 6. Graph-theoretic extraction

Use finite components, cuts, even-degree graphs, bridges, cycle decomposition, and walk
normalization. If a closed walk is enough, do not first prove the existence of a unique simple
cycle. If a path is needed, erase loops with `Walk.toPath` only after preserving the required
support and endpoint facts.

### 7. Weaken to the actual downstream consequence

Examples:

- replace “there is a unique surrounding simple cycle” by “every inner-to-outer path intersects
  one of these four dual crossings”;
- replace a full numerical RSW formula by a positive scale-uniform crossing bound when that is
  all the theorem uses;
- replace a global four-infinite-arm separation theorem by finite annular barriers;
- replace an informal trace bijection by an explicit complement/dual/rotation involution on a
  finite edge set.

### 8. General topology only as a last resort

Do not add a discrete Jordan curve theorem, winding-number library, or global embedding theorem
until the finite alternatives above have been exhausted. A proposal for a larger topological
primitive must:

- state the exact finite consequence that could not be obtained elementarily;
- explain why every earlier rung is insufficient;
- identify all embedding and nondegeneracy hypotheses;
- include small-instance falsification attempts;
- receive an independent read-only review before it becomes a project axiom or trusted boundary.

Never axiomatize the final probability inequality merely because its deterministic picture is
hard. At most isolate the smallest true deterministic incidence lemma.

## Phase 6: design the Lean declaration bundle

The useful unit of autoformalization is normally a small interface, not one giant theorem.

### Deterministic layer

Define, as needed:

- the finite vertex and edge regions;
- named side and corner finsets;
- normalized witness types or predicates;
- coordinate transformations;
- first-hit, last-exit, reflection, or concatenation constructions;
- reachability regions and frontier edge sets;
- incidence, separation, parity, and event-inclusion lemmas.

Prove the deterministic target in a file that does not import probability merely for convenience.
This makes false geometry easier to detect and the result reusable.

### Event and probability layer

Only after the deterministic inclusion builds, add:

- the event definition as existence of a finite witness;
- a finite `DependsOn` support;
- measurability;
- exact disjointness of coordinate supports;
- symmetry or measure transport;
- independence or FKG;
- finite union, disjoint-union, or summation identities;
- numerical inequalities.

Do not prove probability algebra around an unproved geometric inclusion. A compiling probability
shell with an axiomatized picture is not progress on the pictorial step.

## Common proof recipes

### Crossing and gluing figures

For a figure claiming that several crossings create a larger crossing:

1. extract normalized finite witness walks from each event;
2. trim them to the overlap region;
3. prove the required pairwise intersections by alternating endpoints or an existing incidence
   lemma;
4. choose explicit first intersection vertices;
5. take the necessary subwalks, append them, and prove openness edge by edge;
6. prove the appended support lies in the target region;
7. use `toPath` only if the target event requires a path;
8. package the construction as an event inclusion;
9. apply FKG or independence in a later theorem.

The phrase “the crossings can clearly be joined” hides steps 2--7.

### Surrounding circuits and barriers

First ask whether the downstream proof needs a circuit or merely a barrier. Four transverse
crossings may directly imply that every radial path meets a dual closed edge. If an actual cycle
is required, concatenate to a finite closed walk, prove odd ray-crossing parity, decompose the
even-degree graph into cycles, and select an odd component.

### Infinite paths and arms

Never reason directly from how an infinite ray is drawn. Choose a finite outer scale, select a
finite path to a vertex outside it, trim by last exit and first hit, prove the finite annular
statement, and only then quantify over scales or pass to an intersection of events.

### Symmetry, reflection, and duality figures

Provide an explicit vertex equivalence, its induced edge equivalence, the configuration map, and
the event preimage or image theorem. Then prove that the measure is preserved or transported.
Visual congruence of rectangles does not imply equality of events without this chain.

## Canonical crossing and stopping-set checklist

A lowest, leftmost, first, last, highest, or outermost-path argument is incomplete until all of
the following are formalized:

- a finite type or finset of candidate normalized paths;
- existence of a candidate on the source event;
- a deterministic order, reachable-side region, or tie-breaking rule;
- existence and uniqueness of the selected normalized path;
- an exact characterization of the fiber `{selectedPath = P}`;
- a finite `DependsOn` support for that fiber event;
- a proof that the extension event uses a disjoint coordinate support;
- measurability and the resulting independence or conditional identity;
- a finite disjoint-union or summation theorem over all possible selected paths.

A lexicographically least path is not automatically a valid lowest path: its fiber must have the
locality property needed by the probability argument. The phrase “condition on the leftmost
crossing” is never accepted as one informal step.

## Phase gates

Do not advance past a failed gate.

| Gate | Required evidence |
|---|---|
| `G0 Source` | Figure classification, exact citation, surrounding text, and conventions are recorded. |
| `G1 Obligations` | Every visual inference has an atomic `V`-id, exact statement, and downstream use. |
| `G2 Falsification` | Degenerate cases and small legal instances were checked; counterexamples are recorded. |
| `G3 API` | Existing declarations were searched and verified; proposed names are labeled proposed. |
| `G4 Deterministic` | Coordinate, trimming, incidence, separation, or parity lemmas compile without probability shortcuts. |
| `G5 Event` | Event inclusion, finite support, and measurability compile. |
| `G6 Probability` | Independence/FKG/transport hypotheses are explicit and the numerical consequence compiles. |
| `G7 Trust` | Relevant builds pass; sorry/admit and transitive axiom audits are recorded. |
| `G8 Comparator` | The source-to-formal trail states all encoding differences and recovers the source step. |

For a figure classified `ILLUSTRATIVE_ONLY`, only `G0` and a short justification are required.
For a definition-only figure, use `G0`, the relevant part of `G1`, and concrete transcription
tests. All proof-bearing figures require every applicable gate.

## Required proof-expansion artifact

For each substantial proof-bearing figure, add a document under `docs/<target>/`. Use this
minimum structure:

```text
# Pictorial proof expansion for <target>

## Source evidence
source id, pages, figures, caption, invoking prose

## Figure classification and transcription
role, coordinates, regions, boundaries, states, symmetries

## Visual-obligation ledger
V-id, hypotheses, conclusion, downstream use, status

## Falsification record
degenerate instances, finite enumeration, rejected stronger statements

## Finite rigorous proof
one subsection per V-id

## Lean interface
verified existing declarations and clearly labeled proposed declarations

## Dependency and implementation order
deterministic layer, event layer, probability layer

## Review and trust
builds, sorry scan, #print axioms, reviewer findings, remaining boundary
```

The artifact must also state:

- elementary alternatives considered and why the selected certificate is smallest;
- any divergence from the source picture;
- counterexamples to tempting stronger formulations;
- an axiom-discharge plan if a true statement remains external.

For a substantial new topological primitive, canonical stopping-set construction, or proposed
axiom, obtain a fresh read-only proof-expansion review. When an independent agent is unavailable,
record that limitation; do not call a producer's second pass independent. The independent report
must be preserved before repairs, following
[`AUTOMATED_REVIEW.md`](../AUTOMATED_REVIEW.md) when that protocol applies.

## Status vocabulary

Use precise status labels in the artifact and comparator record:

- `ILLUSTRATIVE_ONLY`: no proof step depends on the figure;
- `TRANSCRIBED`: definitions and coordinate conventions are formalized;
- `DETERMINISTIC_COMPLETE`: every visual incidence or construction lemma is proved;
- `FORMALIZED`: deterministic, event, probability, trust, and comparator gates pass;
- `BLOCKED_SOURCE_AMBIGUITY`: the source does not determine a necessary convention;
- `BLOCKED_MISSING_GEOMETRY`: an exact true deterministic lemma remains unproved;
- `REJECTED_FALSE`: a proposed visual inference has a counterexample;
- `PROVED_MODULO_NAMED_AXIOM`: only a specifically cited and vetted true axiom remains.

Do not label a theorem `FORMALIZED` when only the probability algebra builds, when the decisive
event inclusion is an axiom, or when the picture was translated into a stronger unreviewed claim.

## Final completion checklist

A proof-bearing figure is discharged only when:

- every visual obligation has a proved Lean declaration or an explicit accepted disposition;
- the source theorem is recovered by a compiling application;
- deterministic geometry is not hidden inside a probability axiom;
- all witness supports, transformations, and boundary conventions are explicit;
- degenerate scales and discovered counterexamples have regression coverage;
- event support and measurability are explicit where probability is used;
- independence, FKG, and symmetry claims use proved hypotheses;
- file and relevant root builds pass;
- sorry/admit scans and `#print axioms` have the intended result;
- the comparator topic card records the figure replacement and all divergences;
- stale axiom-ledger entries are updated.

For Grimmett Theorem 11.11, the worked example is
[`theorem-11.11/PICTORIAL_PROOF_EXPANSION.md`](theorem-11.11/PICTORIAL_PROOF_EXPANSION.md).
