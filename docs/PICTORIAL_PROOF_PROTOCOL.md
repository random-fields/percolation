# Pictorial proof protocol

This protocol applies whenever a source proof relies on a figure, planar intuition, phrases such
as “clearly surrounds”, “must cross”, “leftmost/lowest path”, or an unstated Jordan-curve
argument. Read it before editing Lean files for such a step.

## Required outcome

A picture is evidence for a finite combinatorial lemma, not a proof object. Replace it by an
explicit statement about finite vertices, edges, walks, reachability, parity, or disjoint finite
coordinate supports. Record the replacement in the relevant comparator topic card.

Do not introduce a global topology theorem when the target needs only a local crossing, barrier,
or parity consequence. In particular, do not make a discrete Jordan curve theorem a dependency
until the finite alternatives below have been exhausted.

## Mandatory workflow

1. **Locate the exact visual claim.** Record the source, page, figure, hypotheses, and the precise
   downstream conclusion. Separate what the figure suggests from what the proof actually needs.
2. **Inventory existing APIs.** Search Mathlib and `Percolation/Planar/` for walk trimming,
   reachability, finite graph cuts, dual-edge correspondence, parity, graph isomorphisms,
   measurable finite-support events, and independence. Never invent a lemma name.
3. **Assign an independent proof-expansion subagent.** Its task is to write a rigorous natural
   language proof, identify hidden hypotheses, try to refute the proposed lemma on the smallest
   boxes, and search for an elementary replacement for any large topological dependency. The
   main proving agent consumes that written artifact rather than re-deriving the picture while
   elaborating Lean.
4. **Make the geometry finite.** Replace rays and infinite clusters by first-hit, last-exit, or
   box-truncated walks. State every side, endpoint, support, and scale inequality explicitly.
5. **Normalize paths.** Trim walks with `takeUntil`/`dropUntil`, convert to paths with `toPath`
   when simplicity is needed, and prove that the retained segment stays in the intended region.
6. **Choose the smallest elementary certificate.** Prefer the techniques below in order.
7. **Prove deterministic geometry first.** Keep probability, measurability, and FKG out of the
   file until the path inclusion or barrier lemma builds on its own.
8. **Add the probability layer.** Prove finite support with `DependsOn`, measurability, disjoint
   coordinate support, symmetry/measure transport, and only then FKG or independence.
9. **Test degenerate scales.** Check `n = 0`, width one, empty side sets, coincident corners, and
   whether strict/non-strict inequalities change the picture. Add executable counterexample tests
   for any formerly axiomatized statement.
10. **Audit the dependency closure.** Run the file build, the relevant root build, sorry/admit
    scans, and `#print axioms` on the final public theorem. Update the comparator trail and any
    axiom ledger entries that became stale.

## Elementary replacement ladder

Use the first rung that proves the required consequence.

### 1. First-hit and last-exit trimming

For a purported infinite or loosely drawn path, choose a finite endpoint outside the relevant
box, then retain the segment from its last visit to the inner boundary to its first visit to the
outer boundary. This is normally enough to produce a literal annulus crossing.

### 2. Finite reachability and flood fill

Define “inside”, “below”, “left of”, or “reachable from the boundary” as reachability in a finite
induced graph after deleting the claimed separator. Its edge boundary is a concrete finite set.
This is the preferred representation of a lowest/leftmost crossing region.

### 3. Local even-degree parity

Around a square cell, membership in a vertex predicate changes zero, two, or four times. Use this
to prove that a finite frontier has even degree at every dual vertex. Then use finite graph cycle
or path extraction, not topological interior/exterior language.

### 4. Mod-two intersection

When two paths have alternating boundary endpoints, define a parity index along one path. Show it
changes exactly when an edge crosses the other path. Different endpoint parities force an
intersection. Reuse the architecture in `Percolation/Planar/AlternatingPaths.lean`.

### 5. Graph-theoretic extraction

Use finite even-degree graphs, bridge/cycle lemmas, walk decomposition, `Walk.takeUntil`,
`Walk.dropUntil`, `Walk.append`, and `Walk.toPath`. If a cycle is requested only to block a radial
path, first ask whether a union of four transverse crossings already supplies the required
barrier.

### 6. Weaken to the downstream consequence

Examples:

- replace “there is a unique surrounding simple cycle” by “every inner-to-outer path intersects
  one of these four dual crossings”;
- replace a full numerical RSW formula by a positive scale-uniform rectangle-crossing bound;
- replace a global four-infinite-arm separation theorem by independent finite annular barriers;
- replace a trace-bijection axiom by an explicit complement/dual/rotation involution on a finite
  edge set.

Only after all six rungs fail should a larger topology theorem be proposed. The proposal must say
why each finite alternative is insufficient and must receive an independent refutation review
before becoming an axiom.

## Canonical crossing and stopping-set checklist

A lowest/leftmost path argument is not complete until all of the following are formalized:

- a finite type or finset of candidate paths;
- a total order or finite reachability region used for deterministic selection;
- existence and uniqueness of the selected normalized path;
- an exact characterization of `{selectedPath = P}`;
- a finite `DependsOn` support for that fiber event;
- a proof that the extension event uses a disjoint coordinate support;
- measurability and the resulting independence identity;
- a finite disjoint-union/summation theorem over all possible selected paths.

The phrase “condition on the leftmost crossing” hides these obligations. Do not use it as a single
informal step.

## Required proof-expansion artifact

For each substantial visual argument, add a document under `docs/<target>/` containing:

- source location and figure numbers;
- the exact informal claim and downstream use;
- a finite rigorous proof with all edge cases;
- proposed Lean declarations, clearly distinguished from existing names;
- existing Mathlib/local APIs verified by search;
- elementary alternatives considered and why the selected one is smallest;
- counterexamples or rejected stronger statements;
- an implementation order and axiom-discharge plan.

For Grimmett Theorem 11.11, the worked example is
[`theorem-11.11/PICTORIAL_PROOF_EXPANSION.md`](theorem-11.11/PICTORIAL_PROOF_EXPANSION.md).

## Completion gate

Never describe a pictorial step as formalized merely because its probability algebra builds. It
is complete only when the deterministic inclusion/separation theorem is proved, the event support
and measurability are explicit, the public theorem has the intended axiom closure, and the
source-to-formal comparator records any divergence from the picture.
