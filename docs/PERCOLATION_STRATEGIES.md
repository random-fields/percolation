# Percolation and statistical-physics pictorial strategies

Companion playbook to [`PICTORIAL_PROOF_PROTOCOL.md`](PICTORIAL_PROOF_PROTOCOL.md). Use both whenever the
source is a percolation, lattice, or statistical-physics argument — crossings, circuits, arms,
duality, exploration, FKG. The section headings below name the phase of the general protocol
they extend.

## Conventions to fix at transcription (extends Phase 1)

For a lattice figure, the transcription must additionally fix:

- lattice ambient type: `ℤ²`, a finite graph, faces, primal edges, or shifted-dual edges;
- open/closed, primal/dual, occupied/vacant conventions;
- whether paths may use boundary edges;
- exact vertex and edge regions of every named box, annulus, side, corner, and port;
- the smallest legal scale.

## Standard degenerate instances (extends Phase 3)

Test every proposed statement at:

- scale `0` and `1`;
- width-one rectangles;
- empty side sets;
- coincident corners;
- touching inner and outer boundaries;
- reversed orientation and swapped endpoints;
- walks that repeat vertices;
- paths running along the boundary.

Distinguish vertex, edge, and primal/dual crossing. Check whether "disjoint regions" really gives
disjoint edge-coordinate supports. Enumerate a very small finite configuration set when cheap.

## Planar certificate rungs (extends Phase 5)

Ordered from most elementary. Take the first that discharges the downstream consequence:

1. **Finite reachability** — define "inside", "below", "left of" as reachability in a finite
   graph after deleting a separator. Its edge boundary is a concrete finite set. Preferred for
   any lowest or leftmost region.
2. **Local parity** — around a square cell, a vertex predicate changes 0, 2, or 4 times; use it
   for even degree at interior dual vertices and explicit odd boundary ports.
3. **Mod-two intersection** — with alternating boundary endpoints, a parity index along one path
   changes exactly at crossings; different endpoint parities force an intersection.

### The Jordan-curve temptation

Do not reach for a discrete Jordan curve theorem, winding number library, or embedding theorem
until the finite rungs are exhausted. In practice the finite substitute has always existed:
where a Jordan argument is tempting, the missing ingredient is usually that the interface graph
*forgets the local non-crossing pairing at degree-four cells* — encode that pairing explicitly
instead.

**Future work.** A reusable discrete Jordan/separation statement for this repository is a named
candidate for later development, per the general protocol's Phase 5 rule: record the general
statement in `DESIGN_DECISIONS.md`, do not axiomatize it. Until it exists, use the elementary
encodings above.

## Probability layering (extends Phase 6)

The deterministic layer — in a file that does not import probability — contains: finite regions,
side sets, coordinate maps, trimming and concatenation constructions, reachability regions,
frontier edge sets, incidence and separation lemmas.

Only once the deterministic inclusion compiles, add, in order:

- the event as existence of a finite witness;
- its finite support;
- measurability;
- exact disjointness of supports;
- symmetry or measure transport;
- independence or FKG;
- the finite summation;
- the numerical bound.

A compiling probability shell wrapped around an unproved geometric inclusion is not progress.
Never axiomatize the final probability inequality because its picture is hard; at most isolate
the smallest true deterministic incidence lemma, and only with the owner's explicit approval.

## Extremal selection and stopping

Use this section whenever the source conditions on a highest / lowest / leftmost / outermost
object, or stops another path at its first or last contact with one — "condition on the highest
crossing", "the outermost circuit", "the unexplored region beyond it", "stop at first
contact". This section distills two successful formalizations of Duminil-Copin's
Proposition 2.14.

> Select a canonical finite region first and derive its frontier. Do not begin by ordering all
> candidate paths. Define "first" and "last" only after a concrete walk has supplied an order.

### Why path enumeration fails

A finite box has finitely many candidate paths, so it is tempting to enumerate them and select
the first open one. This produces a canonical path but not a valid stopping set. The fiber "path
`P` was selected" contains two kinds of information: every edge of `P` is open, *and* every
earlier candidate failed. The second condition may inspect coordinates on exactly the side the
continuation argument needs fresh — a finite finger/neck configuration is a concrete
counterexample. Canonicality of a selector does not imply freshness of the coordinates on one
side of the selected path. Conditioning only on "`P` is open" is also wrong: it omits the
information used to select `P`.

Path enumeration is admissible only when rejection of every earlier candidate provably depends
only on the intended revealed side, and the selected-path fiber has a finite support disjoint
from the continuation event. Otherwise use the region-first construction.

### The region-first construction

1. **Explore a region, not a path.** Define the extremal side as reachability from a boundary
   through the appropriate edge state (e.g. dual faces reached from the top through closed-dual
   edges). The exploration source encodes the extremum: highest ↔ top boundary, lowest ↔ bottom,
   leftmost ↔ left, rightmost ↔ right, outermost ↔ exterior frame.
2. **Work in an explicit finite frame** with exterior margins — real vertices representing
   "above", "below", and the outside, with enough room to close a barrier without re-entering
   the physical domain. Every boundary set and coordinate bound is an explicit finite set.
3. **Fill holes.** The raw reached set can enclose pockets whose boundaries are internal
   circuits, not the intended outer frontier. Fill every complementary component that cannot
   reach the designated opposite exterior. Make the fill-or-not decision explicit.
4. **Extract and normalize the frontier.** Obtain a boundary cycle with a certified separation
   invariant (parity, not an informal Jordan appeal). Normalize it: rotate to a fixed anchor,
   orient by a fixed neighbour, split at a second anchor, discard artificial frame arcs, crop
   with first-hit prefixes. Implement a last visit by reversing the walk and reusing the
   first-visit lemma. Do not assume coordinate monotonicity — an outermost path can wiggle.
5. **Condition on the reached-set fiber, not on the path** — the event that the explored
   region equals a given candidate `R`.
   Fibers are finite in number, pairwise disjoint; restrict to realizable good indices. Choose
   one representative frontier per fiber and prove its required properties hold throughout the
   fiber. Literal uniqueness of a walk representation is usually false (rotation, reversal) and
   unnecessary.
6. **Minimize the fiber support.** The support must contain what is needed to reconstruct the
   stopped exploration — not every coordinate of a geometrically convenient hull. Prove
   directly that the support determines the fiber. An oversized support turns a true
   conditional-independence argument into a false disjointness claim.
7. **Stop at first contact using walk order.** Prove the contact set is nonempty; select the
   first contact along the walk; trim the walk at that contact; state the firstness property
   explicitly. Never select "first" from an unordered set — a set has no traversal order. Audit the
   terminal edge separately: strict-before avoidance does not control the bond entering the
   contact vertex.
8. **Classify every prefix coordinate** rather than demanding freshness:

   | Class | Meaning | Witness may use it? | Event queries it? |
   |---|---|---:|---:|
   | fresh | not revealed by the fiber | yes | yes |
   | fiber-forced usable | revealed, forced to the needed value | yes | no |
   | forbidden | revealed without a usable forced value | no | no |

   The continuation event queries only fresh coordinates; forced coordinates are declared to
   their known value inside the witness predicate.
9. **Assemble probability by finite summation.** Independence comes from disjoint finite
   supports; sum fiberwise bounds over the finite disjoint partition. Avoid conditional ratios
   and regular conditional probabilities. Handle degenerate scales (e.g. `n = 1`) by a direct
   finite witness instead of forcing the general construction through them.

The invariant that works is not "the stopped prefix is completely fresh" but:

> every prefix coordinate is either outside the exact fiber support, or inside it and forced to
> the usable value by the fiber.

### Implementation order

1. Final deterministic gluing theorem, with arbitrary arm witnesses.
2. Fixed-barrier attachment lemma — deterministic barrier, before any random selection.
3. Finite side reachability and exact reached-set fibers.
4. Filled hull and frontier extraction.
5. Selected path normalization, and transfer of its properties across each fiber.
6. Minimized fiber support and the theorem that it determines the fiber.
7. Forced coordinates (exit edges open on the fiber).
8. Fresh/forced continuation events.
9. First-contact prefix theorem, with a separate terminal-edge case.
10. Reflected event cover.
11. Fiberwise bound, finite summation, degenerate scales.
12. Final symmetry/FKG assembly; sorry, axiom, and build audits.

### Failure modes

- Arbitrary first-open selector — rejection of earlier candidates reveals wrong-side coordinates.
- Conditioning only on path openness — omits the information used to select the path.
- Oversized fiber support — convenient hull coordinates produce a false disjointness claim.
- Treating the selected subarc as the whole frontier — side excursions escape the audit.
- Ignoring the terminal contact edge — "strictly before" theorems do not classify it.
- Demanding every prefix coordinate be fresh — some are revealed but forced and usable.
- Demanding literal uniqueness of cycles or walks — rotation and reversal break it.
- Taking "first contact" from the unordered support set — traversal order belongs to the walk.
- One reflection formula for everything — primal vertices, dual faces, and stored
  representatives transform by different formulas; verify each map separately.
- Probability before geometry — the shell compiles while the decisive inclusion is assumed.
- Forcing the general construction through degenerate scales — isolate them as direct witnesses.
