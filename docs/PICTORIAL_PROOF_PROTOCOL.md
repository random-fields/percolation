# Pictorial proof protocol

Use this whenever a proof leans on a figure or on visual language — "clearly surrounds", "must
cross", "as in the picture", "leftmost", "lowest", "inside", "outside", or an unstated
Jordan-curve step.

> A picture may identify a conjectured finite certificate. It is never itself a Lean proof object.

**What this protocol is for.** It is a correctness gate, not a proving accelerator. It earns its
cost by catching a wrong transcription before you build on it, and by naming the exact obligation
that is missing. Once the model survives falsification, stop expanding documents and go prove
Lean. Expanding this protocol's artifacts is not progress on the mathematics.

## Natural language versus Lean

These are two distinct artifacts and must not be blurred.

| | Natural language | Lean |
|---|---|---|
| Lives in | `docs/<target>/PROOF_EXPANSION.md` | `Percolation/…` |
| Says | what is true and why, in full prose | the machine-checked statement |
| Quantifiers | may be implicit | always explicit |
| "Obvious" allowed | never, but prose steps are permitted | nothing is implicit |
| Failure means | the mathematics is wrong or incomplete | the mathematics *or* the encoding is wrong |

Write the natural-language proof **first and completely**. A visual obligation you cannot state
in a paragraph of English you cannot state in Lean either.

### Translating a natural-language step into Lean

For each prose step, in this order:

1. **Name the objects.** Every "the region below γ", "the first crossing" becomes a named finite
   object — a `Finset`, a `Walk`, a function of an index. If you cannot name it without the
   picture, the step is not yet a statement.
2. **Fix the quantifiers.** Decide `∀`/`∃`, and whether existence or *canonical choice* is meant.
   Source existence never becomes Lean uniqueness because the picture draws one object.
3. **Fix the types.** `ℕ` vs `ℤ` vs `ℝ` vs `I`; vertices vs faces; walks vs paths; strict vs
   non-strict; inclusive vs exclusive boundary; primal vs dual.
4. **State the conclusion as the weakest thing the next step consumes.** Not the strongest thing
   the picture suggests.
5. **Write the statement with `sorry` and compile it.** A statement that does not elaborate is not
   a statement. Do this before attempting any proof.
6. **Record the pair** — prose step ↔ Lean declaration — in the expansion document.

If prose and Lean diverge, one of them is wrong. Fix the prose too; do not let the document drift
from the code.

## Figure classification

Classify every figure in scope. A figure may carry several roles — split it into separate
obligations rather than giving the whole picture one vague reading.

| Class | Meaning | Required action |
|---|---|---|
| `ILLUSTRATIVE_ONLY` | Prose is complete without it. | Record why no obligation follows. |
| `DEFINITIONAL` | Fixes notation, coordinates, orientation, boundaries. | Transcribe conventions; test on concrete points. |
| `WITNESS_CONSTRUCTION` | Shows how to trim, concatenate, reflect, or select. | State as a finite function or existence lemma with invariants. |
| `INCIDENCE_OR_SEPARATION` | Uses "meets", "crosses", "surrounds", "blocks", "one side of". | Replace by reachability, a cut, parity, or finite intersection. |
| `SYMMETRY_OR_TRANSPORT` | Identifies objects after a map. | Define the map; prove its action on vertices, edges, events, measure. |
| `SELECTION_OR_STOPPING` | Conditions on a lowest, leftmost, first, last, or outermost object. | See [`STOPPING_SETS.md`](STOPPING_SETS.md) — this class has its own checklist and its own failure modes. |
| `DEPENDENCY_SCHEMATIC` | Suggests events use separate randomness. | Prove exact coordinate supports and disjointness. Drawn separation proves nothing. |
| `COMMUTATIVE_DIAGRAM` | Equality of composites or a universal property. | State objects and arrows; prove path equalities. Geometry is irrelevant. |
| `PLOT_OR_SIMULATION` | Numerical or experimental evidence. | Extract no exact theorem unless the text states one. |

## Phases

Each phase has one output and one gate. Do not pass a failed gate.

### Phase 1 — Extract the image

Read the figure and write down what it actually says, before interpreting it.

Record: source id, edition, printed and PDF page, figure number, caption; the exact sentences
that invoke it; the hypotheses already in force; which features are defined by prose or legend;
which are artistic; and the precise later step that consumes the visual claim.

For a geometric figure also fix: ambient type; axes, origin, orientation, scale; exact vertex and
edge regions; named sides, corners, boxes, annuli; inclusive vs exclusive boundaries; whether
paths may use boundary edges; open/closed, primal/dual, occupied/vacant conventions; every
symmetry map and its fixed points; every asserted disjointness; the smallest legal scale.

Never read off a drawing: equal lengths or angles; tangency, uniqueness, simplicity,
connectedness; disjointness of paths or supports; that a path stays inside a region; an exhaustive
case list; preservation of an event under a visual symmetry; which side of a boundary is closed.

OCR is a navigation aid only — verify symbols, inequalities, subscripts and endpoints against the
rendered page. If the image contradicts the prose, record the conflict and treat the statement as
ambiguous.

> **Gate 1.** Citation, classification, conventions, and consuming step are recorded. If a figure
> is missing, illegible, or genuinely ambiguous, stop and say so. Do not reconstruct it from
> memory or pick the reading that is easiest to prove.

### Phase 2 — Replace the image with a statement

Ask, for each visual inference:

> What is the **weakest** deterministic statement that makes the next non-visual line valid?

Work backwards from the downstream theorem, never forwards from the strongest claim the picture
suggests. Give each inference an id, explicit hypotheses, an exact conclusion, and exactly one
downstream use. Keep them atomic — do not mix geometry, measurability, independence and
arithmetic in one obligation. A single figure typically yields: coordinate membership; witness
trimming or transport; deterministic incidence; finite support and measurability; independence or
transport; the numerical consequence.

> **Gate 2.** Every visual inference has an id, an exact statement in English, and a named
> downstream consumer. Deleting the figure now loses nothing.

### Phase 3 — Sanity-check the edge cases in Lean

Try to break each statement before investing in a proof. Compile the definitions and statements
so far and test them at: scale `0` and `1`; width-one rectangles; empty side sets; coincident
corners; touching inner and outer boundaries; reversed orientation; swapped endpoints; walks that
repeat vertices; paths running along the boundary.

Distinguish vertex, edge, and primal/dual crossing. Check whether "disjoint regions" really gives
disjoint edge-coordinate supports. Enumerate a very small finite configuration set when cheap.

`decide` on a finite model tests; it never proves the general claim. **One checked counterexample
is decisive** — record it, then weaken or reject the obligation. Add hypotheses only when the
source genuinely supplies them.

> **Gate 3.** Degenerate and small instances checked; counterexamples recorded as regression
> examples; surviving statements elaborate in Lean.

### Phase 4 — Look for existing API

Search Mathlib and this repository before naming anything new. Search by concept, by type
signature, and by neighbouring declarations — not only by the source's vocabulary.

Record what you find in **`docs/<target>/GEOMETRY_API.md`**: for each declaration, its exact Lean
statement and *how it is used geometrically* — what picture-level move it performs. This file is
the point of the phase; keep it current as later phases add new geometry.

Mark every name in your expansion either `verified existing` (you compiled it) or `proposed`.
Reuse architecture, not remembered names.

> **Gate 4.** `GEOMETRY_API.md` exists and every cited name is verified or explicitly proposed.

### Phase 5 — Find the simplest proof

Prove the specific thing you need. Do not develop a general theory first.

Take the first rung that discharges the downstream consequence:

1. **Coordinate normalization** — define the translation, rotation, reflection, or dual map; prove
   pointwise formulas, region membership, adjacency, and images of named sides.
2. **First-hit / last-exit trimming** — replace a loosely drawn or infinite path by a finite
   subwalk between explicit stopping vertices; prove the retained support.
3. **Finite reachability** — define "inside", "below", "left of" as reachability in a finite graph
   after deleting a separator. Its edge boundary is a concrete finite set. Preferred for any
   lowest or leftmost region.
4. **Local parity** — around a square cell, a vertex predicate changes 0, 2, or 4 times; use it
   for even degree at interior dual vertices and explicit odd boundary ports.
5. **Mod-two intersection** — with alternating boundary endpoints, a parity index along one path
   changes exactly at crossings; different endpoint parities force an intersection.
6. **Graph extraction** — finite components, cuts, cycle decomposition, walk normalization. If a
   closed walk suffices, do not prove a unique simple cycle exists.
7. **Weaken to what is actually consumed** — replace "there is a unique surrounding cycle" by
   "every inner-to-outer path meets one of these four crossings"; replace an exact formula by the
   bound the theorem uses.

**General topology is the last resort.** Do not reach for a discrete Jordan curve theorem, winding
number library, or embedding theorem until the rungs above are exhausted. In practice the finite
substitute has always existed: where a Jordan argument is tempting, the missing ingredient is
usually that the interface graph *forgets the local non-crossing pairing at degree-four cells* —
encode that pairing explicitly instead.

If a general statement really would settle it, **write it down as prose and record it in
`DESIGN_DECISIONS.md`** as a candidate for later development. Do not axiomatize it to make the
current proof compile. Never axiomatize the final probability inequality because its picture is
hard; at most isolate the smallest true deterministic incidence lemma, and only with the owner's
explicit approval.

> **Gate 5.** The chosen certificate is the smallest that works, and the document says why each
> earlier rung was insufficient.

### Phase 6 — Deterministic geometry before any probability

Prove the geometry in a file that does not import probability. Finite regions, side finsets,
coordinate maps, trimming and concatenation constructions, reachability regions, frontier edge
sets, incidence and separation lemmas.

Only once the deterministic inclusion compiles, add: the event as existence of a finite witness;
its finite support; measurability; exact disjointness of supports; symmetry or measure transport;
independence or FKG; the finite summation; the numerical bound.

A compiling probability shell wrapped around an unproved geometric inclusion is not progress.

> **Gate 6.** Deterministic layer compiles with no probability import and no shortcuts. Then the
> event and probability layers compile on top of it.

### Phase 7 — When it does not work

Failure is expected. Iterate rather than patching Lean around a broken idea.

1. **Locate the failure in the prose.** Take the failing Lean goal and find which sentence of the
   Phase 1–2 expansion it corresponds to. There is always one; if there is not, the expansion is
   incomplete, and that is the bug.
2. **Decide which is wrong** — the mathematics, or the encoding. If Lean rejects a step the source
   asserts, look for a hidden hypothesis the picture supplied silently.
3. **Repair the prose first**, using the Lean feedback. Update `PROOF_EXPANSION.md`, then re-enter
   at the earliest phase the repair affects — usually Phase 2 or 3, not Phase 6.
4. **Record the failed attempt** in `DESIGN_DECISIONS.md`, with the reason it failed. A rejected
   approach is a result; the next agent must not spend the same hours rediscovering it.
5. If the obstruction is a genuinely missing global theorem, say so precisely and stop. A
   precisely identified blocker is a legitimate outcome. Generating more figure commentary is not.

> **Gate 7.** Every failure is traced to a prose step; the prose is repaired; the attempt and its
> reason are recorded.

## Artifacts

Three files per target, under `docs/<target>/`.

**`PROOF_EXPANSION.md`** — the single source of truth for the natural-language proof.
Source evidence and figure transcription; the obligation ledger (id, hypotheses, exact
conclusion, downstream use, status); the falsification record; the full expanded prose proof, one
section per obligation; and the **mapping from each prose step to its Lean declaration**. Phase 7
updates this file — it must never fall behind the code. Have an independent agent verify the
prose ↔ Lean mapping when the proof is substantial.

**`GEOMETRY_API.md`** — Lean statements plus what each does geometrically. Started in Phase 4,
extended whenever new reusable geometry is created. Prefer general, reusable statements over
one-off lemmas *when the general form costs nothing extra*; Phase 5 still says prove the specific
thing first.

**`DESIGN_DECISIONS.md`** — every choice made in turning the picture into Lean, and why:
encodings picked and rejected, divergences from the source picture, counterexamples to tempting
stronger formulations, approaches that failed and the reason, and general statements worth
developing later.

## Review

For any substantial proof-bearing figure, get a fresh reviewer that did not produce the expansion.
Give it the source pages, the theorem context, and the expansion — but do **not** ask it to
confirm the intended proof. Its first pass is read-only and must be preserved before any repair.

A figure review is not an ordinary code review. It must:

- restate each visual claim without geometric hand-waving;
- check the transcription against the rendered page — coordinates, boundary inclusivity,
  orientation, primal/dual, the smallest legal scale;
- expose hidden simplicity, finiteness, and nondegeneracy hypotheses the picture supplied
  silently;
- attempt falsification on the smallest legal instances, and report explicit counterexample
  witnesses;
- check that each obligation is the *weakest* statement its downstream step needs;
- verify the prose ↔ Lean mapping declaration by declaration;
- separate "this is false" from "this is unproved" — the two demand different repairs;
- report before proposing fixes.

If no independent agent is available, record `independent review unavailable`. A producer's second
reading is not independent.

## Release

A proof-bearing figure is discharged when every gate above has passed and:

- every visual obligation has a proved Lean declaration or an explicitly accepted disposition;
- the source theorem is recovered by a compiling application;
- no deterministic geometry is hidden inside a probability axiom;
- discovered counterexamples have regression coverage;
- the file and root builds pass, with `sorry`/`admit` scans and `#print axioms` recording the
  intended result exactly;
- `PROOF_EXPANSION.md`, `GEOMETRY_API.md`, and `DESIGN_DECISIONS.md` match the code.

Report the axiom closure exactly as Lean prints it. Do not describe a theorem as proved when only
the probability algebra compiles, when the decisive inclusion is an axiom or `sorry`, or when the
picture was silently strengthened.
