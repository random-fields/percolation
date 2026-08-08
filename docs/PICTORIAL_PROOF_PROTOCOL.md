# Pictorial proof protocol

Use this whenever a proof leans on a figure or on visual language — "clearly surrounds", "must
cross", "as in the picture", "leftmost", "lowest", "inside", "outside", or any inference that
appeals to how something is drawn.

> A picture may identify a conjectured certificate. It is never itself a Lean proof object.

**What this protocol is for.** It is a correctness gate, not a proving accelerator. It earns its
cost by catching a wrong transcription before you build on it, and by naming the exact obligation
that is missing. Once the model survives falsification, stop expanding documents and go prove
Lean. Expanding this protocol's artifacts is not progress on the mathematics.

**Domain playbooks.** This file is subject-independent. A domain playbook adds the conventions,
degenerate instances, and certificate techniques of a specific area. Current playbooks:
[`PERCOLATION_STRATEGIES.md`](PERCOLATION_STRATEGIES.md) for percolation and statistical-physics
arguments. When a playbook applies, use it together with this file at the points marked below.

## Objective

The goal is always to formalize the stated theorem — not to reproduce the source's pictured
proof. If a simpler formalization exists that does not rely on the figure, take it and record
the divergence in `DESIGN_DECISIONS.md`. Consequences:

- A missing, illegible, or ambiguous figure blocks only when the ambiguity affects the theorem
  statement or a definition, or when no independently justified replacement for the pictured
  step exists.
- Convention ambiguity where all readings are provably equivalent blocks nothing: pick one
  normalization and record it.

## Natural language versus Lean

These are two distinct artifacts and must not be blurred.

| | Natural language | Lean |
|---|---|---|
| Lives in | `docs/<target>/PROOF_EXPANSION.md` | the Lean sources |
| Says | what is true and why, in full prose | the machine-checked statement |
| Quantifiers | may be implicit | always explicit |
| "Obvious" allowed | never, but prose steps are permitted | nothing is implicit |
| Failure means | the mathematics is wrong or incomplete | the mathematics *or* the encoding is wrong |

Write the natural-language proof **first and completely**. A visual obligation you cannot state
in a paragraph of English you cannot state in Lean either.

## Phases

Each phase has one output and one gate. Prototyping ahead of an unresolved gate is allowed —
you may sketch downstream interfaces while a lemma is open. What is forbidden is claiming the
pictorial step complete, or building on it as if proved, while an applicable gate remains
unresolved.

### Phase 1 — Triage and extract the image

First decide whether the proof depends on the figure at all. If the prose is complete without
it, record why in one line and move on — the protocol ends here for that figure. If the proof
does depend on it, describe **in your own words** how the proof uses it: what the picture
supplies that the prose does not. The description must come from reading the source argument. A figure may supply several distinct inferences — describe each
separately; each gets its own obligation in Phase 2.

Then read the figure and write down what it actually says, before interpreting it.

Record: source id, edition, printed and PDF page, figure number, caption; the exact sentences
that invoke it; the hypotheses already in force; which features are defined by prose or legend;
which visual channels carry meaning (color, dash pattern, arrowheads, layering) and which are
decoration; and the precise later step that consumes the visual claim.

For a geometric figure also fix: ambient type; axes, origin, orientation, scale; the exact
region of every named object; named sides, corners, and subregions; inclusive vs exclusive
boundaries; whether paths may use boundary points or edges; every state convention the domain
distinguishes (the playbook lists them for its domain); every symmetry map and its fixed points;
every asserted disjointness; the smallest legal instance.

Do not assume something as a fact just because it appears so in the image. Never read off a drawing: equal lengths or angles; tangency, uniqueness, simplicity,
connectedness; disjointness of paths or supports; that a path stays inside a region; an exhaustive
case list; preservation of an event under a visual symmetry; which side of a boundary is closed. These need to be verified with proof.

OCR is a navigation aid only — verify symbols, inequalities, subscripts and endpoints against the
rendered page. If the image contradicts the prose, record the conflict and treat the statement as
ambiguous.

> **Gate 1.** Citation, the dependence decision, the description of how the proof uses the
> figure, conventions, and consuming step are recorded. If a figure is missing, illegible, or
> genuinely ambiguous, apply the Objective rules: block only where they require it, and never
> reconstruct the figure from memory or pick the reading that is easiest to prove.

### Phase 2 — Replace the image with a statement

Ask, for each visual inference:

> What is the **weakest** deterministic statement that makes the next non-visual line valid?

Work backwards from the downstream theorem, never forwards from the strongest claim the picture
suggests. Give each inference an id, explicit hypotheses, an exact conclusion, and at least one
identified downstream consumer. Keep them atomic — do not mix geometry, locality, transport and
arithmetic in one obligation. 

> **Gate 2.** Every visual inference has an id, an exact statement in English, and a named
> downstream consumer. Deleting the figure now loses nothing.

### Phase 3 — Sanity-check the edge cases in Lean

Try to break each statement before investing in a proof. Compile the definitions and statements
so far and test them at the degenerate and boundary instances of the domain: smallest legal
parameters, empty sets, coincident points, touching boundaries, reversed orientations, swapped
endpoints, witnesses that repeat vertices or run along a boundary. For tasks with specific playbooks, see the
standard instances for its domain; test those too.

Check that visually distinct notions are formally distinct — different kinds of crossing or
contact, region disjointness versus support disjointness. Enumerate a very small finite
configuration set when cheap.

`decide` on a finite model tests; it never proves the general claim. **One checked counterexample
is decisive** — record it, then weaken or reject the obligation. Add hypotheses only when the
source genuinely supplies them.

> **Gate 3.** Degenerate and small instances checked; counterexamples recorded as regression
> examples; surviving statements elaborate in Lean.

### Phase 4 — Look for existing API

Search Mathlib and this repository (see `GEOMETRY_API.md`) before naming anything new. Search by concept, by type
signature, and by neighbouring declarations — not only by the source's vocabulary.

Record what you find in **`docs/<target>/GEOMETRY_API.md`**: for each declaration, its exact Lean
statement and *how it is used geometrically* — what picture-level move it performs. This file is
the point of the phase; keep it current as later phases add new geometry.

Mark every name in your expansion either `verified existing` (you compiled it) or `proposed`.
Reuse architecture, not remembered names.

> **Gate 4.** `GEOMETRY_API.md` exists and every cited name is verified or explicitly proposed.

### Phase 5 — Find the simplest proof

Prove the specific thing you need. Do not develop a general theory first.

**A large abstract theory is the last resort.** Use the weakest abstraction native to the
theorem: do not reach for a global topological or analytic library until simpler strategies are
exhausted. In practice the elementary substitute has usually existed; the
playbook records where the temptation typically arises in its domain and what the missing
elementary ingredient was.

If a general statement really would settle it, **write it down as prose and record it in
`DESIGN_DECISIONS.md`** as a candidate for later development. Do not axiomatize it to make the
current proof compile. Never axiomatize the final target inequality because its picture is
hard; at most isolate the smallest true deterministic lemma, and only with the owner's
explicit approval.

> **Gate 5.** The chosen certificate is the smallest that works, and the document says why
> simpler strategies were insufficient.

### Phase 6 — Deterministic core before downstream transport

Prove the deterministic content in a layer that does not import the downstream machinery —
probability, measure theory, or heavy analysis. Explicit objects, constructions, incidence and
separation lemmas first. For any statement about the geometry, record it in `GEOMETRY_API.md` with a natural language version. Formalize general, reusable geometric statements. 

Only once the deterministic statement compiles, add the transport layer the domain needs —
events, supports, measurability, symmetry transport, independence, summation, or their analogues
(the playbook details the stack for its domain).

A compiling downstream shell wrapped around an unproved deterministic core is not progress.

> **Gate 6.** Deterministic layer compiles with no downstream import and no shortcuts; no
> deterministic content is hidden inside a downstream-layer axiom. Then the transport layers
> compile on top of it.

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

Three files per target, under `docs/<target>/`, whenever the proof depends on a figure. A
figure the proof does not use needs only its one-line disposition from Phase 1.

**`PROOF_EXPANSION.md`** — the single source of truth for the natural-language proof.
Source evidence and figure transcription; the obligation ledger (id, hypotheses, exact
conclusion, downstream consumers, status); the falsification record; the full expanded prose
proof, one section per obligation; and the **mapping from each prose step to its Lean
declaration**. Phase 7 updates this file — it must never fall behind the code. Have an
independent agent verify the prose ↔ Lean mapping when the proof is substantial.

**`GEOMETRY_API.md`** — Lean statements plus what each does geometrically. Started in Phase 4,
extended whenever new reusable geometry is created. Prefer general, reusable statements over
one-off lemmas *when the general form costs nothing extra*; Phase 5 still says prove the specific
thing first.

**`DESIGN_DECISIONS.md`** — every choice made in turning the picture into Lean, and why:
encodings picked and rejected, divergences from the source picture, counterexamples to tempting
stronger formulations, approaches that failed and the reason, and general statements worth
developing later.

## Review

Every figure the proof depends on gets an independent review of the natural-language expansion
before formalization builds on it. The reviewer must not have produced the expansion. Give it
the source pages, the theorem context, and the expansion — but do **not** ask it to confirm the
intended proof. Its first pass is read-only and must be preserved before any repair.

A figure review is not an ordinary code review. It must:

- restate each visual claim without geometric hand-waving;
- check the transcription against the rendered page — coordinates, boundary inclusivity,
  orientation, state conventions, the smallest legal instance;
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

## Final audit

A target is complete when every applicable gate has passed and: every visual obligation has a
proved Lean declaration or an explicitly accepted disposition; the stated theorem is recovered
by a compiling application; the file and root builds pass; `sorry`/`admit` scans are clean;
`#print axioms` records the intended result, reported exactly as Lean prints it; and the
artifacts match the code. Do not describe a theorem as proved when only the downstream algebra
compiles, when a decisive inclusion is an axiom or `sorry`, or when the picture was silently
strengthened.
