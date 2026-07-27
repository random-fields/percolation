# Source Audit Prompt — Autoformalization Suitability (v2)

You are evaluating a mathematical source text (textbook chapter, monograph section, or paper) to determine whether it is suitable for **autonomous Lean 4 formalization** — that is, formalization driven primarily by an LLM agent with minimal human intervention. Your output is a structured scorecard that a formalization team can use to decide whether to proceed and how much human oversight to plan for.

The source to evaluate is given at the bottom of this prompt, either as a filename/path (read the file) or as pasted text. Read it before proceeding.

First settle the **unit of work** (criterion 0 below). Then evaluate each unit against the nine criteria. For each criterion, run the probe question against the text, then assign a rating of **Green**, **Yellow**, or **Red** with a one-sentence justification.

> **What changed in v2.** The Mathlib-facing criteria (2, 5, 6) were unreliable in v1 because the prompt let the agent *reason from memory* and merely tag claims `(unverified)`. v2 replaces that with a mandatory **Mathlib grounding protocol** (below): query a pinned index, never recall; verify every candidate by tool; *unverified can never be Green*; guard the symmetric failure (a single search "no hit" ≠ absent — confirm with ≥2 query forms); score existence on three axes (exists / right generality / same statement); and search **our repos**, not just Mathlib, since the real frontier is Mathlib ∪ our libraries. Also added: a worked grounding-table row, an effort/size axis to the verdict, and an evidence table in the output.

Three rules for a trustworthy audit:
- **Cite specifics.** When a criterion turns on particular lemmas, definitions, or passages, name them by section/page number so a human can check your call.
- **Ground, don't recall.** For every Mathlib (or our-repo) claim, follow the **Mathlib grounding protocol**. A claim that was not confirmed by a tool is `(unverified)` and is **capped at Yellow** (Red if load-bearing) — it may never be scored Green. Do not present a reasoned guess as a checked fact.
- **State your environment up front.** Say which Mathlib **commit/toolchain** you are grounding against (the project pin) and which tools you actually have available this run (live Lean env? `leansearch`/`loogle`/`leanfinder`? a declaration index? the our-repo catalog?). Every Mathlib claim is relative to that pin.

---

## Criterion 0 — Unit of work (do this first)

Before scoring anything, decide *what* to score. A single source can be suitable in one part and unsuitable in another; scoring a heterogeneous text as one blob produces a misleading average.

**Probe (cheap pre-pass):** From the table of contents / section structure and the foundational dependencies of each major part, ask: does this source rest on one foundation, or several? If different strata rest on different foundations (e.g., one Mathlib-proximate, one Mathlib-absent) or use sharply different proof styles, **split the source into segments and score each segment separately** through criteria 1–9.

**This segmentation is provisional.** The cheap pre-pass sees outlines, not proofs — and the dangerous case (a green-looking stratum that secretly rests on a red one) lives inside the proofs, not the table of contents. So treat the initial split as a hypothesis to be confirmed or revised by the scoring, not a final answer. Re-segmentation happens in the closing step (see Output format).

**Output:** the chosen unit(s) of work; if split, the fault line you cut along and why; and a flag that the split is provisional pending the scores.

---

## Mathlib grounding protocol (mandatory for criteria 2, 5, 6)

This protocol replaces "reason from your knowledge of Mathlib." Apply it to every object/lemma you assess for Mathlib (or our-repo) availability.

1. **Pin the target.** State the exact Mathlib commit/toolchain you ground against (the project pin). Every claim is relative to it — never "Mathlib in general." Names drift across versions; an answer without a pin is not an answer.

2. **Search, don't recall.** Your memory may only *propose candidates*; it can never confirm one. Confirmation comes only from a live index, in rough order of preference:
   - **declaration index of the pinned Mathlib** — grep a dumped list of every decl name + signature (the ground truth; unhallucinatable, version-exact);
   - **`leansearch`** (natural-language), **`loogle`** (type/name pattern), **`lean_leanfinder`** (goal-aware semantic);
   - **a live pinned Lean env** for `#check <name>` / `example : <goal> := by exact?`.

3. **Verify every candidate — and treat absence with care.** A name counts as "present" only if a tool confirms it: it elaborates under `#check`, **or** appears verbatim in the declaration index, **or** an `exact?`/`loogle` query returns it. Record the *query, the tool, and the exact declaration name + commit*. **The two failure modes are symmetric:** memory gives *false positives* (hallucinated names — step 2 guards those), and search gives *false negatives* (a real lemma whose phrasing the query missed). So a single "no hit" is **weak evidence of absence** — before scoring a prerequisite missing, try at least two query forms (a natural-language `leansearch` **and** a `loogle` type/name pattern), and prefer the declaration-index grep, which cannot miss on a known name. Only then record "no hit (≥2 queries)."

4. **Unverified ⇒ never Green.** If you could not run a confirming tool for a claim, mark it `(unverified)`; it is capped at **Yellow**, or **Red** if the result is load-bearing for the verdict. This rule is the whole point of v2 — honor it.

5. **Score existence on three axes, not yes/no.** For each prerequisite report:
   - **(a) exists?** is there a declaration at all;
   - **(b) right generality?** at the needed typeclass / hypothesis setting, or only a special/over-general case needing instantiation;
   - **(c) same statement?** definitionally equal / directly usable, or needs a proved bridge (equivalence) first.
   Green only if (a)+(b)+(c); Yellow for a standard instantiation or bridge; Red for absent or nontrivial reconciliation. For **definitions** (criteria 2, 6) axis **(c)** — does the source's definition structurally / defeq-match Mathlib's — is the crux and the costliest to get wrong; for **lemmas** (criterion 5) axes **(a)+(b)** — availability at the right generality — dominate.

6. **Search our repos too.** The frontier is **Mathlib ∪ our libraries**. If an object is not in Mathlib, query the our-repo declaration index (e.g. `catalogs/ALL_LEMMAS.tsv` + the layer libraries) before scoring Red. "Not in Mathlib but already in `gaussian-field`/`markov-semigroups`" is a distinct, better verdict — report *where* it lives.

7. **Emit the evidence.** Produce the grounding table (see Output format): one row per prerequisite — object · query · tool · result (exact name + commit, or "no hit") · axes (a/b/c) · location (Mathlib / our-repo / nowhere). The criterion rating must follow from this table, not from prose.

**Worked row (format + judgment anchor).**
```
object : Haar measure on a compact group
query  : leansearch "Haar measure compact group"  +  loogle "IsHaarMeasure"
tool   : leansearch + loogle + #check
result : MeasureTheory.Measure.haar  (mathlib@<pin>)
axes   : a ✓ exists · b ✓ compact-group instance available · c ~ uniqueness needs a `haar_unique`-style bridge
location: Mathlib
```
The `c ~` makes a uniqueness-dependent step **Yellow**, not Green — exactly the distinction a binary "in Mathlib?" would have lost.

> If you have **no** grounding tool this run, say so explicitly at the top; then criteria 2, 5, 6 are all `(unverified)` and the unit cannot score better than **NEEDS SCAFFOLDING** on Mathlib grounds. Do not paper over a missing environment with recalled names.

---

## Criteria and probes (apply to each unit of work)

**1. Explicit proofs**
Select five non-trivial lemmas from the middle third of the text. For each: is the proof complete in the text, or does it require consulting an external source to fill a gap? *(This is about the source's self-containedness; criterion 4 covers explicit "left to reader" gaps, and 5 covers whether the prerequisites exist in Mathlib.)*
- Green: all five are self-contained
- Yellow: 1–2 require consulting a named, accessible secondary source
- Red: key steps are missing, attributed to papers, or described as "standard"

**2. Unusual conventions** *(run the Mathlib grounding protocol)*
Identify the three most central definitions in the text. Ground each against the pinned Mathlib (protocol steps 2–3, axes in step 5). Are they the same definition, or a structurally different formulation?
- Green: definitions match the pinned Mathlib (or our-repos), or diverge only cosmetically (flagged by the author) — **tool-confirmed**
- Yellow: one definition differs but equivalence is standard and provable (a step-(c) bridge), or the match is `(unverified)`
- Red: one or more central definitions are structurally different in ways that require non-trivial reconciliation

**3. Logical structure**
Draw the dependency graph for the final three theorems. Are all edges (which earlier result each step depends on) explicit in the text?
- Green: clean DAG, all dependencies cited, no cycles
- Yellow: mostly explicit, some dependencies implicit or inferred
- Red: structure is thematic rather than logical; dependencies must be reconstructed by an expert

**4. "Left to reader" gaps**
Search the text for "left to the reader," "exercise," "one can show," "it is easy to see," and similar phrases. For each occurrence on the main proof path: is the gap provable from Mathlib (ground it via the protocol), or does it require original work?
- Green: no gaps on the main proof path, or all gaps are Mathlib-proximate (tool-confirmed)
- Yellow: 1–2 gaps on the main path, but straightforward
- Red: one or more key steps are exercises or omitted proofs that are not obviously Mathlib-proximate

**5. Mathlib proximity** *(run the Mathlib grounding protocol — this is the criterion it matters most for)*
For five representative lemmas (on the main proof path, spanning the unit's foundational strata — not the easiest five), ground their prerequisites against the pinned Mathlib (and our repos). Use `leansearch`/`loogle`/`leanfinder` + the declaration index for the candidate→verify loop; reserve `exact?`/`apply?` for the deeper spot-check where you can actually *state the goal* as a Lean `example` (note: those tactics need a goal, so they are not the audit-stage default). Are the prerequisites available, and **in usable form** (axes a/b/c)?
- Green: direct, tool-confirmed matches for most prerequisites (axes a+b+c)
- Yellow: prerequisites exist as special cases / more general results requiring instantiation (axis b or c gap), or matches are `(unverified)`
- Red: central objects or key lemmas are in neither Mathlib nor our repos; substantial foundational work needed first

**6. Definition uniqueness** *(run the Mathlib grounding protocol)*
Are the central mathematical objects defined in one canonical way across the literature, or do multiple competing formulations exist — and which (if any) does the pinned Mathlib use? Confirm Mathlib's formulation by tool.
- Green: one canonical definition, tool-confirmed to match the pinned Mathlib
- Yellow: two equivalent formulations; one is Mathlib's; equivalence is standard (a provable bridge)
- Red: multiple competing formulations; the source uses one without explaining why; alignment with Mathlib is unclear or `(unverified)`

**7. Constructive content**
Scan the proof for appeals to choice, excluded middle, or existence-without-witness. Are these handled by Lean's `Classical` namespace in standard ways, or do they require structural workarounds?
- Green: constructive or uses standard classical arguments Lean handles cleanly
- Yellow: heavy classical use but within normal Lean/Mathlib practice
- Red: fundamentally non-constructive arguments that would require replacing the proof strategy in Lean

**8. Figure-dependent arguments**
Search for "Figure," "diagram," "see below," "as illustrated," and commutative diagrams. For each occurrence on the main proof path: is the logical content also stated in words, or does the figure carry non-redundant information?
- Green: figures are illustrative only; all logical content is stated in the text
- Yellow: some auxiliary facts conveyed by figure, but standard and Mathlib-proximate
- Red: one or more key proof steps are conveyed by figure with no textual substitute

**9. Tower structure**
List the main theorems in order. For each, identify which earlier results it depends on. Is this list explicit in the text?
- Green: proof decomposes into explicit strata; each layer is a self-contained formalization target
- Yellow: phases exist but interfaces are fuzzy
- Red: proof is holistic; no natural decomposition into independent subtasks

---

## Output format

Return one scorecard **per unit of work**. If criterion 0 kept the source whole, emit a single scorecard; if it split the source, emit one per segment. Each scorecard includes the **grounding evidence table** that backs criteria 2/5/6.

```
SOURCE: [filename — title, author]
ENVIRONMENT: Mathlib pin [commit/toolchain] · tools available this run [decl index? leansearch/loogle/leanfinder? live Lean env? our-repo catalog?]

UNIT OF WORK: [whole source, OR this segment's name + section range]
  (if split) FAULT LINE: [where you cut and why] · split is PROVISIONAL pending scores
  SIZE/EFFORT: [pages or # main results in this unit; coarse effort estimate]

GROUNDING EVIDENCE (criteria 2/5/6):
  object/lemma | query | tool | result (exact name + commit, or "no hit") | axes a/b/c | location (Mathlib / our-repo / nowhere)
  ...

SCORECARD:
1. Explicit proofs        [Green/Yellow/Red] — [one sentence]
2. Unusual conventions    [Green/Yellow/Red] — [one sentence, citing the grounding rows]
3. Logical structure      [Green/Yellow/Red] — [one sentence]
4. Left-to-reader gaps    [Green/Yellow/Red] — [one sentence]
5. Mathlib proximity      [Green/Yellow/Red] — [one sentence, citing the grounding rows]
6. Definition uniqueness  [Green/Yellow/Red] — [one sentence, citing the grounding rows]
7. Constructive content   [Green/Yellow/Red] — [one sentence]
8. Figure-dependent args  [Green/Yellow/Red] — [one sentence]
9. Tower structure        [Green/Yellow/Red] — [one sentence]

VERDICT: [one of the four below] · [effort note: ~N human interventions expected, scaled by SIZE/EFFORT]
  PROCEED            — all green; autonomous agent, ~30 human interventions expected (calibrated, not derived — adjust to unit size)
  PROCEED/CHECKPOINTS — mostly green with 1–2 yellow; tighter soundness monitoring
  NEEDS SCAFFOLDING  — multiple yellow, OR Mathlib grounding was (unverified) for lack of tools; human must define key type signatures / supply the env first
  DO NOT PROCEED     — any red on criteria 1, 2, 6, or 8; find a better secondary source

KEY RISKS: [bullet list of the 1–3 most significant issues found, if any]
```

*Verdict-gate note:* the four "hard-red" criteria are 1 (missing proofs), 2 and 6 (definitions that won't align with Mathlib — the most expensive thing to discover late), and 8 (logical content trapped in figures). A red there means the source itself is the problem; find a better one. The thresholds (`~30`, the hard-red set) are empirically calibrated (see the case studies in this folder), not derived — adjust as data accumulates.

### Closing step — re-segmentation check (always run)

After scoring, re-examine the unit boundaries in light of the scores:

- **Did a segment's scoring reveal a dependency on a lower-rated segment?** The classic case (criterion 9): a green-looking algebraic core whose proofs actually rest on a red foundational stratum. The table of contents hid this; the proofs (and the grounding table) exposed it.
- If so, **re-cut and re-score the affected segment** — either move the boundary, or note that the green segment is only green *conditional on first building* the red one (and is otherwise NEEDS SCAFFOLDING / DO NOT PROCEED on its own).
- This loop is bounded: it only re-touches segments whose boundary moved. State explicitly whether the provisional split survived the scoring or was revised, and give the final unit(s) of work.

---

**SOURCE:** [append filename/path, or paste source text here]
