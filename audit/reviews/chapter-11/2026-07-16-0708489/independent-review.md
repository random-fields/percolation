I now have enough to author the independent report. Note two hard environment constraints I must disclose: **Bash and the Lean MCP execution tools are denied in this session**, so I could not run `lake build`, `#print axioms`, or Comparator myself — the logical-trust gate is therefore reproduced only by static inspection, not mechanically. Here is the complete first-pass report.

---

# Independent Adversarial Review — Grimmett *Percolation* (2nd ed.), Chapter 11
## First-pass, read-only, frozen commit `ff70a71`

```text
review id:            chapter-11-independent-first-pass
scope:                Grimmett, Percolation, 2nd ed., Ch. 11 "Bond Percolation in Two Dimensions"
source id and edition: grimmett-percolation-1999; kg/textbooks/Grimmett-Percolation-2ed-1999.pdf
source pages:         printed 282–332 (PDF offset +13; printed p = PDF p − 13)
git commit:           ff70a71771d9ae0a19c614f8ec2d190e4dc36284 ("feat: formalize Grimmett Chapter 11")
worktree:             clean (git status --short empty); HEAD == ff70a71, so working tree == frozen commit
reviewer:             independent Claude agent (claude-opus-4-8), 2026-07-16, read-only first pass
review mode:          internal, STATIC ONLY (see limitations)
prompt basis:         AUTOMATED_REVIEW.md §10 template; instructed to falsify, not confirm
```

### Commands actually run / attempted

| Command | Result |
|---|---|
| `git ls-tree -r ff70a71`, `git show ff70a71:<path>` | ran; used to read frozen source (via harness Bash before it was locked, then via clean worktree Read/Grep) |
| Read / Grep / Glob over the clean worktree (== frozen commit) | ran; primary evidence for Lean types and definitions |
| PDF read of Chapter 11 (verbatim source transcription) | ran (delegated read; offset verified printed 282 = PDF 295) |
| `lake build` | **NOT RUN — Bash denied by harness (don't-ask mode).** |
| `#print axioms …` / `mcp lean_verify` on headline decls | **NOT RUN — Bash and Lean-MCP execution denied.** |
| Comparator (challenge/solution) | **NOT RUN — no Linux/landrun sandbox on macOS; also no chapter-11 comparator project exists.** |

**Limitation (material):** The authoritative gates of `AUTOMATED_REVIEW.md` §8/§9/§12 — transitive `#print axioms`, a green `lake build`, and Comparator — could not be independently reproduced in this environment. Per §11 those gates are therefore `INCONCLUSIVE` for me and, per protocol, must never be scored as `PASS`. Everything below marked "axiom set" is read from the **declarations and the audit script text**, not from a kernel run I performed.

---

## 1. Source-inventory completeness

I re-derived the named-result list from the source. The topic card's inventory covers every *named* Chapter-11 result I could locate: **11.2, 11.4, 11.11, 11.12, 11.13, 11.21, 11.22, 11.24, 11.25, 11.27, 11.55, 11.63, 11.70, 11.73, 11.75, 11.89, 11.93, 11.115, 11.116**, plus a grouped disposition of every numbered display 11.1–11.116. I did **not** independently re-enumerate all ~116 numbered displays against the OCR (limitation P2), but spot checks of the grouped table (11.5–11.10 Euler proof, 11.14–11.20 square-root trick, 11.28–11.32 tube displays, 11.71–11.88 RSW, 11.90–11.98 power laws, 11.114 definitions) are consistent with the source. **Inventory: adequate.**

One nuance the card handles correctly: **11.115/11.116 use Grimmett's rooted θ (origin-cluster) formulation**, and Grimmett himself notes the "critical surface = line" phrasing is only informal. The Lean `inhomogeneousSquareTheta`/`inhomogeneousTriangularTheta` are origin-cluster probabilities — faithful to the rooted source, **not** the (stronger, unrooted) "∃ infinite cluster" 0–1 event.

---

## 2. Disposition classification (proof / proof-modulo / direct external axiom / wrapper)

Using the four categories requested:

| Source | Lean declaration | Category | Evidence |
|---|---|---|---|
| 11.2 | `existsUnique_boundaryCircuitCrossedEdges` | **direct external axiom** | `Planar/External.lean` `axiom`; Kesten (1982) p.386 |
| 11.4 | `openClustersPerVertex_square_duality` | **direct external axiom** | `Chapter11External.lean` `axiom`; whole theorem, cites Kesten p.244 |
| **11.11** | `cubicCriticalProbability_two_eq_half` | **proof modulo external axioms** | `SquareThresholdExact.lean:110` real proof `le_antisymm …` |
| **11.12** | `theta_two_half_eq_zero` | **proof modulo external axioms** | `SquareThresholdExact.lean:89` real proof via independent barriers |
| **11.21** | `bernoulliBondMeasure_real_grimmettRectangleCrossingEvent_half` | **proof modulo external axioms** | `SquareThreshold.lean:128` real proof (self-dual trace count) |
| 11.22 (literal) | `maxEdgeDisjointGrimmettRectangleCrossings_probability_le_exp` | **direct external axiom** | `Chapter11External.lean` `axiom` |
| 11.22 (centered) | `maxEdgeDisjointSquareRectangleCrossings_probability_le_exp` | **proof modulo external axioms** | `SupercriticalCrossings.lean:423`; **different rectangle** |
| 11.24 | `finiteCorrelationLength_eq_half_correlationLength_complement` | **direct external axiom** | `Chapter11External.lean` `axiom` |
| 11.25 | `finiteClusterSizeProbability_le_exp_neg_sqrt_of_supercritical` | **direct external axiom** | `axiom` |
| **11.27** | `tubeConnectivityDecayRate_properties` | **proof** (claimed standard-axiom-only) | `TubeDecay.lean:683` assembles six real lemmas |
| 11.55 | `logarithmicProfileRegion_criticalProbability` | **direct external axiom** | `axiom` |
| 11.63 | `clusterFunctionalSum_centralLimitTheorem` | **direct external axiom** (book states w/o proof) | `axiom` + added measurability |
| **11.70** | `rswAnnulusOpenCircuitProbability_ge` | **proof modulo external axioms** | `RSWNumeric.lean:74` real proof from gluing |
| 11.73 | `rswThreeHalvesCrossingProbability_ge` | **direct external axiom** | `External.lean` `axiom`; Russo (1981) |
| **11.75** | `rsw_gluing_inequalities` | **proof modulo external axioms** | `RSWGluing.lean:169` from 3 subset axioms |
| 11.89 | `squareCritical_powerLaw_bounds` | **direct external axiom** | `axiom` |
| 11.93 | `squareNearCritical_powerLaw_bounds` | **direct external axiom** | `axiom` |
| **11.115** | `inhomogeneousSquare_criticalSurface` | **wrapper over two direct external axioms** | `Inhomogeneous.lean` |
| **11.116** | `inhomogeneousTriangular_criticalSurface` | **wrapper over two direct external axioms** | `Inhomogeneous.lean` |

**Genuinely proved (modulo the isolated external topology primitives): 11.11, 11.12, 11.21, 11.27, 11.70, 11.75, and the centered 11.22.** Everything else is a whole-theorem axiom or a wrapper over such axioms.

---

## 3. Statement-fidelity spot audit (what the axioms/theorems actually say)

I verified the following against the verbatim source (quantifiers, endpoints, constants, direction, rooting):

- **11.21 / literal 11.22 rectangle** — `grimmettRectangleVertices n = Icc(0,n+1) × Icc(0,n)` (`SquareCritical.lean:27`) is **exactly** Grimmett's `[0,n+1]×[0,n]`. Crossing event = left↦right connection inside the rectangle's edges. `maxEdgeDisjointGrimmettRectangleCrossings` = `Nat.findGreatest` of edge-disjoint crossings — faithful to `M_{n+1}`. Constants `β,γ>0`, `∀ n ≥ 1`, `p>1/2`, bound `≤ exp(-γ n)`: **faithful.**
- **Centered 11.22 divergence** — the *proved* theorem uses `maxEdgeDisjointSquareRectangleCrossings (n+1) n`, i.e. a **different, taller** rectangle (topic card: `[0,n+1]×[-n,n]`). So the *literal* source rectangle is only available as an **axiom**; the proved theorem is a documented divergence, not the source instance.
- **11.4** — `κ(p)=κ(1−p)+1−2p`: Lean `openClustersPerVertex 2 p = openClustersPerVertex 2 (σ p) + 1 - 2*(p:ℝ)`. **Faithful.**
- **11.11/11.12** — `cubicCriticalProbability 2 = 1/2` in ℝ (exact equality); `theta 2 squareHalfDensity = 0` (rooted). **Faithful.**
- **11.70/11.71** — `r^12·(1−√(1−r))^48 ≤ P(O(l))`, `r = rswSquareCrossingProbability`; `rswAnnulusOpenCircuitEvent` is an open cycle in `l < d_∞(0,·) ≤ 3l` with origin at odd face parity = annulus `B(3l)\B(l)`. **Faithful.** (Note: the proved theorem carries `hl : 1 ≤ l`; source (11.72) is stated `∀ l ≥ 1`.)
- **11.75** — the three FKG gluing inequalities (11.76)–(11.78) with exponents 2, 2, 4 and rectangles `LR(2l,l)`, `LR(3l,l)`, `O(l)`: **faithful** (matches `rswRectangleCrossingProbability p 2 l`, `… 3 l`, and `^4`).
- **11.27** — production **generalizes source `k ≥ 1` to `k : ℕ` (includes `k=0`)** and explicitly adds `Antitone`. `squareTube k = {x | |x₂| ≤ k}` matches `T_k`. The conjunction (limit exists, `≤ exp(−nφ_k)`, `0<φ_k`, `φ_k ≤ −log p`, antitone, `→ axisrate`) matches (11.28)–(11.32). Source's `φ_k < ∞` is automatic (ℝ-valued). **Faithful generalization**, but the source `k≥1` instance is only recoverable, not stated (my Challenge tests this — §7).
- **11.89** — lower prefactor `½·n^{−1/2}`, upper `A n^{−a}`, `∀ n≥1`, `boxRadiusTail = P(0↔∂B(n))`, `clusterSizeAtLeast = P(|C|≥n)` (`{n ≤ |C|}`), `Integrable(|C|^{a₃})`: **faithful.**
- **11.93** — (11.94)/(11.95)/(11.96) with the sharp `−1/4` lower exponent on `χ^f`, strict `p≷1/2`: **faithful.**
- **11.115/11.116** — hypotheses `p_h,p_v(,p_d) < 1` (all strict), critical polynomials `p_h+p_v` and `p_h+p_v+p_d−p_h p_v p_d`, θ=0 on `≤1` (non-strict, so the critical line itself gives θ=0) and θ>0 on `>1`. Wrappers expose exactly the two source implications. `triangularGraph` = square + NE diagonal. **Faithful.**
- **11.63** — all five source hypotheses present; **one hypothesis added** (`hfMeasurable`), which is mathematically implicit but formally necessary. Documented specialization; no source case lost.

**No statement-level counterexample found.** One conclusion is silently weakened: **11.24 drops the source's `0 < ξ(p) < ∞`** clause (only the equality `ξᶠ(p) = ½ ξ(1−p)` is asserted). Because it is an axiom, dropping a conclusion is safe (weaker), so this is P3, not a soundness issue.

---

## 4. Axiom-policy audit (user policy: *only results depending on references outside Grimmett may be axioms*)

Every axiom carries a citation. The distinction the producer's card blurs and that I flag:

**Group A — genuinely external (policy-compliant in letter and spirit):**
- `rswThreeHalvesCrossingProbability_ge` (11.73 ← Russo 1981) — external, **but** see F3: the axiom is the *whole probabilistic inequality*, not just the lowest-crossing stopping-set primitive.
- `existsUnique_boundaryCircuitCrossedEdges`, the two `grimmettRectangleDualTrace…`, and the three `rswGluing…Intersection_subset`, `rswAnnulusOpenCircuitProbability_le_half_barrier` (all ← Prop 11.2, Kesten 1982 p.386). These are **deterministic topological** inclusions/equivalences — the right granularity for an external primitive. Policy-compliant.
- `clusterFunctionalSum_centralLimitTheorem` (11.63 — Grimmett states without proof, cites CLT literature) — genuinely external.
- The four inhomogeneous axioms (11.115/11.116 — Grimmett states without proof, cites star–triangle literature) — genuinely external.

**Group B — whole book-proved theorems axiomatized (policy-compliant only under the *permissive* transitive reading):**
`openClustersPerVertex_square_duality` (11.4), `eventuallySurroundingOpenCircuit_probability_one` (11.13), `maxEdgeDisjointGrimmettRectangleCrossings_probability_le_exp` (11.22), `truncatedTwoPointConnectivity_logRate_tendsto` (11.23), `finiteCorrelationLength_eq_half_…` (11.24), `finiteClusterSizeProbability_le_exp_neg_sqrt_…` (11.25), `logarithmicProfileRegion_criticalProbability` (11.55), `squareCritical_powerLaw_bounds` (11.89), `squareNearCritical_powerLaw_bounds` (11.93).

For each of these, **Grimmett proves the theorem inside the book**; only a sub-step (Prop 11.2, or the Kesten p.244 face/component correspondence) is external. The producer axiomatizes the *entire conclusion*. This is within the *letter* of "depends on an external reference" but not its *spirit* (AGENTS.md: "Never introduce a convenient stronger statement just to unblock a proof"). The effect is that the chapter is largely an **axiomatic interface**, and `#print axioms` cannot distinguish "proved modulo Kesten's topology" from "assumed outright." The producer's card **does disclose** this ("external axiom" status, "complete as an autoformalized interface … not assumption-free") — the disclosure is honest, but the word **"complete"** overstates: the majority of Chapter 11's headline theorems are not formalized proofs.

---

## 5. Adversarial / consistency probes on the axioms

Because these are `axiom`s, a false instance would make the environment inconsistent (P0). I probed degenerate indices, which I could not compile:

- `grimmettRectangleDualTraceEquiv (n : ℕ)` and `card_grimmettRectangleDualTraceEquiv_apply (n)` are stated **for all `n`, including `n=0`**. A bijection `{crossing traces} ≃ {noncrossing traces}` is *inconsistent* if at some `n` one side is empty and the other is not. Hand-analysis of `n=0` (rectangle `[0,1]×[0,0]`, single horizontal edge) gives one crossing trace and one noncrossing trace, so `n=0` is *likely* consistent — but I could not machine-check it, and larger `n` rely on the very self-duality being assumed. **INCONCLUSIVE, flagged.**
- `rswThreeHalvesCrossingProbability_ge (p) (l)` has **no `1 ≤ l` guard** (unlike the gluing axioms). At `l=0` the bound `(1−√(1−r))^3 ≤ P(LR(³⁄₂·0,0))` on a degenerate rectangle is unverified. **INCONCLUSIVE, flagged.**

I found **no proved counterexample** and **no proved inconsistency**; these are open *risks*, not defects. They matter more than usual precisely because the statements are axioms.

---

## 6. Findings (by severity)

**F1 — P1 — Mandatory §4 review artifacts do not exist for Chapter 11.**
`audit/reviews/chapter-11/**` is **absent** (Glob: no files). There is no `MANIFEST.md`, `correspondence.md` (with `#check` types), `cases/`, `counterexamples/`, `comparator/Challenge.lean`+`Solution.lean`+`config.json`, `AxiomAudit.lean` transitive results, `independent-review.md`, or `SUMMARY.md`. Only a topic card and a vetting card exist. Per §12 the batch **cannot be called "reviewed and faithful."** Disposition: this report + a created run directory are prerequisites to any completion claim.

**F2 — P1 — Logical-trust gate not reproduced; "proved modulo external topology" is unverified here.**
`lake build`, `#print axioms`, and Comparator were all denied in this session. `Percolation/Tests/Chapter11AxiomAudit.lean` contains the *right* `#print axioms` commands, but a script that lists commands is not a passing gate. The transitive-axiom claims (incl. "the exact threshold contains only the named Kesten/Russo axioms and no theorem-specific axiom") are **INCONCLUSIVE** pending a kernel run on a clean Linux/CI. Recommendation: run the audit file with `lake env lean` and archive the output verbatim.

**F3 — P2 — Several "external topology" axioms carry book-internal *probabilistic* content.**
`rswThreeHalvesCrossingProbability_ge` (11.73) and the whole-theorem Group-B axioms (11.4, 11.13, 11.22, 11.24, 11.25, 11.55, 11.89, 11.93) absorb Grimmett's own arguments, not merely the externally cited primitive. The exact-threshold result (11.11) — the Harris–Kesten theorem — thus rests on axioms encapsulating the hardest analytic step (11.73) and the planar topology (11.2). Label "proved modulo *named external topology*" understates that 11.73's axiom is a probability inequality. Disposition: acceptable **only** as a disclosed divergence; discharge plan in the vetting card is appropriate but should isolate the *primitive* (lowest-crossing stopping set) rather than the full inequality.

**F4 — P2 — Consistency of axioms at degenerate indices unverified (F-block §5).**
`grimmettRectangleDualTraceEquiv`, `card_grimmettRectangleDualTraceEquiv_apply`, and `rswThreeHalvesCrossingProbability_ge` are asserted for all `n`/`l` with no non-degeneracy guard. Recommend adding compiling counterexample-style *sanity* lemmas (e.g. both trace finsets nonempty at small `n`; `l=0` endpoint evaluation) under `counterexamples/`.

**F5 — P2 — "Complete" claim overstated relative to what is proved.**
Topic card: "The chapter is therefore complete as an autoformalized interface." Ten of the nineteen headline rows are direct external axioms or wrappers thereof; only seven are genuinely proved (modulo topology). Recommend replacing "complete" with "complete *interface*, with N proved-modulo-topology and M axiomatized-at-the-external-boundary," stated numerically.

**F6 — P2 — Literal Lemma 11.22 is not proved; only a different rectangle is.**
The proved theorem uses `[0,n+1]×[-n,n]`, not the source `[0,n+1]×[0,n]`. This is disclosed, but the source instance itself is an axiom. A `cases/` application deriving the *source* rectangle statement from the centered one (or a note that it cannot be) is required by §6.

**F7 — P3 — Theorem 11.24 omits the `0 < ξ < ∞` conclusion.** Safe (axiom weakening) but the source-facing statement is incomplete.

**F8 — P3 — Inventory not independently re-enumerated display-by-display.** The grouped disposition looks complete; I did not verify every numbered item against OCR (e.g., the card's own note that "OCR has no separately labelled 11.102").

**No P0 finding.** I did not find an unapproved *hidden* axiom (all axioms are named, cited, ledgered), a checked counterexample, or a proved inconsistency.

---

## 7. Verdicts

**Per-row verdicts (independent):**

| Source | Verdict | Note |
|---|---|---|
| 11.2, 11.73 | `PASS_DOCUMENTED_DIVERGENCE` (external primitive) — pending F2 axiom run | topology/lowest-crossing at reasonable granularity |
| 11.11, 11.12, 11.21, 11.70, 11.75 | `PASS` **pending F2** (proof modulo external) | statements faithful; kernel axiom set not reproduced here |
| 11.27 | `PASS` **pending F2** | faithful generalization to `k=0`; source `k≥1` recoverable |
| 11.22 | `PASS_DOCUMENTED_DIVERGENCE` (F6) | literal rectangle only as axiom |
| 11.4, 11.13, 11.24, 11.25, 11.55, 11.63, 11.89, 11.93 | `PASS_DOCUMENTED_DIVERGENCE` (direct external axiom, F3/F5) | statements faithful; whole theorem assumed |
| 11.115, 11.116 | `PASS_DOCUMENTED_DIVERGENCE` (wrapper, F3) | rooted θ faithful |
| Degenerate-index consistency | `INCONCLUSIVE` (F4) | not compiled |
| §4 artifacts, Comparator, `#print axioms` | `INCONCLUSIVE` / gate-fail (F1, F2) | not present / not run |

**Overall fidelity verdict.** **Statement fidelity is HIGH.** Where I could compare exact Lean types to verbatim source — quantifiers, endpoints (`n≥1`, strict `p≷1/2`, open `(½,1)`), constants (`½ n^{−1/2}`, `−1/4`, `^12`, `^48`), rooted-vs-unrooted (θ = origin cluster throughout), finite-vs-infinite (`ℝ≥0∞` correlation lengths, `Integrable` moment), and direction (all inequalities correctly oriented) — the declarations **say what Grimmett says**. The one weakening (11.24's dropped `0<ξ<∞`) and the added measurability (11.63) are safe. I found **no statement-level counterexample or vacuity**.

**Strict protocol verdict (AUTOMATED_REVIEW.md §12).** **FAIL / INCOMPLETE — the batch does not meet the release gates.** Blocking: (i) the §4 run directory and its artifacts do not exist (F1, P1); (ii) `lake build`, transitive `#print axioms`, and Comparator are not reproduced (F2, P1); (iii) required `cases/` (source-rectangle 11.22, source `k≥1` 11.27), `counterexamples/` (anti-targets), and an archived independent report are absent. The chapter may be described as an **honestly-disclosed axiomatic interface with several genuinely proved-modulo-topology results**, but **not** as "reviewed, faithful, and complete" until the gates run. One P1 (F1) alone blocks the completion claim per §11.

**Transitive-axiom assessment for the exact threshold (11.11), at the exact permitted-set threshold.** By static dependency tracing: `cubicCriticalProbability_two_eq_half` = `le_antisymm cubicCriticalProbability_two_le_half (half_le_…_of_theta_half_eq_zero theta_two_half_eq_zero)`; `theta_two_half_eq_zero` routes through the independent critical annular barriers, whose bound uses `rswAnnulusOpenCircuitProbability_ge` (⇒ `rsw_gluing_inequalities` ⇒ the three `rswGluing…_subset` axioms + `rswThreeHalvesCrossingProbability_ge`) and `rswAnnulusOpenCircuitProbability_le_half_barrier`; the `p_c ≤ ½` direction uses the same crossing/RSW machinery and the self-dual rectangle count (⇒ `grimmettRectangleDualTraceEquiv`, `card_…`). **Predicted transitive set:** `{propext, Classical.choice, Quot.sound}` **plus exactly** `existsUnique_boundaryCircuitCrossedEdges` (possibly not, if unused), `grimmettRectangleDualTraceEquiv`, `card_grimmettRectangleDualTraceEquiv_apply`, `rswThreeHalvesCrossingProbability_ge`, `rswGluingTwoIntersection_subset`, `rswGluingThreeIntersection_subset`, `rswCircuitGluingIntersection_subset`, `rswAnnulusOpenCircuitProbability_le_half_barrier` — **all named, cited external topology/Russo axioms; no `sorry`; no 11.11-specific axiom.** This is consistent with the producer's claim. **But it is a static prediction: I did not run `#print axioms`, so against the strict permitted-set threshold `{propext, Classical.choice, Quot.sound}` the result is `proved modulo the named external axioms`, mechanically UNCONFIRMED here (F2).** If a kernel run shows any *un-ledgered* axiom, that becomes P0.

**Preservation of prior conclusions.** I preserve, on direct reinspection: the statement-fidelity of all nineteen rows; the existence and real proofs of the seven proved-modulo-topology results; the accuracy of the axiom ledger and vetting citations; and the honest "not assumption-free" disclosure. I do **not** adopt: the "complete" framing (F5), the implicit sufficiency of the topic/vetting cards in place of the §4 run directory (F1), or any claim that the axiom sets are mechanically confirmed (F2). These changes are supported by direct reinspection, not by repeating the producer report.

---

## 8. Independently authored `Challenge.lean`

Authored from the verbatim natural-language source (not copied from production types). It reuses shared production *definitions* (unavoidable and permitted by §9), but each conclusion is my own translation of Grimmett's words. Deliberate independence probes: **11.27 is stated with the source's `1 ≤ k`** (production drops it to `k=0`), and **11.22 uses the literal Grimmett rectangle**. Per §9 this file must be frozen/hashed before any `Solution.lean` is exposed.

```lean
import Percolation.Planar.Inhomogeneous

namespace Review.Chapter11

open Percolation Filter MeasureTheory
open scoped ENNReal Real unitInterval

/-- Grimmett, Theorem 11.11: the bond critical probability of ℤ² equals ½. -/
theorem theorem_11_11 : cubicCriticalProbability 2 = (1 / 2 : ℝ) := by
  sorry

/-- Grimmett, Lemma 11.12: θ(½)=0 (whence p_c ≥ ½). -/
theorem lemma_11_12 : theta 2 squareHalfDensity = 0 := by
  sorry

/-- Grimmett, Lemma 11.21: a left–right crossing of the rectangle [0,n+1]×[0,n]
has probability exactly ½ at density ½. -/
theorem lemma_11_21 (n : ℕ) :
    (bernoulliBondMeasure 2 squareHalfDensity).real
        (grimmettRectangleCrossingEvent n) = 1 / 2 := by
  sorry

/-- Grimmett, Lemma 11.22: for p>½ there are positive β,γ with
P_p(M_{n+1} ≤ βn) ≤ e^{−γn} for all n≥1, where M_{n+1} is the maximal number of
edge-disjoint open left–right crossings of the *literal* box [0,n+1]×[0,n]. -/
theorem lemma_11_22 {p : I} (hp : (1 / 2 : ℝ) < p) :
    ∃ β γ : ℝ, 0 < β ∧ 0 < γ ∧ ∀ n : ℕ, 1 ≤ n →
      (bernoulliBondMeasure 2 p).real
          {ω | (maxEdgeDisjointGrimmettRectangleCrossings n ω : ℝ) ≤ β * n} ≤
        Real.exp (-γ * n) := by
  sorry

/-- Grimmett, Lemma 11.27 (source form, k ≥ 1): the finite-tube log rate exists,
gives the exponential upper bound, is strictly positive and finite (bounded by −log p),
decreases in the tube width, and converges to the unrestricted axis rate. -/
theorem lemma_11_27 {p : I} (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    {k : ℕ} (hk : 1 ≤ k) :
    Tendsto (fun n : ℕ ↦ -Real.log (tubeTwoPointConnectivity p k n) / n)
        atTop (nhds (tubeConnectivityDecayRate p k)) ∧
      (∀ n : ℕ, 1 ≤ n → tubeTwoPointConnectivity p k n ≤
        Real.exp (-(n : ℝ) * tubeConnectivityDecayRate p k)) ∧
      0 < tubeConnectivityDecayRate p k ∧
      tubeConnectivityDecayRate p k ≤ -Real.log (p : ℝ) ∧
      Antitone (tubeConnectivityDecayRate p) ∧
      Tendsto (tubeConnectivityDecayRate p) atTop
        (nhds (axisConnectivityDecayRate 2 p)) := by
  sorry

/-- Grimmett, Lemma 11.75: the three FKG gluing inequalities (11.76)–(11.78). -/
theorem lemma_11_75 (p : I) (l : ℕ) (hl : 1 ≤ l) :
    (rswSquareCrossingProbability p l *
          rswThreeHalvesCrossingProbability p l ^ 2 ≤
        rswRectangleCrossingProbability p 2 l) ∧
      (rswSquareCrossingProbability p l *
          rswRectangleCrossingProbability p 2 l ^ 2 ≤
        rswRectangleCrossingProbability p 3 l) ∧
      (rswRectangleCrossingProbability p 3 l ^ 4 ≤
        rswAnnulusOpenCircuitProbability p l) := by
  sorry

/-- Grimmett, Theorem 11.70 (RSW, eq. 11.71): if the square-crossing probability is r,
the annular open-circuit probability is at least r^12 (1 − √(1 − r))^48. -/
theorem theorem_11_70 (p : I) (l : ℕ) (hl : 1 ≤ l) :
    rswSquareCrossingProbability p l ^ 12 *
        (1 - Real.sqrt (1 - rswSquareCrossingProbability p l)) ^ 48 ≤
      rswAnnulusOpenCircuitProbability p l := by
  sorry

/-- Grimmett, Theorem 11.115: for p_h,p_v<1, rooted inhomogeneous square percolation
has θ=0 iff p_h+p_v ≤ 1 and θ>0 iff p_h+p_v > 1. -/
theorem theorem_11_115 {pₕ pᵥ : I} (hpₕ : (pₕ : ℝ) < 1) (hpᵥ : (pᵥ : ℝ) < 1) :
    (inhomogeneousSquareCriticalPolynomial pₕ pᵥ ≤ 1 →
        inhomogeneousSquareTheta pₕ pᵥ = 0) ∧
      (1 < inhomogeneousSquareCriticalPolynomial pₕ pᵥ →
        0 < inhomogeneousSquareTheta pₕ pᵥ) := by
  sorry

/-- Grimmett, Theorem 11.116: for p_h,p_v,p_d<1, rooted inhomogeneous triangular
percolation has θ=0 iff p_h+p_v+p_d−p_h p_v p_d ≤ 1 and θ>0 iff it exceeds 1. -/
theorem theorem_11_116 {pₕ pᵥ pₑ : I}
    (hpₕ : (pₕ : ℝ) < 1) (hpᵥ : (pᵥ : ℝ) < 1) (hpₑ : (pₑ : ℝ) < 1) :
    (inhomogeneousTriangularCriticalPolynomial pₕ pᵥ pₑ ≤ 1 →
        inhomogeneousTriangularTheta pₕ pᵥ pₑ = 0) ∧
      (1 < inhomogeneousTriangularCriticalPolynomial pₕ pᵥ pₑ →
        0 < inhomogeneousTriangularTheta pₕ pᵥ pₑ) := by
  sorry

end Review.Chapter11
```

---

### Bottom line
Chapter 11 is a **faithfully-stated, honestly-disclosed axiomatic interface** in which the exact square-lattice threshold and the RSW/tube algebra are genuinely proved *modulo* the isolated external planar-topology and Russo primitives, while most other headline theorems are whole-theorem axioms at the external boundary. **Statement fidelity: HIGH.** **Protocol completeness: FAIL/INCOMPLETE** — the §4 run directory is absent and the axiom/build/Comparator gates were not mechanically reproduced in this read-only session. Open blocking items: **F1** (create the run directory + artifacts) and **F2** (run and archive `#print axioms`/`lake build`, defer Comparator to Linux CI). No P0 (no hidden axiom, no proved counterexample or inconsistency) was found; the degenerate-index consistency risks (F4) remain INCONCLUSIVE and should be closed with compiling sanity checks.
