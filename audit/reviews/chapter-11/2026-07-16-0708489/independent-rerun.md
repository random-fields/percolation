I have completed all checks. Writing the report.

---

# Final Review — Grimmett Chapter 11 (commit `0708489`, frozen audit `2026-07-16-0708489`)

## Verdict

**PASS.** The F5 and F7 findings are genuinely repaired. `finiteCorrelationLength_pos_lt_top` is a real (non-axiom) proof with a source-faithful type and load-bearing endpoint hypotheses; the 6 / 11 / 2 = 19 proof/axiom/wrapper counts are exactly what the kernel reports. No P0/P1. Two P2 documentation/scope notes below. I did not trust any claimed command — I re-ran the authoritative axiom audit myself.

## Checks performed (and how)

- **Read the exact type/proof** of `Percolation.finiteCorrelationLength_pos_lt_top` (`Percolation/Planar/Chapter11External.lean:103–124`) and the definitions it relies on: `correlationLength` (`Critical/TwoPoint.lean:1533`) and `boxRadiusDecayRate_pos_of_lt_critical` (`Critical/BoxRadiusProperties.lean:120`).
- **Ran the authoritative axiom audit** myself: `lake env lean audit/reviews/chapter-11/2026-07-16-0708489/AxiomAudit.lean` — completed, full `#print axioms` output for all 22 declarations, **no `sorryAx`**.
- **Cross-checked counts** across SUMMARY.md, RESPONSE_TO_INDEPENDENT_REVIEW.md, correspondence.md, and the topic card `audit/topics/topic-11-bond-percolation-two-dimensions.md` against the kernel output (self-referential = axiom; absent-from-own-set = proved).
- **Inspected** cases/Chapter11Cases.lean, counterexamples/Chapter11Counterexamples.lean, comparator/{Challenge,Solution}.lean + config.json, correspondence.md, axioms.md, and `.github/workflows/chapter11-comparator.yml`.
- **Grepped** production for `sorry`/`admit` (0) and for the location of project axioms (3 files only).

## F7 — Theorem 11.24 positivity/finiteness: **CLOSED**

- **Type is faithful.** `{p : I} (hpHalf : 1/2 < p) (hpOne : p < 1) : 0 < finiteCorrelationLength p ∧ finiteCorrelationLength p < ⊤`, with `finiteCorrelationLength : I → ℝ≥0∞`. This is exactly Grimmett 11.24's `0 < ξᶠ(p) < ∞` under supercritical `p ∈ (½,1)`. The `ℝ≥0∞` codomain preserves the infinite endpoint convention.
- **Endpoint hypotheses are load-bearing, not decorative.** The proof derives `hσ0 : 0 < 1-p` from `hpOne` and `hσpc : 1-p < ½` from `hpHalf` (both via `linarith`), then feeds them to `boxRadiusDecayRate_pos_of_lt_critical`. Dropping `p<1` collapses `σ p` to a non-positive density (rate positivity fails); dropping `½<p` puts `σ p` at/above criticality where the rate is `0` and finiteness genuinely fails. Both hypotheses are used.
- **It is a genuine proof, not an axiom.** In the kernel output `finiteCorrelationLength_pos_lt_top` does **not** list itself; it depends on `propext, Classical.choice, Quot.sound`, the equality axiom `finiteCorrelationLength_eq_half_correlationLength_complement`, plus the six proved-threshold primitives (`grimmettRectangleDualTraceEquiv`, `rswAnnulusOpenCircuitProbability_le_half_barrier`, three `rsw*Gluing*Intersection_subset`, `rswThreeHalvesCrossingProbability_ge`). This **exactly matches** axioms.md's row for it. The six primitives enter legitimately because the proof rewrites through `cubicCriticalProbability_two_eq_half`.
- **Independently exercised** by a concrete `3/4`-density case (Chapter11Cases.lean:32–37) and by the density-one exclusion anti-target (Chapter11Counterexamples.lean:19–22).
- Transitive-assumption honesty: positivity/finiteness is proved *conditional on* the 11.24 equality axiom (the headline result), documented as such in correspondence.md and the topic card. The limit-existence part of 11.24 is the separate axiom `truncatedTwoPointConnectivity_logRate_tendsto`. All three components of 11.24 are present.

## F5 — exact counts / "complete" wording: **CLOSED**

Kernel output classifies each of the 19 source rows, and the totals match the topic card / SUMMARY exactly:

- **11 direct external axioms** (declaration lists itself): Prop 11.2, Thm 11.4, Lem 11.13, Lem 11.22 (literal), Thm 11.24 (equality), Thm 11.25, Thm 11.55, Thm 11.63, Lem 11.73, Thm 11.89, Thm 11.93.
- **6 proved** (declaration absent from own axiom set): Thm 11.11, Lem 11.12, Lem 11.21, Lem 11.70, Lem 11.75 (five modulo named primitives) + Lem 11.27 (`tubeConnectivityDecayRate_properties` → only `propext, Classical.choice, Quot.sound`).
- **2 wrappers**: 11.115 → `inhomogeneousSquareTheta_{eq_zero,pos}_iff`; 11.116 → `inhomogeneousTriangularTheta_{eq_zero,pos}_iff` (each over two named axioms, neither self-referential).
- 6 + 11 + 2 = **19**, plus the additional proved centered normalization `maxEdgeDisjointSquareRectangleCrossings_probability_le_exp` (correctly described as supplementary, not counted). Verified.

## Other checks — no hidden holes found

- **Production is clean.** No `sorry`/`admit` in Chapter11External.lean. Project `axiom` declarations exist in **only three files** — `Chapter11External.lean`, `Planar/External.lean` (8 axioms), `Planar/Inhomogeneous.lean` — matching the "three external-boundary files" claim.
- **Comparator is internally consistent.** Challenge.lean re-states 9 source types with `sorry`; Solution.lean discharges them from production; config.json's `theorem_names` and `permitted_axioms` line up with the actual dependency sets (e.g. the literal-11.22 axiom is explicitly permitted because `lemma_11_22` legitimately rests on it — honest, not concealed). `enable_nanoda: false`.
- **CI workflow** pins Lean `v4.30.0`, a fixed Landrun SHA and Comparator rev, restores Mathlib cache, and runs the comparator under a `systemd-run` network-restricted sandbox. Structurally sound; I did not execute it (no Linux sandbox locally).
- **Cases/counterexamples compile-plausible and on-target:** `rswThreeHalvesCrossingEvent 0 = Set.univ`, `¬ 1 ≤ (0:ℕ)`, `¬((1:I)<1)`, `-Real.log 0 = 0` all guard the documented degenerate/endpoint cases.

## Findings

- **P2 (comparator scope).** The trusted comparator covers 9 of 19 rows; it does **not** independently re-state the F7 repair `finiteCorrelationLength_pos_lt_top` nor the 11.24 equality axiom in Challenge.lean. The F7 corollary is verified only by the cases file and the axiom audit, not by the trusted-comparator gate. Reasonable (pure axioms have nothing to compare), but the F7 statement itself is provable and could have been added to the comparator.
- **P2 (unexecuted trusted gates, already disclosed).** Trusted Comparator, `lake build`, and the case/counterexample builds were not run in a trusted sandbox during this review; MANIFEST/SUMMARY disclose this and defer to CI. I independently re-ran only the axiom audit (exit success, output matches axioms.md verbatim); I did not run `lake build` or the comparator.

## Command-trust note

I did not accept any claimed result on faith. I personally ran `lake env lean .../AxiomAudit.lean` and confirmed its output matches axioms.md's dependency table row-for-row, including the F7 theorem's exact axiom set and the absence of `sorryAx`. I did **not** run `lake build` (8,725-job claim unverified) or the trusted comparator; those remain as asserted in SUMMARY/MANIFEST.
