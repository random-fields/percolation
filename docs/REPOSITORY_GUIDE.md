# Repository guide — material, process, and campaign state

*A map of everything in this repository: the autoformalization **process** (how Grimmett is turned into
Lean), the **material** it produces (targets, proofs, audits, review runs), and the current **campaign
state** (the open PRs, their debt, and an independent faithfulness review). Read this first to know what
is here and how to navigate it.*

> **Integration-branch note.** This guide was authored on PR #14 as a map of `main` and the then-open
> PR campaign. On `codex/theorem-11-11-integration`, the exact heads of PRs #1--#14 (excluding the
> nonexistent #5) are all ancestors of the branch. Section 4 is therefore a historical snapshot of
> the source branches, not a claim that their files remain separated here. The integration keeps the
> canonical later APIs and reconciles compatible material from the competing Chapter 2 branches;
> see [`theorem-11.11/PR_CONSOLIDATION.md`](theorem-11.11/PR_CONSOLIDATION.md).

`main` is a **scaffold** (the framework docs + `kg/` + `audit/` + a small `Percolation/` core). The
formalized mathematics lives in the **open PR branches** (§4); the per-chapter *review runs* (§3)
accumulate on those branches, not on `main`.

---

## 1. What this repository is

A Lean 4 / Mathlib **v4.30.0** autoformalization of Grimmett, *Percolation* (2nd ed. 1999) and *The
Random-Cluster Model* (2006), run as an agent-driven **plan-loop** adapted from
`random-fields/optimal-transport`. The method is documented in
[`docs/METHODOLOGY.md`](METHODOLOGY.md):

```
kg/textbooks  →  extract targets (kg/ + docs/PLAN.md)  →  cut frontier vs Mathlib
   →  design review (faithfulness)  →  prove in dependency order  →  lake build
   →  automated review (comparator + independent review + counterexamples)
```

Guiding rules (from [`AGENTS.md`](../AGENTS.md), [`audit/FAITHFULNESS.md`](../audit/FAITHFULNESS.md)):
theorem statements **no stronger than the source**; finite-volume vs infinite-volume objects kept
separate; random-cluster boundary conditions explicit; axiom/sorry tracked; every target carries a source
id from [`formalization.yaml`](../formalization.yaml).

## 2. The material, by directory (on `main`)

| path | what it is |
|---|---|
| [`docs/PLAN.md`](PLAN.md) | source-ordered list of formalization targets |
| [`docs/DESIGN.md`](DESIGN.md) | object hierarchy + module boundaries |
| [`docs/METHODOLOGY.md`](METHODOLOGY.md) | the plan-loop / comparator process |
| [`docs/VALIDATION.md`](VALIDATION.md) · [`docs/VERIFICATION.md`](VERIFICATION.md) | acceptance theorems ("done"); informal→formal map + source links |
| [`docs/HISTORY.md`](HISTORY.md) · [`docs/HANDOFF.md`](HANDOFF.md) · [`docs/FRONTIER.md`](FRONTIER.md) | decision log; cross-run handoff; open frontier |
| [`kg/`](../kg/) | the knowledge graph: `percolation_targets.seed.json`, `source_catalog.json` — how textbook defs/theorems became targets with ids |
| [`audit/`](../audit/) | the faithfulness framework: `CONVENTIONS.md`, `FAITHFULNESS.md`, `VALIDATION.md`, `vetting/policy.yml`, `topics/topic-0X-*.md` |
| [`formalization.yaml`](../formalization.yaml) | machine-readable manifest: targets, source ids, `main_results`, fidelity notes |
| [`AXIOM_AUDIT.md`](../AXIOM_AUDIT.md) | project axiom ledger (see §6) |
| [`Percolation/`](../Percolation/) | the Lean library (rich on the PR branches; a stub on `main`) |
| [`.github/workflows/`](../.github/workflows/) | CI: `lean.yml` (build) + per-chapter **comparator** workflows |

## 3. The automated-review runs (the process trace) — on the PR branches

The richest process artifact is the per-chapter **review run**, under
`audit/reviews/chapter-XX/DATE-HASH/`, with **multiple runs per chapter** (rounds / competing models).
Each run bundles:

| file | role |
|---|---|
| `correspondence.md` | the **Lean-statement ↔ Grimmett-theorem map** (which decl is which textbook result) |
| `independent-review.md` · `SUMMARY.md` · `MANIFEST.md` | the review model's independent faithfulness verdict |
| `comparator/{Challenge.lean, Solution.lean, config.json, lakefile.toml}` | the **adversarial comparator** harness — the content behind the `trusted-comparator` CI check |
| `counterexamples/AntiTargets.lean` | **anti-vacuity guards** — statements that must *not* be provable |
| `cases/*.lean` | probe lemmas (e.g. `Analyticity`, `TailAndRates`, `TreeMoments`) |
| `axioms.md` · `AxiomAudit.lean` | per-run axiom audit |

⚠ **Not present:** raw model transcripts / chain-of-thought / tool-call logs. This repo captures the
*structured outputs* of the process (plans, correspondence maps, reviews, comparator challenges,
counterexamples, axiom audits) plus the git history and the GitHub PR threads — not a replay of the
model's reasoning.

## 4. Campaign state — the open PRs

`main` is nearly empty; the work is in stacked PR branches. As of the last review (2026-07-27):

| PR | chapter / target | base | debt (axiom decls / real sorry) | CI |
|---|---|---|---|---|
| **#1** | Thm 1.10 + Peierls | main | 0 / 0 (`#print axioms` clean) | ✅ |
| **#2** | textbook audit scorecards | main | docs only | ✅ |
| **#3** | Ch 2 (Codex) | main | 0 / 0 (+1 legit `native_decide`) | ✅ |
| **#4** | Ch 2 (Fable) | main | 0 / 0 | ✅ |
| **#6** | random-cluster FKG | main | 0 / 0 (self-labeled scaffold) | ✅ |
| **#7** | Ch 4 | main | 0 / 0 | ✅ |
| **#8** | Ch 5 | #7 | 0 / 0 | ✅ |
| **#9** | Ch 6 | main | 0 / **58** | ✅ |
| **#10** | Ch 11-prereqs | #9 | 0 / 60 | ✅ |
| **#11** | Ch 11 | #10 | **23** / 70 | ✅ (conflicting) |
| **#12** | Ch 8 | #11 | 23 / 70 | ❌ comparator |
| **#13** | Ch 12 | #12 | 20 / 70 | ❌ comparator |
| **#14** | repository guide and campaign review | main | docs only | ✅ |

**Two stacks + independents.** Stack A (clean): #7 (Ch4) ← #8 (Ch5). Stack B (debt-laden): #9 (Ch6) ←
#10 ← #11 ← #12 ← #13 — debt is *generated* at #9 (sorries) and #11 (axioms), then inherited up the
chain; merge bottom-up. Independent, clean: #1, #3/#4 (competing Ch2), #6. (Debt counts are `axiom`
*declarations* and non-comment `sorry`; a plain word-grep over-counts because of `AXIOM_AUDIT.md`
references.)

## 5. Independent faithfulness review (2026-07-27)

Four PRs were audited from scratch (each in an isolated worktree, checking definitions and theorem
**statements** against Grimmett — faithfulness, quantifiers, vacuity — not compilation). Verdicts are
posted on the PRs themselves:

- **#1** (Thm 1.10 + Peierls) — **MERGE.** `0 < p_c(d) < 1` (d≥2) proved unconditionally; real Peierls
  contour argument; `#print axioms` = the 3 standard Lean axioms only.
- **#4** (Ch 2, Fable) — **MERGE-WITH-FIXES.** Faithful; **`p_c < 1` proved unconditionally.**
- **#3** (Ch 2, Codex) — **MERGE-WITH-FIXES.** Faithful and broader (~1533 vs ~901 theorems), but
  **`p_c < 1` and general Reimer-BK are conditional** on (honest, non-vacuous) hypothesis packages.
- **#6** (random-cluster FKG) — **NEEDS-WORK / mislabeled.** The abstract Chapter-2 FKG machinery is
  faithful, but the random-cluster measure `φ_{p,q}` with the `q^{k(ω)}` cluster weight — and the `q ≥ 1`
  regime — are **absent**; it is Ch 2, not Ch 3. (The PR's own `formalization.yaml` discloses this.)

**Recommendations:** (i) **Ch 2 bake-off → base on #4** (unconditional `p_c<1`), harvest #3's breadth on
top; #1 and #4 overlap on the Peierls/`p_c` machinery, so merge one phase-transition formalization, not
two. (ii) **Repo-wide prune:** `Core/Configuration.lean`'s `OpenConnection := ∃_:Unit, True`,
`openCluster`, `BondConfiguration`, `BaseGraph`, `PercolationProbability.theta : ℝ` are **dead trivial
scaffolds** — unused by the real theorems but a landmine (the reason #6 looks hollow); delete or
quarantine them. (iii) The real scrutiny is owed to **Stack B** (#9's 58 sorries, #11's 23 axioms) —
audit whether they are load-bearing.

## 6. Conventions & guardrails

- **Toolchain:** Lean/Mathlib **v4.30.0** (`require`-compatible with the `random-fields` v4.30 cluster).
- **Axioms/sorries:** tracked in [`AXIOM_AUDIT.md`](../AXIOM_AUDIT.md) and per-run `axioms.md`; the
  `trusted-comparator` CI check enforces the axiom whitelist + kernel replay on headline results (it
  correctly fails on the debt-carrying top of Stack B).
- **Faithfulness discipline:** statements no stronger than the source; anti-target/counterexample guards;
  comparator challenge-solution; independent design/faithfulness reviews. Studying whether these
  automated guards **caught** the §5 stubs (`OpenConnection := True`, the missing `q^{k}`) — or let them
  through — is the most informative use of this material for improving the pipeline.

## 7. How to study the process

- **Pipeline design:** [`docs/METHODOLOGY.md`](METHODOLOGY.md) + [`formalization.yaml`](../formalization.yaml) + [`docs/PLAN.md`](PLAN.md).
- **Faithfulness mechanism:** any `audit/reviews/*/correspondence.md` + `independent-review.md` (on a PR
  branch, e.g. PR #13) — the repo's *own* automated verdict, comparable to §5.
- **Adversarial checks:** `comparator/Challenge.lean` + `counterexamples/AntiTargets.lean` — the machinery
  meant to catch vacuity.
- **Campaign history:** git commit trail + the GitHub PR conversation threads.
