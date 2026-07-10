# Automated Review Protocol for Large-Scale Autoformalization

This file is the executable review contract for chapter-scale and other batch
autoformalization in this repository. It supplements `AGENTS.md`; it does not replace the
proof, build, source-citation, or axiom rules there.

The protocol is designed to answer four different questions which must not be conflated:

1. **Source fidelity:** does the Lean proposition say the same thing as the source?
2. **Usability and boundary behavior:** can the formal theorem derive the source's concrete
   instances, including endpoints and degenerate cases?
3. **Logical trust:** was the proposition kernel-checked without hidden, unapproved axioms?
4. **Independent reproducibility:** does a reviewer who did not write the result reach the same
   conclusion?

A green `lake build` answers none of these questions except that the checked files elaborate.
Likewise, a successful Comparator run proves exact agreement with a *formal challenge*, not
agreement between that challenge and natural language. The correspondence review remains
essential.

## 1. When this protocol is mandatory

Run this protocol before claiming completion of any of the following:

- a textbook chapter or section;
- a PR containing several source-facing theorems;
- an autoformalization campaign or generated theorem batch;
- a foundational definition used by many later source-facing results;
- any theorem whose statement has substantial coercions, extended values, limiting conventions,
  probability endpoints, or generalized functional hypotheses;
- any result proved modulo a project axiom.

For a single routine helper theorem, the ordinary `AGENTS.md` checks are enough unless a reviewer
or topic card explicitly requests this protocol.

The producer must not label a batch `faithful`, `complete`, or `assumption-free` until all
mandatory gates in Section 12 pass. In particular, “all results were autoformalized” means every
result in the declared source inventory has a disposition, not merely that every result selected
by the producer was proved.

## 2. Roles and separation of responsibility

Use these roles even when one person orchestrates the run:

| Role | Responsibility | May edit production proofs during its first pass? |
|---|---|---:|
| Producer | Implements definitions and proofs; supplies source locations and intended mappings | yes |
| Review orchestrator | Freezes the reviewed revision, creates the inventory, runs mechanical checks, and assembles evidence | no |
| Independent fidelity reviewer | Re-derives the source-to-Lean comparison from the source and exact Lean types | no |
| Adversarial reviewer | Looks for missing hypotheses, vacuity, junk values, false strengthening, inconsistent assumptions, and unapproved axioms | no |
| Maintainer/arbitrator | Accepts documented divergences and resolves disagreements | yes, after reports are frozen |

The fidelity and adversarial roles may be performed by one independent agent for a smaller batch.
For a chapter-scale completion claim, prefer a separate model family or vendor (for example Claude
Code reviewing Codex output, or the reverse). “Independent” means a fresh task with a fixed
revision and no instruction to confirm the producer's conclusion. Record the agent, model if
known, date, reviewed commit, and prompt.

The first independent pass is read-only. If the reviewer edits the theorem before recording the
failure, the original defect and the independence of the report are both lost. Repair in a later
commit, then rerun the affected review and all downstream gates.

## 3. Freeze the object being reviewed

Every review run must identify an immutable revision. Record at least:

```text
review id:
scope:
source id and edition:
source pages/sections:
git commit:
Lean version:
Mathlib revision:
Comparator revision:
review mode: internal | adversarial-sandboxed
started at:
completed at:
```

Run and record:

```sh
git status --short
git rev-parse HEAD
lake env lean --version
lake build
```

A dirty worktree is allowed only if the review manifest lists the diff or tree hash being
reviewed. Prefer a review commit. If any reviewed declaration, definition occurring in its type,
or transitive proof dependency changes, mark the old evidence stale and rerun the relevant gates.

Never reconstruct elapsed time or token usage after the fact. If telemetry is requested, snapshot
the available counters immediately before and after each review window. Keep formalization,
shared-infrastructure, review, documentation, and Git/PR time in separate rows. Label unavailable
data `not measured`; do not estimate it.

## 4. Required review artifacts

Create a run directory under:

```text
audit/reviews/<scope>/<YYYY-MM-DD>-<short-commit>/
```

Use the following layout. A future automation script may generate it, but the files remain the
review record and must be understandable without that script.

```text
MANIFEST.md                 frozen revision, source, scope, tools, and reviewers
correspondence.md           complete source-to-Lean inventory and verdicts
cases/                      compiling application, oracle, and boundary tests
counterexamples/            compiling counterexamples/anti-targets; attempted searches in Markdown
comparator/
  Challenge.lean            trusted, independently authored source-facing statements
  Solution.lean             wrappers proved from production declarations
  config.json               Comparator configuration
  lakefile.toml             isolated Comparator project configuration
  README.md                 pinned tool versions, trust mode, exact command and result
AxiomAudit.lean             explicit #print axioms commands for reviewed declarations
axioms.md                   transitive #print axioms results and exceptions
independent-review.md       unedited first-pass independent report plus disposition
SUMMARY.md                  concise gate result suitable for the PR description
```

Do not commit huge nondeterministic logs. Record exact commands, exit status, relevant diagnostics,
tool versions, and a stable path or CI link for the full log. Review Lean files may contain `sorry`
only in the trusted Comparator `Challenge.lean`, where Comparator explicitly expects an open
challenge. No production file, case file, counterexample file, or `Solution.lean` may contain
`sorry` or `admit`.

## 5. Build the source inventory before reviewing proofs

Start with the source, not with the declarations that happen to exist. Enumerate every named
theorem, proposition, lemma, corollary, and every numbered consequence included in the claimed
scope. Give omitted items an explicit disposition such as `out of scope`, `definition only`,
`duplicate formulation`, or `missing`. A missing row is not an acceptable disposition.

The correspondence table must contain these columns:

| Field | Required content |
|---|---|
| Source result | source id plus theorem/equation number and exact page or stable section |
| Natural-language statement | a precise paraphrase including every quantifier and hypothesis |
| Mathematical conventions | domains, endpoints, finiteness, normalization, and empty/infinite conventions |
| Lean declaration | fully qualified declaration name, or `missing` |
| Exact Lean type | output of `#check`/`#print`, formatted for review rather than paraphrased |
| Dependencies | important mathematical dependencies and source results, not just imported modules |
| Divergence | none, or an explicit generalization/specialization/encoding difference |
| Case tests | paths and test names |
| Adversarial tests | paths, search result, and any witness found |
| Comparator | challenge name and pass/fail/not-run reason |
| Axioms | exact transitive axiom set |
| Independent verdict | one of the verdicts in Section 11 |
| Status | target/proved/proved-modulo/missing/rejected |
| Time/tokens | measured formalization and review telemetry, separately labeled |

For each row, compare all of the following explicitly:

- order and scope of quantifiers;
- explicit and implicit Lean arguments;
- typeclass assumptions and nonemptiness assumptions;
- `Nat`, `Int`, `Real`, `ENNReal`, `ENat`, finite-set, set, and measure coercions;
- strict versus non-strict inequalities;
- equality versus one-way implication;
- open/closed interval endpoints and positivity needed before division or logarithms;
- finite versus infinite cardinality conventions;
- `0`, `1`, empty objects, dimension zero/one, `⊤`, denominators equal to zero, and other junk values;
- whether the Lean conclusion is source-facing or only an auxiliary conditional theorem;
- whether a generalized functional theorem has enough assumptions to recover the source theorem;
- whether a specialized theorem silently drops valid source cases;
- whether definitions in the Lean type have the source normalization.

A generalization is not automatically faithful. It is acceptable only when the source theorem is
derived as a public corollary or a compiling application test, and the extra domain introduces no
misleading junk behavior. A theorem with an added hypothesis is a specialization and must list
which source cases are lost.

## 6. Generate concrete and semantic test cases

General theorems—especially analytic inequalities stated for arbitrary functions—must be tested by
deriving concrete source-valid instances. Tests are review evidence, not examples chosen only
because `simp` can solve them.

Create between three and seven meaningful cases per major general theorem, chosen from:

1. a literal example or parameter choice from the source;
2. the smallest nontrivial finite case;
3. an equality or sharpness case;
4. each meaningful endpoint (`0`, `1`, empty set, radius zero, and so on);
5. an infinite or extended-value case when the formal type admits one;
6. a source-valid case most likely to expose a missing argument;
7. a junk-value case admitted by the Lean types but absent from the source.

Use two kinds of test:

### 6.1 Application tests

An application test proves the concrete statement *using the reviewed theorem*. Its purpose is to
show that the public API has the needed arguments, hypotheses, and conclusion.

```lean
import Percolation.The.Module.Under.Review

namespace ReviewCases

-- Name the source result and case in a comment.
example (h₁ : SourceHypothesis₁) (h₂ : SourceHypothesis₂) : ConcreteConclusion := by
  exact Percolation.reviewedTheorem
    (explicitArgument := explicitValue) h₁ h₂

end ReviewCases
```

Prefer `exact` with named arguments. If syntactic normalization is necessary, use a narrow
`simpa only [...] using ...`. Do not use unrestricted `simp`, `aesop`, `omega`, or an independent
proof in this test: they can make the file compile without exercising the reviewed declaration.
The test body must visibly reference that declaration.

Failure to derive a source-valid instance is a statement/API defect until explained. It commonly
reveals a missing parameter, the wrong inequality direction, an unnecessary hypothesis, or a
coercion that changed the domain.

### 6.2 Independent oracle tests

When a finite or computational case is decidable, also prove it independently without the target
theorem, using `decide`, `native_decide`, `norm_num`, finite enumeration, or a short direct proof.
This is a semantic cross-check rather than an application check. Keep the oracle and application
as separate declarations and state why the oracle is independent.

An oracle test is valuable only when it tests the same definitions and normalization as the
source-facing statement. Proving an unrelated numerical shadow is not evidence.

### 6.3 Vacuity checks

Every test must show that its hypotheses are jointly satisfiable. Concrete inputs are best. For
abstract hypotheses, add or cite an inhabitance witness. Prohibited review evidence includes:

- `False.elim` or `by_contra` fed by inconsistent test assumptions;
- a conclusion discharged before the reviewed theorem is used;
- a test where a denominator/logarithm side condition cannot hold;
- an event or finite type that is empty only because of a mistaken encoding;
- an unrestricted simplifier that erases the theorem application.

Compile every case file directly and as part of the repository build when it is included in a Lean
library:

```sh
lake env lean audit/reviews/<run>/cases/<file>.lean
```

Record case generation failures in `correspondence.md`; do not silently delete them.

## 7. Adversarial tests and attempts to prove the opposite

“Try to prove the opposite” is a falsification technique, not a proof of fidelity. Failure to find
a counterexample is inconclusive. Success is high-priority evidence and must never be hidden.

For a theorem of the form `∀ x, H x → C x`, search for the genuine negation:

```lean
∃ x, H x ∧ ¬ C x
```

For an inequality, test the reversed strict inequality on concrete boundary and representative
inputs. For an equivalence, test both missing directions independently. For a uniqueness theorem,
construct two candidates. For a limit theorem, test endpoint and constant-sequence behavior.

Use, in descending order of evidentiary value:

1. an explicit mathematical counterexample checked by Lean;
2. exhaustive finite search using a trusted decidable computation;
3. `native_decide`, `decide`, `norm_num`, or another small proof-producing decision procedure;
4. `/lean4:disprove` or an equivalent counterexample search when available;
5. an independent agent's structured search.

Also create **anti-targets** for tempting but unjustified strengthenings: omitted source hypotheses,
strict instead of non-strict bounds, inclusion of a forbidden endpoint, swapping finite and
infinite cardinality, or replacing an implication by an equivalence. A compiling counterexample
to the stronger anti-target is positive evidence that the production theorem did not accidentally
overclaim.

If both a reviewed theorem and its exact negation appear provable under the same satisfiable
hypotheses, stop the review. Investigate, in this order:

1. the two propositions are not actually definitionally the same (coercion or notation drift);
2. the hypotheses are inconsistent or vacuous;
3. an unapproved axiom or unsafe definition entered the environment;
4. the counterexample used a different definition/normalization;
5. a tooling or kernel issue.

Do not commit intentionally noncompiling Lean files as evidence that an opposite was attempted.
Write the attempted proposition, methods, search bounds, and outcome in
`counterexamples/README.md`. Commit only successful counterexamples and anti-targets as compiling
Lean files. `no counterexample found up to bound N` must never be restated as `proved true`.

## 8. Transitive axiom and sorry audit

Run the ordinary scans and a transitive axiom check for every source-facing declaration, including
wrappers used only in correspondence tests.

When the lean4-skills helpers are installed:

```sh
lean4-skills-sorry-analyzer . --report-only
lean4-skills-check-axioms-inline . --report-only
```

The inline axiom helper is supplemental: its current implementation temporarily edits and
restores the selected Lean files and may miss declarations in nested namespaces. Run it only on a
clean worktree with no concurrent writers, verify that the tree is restored afterward, and do not
use it instead of the explicit headline audit below.

If a wrapper is unavailable, make a temporary or review-local Lean file importing the production
modules and add one command per declaration:

```lean
#print axioms Percolation.theoremName
```

Then run it with `lake env lean`. `#print axioms` is transitive and is the authoritative per-theorem
record; a text search alone is not. The default permitted set is exactly:

```text
propext
Classical.choice
Quot.sound
```

Any additional axiom is a gate failure unless it is an intentional, true project axiom already
listed in `AXIOM_AUDIT.md`, independently vetted in `audit/vetting/`, and explicitly accepted for
this scope. A theorem depending on such an axiom must say `proved modulo <axiom>`; it is not
`assumption-free`. Ordinary theorem parameters are not axioms, but the fidelity review must still
check that the source has the corresponding hypotheses.

Scan production and review solution/test files for `sorry`, `admit`, `axiom`, unsafe declarations,
and placeholder declarations. Avoid naive claims based only on raw substring matches in comments;
record the command and inspect each hit.

## 9. Comparator challenge protocol

Use [leanprover/comparator](https://github.com/leanprover/comparator) according to its pinned
upstream README. Comparator checks that each solution theorem:

- has exactly the same statement as the trusted challenge theorem;
- uses no axioms outside `permitted_axioms`;
- is accepted by the Lean kernel (and optionally an additional supported kernel).

It does **not** decide whether the trusted challenge faithfully translates the book. Therefore the
challenge must be authored from the natural-language source by the reviewer, not generated by
copying the production theorem type. Freeze and hash `Challenge.lean` before preparing or exposing
`Solution.lean` to the checking environment.

For a chapter, one challenge module may contain all headline declarations. Use one theorem name
per correspondence row and source-based names such as `Review.Chapter05.theorem_5_4`. A typical
configuration is:

```json
{
  "challenge_module": "Challenge",
  "solution_module": "Solution",
  "theorem_names": [
    "Review.Chapter05.theorem_5_4",
    "Review.Chapter05.lemma_5_12"
  ],
  "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
  "enable_nanoda": false
}
```

`Challenge.lean` should import the smallest trusted layer containing the definitions in the
statement, preferably a module below the production proof:

```lean
import Percolation.Critical.RadiusEvents

namespace Review.Chapter05

/-- Reviewer-authored translation of Grimmett, Theorem 5.4. -/
theorem theorem_5_4 (/* every source parameter and hypothesis */) :
    /* independently translated source conclusion */ := by
  sorry

end Review.Chapter05
```

`Solution.lean` imports the production theorem and proves the same reviewer-owned challenge using
it. Named arguments make mismatches diagnosable:

```lean
import Percolation.Critical.RadiusDecay

namespace Review.Chapter05

theorem theorem_5_4 (/* the challenge parameters and hypotheses */) :
    /* the challenge conclusion */ := by
  exact Percolation.radiusTail_exponential_decay_of_lt_critical
    (/* explicit arguments and hypotheses */)

end Review.Chapter05
```

Follow Comparator's current security assumptions exactly. At the time this protocol was written,
its strong adversarial guarantee requires `landrun`, a Lean-compatible `lean4export`, an
unprivileged Linux environment, trusted challenge imports and Lake files, and that potentially
adversarial solution files have not previously been compiled outside the sandbox. Its documented
production invocation also wraps Comparator with a restricted `systemd-run`. Pin the Comparator,
`lean4export`, and optional additional-kernel revisions and copy the exact upstream command into
the run README rather than relying on this document to remain a command-line authority.

If those conditions are unavailable (for example on macOS, or after production solution files
were already compiled), run Comparator only in explicitly labeled `internal` mode or defer it to a
clean Linux CI/VM. The upstream fake-landrun script is for development and does not establish the
full sandbox guarantee. Never report an internal-mode result as adversarially sandboxed.

A Comparator pass is mandatory for every headline theorem when the infrastructure is available.
Otherwise record `not run`, the concrete missing prerequisite, and a CI/owner follow-up. A plain
`lake build` or textual comparison is not a substitute and must not be labeled a Comparator pass.

## 10. Independent coding-agent review

Give the independent agent the natural source, frozen commit, inventory of claimed results, and
this protocol. Do not give it a prompt that presupposes success. Use this template, adapting only
paths and scope:

```text
You are the independent, read-only reviewer of <scope> at commit <sha>.
Read AGENTS.md and AUTOMATED_REVIEW.md completely. Do not edit production files during the first
pass. Starting from <source id, edition, pages>, verify whether the inventory is complete and each
natural-language result is faithfully represented by the claimed fully qualified Lean declaration.

For every row:
1. restate all source quantifiers, hypotheses, domains, endpoints, and conventions;
2. inspect the exact Lean type and definitions it uses;
3. classify generalization, specialization, changed normalization, or missing cases;
4. propose and, where feasible, compile application/boundary tests;
5. search for counterexamples, vacuous hypotheses, and junk-value behavior;
6. run or inspect #print axioms and check for sorry/admit/new axioms;
7. inspect dependency direction and possible circular wrappers;
8. give one of the protocol verdicts with evidence and file/line references.

Try to falsify the producer's mapping. Do not treat the existing correspondence table as ground
truth. Return the unedited first-pass report before proposing repairs. Clearly separate a proved
defect, a plausible risk, and an inconclusive search.
```

The reviewer must report:

- missing source results, not only defects in listed rows;
- exact declaration names and file/line links;
- every command actually run and whether LSP/MCP was available;
- concrete counterexamples or failed source-valid application tests;
- the exact axiom set for headline declarations;
- disagreements with the producer's correspondence or status;
- limitations, timeouts, and uninspected items;
- a per-theorem verdict and overall gate recommendation.

Store the first-pass report verbatim in `independent-review.md`, followed by an orchestrator
disposition table. Do not rewrite the report to make consensus appear stronger. For a substantive
disagreement, obtain maintainer arbitration or a third independent review. Majority vote does not
override a compiling counterexample or an unapproved axiom.

## 11. Verdicts and severity

Use exactly these per-row verdicts:

| Verdict | Meaning |
|---|---|
| `PASS` | faithful statement, required tests pass, Comparator passes where required, and only permitted axioms occur |
| `PASS_DOCUMENTED_DIVERGENCE` | mathematically valid generalization/specialization/encoding difference, source corollary is demonstrated, and maintainer accepts the note |
| `FAIL_MISSING` | source result has no adequate Lean declaration |
| `FAIL_STATEMENT` | quantifier, hypothesis, domain, conclusion, endpoint, or normalization mismatch |
| `FAIL_VACUOUS` | theorem/test is true only through inconsistent or uninhabited hypotheses, or junk conventions defeat the intended meaning |
| `FAIL_TEST` | a required source-valid instance cannot be derived or an independent oracle disagrees |
| `FAIL_COUNTEREXAMPLE` | a genuine counterexample to the claimed statement/translation was checked |
| `FAIL_AXIOM` | unapproved axiom, sorry, unsafe dependency, or false assumption-free claim |
| `FAIL_COMPARATOR` | solution statement/axiom/kernel check fails against the trusted challenge |
| `INCONCLUSIVE` | required evidence could not be obtained; never counts as pass |

Assign severity separately:

- **P0:** inconsistency, unapproved axiom, checked counterexample, wrong theorem advertised as
  proved, or materially false completion claim;
- **P1:** missing major theorem, source/Lean mismatch, vacuity, or Comparator failure;
- **P2:** incomplete test coverage, unclear divergence, stale evidence, or missing reproducibility
  metadata;
- **P3:** documentation or naming issue that cannot change mathematical meaning.

Do not average scores across the chapter. One P0/P1 headline failure blocks the chapter completion
claim even if every other row passes.

## 12. Release gates

A batch may be called reviewed and faithful only when all of these hold:

- [ ] The source inventory is complete and every omission has an accepted disposition.
- [ ] Every major row contains a precise natural statement and exact Lean type.
- [ ] Every divergence is explicit and the source-facing corollary compiles.
- [ ] Required application, oracle, endpoint, and junk-value tests compile.
- [ ] Counterexample/anti-target searches are recorded without overstating negative results.
- [ ] `lake build` passes at the frozen revision.
- [ ] Production and review solution/test files contain no `sorry` or `admit`.
- [ ] Every headline `#print axioms` result is recorded and permitted.
- [ ] Comparator passes against independently authored trusted challenges, or the batch is clearly
      marked incomplete with a concrete infrastructure follow-up.
- [ ] The independent first-pass review is present and every finding has a disposition.
- [ ] No P0/P1 finding remains open; P2 limitations are visible in the PR.
- [ ] Telemetry is measured and scoped, or honestly marked unavailable.
- [ ] `SUMMARY.md`, the topic card, `docs/VERIFICATION.md`, and `AXIOM_AUDIT.md` agree.

If production declarations change during repair, create a new review revision and rerun, at
minimum, correspondence, affected cases, counterexamples, axiom printing, Comparator, dependency
audits, and the repository build. Downstream theorems depending on the changed type require fresh
review.

## 13. PR review-summary template

Copy the substantive content of `SUMMARY.md` into the PR description:

```markdown
## Automated formalization review

- Reviewed commit: `<sha>`
- Source/scope: `<source id, edition, chapter/pages>`
- Inventory: `<N>` required results; `<proved>/<documented divergence>/<missing>`
- Independent reviewer: `<agent/model/date>`
- Review mode: `<internal or adversarial-sandboxed>`
- Build: `<command and result>`
- Comparator: `<passed>/<failed>/<not run and why>`
- Axiom policy: `<permitted set>`; `<exceptions or none>`

| Source | Natural statement | Lean declaration | Cases | Counterexample search | Comparator | Axioms | Independent verdict | Formalization time/tokens | Review time/tokens |
|---|---|---|---|---|---|---|---|---|---|
| ... | ... | ... | ... | ... | ... | ... | ... | measured/not measured | measured/not measured |

### Findings and limitations

| Severity | Result | Evidence | Disposition |
|---|---|---|---|
| ... | ... | ... | ... |

### Completion statement

State exactly what was reviewed. If anything is missing, modulo an axiom, internally rather than
adversarially checked, or inconclusive, say so here. Do not write “all results” unless the source
inventory demonstrates it.
```

The PR table must include time and token usage for each major theorem when measured, as well as
separate shared-infrastructure and review rows. Its total must be the sum of disjoint windows; do
not double-count shared work or present reconstructed values as measurements.

## 14. Minimum manual command sequence

The review remains possible when Lean MCP, agent wrappers, or Comparator are unavailable locally.
The minimum manual sequence is:

```sh
git status --short
git rev-parse HEAD
lake env lean --version
lake build
lean4-skills-sorry-analyzer . --report-only
lean4-skills-check-axioms-inline . --report-only
RUN=audit/reviews/chapter-05/2026-01-01-deadbeef
lake env lean "$RUN/cases/CaseFile.lean"
lake env lean "$RUN/counterexamples/CounterexampleFile.lean"
lake env lean "$RUN/AxiomAudit.lean"
```

Run Comparator separately under its pinned, documented trust conditions. If a listed helper is
missing, record that fact and perform the `rg` inspection plus the explicit `#print axioms` fallback
described above. Never claim LSP goal inspection, external-agent review, Comparator, or a sandboxed
check when it was not actually used.

## 15. Automation design requirements

When implementing scripts or CI for this protocol, preserve these properties:

- idempotent runs keyed by scope and commit;
- machine-readable manifest data plus human-readable Markdown;
- one-to-one coverage checks between inventory rows, challenge names, axiom results, and verdicts;
- direct compilation of every committed review Lean file;
- stale-review detection when declaration types or dependencies change;
- exact command/tool-version capture and nonzero exit propagation;
- no network access or mutation during the read-only review phase except fetching explicitly pinned
  tools/sources;
- no automatic conversion of `INCONCLUSIVE` or `not run` to pass;
- no generation of the trusted challenge from the production theorem type;
- no use of an LLM's self-reported success as mechanical evidence;
- no estimates masquerading as measured time or tokens.

Prefer small scripts under `scripts/review/` and a CI job that invokes them. Do not add placeholder
scripts or fabricate successful logs merely to satisfy this layout. Until automation exists, the
manual artifacts and gates in this file are authoritative.

## 16. Why the layers are all necessary

The failure modes are complementary:

| Evidence | What it catches | What it cannot establish alone |
|---|---|---|
| Correspondence table | missing hypotheses, wrong domains, incomplete source inventory | kernel trust or actual proof dependencies |
| Application/boundary tests | unusable general theorem, hidden arguments, endpoint and junk behavior | universal truth or source equivalence by themselves |
| Independent oracle tests | definition/normalization mistakes on checked instances | untested cases |
| Counterexample and anti-target search | false claims and unjustified strengthenings | truth when no witness is found |
| `#print axioms` and sorry scan | hidden trust assumptions and proof holes | natural-language fidelity |
| Comparator | exact challenge/solution statement, permitted axioms, kernel acceptance | whether the challenge translated the source correctly |
| Independent agent | producer blind spots, inventory gaps, circular reasoning in the review | mechanical certainty without compiling evidence |

The review is complete only when these layers agree. A discrepancy is a finding to investigate,
not a reason to select whichever layer gives the preferred answer.
