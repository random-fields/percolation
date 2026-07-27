# Chapter 11 review summary

Production statement-fidelity result: **PASS with documented external-axiom divergences**.
Assumption-free result: **not applicable / false**.  Trusted Comparator result: **pending CI**.

The source-first inventory covers all 19 named Chapter 11 results.  Six source rows are proved
declarations (five modulo named Kesten/Russo primitives and Lemma 11.27 with standard axioms), 11
are direct external axioms, and two are wrappers over external inhomogeneous-surface axioms.  The
proved centered normalization of Lemma 11.22 is additional; the literal source rectangle remains
an explicitly cited axiom.

The independent first pass found no P0, no hidden axiom, no source-level counterexample, and no
vacuous public theorem.  It found four actionable documentation/review gaps and one missing source
consequence.  The repair:

- adds `finiteCorrelationLength_pos_lt_top` for the positivity/finiteness part of Theorem 11.24;
- replaces the ambiguous completion wording with exact proof/axiom counts;
- supplies frozen cases, counterexamples, Comparator artifacts, and transitive axiom output;
- proves the degenerate `rswThreeHalvesCrossingEvent 0 = Set.univ` sanity case;
- retains the exact source/centered-rectangle distinction for Lemma 11.22.

The focused final rereview reports **PASS**, closes F5 and F7, and finds no P0/P1.  Its sole
actionable P2 was closed by adding the complete three-part Theorem 11.24 statement to the trusted
Comparator challenge.  The unedited report remains in `independent-rerun.md`.

Local mechanical results:

- full repository build: `lake build`, 8,725 jobs, exit `0`;
- all case, counterexample, ten-challenge solution, and axiom-audit files: exit `0`;
- production scan: no `sorry` or `admit`; project axioms occur only in the three documented
  external-boundary files;
- `git diff --check`: exit `0`.

Strict `AUTOMATED_REVIEW.md` status remains **INCONCLUSIVE only for trusted Comparator**, because
the required sandbox tools are unavailable locally.  The PR CI workflow is the authoritative
trusted run.  See `independent-review.md` for the unedited first pass and `axioms.md` for the
actual kernel-reported dependency sets.

Measured tracker telemetry through the end of review (before Git/PR publication) is 23,262
seconds and 4,320,600 tokens.  The final-review window, measured by subtracting its two tracker
snapshots, is 7,051 seconds and 1,585,537 tokens.  Individual theorem windows were not captured
consistently and remain labelled **not individually measured** rather than estimated.
