# Fresh independent Chapter 6 review — commit `791f82b`

Reviewer: `/root/chapter6_final_review`, strictly read-only. Frozen production commit:
`791f82bd0028039b35d45f1597d1af64f9f1b2e0`.

## Bottom line

- **Statement fidelity of production declarations: PASS**, with documented encoding divergences.
- **Axiom discipline: PASS.** Audited declarations use only `propext`, `Classical.choice`, and
  `Quot.sound`; no project axioms or production `sorry` were found.
- **Full `AUTOMATED_REVIEW.md` release gate: BLOCK / INCONCLUSIVE.** Comparator was unavailable,
  and the producer-authored challenge at review time was neither independent nor trusted evidence.
- The false literal readings of 6.75 and 6.87 must remain `rejected/anti-target`; their corrected
  theorems pass separately.
- No files were edited during the review.

Lean was 4.30.0 (`d024af…`), Mathlib was
`c5ea00351c28e24afc9f0f84379aa41082b1188f`, and no callable Lean MCP tool was exposed. The
reviewer used `lake env lean`, `lake build`, `rg`, and `pdftotext` and made no interactive-goal
inspection claim.

## Per-result verdicts

The strict-protocol column remains `INCONCLUSIVE` wherever Comparator is mandatory but unavailable.

| Source result | Independent statement/axiom assessment | Strict protocol | Notes |
|---|---|---|---|
| 6.1 / (6.2) | `PASS` | `INCONCLUSIVE` | Correct susceptibility hypothesis, positive rate, and non-strict box-radius tail bound. |
| 6.10 | `PASS_DOCUMENTED_DIVERGENCE` | `INCONCLUSIVE` | Denominator form is equivalent and avoids endpoint junk. |
| 6.14 / 6.40 | `PASS_DOCUMENTED_DIVERGENCE` | `INCONCLUSIVE` | Endpoint-safe extension and necessary denominator conditions are explicit. |
| 6.44 | `PASS_DOCUMENTED_DIVERGENCE` | `INCONCLUSIVE` | Axis rate and two-sided estimate match after explicit positivity conventions. |
| 6.47 | `PASS_DOCUMENTED_DIVERGENCE` | `INCONCLUSIVE` | `x ≠ 0` avoids the source's undefined lower display at zero. |
| 6.49 and correlation length | `PASS_DOCUMENTED_DIVERGENCE` | `INCONCLUSIVE` | Continuity, strict monotonicity, zero-density limit, critical divergence, and `ξ≤χ` are present; zero uses a clamped real adapter. |
| Literal all-`n≥1` 6.75 | `FAIL_COUNTEREXAMPLE`; `rejected` | `FAIL_COUNTEREXAMPLE` | At `n=1` the tail is one. |
| Corrected 6.75 | `PASS` | `INCONCLUSIVE` | Eventual decay has explicit threshold `N`. |
| 6.78 / 6.80 / 6.82–6.83 | `PASS` | `INCONCLUSIVE` | Full `0<p<1` exact-size rate, exact prefactor, finite-tail distinction, positivity, and `ζ≤φ`. |
| Literal arbitrary-set 6.87 | `FAIL_STATEMENT`; `rejected` | `FAIL_STATEMENT` | False on a bi-infinite path. |
| Corrected finite 6.87 | `PASS` | `INCONCLUSIVE` | Nonempty `Finset` formulation is correct and sufficient downstream. |
| 6.89 | `PASS_DOCUMENTED_DIVERGENCE` | `INCONCLUSIVE` | ENNReal summation is endpoint-safe. |
| 6.93 | `PASS` | `INCONCLUSIVE` | General skeleton bound is appropriately stated. |
| 6.95–6.96 | `PASS_DOCUMENTED_DIVERGENCE` | `INCONCLUSIVE` | Count is `Nat.card` of a canonical insertion-code type; recurrence is primary and the concrete decoder has equal cardinality. Residual P2: no quotient-by-graph-isomorphism equivalence. |
| 6.97 | `PASS` | `INCONCLUSIVE` | Weighted series is identified with the literal expectation and the square-root bound applies to it. |
| 6.102 | `PASS` | `INCONCLUSIVE` | Exact normalization and factor remain correct. |
| 6.108 | `PASS_DOCUMENTED_DIVERGENCE` | `INCONCLUSIVE` | Analytic series have physical cluster-density and susceptibility identity theorems. |

## Repair-specific conclusions

`clusterSizeAtLeast_exponential_decay_of_lt_critical` is the correct repaired eventual form of
6.75; the compiled anti-target proves the size-at-least-one probability is one. For 6.87,
`exists_terminal_deletion_preserves_connected` is the correct finite theorem and the unrestricted
reading is rejected.

The skeleton circularity is materially removed: `connectivitySkeletonCount` is the cardinality of
a recursive canonical type whose successor records one of `2n-3` insertion edges. The recurrence,
odd double-factorial, factorial form, and equality with the concrete decoder cardinality are
derived theorems. The decoder supplies the graph geometry used by the tree-graph proof.

For 6.97, `clusterSizeExponentialMoment`,
`clusterSizeWeightedExpMoment_eq_exponentialMoment`, and `clusterSizeExponentialMoment_le` connect
the literal ENNReal expectation to its series and bound. The correlation-length repair supplies
continuity, strict monotonicity, and the zero-density limit alongside the existing critical
divergence. The 6.78 exact-size limit retains its full `0<p<1` range. The 6.108 series are connected
to `openClustersPerVertex` and `susceptibility.toReal` by public identity theorems.

## Trust and mechanical evidence

`lake exe cache get && lake build` exited 0 after 8,549 jobs. Every repair case,
`counterexamples/AntiTargets.lean`, `AxiomAudit.lean`, and `comparator/Solution.lean` exited 0.
Explicit `#print axioms` checks reported exactly
`[propext, Classical.choice, Quot.sound]`. A production scan found no actual `sorry`, `admit`, new
`axiom`, or `unsafe` declaration. The only holes were in producer challenge files, which were not
accepted as independent evidence.

Source inspection used the local Grimmett PDF (printed pp. 117–145, PDF pp. 130–158), including:

```sh
pdftotext -f 140 -l 145 -layout kg/textbooks/Grimmett-Percolation-2ed-1999.pdf -
pdftotext -f 145 -l 158 -layout kg/textbooks/Grimmett-Percolation-2ed-1999.pdf -
```

## Remaining protocol limitations

1. Comparator was not run in this review environment.
2. The challenge present during the review was producer-authored.
3. The rejected-source dispositions and final report were concurrent untracked evidence, not part
   of the frozen production commit.
4. The canonical skeleton code has no explicit equivalence with labelled trivalent graph
   isomorphism classes.
5. The zero-density correlation-length result uses a documented clamped adapter.

The first three block a claim that every mandatory automated-review gate passed, but they expose
no remaining false production theorem.
