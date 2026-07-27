# Independent source review — preliminary findings

Reviewer task: `/root/chapter6_source_review` (read-only independent agent), 2026-07-10.

The reviewer checked the local Grimmett PDF rather than the producer's paraphrases and found:

- Theorem 6.1 should expose `2 ≤ d` and `χ(p)<∞`, not an extra `p<1` input.  The implementation
  was corrected to derive `p<1` internally.
- The lower factors proposed for (6.46) and (6.48) were transcribed incorrectly; the topic card
  now records the corrected factors.
- Theorem 6.75 needs an eventual-radius qualification or shifted exponent.
- Lemma 6.87 needs finiteness.
- General-density tree-graph sums must live in `ℝ≥0∞`.
- Equation (6.40) needs `b<1` in ratio form.
- Correlation length is source-defined only through the critical density.

These are failing findings against the original plan, not confirmations.  Their disposition must
be rechecked against the final Lean declarations.

