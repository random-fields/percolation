# Adversarial searches

The committed Lean file contains checked anti-targets. Additional searches and dispositions:

- Theorem 6.1: strict inequality at radius zero was refuted in the preliminary frozen-against
  case file `../2026-07-10-worktree/cases/Theorem61.lean`.
- Theorem 6.14: reversed subcritical monotonicity was refuted using strict antitonicity; including
  `b=1` in the logarithmic ratio formula was rejected because its denominator is zero.
- Proposition 6.47: the missing `x != 0` variant is rejected by the checked zero denominator.
- Theorem 6.75: the book's unshifted all-`n>=1` strict exponential claim is refuted at `n=1`.
- Lemma 6.87: omitting finiteness is refuted by the integer path with every integer terminal;
  removing any terminal separates terminals on its two sides. This infinite object is recorded
  mathematically rather than encoded as a large finite search, because every finite path does
  have a removable endpoint.
- Tree-graph sums: replacing `ENNReal.tsum` by a real `tsum` at arbitrary density is rejected;
  nonsummable real `tsum` has Lean's junk value zero.
- Theorem 6.108: attempted weakening to real differentiability is not accepted as a translation;
  the checked endpoint case exercises `AnalyticAt`, which includes a genuine neighborhood.

Failure to find a further counterexample is inconclusive and is not reported as a proof.

