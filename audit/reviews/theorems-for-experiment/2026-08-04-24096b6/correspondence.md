# Source-to-Lean correspondence

| Source result | Exact source statement | Lean declaration | Conventions and encoding | Divergence | Axioms | Independent verdict | Status |
|---|---|---|---|---|---|---|---|
| Grimmett, Theorem 3.7, printed p. 59 / PDF p. 72 | `p_c(T) < p_c(L^2)` for bond percolation | `Percolation.grimmett_theorem_3_7 : triangularCriticalProbability < cubicCriticalProbability 2` | The triangular graph is the square lattice with north-east/south-west diagonals; all three bond directions have density `p`; both thresholds use `sup {p | theta(p) = 0}`. | none | `sorryAx` plus standard axioms | `FAIL_AXIOM`; statement mapping faithful | target (`sorry`) |
| Grimmett, Theorem 11.70 and (11.71), printed p. 315 / PDF p. 328 | If `P_p(LR(l)) = tau`, then `P_p(O(l)) >= {tau(1-sqrt(1-tau))^4}^12` | `Percolation.grimmett_theorem_11_70 (p : I) (l : Nat) (hl : 1 <= l) (tau : Real) (htau : rswSquareCrossingProbability p l = tau) : grimmettRSWLowerBound tau <= rswAnnulusOpenCircuitProbability p l` | The square crossing omits boundary-to-boundary edges. Its translated box has the same probability. The annulus is `l < ||z||_infinity <= 3l`; odd parity around the central face is equivalent to surrounding the origin because `l >= 1`. | representational translation and central-face parity, with no event-level mathematical change | `sorryAx` plus standard axioms | `FAIL_AXIOM`; statement mapping faithful with representational caveat | target (`sorry`) |
| Duminil-Copin, Proposition 2.14, printed p. 19 / PDF p. 27 | For every integer `n >= 1`, `P_(1/2)[C_v([-n,n] x [-n,2n])] >= 1/128` | `Percolation.duminilCopin_proposition_2_14 (n : Nat) (hn : 1 <= n) : (1 / 128 : Real) <= duminilCopinVerticalCrossingProbability squareHalfDensity n` | The event uses every nearest-neighbor bond internal to the literal rectangle and connects its bottom side to its top side under homogeneous square-lattice bond measure. | none | `sorryAx` plus standard axioms | `FAIL_AXIOM`; statement mapping faithful | target (`sorry`) |

## Boundary and adversarial checks

- The strict inequality in Theorem 3.7 is preserved.
- The RSW exponent `4` inside the braces and outer exponent `12` are preserved; equivalently the
  second factor has total exponent `48`.
- The RSW hypothesis is an equality to the explicitly quantified real `tau`, as in the source.
- Both source domains require a positive integer scale; Lean represents this as `n : Nat` or
  `l : Nat` plus `1 <= n` or `1 <= l`.
- Proposition 2.14 uses vertical, not horizontal, crossing and the asymmetric height interval
  `[-n, 2n]`.
- No counterexample or source-valid case lost by the Lean types was identified.

Application checks are in `cases/Applications.lean`. Counterexample-search notes are in
`counterexamples/README.md`. Comparator was not run because the requested production artifacts
are explicitly unproved statement targets.
