# Chapter 11 transitive axiom audit

Authoritative command:

```sh
lake env lean audit/reviews/chapter-11/2026-07-16-0708489/AxiomAudit.lean
```

Exit status: `0`.

The output contains no `sorryAx` and no unledgered project axiom.  The exact dependency classes
are:

| Declaration group | Transitive axiom set beyond `propext`, `Classical.choice`, `Quot.sound` |
|---|---|
| `tubeConnectivityDecayRate_properties` | none |
| `existsUnique_boundaryCircuitCrossedEdges` | itself |
| `openClustersPerVertex_square_duality` | itself |
| `bernoulliBondMeasure_real_grimmettRectangleCrossingEvent_half` | `grimmettRectangleDualTraceEquiv` |
| `theta_two_half_eq_zero`, `cubicCriticalProbability_two_eq_half` | `grimmettRectangleDualTraceEquiv`; `rswAnnulusOpenCircuitProbability_le_half_barrier`; `rswCircuitGluingIntersection_subset`; `rswGluingThreeIntersection_subset`; `rswGluingTwoIntersection_subset`; `rswThreeHalvesCrossingProbability_ge` |
| `maxEdgeDisjointSquareRectangleCrossings_probability_le_exp` | the preceding six plus `card_grimmettRectangleDualTraceEquiv_apply` |
| `rsw_gluing_inequalities` | the three `rsw*Gluing*Intersection_subset` axioms |
| `rswAnnulusOpenCircuitProbability_ge` | the three gluing axioms plus `rswThreeHalvesCrossingProbability_ge` |
| `finiteCorrelationLength_pos_lt_top` | `finiteCorrelationLength_eq_half_correlationLength_complement` plus the same six axioms used by the exact threshold |
| Each direct source theorem in `Chapter11External.lean` | that theorem's own, same-named axiom |
| `inhomogeneousSquare_criticalSurface` | `inhomogeneousSquareTheta_eq_zero_iff`, `inhomogeneousSquareTheta_pos_iff` |
| `inhomogeneousTriangular_criticalSurface` | `inhomogeneousTriangularTheta_eq_zero_iff`, `inhomogeneousTriangularTheta_pos_iff` |

In particular, `cubicCriticalProbability_two_eq_half` is a Lean proof and has no
theorem-specific axiom.  Its six project assumptions are exactly the named self-dual trace,
Russo lowest-crossing, deterministic RSW gluing, and annulus-barrier boundaries recorded in
`AXIOM_AUDIT.md`.

All project assumptions above are permitted only under the user's explicit external-reference
policy.  They are not part of the standard Lean trusted base and are not described as such.
