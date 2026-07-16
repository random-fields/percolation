# AXIOM_AUDIT

Project axioms are present only at the explicitly cited external-reference boundary for Grimmett
Chapter 11.  All are listed below and vetted in
`audit/vetting/chapter-11-external-results.md`.

## Policy

- Standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`) are acceptable.
- Any project axiom must be a true, named, cited theorem with a discharge plan.
- Every project axiom must have a vetting card under `audit/vetting/`.
- Comparator cards in `audit/topics/` must identify which source theorem is affected.

## Current Snapshot

| declaration | file | source | status |
|---|---|---|---|
| `existsUnique_boundaryCircuitCrossedEdges` | `Planar/External.lean` | Grimmett Prop. 11.2; Kesten (1982), p. 386 | external topology; discharge by a combinatorial Jordan-curve proof |
| `grimmettRectangleDualTraceEquiv` | `Planar/External.lean` | Prop. 11.2 / Eq. 11.20; Kesten (1982), p. 386 | external topology; discharge from finite planar duality |
| `card_grimmettRectangleDualTraceEquiv_apply` | `Planar/External.lean` | same | weight complement for the preceding equivalence |
| `rswThreeHalvesCrossingProbability_ge` | `Planar/External.lean` | Grimmett Lemma 11.73; Russo (1981) | external lowest-crossing topology |
| `rswGluingTwoIntersection_subset` | `Planar/External.lean` | Grimmett Eq. 11.76 / Prop. 11.2 | deterministic planar gluing |
| `rswGluingThreeIntersection_subset` | `Planar/External.lean` | Grimmett Eq. 11.77 / Prop. 11.2 | deterministic planar gluing |
| `rswCircuitGluingIntersection_subset` | `Planar/External.lean` | Grimmett Eq. 11.78 / Prop. 11.2 | deterministic planar circuit extraction |
| `rswAnnulusOpenCircuitProbability_le_half_barrier` | `Planar/External.lean` | Prop. 11.2, self-dual separation | deterministic planar separation |
| `openClustersPerVertex_square_duality` | `Planar/Chapter11External.lean` | Grimmett Thm. 11.4; Kesten (1982), p. 244 | externally sourced face/component correspondence |
| `eventuallySurroundingOpenCircuit_probability_one` | `Planar/Chapter11External.lean` | Grimmett Lemma 11.13 via Prop. 11.2 | source-facing external descendant |
| `maxEdgeDisjointGrimmettRectangleCrossings_probability_le_exp` | `Planar/Chapter11External.lean` | Grimmett Lemma 11.22 via Eq. 11.20 | literal source rectangle; centered normalization is proved |
| `truncatedTwoPointConnectivity_logRate_tendsto` | `Planar/Chapter11External.lean` | Grimmett Eq. 11.23 via Prop. 11.2 | source-facing external descendant |
| `finiteCorrelationLength_eq_half_correlationLength_complement` | `Planar/Chapter11External.lean` | Grimmett Thm. 11.24 | source-facing external descendant |
| `finiteClusterSizeProbability_le_exp_neg_sqrt_of_supercritical` | `Planar/Chapter11External.lean` | Grimmett Thm. 11.25 via Prop. 11.2 | source-facing external descendant |
| `logarithmicProfileRegion_criticalProbability` | `Planar/Chapter11External.lean` | Grimmett Thm. 11.55 via 11.24 | source-facing external descendant |
| `clusterFunctionalSum_centralLimitTheorem` | `Planar/Chapter11External.lean` | Grimmett Thm. 11.63; cited CLT literature | theorem stated without book proof |
| `squareCritical_powerLaw_bounds` | `Planar/Chapter11External.lean` | Grimmett Thm. 11.89 via Prop. 11.2 / Russo | source-facing external descendant |
| `squareNearCritical_powerLaw_bounds` | `Planar/Chapter11External.lean` | Grimmett Thm. 11.93 via 11.89 | source-facing external descendant |
| `inhomogeneousSquareTheta_eq_zero_iff` | `Planar/Inhomogeneous.lean` | Grimmett Thm. 11.115 | theorem stated without book proof |
| `inhomogeneousSquareTheta_pos_iff` | `Planar/Inhomogeneous.lean` | Grimmett Thm. 11.115 | positive half of same result |
| `inhomogeneousTriangularTheta_eq_zero_iff` | `Planar/Inhomogeneous.lean` | Grimmett Thm. 11.116 | theorem stated without book proof |
| `inhomogeneousTriangularTheta_pos_iff` | `Planar/Inhomogeneous.lean` | Grimmett Thm. 11.116 | positive half of same result |

Chapter 6's frozen automated-review audit prints 41 headline and supporting declarations; every
one has exactly `[propext, Classical.choice, Quot.sound]`. See
`audit/reviews/chapter-06/2026-07-10-c4286f9/axioms.md`.
