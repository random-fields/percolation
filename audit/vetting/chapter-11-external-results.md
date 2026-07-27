# Vetting card — Grimmett Chapter 11 external-reference boundary

Date: 2026-07-16

Last reconciled with the exact Theorem 11.11 transitive audit: 2026-07-26.

Source: Geoffrey Grimmett, *Percolation*, 2nd ed., Chapter 11, pp. 282–332.

Policy: the user explicitly requested that results depending on references outside this book be
represented as axioms.  This card records why each declaration is mathematically intended to be
true, what would refute a bad encoding, and how it can eventually be discharged.

## Planar topology group

Globally retained external declarations:

- `existsUnique_boundaryCircuitCrossedEdges`;
- `grimmettRectangleDualTraceEquiv` and
  `card_grimmettRectangleDualTraceEquiv_apply`;
- `rswAnnulusOpenCircuitProbability_le_half_barrier`.

Formerly external rows which are now proved:

- `rswGluingTwoIntersection_subset` and `rswGluingThreeIntersection_subset` in
  `RSWIncidence.lean`;
- `rswCircuitGluingIntersection_subset` in `RSWCircuitIncidence.lean`;
- `rswAnnulusOpenCircuitProbability_le_half_expandedBarrier` in `AnnulusDuality.lean`, the
  expanded-annulus transfer actually used by the exact-threshold proof.

External source: Grimmett explicitly sends Proposition 11.2 to Kesten, *Percolation Theory for
Mathematicians* (1982), p. 386; the face/component correspondence used in Theorem 11.4 is also
attributed to Kesten, p. 244.

Adversarial checks:

- literal uniqueness of a bundled closed walk is false because the same geometric circuit may be
  cyclically rebased or reversed; the proposition therefore asserts uniqueness of the crossed
  primal-edge finset;
- the finite subgraph structure records both vertices and chosen edges, so its edge boundary
  includes ambient incident edges omitted from the subgraph, as in the source;
- every circuit is required to contain every subgraph vertex at odd face index and every crossed
  primal edge must lie in the edge boundary;
- the now-proved rectangle and circuit gluing theorems are deterministic event inclusions; all
  probability transport and FKG multiplication is proved separately;
- the older unexpanded barrier declaration remains a global project axiom, but the exact-threshold
  proof uses the proved expanded-annulus transfer and does not depend on that axiom.

Discharge plan: formalize a finite square-cell complex, prove the mod-two Jordan separation
theorem, identify the exterior boundary component, and derive the remaining boundary-circuit,
trace-equivalence, and legacy unexpanded-barrier declarations.  The gluing inclusions and the
expanded barrier transfer require no discharge: they are already proved.

## Lowest-crossing group

Declaration: `rswThreeHalvesCrossingProbability_ge`.

External source: Grimmett's proof of Lemma 11.73 follows Russo (1981) and explicitly calls out the
existence, uniqueness, and stopping-set property of the lowest crossing as topological input.

Adversarial checks: the axiom states only the exact probability inequality, for every
`p∈[0,1]` and natural scale, and does not postulate a lowest path selector with unjustified
measurability.  Endpoint evaluations are non-contradictory: at `r=0` the lower bound is zero and
at `r=1` it is one.

Discharge plan: construct the lowest crossing as the boundary of the finite left-reachable cell
complex and prove its stopping-set measurability.

## Exact Theorem 11.11 trust boundary

At audited Chapter 12 commit `fa86568`, both
`#print axioms Percolation.theta_two_half_eq_zero` and
`#print axioms Percolation.cubicCriticalProbability_two_eq_half` report exactly

```text
[propext, Classical.choice, Quot.sound,
 Percolation.rswThreeHalvesCrossingProbability_ge]
```

Consequently, the lowest-crossing inequality above is the only project axiom in the exact theorem
closure.  In particular:

- `cubicCriticalProbability_two_le_half` is proved through the bond-interface and subcritical
  radius-decay route and does not use the external finite-trace axioms;
- `rswGluingTwoIntersection_subset`, `rswGluingThreeIntersection_subset`, and
  `rswCircuitGluingIntersection_subset` are proved incidence theorems;
- `rswAnnulusOpenCircuitProbability_le_half_expandedBarrier`, shifted-annulus independence, the
  blocking inclusion, and `theta_eq_zero_of_iIndep_barriers` are proved;
- the global Proposition 11.2, trace-equivalence, source-facing descendant, inhomogeneous, and
  legacy unexpanded-barrier axioms remain relevant to other declarations, but are not transitive
  dependencies of Theorem 11.11.

This exact certificate must be rerun on the frozen integration revision; it is narrower than the
global Chapter 11 axiom inventory below.

## Source-facing descendants of Proposition 11.2

Declarations:

- `eventuallySurroundingOpenCircuit_probability_one`;
- `maxEdgeDisjointGrimmettRectangleCrossings_probability_le_exp`;
- `truncatedTwoPointConnectivity_logRate_tendsto`;
- `finiteCorrelationLength_eq_half_correlationLength_complement`;
- `finiteClusterSizeProbability_le_exp_neg_sqrt_of_supercritical`;
- `logarithmicProfileRegion_criticalProbability`;
- `squareCritical_powerLaw_bounds` and `squareNearCritical_powerLaw_bounds`.

Vetting notes:

- the surrounding-circuit event is the literal source event, not the earlier stronger RSW-annulus
  surrogate;
- Lemma 11.22 uses the literal rectangle `[0,n+1]×[0,n]` and an actual bounded maximum of
  pairwise edge-disjoint open walks; a centered-rectangle version is independently proved;
- finite correlation length is valued in `ℝ≥0∞`, avoiding the junk real convention `1/0=0`;
- Theorem 11.25 uses exact-size probability, not a strict or shifted tail;
- the profile theorem constrains the real function only on its source domain `[0,∞)`;
- critical/near-critical inequalities preserve strict phase hypotheses, real powers, and the
  source `n≥1` convention.

Discharge plan: once Proposition 11.2 and lowest-crossing topology are proved, follow the book's
finite-volume arguments and replace each source-facing axiom in dependency order.

## Results stated without a proof in the chapter

Declarations:

- `openClustersPerVertex_square_duality` (face/component step externally attributed);
- `clusterFunctionalSum_centralLimitTheorem` (Cox–Grimmett / strong-mixing literature);
- the four inhomogeneous zero/positive axioms underlying Theorems 11.115 and 11.116
  (original square and star–triangle literature).

Vetting notes:

- cluster density uses the existing `E(1/|C|)` normalization;
- the CLT includes the source's boundedness, off-critical, infinite-cluster constancy, growing
  interior, and positive normalized variance hypotheses, plus the mathematically implicit
  measurability of each random variable;
- inhomogeneous square `theta` is the probability that the **origin cluster** is infinite;
- the triangular graph is exactly the square lattice plus north-east diagonals;
- every density excluded by the source's `<1` hypotheses remains excluded in Lean.

Discharge plan: prove the finite Euler identity and thermodynamic limit for cluster density;
import or prove the required strong-mixing CLT; formalize the star–triangle coupling and the
inhomogeneous sharp-threshold argument.

## Mechanical evidence

- Exact transitive sets: `Percolation/Tests/Chapter11AxiomAudit.lean`.
- Source-to-Lean inventory: `audit/topics/topic-11-bond-percolation-two-dimensions.md`.
- Semantic applications: `Percolation/Tests/Chapter11Infrastructure.lean`.
- Placeholder scan and independent read-only report are recorded in the frozen Chapter 11 review
  directory.
