# Topic 07 — Dynamic and Static Renormalization

Source id: `grimmett-percolation-1999`

Source: Geoffrey Grimmett, *Percolation*, 2nd edition, Chapter 7, pp. 146–196.

This card is the live source-to-formal inventory for the Chapter 7 autoformalization.  A
declaration is marked `proved slice` only when the cited declaration compiles without `sorry` or
a new axiom.  Headline results remain `target` until their complete source-facing statements and
all prerequisite estimates are proved.

## Headline correspondence

| Source result | Informal statement | Lean declaration | Dependencies | Status | Divergence / review note | Time | Tokens |
|---|---|---|---|---|---|---:|---:|
| Theorem 7.2(a) | An infinite connected region with critical probability below one has a sufficiently thick dilation whose critical probability is at most `p_c + η`. | `regionCriticalProbability_thickening_le_add` | 7.9, 7.17, 7.24; steering blocks | target | Arbitrary connected `F` must be retained. | — | — |
| Theorem 7.2(b) | Slab critical probabilities decrease to the cubic critical probability. | `slabCriticalProbability_tendsto_cubicCriticalProbability` | 7.2(a), planar choice of `F` | target | `cubicSlab 2 k = Set.univ` is already proved. | — | — |
| Lemma 7.9 | A central box connects with probability greater than `1-η` to a seeded point in a boundary quadrant. | `seedConnection_probability_gt` | seed support, FKG, boundary contacts | target | Event and measurability are proved; probability estimate remains. | — | — |
| Lemma 7.17 | Uniform sprinkling/restart estimate conditional on a boundary history. | `sprinkledRestart_inter_history_gt`; `sprinkledRestart_conditionalProbability_gt` | 7.9, threshold coupling | target | Primary form must be ratio-free on null histories. | — | — |
| Lemma 7.24 | Uniformly supercritical exploration steps produce an infinite occupied cluster with positive probability. | `siteExploration_infinite_probability_pos` | sequential domination | target | Deterministic finite-history kernel is proved. | — | — |
| Theorem 7.35 | Half-space percolation vanishes at the critical point. | `halfSpaceTheta_critical_eq_zero` | 7.36, 7.52, finite-event continuity | target | Half-space connectedness/root independence are proved. | — | — |
| Lemma 7.36 | Positive critical half-space percolation yields arbitrarily reliable good bricks. | `exists_halfSpaceBrick_good_probability_gt` | brick facets, horizontal zero-one law | target | Finite good-brick event is defined and measurable. | — | — |
| Lemma 7.52 | Sufficiently reliable good bricks imply positive half-space percolation. | `halfSpaceTheta_pos_of_goodBrick_probability_gt` | brick exploration, 7.24 | target | Dimension-dependent overlap constant must be explicit. | — | — |
| Theorem 7.61 | Above criticality, the probability of an `ε`-good box tends to one. | `epsilonGoodBox_probability_tendsto_one` | 7.89, 7.97, 7.104; planar 7.110 in `d=2` | target | Good-box event is now a proved finite cylinder. | — | — |
| Theorem 7.65 | High-density `k`-dependent site fields dominate a high-density iid field. | `exists_lssDominationDensity` | 7.64, dilution 7.114–7.122 | target | Measure-level expectation orientation has an iid coupling oracle test. | — | — |
| Theorem 7.68 | A box has order `r^(d-1)` edge-disjoint crossings except with exponentially small failure probability. | `maxEdgeDisjointCrossings_probability_ge` | 7.61, 7.65, 7.70, sprinkling, general edge Menger | target | Source-facing real inequality must avoid an implicit rounding convention. | — | — |
| Lemma 7.78 | Uniform positive finite-thick-slab connection probabilities. | `exists_uniform_slabConnection_lowerBound` | 7.2, FKG, finite energy | target | `d ≥ 3`. | — | — |
| Lemma 7.89 | Two macroscopic arms fail to coalesce with exponentially small probability. | `twoArmSeparation_probability_le_exp` | 7.78, annular peeling | target | Integer-radius primary statement; real scaling is a ceiling corollary. | — | — |
| Lemma 7.97 | A large box contains a dense crossing cluster with probability tending to one. | `largeCrossingCluster_probability_tendsto_one` | density law, 7.89 | target | Must not use the unresolved pointwise ergodic adapter. | — | — |
| Lemma 7.104 | A second macroscopic cluster has the stated polynomial-times-exponential upper bound. | `secondMacroscopicCluster_probability_le` | 7.78, strip peeling | target | Deterministic impossibility for `m>2n` is proved. | — | — |

## Proved infrastructure correspondence

| Source location | Informal role | Lean declarations | Status | Review note |
|---|---|---|---|---|
| §7.1 induced regions | Bond connections constrained to a vertex region; root-free and rooted critical quantities. | `cubicRegionGraph`, `connectionEventWithinVertices`, `hasInfiniteOpenClusterInVertices`, `regionThetaFrom`, `regionHasInfiniteClusterProbability`, `regionCriticalProbability` | proved slice | Infinite events are reindexed by countable finite path witnesses and are measurable. |
| §7.1 connected-region adapters | Rooted probabilities vanish together in a connected region. | `bernoulliBondMeasure_real_connectionWithin_mul_regionThetaFrom_le`, `regionThetaFrom_eq_zero_iff_of_connected`, `regionHasInfiniteClusterProbability_eq_zero_iff_regionThetaFrom_eq_zero_of_connected` | proved slice | Uses constrained FKG surgery; handles `p=0` separately. |
| §7.1 region critical adapters | Monotonicity and critical zero/positive sides. | `regionCriticalProbability_anti`, `regionHasInfiniteClusterProbability_eq_zero_of_lt_critical`, `regionHasInfiniteClusterProbability_pos_of_critical_lt` | proved slice | Critical probability is root-free, avoiding arbitrary roots in translated regions. |
| §7.1 site percolation | Site-open clusters, critical density, and endpoint adapters. | `siteOpenGraph`, `siteConnectionEvent`, `hasInfiniteSiteCluster`, `siteTheta`, `siteCriticalProbability`, `siteTheta_eq_zero_of_lt_criticalProbability`, `siteTheta_pos_of_criticalProbability_lt` | proved slice | A closed root is excluded explicitly; raw graph reachability alone would incorrectly include it. |
| Slab/half-space geometry | Coordinate-convex induced regions are connected. | `CubicCoordinateBetween`, `exists_cubicWalk_support_between`, `cubicRegionGraph_connected_of_coordinateConvex`, `cubicRegionGraph_cubicSlab_connected`, `cubicRegionGraph_cubicHalfSpace_connected` | proved slice | Supplies actual constrained walks, not a connectedness axiom. |
| Equations 7.5–7.10 | Seed, random target set `K(m,n)`, and central connection event. | `cubicSeedEvent`, `seededBoundaryQuadrant`, `IsSeededBoundaryPoint`, `seedConnectionEvent`, `measurableSet_seedConnectionEvent` | proved slice | Existential seed centers are a genuine countable union. |
| Equation 7.17 safety | Ratio-free conditional bound vocabulary and common inhomogeneous thresholds. | `HistorySuccessLowerBound`, `HistorySuccessLowerBound.conditionalRatio`, `BoundaryThresholdProfile`, `BoundaryThresholdProfile.configuration_mono` | proved slice | Division is available only after positive history mass is supplied. |
| Exploration histories | Deterministic accepted/rejected/frontier state machine. | `SiteExplorationState`, `SiteExploration`, `SiteExploration.step`, `SiteExploration.stateAfter`, `SiteExploration.step_wellFormed`, `SiteExploration.stateAfter_wellFormed` | proved slice | The fixed linear order is the explicit enumeration rule. |
| Half-space bricks | Dimension-uniform facets, seed planes, and good-brick event. | `halfSpaceBrick`, `BrickFacetKind`, `brickFacet`, `brickSeedPlane`, `halfSpaceBrickGoodEvent` | proved slice | `brickFacetKind_card`; dimension three has exactly four top and eight side subfacets. |
| Static boxes | Finite components, diameters, crossing predicates, canonical largest component. | `finiteBoxOpenGraph`, `boxComponentDiameter`, `boxComponentIsCrossing`, `boxLargestCluster`, `boxComponentKey_injective` | proved slice | Tie-break uses coordinates relative to the center and is therefore translation-neutral. |
| Static finite support | Good-box predicate depends only on internal box edges. | `finiteBoxOpenGraph_eq_of_agree`, `FiniteBoxGraph.IsEpsilonGood`, `dependsOn_epsilonGoodBoxEvent`, `measurableSet_epsilonGoodBoxEvent` | proved slice | Graph-parametric factoring resolves dependent-component transport correctly. |
| Two-arm and second-cluster events | Finite annular/static bad events and basic endpoint checks. | `twoArmSeparationEvent`, `twoArmSeparationEvent_self`, `secondMacroscopicClusterEvent_eq_empty_of_two_mul_lt`, `scaledBoxRadius` | proved slice | Probability estimates remain targets. |
| Chapter 11 rectangle kernel | Finite left-right crossing event and bounded maximum of disjoint crossings. | `squareRectangleCrossingEvent`, `maxEdgeDisjointSquareRectangleCrossings`, `hasEdgeDisjointSquareRectangleCrossings_iff_le_max` | proved slice | The maximal-count interface is restricted to positive width; at width zero unlimited duplicate nil walks make an unrestricted maximum ill-posed. |
| Stochastic-order vocabulary | Expectation definition, event consequence, iid ordering, finite-range dependence. | `StochasticallyDominates`, `StochasticallyDominates.measureReal_le`, `setBernoulli_stochasticallyDominates`, `KDependent`, `setBernoulli_kDependent` | proved slice | The iid theorem checks the direction of domination. LSS remains a target. |

## Adversarial checks already encoded

- `squareRectangleCrossingEvent 0 n = Set.univ`, while
  `maxEdgeDisjointSquareRectangleCrossings 0 n ω = 0` is deliberately a guarded convention:
  positive-width hypotheses are required for the maximum theorem.
- The completely closed positive-width rectangle has zero edge-disjoint crossings:
  `maxEdgeDisjointSquareRectangleCrossings_empty`.
- `twoArmSeparationEvent d n N x x = ∅`.
- `secondMacroscopicClusterEvent d m n x = ∅` when `2*n < m`.
- `Fintype.card (BrickFacetKind 3) = 12` by kernel-checked computation.
- `siteTheta G 0 = 0`; the proof detects the junk closed-root value that raw reachability would
  otherwise introduce.
- `cubicSlab 2 k = Set.univ`.

## Focused Chapter 11 prerequisites still open

- `squareCriticalProbability_eq_half`.
- Exponential long-rectangle crossing estimate corresponding to 7.110.
- High-density site rectangle estimate corresponding to 7.70.
- Arbitrary-cardinality finite edge Menger and the Chapter 11 Lemma 11.22 adapter.

These remain explicit blockers; no Chapter 11 axiom or theorem parameter has been introduced.

## Measured telemetry

The goal tracker is `019f486f-e045-7e71-b571-5b6ad19e3cb4`.  Figures below are direct tracker
snapshots, not reconstructions.  These broad infrastructure windows will not also be charged to
individual theorem rows.

| Window | Start time | End time | Time | Start tokens | End tokens | Tokens |
|---|---:|---:|---:|---:|---:|---:|
| Initial Chapter 11 crossing and region/site/static foundation | 0s | 2238s | 2238s | 0 | 692,564 | 692,564 |
| Region root-independence, static finite support, exploration, and brick infrastructure | 2238s | 3666s | 1428s | 692,564 | 1,024,002 | 331,438 |
| Finite-event continuity, coarse-block separation, and finite seed support | 3666s | 4416s | 750s | 1,024,002 | 1,178,200 | 154,198 |
| **Infrastructure subtotal** |  |  | **4416s** |  |  | **1,178,200** |

Documentation, Git operations, and final PR composition are excluded from theorem telemetry but
will receive separate non-theorem rows in the frozen review run.
