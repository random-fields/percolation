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

## Numbered supporting-result inventory

The rows below were checked directly against the repository copy of the second edition, rather
than inferred from declaration names.  A grouped row means that the source equations form one
proof window; it does not mark any member of the group proved unless the status says so.

| Source, page | Source role or statement | Lean disposition | Status / fidelity note |
|---|---|---|---|
| (7.3)–(7.4), p. 148 | `p_c(2kF+B(k)) ≤ p_c+η`; specializing `F=ℤ²×{0}` identifies the thickening with a translated slab. | `regionCriticalProbability_thickening_le_add`; `cubicDilatedThickening_eq_minkowskiSum`; slab identification target | geometric Minkowski identity proved; critical inequality and exact slab identity target |
| (7.5)–(7.8), p. 150 | Distinguished face/quadrant, layered region `T(m,n)`, seeds, and random target `K(m,n)`. | `seededBoundaryQuadrant`; `seededBoundaryLayerRegion`; `cubicSeedEvent`; `seededBoundaryPoints` | proved definitions; `K(m,n)=∅` for `n<2m` proved for the necessary `d≥2` |
| (7.10)–(7.16), pp. 150–152 | Seeded boundary connection tends above `1-η`; proof via many boundary contacts, FKG symmetry, and closed exiting edges. | `seedConnectionEvent`; `seedConnection_probability_gt`; boundary-contact helper targets | event/support/measurability proved; estimates target |
| (7.18)–(7.23), pp. 152–154 | Parameter choices and exit set `U(K)`; a near-certain boundary connection forces many available exit edges. | threshold/exit-set and `sprinkledRestart_inter_history_gt` helper targets | target |
| (7.25), p. 155 | Every next queried site succeeds conditionally with probability at least `γ>p_c^site(F)`. | ratio-free finite-history hypothesis for `siteExploration_infinite_probability_pos` | target; null histories will not be divided by zero |
| (7.26)–(7.34), pp. 155–160 | Dynamic-block parameters, monotone revealed thresholds, conditional block success, and the `p+η` bound on every revealed edge. | `BoundaryThresholdProfile`; `GrimmettMarstrandBlock`; fresh-support/steering theorems | threshold vocabulary proved; block geometry and estimates target |
| (7.37)–(7.51), pp. 165–169 | Half-space zero-one step, top/side contact counts, disjoint seeds, and FKG distribution over all twelve subfacets. | `exists_halfSpaceBrick_good_probability_gt` helper suite | faithful finite good-brick event proved; probability/zero-one arguments target |
| (7.53)–(7.56), pp. 169–174 | If brick goodness exceeds `1-ν`, at most 125 fresh good bricks per tube give step probability at least `π^125`. | `halfSpaceTheta_pos_of_goodBrick_probability_gt`; rotated-placement/overlap targets | placement vocabulary proved; explicit 125-brick stacking target |
| (7.57)–(7.60), pp. 177–178 | Coarse boxes are centered at `nx`; good-block indicators are stationary and `3d`-dependent. | `epsilonGoodBlockCenter`; `epsilonGoodBlockField`; `epsilonGoodBlockLaw_kDependent`; translation-stationarity target | center and actual `3d` dependence proved for `n≥1`; stationarity and selected-cluster transport target |
| (7.62), pp. 178–179 | Above `p_c`, `P_p(B(n) is ε-good)→1`. | `epsilonGoodBox_probability_tendsto_one` | target |
| (7.63), p. 179 | Stochastic domination is comparison of expectations of every bounded increasing measurable function. | `StochasticallyDominates`; `stochasticallyDominates_of_measureReal_le` | proved, including both event consequence and layer-cake converse for probability laws |
| (7.64), p. 179 | Uniform one-step conditional lower bounds along an enumeration imply domination of iid sites. | `iidBoolEventMass_le_of_hasSequentialLowerBound`; `finiteSequentialLowerBound_stochasticallyDominates`; countable `sequentialLowerBound_stochasticallyDominates` target | finite ratio-free Boolean-cube kernel and exact expectation-level measure theorem proved; countable-extension proof window remains |
| (7.66)–(7.67), p. 179 | A `k`-dependent field with one-site density at least `δ` dominates iid density `π(δ)`. | `exists_lssDominationDensity` | target |
| (7.69)–(7.75), pp. 180–181 | Exponentially likely order-`r^(d-1)` disjoint crossings; slice crossings, independent slice family, and ACCFR sprinkling. | `maxEdgeDisjointCrossings_probability_ge`; `maxEdgeDisjointSquareRectangleCrossings`; `EdgeMenger.isEdgeReachable_iff_exists_pairwise_edgeDisjoint_paths`; existing `interiorDepth` inequality | arbitrary finite edge Menger and bounded crossing count proved; probability estimates and the set-to-set adapter target |
| (7.70), p. 180 | High-density iid site percolation crosses a square with failure exponentially small in its scale. | `siteSquareRectangleCrossingEvent`; `siteSquareRectangleCrossingProbability`; exponential bound target | faithful finite site event/support/measurability/increasingness proved |
| (7.76)–(7.80), pp. 181–182 | Finite thick slabs `S_n(L)`, `T_n(L)` and uniform positive pair-connection bounds. | `exists_uniform_slabConnection_lowerBound` and region definitions | target |
| (7.82)–(7.88), pp. 182–185 | FKG corner connections and bounded finite-energy modifications establish (7.79)–(7.80). | slab-corner and modification helper targets | target |
| (7.90)–(7.96), pp. 186–188 | Annular peeling: each layer coalesces two arms with a uniform positive conditional chance. | `twoArmSeparation_probability_le_exp` helpers | event/measurability/self endpoint proved; peeling estimates target |
| (7.98)–(7.103), pp. 188–189 | A dense interior set of infinite-arm vertices coalesces into an all-direction crossing cluster. | `largeCrossingCluster_probability_tendsto_one`; density law | finite large-cluster event proved; probability and density law target |
| (7.105)–(7.109), pp. 190–191 | Coordinate strip peeling bounds a second diameter-`m` cluster by a geometric factor. | `secondMacroscopicCluster_probability_le` helpers | finite event/measurability and impossible endpoint proved; estimate target |
| (7.110)–(7.113), pp. 191–193 | Supercritical planar long-rectangle crossing estimate and the four boundary-tube consequence. | `squareRectangleCrossingEvent`; exponential rectangle theorem target | bond event/support/measurability proved; exponential estimate target |
| (7.114)–(7.122), pp. 193–195 | LSS dilution: choose `α,ρ`, partition nearby revealed zeros/ones, inductively retain conditional density `α`, then dominate iid `αρ`. | scalar parameter, dilution law, and induction targets under `exists_lssDominationDensity` | target |

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
| Half-space bricks | Dimension-uniform facets, facet-parallel seed planes, and the finite good-brick event. | `halfSpaceBrick`, `BrickFacetKind`, `brickFacetSeedNormal`, `brickFacetSeedCenters`, `brickSeedConnectionEvent`, `halfSpaceBrickGoodEvent` | proved slice | Target seeds lie wholly in their subfacet; paths join the central and target seed vertex sets using no underside edge. `brickFacetKind_card` gives four top and eight side subfacets in dimension three. |
| Static boxes | Finite components, diameters, crossing predicates, and a canonical largest-component selector. | `finiteBoxOpenGraph`, `boxComponentDiameter`, `boxComponentIsCrossing`, `boxLargestCluster`, `boxComponentKey_injective` | proved slice | The tie-break key uses coordinates relative to the center. The theorem transporting the selected component under translations is still open. |
| Static finite support | Good-box predicate depends only on internal box edges. | `finiteBoxOpenGraph_eq_of_agree`, `FiniteBoxGraph.IsEpsilonGood`, `dependsOn_epsilonGoodBoxEvent`, `measurableSet_epsilonGoodBoxEvent` | proved slice | Graph-parametric factoring resolves dependent-component transport correctly. |
| Static finite bad events | Finite-cylinder definitions and basic endpoint checks for large crossing and second macroscopic components. | `largeCrossingClusterEvent`, `dependsOn_largeCrossingClusterEvent`, `measurableSet_largeCrossingClusterEvent`, `secondMacroscopicClusterEvent`, `dependsOn_secondMacroscopicClusterEvent`, `measurableSet_secondMacroscopicClusterEvent`, `secondMacroscopicClusterEvent_eq_empty_of_two_mul_lt` | proved slice | All probability estimates remain targets. |
| Two-arm event | Annular two-arm separation event and its self-endpoint check. | `twoArmSeparationEvent`, `measurableSet_twoArmSeparationEvent`, `twoArmSeparationEvent_self`, `scaledBoxRadius` | proved slice | The exponential estimate remains a target. |
| Chapter 11 rectangle kernel | Finite left-right crossing event and bounded maximum of disjoint crossings. | `squareRectangleCrossingEvent`, `maxEdgeDisjointSquareRectangleCrossings`, `hasEdgeDisjointSquareRectangleCrossings_iff_le_max` | proved slice | The maximal-count interface is restricted to positive width; at width zero unlimited duplicate nil walks make an unrestricted maximum ill-posed. |
| General finite edge Menger | `k`-edge reachability is equivalent to `k` pairwise edge-disjoint paths. | `EdgeMenger.IsUnitFlow`, `EdgeMenger.exists_residual_path_of_isEdgeReachable_succ`, `EdgeMenger.exists_unitFlow_of_isEdgeReachable`, `EdgeMenger.exists_pairwise_edgeDisjoint_paths_of_unitFlow`, `EdgeMenger.isEdgeReachable_iff_exists_pairwise_edgeDisjoint_paths` | proved slice | Constructive integral augmenting-flow proof; no max-flow axiom or external graph theorem. This is shared Chapter 11 infrastructure and is telemetered separately from Chapter 7. |
| Stochastic-order vocabulary | Expectation definition, event consequence, iid ordering, monotone-coupling bridge, finite-range dependence. | `StochasticallyDominates`, `StochasticallyDominates.measureReal_le`, `stochasticallyDominates_iff_measureReal_le`, `HasMonotoneCoupling`, `HasMonotoneCoupling.stochasticallyDominates`, `setBernoulli_stochasticallyDominates`, `KDependent`, `setBernoulli_kDependent` | proved slice | The iid theorem checks the direction of domination. The coupling theorem derives the exact expectation formulation from an almost-sure coordinatewise inclusion. LSS remains a target. |

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
- In dimension at least two, `K(m,n)=∅` when `n<2m`:
  `seededBoundaryPoints_eq_empty_of_lt_two_mul`.

## Focused Chapter 11 prerequisites still open

- `squareCriticalProbability_eq_half`.
- Exponential long-rectangle crossing estimate corresponding to 7.110.
- High-density site rectangle estimate corresponding to 7.70.
- The Chapter 11 Lemma 11.22 crossing adapter (arbitrary-cardinality finite edge Menger itself is
  now proved).

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
| Independent review remediation, faithful brick geometry, and checkpoint verification | 4416s | 5517s | 1101s | 1,178,200 | 1,413,658 | 235,458 |
| Direct source inventory, finite static events, rooted exploration limit, stochastic-order layer cake, and site crossings | 5517s | 6466s | 949s | 1,413,658 | 1,733,685 | 320,027 |
| General finite edge Menger (Chapter 11 shared prerequisite) and monotone-coupling bridge | 6466s | 7052s | 586s | 1,733,685 | 1,856,480 | 122,795 |
| Finite sequential domination criterion (7.64 kernel and measure bridge) | 7052s | 7804s | 752s | 1,856,480 | 2,068,815 | 212,335 |
| **Infrastructure subtotal** |  |  | **7804s** |  |  | **2,068,815** |

The final measured window contains both the Chapter 11 edge-Menger prerequisite and the Chapter
7 coupling bridge because its intermediate boundary snapshot was missed.  It is retained as one
disjoint measured row; no reconstructed split is reported as measured telemetry.

Documentation, Git operations, and final PR composition are excluded from theorem telemetry but
will receive separate non-theorem rows in the frozen review run.
