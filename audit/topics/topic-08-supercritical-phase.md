# Topic 08 — The Supercritical Phase

Source: `grimmett-percolation-1999`, Chapter 8, pp. 197–228.

## Scope and current status

This chapter is partially formalized, without new axioms or `sorry`.  The completed core is:

- Burton–Keane uniqueness, including the finite compatible-three-partition lemma;
- continuity of `theta` throughout the supercritical phase;
- existence and finite-prefactor bounds for the finite-cluster radius rate;
- the exact signed-hyperplane union bound (8.43) and the analytic deduction that an
  exponential hyperplane-avoidance estimate forces a positive radius rate;
- the exact even/odd gluing proof of the truncated-connectivity rate;
- the Aizenman–Delyon–Souillard lower cluster-size bound; and
- qualitative supercritical box crossing; and
- the full higher-derivative animal-series argument for the interior of Theorem 8.92, from an
  explicit compact-uniform finite-cluster tail hypothesis; and
- the exact one-edge interior/boundary balance underlying Theorem 8.99, including semantic
  identification with Grimmett's infinite-cluster edge sets, finite-box count definitions,
  aggregate directional intensity balance, positivity of the interior intensity, and the
  almost-sure pointwise density laws and ratio, conditional only on the positive radius exponent
  which is exactly the remaining conclusion of Theorem 8.21.

The complete strip-exploration argument (8.44)--(8.48) is now formalized.  In dimension at least
three it proves `a(p)>0`, compact-uniform (8.91), the interior interval form of Theorem 8.92, and
Theorem 8.99 from the single named premise `SlabCriticalApproximation d`.  That premise is exactly
the still-unfinished unconditional output of Chapter 7 Theorem 7.2; it is retained visibly in
every downstream theorem type.  The remaining Chapter 8 source work is Theorem 8.65, whose proof
explicitly omits the high-dimensional external-boundary topology, the separate planar route to
8.21, and the `p=1` endpoint of 8.92 based on (8.88).  No Chapter 7 theorem parameter or Chapter
11 external axiom is hidden inside a result marked unconditional.

## Source-to-Lean correspondence and telemetry

Time and token counters are measured by the active Chapter 8 goal tracker.  The surviving
snapshots do not separate the earlier theorem windows, so those rows are honestly labelled
`jointly measured`; no reconstructed per-theorem figure is presented as measured telemetry.

| Source result | Page | Natural-language statement | Exact Lean declaration | Status / fidelity note | Time | Tokens |
|---|---:|---|---|---|---:|---:|
| Theorem 8.1 | 197–202 | If `theta(p)>0`, almost surely there is exactly one infinite open cluster | `Percolation.unique_infiniteOpenCluster_almostSure_of_theta_pos` | proved; the number of infinite components is `ENat`-valued, finite multiplicities are eliminated by finite-energy splicing, and infinite multiplicity is eliminated by the trifurcation boundary count | jointly measured | jointly measured |
| Lemma 8.5 | 200–201 | A pairwise compatible family of distinct three-partitions of a finite set has at most `|Y|-2` members | `Percolation.ThreePartition.compatibleThreePartitions_card_le` | proved for a finite `Finset`; this is the exact finitary statement used by Burton–Keane | jointly measured | jointly measured |
| Theorem 8.8; Lemmas 8.9–8.10 | 202–205 | `theta` is right-continuous everywhere and left-continuous above `p_c`, hence continuous on `(p_c,1]` | `Percolation.theta_continuousWithinAt_right`, `Percolation.theta_continuousWithinAt_left_of_theta_pos`, `Percolation.theta_continuousWithinAt_left_of_criticalProbability_lt`, `Percolation.theta_continuousOn_supercritical` | proved; the left-limit proof uses the common-uniform coupling and the almost-sure uniqueness theorem, including the endpoint `p=1` | jointly measured | jointly measured |
| Theorem 8.18 | 205–210 | The normalized negative logarithm of the finite box-radius probability converges to a finite rate `a(p)`, with the source polynomial-times-exponential upper bound | `Percolation.finiteClusterLInfDiameterProbability_logRate_tendsto`, `Percolation.finiteBoxRadiusProbability_logRate_tendsto`, `Percolation.exists_finiteBoxRadiusProbability_le_pow_mul_exp_neg_rate` | proved for `2≤d` and `0<p<1`; uses the exact diameter gluing inequality and a shifted quasi-subadditive limit theorem | jointly measured | jointly measured |
| Theorem 8.21; equations 8.43–8.48 | 210–212 | `a(p)>0` for `p>p_c`, uniformly on compact subintervals of `(p_c,1)`; a finite cluster of box radius at least `n` hits one of the `2d` signed coordinate hyperplanes at distance `n` | front end: `Percolation.finiteBoxRadiusEvent_subset_iUnion_signedHyperplane`; contraction: `Percolation.bernoulliBondMeasure_real_history_inter_coordinateStripRestartEvent_le`, `Percolation.bernoulliBondMeasure_real_coordinateStripAvoidanceHistory_le_pow`, `Percolation.finiteClusterHitsHyperplane_probability_le_exp_of_stripTheta_pos`; assembly: `Percolation.finiteClusterRadiusDecayRate_pos_of_coordinateStrip_critical_lt`, `Percolation.finiteClusterRadiusDecayRate_pos_of_critical_lt_of_slabCriticalApproximation` | the entire Chapter 8 argument is proved, including canonical first entrances determined by strict-past bonds, arbitrary-coordinate product independence, iteration, quotient rounding, small radii, and rotation of a supercritical slab to the reference strip. The `d≥3` source conclusion retains exactly `SlabCriticalApproximation d`, the unfinished Chapter 7 input; the separate planar route remains | 14m19s front end + 29m32s strip/integration | 264,188 + 438,557 |
| Lemma 8.27 | 206–209 | Diameter probabilities satisfy the source shifted supermultiplicative gluing inequality | `Percolation.finiteClusterLInfDiameterProbability_glue_lower_bound` | proved with the exact finite-energy factor and polynomial denominator | jointly measured | jointly measured |
| Equations 8.39–8.40 | 209–210 | Diameter and finite radius tails compare up to explicit box/surface factors | `Percolation.finiteClusterLInfDiameterTailProbability_logRate_tendsto`, `Percolation.finiteBoxRadiusProbability_logRate_tendsto` | proved, including the zero-rate case rather than dividing by the rate | jointly measured | jointly measured |
| Equation 8.51 | 213 | Truncated two-point connectivity is bounded by the finite-radius probability and hence by the source prefactor | `Percolation.truncatedTwoPointConnectivity_le_finiteBoxRadiusProbability`, `Percolation.exists_truncatedAxisConnectivity_le_pow_mul_exp_neg_rate` | proved for all radii, with the positive-density endpoint handled explicitly | jointly measured | jointly measured |
| Theorem 8.53; equations 8.59–8.60 | 213–216 | Axis truncated connectivity has the same logarithmic rate `a(p)` as the finite radius | `Percolation.truncatedAxisConnectivity_even_glue_lower_bound`, `Percolation.truncatedAxisConnectivity_odd_glue_lower_bound`, `Percolation.truncatedAxisConnectivity_logRate_tendsto` | proved; separate even and odd splices retain the exact source weights `p^2(1-p)^(2d-2)` and `p^3(1-p)^(4d-4)` and the exact denominator `d^2|∂B(m)|^2|B(m)|^2` | jointly measured | jointly measured |
| Theorem 8.61; equation 8.62 | 215–222 | Above `p_c`, exact finite-cluster probabilities have the stretched-exponential lower bound `exp(-gamma n^((d-1)/d))` | `Percolation.finiteClusterSizeProbability_ge_exp_neg_surface_of_critical_lt` | proved for every `n`; the exact source choice `delta=2^(d+3) theta(p)^(-2)` is retained through Lemmas 8.68, 8.72, and 8.82 | jointly measured | jointly measured |
| Lemma 8.68 | 217–218 | A box contains at least half its mean-density share of infinite-cluster vertices with probability at least `theta(p)/2` | `Percolation.infiniteClusterVertexCount_ge_half_probability_ge` | proved directly from the expectation identity and boundedness | jointly measured | jointly measured |
| Lemma 8.72 | 218–221 | There is a geometrically controlled sequence of exact cluster sizes with the required lower mass | `Percolation.exists_supercriticalClusterSize_scale` | proved with positive integer scales and both source ratio bounds | jointly measured | jointly measured |
| Lemma 8.82 | 220–222 | Every sufficiently large integer is a bounded-radix sum of the selected scales | `Percolation.exists_boundedRadixRepresentation_weighted` (from `Percolation.exists_boundedRadixRepresentation`) | proved as the source-facing weighted representation and consumed by animal concatenation | jointly measured | jointly measured |
| Equation 8.64 | 216 | Positive radius rate implies `P(n≤|C|<∞)≤exp(-eta n^(1/d))` | `Percolation.finiteClusterSizeTail_le_exp_neg_rpow_of_radiusRate_pos`, `Percolation.finiteClusterSizeTail_le_exp_neg_rpow_of_critical_lt_of_slabCriticalApproximation` | proved from `0<a(p)` in every dimension and from `SlabCriticalApproximation d` for `d≥3`; all `n=0`, small-size, and zero-tail cases are discharged | 31m37s shared final window + 11m52s uniform/consequence window | 486,071 + 559,110 |
| Theorem 8.65; equation 8.66 | 216, 222–223 | The finite-cluster tail has the sharper surface-order upper bound | — | target; the source omits the high-dimensional external-boundary topology and then invokes Chapter 7 LSS/good-block renormalization | — | — |
| Theorem 8.92 | 224–225 | `theta`, finite susceptibility, and cluster density are `C^infinity` on `(p_c,1]` | analytic core: `Percolation.theta_finiteSusceptibility_clusterDensity_contDiffOn_interior`; uniform input/assembly: `Percolation.exists_uniformFiniteClusterSizeTailStretchedExponential_of_slabCriticalApproximation`, `Percolation.theta_finiteSusceptibility_clusterDensity_contDiffOn_supercriticalInterior_of_slabCriticalApproximation`; identifications: `Percolation.thetaAnimalSeries_eq_theta`, `Percolation.concreteSusceptibilitySeries_eq_finiteSusceptibility_toReal`, `Percolation.concreteClusterDensitySeries_eq_openClustersPerVertex` | the whole open interval `(p_c,1)` is proved for `d≥3` from `SlabCriticalApproximation d`: the left-endpoint strip gives one rate uniformly for every `p∈[a,b]`, closing the former uniformity gap. The source's one-sided `p=1` endpoint still uses the separately omitted high-density topology in (8.88) | 38m40s analytic core + 11m52s uniform/consequence window | 503,373 + 559,110 |
| Theorem 8.97 | 226–228 | If `theta(p)>0`, left-right box crossing probability tends to one | `Percolation.leftRightCrossing_probability_tendsto_one` | proved from uniqueness, finite inner-box contact, face FKG, and finite-box coalescence; no quantitative Chapter 7 estimate is assumed | jointly measured | jointly measured |
| Theorem 8.99 | 226–227 | The closed-boundary/open-interior edge ratio of the infinite cluster tends almost surely to `(1-p)/p` | `Percolation.infiniteClusterBoundaryInteriorEdgeRatio_tendsto_ae_of_radiusRate_pos`, `Percolation.infiniteClusterBoundaryInteriorEdgeRatio_tendsto_ae_of_critical_lt_of_slabCriticalApproximation`; density laws and local balance as below | proved from the positive radius exponent, and for `d≥3` now assembled directly from `SlabCriticalApproximation d`. A generic summable cylinder-approximation strong law, exponential finite-cluster approximation errors, square-box Borel–Cantelli, deterministic boundary comparison, and square-to-all-radius interpolation discharge the former density-limit premise without an ergodic axiom | 9m20s local balance + 6m09s assembly + 42m40s density law + shared strip/consequence windows | 227,022 + 164,905 + 907,656 + shared strip/consequence windows |

## Measured tracker windows

| Window | Scope | Time | Tokens |
|---|---|---:|---:|
| Chapter 8 tracker through the current checkpoint | all theorem construction, source inspection, verification, and separately identified closeout work below | 12h10m06s | 11,063,659 |
| Final surviving disjoint snapshot | production repair of the exact 8.53 parity squeeze, complete conditional 8.64 construction, integration, production builds, and transitive axiom audit | 31m37s | 486,071 |
| Theorem 8.99 local edge-balance window | off-edge continuation event, deletion survival, semantic interior/boundary equivalences, exact Bernoulli factors, integration, and axiom audit | 9m20s | 227,022 |
| Theorem 8.99 conditional assembly window | finite-box counts/densities, aggregate directional balance, positivity, specialized pointwise-limit interface, exact ratio assembly, build, and axiom audit | 6m09s | 164,905 |
| Theorem 8.21 front-end window | signed-hyperplane event and measurability, first-hit cover, cubic symmetry reductions, exact factor `2d` in (8.43), analytic rate implication, strict build, and axiom audit | 14m19s | 264,188 |
| Theorem 8.99 pointwise-density window | generic summable cylinder strong law, finite-radius edge approximations, square-box laws, deterministic boundary correction, interpolation to every radius, source ratio, strict build, and transitive axiom audit | 42m40s | 907,656 |
| Theorem 8.92 interior analytic-core window | arbitrary animal-weight derivatives, exact-size level bounds, polynomial-times-stretched-exponential summability, weighted `C∞` series for `theta`, finite susceptibility, and cluster density, physical-series identifications, strict compilation, and transitive axiom audit | 38m40s | 503,373 |
| Aggregate-build integration window | resolve the Chapter 11/Chapter 8 helper collision and complete the repository-wide integration build | 29m58s | 410,245 |
| Theorem 8.21 strip-contraction window | arbitrary-coordinate support/independence, canonical first entrances, fresh-strip factorization, iterated avoidance histories, exact floor estimate, exponential absorption, slab rotation, strict builds, and axiom audit | 29m32s | 438,557 |
| Uniform (8.91) and downstream consequence window | rooted region monotonicity, one-rate compact-uniform hyperplane/radius/volume estimates, global interior `C∞` assembly, (8.64)/8.99 wrappers, and strict verification | 11m52s | 559,110 |
| Final verification and documentation window | targeted transitive audit, repository-wide build, source scan, comparator/status reconciliation, and documentation closeout | 22m34s | 234,108 |

The disjoint windows are included in the tracker total and are not added to it.  The later windows
start from explicit tracker snapshots; unallocated tracker activity between surviving
snapshots is intentionally not reconstructed.  Earlier per-theorem snapshots are unavailable, so
the joint total remains the only honest measured roll-up for those rows.

## Axiom and build status

`Percolation.Tests.Chapter8AxiomAudit` builds and reports only:

- `propext`;
- `Classical.choice`; and
- `Quot.sound`.

No Chapter 8 production file contains `sorry`, `admit`, or a new `axiom`.  The completed chapter
modules are imported by `Percolation.lean`; the Chapter 8 transitive audit build succeeds (8,603
jobs), and the repository-wide build succeeds (8,757 jobs).  The chapter remains marked
incomplete until Theorem 8.21 is unconditional in all
source dimensions, Theorem 8.65 is proved, and the `p=1` endpoint of Theorem 8.92 is discharged.
The source-facing 8.99 corollary follows from 8.21's positive radius exponent without any
additional analytic hypothesis.
