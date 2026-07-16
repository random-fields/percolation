# Topic 11 — Bond Percolation in Two Dimensions

Source id: `grimmett-percolation-1999`

Source: Geoffrey Grimmett, *Percolation*, 2nd edition, Chapter 11, pp. 282–332.

This card is the source-first inventory for the complete named-result scope of Chapter 11.  The
repository proves the exact square-lattice threshold, the finite rectangle calculation, the RSW
algebra above its explicitly isolated topology inputs, supercritical centered-rectangle
crossings, and finite-tube decay.  In accordance with the user's instruction, a source-facing
result which depends on a reference outside the book is isolated as an axiom (or has that cited
result as a visible transitive axiom).  This is a complete **source-facing interface**, not a
complete proof development and not an assumption-free chapter: among the 19 named source rows,
six are proved declarations (five modulo named external primitives and one with standard axioms),
11 are direct external axioms, and two are wrappers over external axioms.  A separately proved
centered-rectangle normalization supplements the literal, axiomatized Lemma 11.22.

## Named-result correspondence

| Source result | Natural-language statement | Lean declaration | Important dependencies | Status | Divergence / fidelity note | Construction time | Construction tokens |
|---|---|---|---|---|---|---:|---:|
| Proposition 11.2, p. 284 | Every finite connected square-lattice subgraph has a unique surrounding dual circuit, every edge of which crosses the graph's edge boundary. | `existsUnique_boundaryCircuitCrossedEdges` | Kesten (1982), p. 386 | external axiom | Uniqueness is extensional equality of the crossed primal-edge finset, quotienting cyclic base-point and reversal choices that make literal walk uniqueness false. | not individually measured | not individually measured |
| Theorem 11.4, p. 285 | `K(p)=K(1-p)+1-2p` for square-lattice cluster density. | `openClustersPerVertex_square_duality` | face/component correspondence attributed to Kesten, Euler formula | external axiom | `openClustersPerVertex` is the repository's real `E(1/|C|)` normalization. | not individually measured | not individually measured |
| Theorem 11.11, p. 287 | The bond critical probability of `ℤ²` equals `1/2`. | `cubicCriticalProbability_two_eq_half` | 11.12, 11.21, RSW, external planar-topology inputs | proved modulo named external topology axioms | Exact equality in `ℝ`; no theorem-specific axiom. | not individually measured | not individually measured |
| Lemma 11.12, p. 288 | `θ(1/2)=0`, hence `p_c≥1/2`. | `theta_two_half_eq_zero` | independent annular barriers, 11.70, external circuit separation | proved modulo named external topology axioms | Exact rooted percolation probability. | not individually measured | not individually measured |
| Lemma 11.13, p. 288 | If `θ(p)>0`, then almost surely some open circuit surrounds each fixed `B(n)`. | `eventuallySurroundingOpenCircuit_probability_one` | Proposition 11.2 | external axiom | The event quantifies over literal finite square-lattice cycles and requires odd face index for every vertex of `B(n)`. | not individually measured | not individually measured |
| Lemma 11.21, p. 294 | A left–right crossing of `[0,n+1]×[0,n]` has probability exactly `1/2` at density `1/2`. | `bernoulliBondMeasure_real_grimmettRectangleCrossingEvent_half` | finite trace weights, external Kesten dual-trace bijection | proved modulo named external topology axiom | Literal source rectangle and endpoints. | not individually measured | not individually measured |
| Lemma 11.22, p. 295 | For `p>1/2`, `P(M_{n+1}≤βn)≤e^{-γn}` for positive `β,γ` and all `n≥1`. | `maxEdgeDisjointGrimmettRectangleCrossings_probability_le_exp`; proved normalization `maxEdgeDisjointSquareRectangleCrossings_probability_le_exp` | 11.20/Proposition 11.2, ACCFR, arbitrary finite edge Menger | literal source form external; centered normalization proved modulo external topology | `maxEdgeDisjointGrimmettRectangleCrossings` is the exact maximum in `[0,n+1]×[0,n]`; the independently proved reusable theorem uses `[0,n+1]×[-n,n]`. | not individually measured | not individually measured |
| Theorem 11.24, p. 295 | For `1/2<p<1`, finite-cluster correlation length is positive and finite and equals one half the complementary subcritical correlation length. | `finiteCorrelationLength_eq_half_correlationLength_complement`; `finiteCorrelationLength_pos_lt_top`; `truncatedTwoPointConnectivity_logRate_tendsto` | Proposition 11.2 surrounding-circuit comparison, Chapter 6 positivity of the subcritical rate | equality external; positivity/finiteness proved from it | Correlation lengths use `ℝ≥0∞`, preserving infinite endpoint conventions; hypotheses exclude both logarithmic endpoints. | not individually measured | not individually measured |
| Theorem 11.25, p. 296 | For `1/2<p<1`, `P_p(|C|=n)≤exp(-η√n)`. | `finiteClusterSizeProbability_le_exp_neg_sqrt_of_supercritical` | Proposition 11.2 dual enclosure | external axiom | Exact-size probability and source exponent; valid for every natural `n`. | not individually measured | not individually measured |
| Lemma 11.27, pp. 296–297 | The finite-tube log rate exists, gives an exponential upper bound, is positive and finite, decreases in tube width, and converges to the unrestricted rate. | `tubeConnectivityDecayRate_properties` | Fekete/subadditivity, independent closed cuts, continuity from below | proved | Generalized to width `k=0`; the source's `k≥1` cases are direct instances. `Antitone` is explicitly included, not inferred from convergence notation. | not individually measured | not individually measured |
| Theorem 11.55, p. 304 | If `f(u)/log u→a>0`, `p_c(G(f))` is the unique `π∈(1/2,1)` with `ξ(1-π)=a`. | `logarithmicProfileRegion_criticalProbability` | 11.24 and surrounding dual circuits | external axiom | `f : ℝ→ℝ` is constrained only on `[0,∞)`; the graph itself enforces nonnegative coordinates. | not individually measured | not individually measured |
| Theorem 11.63, p. 311 | Bounded cluster-functional sums over growing circuit interiors satisfy a CLT away from `p=1/2`, under the infinite-cluster and variance hypotheses. | `clusterFunctionalSum_centralLimitTheorem` | externally cited method-of-moments / strong-mixing CLTs | external axiom | Adds the mathematically implicit measurability of each random variable; arbitrary set functions are not automatically measurable in Lean. | not individually measured | not individually measured |
| Theorem 11.70, p. 315 | RSW: if the square-crossing probability is `r`, the annular-circuit probability is at least `r^12(1-√(1-r))^48`. | `rswAnnulusOpenCircuitProbability_ge` | 11.73, 11.75 | proved modulo named external planar topology | Exact numerical expression (11.71). | not individually measured | not individually measured |
| Lemma 11.73, p. 316 | A square crossing probability `r` gives a `3l×2l` crossing probability at least `(1-√(1-r))^3`. | `rswThreeHalvesCrossingProbability_ge` | Russo (1981) lowest-crossing topology | external axiom | Exact probability conclusion; only the externally cited lowest-crossing/stopping-set step is assumed. | not individually measured | not individually measured |
| Lemma 11.75, p. 317 | The three FKG gluing inequalities (11.76)–(11.78). | `rsw_gluing_inequalities` | FKG, graph-automorphism invariance, three Proposition-11.2 event inclusions | proved modulo three isolated deterministic topology axioms | Exact three conjuncts and constants. | not individually measured | not individually measured |
| Theorem 11.89, p. 324 | Critical radius and cluster-size tails obey two-sided power bounds, and a positive cluster-size moment is finite. | `squareCritical_powerLaw_bounds` | 11.70/11.73 and Proposition 11.2 | external axiom | Exact `n≥1` lower prefactor `1/2`, existential positive finite real constants, and `Integrable` moment conclusion. | not individually measured | not individually measured |
| Theorem 11.93, p. 325 | Near-critical power bounds for `θ`, `χ`, and finite susceptibility. | `squareNearCritical_powerLaw_bounds` | 11.89 | external axiom | Strict sides of `1/2` are retained; `toReal` is safe under the stated phase hypotheses. | not individually measured | not individually measured |
| Theorem 11.115, p. 332 | For `p_h,p_v<1`, rooted square percolation vanishes iff `p_h+p_v≤1` and is positive iff the sum is greater than one. | `inhomogeneousSquare_criticalSurface` | original inhomogeneous square-lattice result | proved wrapper over two external axioms | `inhomogeneousSquareTheta` is the origin-cluster event, not the zero–one event that an infinite cluster exists somewhere. | not individually measured | not individually measured |
| Theorem 11.116, p. 332 | For three densities below one, rooted triangular percolation is separated by `p_h+p_v+p_d-p_hp_vp_d=1`. | `inhomogeneousTriangular_criticalSurface` | original star–triangle result | proved wrapper over two external axioms | The graph is the square lattice plus north-east diagonals; all three endpoint hypotheses are explicit. | not individually measured | not individually measured |

## Numbered supporting-result inventory

The following groups account for every numbered item in the chapter.  They are definitions,
displayed proof steps, or consequences rather than additional named results.

| Source numbers | Disposition |
|---|---|
| 11.1 | Shifted dual square-lattice definitions: `dualSquareGraph`, `squareEdgeDualCrossingEquiv`, `dualSquareConfiguration`. |
| 11.3 | Isoperimetric comparison following externally sourced Proposition 11.2; not exposed as a separate headline because later public statements use direct radius/size encodings. |
| 11.5–11.10 | Euler/face proof of Theorem 11.4; represented by the source-facing external theorem axiom. |
| 11.14–11.20 | Square-root trick, finite crossing traces, complementary weights, and crossing alternative: `grimmettRectangleCrossingProbability_add_complement`, FKG APIs, and the isolated trace/topology axioms in `External.lean`. |
| 11.23, 11.26, 11.28–11.32 | Truncated connectivity, tube events, tube rates, exponential upper bound, width monotonicity, and unrestricted limit: `truncatedTwoPointConnectivity`, `squareTube`, `tubeTwoPointConnectivity`, `tubeConnectivityDecayRate`, and `tubeConnectivityDecayRate_properties`. |
| 11.33–11.54 | Proof steps for 11.24/11.25 and definitions of profile regions/critical probability; either proved as tube helpers or covered by the explicitly sourced external headline declarations. |
| 11.56–11.62 | Upper/lower profile estimates used for 11.55; subsumed by the source-facing external theorem under the transitive Proposition-11.2 policy. |
| 11.64–11.69 | Exact CLT hypotheses, normalization, functional sum, and examples: `SquareCircuitInterior`, `clusterFunctionalSum`, `SatisfiesCentralLimitTheorem`, and the external Theorem 11.63 declaration. |
| 11.71–11.88 | RSW numerical expression, uniform critical annular bound, gluing inequalities, and independent annular barriers: `RSWNumeric.lean`, `RSWGluing.lean`, `IndependentBarriers.lean`, and `SquareThresholdExact.lean`. |
| 11.90–11.113 | Critical/near-critical power inequalities and their proof chain; represented by exact source-facing Theorems 11.89 and 11.93 at the externally sourced topology boundary. The OCR text has no separately labelled 11.102. |
| 11.114 | Rooted inhomogeneous percolation definitions: `inhomogeneousSquareTheta` and `inhomogeneousTriangularTheta`. |

## Trust boundary

`Percolation/Tests/Chapter11AxiomAudit.lean` prints the full transitive axiom sets.  Project
axioms occur only in:

- `Percolation/Planar/External.lean`: Kesten/Russo planar topology and deterministic gluing;
- `Percolation/Planar/Chapter11External.lean`: source-facing descendants which the book delegates
  outside itself or states without proof;
- `Percolation/Planar/Inhomogeneous.lean`: the original inhomogeneous critical-surface results.

The exact threshold theorem is a Lean proof, but its audit visibly contains the named Kesten and
Russo boundary axioms.  It is therefore reported as “proved modulo named external topology,” not
as assumption-free.

## Semantic tests

`Percolation/Tests/Chapter11Infrastructure.lean` includes application checks for the exact
threshold, rectangle probability, RSW, exact and centered Lemma 11.22 encodings, surrounding
circuits, truncated correlation length, supercritical cluster tails, tube rates, Proposition
11.2, Theorem 11.4, critical power laws, and both inhomogeneous surfaces.  Arithmetic oracles
independently verify `p_h+p_v=1` for `(1/4,3/4)` and
`p_h+p_v+p_d-p_hp_vp_d=11/8` for `(1/2,1/2,1/2)`.

## Telemetry

The active Chapter 11 goal tracker is `019f486f-e045-7e71-b571-5b6ad19e3cb4`.  At the start of
the final review window it reported 16,211 seconds and 2,735,063 tokens.  This is measured
aggregate goal usage, not a per-theorem reconstruction.  Per-theorem snapshots were not taken
consistently during construction, so the table reports them as **not individually measured**;
no estimated allocation is presented as measured telemetry.
