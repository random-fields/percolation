# Topic 06 — Exponential Decay and Analyticity

Source: `grimmett-percolation-1999`, Chapter 6, pp. 117–145.

## Scope and current status

The target is every named theorem, proposition, and lemma in Chapter 6 together with the major
displayed consequences used by those results.  This card remains **incomplete** until every target
row is proved, reviewed, and axiom-audited.  Status is based on exact public declarations, not on
informal proof sketches or conditional helper theorems.

## Source corrections discovered by adversarial review

- The lower bound in (6.46) contains a constant times `p`, not `p ^ n`, and is meaningful for
  positive `n`.
- The lower bound in (6.48) contains `p ^ (d * |x|)` and its printed negative power of `|x|` is
  undefined at `x = 0`; the faithful Lean lower bound will assume `x ≠ 0`.
- The displayed exponential tail following Theorem 6.75 cannot hold at `n = 1`, since
  `P(|C| ≥ 1) = 1`.  The exact bound (6.77) assumes `n > χ(p)^2`; the general corollary will be
  stated eventually or with an `n - 1` exponent.
- Lemma 6.87 needs a finite nonempty terminal set.  It is false for an arbitrary infinite set.
- The sums in (6.89) and (6.93) must be `ℝ≥0∞` sums at general density; a nonsummable real `tsum`
  is zero in Lean and would falsify the `p = 1` instance.
- Equation (6.40) divides by `log (1 / b)` and therefore needs `b < 1`; `b = 1` is a separate
  endpoint statement.
- Correlation length is source-defined only for `p ≤ p_c`; any all-density definition is an
  explicitly documented extension.

## Source-to-Lean correspondence and telemetry

Time and token entries are measured active-goal counter differences.  A blank entry means that no
formalization window has yet completed; it is not an estimate.

| Source result | Page | Natural-language statement | Exact Lean declaration | Status / fidelity note | Time | Tokens |
|---|---:|---|---|---|---:|---:|
| Theorem 6.1, (6.2) | 117–120 | If `χ(p)<∞`, connection from `0` to `∂B(n)` is at most `exp (-n σ(p))` | `Percolation.boxRadiusTail_exponential_decay_of_susceptibility_lt_top` | proved for the chapter range `2 ≤ d`, all `n`; no extra public `p<1` hypothesis | 2m25s | 39,091 |
| Theorem 6.10, (6.11), (6.33)–(6.36) | 120–124 | The box-radius logarithmic rate exists and has two-sided polynomial corrections | `Percolation.boxRadiusTail_logRate_tendsto`, `Percolation.boxRadiusTail_twoSided_decay` | proved; constants are quantified before `p`, bounds require `n>0`, and use denominator/positive-power forms | 32m44s | 358,918 |
| Theorem 6.14, (6.15)–(6.18), (6.40) | 121, 124–125 | Continuity, monotonicity, strict subcritical decrease, zero-density divergence, and critical value | `Percolation.boxRadiusDecayRate_continuousOn`, `Percolation.boxRadiusDecayRate_antitoneOn_pos`, `Percolation.boxRadiusDecayRate_strictAntiOn_subcritical`, `Percolation.boxRadiusDecayRate_tendsto_top_at_zero`, `Percolation.boxRadiusDecayRate_critical_eq_zero`, `Percolation.boxRadiusDecayRate_log_ratio_comparison` | proved; continuity is a uniform limit of finite-event polynomials, the critical value does not assume `θ(p_c)=0`, and (6.40) carries the necessary `b<1` hypothesis | 16m45s | 294,286 |
| Theorem 6.44, (6.45)–(6.46) | 126 | Axis two-point function has rate `φ` and lower bound `c p / n^(4(d-1)) * exp(-nφ)` | `Percolation.twoPointConnectivity_axis_logRate_tendsto`, `Percolation.twoPointConnectivity_axis_twoSided_decay` | proved; the dimension-only constant is quantified before `p`, and the displayed bound requires `n>0` | jointly measured | jointly measured |
| Proposition 6.47, (6.48) | 126–127 | General two-point function has matching norm-dependent exponential bounds | `Percolation.twoPointConnectivity_twoSided_decay` | proved; lower bound requires `x≠0` and contains the corrected `p^(d*|x|)` factor; upper bound handles `x=0` exactly | jointly measured | jointly measured |
| Proposition 6.49 | 127–128 | `τ(0,x)≤(1-χ⁻¹)^|x|`, hence `ξ≤χ` below criticality | `Percolation.twoPointConnectivity_le_one_sub_susceptibility_inv_pow`, `Percolation.correlationLength_le_susceptibility`, `Percolation.susceptibility_tendsto_top_at_critical` | proved; `correlationLength` is ENNReal-valued, equals `⊤` at `p_c`, and the divergence theorem uses the left-neighborhood filter | jointly measured | jointly measured |
| Theorem 6.75, (6.77) | 132 | Subcritical cluster size has an exponential tail | `Percolation.clusterSizeAtLeast_exponential_decay_of_lt_critical`, `Percolation.clusterSizeAtLeast_le_two_exp_neg` | proved; exact (6.77) assumes `n>χ²`; the strict no-prefactor bound is stated eventually because the printed `n≥1` claim is false at `n=1` | jointly measured | jointly measured |
| Theorem 6.78, (6.80), (6.82)–(6.83) | 132–134 | Exact-size and finite-tail exponential rates exist, are positive below criticality, and `ζ≤φ` | `Percolation.clusterSizeProbability_logRate_tendsto`, `Percolation.finiteClusterSizeProbability_le_rate`, `Percolation.finiteClusterSizeTail_logRate_tendsto`, `Percolation.clusterSizeDecayRate_pos_of_lt_critical`, `Percolation.clusterSizeDecayRate_le_boxRadiusDecayRate` | proved; (6.80) retains the exact `n p⁻¹(1-p)²` prefactor, the finite tail explicitly excludes infinite clusters, and the identification with the ordinary at-least tail uses `θ(p)=0` below criticality | 30m17s | 270,822 |
| Lemma 6.87 | 134–135 | A finite nonempty terminal set has a removable terminal preserving connectivity of the rest | `Percolation.exists_terminal_deletion_preserves_connected` | proved for an arbitrary connected ambient graph and a finite nonempty `Finset`; deletion is encoded by `deleteIncidenceSet` | jointly measured | jointly measured |
| Lemma 6.89 | 135–136 | Three-point connectivity is bounded by a sum of three two-point products | `Percolation.threePointConnectivity_le_tsum_prod` | proved in `ℝ≥0∞`; includes deterministic first-hit tripod extraction and iterated BK | jointly measured | jointly measured |
| (6.93)–(6.97) | 136–138 | Skeleton tree-graph bound, skeleton count, moment bound, and exponential-moment bound | `Percolation.multiPointConnectivity_le_skeleton_sum`, `Percolation.cubicConnectivitySkeleton_card_eq`, `Percolation.connectivitySkeletonCount_eq_doubleFactorial`, `Percolation.clusterSizeMoment_le`, `Percolation.clusterSize_expMoment_le` | proved; the moment theorem uses the actual `ℝ≥0∞` cluster-size integral, and (6.97) evaluates the exact half-binomial skeleton generating function | jointly measured | jointly measured |
| Lemma 6.102 | 139–141 | Normalized exact cluster-size probabilities satisfy the animal-concatenation inequality | `Percolation.CubicBondAnimal.finiteClusterSizeProbability_normalized_supermultiplicative` | proved with the exact factor `p(1-p)⁻²`; the `1/n` normalization is discharged by an explicit equivalence between rooted animals and an anchored translation class with a selected root | 63m50s | 798,069 |
| Theorem 6.108 | 142–145 | `κ` and `χ` are analytic on `[0,p_c)` | `Percolation.concreteClusterDensitySeries_analyticOnNhd_belowCritical`, `Percolation.concreteSusceptibilitySeries_analyticOnNhd_belowCritical`, `Percolation.clusterDensity_and_susceptibility_analytic_belowCritical` | proved by genuine complex animal series; the endpoint uses an explicit complex disk, interior neighborhoods use Theorem 6.78 at the same density, and restriction lemmas identify the series with `openClustersPerVertex` and `susceptibility.toReal` on physical subcritical parameters | 21m14s | 278,299 |

## Shared infrastructure telemetry

| Measured window | Scope | Time | Tokens |
|---|---|---:|---:|
| Coordinate-box geometry and finite support | `L∞` distance, norm comparison, surfaces, exact internal edge support, first-hit paths, event measurability/monotonicity, and initial 6.1 scaffold | 5m23s | 119,967 |
| Theorem 6.10 and its shared block/rate infrastructure | exact face counts, translations, coordinate permutations/reflections, BK upper block, FKG lower block, two-sided corrected Fekete theorem, logarithmic rate, and public constants | 32m44s | 358,918 |
| Theorem 6.44 and Propositions 6.47–6.49 with shared two-point infrastructure | graph-isomorphism measure transport, axis Fekete rate, face reflection, arbitrary signed-coordinate concatenation, shell-mass selection, susceptibility comparison, ENNReal correlation length, and critical divergence | 62m09s | 725,848 |
| Lemmas 6.87 and 6.89 with tripod infrastructure | minimum finite connected carrier, removable terminal, first-hit path splitting, component-local tripods, open-graph transport, and endpoint-safe BK summation | 19m51s | 205,604 |
| Skeleton extraction and (6.93) infrastructure | recursive edge-insertion decoder, exact skeleton count, first-hit insertion of a new terminal, path normalization, pairwise edge-disjointness, deterministic event extraction, iterated BK, two-point row-sum identity, and initial connected-kernel partition infrastructure | 63m17s | 660,031 |
| Connected-kernel partition and (6.94) infrastructure | vertex-deletion induction for finite connected kernels, specialization to decoded skeletons, instance-independent cardinality transport, ordered terminal summation, measurable tuple expansion of cluster-size powers, and the source moment bound | 57m04s | 954,610 |
| (6.97), Theorem 6.75, and (6.77) infrastructure | exact half-multichoose skeleton generating function, ENNReal exponential moment, at-least tail and strict-tail shift, series Markov inequality, optimized source constant, and corrected eventual exponential theorem | 42m48s | 883,194 |
| Lemma 6.102 and anchored-animal infrastructure | lexicographic anchoring, injective animal concatenation, exact occupied-edge and closed-boundary counts, rerooting equivalence, rooted/anchored mass identity, and normalized probability inequality | 63m50s | 798,069 |
| Theorem 6.78 and exact/tail-rate infrastructure | positive exact-size masses, corrected logarithmic Fekete sequence, exact finite-index prefactor, geometric first-moment tail majorant, finite-tail event/series identification, tail-rate squeeze, and comparison with box-radius decay | 30m17s | 270,822 |
| Theorem 6.108 and complex animal-series infrastructure | complex density and susceptibility levels, endpoint animal-count majorants, interior complex/physical weight comparison, locally uniform summability from the exact-size decay rate, restriction to real parameters, probabilistic identification, full build, and axiom audits | 21m14s | 278,299 |

The initial window included the first 6.1 scaffold before an internal counter snapshot was taken.
It is charged once to shared infrastructure and is not duplicated in the theorem row.  The 6.1
row measures the disjoint source-facing wrapper, independent review disposition, application and
adversarial cases, module build, and axiom audit from counter snapshots `(328s, 121659)` through
`(473s, 160750)`.

The 6.10 window runs from `(473s, 160750)` through `(2437s, 519668)`. It necessarily combines
the theorem with its new shared symmetry, face-event, and corrected-subadditivity infrastructure;
no reconstructed split is presented.

The 6.14 window runs from `(2437s, 519668)` through `(3442s, 813954)`. It includes the uniform
finite-radius approximation, the box-tail-to-`θ` squeeze, the self-avoiding-walk endpoint bound,
all local verification, and the corrected source-domain audit for (6.40).

The two-point window runs from `(3442s, 813954)` through `(7171s, 1539802)`. Because no reliable
counter snapshot was taken between 6.44, 6.47, and 6.49, this is reported as one joint measured
window and is charged exactly once. No reconstructed per-theorem split is presented as measured
telemetry.

The initial tree-graph window runs from `(7644s, 1620051)` through `(8835s, 1825655)`. It jointly
measures Lemmas 6.87 and 6.89 and their shared tripod infrastructure; no reconstructed split is
reported.

The skeleton-extraction window runs from `(8835s, 1825655)` through `(12632s, 2485686)`. It
jointly measures the recursive realization theorem, the exact skeleton enumeration, (6.93), its
axiom/build audits, and the connected-kernel infrastructure begun for (6.94). The time spent
detecting and correcting stale foreground Lean processes is included because it occurred inside
the theorem-verification window; no portion is silently removed or reassigned.

The connected-kernel and moment window runs from `(12632s, 2485686)` through
`(16056s, 3440296)`. It includes the general finite-kernel deletion theorem, its skeleton
specialization, the ordered-multipoint mass estimate, the exact measurable identity between
cluster moments and ordered connection masses, (6.94), local module builds, and axiom audits.

The exponential-moment and tail window runs from `(16056s, 3440296)` through
`(18624s, 4323490)`. It includes the coefficient identification and generating-function proof for
(6.97), the at-least-tail API and exact shift to Chapter 5's strict tail, the series Markov bound,
the optimized inequality (6.77), the corrected eventual form of Theorem 6.75, local verification,
and axiom audits.

The anchored-animal window runs from `(18624s, 4323490)` through `(22454s, 5121559)`. It includes
the exact boundary-overlap proof, injectivity of concatenation, the construction and verification
of rerooted animals, the equivalence between rooted animals and pointed anchored translation
classes, the `1/n` mass identity, Lemma 6.102 itself, local builds, and axiom audits.

The exact-size-rate window runs from `(22454s, 5121559)` through `(24271s, 5392381)`. It includes
the positive-mass base animal, the corrected subadditive logarithmic sequence, the exact-size
Fekete limit and (6.80), positivity below criticality, the finite-tail geometric majorant and
measure-theoretic series identity, (6.82), (6.83), local builds, and axiom audits.

The analyticity window runs from `(24271s, 5392381)` through `(25545s, 5670680)`. It includes
the complex animal terms and both series, the independent small-density complex disk, the
interior majorant which spends half of the exact-size decay exponent, locally uniform complex
differentiability, restriction to real parameters, identification with the probabilistic
cluster density and susceptibility, a repository-wide build, and headline axiom audits.
