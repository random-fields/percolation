# Topic 12 — Extensions of Percolation

Source: `grimmett-percolation-1999`, Chapter 12, pp. 349–377.

Status: implementation plan and source inventory.  No Chapter 12 result is to be marked
complete merely because a definition or a theorem-shaped interface has been added.  A row becomes
`proved` only after its source comparison, application tests, adversarial tests, transitive axiom
audit, and clean build have all passed.

## Completion contract

The Chapter 12 stack will formalize the mathematical assertions in all ten sections of
“Extensions of Percolation,” including the results that the chapter cites rather than proves.
The mandatory headline scope is:

- Theorems 12.3, 12.8, 12.9, 12.22, 12.24, 12.28, and 12.35.
- The displayed subcritical criteria 12.1–12.2; surface bounds 12.20–12.21; entanglement
  estimate 12.26; invasion limits 12.29–12.30; oriented definitions and tail estimate
  12.31–12.33; and continuum comparison chain 12.37–12.46.
- The unnumbered but theorem-level claims in §§12.1–12.2 and §§12.8–12.10: the two
  inhomogeneous critical surfaces, the stated AB-percolation conclusions, non-triviality and
  critical extinction for oriented percolation, first-passage subadditivity/time constant and the
  shape theorem, continuum subcritical rate positivity, and uniqueness of the infinite Boolean
  cluster.

Completion means:

- no `sorry`, `admit`, new axiom, hidden theorem parameter, or “proved modulo” headline;
- source-facing public declarations with explicit endpoint and dimension hypotheses;
- `lake build` succeeds from a clean worktree;
- every Chapter 12 headline has an explicit `#print axioms` audit containing only `propext`,
  `Classical.choice`, and `Quot.sound` (unrelated axioms on the stacked base do not excuse a
  transitive dependency in a Chapter 12 result);
- the chapter-scale gates in `AUTOMATED_REVIEW.md` pass;
- the final PR has one source/Lean correspondence row per inventory item and measured wall-clock
  time and token usage for every major theorem, with separate non-overlapping infrastructure and
  review rows; and
- the work is published as a draft PR stacked on
  `agent/grimmett-chapter-8-autoformalization`.  The dirty Chapter 7/8 worktree is not touched.

## 1. Source inventory and planned public declarations

### §12.1 — mixed percolation on a general lattice, pp. 349–351

| Source assertion | Planned Lean declaration | Disposition |
|---|---|---|
| Periodic/geometric and graph-theoretic notions of a `d`-dimensional lattice | `PeriodicLattice`, `cubicPeriodicLattice`, `GeometricPeriodicLattice`, `cubicGeometricPeriodicLattice` | proved, using proper integer boxes and a uniform edge-span bound as a checkable sufficient encoding of compact edge-local-finiteness |
| Site percolation and mixed site/bond percolation | `MixedConfiguration`, `mixedOpenGraph`, `mixedTheta`, `mixedCriticalSet` | proved at the model/interface level: measurable rooted events, simultaneous monotone coupling, downward-closed zero phase, both zero axes, exact bond-density-one rooted-site boundary, and exact cubic site-density-one bond boundary; no universal closed-form critical curve is asserted |
| Square inhomogeneous critical surface `p_h+p_v-1=0` | `squareInhomogeneous_theta_eq_zero_of_add_lt_one`, `squareInhomogeneous_theta_pos_of_one_lt_add` | reuse the Chapter 11 finite-energy/duality layer only after its transitive axiom dependencies have been discharged |
| Triangular inhomogeneous critical surface `p₁+p₂+p₃-p₁p₂p₃-1=0` | `triangularInhomogeneous_theta_eq_zero_of_criticalPolynomial_lt`, `triangularInhomogeneous_theta_pos_of_criticalPolynomial_pos` | requires a triangular-lattice and star–triangle stack; no theorem is recorded as proved merely from the prose reference |

### §12.2 — AB percolation, p. 351

| Source assertion | Planned Lean declaration | Disposition |
|---|---|---|
| An edge is AB-open exactly when its endpoint labels differ | `abOpenGraph` | define for an arbitrary simple graph and Bernoulli site labels |
| Interchanging labels `A` and `B` preserves the model, hence `θ_AB(p)=θ_AB(1-p)` | `abTheta_complementary_density` | proved for every countable simple graph and root, including event measurability and the Bernoulli-complement pushforward |
| No infinite AB path on the square lattice for any density | `squareABTheta_eq_zero` | formal theorem for every `p : I` |
| The triangular lattice has positive AB percolation on a nonempty interval containing `1/2` | `exists_Icc_subset_triangularABTheta_pos` | make the interval and its containment explicit; do not silently turn “containing” into an open-neighbourhood claim |

### §12.3 — one-dimensional long-range percolation, pp. 351–359

| Source | Natural-language result | Planned Lean declaration |
|---|---|---|
| 12.1 | If `∑ n p(n) < ∞`, every long-range component is almost surely finite | `longRange_ae_all_components_finite_of_summable_nat_mul` |
| 12.2 | If `2∑p(n) ≤ 1`, every component is almost surely finite | `longRange_ae_all_components_finite_of_two_mul_tsum_le_one` |
| 12.3–12.5 | The random graph on `ℤ` is almost surely connected iff the positive support is aperiodic and `∑p(n)=∞` | `longRange_ae_connected_iff` |
| 12.10–12.19 | Under `p(1)>0` and divergent total intensity, the half-line graph is almost surely connected; finite restrictions satisfy the component-count estimates used by Kalikow | `longRangeHalfLine_ae_connected_of_p_one_pos_of_tsum_eq_top` plus numbered helper declarations |
| 12.8 | For `1<α<2` and `β>0`, a non-trivial nearest-neighbour critical parameter separates zero and positive percolation | `longRangePowerLaw_exists_critical` |
| 12.9(a) | At `α=2`, `β≤1` has no percolation below nearest-neighbour density one | `longRangeInverseSquare_theta_eq_zero_of_beta_le_one` |
| 12.9(b) | At `α=2`, `β>1` has a non-trivial critical parameter and supercritical probability at least `β⁻¹ᐟ²` | `longRangeInverseSquare_exists_critical_and_theta_ge` |

The notation `θ(p,α,β)` in the book suppresses the choice of the complete probability vector:
an asymptotic relation alone does not define a measure.  The Lean interface will therefore use a
`LongRangePowerLawFamily` carrying the whole profile, the nearest-neighbour parameter, the tail
asymptotic, and monotonicity in that parameter.  Critical values are indexed by this family.  A
canonical corollary will use `p(n)=1-exp(-β n^{-α})` away from `n=1`.  This is a fidelity repair,
not an extra assumption hidden from the comparator.

### §12.4 — plaquette surfaces in three dimensions, pp. 359–361

| Source | Natural-language result | Planned Lean declaration |
|---|---|---|
| 12.20 | The canonical `n²`-plaquette spanning surface gives `Pₚ(Cₙ) ≥ (1-p)^(n²)` | `closedPlaquetteSurface_probability_ge` |
| 12.21 | Boundary-edge incidence gives `Pₚ(Cₙ) ≤ (1-p^4)^(4(n-1))` | `closedPlaquetteSurface_probability_le` |
| 12.22(a) | Below `p_c(ℤ³)`, `Pₚ(Cₙ)` obeys a perimeter law with logarithmic rate `α(p)` | `closedPlaquetteSurface_perimeterLaw` |
| 12.22(b) | Above `p_c(ℤ³)`, `Pₚ(Cₙ)` obeys an area law with logarithmic rate `β(p)` | `closedPlaquetteSurface_areaLaw` |

The book defines `aₙ≈bₙ` by `log aₙ/log bₙ → 1`.  Lean will expose that definition as
`LogAsymptotic` and will also prove equivalent normalized-log limit forms, avoiding division at
finite indices where a probability might be `0` or `1`.

### §12.5 — entanglement, pp. 362–364

| Source | Natural-language result | Planned Lean declaration |
|---|---|---|
| 12.23 | Definition of the entanglement critical probability | `entanglementCriticalProbability` |
| 12.24–12.25 | In three-dimensional cubic bond percolation, `0<p_c^ent<p_c` | `entanglementCriticalProbability_pos_lt_cubicCriticalProbability` |
| 12.26 | For sufficiently small positive `p`, the maximal origin entanglement has tail at most `exp(-a(p)n/log n)` | `entanglementSizeTail_le_exp_neg_div_log` |

The primary 12.26 statement will require `2≤n`; the literal formula is undefined at `n=1`.
Small `n` will be covered by a separate constant-adjusted corollary.

### §12.6 — rigidity, pp. 364–366

| Source | Natural-language result | Planned Lean declaration |
|---|---|---|
| 12.27 | A framework motion preserves every graph-edge length | `FrameworkMotion` and `FrameworkMotion.preserves_edge_dist` |
| 12.28(a) | On a `d`-dimensional lattice (`d≥2`), ordinary bond critical probability is strictly below the rigidity threshold | `criticalProbability_lt_rigidityCriticalProbability` |
| 12.28(b) | The rigidity threshold is below one iff the lattice itself is rigid | `rigidityCriticalProbability_lt_one_iff` |
| following consequence | The cubic lattice is not rigid for `d≥2`, so its rigidity threshold is one | `cubicRigidityCriticalProbability_eq_one` |

The source invokes an unspecified “natural probability measure” to define generic rigidity.
Lean will use the standard algebraic definition through maximal rank of the rigidity matrix and
prove its equivalence to almost-everywhere rigidity for frameworks over `ℝ`.  The comparator will
record this hypothesis repair; an unspecified measure will not be encoded as data.

### §12.7 — invasion percolation, pp. 366–367

| Source | Natural-language result | Planned Lean declaration |
|---|---|---|
| construction | Repeatedly add the least-labelled edge in the finite edge boundary | `invasionCluster`, `invasionEdge`, `invasionEmpiricalCDF` |
| 12.29 | `Qₙ(y)→1` almost surely for `y>p_c` | `invasionEmpiricalCDF_tendsto_one_ae` |
| 12.30 | `Qₙ(y)→y/p_c` almost surely for `y<p_c` | `invasionEmpiricalCDF_tendsto_div_critical_ae` |

The recursive definition uses a deterministic edge enumeration only to break ties.  A separate
lemma proves that iid continuous labels are pairwise distinct almost surely, so source-facing
results are independent of the enumeration.

### §12.8 — oriented percolation, pp. 367–369

| Source | Natural-language result | Planned Lean declaration |
|---|---|---|
| 12.31–12.32 | Directed origin cluster, percolation probability, and critical probability | `northEastCluster`, `orientedTheta`, `orientedCriticalProbability` |
| exercise after 12.32 | `0<p_c^→(d)<1` for `d≥2` | `orientedCriticalProbability_pos_lt_one` |
| 12.33 | In dimension two and above the oriented threshold, the finite-cluster tail lies between two `exp(-c√n)` bounds | `orientedFiniteClusterTail_twoSided` |
| following assertion | Critical oriented percolation dies out for all `d≥2` | `orientedTheta_critical_eq_zero` |
| random-orientation observation | At density `1/2`, the probability of an infinite directed path is zero | `randomOrientationTheta_half_eq_zero` |

The open question asking whether the last probability is positive away from `1/2` is an explicit
anti-target, not a theorem obligation.

### §12.9 — first-passage percolation, pp. 369–371

| Source assertion | Planned Lean declaration |
|---|---|
| Passage time of a path and the infimum over paths | `firstPassagePathTime`, `firstPassageTime` |
| Wet vertices and the filled geometric region | `firstPassageWetVertices`, `firstPassageWetRegion` |
| Stationarity of axial passage times | `axialPassageTime_stationary` |
| `aₘₙ≤aₘᵣ+aᵣₙ` | `axialPassageTime_subadditive` |
| Expected subadditive time constant | `meanAxialFirstPassageTime_div_tendsto` |
| Subadditive-ergodic time constant | `axialPassageTime_div_tendsto_ae` |
| Shape theorem under the standard moment condition | `firstPassage_shape_theorem` |

The phrase “a suitable moment condition” is not a formal hypothesis.  The source-facing theorem
will state the Cox–Durrett/Kesten condition explicitly (integrability of the minimum of the
`2d` incident edge times to the `d`th power), with separate nondegenerate and zero-time-constant
cases.  A reusable proof of the subadditive ergodic theorem is part of the stack because Mathlib
does not currently contain Kingman’s theorem.

### §12.10 — continuum percolation, pp. 371–377

| Source | Natural-language result | Planned Lean declaration |
|---|---|---|
| 12.34 | Boolean-model percolation probability | `continuumTheta` |
| 12.35–12.36 | A finite positive critical intensity separates the phases, and mean cluster size is finite below it | `continuum_exists_criticalIntensity`, `continuum_meanClusterSize_lt_top_of_lt_critical` |
| following assertions | Positive subcritical exact-size decay rate and uniqueness above criticality | `continuumClusterSize_logRate_pos`, `continuum_uniqueInfiniteCluster_ae` |
| 12.37 | Definition and finite-range geometry of the discretization lattice `Lₙ` | `continuumApproximationGraph` and distance lemmas |
| 12.38 | Cube occupation probability is `1-exp(-λn⁻ᵈ)` | `continuumCubeOccupied_probability` |
| 12.39–12.41 | Infinite Boolean cluster implies an infinite occupied `Lₙ` cluster and yields the lower critical-intensity bound | `continuumApproximationCriticalIntensity_one_le_continuumCriticalIntensity` proves the exact unit-mesh instance; the all-`n` declaration awaits the Poisson repartition law |
| 12.42–12.44 | Mean-size threshold and discrete upper comparison | `continuumMeanClusterThreshold_ge_discreteLowerBound` |
| 12.45 | Enlarged-radius comparison yields the upper critical-intensity bound | `continuumCriticalIntensity_le_discreteUpperBound` |
| 12.46 | The two thresholds agree and equal the limit of the discrete critical expressions | `continuumMeanClusterThreshold_eq_criticalIntensity`, `continuumCriticalIntensity_eq_tendsto_approximation` |

## 2. Core definitions

| Planned definition | Encoding |
|---|---|
| `PeriodicLattice V d` | locally finite connected `SimpleGraph V`, a free `Multiplicative (Fin d → ℤ)` translation action by graph automorphisms, and finitely many vertex orbits |
| `inhomogeneousSetBernoulli q` | map of `Measure.infinitePi` of coordinate Bernoulli measures to `Set ι` |
| `MixedConfiguration G` | an open-site set paired with an open-edge set, with a path open iff all of its vertices and edges are open |
| `LongRangeProfile` | symmetric positive-distance probabilities in `I`, with `p(0)=0` by construction |
| `LongRangeEdge` | non-diagonal `Sym2 ℤ`; its density is determined by endpoint distance |
| `longRangeOpenGraph` | simple graph containing precisely configured long-range pairs |
| `CubicPlaquette3` | coordinate-normal and integer anchor; equipped with a bijection to primal cubic edges |
| `plaquetteBoundary` | four shifted-dual lattice edges; surface boundary is the mod-two symmetric difference of these finsets |
| `SeparatingSphere` | a subset homeomorphic to `Metric.sphere 0 1` together with its two complementary components and bounded/unbounded certificates |
| `FiniteEntangled`, `Entangled` | source definitions for finite edge sets and the finite-subset exhaustion definition for infinite sets |
| `Framework`, `RigidityMatrix`, `GenericallyRigid` | finite graph embedding into `EuclideanSpace ℝ (Fin d)`, its linearized edge constraints, and maximal-rank rigidity |
| `invasionCluster` | primitive recursion on finite vertex/edge sets, selecting the minimum `(label, enumeration-index)` boundary edge |
| `northEastDigraph` | `Digraph (Cubic d)` with one positive coordinate step per arc |
| `FirstPassageEnvironment` | nonnegative extended-real edge weights; real-valued source corollaries assume finite weights almost surely |
| `PoissonCubeConfiguration` | a countable product over integer cubes of a Poisson count and conditionally iid uniform points in the unit cube |
| `continuumBlobGraph` | graph on marked Poisson points, adjacent when their closed radius-one balls intersect |

## 3. Dependency graph and proof order

```text
inhomogeneous countable product measures
    ├── mixed/site/bond specializations (§12.1)
    ├── long-range edge law (§12.3)
    ├── oriented bond law (§12.8)
    └── Poisson cube product construction (§12.10)

periodic-lattice and graph-action API
    ├── ergodicity / mass transport
    ├── generic site susceptibility threshold
    ├── rigidity threshold (§12.6)
    └── first-passage stationarity (§12.9)

long-range finite restrictions + cylinder products
    ├── cut events and branching domination (12.1–12.2)
    ├── Borel–Cantelli necessity in 12.3
    └── Kalikow component-count recursion 12.10–12.19
            └── Theorem 12.3
                    └── power-law multiscale estimates
                            ├── Theorem 12.8
                            └── Theorem 12.9

3D plaquette combinatorics
    ├── exact canonical surface (12.20)
    ├── boundary incidence (12.21)
    └── dual cut/open-cluster comparison + Chs. 5/7
            └── perimeter and area laws (12.22)
                    └── entanglement counting/enhancement
                            ├── Theorem 12.24
                            └── estimate 12.26

Euclidean frameworks + rigidity matroid
    ├── generic-rigidity equivalence
    ├── periodic lattice finite exhaustions
    └── diminishment differential inequality
            └── Theorem 12.28

finite boundary recursion + iid continuous labels
    └── invasion process
            ├── supercritical slab capture (Chapter 7)
            └── empirical occupation law
                    └── 12.29–12.30

directed paths + oriented block construction
    ├── nontrivial oriented threshold
    ├── critical extinction
    └── 2D contact-process edge estimates
            └── 12.33

weighted paths
    ├── deterministic passage-time pseudometric
    ├── product-measure stationarity/integrability
    └── Kingman subadditive ergodic theorem
            ├── axial time constant
            └── rational-direction limits + convexity + covering
                    └── shape theorem

Poisson cube process
    ├── occupation independence and 12.38
    ├── finite-range approximation graph 12.37
    ├── general site sharpness/susceptibility
    └── two geometric couplings
            ├── 12.39–12.44
            └── 12.45
                    └── 12.35 and 12.46
```

### Stacked implementation order

1. **General products and periodic lattices.** Add a countable inhomogeneous Bernoulli measure,
   finite-cylinder probabilities, reindexing invariance, graph actions, mixed configurations,
   and general rooted/unrooted critical parameters.
2. **Long-range base model.** Define profiles, edges, finite restrictions, half-line restrictions,
   component counts, cut events, measurability, and translation invariance.  Prove 12.1–12.5 and
   12.10–12.19, culminating in Theorem 12.3.
3. **Power-law long range.** Formalize dyadic blocks and Newman–Schulman/Aizenman–Newman
   renormalization, then prove Theorems 12.8 and 12.9 for profile families and the canonical
   inverse-power model.
4. **Plaquettes and surfaces.** Build the primal-edge/dual-plaquette bijection and mod-two
   boundary chain complex, prove 12.20–12.21, then the perimeter/area laws 12.22.
5. **Entanglement and rigidity.** Define topological entanglement, prove its finite counting and
   enhancement estimates, construct rigidity matrices and generic rigidity, and prove 12.24,
   12.26, and 12.28.
6. **Invasion and oriented percolation.** Build the deterministic recursion and its measurable
   iid law, close the precise Chapter 7 slab input used by 12.29–12.30, then build the directed
   model and prove 12.31–12.33 plus critical extinction.
7. **First-passage percolation.** Add weighted-path APIs and prove deterministic metric facts;
   prove Kingman’s theorem; construct the time constant and finish the shape theorem under the
   explicit moment condition.
8. **Poisson point process and continuum geometry.** Construct the cube-coded homogeneous
   Poisson process, establish restriction/void/count laws, define clusters, and prove the
   occupation coupling 12.37–12.45.
9. **Continuum conclusions.** Prove 12.35, threshold equality and limit 12.46, subcritical
   exact-size rate positivity, and uniqueness.
10. **Chapter audit and publication.** Generate tests and anti-targets, freeze Comparator
    challenges, conduct independent read-only review, run transitive axiom audits and the clean
    build, complete telemetry/correspondence tables, and open the stacked draft PR.

## 4. Existing repository APIs to reuse

| Existing API | Chapter 12 use |
|---|---|
| `Cubic d`, `cubicGraph d`, `CubicEdge d`, `EdgeConfiguration d` | cubic models, plaquettes, invasion, oriented and first-passage environments |
| `Sym2`, cubic edge endpoint and translation APIs | long-range unordered pairs and all edge-reindexing arguments |
| `setBer`, `bernoulliBondMeasure`, `Measure.infinitePi` patterns | homogeneous and inhomogeneous product laws |
| `finiteBernoulliWeightFamily`, `finiteBernoulliProbabilityFamily` | finite restrictions, long-range component-count calculations, mixed models |
| `DependsOn`, coordinate sigma-algebras, finite-cylinder transfer | event measurability, independence and continuity |
| `siteOpenGraph`, `siteTheta`, `siteCriticalProbability` | §12.1 site model and the continuum discretizations |
| `cubicRegionGraph`, `regionCriticalProbability` | finite-range approximation regions and comparison arguments |
| FKG, BK, Russo, reliability, sprinkling | surface laws, enhancement/diminishment, oriented blocks |
| Chapter 5 susceptibility threshold and exponential decay | general sharpness pattern and subcritical estimates |
| Chapter 6 quasi-subadditive/log-rate infrastructure | surface, oriented-tail and continuum exact-size rates |
| Chapter 7 slab/static renormalization interfaces | area law and invasion capture; any still-conditional premise must be discharged before use |
| Chapter 8 uniqueness and supercritical finite-cluster estimates | invasion and continuum uniqueness patterns |
| Chapter 11 planar duality/inhomogeneous interfaces | §12.1 square/triangular surfaces and the random-orientation half-density result |
| `SimpleGraph.Walk`, append/reverse/take/drop/support/edges | long-range, plaquette, first-passage and cluster paths |
| translation ergodicity and finite-range strong-law modules | stationary cut events, density limits, and invasion empirical laws |

Explicit non-reuse rules:

- `WithinRadius` is configuration Hamming distance, not geometric or first-passage distance.
- `componentSize` maps infinite clusters to zero; it cannot define continuum, oriented, or
  long-range susceptibility.
- `CubicEdge` contains only nearest-neighbour edges and cannot encode long-range bonds.
- `SimpleGraph` cannot encode one-way paths; oriented percolation uses `Digraph`/`Quiver.Path`.
- Existing real cluster-series differentiability does not supply the topological, rigidity,
  Poisson, Kingman, or continuum results.
- Chapter 11 project axioms cannot appear transitively in Chapter 12 declarations accepted as
  assumption-free.

## 5. Mathlib and local APIs by result

| Target | Mathlib APIs | Local APIs | New proof obligation |
|---|---|---|---|
| Inhomogeneous countable products | `Measure.infinitePi`, `Measure.infinitePi_cylinder`, `Measure.pi_pi`, `iIndepFun_infinitePi`, `MeasurableEquiv.setOf` | finite Bernoulli family transfer pack | construct the mapped set measure, cylinder formula, independence and reindexing invariance |
| Periodic lattices | `MulAction`, `MulSemidirectAction`, `SimpleGraph.Iso`, quotient/orbit finiteness | cubic translations and symmetries | bundle freeness, local finiteness, cocompactness, root independence and mass transport |
| 12.1 | infinite products, logarithm/product convergence, the ergodic/strong-law APIs | translation ergodicity, finite cylinders | positive density of cut events and exclusion of infinite components |
| 12.2 | `lintegral_tsum`, monotone convergence, Galton–Watson/branching-process primitives where available | BK/path exploration | build an exploration dominated by mean offspring `2∑p(n)` and treat the critical equality case |
| 12.3 | `ProbabilityTheory.measure_limsup_eq_one` (second Borel–Cantelli), `MeasureTheory.tendsto_measure_iUnion`, `Finset` component counts | coordinate independence and zero–one laws | necessity via isolated vertices; sufficiency via the exact Kalikow recursion and aperiodic support reduction |
| 12.8–12.9 | real `rpow`, regular variation/tendsto algebra, geometric series | LSS/sequential domination, block exploration | prove dyadic-block domination, nontrivial threshold, and the inverse-square discontinuity lower bound |
| 12.20–12.21 | `Finset.symmDiff`, parity/cardinality lemmas, finite product probabilities | cubic edge cylinders | prove canonical surface boundary and select disjoint four-plaquette incidence groups |
| 12.22 | `Filter.Tendsto`, `Real.log`, normalized-limit algebra | Chapter 5 decay, Chapter 7 slab approximation, dual cutsets | turn open connection/cut estimates into both normalized logarithmic laws with finite-index endpoint care |
| Entanglement | `Homeomorph`, `Metric.sphere`, connected components, compact/bounded sets | cubic geometric embedding | supply the missing Jordan–Brouwer separation interface constructively for polyhedral spheres and enumerate finite entangled graphs |
| 12.24/12.26 | finite lattice-animal counting, `Real.exp`, enhancement differential inequalities | Russo/reliability/sprinkling | prove strict positivity, strict comparison with `p_c`, and the `n/log n` tail |
| Framework rigidity | matrices, `Module.finrank`, rank/nullity, polynomial zero-set measure results, `HasFDerivAt` | periodic-lattice API | construct rigidity matrix, prove generic equivalence and finite/infinite containment lemmas |
| 12.28 | matroid closure/rank counting, finite-volume derivatives | Russo diminishment pattern | strict threshold separation and threshold-one iff lattice rigidity |
| Invasion recursion | `Finset.min'`, `Function.argminOn`, primitive recursion, uniform measure on `I` | cubic finite boundaries and edge enumeration | prove finiteness/connectivity/nesting, measurability and almost-sure absence of label ties |
| 12.29–12.30 | strong law, conditional distribution and Cesàro limits | Chapter 7 slab capture, uniqueness | control outlets above `p_c` and identify the empirical conditional-uniform law below `p_c` |
| Oriented model | `Digraph`, `Quiver.Path`, path vertices/decomposition | cubic signed steps, product measures | directed reachability, event measurability, monotonicity and critical parameter |
| 12.33 | stopping times, subadditive/contact-process edge estimates, `Real.sqrt` | block renormalization and exponential decay patterns | prove matching square-root exponential upper/lower bounds without replacing a finite cluster by a natural-cardinality junk value |
| First-passage deterministic layer | `sInf`, `ENNReal`, finite sums, `SimpleGraph.Walk.append`, `edist_eq_sInf` pattern | cubic walks/translations | weighted infimum, triangle inequality, stationarity and measurability |
| Kingman/time constant | conditional expectation, maximal inequalities, `Filter.Tendsto` | translation action/ergodicity | Mathlib has no Kingman theorem; prove the integrable stationary subadditive theorem and specialize it |
| Shape theorem | convex hulls, compactness, Hausdorff/metric neighbourhoods, rational density, finite covers | cubic norm comparisons | directional convergence, deterministic convex limit set and uniform inner/outer inclusions |
| Poisson cube process | `poissonMeasure`, `poissonMeasure_singleton`, `integral_poissonMeasure`, `Measure.bind`, `Measure.pi`, `Measure.infinitePi` | coordinate independence | countable cube coding, iid uniform marks, count/void/restriction laws and scale covariance |
| 12.37–12.38 | Euclidean norm inequalities, floor/cube partitions, exponential identities | site percolation | finite degree of `Lₙ`, overlap implication, independent cube occupation and exact density |
| 12.39–12.44 | `lintegral_tsum`, conditional Poisson expectation | site susceptibility threshold | cluster projection, neighbour count `(4n)^d`, and the exact mean-size comparison factor |
| 12.45–12.46 | rescaling maps, `Real.log`, squeeze theorem | site critical monotonicity | enlarged-sphere coupling, threshold equality, positivity/finiteness and convergence of discrete approximants |
| 12.35 | `csSup`, monotone critical sets | all continuum comparisons | assemble the two phases and finite subcritical mean without assuming the desired sharpness statement |

## 6. Fidelity and endpoint rules

- All source-facing dimension hypotheses are explicit: plaquette/entanglement results are for
  `d=3`; rigidity, oriented, first-passage and continuum results use their stated `d≥2` ranges.
- Long-range profiles take values in `[0,1)` as in the source.  Distance zero is excluded by the
  edge subtype, not assigned an accidental self-loop probability.
- Divergence of `∑p(n)` is represented in `ℝ≥0∞`; no conversion to a real `tsum` loses `∞`.
- Aperiodicity is primarily the additive subgroup generated by the positive support being all of
  `ℤ`; an exact gcd corollary supplies the book’s wording.
- The 12.8/12.9 family parameter omitted by the prose is never hidden.
- `LogAsymptotic` is guarded against zeros and ones before using logarithmic quotients.
- Infinite entanglement uses the source’s finite-subset exhaustion definition.  Alternative
  notions mentioned in the text are recorded, not conflated.
- The rigidity theorem uses a proved standard generic-rigidity equivalence, not an arbitrary
  measure field whose properties merely assert the result.
- Invasion limits are almost-sure `Tendsto` statements.  The critical value `y=p_c` is not added.
- Oriented cluster size uses `ENat`/`ENNReal` so an infinite cluster is not encoded as zero.
- First-passage times use `ℝ≥0∞`; real-valued corollaries require almost-sure finite edge times.
- The source’s vague moment condition is replaced by the cited standard condition and recorded.
- A continuum cluster at a deterministic spatial point is defined through spheres covering that
  point; no Poisson point is silently inserted at the origin.
- The continuum critical statement makes no claim at `λ=λ_c`, matching 12.36.
- Open problems in §§12.5, 12.6, 12.8 and 12.9 are anti-targets and must not be “proved” by an
  over-strong or junk-valued encoding.

## 7. Verification, automated review, and telemetry

### Executable theorem tests

Tests will include:

- homogeneous specialization and two-coordinate cylinders for the inhomogeneous measure;
- long-range profiles of finite range, support `2ℕ`, support containing `1`, zero profile, and a
  divergent harmonic-type profile;
- a counterexample showing why gcd/aperiodicity cannot be omitted from 12.3;
- finite graphs validating the component-count inequalities 12.17–12.19;
- canonical plaquette surfaces at `n=1,2` and exact mod-two boundaries;
- all-open/all-closed configurations for 12.20–12.21;
- connected implies entangled for finite embedded cubic graphs and a linked disconnected example;
- flexible and rigid small frameworks, plus dimension-sensitive examples;
- invasion clusters for the first four steps under a strictly ordered finite label pattern and a
  tie pattern exercising the deterministic tie-break;
- directed clusters at `p=0,1`, `d=1,2`, and the finite/infinite size convention;
- first-passage time under zero, constant-one and one-distinguished-edge environments;
- Poisson void probability for one and two disjoint cubes, scale covariance, and the
  `λ=0` endpoint;
- continuum approximation adjacency at the maximal cube separation and the enlarged-radius
  reverse coupling; and
- endpoint tests for every logarithm, division, `n=0/1`, critical threshold and dimension guard.

### Adversarial review

For every headline theorem, attempt at least one of: the logical negation, a reversed inequality,
removal of a dimension/aperiodicity/moment hypothesis, replacement of strict by non-strict
critical comparison, a junk-valued cluster-size interpretation, or an unguarded logarithmic
endpoint.  Successful anti-targets block publication until the candidate statement is repaired.

Comparator challenges will live under `audit/challenges/chapter-12/` and import prerequisites but
not the candidate theorem.  A frozen review run will live under
`audit/reviews/chapter-12/<date>-<commit>/` and contain the inventory, exact Lean types, test and
counterexample transcripts, Comparator output (or exact tool-unavailability record), transitive
axiom output, an unedited independent read-only review, and `SUMMARY.md`.

### Telemetry ledger

Goal-tracker snapshots are taken immediately before and after these disjoint windows:

- source inventory and plan;
- general product/periodic-lattice infrastructure;
- long-range base infrastructure and each of 12.1, 12.2, 12.3, 12.8, 12.9;
- plaquette infrastructure and 12.20–12.22;
- entanglement infrastructure, 12.24 and 12.26;
- rigidity infrastructure and 12.28;
- invasion infrastructure, 12.29 and 12.30;
- oriented infrastructure and 12.33/critical extinction;
- weighted-path and Kingman infrastructure, time constant, and shape theorem;
- Poisson/continuum infrastructure, 12.35, and 12.37–12.46;
- review/documentation; and
- Git/PR publication.

No estimate or reconstructed number is labelled measured.  Shared infrastructure has its own row
and is not double-counted.  The final PR total is exactly the sum of the disjoint rows.

Measured windows to date:

| Window | Start | End | Time | Tokens |
|---|---:|---:|---:|---:|
| Goal setup, source inventory, repository/API audit, clean stacked worktree, and detailed plan | 0 | first plan checkpoint | 11m40s | 381,254 |
| Axiom-free inhomogeneous products, long-range configuration/graph/measurability/translation, and finite-cylinder weak-law infrastructure | first plan checkpoint | second implementation checkpoint | 36m15s | 493,436 |
| Criterion 12.1: positive cut probability, two-sided cut recurrence, and almost-sure finiteness of every component | second implementation checkpoint | third implementation checkpoint | 12m04s | 191,859 |
| Criterion 12.2: signed-step encoding, nonreversing pair bound at equality, exact path weights, almost-sure local finiteness, and extinction at mean degree at most one | third implementation checkpoint | fourth implementation checkpoint | 29m07s | 409,344 |
| Cubic plaquette cell geometry and exact bounds 12.20–12.21, plus the support/aperiodicity and isolated-origin necessity layers for 12.3 | fourth implementation checkpoint | fifth implementation checkpoint | 25m05s | 370,182 |
| Kalikow finite-component infrastructure and the complete divergent-intensity connectivity proof under the direct generator hypothesis `p₁>0` | fifth implementation checkpoint | sixth implementation checkpoint | 31m53s | 656,347 |
| Theorem 12.3: arbitrary supported-generator Kalikow insertion, support-subgroup closure, and full necessity/sufficiency theorem | sixth implementation checkpoint | seventh implementation checkpoint | 13m27s | 298,408 |
| Power-law long-range analytic/order infrastructure: common-uniform profile monotonicity, exact inverse-power family, summability, critical zero set, and endpoint-safe phase separation | seventh implementation checkpoint | eighth implementation checkpoint | 14m06s | 220,350 |
| Newman--Schulman finite-block infrastructure: aligned block/component selectors, independent child-failure estimate, exact fixed-set cross-bond bound, canonical trace partition, selected-pair estimate, deterministic child-to-parent gluing, and quantitative one-step recursion | eighth implementation checkpoint | ninth implementation checkpoint | 54m35s | 668,145 |
| Newman--Schulman variable-scale completion and upper phase of 12.8: quadratic retained-density scheme, summable error profile, uniform cross-bond parameter choice, strict near-one initialization, translated cluster-size tails, finite-volume mass transport, and positive percolation at some `q<1` | ninth implementation checkpoint | tenth implementation checkpoint | 39m53s | 428,732 |
| First-passage deterministic and iid foundations: extended edge times, path infimum, pseudometric laws, translation covariance, measurable passage times, product law, and axial stationarity/subadditivity | tenth implementation checkpoint | eleventh implementation checkpoint | 12m19s | 170,336 |
| Shared asymptotic/continuum/invasion foundations: normalized logarithmic-rate interface, exact Poisson cube law 12.38, source adjacency 12.37 and cubic subgraph comparison, canonical invasion recursion, state growth, frontier freshness, empirical CDF bounds, and almost-sure absence of label ties | eleventh implementation checkpoint | twelfth implementation checkpoint | 26m30s | 272,278 |
| Oriented-percolation foundations and deterministic invasion capture: north-east reachability, measurable cluster size and critical parameter, endpoint and ordinary-percolation comparisons, least-label invasion choice, and eventual sublevel trapping after capture | twelfth implementation checkpoint | thirteenth implementation checkpoint | 13m52s | 418,326 |
| Rigidity and entanglement foundations: exact differentiable motions and edge-length preservation, rigidity linear map and generic-rank interface, cubic edge segments, finite-exhaustion sphere separation, maximal origin entanglement, measurable infinite-entanglement event, and its density monotonicity/endpoints | thirteenth implementation checkpoint | fourteenth implementation checkpoint | 4h19m05s | 476,865 |
| Ordinary-to-entanglement comparison and finite rigidity events: walk realizations are finite entanglements, infinite open clusters force infinite origin entanglement, `θ≤θ_ent` and `p_c^ent≤p_c`, rigidity rank monotonicity under added edges, explicit finite induced-edge supports, measurability, and increasingness | fourteenth implementation checkpoint | fifteenth implementation checkpoint | 48m38s | 293,814 |
| Rigidity percolation and the cubic-lattice obstruction: infinite rigid witnesses imply ordinary connectivity, rigidity probability/threshold comparisons, exact directed-boundary handshake identity, slice-max boundary injection, rigidity-matrix row-rank bound, proof that no infinite cubic subgraph is rigid, `p_c^rig(ℤ^d)=1`, and the strict cubic instance of 12.28(a) | fifteenth implementation checkpoint | sixteenth implementation checkpoint | 23m36s | 361,550 |
| Deterministic continuum geometry: literal radius-one Boolean graph, half-open cube indexing, projection of continuum walks to `L_n`, finite cube fibers under local finiteness, and the infinite-cluster implication preceding 12.39 | sixteenth implementation checkpoint | seventeenth implementation checkpoint | 4m01s | 74,141 |
| Poisson-cube/site comparison: unit-interval density, exact one-coordinate threshold law, equality of the complete thresholded product measure with iid site percolation, `L_n` theta identification, graph-inclusion comparison, and existence of a finite percolating approximation intensity | seventeenth implementation checkpoint | eighteenth implementation checkpoint | 10m12s | 180,829 |
| Chapter-module integration and reverse continuum geometry: root imports and collision repair, Euclidean triangle/cube-diameter bounds, injective occupied-cube representatives, and the homomorphic embedding of `L_n` clusters into the Boolean model enlarged to radius `1+d/n` | eighteenth implementation checkpoint | nineteenth implementation checkpoint | 12m05s | 240,724 |
| Marked continuum point process and unit-mesh comparison: count/mark product law, measurable active-point Boolean graph, exact cube-count marginal, projection of infinite Boolean components through finite fibers, and the probability inequality corresponding to the unit instance of 12.39 | nineteenth implementation checkpoint | twentieth implementation checkpoint | 16m14s | 245,374 |
| Bounded-degree site branching and the lower continuum phase: finite rooted-walk enumeration, open self-avoiding-path union bound, generic `D p < 1` extinction theorem, finite-degree geometry of the unit approximation graph, and an explicit positive Boolean intensity with `continuumTheta = 0` | twentieth implementation checkpoint | twenty-first implementation checkpoint | 17m39s | 263,415 |
| Source-faithful rooted Boolean transition and mean-threshold foundations: central-port representatives and exact iid law, rooted site-to-Boolean comparison, Poisson superposition coupling and monotonicity, finite positive `lambda_c`, the literal sphere cluster `W(0)` and its measurable extended size, the zero-intensity mean, mean-size monotonicity, and the elementary inequality `lambda_T ≤ lambda_c` from 12.43 | twenty-first implementation checkpoint | twenty-second implementation checkpoint | 1h36m56s | 1,386,479 |
| Weighted site susceptibility and a nonzero finite-mean Boolean regime: generic extended site susceptibility, endpoint-preserving weighted self-avoiding-path domination, measurable projected Poisson mass, finite Poisson second moment, Cauchy--Schwarz without a false independence assumption, geometric path summation, an explicit positive finite-mean intensity, and `0 < lambda_T` | twenty-second implementation checkpoint | twenty-third implementation checkpoint | 38m39s | 504,699 |
| Expected first-passage time constant: a fixed shortest axial walk, exact expected time of every fixed walk under the iid edge law, finite mean axial times under a finite first moment, stationarity-based mean subadditivity, and the normalized Fekete limit | twenty-third implementation checkpoint | twenty-fourth implementation checkpoint | 7m27s | 131,457 |
| Deterministic empirical consequence of invasion capture: persistence of selected edges, a sharp `n-N` good-edge count, ratio bounds, and convergence of `Q_n(y)` to one after the invaded state meets an infinite `y`-sublevel cluster | twenty-fourth implementation checkpoint | twenty-fifth implementation checkpoint | 5m48s | 216,899 |
| First-passage filled-region fidelity repair: separate wet lattice vertices from Grimmett's Euclidean union of closed unit cubes, with membership and monotonicity laws for both encodings | twenty-fifth implementation checkpoint | twenty-sixth implementation checkpoint | 1m22s | 31,306 |
| AB atom-swap symmetry infrastructure: measurable AB walk/connection/infinite-root-cluster events, complement pushforward for homogeneous and inhomogeneous Bernoulli sets, and `theta_AB(p)=theta_AB(1-p)` on every countable graph | twenty-sixth implementation checkpoint | twenty-seventh implementation checkpoint | 18m08s | 153,443 |
| Exact continuum discretization thresholds and sharp reverse geometry: `sqrt d/n` cube diameter, source enlargement `1+sqrt d/n`, graph-antitonic site thresholds, exact phases around `-n^d log(1-p_c(L_n))`, and the unit-mesh Boolean lower bound from 12.39–12.41 | twenty-seventh implementation checkpoint | twenty-eighth implementation checkpoint | 26m15s | 220,954 |
| Cubic periodic-lattice instance: connectedness, finite neighbor sets, the free additive translation action, and a singleton fundamental domain | twenty-eighth implementation checkpoint | twenty-ninth implementation checkpoint | 2m18s | 35,939 |
| Mixed site–bond event infrastructure: finite walk certificates, measurable connection and rooted infinite-cluster events, configuration monotonicity, zero-density endpoint laws, and exact all-bonds site specialization | twenty-ninth implementation checkpoint | thirtieth implementation checkpoint | 2m52s | 35,842 |
| Mixed two-parameter coupling and zero phase: exact product-Bernoulli marginals from two common-uniform fields, joint density monotonicity, and the downward-closed `mixedCriticalSet` | thirtieth implementation checkpoint | thirty-first implementation checkpoint | 1m46s | 28,102 |
| Mixed boundary fidelity and planar-dependency audit: exact bond-density-one reduction to rooted site percolation (including the isolated closed-root edge case), plus a transitive audit showing that the inherited square-threshold declarations still use six named Chapter 11 RSW/duality axioms and therefore cannot discharge Chapter 12 | thirty-first implementation checkpoint | thirty-second implementation checkpoint | 5m07s | 139,271 |
| Geometric/mixed/AB endpoint completion: a proper equivariant geometric periodic-lattice interface and cubic instance, exact cubic site-density-one reduction to ordinary `theta`, both mixed zero axes and upper complement, and zero/one AB endpoint laws | thirty-second implementation checkpoint | thirty-third implementation checkpoint | 9m02s | 142,447 |
| Planar dependency discharge I: a fully discrete left-right/bottom-top walk-intersection theorem for square rectangles, normalized RSW placements, and an explicit boundary-free splicing proof of Figure 11.25 eliminating `rswGluingTwoIntersection_subset` from the Chapter 11 external-axiom layer | thirty-third implementation checkpoint | thirty-fourth implementation checkpoint | 26m43s | 389,840 |
| Planar dependency discharge II: normalized Figure 11.26 placements and a second explicit walk-intersection/splicing proof eliminating `rswGluingThreeIntersection_subset` from the Chapter 11 external-axiom layer | thirty-fourth implementation checkpoint | thirty-fifth implementation checkpoint | 4m17s | 58,121 |
| Planar dependency discharge III: normalized Figure 11.27 placements, four verified crossing incidences, strict boundary-free annulus geometry, arbitrary closed-walk incidence parity, mod-two even-graph reduction, and extraction of an open simple odd-index circuit eliminating `rswCircuitGluingIntersection_subset` from the Chapter 11 external-axiom layer | thirty-fifth implementation checkpoint | thirty-sixth implementation checkpoint | 30m53s | 625,868 |
| Planar dependency discharge IV: a finite primal reachable-set interface, its dual-open bottom--top walk after crossing failure, exact rotate/complement/reindex invariance of the half-density Bernoulli law, the centered self-dual rectangle crossing lower bound `1/2`, and the axiom-free consequence `p_c(ℤ²) ≤ 1/2` | thirty-sixth implementation checkpoint | thirty-seventh implementation checkpoint | 30m21s | 515,778 |
| Planar dependency discharge V: translation of the centered interface bound to even Grimmett rectangles, a three-fresh-edge adaptive extension absorbing the parity shift, boundary-free square embedding, and an axiom-free uniform RSW square-crossing lower bound `1/16` | thirty-seventh implementation checkpoint | thirty-eighth implementation checkpoint | 17m18s | 253,496 |

## 8. PR correspondence table template

| Source result | Page | Natural-language statement | Lean declaration | Key dependencies | Status | Time | Tokens |
|---|---:|---|---|---|---|---:|---:|
| 12.1 | 350 | If `∑ n p_n < ∞` (with strict positive-distance densities), every component is finite almost surely | `longRangeMeasure_real_allComponentsFinite_eq_one_of_summable_nat_mul` | canonical cuts, tail union bound, translation recurrence | proved | 12m04s | 191,859 |
| 12.2 | 350 | If `2∑p_n≤1`, every component is finite almost surely | `longRangeMeasure_real_allComponentsFinite_eq_one_of_meanDegree_le_one` | nonreversing path pairs, Borel--Cantelli local finiteness | proved | 29m07s | 409,344 |
| 12.3 | 354–359 | Long-range graph is a.s. connected iff support is aperiodic and total intensity diverges | `longRange_ae_connected_iff` | inhomogeneous product, Kalikow recursion | proved | 13m27s | 298,408 |
| 12.8 | 356 | Nontrivial transition for `1<α<2` | `longRangePowerLaw_exists_critical` | long-range blocks, quadratic multiscale recursion, mass transport | proved (source hypothesis repaired to a complete monotone family with an explicit positive zero-phase witness) | 1h48m34s | 1,317,227 |
| 12.9 | 356 | Inverse-square dichotomy and first-order lower bound | two inverse-square declarations | long-range blocks | target | measured later | measured later |
| AB atom-swap symmetry | 351 | Interchanging atom types preserves AB connectivity and sends density `p` to `1-p` | `abTheta_complementary_density` | measurable AB connection events, Bernoulli-complement pushforward | proved | 18m08s | 153,443 |
| 12.22 | 361 | Plaquette perimeter and area laws | two plaquette-law declarations | dual surfaces, Chs. 5/7 | target | measured later | measured later |
| 12.24 | 364 | `0<p_c^ent<p_c` | `entanglementCriticalProbability_pos_lt_cubicCriticalProbability` | topology, enhancement | target | measured later | measured later |
| 12.28 | 366 | Rigidity threshold inequalities | `criticalProbability_lt_rigidityCriticalProbability`, `cubic_rigidityCriticalProbability_eq_one`; the arbitrary-lattice iff remains | rigidity matrix, directed boundary deficiency, coordinate-slice obstruction | partially proved (complete cubic consequence; general periodic-lattice diminishment theorem remains) | 23m36s | 361,550 |
| 12.29–12.30 | 367 | Invasion empirical CDF limits | `invasionEmpiricalCDF_tendsto_one_of_state_meets_infiniteSublevelCluster` proves the exact deterministic conclusion after capture; the almost-sure capture input and the subcritical `y/p_c` law remain | invasion recursion, slab capture, conditional uniform law | partially proved | 5m48s | 216,899 |
| 12.33 | 369 | Supercritical oriented finite-cluster two-sided tail | `orientedFiniteClusterTail_twoSided` | directed blocks/contact estimates | target | measured later | measured later |
| time constant/shape theorem | 370–371 | Linear axial rate and deterministic asymptotic shape | `meanAxialFirstPassageTime_div_tendsto` proves the expectation-level Fekete limit; the almost-sure rate and shape declaration remain | iid stationarity, Fekete; then Kingman and convex geometry | partially proved | 7m27s | 131,457 |
| 12.35 | 373–377 | Nontrivial continuum threshold and finite subcritical mean | `continuum_phase_transition`, `continuumMeanClusterThreshold_pos`, `continuumMeanClusterThreshold_le_criticalIntensity`; finiteness at every `lambda < lambda_c` remains | rooted marked Poisson process, weighted site-path susceptibility, central-port comparison, Poisson superposition | partially proved (both literal thresholds are now finite/positive and the strict Boolean phases are proved; equality of thresholds and hence the full subcritical mean conclusion await 12.44–12.46) | 2h15m35s | 1,891,178 |
| 12.37–12.41 | 374–375 | `L_n`, iid cube density, continuum-to-site projection, and `lambda_c ≥ -n^d log(1-p_c(L_n))` | `continuumApproximationGraph`, `continuumCubeOccupied_probability`, `continuumApproximationTheta_eq_zero_of_lt_criticalIntensity`, `continuumApproximationCriticalIntensity_one_le_continuumCriticalIntensity` | Poisson cube law, exact logarithmic inversion, unit-mesh point-process projection | partially proved (the exact transformed threshold is proved for every `n`; the Boolean comparison is proved at `n=1`, while the all-mesh statement still requires the Poisson repartition law) | 26m15s | 220,954 |
| 12.44 | 376 | `lambda_T ≥ -n^d log(1-p_c(L_n))` | `continuumMeanClusterSize_lt_top_of_sqrt_density` is a verified stronger-hypothesis unit-mesh precursor; exact source inequality remains | weighted path comparison, Poisson second moment, site susceptibility | partially proved (no source-faithful threshold inequality claimed yet) | included in 12.35 window | included in 12.35 window |
| 12.46 | 376 | Mean and percolation thresholds agree and are limits of discrete approximations | two continuum limit declarations | 12.37–12.45 | target | measured later | measured later |
| **Total** |  |  |  |  |  | **sum** | **sum** |
