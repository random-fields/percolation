# VALIDATION — acceptance suite

Status legend: `[target]`, `[done]`, `[done mod axioms]`.

## Tier A — Encoding Sanity

- **[target]** Finite bond configurations are equivalent to subsets/functions on a finite edge set.
- **[target]** Increasing events are closed under finite intersection and union.
- **[target]** Product Bernoulli measure is a probability measure and assigns cylinder events the
  expected product weights.
- **[target]** Open connection is reflexive and transitive via graph-walk concatenation.
- **[target]** The open cluster of a vertex is exactly the set of vertices connected to it by open paths.
- **[target]** Random-cluster finite-volume weights normalize to a probability measure when `q > 0`.

## Tier B — Structural Theorems

- **[target]** FKG inequality for increasing events under Bernoulli product percolation.
- **[target]** Russo's formula for finite edge sets and increasing events.
- **[target]** Coupling monotonicity in `p` for Bernoulli percolation.
- **[target]** Random-cluster FKG for `q ≥ 1` on finite graphs.
- **[target]** Free/wired boundary-condition stochastic ordering.
- **[target]** Edwards-Sokal coupling has Potts and random-cluster marginals.

## Tier C — Percolation Theorems

- **[target]** Existence and monotonicity of the critical probability `p_c`.
- **[done]** Subcritical exponential decay by Menshikov's source-order argument
  (`radiusTail_exponential_decay_of_lt_critical`), including the full pivotal-sausage,
  renewal, master-inequality, and inverse-square-root bootstrap chain; independently,
  Aizenman–Barsky's ghost-field route proves finite susceptibility below `p_c`.
- **[done]** Chapter 6 systematic subcritical estimates: coordinate-box and two-point exponential
  rates, correlation length, tree-graph moment bounds, corrected exponential cluster-size tail,
  exact cluster-size decay rate, and analytic `κ`/`χ` below `p_c`. False printed endpoint/infinite-
  set readings are explicit rejected anti-targets rather than silently strengthened theorems.
- **[target]** Chapter 7 dynamic and static renormalization. The finite-history foundation and
  source-facing adaptive exploration Lemma 7.24, Theorem 7.65, and the finite directed-edge
  bond-to-site comparison needed by Theorem 7.2 are done. Its exact finite-ball exhaustion and
  strict site-critical adapter are now also proved. Successful restart cells now carry literal
  final-density inlet-to-target bond paths through a full transverse-sign steering frame and
  retain a deterministic finite target-seed witness. The central seed, all `2d` signed root
  branches, their freshness factorization, and one common pair of Lemma 7.17 radii are now
  constructed with positive mass; composing the concrete `2d+1` non-root seed chain remains
  before Theorem 7.2. Theorems 7.2, 7.35, 7.61, and 7.68 remain targets.
- **[done]** Burton–Keane uniqueness of the infinite open cluster (Theorem 8.1), including the
  compatible-three-partition bound, finite-energy elimination of finite multiplicities, and the
  amenable trifurcation boundary contradiction.  Chapter 8 also has assumption-free proofs of
  supercritical continuity, the finite radius and truncated-connectivity logarithmic rates, the
  lower cluster-size tail, qualitative box crossing, and the exact local interior/boundary edge
  local and aggregate edge balances and the pointwise finite-box density laws underlying 8.99.
  A summable cylinder approximation and Borel–Cantelli replace the unavailable multiparameter
  ergodic theorem and prove the ratio from the positive radius exponent.  Equation
  8.43 and the full fresh-strip contraction 8.44--8.48 are proved.  For `d≥3` they give `a(p)>0`
  from the single explicit Chapter 7 premise `SlabCriticalApproximation d`.
  The higher-derivative animal-series argument in Theorem 8.92 is proved for every compact
  interior interval from the exact uniform form of (8.91), including the `theta`, finite
  susceptibility, and cluster-density identifications.
  The compact-uniform form of (8.91), the full open-interval `C∞` conclusion of 8.92, equation
  8.64, and Theorem 8.99 are now assembled for `d≥3` from that same visible slab premise.  The
  remaining targets are the unconditional discharge of Chapter 7's premise, the separate planar
  route, Theorem 8.65's omitted high-dimensional boundary topology, and the `p=1` endpoint of
  8.92 based on (8.88).  See
  `audit/topics/topic-08-supercritical-phase.md`.
- **[done mod axioms]** Chapter 11 planar duality interfaces, RSW, two-dimensional tail results,
  power-law interfaces, and inhomogeneous critical surfaces. Results whose proofs the source
  delegates to Kesten, Russo, the CLT literature, or the original star–triangle literature are
  explicit project axioms with a vetting card and transitive audit.
- **[done mod axioms]** `p_c = 1/2` for bond percolation on `Z^2`, proved in Lean from the exact
  finite rectangle calculation, RSW/independent barriers, and the explicitly named external
  planar-topology boundary.
- **[target]** Random-cluster planar duality and the critical-point formula target
  `p_c(q) = sqrt q / (1 + sqrt q)` under the theorem's valid hypotheses.

Acceptance principle: Tier A validates the encodings, Tier B validates the probabilistic
machinery, and Tier C validates that the formalization reaches core percolation theory.
