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
- **[target]** Burton-Keane uniqueness of the infinite cluster under standard hypotheses.
- **[target]** Planar duality for bond percolation on the square lattice.
- **[target]** `p_c = 1/2` for bond percolation on `Z^2`.
- **[target]** Random-cluster planar duality and the critical-point formula target
  `p_c(q) = sqrt q / (1 + sqrt q)` under the theorem's valid hypotheses.

Acceptance principle: Tier A validates the encodings, Tier B validates the probabilistic
machinery, and Tier C validates that the formalization reaches core percolation theory.
