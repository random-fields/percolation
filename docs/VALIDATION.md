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
- **[target]** Subcritical exponential decay, first as a conditional theorem if needed.
- **[target]** Burton-Keane uniqueness of the infinite cluster under standard hypotheses.
- **[target]** Planar duality for bond percolation on the square lattice.
- **[target]** `p_c = 1/2` for bond percolation on `Z^2`.
- **[target]** Random-cluster planar duality and the critical-point formula target
  `p_c(q) = sqrt q / (1 + sqrt q)` under the theorem's valid hypotheses.

Acceptance principle: Tier A validates the encodings, Tier B validates the probabilistic
machinery, and Tier C validates that the formalization reaches core percolation theory.
