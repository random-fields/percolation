# FRONTIER — Mathlib and local gap inventory

Status: initial heuristic inventory. Re-check with `rg`/Loogle before proving.

## Likely Present in Mathlib

| Building block | Expected location | Use |
|---|---|---|
| finite sets, finite products, sums | `Mathlib.Data.Finset`, algebra/order libraries | product weights, partition functions |
| simple graphs and walks | `Mathlib.Combinatorics.SimpleGraph.*` | finite graphs, paths, clusters |
| probability measures | `Mathlib.MeasureTheory`, `Mathlib.Probability` | infinite-volume limits and events |
| finite probability mass functions | `PMF` / finite measure APIs | finite-volume random-cluster/Bernoulli measures |
| filters and weak convergence primitives | topology/measure libraries | infinite-volume weak limits |
| real inequalities and monotonicity | analysis/order libraries | FKG/Russo/sharp-threshold estimates |

## Likely Absent

- Percolation-specific edge/site configuration API.
- Bernoulli bond/site percolation measures on graphs/lattices.
- Open cluster, percolation probability, susceptibility, critical threshold.
- FKG/BK/Russo specialized to percolation events.
- Burton-Keane uniqueness theorem.
- Planar percolation duality and square-lattice `p_c = 1/2`.
- Random-cluster finite/infinite-volume measures and boundary conditions.
- Edwards-Sokal coupling.
- Random-cluster stochastic ordering and critical point theory.

## Local Repos to Search

- `RandomFields`: finite graph and Markov/Dirichlet-form infrastructure.
- `optimal-transport`: agent methodology and source-plan structure.
- `brownian-motion`, `statlib`, `mathlib4`: probability and graph-adjacent APIs.

## First Search Commands

```bash
rg -n "SimpleGraph|Walk|Adj" .lake/packages/mathlib/Mathlib/Combinatorics
rg -n "FKG|positive association|Association|Increasing" .lake/packages/mathlib/Mathlib
rg -n "PMF|ProbabilityMassFunction|Measure.map|iInf|support" .lake/packages/mathlib/Mathlib
```
