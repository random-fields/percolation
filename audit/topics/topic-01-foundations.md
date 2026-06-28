# Topic 01 — Foundations and Configurations

Sources: `grimmett-percolation-1999` Ch. 1; `grimmett-random-cluster-2006` Ch. 1.

## Comparator Map

| Source item | Informal claim | Lean declaration | Status | Notes |
|---|---|---|---|---|
| P Ch. 1.3 | bond configuration assigns open/closed states to edges | `Percolation.BondConfiguration` | scaffold | replace with production Mathlib graph-edge encoding |
| P Ch. 1 | open path and cluster | `Percolation.OpenConnection`, `Percolation.openCluster` | scaffold | current `OpenConnection` is only a placeholder |
| RC Ch. 1.2 | random-cluster model on finite graph | `Percolation.RandomClusterModel` | scaffold | weight/measure not yet defined |

## Acceptance

- Production graph carrier selected.
- Open paths represented by graph walks.
- Cluster agrees with connected component of the open subgraph.
- Finite configuration space supports Bernoulli and random-cluster measures.
