# VERIFICATION — informal to formal map

This is the human-readable comparator surface. Each row should eventually cite a source id from
`formalization.yaml`, a stable book location, and an exact Lean name.

## Primary Objects

| Object | Informal | Lean target | Source |
|---|---|---|---|
| Base graph/lattice | vertices and nearest-neighbor bonds | `Percolation.BaseGraph`, later Mathlib graph carrier | Grimmett P Ch. 1 |
| Bond configuration | each edge is open or closed | `Percolation.BondConfiguration` | P Ch. 1.3 |
| Increasing event | event preserved when more edges are opened | `Percolation.IncreasingEvent` | P Ch. 2.1; RC Ch. 2 |
| Open connection | vertices joined by an open path | production replacement for `OpenConnection` | P Ch. 1 |
| Open cluster | connected component of open graph containing a vertex | `Percolation.openCluster` | P Ch. 1 |
| Bernoulli bond model | independent edges open with probability `p` | `Percolation.BernoulliBond` | P Ch. 1.3 |
| Critical probability | threshold for infinite open cluster | `Percolation.CriticalParameter` | P Ch. 1.4 |
| Random-cluster measure | edge configuration weight proportional to `p^o (1-p)^c q^k` | `Percolation.RandomClusterModel` | RC Ch. 1.2 |
| Edwards-Sokal coupling | joint Potts/random-cluster measure with both marginals | TBD | RC Ch. 1.4 |

## Theorem Map

| Status | Claim | Lean name | Source | Comparator note |
|---|---|---|---|---|
| target | FKG inequality for increasing events in Bernoulli percolation | TBD | P Ch. 2.2 | finite product-space theorem first |
| target | BK/Reimer inequality | TBD | P Ch. 2.3 | likely deep; isolate finite statement |
| target | Russo's formula | TBD | P Ch. 2.4 | pivotal-edge encoding is central |
| target | Burton-Keane uniqueness | TBD | P Ch. 8 | requires amenability/mass transport design |
| target | Square-lattice bond threshold `p_c = 1/2` | TBD | P Ch. 11 | planar duality plus crossing estimates |
| target | Random-cluster FKG for `q ≥ 1` | TBD | RC Ch. 3 | finite graph first |
| target | Edwards-Sokal marginal theorem | TBD | RC Thm. 1.10/1.13 | exact finite graph coupling |

## Axiom Certificate

No project axioms are currently present. Any future axiom must be named in `AXIOM_AUDIT.md`
and have a vetting card in `audit/vetting/`.
