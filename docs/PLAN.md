# PLAN — percolation formalization targets

Status: seed plan, source-ordered from Grimmett's two books. The next automation step is to turn
this into page-anchored JSON in `kg/derived/`.

## Source P — Grimmett, *Percolation*, 2nd ed.

| order | source | target | layer | Mathlib/local status |
|---|---|---|---|---|
| P1 | Ch. 1.3 | Bond percolation on a graph/lattice; edge configurations | Core/Bernoulli | partial: graphs/probability exist, percolation API absent |
| P2 | Ch. 1.4 | Critical probability and percolation probability | Critical | absent |
| P3 | Ch. 1.6 | Site percolation and bond-to-site transformation | Core/Bernoulli | absent |
| P4 | Ch. 2.1 | Increasing events and stochastic order | Bernoulli | partial: order APIs exist |
| P5 | Ch. 2.2 | FKG inequality for product percolation | Bernoulli | partial: finite products/order likely reusable |
| P6 | Ch. 2.3 | BK/Reimer disjoint-occurrence inequality | Bernoulli | absent/deep |
| P7 | Ch. 2.4 | Russo's formula and pivotal edges | Bernoulli | absent |
| P8 | Ch. 3 | Equalities and inequalities for critical probabilities | Critical | absent |
| P9 | Ch. 4 | Number of open clusters per vertex | Critical | absent |
| P10 | Ch. 5 | Menshikov/Aizenman-Barsky subcritical threshold methods | Critical | absent/deep |
| P11 | Ch. 6 | Systematic subcritical phase estimates | Critical | absent/deep |
| P12 | Ch. 7 | Supercritical renormalization and slab criteria | Critical | absent/deep |
| P13 | Ch. 8 | Burton-Keane uniqueness of the infinite cluster | Critical | absent/deep |
| P14 | Ch. 9 | Scaling theory and critical exponents, informal interface | Critical | external/interface first |
| P15 | Ch. 10 | High-dimensional mean-field/lace-expansion statements | Critical | external/interface first |
| P16 | Ch. 11 | Planar duality and `p_c = 1/2` for square-lattice bond percolation | Planar | absent/deep |
| P17 | Ch. 13 | Related processes: continuum, first-passage, electrical networks, random-cluster | Extensions | later |

## Source RC — Grimmett, *The Random-Cluster Model*

| order | source | target | layer | Mathlib/local status |
|---|---|---|---|---|
| RC1 | Ch. 1.2 | Finite random-cluster measure and partition function | RandomCluster | absent |
| RC2 | Ch. 1.4 | Edwards-Sokal coupling and Potts/Ising marginals | RandomCluster | absent |
| RC3 | Ch. 2 | Stochastic ordering, positive association, influence, sharp thresholds | RandomCluster | partial/absent |
| RC4 | Ch. 3 | Conditional probabilities, comparison inequalities, series/parallel laws | RandomCluster | absent |
| RC5 | Ch. 4 | Boundary conditions and infinite-volume weak limits | RandomCluster | absent/deep |
| RC6 | Ch. 5 | Random-cluster phase transition and percolation probability | RandomCluster/Critical | absent/deep |
| RC7 | Ch. 6 | Planar random-cluster duality and critical point formula | RandomCluster/Planar | absent/deep |
| RC8 | Ch. 7 | Higher-dimensional duality and surface/plaquette representations | RandomCluster | absent/deep |
| RC9 | Ch. 8 | Dynamics, Glauber/Gibbs sampler, coupling from the past | RandomCluster | partial: Markov chain APIs may help |
| RC10 | Ch. 9 | Flow polynomial and random-current-adjacent representations | RandomCluster | later |
| RC11 | Ch. 10 | Complete graph and binary tree exact calculations | RandomCluster | later |
| RC12 | Ch. 11 | Applications to Potts, Ashkin-Teller, spin-glass, lattice-gas models | Interfaces | later |

## First Concrete Sprint

1. Replace `BaseGraph` with the chosen Mathlib graph carrier.
2. Define finite bond configurations as functions on a finite edge type.
3. Define increasing events and prove closure under intersection/union.
4. Define Bernoulli product measure on finite edge configurations.
5. State and prove finite product FKG, or bridge to an existing Mathlib theorem.
6. Define open connection and cluster in terms of graph walks.
7. Define finite-volume random-cluster weights and prove the partition function is positive
   under nonempty finite edge sets and `q > 0`.
