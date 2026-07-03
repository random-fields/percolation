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
| P5 | Ch. 2.2 | FKG inequality for product percolation | Bernoulli | proved: finite weighted product FKG, finite-support observable FKG, measurable/countable event lift, decreasing variants, finite-family iterated FKG, covariance FKG for finite nonnegative sums of increasing event indicators, threshold-step dominated-convergence bridge, bounded-observable FKG, and the general square-integrable observable form, including the cubic bond wrapper |
| P6 | Ch. 2.3, Thm. 2.12/Eq. 2.14/Thm. 2.15/Eq. 2.17 | BK disjoint-occurrence inequality | Bernoulli | proved directly from Grimmett's pp. 39-40 two-copy swap-injection/telescoping proof: binary and repeated heterogeneous finite-trace BK, homogeneous finite-support product-measure BK, finite-family trace-to-cylinder bridges for open-witness and ordinary disjoint occurrence, source-facing `grimmettTheorem212_homogeneous`, `grimmettEquation214_homogeneous`, `grimmettTheorem215`, and finite path-family `grimmettEquation217_finite`; this proof path does not use Reimer's inequality |
| P6R | Ch. 2.3, Thm. 2.19 | Reimer inequality and conditional Reimer-to-BK interfaces | Bernoulli | separate/deferred: existing deterministic forcing, Reimer-box occurrence, finite-cube slice, and conditional Reimer-to-BK wrappers are kept as auxiliary infrastructure, but they are not the proof route for BK on this branch; the general interior-parameter Reimer probability inequality and arbitrary finite-support cardinality Reimer remain target and are not axiomatized |
| P7 | Ch. 2.4 | Russo's formula and pivotal edges | Bernoulli | finite event, finite conditional-pivotal, finite-support product/bond, random-variable, and second-difference Russo formulas proved; infinite/measurable event lift and pivotal-pair refinements target |
| P7a | Ch. 2.5 | Reliability covariance and derivative inequalities | Bernoulli | finite covariance form of Theorem 2.34 plus finite Cauchy-Schwarz upper bound (2.36a), monotone lower bound (2.36b)/(2.37), scalar inequality (2.44), finite power inequality (2.42), finite log-ratio monotonicity (2.38), and finite-support product/bond wrappers proved; infinite/general threshold consequences remain target |
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
5. State and prove finite product FKG, lift it to measurable/countable Bernoulli product events,
   and close the square-integrable observable form of Theorem 2.4.
6. Define open connection and cluster in terms of graph walks.
7. Define finite-volume random-cluster weights and prove the partition function is positive
   under nonempty finite edge sets and `q > 0`.
