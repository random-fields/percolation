# PLAN — percolation formalization targets

Status: seed plan, source-ordered from Grimmett's two books. The next automation step is to turn
this into page-anchored JSON in `kg/derived/`.

## Source P — Grimmett, *Percolation*, 2nd ed.

| order | source | target | layer | Mathlib/local status |
|---|---|---|---|---|
| P1 | Ch. 1.3 | Bond percolation on a graph/lattice; edge configurations | Core/Bernoulli | partial: graphs/probability exist, percolation API absent |
| P2 | Ch. 1.4 | Critical probability and percolation probability | Critical | absent |
| P3 | Ch. 1.6 | Site percolation and bond-to-site transformation | Core/Bernoulli | **proved for cubic regions**: the finite directed-edge comparison is exhausted over induced metric balls; `siteTheta_densityI_pos_of_regionCriticalProbability_lt` and `siteCriticalProbability_lt_one_of_regionCriticalProbability_lt_one` give the infinite-volume and critical-probability conclusions |
| P4 | Ch. 2.1 | Increasing events and stochastic order | Bernoulli | **proved**: `IsIncreasingEvent`/`DependsOn` vocabulary, finite-cube transfer pack, Thm 2.1 via the uniform coupling (`Increasing.lean`, `FiniteCube.lean`, `Coupling.lean`) |
| P5 | Ch. 2.2 | FKG inequality for product percolation | Bernoulli | **proved**: finite-support FKG via four functions theorem (`FKG.lean`) and general increasing measurable events via measure-density approximation (`FKGInfinite.lean`); Thm 2.8 in `Critical/VertexIndependence.lean` |
| P6 | Ch. 2.3 | BK/Reimer disjoint-occurrence inequality | Bernoulli | **proved**: BK 2.12/2.14/2.15 by the two-copy method (`BK.lean`), limit form (2.17) (`DisjointConnections.lean`); Reimer 2.19 recorded as anti-target |
| P7 | Ch. 2.4 | Russo's formula and pivotal edges | Bernoulli | **proved**: Thm 2.25 + (2.29)/(2.31)/2.32/(2.33) (`Russo.lean`); §2.5 reliability inequalities 2.34/2.36/2.38 (`Reliability.lean`); §2.6 sprinkling 2.45 proved (`Sprinkling.lean`) |
| P8 | Ch. 3 | Equalities and inequalities for critical probabilities | Critical | absent |
| P9 | Ch. 4 | Number of open clusters per vertex | Critical | **4.20 and 4.31 proved unconditionally**: concrete rooted animals discharge (4.25), `cubicAnimal_largeDeviation_sharp_one_le` has the source prefactor/exponent for every `n≥1`, and `concreteClusterDensitySeries_contDiffOn_unitInterval` proves `C¹` on `[0,1]`; Theorem 4.2 remains conditional on the multiparameter box-ergodic/boundary inputs and its `L¹` conclusion remains a target |
| P10 | Ch. 5 | Menshikov/Aizenman-Barsky subcritical threshold methods | Critical | **proved for the selected complete chapter scope**: both independent proofs of 5.2, 5.3–5.8, full sausage/renewal chain 5.12–5.24, ghost equations 5.42–5.53, and Appendix I limits 5.64–5.66; see `audit/topics/topic-05-exponential-decay.md` |
| P11 | Ch. 6 | Systematic subcritical phase estimates | Critical | **proved for the declared complete chapter scope**: 6.1/6.10/6.14, two-point and correlation-length results, tree-graph moments, corrected 6.75, exact-size rate 6.78, and genuine complex-series analyticity 6.108; false literal readings of 6.75 and 6.87 are rejected with proved corrected forms; see `audit/topics/topic-06-exponential-decay-analyticity.md` |
| P12 | Ch. 7 | Supercritical renormalization and slab criteria | Critical | **in progress**: induced-region/site percolation, finite-history exploration, Lemmas 7.9/7.17/7.24, the infinite-volume bond-to-site adapter, full transverse steering frames, pathwise final-density restart certificates, finite deterministic target-seed cells, the literal positive `2d`-branch **radial phase**, source-order root/later-site schedules, actual-selected-seed `T*` containment, generic reused-coordinate interval fibers, and the exact edge updates (7.31)--(7.32) are proved. The source-faithful state uses the whole cubic edge-line boundary `ΔE_k`, lets `E_Z` change by stage, and is identified with the root radial update. Its current `profile` is a deterministic Markov cell; its stronger `historyProfile` retains both endpoints of every absorbed boundary interval and is preserved on one explicit probability-one coupling support. The concrete state-dependent root-prefix range is finite, its reachable accumulated-history cells are pairwise disjoint, and a canonical `RootExtensionPrefixStateIndex` generates their exact classifier and framed stage. A separate finite threshold-pattern refinement gives an exact almost-sure partition of the radial event with any prescribed selected-seed profile, but review proved that this full refinement is too strong for Lemma 7.17: it may constrain a later restart coordinate or strengthen its boundary lower threshold. The replacement `stableRootExtensionPrefixHistory` keeps the unchanged state cells. A successful radial branch now yields an explicit explored certificate containing its last exit, exterior walk, outward edge, and complete target seed. Those coordinates remain open throughout every post-radial and root-prefix accumulated-history cell. More strongly, the recursive event comprising radial success and the first `k` successful framed restarts is constant on every canonical `k`-prefix history cell, and its stable-cell union is equal to that semantic event on the probability-one nonnegative coupling support for every `k`. Probability-one support transfer now converts these stage-specific partitions into the exact one-step measure recurrence and its `(1-ε)^(2d)` iteration. Reachable lower-threshold bounds prove that the canonical budgeted policy takes the literal `+δ` branch throughout the root prefix under one explicit total-budget inequality; no false global equality on arbitrary states is assumed. The replay layer now preserves one final-density `RootedOpen` component through every actual root and later-site prefix, and every published selected seed is connected to its physical root anchor under a separate reachable-prefix threshold certificate. Every limiting accepted coarse site has a finite first-success time and an exact realized suffix history. The remaining global obligations are the concrete non-root `2d+1` overlap budget, injectivity and literal thickening containment for the random selected anchors, and the realized-state/replay-state identification needed to apply the random-anchor assembly. Half-space/static headline assemblies also remain; see `audit/topics/topic-07-dynamic-static-renormalization.md` |
| P13 | Ch. 8 | Supercritical phase: uniqueness, continuity, finite-cluster rates, and geometry | Critical | **substantial assumption-free core plus complete Chapter 8 strip argument**: Theorems 8.1, 8.8, 8.18, 8.53, 8.61, and 8.97 and their named lemmas are complete. Equations 8.43–8.48 now include arbitrary-coordinate independence, canonical fresh-strip entrances, iterated contraction, and exponential absorption. For `d≥3`, Theorem 8.21, compact-uniform (8.91), open-interval Theorem 8.92, (8.64), and Theorem 8.99 are assembled from the single visible `SlabCriticalApproximation d` premise, exactly unfinished Chapter 7 Theorem 7.2. Remaining: discharge that premise, the separate planar route, Theorem 8.65's source-omitted high-dimensional topology, and the `p=1` endpoint of 8.92 based on (8.88). See `audit/topics/topic-08-supercritical-phase.md`. |
| P14 | Ch. 9 | Scaling theory and critical exponents, informal interface | Critical | external/interface first |
| P15 | Ch. 10 | High-dimensional mean-field/lace-expansion statements | Critical | external/interface first |
| P16 | Ch. 11 | Planar duality and `p_c = 1/2` for square-lattice bond percolation | Planar | **complete modulo explicitly cited external-reference axioms**: exact `p_c(ℤ²)=1/2`, half-density rectangle duality, RSW algebra, centered supercritical crossing tails, and tube decay are proved; Proposition 11.2/Kesten topology, Russo lowest crossing, source-facing descendants, the cited CLT, and inhomogeneous critical surfaces are isolated and audited as project axioms; see `audit/topics/topic-11-bond-percolation-two-dimensions.md` |
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
