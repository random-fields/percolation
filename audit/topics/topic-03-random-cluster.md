# Topic 03 — Random-Cluster Model

Source: `grimmett-random-cluster-2006`.

## Comparator Map

| Source item | Informal claim | Lean declaration | Status | Notes |
|---|---|---|---|---|
| RC Ch. 1.2 | finite random-cluster measure | `Percolation.RandomClusterModel` | scaffold | no partition function yet |
| RC Thm. 1.10 | Edwards-Sokal marginals | TBD | target | finite graph first |
| RC Ch. 2.1, Thm. 2.1 | Holley inequality for finite monotonic measures | `Percolation.FiniteCubeMeasure.holley_inequality`, `Percolation.FiniteCubeMeasure.stochLE_of_holley` | proved slice | abstract finite cube over `Set ι`; wraps Mathlib's finite-lattice Holley theorem; public statement has `[Fintype ι]` and no public `[DecidableEq ι]` |
| RC Ch. 2.2, Thm. 2.16/(2.18) | FKG inequality and increasing-event corollary for strictly positive finite measures satisfying the FKG lattice condition | `Percolation.FiniteCubeMeasure.fkg`, `Percolation.FiniteCubeMeasure.positivelyAssociated_of_fkg`, `Percolation.FiniteCubeMeasure.prob_fkg` | proved slice | source-faithful tilt proof from Holley: shift the second observable positive, tilt by it, verify Holley from the lattice condition, then subtract the shift; standard Lean axioms only |
| RC Ch. 2-3 | influence, sharp thresholds, random-cluster `q ≥ 1` specialization, positive association and comparison | TBD | target | Chapter 2.16 abstract FKG is proved; Chapter 3 still needs finite random-cluster weights and the `q ≥ 1` lattice-condition proof |
| RC Ch. 4 | infinite-volume measures | TBD | target | requires topology on configuration space |
| RC Ch. 6 | planar duality | TBD | target | depends on planar graph API |

## Acceptance

- Finite-volume random-cluster probability measure defined.
- Free/wired boundary conditions formalized.
- FKG for `q ≥ 1` proved.
- Edwards-Sokal coupling marginal theorem proved.
- Infinite-volume limit interface stated faithfully.
