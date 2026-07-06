# Topic 03 — Random-Cluster Model

Source: `grimmett-random-cluster-2006`.

## Comparator Map

| Source item | Informal claim | Lean declaration | Status | Notes |
|---|---|---|---|---|
| RC Ch. 1.2 | finite random-cluster measure | `Percolation.RandomClusterModel` | scaffold | no partition function yet |
| RC Thm. 1.10 | Edwards-Sokal marginals | TBD | target | finite graph first |
| RC Ch. 2.1, Thm. 2.1 | Holley inequality for finite monotonic measures | `Percolation.FiniteCubeMeasure.holley_inequality`, `Percolation.FiniteCubeMeasure.stochLE_of_holley` | proved slice | abstract finite cube over `Set ι`; wraps Mathlib's finite-lattice Holley theorem; public statement has `[Fintype ι]` and no public `[DecidableEq ι]` |
| RC Ch. 2.1, Thm. 2.6 / Eq. 2.7 and Eq. 2.14; RC Ch. 2.2, Thm. 2.19 local-pair shape | one-point conditional monotonicity and its cross-multiplied atom form | `Percolation.FiniteCubeMeasure.coordOpenEvent`, `Percolation.FiniteCubeMeasure.forceOpen`, `Percolation.FiniteCubeMeasure.forceClosed`, `Percolation.FiniteCubeMeasure.conditionDenom_singleton`, `Percolation.FiniteCubeMeasure.onePointOpenProb_eq_div`, `Percolation.FiniteCubeMeasure.onePointOpenProb_le_iff_cross`, `Percolation.FiniteCubeMeasure.onePointOpenProb_le_of_holleyCondition`, `Percolation.FiniteCubeMeasure.LocalTwoCoordinateFKG`, `Percolation.FiniteCubeMeasure.localTwoCoordinateFKG_iff_cross`, `Percolation.FiniteCubeMeasure.localTwoCoordinateFKG_of_oneMonotonicMeasure` | proved partial | proves the easy direction by conditioning both measures on the one-coordinate cube, deriving Holley for the conditional pair, and applying stochastic domination to the coordinate-open event; also proves the singleton conditional probability formula, the equivalence with (2.14), the two-coordinate local cross inequality produced by 1-monotonicity, and packages its local FKG lattice form as `LocalTwoCoordinateFKG`. The reverse implication remains future work via Theorem 2.3 |
| RC Ch. 2.2, Thm. 2.16/(2.18) | FKG inequality and increasing-event corollary for strictly positive finite measures satisfying the FKG lattice condition | `Percolation.FiniteCubeMeasure.fkg`, `Percolation.FiniteCubeMeasure.positivelyAssociated_of_fkg`, `Percolation.FiniteCubeMeasure.prob_fkg` | proved slice | source-faithful tilt proof from Holley: shift the second observable positive, tilt by it, verify Holley from the lattice condition, then subtract the shift; standard Lean axioms only |
| RC Ch. 2.2, Eq. 2.20-2.23 / Thm. 2.24 | conditional measures, strong positive association, monotonicity, and one-monotonicity | `Percolation.FiniteCubeMeasure.conditionOn`, `Percolation.FiniteCubeMeasure.StronglyPositivelyAssociated`, `Percolation.FiniteCubeMeasure.MonotonicMeasure`, `Percolation.FiniteCubeMeasure.OneMonotonicMeasure`, `Percolation.FiniteCubeMeasure.stronglyPositivelyAssociated_of_fkgLatticeCondition`, `Percolation.FiniteCubeMeasure.monotonicMeasure_of_fkgLatticeCondition`, `Percolation.FiniteCubeMeasure.oneMonotonicMeasure_of_monotonicMeasure` | proved partial | conditionals are represented on a dedicated finite coordinate type `ConditionCoord F`; the FKG lattice condition is inherited by conditionals, giving `(b) => (a)`, `(b) => (c)`, and `(c) => (d)` of Theorem 2.24. The reverse implications remain future work via Theorems 2.3, 2.6, and 2.19 |
| RC Ch. 2-3 | influence, sharp thresholds, random-cluster `q ≥ 1` specialization, positive association and comparison | TBD | target | Chapter 2.16 abstract FKG is proved; Chapter 3 still needs finite random-cluster weights and the `q ≥ 1` lattice-condition proof |
| RC Ch. 4 | infinite-volume measures | TBD | target | requires topology on configuration space |
| RC Ch. 6 | planar duality | TBD | target | depends on planar graph API |

## Acceptance

- Finite-volume random-cluster probability measure defined.
- Free/wired boundary conditions formalized.
- FKG for `q ≥ 1` proved.
- Edwards-Sokal coupling marginal theorem proved.
- Infinite-volume limit interface stated faithfully.
