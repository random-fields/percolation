# Theorem 7.65 repaired correspondence

| Field | Review evidence |
|---|---|
| Source result | `grimmett-percolation-1999`, Theorem 7.65 and (7.66)–(7.67), p. 179 |
| Natural-language statement | For fixed dimension and dependence range there exists one nondecreasing `π : [0,1] → [0,1]`, with `π(δ) → 1` as `δ → 1`, such that every `k`-dependent site field whose one-site marginals are at least `δ` stochastically dominates iid site percolation of density `π(δ)`. |
| Mathematical conventions | Densities include both endpoints. Stochastic domination means the expectation inequality for every bounded increasing measurable real observable. The source lattice is `ℤ^d`, `d≥1`. |
| Lean declaration | `Percolation.exists_cubic_lssDominationDensity` |
| Exact Lean type | `∀ d k, 0 < d → ∃ pi : I → I, Monotone pi ∧ Tendsto pi (𝓝 1) (𝓝 1) ∧ ∀ delta mu, IsProbabilityMeasure mu → KDependent (cubicGraph d) k mu → (∀ current, delta ≤ mu.real {η | current ∈ η}) → StochasticallyDominates mu setBer(Set.univ, pi delta)` |
| General engine | `Percolation.exists_lssDominationDensity`, with an explicit enumeration and uniform dependence-neighborhood bound |
| Dependencies | (7.64), the finite LSS dilution proof (7.114)–(7.122), compact Boolean-product regularity, layer cake, cubic metric-ball cardinality |
| Divergence | The abstract engine is denumerable because it accepts `e : ℕ ≃ V`; finite countable types use the separate finite theorem. There is no source loss because `Cubic d` is denumerable for `d>0`. |
| Case tests | `cases/LSSFunctionCases.lean`: literal existential application, monotonicity, limit, zero endpoint, one endpoint, all-closed and all-open domination |
| Adversarial tests | `counterexamples/LSSFunctionCounterexamples.lean`: refutes asking a marginal density strictly below one to dominate iid density one in the old fixed-target form |
| Comparator | Challenge and solution wrappers recorded; not run locally because the required pinned Linux tools are unavailable |
| Axioms | `propext`, `Classical.choice`, `Quot.sound` only |
| Independent verdict | PASS after repair; unedited report in `independent-review.md` |
| Status | proved faithfully on `ℤ^d`, `d≥1` |
| Time/tokens | not measured; post-pause work is never reconstructed |

The prior frozen review at `2026-07-12-d72bdde` remains a failed source-fidelity record and contains
the unedited report that triggered this repair.
