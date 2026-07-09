# Topic 04 — Open Clusters per Vertex

Source: `grimmett-percolation-1999`, Chapter 4, pp. 77–86.

## Comparator Map

| Source item | Informal statement | Exact Lean declaration | Status | Divergence / remaining input |
|---|---|---|---|---|
| §4.1, (4.1) | `κ(p) = E_p(|C|⁻¹)`, with an infinite cluster contributing zero | `Percolation.openClustersPerVertex`, `Percolation.openClustersPerVertex_eq_integral_inv_ncard` | proved | The Lean definition uses `componentSize`; the bridge proves that this is the `ncard` of the production open cluster. Lean's `ncard` convention makes an infinite set contribute zero after reciprocal coercion, matching the book. |
| §4.1, (4.4)–(4.8) | summing reciprocal component sizes over a finite graph counts components | `Percolation.componentSize`, `Percolation.componentWeight`, `Percolation.sum_componentWeight_eq_componentCount`, `Percolation.sum_componentWeight_fiber_eq_one` | proved | Generalized from cubic boxes to arbitrary finite simple graphs. |
| §4.1, (4.10)–(4.12) | the induced-box component count is squeezed between the reciprocal-cluster sum and that sum plus a boundary error | `Percolation.componentWeightAverage_le_normalizedComponentCount`, `Percolation.componentCount_le_weightSum_add_escaping`, `Percolation.componentCount_le_weightSum_add_boundary`, `Percolation.normalizedComponentCount_tendsto_of_sandwich` | proved | The escaping-component-to-boundary injection/cardinality estimate is exposed as a hypothesis in `componentCount_le_weightSum_add_boundary`; no cubic boundary cardinality theorem is claimed. |
| §4.1, Theorem (4.2) | `K_n/|B(n)| → κ(p)` almost surely and in `L¹` | `Percolation.normalizedCubicOpenClusterCountIn_tendsto_ae_of_ergodicAverage` | proved modulo named hypotheses | The almost-sure squeeze is proved for any exhaustion `B`; `haverage` is exactly the missing multiparameter box pointwise-ergodic input (4.9), while `hboundary`/`hupper` encode (4.11)–(4.12). The source's `L¹` convergence is not formalized. Status is not “faithful” until those inputs are instantiated for `cubicBoxVertices`. |
| §4.1, cubic box geometry | `B(n)=[-n,n]^d∩ℤ^d`, so `|B(n)|=(2n+1)^d` | `Percolation.cubicBoxVertices`, `Percolation.mem_cubicBoxVertices`, `Percolation.cubicBoxVertices_card` | proved | Exact encoding on `Fin d → ℤ`. |
| §4.1, open graph / cluster identification | graph connected components in the open subgraph are the percolation clusters | `Percolation.cubicOpenGraph_reachable_iff`, `Percolation.cubicOpenGraph_component_supp`, `Percolation.componentSize_cubicOpenGraph` | proved | Bridges Mathlib connected components to the repository's pre-existing `cubicOpenClusterFrom`. |
| §4.2, (4.14)–(4.15) | an animal with `n` vertices has `n-1 ≤ m ≤ dn` occupied and `1 ≤ b ≤ 2dn` boundary bonds | `Percolation.animalParameterPairs`, `Percolation.animalParameterPairs_card_le` | proved as range/counting layer | The geometric proof that a concrete cubic animal lies in the range is not yet encoded because the concrete animal type/table is not constructed. The finite parameter range has at most `2d²n²` pairs, improving the retained book prefactor `3d²n²`. |
| §4.2, (4.24)–(4.25) | compare the animal weight at `p` to its maximizing parameter `r=m/(m+b)` | `Percolation.animalOpenFraction`, `Percolation.exp_neg_mul_binaryRelativeEntropy`, `Percolation.weightedTerm_le_exp_neg_entropy` | proved modulo coefficient inequality | The exact coefficient estimate `aₙₘᵦ r^m(1-r)^b ≤ 1` is the explicit hypothesis `href`; it must later be discharged from a concrete cubic-animal enumeration. |
| §4.2, Theorem (4.20) | exceptional pairs `|m/p-b/q|>dxn` have total weight at most `3d²n² exp(-nx²p²q/3)` | `Percolation.binaryRelativeEntropy_ge_half_sq`, `Percolation.animalWeight_le_exp_of_deviation`, `Percolation.latticeAnimal_largeDeviation` | proved modulo (4.25), with weaker constant | For `n≥2` and all `x>0`, the formal theorem proves the same exceptional sum and prefactor with `exp(-nx²p²q²/18)`. The source proves a sharper small-`x` exponent `exp(-nx²p²q/3)` and separately dismisses `n=1` as straightforward. The concrete `aₙₘᵦ` bridge remains. |
| §4.3, (4.18) and (4.32) | `κ` is the animal series and its derivative is `Σ n⁻¹aₙₘᵦ(mp^{m-1}q^b-bp^mq^{b-1})` | `Percolation.AnimalSeriesIndex`, `Percolation.animalSeriesTerm`, `Percolation.animalSeriesTermDerivative`, `Percolation.animalSeriesTerm_hasDerivAt` | derivative formula proved | The termwise derivative is exact. Equality of `clusterDensitySeries` with `openClustersPerVertex` for the concrete cubic-animal counts is not yet proved. |
| §4.3, Theorem (4.31), (4.33)–(4.37) | `κ` is continuously differentiable on `[0,1]`; the differentiated series converges uniformly, with separate endpoint arguments | `Percolation.clusterDensitySeries`, `Percolation.clusterDensityDerivativeSeries`, `Percolation.clusterDensitySeries_contDiffOn_unitInterval` | proved modulo explicit analytic interface | Given a summable uniform bound for derivative terms on a neighbourhood of `[0,1]` and base-point summability, Mathlib's uniform-limit theorem gives `ContDiffOn ℝ 1` and the exact derivative series at every `p∈[0,1]`. Derivation of that majorant from the concrete 4.20 estimate and the endpoint calculations (4.36)–(4.37) remains; no axiom is introduced. |

## Major-Theorem Telemetry

The measured autoformalization windows are wall-clock/token deltas from the active goal tracker.
They cover theorem construction and local verification, but exclude the final repository-wide audit,
documentation, Git operations, and PR writing.

| Major theorem | Time | Tokens |
|---|---:|---:|
| Theorem 4.2 | 14m44s | 312,517 |
| Theorem 4.20 | 14m51s | 318,792 |
| Theorem 4.31 | 3m10s | 55,995 |
| **Total** | **32m45s** | **687,304** |

## Axiom Certificate

The headline declarations use only `propext`, `Classical.choice`, and `Quot.sound`. The three new
files contain zero `sorry` declarations and introduce no project axiom.
