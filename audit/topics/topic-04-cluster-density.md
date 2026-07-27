# Topic 04 — Open Clusters per Vertex

Source: `grimmett-percolation-1999`, Chapter 4, pp. 77–86.

## Comparator map

| Source item | Informal statement | Exact Lean declaration | Status | Divergence / remaining input |
|---|---|---|---|---|
| §4.1, (4.1) | `κ(p) = E_p(|C|⁻¹)`, with an infinite cluster contributing zero | `Percolation.openClustersPerVertex`, `Percolation.openClustersPerVertex_eq_integral_inv_ncard` | proved | Lean uses the reciprocal of `ncard`; the infinite-set convention contributes zero, matching the book. |
| §4.1, (4.4)–(4.8) | summing reciprocal component sizes over a finite graph counts components | `Percolation.sum_componentWeight_eq_componentCount`, `Percolation.sum_componentWeight_fiber_eq_one` | proved | Generalized from cubic boxes to arbitrary finite simple graphs. |
| §4.1, (4.10)–(4.12) | finite-box component count is squeezed by reciprocal cluster weights plus a boundary error | `Percolation.componentWeightAverage_le_normalizedComponentCount`, `Percolation.componentCount_le_weightSum_add_boundary`, `Percolation.normalizedComponentCount_tendsto_of_sandwich` | proved | The abstract squeeze is complete; the multiparameter cubic-box ergodic instantiation remains explicit. |
| §4.1, Theorem (4.2), pp. 77–79 | `K_n/|B(n)| → κ(p)` almost surely and in `L¹` | `Percolation.normalizedCubicOpenClusterCountIn_tendsto_ae_of_ergodicAverage` | proved modulo named hypotheses | The almost-sure squeeze is proved; the box pointwise-ergodic input, its concrete boundary instantiation, and the source's `L¹` conclusion remain. Chapter 4 as a whole is therefore not claimed complete. |
| §4.2, (4.14)–(4.18), pp. 80–81 | concrete rooted animals have `n−1≤m≤dn`, `1≤b≤2dn`, and give the exact finite-cluster expansion | `Percolation.CubicBondAnimal`, `Percolation.CubicBondAnimal.edges_card_lower`, `Percolation.CubicBondAnimal.edges_card_upper`, `Percolation.CubicBondAnimal.boundary_card_le`, `Percolation.finiteClusterSizeProbability_eq_sum_cubicAnimalCount` | proved | The coefficient table is the actual finite type of rooted cubic bond animals, not an abstract parameter. |
| §4.2, (4.24)–(4.26), pp. 81–82 | animal coefficients obey the maximizing-parameter estimate used in the large-deviation proof | `Percolation.cubicAnimalCount`, `Percolation.cubicAnimalCount_mul_weight_le_one`, `Percolation.cubicAnimalCount_mul_maximizingWeight_le_one` | proved | Discharged by pairwise-disjoint exact cluster cylinders. |
| §4.2, Theorem (4.20), pp. 81–83 | for all `n≥1` and sufficiently small `x>0`, the exceptional animal mass is at most `3d²n² exp(-nx²p²(1-p)/3)` | `Percolation.cubicAnimal_largeDeviation_sharp_one_le` | proved | Lean supplies the explicit uniform witness `x≤1/100` for the book's existential “sufficiently small” range. The prefactor, exponent, `n≥1`, and `0<p<1` range are exact. |
| §4.3, (4.18), (4.32), pp. 83–85 | `κ` is the concrete animal series and its derivative is the termwise differentiated series | `Percolation.concreteClusterDensitySeries`, `Percolation.concreteClusterDensityDerivativeSeries`, `Percolation.concreteClusterDensitySeries_eq_openClustersPerVertex`, `Percolation.concreteClusterDensityLevel_hasDerivAt` | proved | Equality with the production `openClustersPerVertex` is stated for physical densities `p : I`; the polynomial series itself is extended to real `p` for calculus. |
| §4.3, Theorem (4.31), (4.33)–(4.37), pp. 84–86 | `κ` is continuously differentiable throughout `[0,1]` | `Percolation.concreteClusterDensitySeries_contDiffOn_unitInterval` | proved | Unconditional for `d≥2`. The interior uses the sharp animal deviation estimate; `p=0` uses a two-sided geometric animal majorant; `p=1` uses periodic component counts and a three-edge square detour. |

## Measured autoformalization telemetry

Times and tokens are exact active-goal counter differences. They include theorem-specific helpers
and local verification, and exclude final documentation, Git operations, and PR writing.

| Result / measured window | Time | Tokens |
|---|---:|---:|
| Theorem 4.2 conditional core | 14m44s | 312,517 |
| Theorem 4.20 initial coefficient-table core | 14m51s | 318,792 |
| Theorem 4.20 sharp concrete completion | 13m51s | 228,679 |
| Theorem 4.20 `n=1` source-range completion | 3m33s | 31,921 |
| **Theorem 4.20 roll-up** | **32m15s** | **579,392** |
| Theorem 4.31 initial generic calculus interface | 3m10s | 55,995 |
| Theorem 4.31 concrete interior completion | 12m22s | 202,452 |
| Theorem 4.31 endpoint completion | 1h01m40s | 805,351 |
| **Theorem 4.31 roll-up** | **1h17m12s** | **1,063,798** |
| **Chapter 4 recorded total** | **2h04m11s** | **1,955,707** |

The roll-up rows are sums and are not additional windows.

## Axiom certificate

`cubicAnimal_largeDeviation_sharp_one_le` and
`concreteClusterDensitySeries_contDiffOn_unitInterval` each audit to exactly `propext`,
`Classical.choice`, and `Quot.sound`. No project axiom, `sorry`, or unresolved theorem parameter is
used. Theorem 4.2 retains ordinary theorem hypotheses, not axioms, and is still marked conditional.
