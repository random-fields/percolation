# Topic 05 — Exponential Decay

Source: `grimmett-percolation-1999`, Chapter 5, pp. 87–116.

## Scope and completion claim

The chapter target is complete for both proof routes selected in the implementation plan:
Menshikov's radius-decay proof in §5.2, Aizenman–Barsky's ghost-field proof in §5.3, and the
Appendix I limits used by the latter. Every named theorem, proposition, and lemma in that scope,
and every listed major numbered consequence, has an assumption-free source-facing Lean
declaration. This does not mean that every displayed equation in Chapter 5 is promoted to a
separate public theorem; intermediate equations are often internal helper declarations.

## Foundational correspondence

| Source concept | Exact Lean declaration(s) | Status / fidelity note |
|---|---|---|
| Cubic graph distance and metric balls | `Percolation.cubicL1Dist`, `Percolation.cubicGraph_dist_eq_l1Dist`, `Percolation.cubicMetricBall`, `Percolation.cubicMetricSphere`, `Percolation.cubicMetricBallEdges` | proved; the finite ball edge set is the support of the radius event |
| `A_n(x)`, `g_p(n)`, cluster radius | `Percolation.radiusConnectionEvent`, `Percolation.radiusTail`, `Percolation.clusterRadius` | proved; first-hitting paths identify the finite-support event with ordinary connection to the sphere |
| Susceptibility and threshold | `Percolation.clusterSizeENNReal`, `Percolation.susceptibility`, `Percolation.susceptibilityThreshold` | proved in `ℝ≥0∞`; infinite clusters contribute `⊤`, unlike Chapter 4's reciprocal convention |
| Pivotal sausages and gaps | `Percolation.radiusPivotalDarts`, `Percolation.sausageGap`, `Percolation.sausageGapPrefixEvent` | proved as finite-trace observables with canonical pivotal order; pivotal darts use `SimpleGraph.Dart` directly |
| Ghost field | `Percolation.GhostConfiguration`, `Percolation.ghostMeasure`, `Percolation.ghostTheta`, `Percolation.ghostSusceptibility`, `Percolation.finiteSusceptibility` | proved as the bond/green product model |
| Periodic volume and animals | `Percolation.CubicTorus`, `Percolation.CubicBondAnimal`, `Percolation.CubicTorusBondAnimal`, `Percolation.cubicAnimalCount` | proved; torus results require `N≥2`, and coefficient stabilization uses `n<N` |

## Source-to-Lean correspondence with theorem telemetry

All times and token counts below are measured active-goal counter differences, not estimates.
Helpers built specifically for a theorem are included in that theorem's window; substantial shared
infrastructure is listed separately in the next table.

| Source result | Page | Natural-language statement | Exact Lean declaration | Key dependencies | Status / divergence | Time | Tokens |
|---|---:|---|---|---|---|---:|---:|
| Theorem 5.2 via §5.2 | 88–89 | `p<p_c` implies finite mean cluster size, using exponential radius decay | `Percolation.susceptibility_lt_top_of_lt_critical_via_radius` | 5.4, ball-volume and sphere-sum bounds | proved | 9m26s | 185,758 |
| Theorem 5.2 via §5.3 | 88, 102–108 | the same conclusion, independently from the ghost-field theorem | `Percolation.susceptibility_lt_top_of_lt_critical_via_ghost` | 5.48, `χ=χᶠ` when `θ=0` | proved | 3m35s | 71,534 |
| Theorem 5.2 and (5.3) | 88 | finite susceptibility below criticality and `p_T=p_c` | `Percolation.susceptibility_lt_top_of_lt_critical`, `Percolation.susceptibilityThreshold_eq_criticalProbability` | both source routes; positivity of `θ` above `p_c` | proved; wrapper/threshold window is shared | 7m38s | 320,747 |
| Theorem 5.4 | 88–89 | below `p_c`, `g_p(n)` decays exponentially | `Percolation.radiusTail_exponential_decay_of_lt_critical`, `Percolation.radiusTail_lt_exp_neg_of_lt_critical` | 5.22, 5.24, stretched-exponential summability | proved; primary `≤ exp(-cn)` form includes `n=0`, strict corollary assumes positive radius | 11m02s | 116,214 |
| (5.6)–(5.7) | 89 | cluster-size tail is at most `exp(-β n^(1/d))` | `Percolation.clusterSize_tail_le_exp_neg_rpow_of_lt_critical` | 5.4 and cubic ball-volume bound | proved, including `n=0` | 10m14s | 193,154 |
| Theorem 5.8 | 89–90, 100–101 | immediately above `p_c`, `θ(p)-θ(p_c)` grows at least linearly | `Percolation.theta_sub_theta_critical_ge_linear` | (5.36)–(5.39), right continuity, continuation argument | proved without assuming `θ(p_c)=0` | 17m14s | 438,675 |
| (5.10)–(5.11) | 90 | logarithmic differentiation of `g_p(n)` identifies the conditional pivotal mean and integrates it | `Percolation.radiusTail_logDeriv_eq_conditionalExpectedPivotalCount`, `Percolation.radiusTail_log_hasDerivAt` | Russo, pivotal-event identity, positivity of `g_p(n)` | proved; measured with the finite renewal/parameterized-master layer | 41m57s | 588,028 |
| Lemma 5.12 | 92–94 | conditional sausage gaps are stochastically dominated by independent cluster-radius copies | `Percolation.sausageGap_conditional_cdf_ge` | exploration cylinders, residual two-edge Menger, BK | proved for every feasible nonempty history and the first-sausage endpoint | 12m26s | 170,351 |
| Lemma 5.17 | 95–96 | `E(N(A_n) | A_n) ≥ n/(Σ_{i≤n}g_p(i)) - 1` | `Percolation.conditionalExpectedPivotalCount_ge` | 5.12, bounded finite Wald/renewal comparison | proved | 31m01s | 311,637 |
| (5.22) | 96 | integrated master comparison between `g_α(n)` and `g_β(n)` | `Percolation.radiusTail_master_inequality` | 5.10, 5.17, monotonicity in density | proved with no pivotal-bound parameter | 55s | 7,532 |
| Lemma 5.24, (5.27)–(5.35) | 97–100 | for `p<p_c`, `g_p(n)≤δ(p)/√n` | `Percolation.radiusTail_le_inv_sqrt_of_lt_critical` | 5.22 and the explicit density/radius recursion | proved in source order; no later susceptibility shortcut | 13m36s | 227,144 |
| (5.42)–(5.47) | 104–105 | ghost generating series, `γ↓0` limits, and `χ(p,γ)=(1-γ)∂_γθ(p,γ)` | `Percolation.ghostTheta_eq_series`, `Percolation.ghostTheta_tendsto_theta`, `Percolation.ghostSusceptibility_eq_series`, `Percolation.ghostSusceptibility_tendsto_finiteSusceptibility`, `Percolation.ghostSusceptibility_eq_deriv` | exact finite/infinite green-avoidance probabilities, termwise calculus | proved, including the `χᶠ(p)=⊤` limit | 24m56s | 328,107 |
| Theorem 5.48 | 105, 107–108 | if `χᶠ(p)=∞`, then either `θ(p)>0`, or every `p'≥p` obeys `θ(p')≥(p'-p)/(2p')` | `Percolation.finiteSusceptibility_eq_top_imp_theta_lower_bound` | 5.49, 5.53, rectangle integration | proved; handles `p'=p` and `p'=1` separately | 39m40s | 875,985 |
| Proposition 5.49 | 105–107 | infinite finite-cluster susceptibility forces `θ(p,γ)≥α√γ` for small positive `γ` | `Percolation.ghostTheta_ge_sqrt` | 5.46, 5.47, 5.51, 5.53 | proved for both `θ(p)=0` and `θ(p)>0` branches | 25m22s | 233,464 |
| Lemma 5.51, (5.52) | 106, 109–111 | `(1-p)∂_pθ ≤ 2d(1-γ)θ∂_γθ` | `Percolation.ghostTheta_p_deriv_le` | finite torus Russo, exact cluster conditioning, 5.64–5.66 | proved; window includes the shared conditioning layer used again by 5.53 | 35m38s | 385,040 |
| Lemma 5.53, (5.54) | 106, 111–114 | `θ ≤ γ∂_γθ + θ² + pθ∂_pθ` | `Percolation.ghostTheta_le_differential` | inhomogeneous BK, augmented two-edge graph, conditioning, Appendix I | proved | 44m26s | 615,991 |
| Appendix I, (5.64)–(5.66) | 109 | torus ghost probability and both partial derivatives converge to infinite volume | `Percolation.torusGhostTheta_tendsto`, `Percolation.torusGhostTheta_pDeriv_tendsto`, `Percolation.torusGhostTheta_gammaDeriv_tendsto` | concrete lattice/torus animals and coefficient stabilization | proved; p-derivative limit is identified with the actual derivative | 1h01m12s | 792,166 |

## Shared-infrastructure telemetry roll-up

This is the disjoint window ledger used for the total. Rows whose label contains a theorem are the
same windows shown above; roll-up rows are not counted again. A few windows necessarily combine a
theorem with shared infrastructure because no internal counter snapshot was taken; those rows say
so explicitly rather than reconstructing a split.

| Measured window | Scope | Time | Tokens |
|---|---|---:|---:|
| Metric radius and susceptibility infrastructure | L¹ graph metric, finite radius events, `g_p→θ`, ball volume, susceptibility expansion | 13m29s | 245,289 |
| Two-edge Menger and concrete-animal infrastructure | residual flow/cut theorem plus rooted cubic animals and exact cylinders | 46m17s | 1,046,878 |
| First-sausage infrastructure | first gap, target-set endpoint, initial BK bound | 55m30s | 646,591 |
| Ghost equations (5.42)–(5.47) | infinite product model, series and limits | 24m56s | 328,107 |
| Torus, inhomogeneous BK, and right-continuity infrastructure | periodic graph/model, mixed finite cube, `θ=inf g_n` | 29m48s | 528,203 |
| Torus susceptibility (5.63) | exact finite cluster-cardinality polynomial | 8m16s | 156,420 |
| Infinite cluster/animal bridge | exact concrete coefficient expansion used by Appendix I | 13m23s | 162,081 |
| Finite sausage-trace observability | canonical trace invariance and measurable prefix events | 10m53s | 140,625 |
| Finite renewal/Wald and parameterized master layer | bounded Wald identity, (5.10)–(5.11), parameterized (5.22) | 41m57s | 588,028 |
| Appendix I (5.64)–(5.66) | stabilization and all three limits | 1h01m12s | 792,166 |
| Joint torus edge/green cube | Fubini, translation invariance, mixed BK | 13m27s | 231,072 |
| One-green and BK decomposition (5.68)–(5.71) | exact `γ∂γθ`, `θ²`, exceptional remainder | 15m02s | 184,958 |
| Conditioning infrastructure plus Lemma 5.51 | cluster-block factorization and finite/infinite differential inequality | 35m38s | 385,040 |
| Lemma 5.53 | augmented-graph bridge decomposition through infinite-volume limit | 44m26s | 615,991 |
| Quality refactor for differential slice | separated generic finite-cube API and reverified both modules | 5m05s | 79,417 |
| Proposition 5.49 | square-root ghost lower bound | 25m22s | 233,464 |
| Theorem 5.48 | rectangle integration and endpoint passage | 39m40s | 875,985 |
| Theorem 5.2, ghost route | independent Aizenman–Barsky conclusion | 3m35s | 71,534 |
| Headline Theorem 5.2 and (5.3) | public wrapper and susceptibility threshold | 7m38s | 320,747 |
| Translation and radius-block infrastructure | invariance, first-hit BK block, finite-χ contraction | 14m52s | 341,775 |
| Consequence (5.7) | stretched-exponential cluster-size tail | 10m14s | 193,154 |
| Theorem 5.2, radius route | exponential radius decay implies finite susceptibility | 9m26s | 185,758 |
| Deleted-cluster exploration infrastructure | marked-graph conditioning and pivotal-prefix stability | 36m39s | 478,528 |
| Residual terminal/Menger infrastructure | two-path terminal geometry for later sausage gaps | 26m43s | 246,361 |
| Exact-budget deterministic inclusion | borderline radius budget for the residual BK event | 2m29s | 36,400 |
| Lemma 5.12 | all-index conditional domination | 12m26s | 170,351 |
| Lemma 5.17 | renewal transfer to pivotal expectation | 31m01s | 311,637 |
| Master inequality (5.22) | discharge the pivotal-bound parameter | 55s | 7,532 |
| Lemma 5.24 | Menshikov recursion | 13m36s | 227,144 |
| Theorem 5.4 | source-order exponential bootstrap | 11m02s | 116,214 |
| Theorem 5.8 | right-continuous continuation argument | 17m14s | 438,675 |
| **Chapter 5 measured total** | sum of the 31 disjoint windows above | **11h22m11s** | **10,386,125** |

## Axiom and build certificate

The repository-wide `lake build` completes all 8,532 jobs. A single audit file ran `#print axioms`
for every headline declaration in the correspondence table; each reported exactly `propext`,
`Classical.choice`, and `Quot.sound`. Production files contain no `sorry`, `admit`, or new `axiom`.
