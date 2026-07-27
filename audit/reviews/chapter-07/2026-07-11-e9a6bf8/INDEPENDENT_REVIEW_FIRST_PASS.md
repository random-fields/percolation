# Independent first-pass review — commit `e9a6bf8`

Verdict: the infrastructure is axiom-clean and most “proved slice” rows are accurate, but the half-space good-brick row is materially overstated. The current event is not a faithful encoding of Grimmett’s good brick and is too strong for Lemma 7.36.

## Blockers

### 1. `halfSpaceBrickGoodEvent` is not Grimmett’s good-brick event

Files:

- `Percolation/Critical/HalfSpaceBricks.lean:139`
- `Percolation/Critical/HalfSpaceBricks.lean:141`
- `Percolation/Critical/HalfSpaceBricks.lean:145`
- `Percolation/Critical/HalfSpaceBricks.lean:146`
- `audit/topics/topic-07-dynamic-static-renormalization.md:44`

The source on p. 164 requires:

- a seed square parallel to each side/top subfacet;
- an open path joining that seed square to the central square `b(0)`;
- no path edge lying in the underside.

The Lean event instead requires:

```lean
brickSeedPlaneEvent y (brickVerticalIndex hd) m ∩
connectionEventIn ... cubicOrigin y
```

This differs critically:

- Every side seed is horizontal because the normal is always `brickVerticalIndex`; side seeds should be parallel to their side facet, hence use the corresponding horizontal normal.
- It connects two fixed centers, `cubicOrigin` and `y`, rather than connecting the two seed-plane vertex sets.
- `halfSpaceBrickEdges` includes underside edges, so the required exclusion is absent.

The fixed-origin condition makes the planned Lemma 7.36 impossible in its intended arbitrary-accuracy form. For positive `L,H`, goodness forces a nontrivial open path from the origin. At any `p<1`, the origin is isolated with positive probability, so the event’s probability is uniformly bounded below one. Grimmett avoids this obstruction by allowing any vertex of the growing central square `b(0)` as the connection endpoint; `b(0)` itself need not be a seed.

The finite-support and measurability proofs are valid for the currently defined surrogate event, but not evidence that Grimmett’s event has been formalized. Topic row 44 should be downgraded or split until the definition is corrected.

### 2. The Lemma 7.24 adapter does not yet capture the source conclusion

Files:

- `Percolation/Critical/SiteExplorationDomination.lean:17`
- `Percolation/Critical/SiteExplorationDomination.lean:20`
- `Percolation/Critical/SiteExplorationDomination.lean:25`
- `Percolation/Critical/DynamicRenormalization.lean:178`

The source concludes `P(|A∞| = ∞) > 0` for the connected exploration grown from a fixed initial vertex. The current adapter proves positive probability of the global event

```lean
∃ x, (siteOpenCluster G η x).Infinite
```

under an arbitrary measure `μ`.

The missing work is more than the sequential domination criterion:

- define the limiting occupied set `A∞`;
- prove it is the field whose law is being dominated;
- prove the exploration remains connected/rooted;
- transfer global or rooted iid percolation to infinitude of that particular `A∞`.

Thus the file-level claim that the remaining content is “precisely” sequential domination is too strong. The topic row itself is more careful—it only claims the finite-history kernel—so row 20 can remain a target.

### 3. The “finite bad events” audit row exceeds the proved API

Files:

- `Percolation/Critical/StaticBlocks.lean:481`
- `Percolation/Critical/StaticBlocks.lean:488`
- `Percolation/Critical/StaticBlocks.lean:492`
- `audit/topics/topic-07-dynamic-static-renormalization.md:47`

`twoArmSeparationEvent` has a measurability proof. `largeCrossingClusterEvent` and `secondMacroscopicClusterEvent` currently have neither `DependsOn` nor measurability theorems; only the deterministic impossibility result for `m > 2n` is proved.

They are mathematically finite-cylinder events, but that fact has not yet been kernel-checked. Row 47 should say that their definitions and endpoint identity are proved, not that all listed bad events have completed finite-event infrastructure.

## Important suggestions

- `boxLargestCluster` uses a relative-coordinate key, but translation equivariance of the selected component is not proved. The note at `topic-07...md:45` should describe this as the intended tie-break until an explicit transport theorem establishes stationarity 7.60.
- `epsilonGoodBlockField` degenerates at `n=0`: every center equals the origin (`StaticBlocks.lean:394–398`). The support-separation theorem correctly assumes `1 ≤ n` at line 403. Any future `KDependent` theorem must retain that hypothesis.
- Add the source check `K(m,n)=∅` when `n<2m`; the geometry is encoded, but this mandatory adversarial test is not yet present.
- `StochasticallyDominates` is defined for arbitrary measures, although Grimmett’s relation concerns probability laws. This is harmless for present probability-measure uses, but future LSS interfaces should explicitly require probability measures.
- The frozen summary’s “source inventory: present” should not be read as complete: the live topic card does not yet give individual dispositions for all requested numbered results 7.3, 7.20–7.25, 7.33–7.34, 7.53, 7.56, 7.60, 7.62–7.67, and so on. It correctly labels itself intermediate.

## Checks that passed

- No production `sorry`, `admit`, or project `axiom` was found in this slice.
- Independent scans of Regions, Seeds, StaticBlocks, Crossings, and the pinned StochasticDomination file found only `propext`, `Classical.choice`, and `Quot.sound`.
- The explicit frozen axiom sample also reports only those standard axioms for the half-space support theorem and other representative declarations.
- Stochastic-domination orientation is correct: the higher-density iid law dominates the lower-density law.
- Region infinite-cluster measurability, connected-region root-zero equivalence, critical-threshold directions, and site closed-root handling are faithful.
- Seeded boundary geometry, existential seed centers, finite support, and measurability match 7.5–7.10.
- Static good-box conditions match Grimmett’s crossing, uniqueness, and density requirements.
- The guarded width-zero rectangle convention is transparent and avoids the unlimited duplicate-nil-walk junk value.

No headline Chapter 7 result is falsely marked proved; all remain targets. The primary correction needed at this checkpoint is to stop treating the current half-space brick event as a faithful proved slice.
