# Independent first-pass review — commit `d72bdde`

Overall result: **FAIL for the claim that exact Theorem 7.65 is fully formalized.**  
The fixed-target LSS theorem, equation 7.64, regularity lift, cubic specialization, good-block application, build, and axiom audit all pass. The failure is statement fidelity: the source’s single monotone limiting function \(\pi(\delta)\) is not constructed.

## Blocking finding

### The public theorem is an equivalent-style threshold principle, not the exact source statement

Source, p. 179:

- for fixed \(d,k\), there exists one function \(\pi:[0,1]\to[0,1]\);
- \(\pi\) is nondecreasing;
- \(\pi(\delta)\to1\) as \(\delta\to1\);
- every \(k\)-dependent field with marginals at least \(\delta\) dominates iid density \(\pi(\delta)\).

The committed declarations instead prove:

```lean
∀ q < 1, ∃ δ < 1, every qualifying field with marginals ≥ δ dominates iid(q)
```

See:

- `Percolation/Bernoulli/LSSCountable.lean:306–327`
- `Percolation/Critical/LSSCubic.lean:127–140`

No declaration defines a domination function of the marginal parameter, proves it monotone, proves its limit at one, or handles the source endpoint \(\delta=1\).

The threshold family is a valid and useful qualitative consequence, and it contains the central mathematics. It can likely be used to construct the source function, but that construction and equivalence are not currently formalized.

Therefore these claims are overstated:

- `audit/topics/topic-07-dynamic-static-renormalization.md:25`
- `audit/topics/topic-07-dynamic-static-renormalization.md:53`
- the assertion that the “exact source quantifier order” is proved;
- `docs/VALIDATION.md`, which marks Theorem 7.65 done.

The actual source order begins with an existential function and then quantifies over \(\delta\) and laws. It is not literally `∀q<1, ∃δ<1`.

## Results that pass

### Equation 7.64: PASS

`sequentialLowerBound_stochasticallyDominates` at `SequentialDominationRegularity.lean:252–262` faithfully captures the sequential criterion through finite prefix laws.

- The index convention is correct: coordinate \(i\) is conditioned on the first \(i\) coordinates.
- Domination direction is correct:
  `StochasticallyDominates μ iid(q)` means expectations under iid are bounded by expectations under `μ`.
- The ratio-free hypothesis correctly handles null histories. On positive histories it is exactly the displayed conditional inequality; on null histories both relevant masses vanish.
- The finite theorem and countable regularity lift reach all bounded increasing measurable observables, not merely cylinder events.

Minor interface limitation: the countable theorem requires an explicit `e : ℕ ≃ V`, so it applies to denumerable spaces. Finite spaces are handled separately, but there is no single theorem covering every `Countable V` exactly as the book phrases it.

### Compactness and regularity argument: PASS

`SequentialDominationRegularity.lean:83–250` is sound.

- Boolean products are compact.
- A point of an increasing set admits a positive-cylinder neighborhood inside any open superset.
- Compactness gives a finite union of such cylinders.
- Inner regularity is applied to the allegedly larger measure and outer regularity to the smaller measure in the correct direction.
- The finite-cylinder comparison then gives the required contradiction.
- Probability-measure hypotheses justify conversion between real and `ENNReal` measures.

I found no hidden reversal or missing measurability condition.

### LSS dilution and quantifiers for fixed target density: PASS

`lss_stochasticallyDominates` at `LSSCountable.lean:258–278` correctly proves the fixed-\(q\) result.

- The marginal threshold is chosen before the law.
- It is uniform over all qualifying laws.
- The threshold is strictly below one.
- The neighborhood bound may depend on the fixed graph/range data, not on the law.
- Choosing the two auxiliary densities equal is a valid specialization of 7.114–7.115.
- The larger cubic neighborhood bound only weakens the threshold and is safe.

### Cubic and good-block specializations: PASS

- `LSSCubic.lean` correctly hides the enumeration only for positive dimension.
- `LSSGoodBlocks.lean` uses the proved `3d`-dependence and stationarity to reduce the marginal hypothesis to the origin.
- The `n≥1` hypothesis correctly prevents the degenerate zero-scale block field.
- The domination direction remains correct.

## Endpoint and adversarial findings

- The restriction `q < 1` is necessary for a theorem with a threshold `δ < 1`. If it were removed, iid density `r<1` would be a counterexample: it is \(k\)-dependent with marginal \(r\), but cannot dominate iid density one even on a one-coordinate event.
- `q=0` is safe, though the explicit threshold is much stronger than necessary.
- The exact source theorem still needs the \(\delta=1\) endpoint and a function value there.
- No counterexample was found to any currently compiled Lean theorem.

Recommended tests still missing:

- a documented `q=1` anti-target;
- monotonicity and \(\delta\to1\) tests for the future source-facing function;
- the \(\delta=1\) endpoint;
- a simple one-coordinate LSS consequence, in addition to the existing general iid direction oracle;
- a unified finite-countable 7.64 adapter or an explicit comparator divergence note.

## Verification

- All four reviewed modules compile individually.
- `Chapter7Infrastructure.lean` compiles.
- No `sorry`, `admit`, or new project axiom occurs in the reviewed files.
- Independent axiom scans of `LSSCountable`, `LSSCubic`, and `LSSGoodBlocks` report only:
  - `propext`
  - `Classical.choice`
  - `Quot.sound`
- The regularity theorem is a transitive dependency of the scanned LSS declarations, so its use introduces no additional axiom.

In short: **the hard analytic and probabilistic core passes, but the exact function-valued statement of Theorem 7.65 remains to be added before the headline may faithfully be marked proved.**
