# Follow-up review — uncommitted LSS function correction

Overall result: **PASS for literal Grimmett Theorem 7.65 on \(\mathbb Z^d\), \(d\ge1\).**

The original blocker is resolved. The new declaration now chooses one function before quantifying over the input marginal and probability law.

## Source quantifier order: PASS

`Percolation/Bernoulli/LSSDominationFunction.lean:242–260` proves:

```lean
∃ pi : I → I,
  Monotone pi ∧
  Tendsto pi (𝓝 1) (𝓝 1) ∧
  ∀ delta mu, IsProbabilityMeasure mu →
    KDependent G k mu →
    marginals(mu) ≥ delta →
    StochasticallyDominates mu iid(pi delta)
```

Thus:

- `pi` is selected before `delta` and `mu`;
- it is uniform over every qualifying law;
- it is nondecreasing;
- it tends to one;
- the conclusion uses Grimmett’s all-observable expectation definition.

The cubic adapter at `LSSCubic.lean:142–157` fixes \(d,k\), computes the neighborhood bound from them, hides the enumeration, and then returns the single function. This matches the actual source scope of Theorem 7.65.

Renaming the former fixed-target theorem to `exists_lssDominationThreshold` correctly distinguishes the useful equivalent-style reformulation from the literal source theorem.

## Explicit function and inverse calculation: PASS

The function at `LSSDominationFunction.lean:20–21` is a valid inverse of the previously proved threshold:

\[
\pi_B(\delta)=
\max\!\left(0,\,
1-2\,[2(1-\delta)]^{1/(B+1)}\right).
\]

The calculation at lines 108–153 correctly establishes that whenever the output is positive,

\[
\texttt{lssMarginalThreshold}\bigl(B,\pi_B(\delta)\bigr)\le\delta.
\]

The two facts used are correct:

- for \(0\le q\le1\), the minimum defining the LSS slack is
  \((1-a)^{B+1}\), since \(1-a\le a\);
- raising the real root to the positive integer \(B+1\) recovers \(2(1-\delta)\).

I found no exponent, factor-of-two, or inequality-direction error.

## Monotonicity and limit: PASS

- `monotone_lssDominationDensityUnit`, lines 91–106, proves the required nondecreasing property.
- `lssDominationDensityUnit_tendsto_one`, lines 76–89, proves convergence to one.
- The filter is the neighborhood filter in the subtype `[0,1]`, so at the endpoint this is precisely the source’s one-sided limit \(\delta\uparrow1\).

The continuity proof is stronger than necessary and is used correctly.

## Endpoints: PASS

### \(\delta=0\)

The explicit formula evaluates to zero: its untruncated expression is negative, so the maximum is zero. The general domination theorem handles this through the zero-output branch at lines 223–227, using the correctly proved fact that every probability law dominates the all-closed iid configuration.

A named simp theorem `lssDominationDensityUnit B 0 = 0` would improve the review surface, but its absence is not a semantic gap.

### \(\delta=1\)

Lines 215–222 handle this endpoint separately.

- The output function equals one.
- Unit one-site marginals imply every enumerated coordinate is open almost surely.
- Countability then implies the entire configuration is all-open almost surely.
- Hence the law dominates iid density one.

This correctly avoids the false assertion that some threshold strictly below one could force domination of iid density one.

## Cubic and good-block adapters: PASS

- `exists_cubic_lssDominationDensity` has the literal source-facing form.
- `epsilonGoodBlockLaw_lssDominationDensity_stochasticallyDominates` correctly combines the explicit function with actual `3d`-dependence.
- Stationarity reduces all marginal hypotheses to the origin.
- `n≥1` remains present, excluding the degenerate zero-scale field.
- Domination direction remains correct.

## Denumerable versus countable scope

This is a **documented minor scope caveat, not a blocker for Theorem 7.65**.

The abstract theorem assumes both `[Countable V]` and an explicit `e : ℕ ≃ V`; it therefore covers denumerable spaces, not arbitrary finite countable spaces in one declaration. The finite sequential theorem covers finite spaces separately.

Grimmett’s Theorem 7.65 concerns \(\mathbb Z^d\) with \(d\ge1\), which is denumerable, and the cubic adapter supplies the equivalence. Thus the source theorem’s scope is fully covered. Generic documentation should avoid claiming one unified theorem for every finite-or-infinite countable type unless such an adapter is added.

## Verification and axioms

- `LSSDominationFunction.lean`: compiles.
- `LSSCubic.lean`: compiles.
- `LSSGoodBlocks.lean`: compiles.
- `Chapter7Infrastructure.lean`: compiles.
- No `sorry`, `admit`, or project axiom occurs in the reviewed changes.
- Independent scans of the new function module and cubic adapter report only:
  - `propext`
  - `Classical.choice`
  - `Quot.sound`
- The good-block theorem is a direct specialization of these audited declarations and previously audited dependence/stationarity results.

## Nonblocking test suggestions

Add explicit compiling checks for:

- `lssDominationDensityUnit B 0 = 0`;
- the all-open marginal endpoint theorem;
- impossibility of replacing `q<1` by `q=1` in the old strict-threshold formulation.

These would improve the adversarial review record, but no counterexample or hidden gap remains in the corrected theorem.

**Final assessment: PASS. The function-valued correction discharges the original independent-review blocker and faithfully formalizes Theorem 7.65.**

---

This report is preserved exactly as returned by the independent reviewer. The producer subsequently
implemented the nonblocking named zero-endpoint theorem and compiling endpoint cases; those later
test additions do not alter the report above.
