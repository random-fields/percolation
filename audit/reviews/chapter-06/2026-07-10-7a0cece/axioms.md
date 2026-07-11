# Axiom audit

Authoritative command:

```sh
lake env lean audit/reviews/chapter-06/2026-07-10-7a0cece/AxiomAudit.lean
```

Expected and permitted transitive set for every declaration:

```text
[propext, Classical.choice, Quot.sound]
```

Exit status: `0`.

All 34 printed declarations reported a subset of the permitted set. Thirty-three reported exactly
`[propext, Classical.choice, Quot.sound]`; the purely finite arithmetic theorem
`connectivitySkeletonCount_eq_doubleFactorial` reported the smaller set
`[propext, Quot.sound]`. No additional axiom occurred.

Production, case, counterexample, and Comparator solution files are also scanned for `sorry`,
`admit`, new `axiom`, and unsafe declarations. `Challenge.lean` is the sole permitted review file
containing `sorry`, as required by Comparator's trusted-challenge workflow.
