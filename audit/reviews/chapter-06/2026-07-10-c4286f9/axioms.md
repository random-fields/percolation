# Axiom audit

Authoritative command:

```sh
lake env lean audit/reviews/chapter-06/2026-07-10-c4286f9/AxiomAudit.lean
```

Expected and permitted transitive set for every declaration:

```text
[propext, Classical.choice, Quot.sound]
```

Exit status: `0`.

All 41 printed declarations reported exactly the permitted set. No project axiom, `sorryAx`, or
additional logical assumption occurred.

Production, case, counterexample, and Comparator solution files are also scanned for `sorry`,
`admit`, new `axiom`, and unsafe declarations. `Challenge.lean` is the sole permitted review file
containing `sorry`, as required by Comparator's trusted-challenge workflow.
