# Transitive axiom audit

Command:

```sh
lake env lean audit/reviews/chapter-07/2026-07-12-711c8eb/AxiomAudit.lean
```

Result: every reviewed declaration reports exactly a subset of:

- `propext`
- `Classical.choice`
- `Quot.sound`

No project axiom, `sorryAx`, or additional classical principle appears.
