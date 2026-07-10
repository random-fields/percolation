# Preliminary axiom audit

Command:

```sh
lake env lean audit/reviews/chapter-06/2026-07-10-worktree/AxiomAudit.lean
```

Exit status: 0.

Each reviewed declaration reports exactly:

```text
[propext, Classical.choice, Quot.sound]
```

Declarations:

- `Percolation.boxRadiusTail_exponential_decay_of_susceptibility_lt_top`
- `Percolation.mem_boxRadiusConnectionEvent_iff_exists_connection`
- `Percolation.cubicL1Dist_le_card_mul_lInfDist`

