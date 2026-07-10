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
- `Percolation.twoPointConnectivity_axis_logRate_tendsto`
- `Percolation.twoPointConnectivity_axis_twoSided_decay`
- `Percolation.twoPointConnectivity_twoSided_decay`
- `Percolation.twoPointConnectivity_le_one_sub_susceptibility_inv_pow`
- `Percolation.correlationLength_le_susceptibility`
- `Percolation.susceptibility_tendsto_top_at_critical`
- `Percolation.exists_terminal_deletion_preserves_connected`
- `Percolation.threePointConnectivity_le_tsum_prod`
