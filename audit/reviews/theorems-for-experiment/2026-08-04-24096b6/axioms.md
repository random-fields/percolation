# Axiom audit

The three declarations are intentionally statement-only targets. Direct `#print axioms` checks
in `AxiomAudit.lean` reported the following exact transitive axiom set for each declaration:

```text
[propext, sorryAx, Classical.choice, Quot.sound]
```

The command exited successfully on 2026-08-04.

Therefore the logical-trust gate is intentionally **open**. This review does not describe the
declarations as proved, assumption-free, or kernel-certified results.
