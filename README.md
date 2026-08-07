# percolation

A Lean 4 / Mathlib formalization of **percolation theory** and the **random-cluster model**,
maintained as a clean bed for experiments with the
[pictorial proof protocol](docs/PICTORIAL_PROOF_PROTOCOL.md).

**Mathlib v4.30.0.** Build: `lake exe cache get && lake build`.

## Invariants

This repository is deliberately kept in a state that makes experiments measurable:

- **No project axioms.** `#print axioms` on any declaration returns at most `propext`,
  `Classical.choice`, `Quot.sound`.
- **No `sorry` or `admit`.**
- **No review, comparator, or orchestration harness.** The pictorial protocol is the only
  proof-methodology document, so an experiment measures it and not the surrounding scaffolding.

Anything added should preserve all three, or say explicitly why it does not.

## Scope

- **Core:** graph/lattice vocabulary, edge configurations, paths, clusters, events.
- **Bernoulli percolation:** product edge measures, increasing events, FKG, BK/Reimer, Russo's
  formula, critical probability, subcritical and supercritical phases.
- **Planar theory:** duality, crossings, square-lattice self-duality, and `p_c = 1/2` for bond
  percolation on `ℤ²` (Grimmett, Theorem 11.11) — proved via strict dual crossings, using no RSW
  input and no discrete Jordan curve theorem.
- **Random-cluster model:** finite-volume measures, boundary conditions, FKG, infinite-volume
  limits, Edwards–Sokal coupling, phase transition, planar duality.

## Sources

Primary sources are in [`kg/textbooks/`](kg/textbooks/) — Grimmett's *Percolation* (2nd ed., 1999)
and *The Random-Cluster Model* (2006), Duminil-Copin's *Graphical Representations of Lattice Spin
Models* (2016), and Bollobás–Riordan. Figures live in these PDFs; the protocol requires citing the
printed and PDF page for any figure you rely on.

## Working on a proof with a figure

1. Read [`docs/PICTORIAL_PROOF_PROTOCOL.md`](docs/PICTORIAL_PROOF_PROTOCOL.md).
2. If the proof conditions on a lowest, leftmost, first, or outermost object, also read
   [`docs/STOPPING_SETS.md`](docs/STOPPING_SETS.md).
3. Produce the three artifacts under `docs/<target>/` that the protocol requires.
