# percolation

A Lean 4 / Mathlib formalization workspace for **percolation theory** and the
**random-cluster model**, built for autoformalization in the `random-fields` organization.

Primary sources are Geoffrey Grimmett's *Percolation* (2nd ed., 1999) and
*The Random-Cluster Model* (2006). The repo is set up like `random-fields/optimal-transport`:
source corpus in `kg/`, planning and verification docs in `docs/`, Lean modules under
`Percolation/`, and an agent-facing contract in `AGENTS.md`.

**Mathlib v4.30.0.** Build: `lake exe cache get && lake build`.

## Scope

- **Core:** graph/lattice vocabulary, edge configurations, paths, clusters, events.
- **Bernoulli percolation:** product edge measures, increasing events, FKG, BK/Reimer,
  Russo's formula, critical probability, subcritical and supercritical phases.
- **Planar theory:** duality, crossings, square-lattice self-duality, `p_c = 1/2` for bond
  percolation on `Z^2`.
- **Random-cluster model:** finite-volume measures, boundary conditions, FKG/positive
  association, infinite-volume limits, Edwards-Sokal coupling, phase transition, planar duality.
- **Interfaces with RandomFields:** graph, Markov, stochastic-ordering, finite-volume Gibbs,
  and inequality infrastructure should be reusable with neighboring `random-fields` repos.

## Verification Trail

1. [`docs/PLAN.md`](docs/PLAN.md) — source-ordered formalization target plan.
2. [`docs/DESIGN.md`](docs/DESIGN.md) — object hierarchy and module boundaries.
3. [`docs/VALIDATION.md`](docs/VALIDATION.md) — acceptance theorems defining "done".
4. [`docs/VERIFICATION.md`](docs/VERIFICATION.md) — informal-to-formal map and source links.
5. [`audit/`](audit/) + [`formalization.yaml`](formalization.yaml) — comparator-facing
   faithfulness, validation, and axiom/sorry tracking.

Working with an agent? Start with [`AGENTS.md`](AGENTS.md).
