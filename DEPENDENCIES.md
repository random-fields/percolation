# Dependency Ledger

## Toolchain

- Lean: `leanprover/lean4:v4.30.0`
- Mathlib: `v4.30.0`
- Build command: `lake exe cache get && lake build`

## Methodology Inputs

- `random-fields/optimal-transport`: repo layout, `AGENTS.md` contract, plan-loop docs.
- `RandomFields`: `formalization.yaml`, audit/comparator convention style.
- `lean4-skills`: Lean proving workflow and helper wrappers.
- `math-commons/formalization-assurance`: comparator, verification, validation, and axiom-vetting
  conventions.

## Source Inputs

- Geoffrey Grimmett, *Percolation*, 2nd ed., Springer, 1999.
- Geoffrey Grimmett, *The Random-Cluster Model*, Springer, 2006.
