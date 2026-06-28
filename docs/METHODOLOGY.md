# METHODOLOGY — lean4-skills + comparator plan-loop

This repo adapts the `random-fields/optimal-transport` plan-loop to percolation.

## Target Selection

1. Start from the source corpus in `kg/textbooks/`.
2. Extract definitions/theorems into `kg/derived/` and `docs/PLAN.md`.
3. Cut the frontier against Mathlib and `random-fields` repos.
4. Prove targets in dependency order, keeping source ids from `formalization.yaml`.

## Design Review

Before deep proving, run two independent design reviews over `docs/DESIGN.md`:

- Are the Lean objects faithful to Grimmett's finite-graph and lattice definitions?
- Are finite-volume and infinite-volume objects separated cleanly?
- Are random-cluster boundary conditions explicit?
- Are theorem statements no stronger than the source?

Fold consensus changes into `docs/DESIGN.md` and record them in `docs/HISTORY.md`.

## Proof Loop

```
target card
  -> Mathlib/local search
  -> Lean scaffold
  -> lean4-skills proof work
  -> lake build
  -> axiom/sorry check
  -> comparator update
  -> history entry
```

Use Lean LSP tools for goal inspection and lemma search when available. If the host lacks LSP,
use `lake env lean` file gates and `lake build` checkpoints.

## Comparator Layer

Comparator work is the source-faithfulness discipline:

- `formalization.yaml` gives source ids.
- `docs/VERIFICATION.md` maps informal objects and theorems to Lean names.
- `audit/topics/*.md` record source excerpts in paraphrase, formal statements, divergences,
  validation status, and review notes.
- `AXIOM_AUDIT.md` records any non-standard assumptions.

For every result, ask: "Could a reader locate the source statement and understand why the Lean
statement is the same theorem, or a clearly documented generalization/specialization?"

## Axiom Discipline

Do not use `sorry` as a research convenience on `main`. If a true classical theorem is missing,
make the axiom minimal, named, cited, reviewed, and discharge-owned. Prefer conditional theorems
over axioms when the missing fact is a large analytic or geometric theorem.
