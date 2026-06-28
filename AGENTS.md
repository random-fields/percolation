# AGENTS.md — operating instructions for coding agents

You are formalizing **percolation theory and the random-cluster model** in Lean 4 + Mathlib,
using `lean4-skills` and a comparator-style source-to-formal audit. This file is the contract.

## Startup

Run once before serious proving:

1. `lake exe cache get && lake build`
2. `rg --version`
3. Confirm Lean LSP MCP is available through `.mcp.json` when the host supports it.
4. Confirm `lean4-skills` commands or wrappers are available. Prefer `/lean4:prove`,
   `/lean4:autoprove`, `/lean4:checkpoint`, `/lean4:review`, and the `lean4-skills-*`
   helper wrappers when they exist.

If Lean MCP is down, say so and use `lake env lean <file>` plus `lake build`; do not pretend
interactive goal inspection was used.

## The Loop

1. Pick one target from `docs/PLAN.md` or `docs/VALIDATION.md`.
2. Search Mathlib and local repos first. Do not re-prove existing graph, measure, probability,
   order, or lattice facts.
3. Scaffold the smallest useful file under `Percolation/<Layer>/`.
4. Prove incrementally using Lean LSP/lean4-skills. Keep statements general where it is free,
   but concrete for classical lattice theorems whose source is concrete.
5. Verify:
   - `lake build` is green.
   - No accidental `sorry` on `main` unless the target branch is explicitly marked as a
     design branch.
   - `#print axioms <new theorem>` uses only standard axioms, or exactly the named true
     project axioms recorded in `AXIOM_AUDIT.md`.
6. Update `docs/HISTORY.md`, `docs/VERIFICATION.md`, and the relevant comparator topic card
   in `audit/topics/`.

## Comparator Discipline

Every serious theorem needs a source-to-formal comparator trail:

- source id from `formalization.yaml`;
- book location, theorem/definition number, or stable section;
- informal statement;
- exact Lean declaration name;
- status: target, proved, proved modulo a named axiom, or rejected/anti-target;
- notes on divergences such as generalized hypotheses, finite-volume encodings, or changed
  normalization.

Do not mark a theorem "faithful" until this trail exists. If an axiom is introduced, run an
independent read-only review whose job is to refute it, then record the result in
`audit/vetting/`.

## Axiom and Sorry Rules

- `main` should be build-green and sorry-free once the initial scaffold is replaced by real
  targets. During design, skeletal declarations may be absent rather than `sorry`-filled.
- If a classical theorem is absent from Mathlib and genuinely blocks progress, isolate it as
  one named, cited, true `axiom` with a discharge plan. Record it in `AXIOM_AUDIT.md`.
- Never introduce a convenient stronger statement just to unblock a proof.
- Never fabricate Mathlib names, source references, or comparator statuses.

## Module Layout

`Percolation/Core/` — graphs, configurations, paths, clusters, events.

`Percolation/Bernoulli/` — Bernoulli bond/site percolation, product measures, FKG/BK/Russo.

`Percolation/Critical/` — critical probabilities, subcritical/supercritical phase, uniqueness.

`Percolation/Planar/` — planar duality, crossing estimates, square-lattice exact threshold.

`Percolation/RandomCluster/` — random-cluster measures, boundary conditions, stochastic order,
Edwards-Sokal coupling, infinite-volume limits.

Use `docs/DESIGN.md` as the authority when in doubt.
