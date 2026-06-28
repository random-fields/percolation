# HANDOFF

## Current State

The repo is scaffolded but not yet doing serious mathematics. The Lean files compile-light objects
to anchor imports and namespaces; they are intended to be replaced by Mathlib-native graph and
measure encodings after design review.

## Next Best Step

Run the first sprint from `docs/PLAN.md`:

1. Search Mathlib graph APIs.
2. Decide the edge carrier.
3. Replace `BaseGraph`/`BondConfiguration` with production finite graph configuration objects.
4. Define increasing events and prove closure lemmas.
5. Define finite Bernoulli product measure.

## Commands

```bash
lake exe cache get
lake build
rg -n "sorry|axiom" Percolation docs audit
```
