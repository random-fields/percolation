# Response to the independent first-pass review

The unedited report is preserved in `INDEPENDENT_REVIEW_FIRST_PASS.md`.  The following changes
were made after that review; they are not retroactively attributed to commit `e9a6bf8`.

## Blocker 1 — good-brick geometry

Addressed in the subsequent working tree:

- `brickFacetSeedNormal` gives top seeds the vertical normal and side seeds their side-face
  normal;
- `brickFacetSeedCenters` admits only centers whose entire seed plane lies in the chosen
  subfacet;
- `brickSeedConnectionEvent` quantifies over endpoints in the central and target seed vertex
  sets rather than fixing their centers;
- `halfSpaceBrickUsableEdges` removes every bond lying wholly in the underside;
- finite support, measurability, increasingness, and continuity were reproved for the corrected
  event.

The live topic card now describes these exact geometric conditions.

## Blocker 2 — Lemma 7.24 adapter

The module and declaration comments now state explicitly that the domination consequence is
only a post-domination adapter.  The limiting explored set, its law, rooted connectedness, and
the sequential criterion remain open, and Lemma 7.24 remains a `target`.

## Blocker 3 — static bad-event audit wording

The live topic card now claims only definitions and endpoint checks for the large-crossing and
second-cluster events.  Their finite-support/measurability theorems remain explicit targets.

## Important suggestions

- The topic card no longer calls the largest-component selector translation equivariant; that
  transport theorem remains open.
- The proved `epsilonGoodBlockLaw_kDependent` retains the necessary hypothesis `1 ≤ n`.
- LSS and the finite-terminal `K(m,n)` adversarial test remain open follow-up items.

