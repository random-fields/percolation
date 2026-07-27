# Pull-request consolidation for Theorem 11.11

Date: 2026-07-27

Integration branch: `codex/theorem-11-11-integration`

This branch consolidates every pull request which was open in
`random-fields/percolation` when the work began, plus PR #14, which opened during integration.
The table records the immutable head commit reported by GitHub and the disposition used by the
integration.  A pull request is counted as integrated only when its head commit is an ancestor of
the integration branch; copying selected files without preserving that ancestry is not sufficient
for this ledger.

| PR | Head commit | Disposition |
|---:|---|---|
| #1 | `d65765b` | Already in the Chapter 12 ancestry. |
| #2 | `96f1bba` | Merged as the source-audit scorecard stack. |
| #3 | `ff1211f` | Reconciled by a two-parent merge; the canonical later APIs win conflicts, while compatible Cubic walk-openness lemmas and its source PDFs are retained. |
| #4 | `9281da9` | Already in the Chapter 12 ancestry. |
| #6 | `d7db304` | Merged as the random-cluster FKG stack. |
| #7 | `6eec5b1` | Already in the Chapter 12 ancestry. |
| #8 | `03876d0` | Already in the Chapter 12 ancestry. |
| #9 | `e4e8052` | Already in the Chapter 12 ancestry. |
| #10 | `f990513` | Merged as the latest Chapter 7 prerequisite stack. |
| #11 | `9481b37` | Already in the Chapter 12 ancestry. |
| #12 | `35b7d53` | Already in the Chapter 12 ancestry. |
| #13 | `fa86568` | Initial integration base: the latest Chapter 12 stack. |
| #14 | `7180033` | Merged as the repository guide, then annotated for the consolidated branch. |

At integration commit `c433f02`, `git merge-base --is-ancestor <head> HEAD` returned success for
all thirteen heads above.  A fresh `gh pr list` query at that revision reported the same thirteen
open heads.  This check must be rerun after the final consolidation commit in case a pull-request
head moves or another pull request opens.

## Conflict policy

The chronological Chapter 4--12 chain is treated as the canonical public API because later
chapters already consume it.  Independent stacks are merged into that chain and conflicts are
resolved declaration by declaration:

- preserve the canonical `IsDecreasingEvent`, symmetric pivotality, `thetaFrom d p x`, and the
  open-witness definition of disjoint occurrence;
- retain compatible facts rather than parallel definitions; from PR #3 this includes
  `cubicOpenClusterFrom_subset_of_walkIsOpen`,
  `hasInfiniteOpenClusterFrom_of_walkIsOpen`, and
  `hasInfiniteOpenClusterFrom_iff_of_walkIsOpen`;
- keep source artifacts cited by an accepted audit card, with hashes and provenance recorded in
  `kg/source_catalog.json`;
- do not port large noncanonical alternatives merely to maximize line count.  The PR #3
  martingale-FKG, forcing-Reimer/BK, and multiparameter-Russo families remain recoverable from its
  preserved parent commit and may be ported later behind the canonical APIs if a concrete target
  needs them.

## Verification gates

The integration is not declared clean merely from ancestry.  Before consolidation is complete:

1. incorporate the compatible post-PR Chapter 7 work from
   `agent/grimmett-chapter-11-prereqs` as a separate reviewed commit;
2. run focused builds for every conflict area, including `Percolation.Core.Cubic`,
   `Percolation.RandomCluster.MonotonicMeasures.Influence`, and
   `Percolation.Planar.SquareThresholdExact`;
3. run full `lake build` on the resulting integration revision;
4. run `git diff --check`, the Chapter 11 application tests, and the exact transitive axiom
   audit;
5. record the final commit and commands in `docs/HISTORY.md` and `docs/VERIFICATION.md`.

Sorries are permitted while reconciling design files under the user's instruction, but build
failures, unresolved merge markers, fabricated compatibility wrappers, and unrecorded project
axioms are not.
