# HISTORY — percolation

Dated milestones and anti-library notes.

1. **Repo bootstrapped (2026-06-28).** Created `random-fields/percolation` as a Lean 4 /
   Mathlib v4.30.0 project for percolation and random-cluster autoformalization. Added the
   Grimmett source corpus, `lean4-skills` agent contract, comparator/audit docs, a source-ordered
   seed plan, and compile-light Lean scaffolding for core configurations, Bernoulli percolation,
   critical parameters, planar duality, and random-cluster parameters.

2. **Percolation textbook source audit scorecards (2026-06-29).** Imported the
   optimal-transport repository's autonomous-autoformalization source criterion
   into `kg/TextbookCriterion/` and added a percolation-specific textbook audit
   scorecard. The scorecards distinguish the official Grimmett comparator
   sources from local candidate PDFs by Kesten, Duminil-Copin, and Grimmett's
   *Probability on Graphs*, and record that planar surrounding-circuit arguments
   require explicit discrete frontier/parity scaffolding before autonomous proof
   search.

## Axiom Ledger

Empty.

## Anti-Library

Nothing rejected yet. Record false starts here with the lesson learned.
