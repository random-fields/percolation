# Comparator producer draft

The producer drafted the challenge statements from the source inventory, then wrote solution
wrappers against production declarations. `Solution.lean` is compiled directly and contains no
`sorry` or `admit`. `Challenge.lean` intentionally contains open proofs, but it is not independent
review evidence and cannot be treated as trusted under `AUTOMATED_REVIEW.md`.

Comparator was **not run locally**. This macOS environment lacks `landrun`, Lean-compatible
`lean4export`, and Comparator. Under `AUTOMATED_REVIEW.md`, a normal Lean build is not a substitute
for Comparator and cannot establish the adversarial sandbox guarantee.

Follow-up: run the pinned upstream Comparator workflow in clean unprivileged Linux CI, hash
`Challenge.lean` before exposing `Solution.lean`, and record Comparator/`lean4export` revisions,
the exact `systemd-run`/`landrun` command, exit status, and stable CI log here.
