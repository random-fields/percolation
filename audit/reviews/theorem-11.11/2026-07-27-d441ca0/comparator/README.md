# Theorem 11.11 Comparator candidate

This source-only bundle has exactly one configured theorem:
`ComparatorChallenge.grimmett_theorem_11_11`. Its statement is Grimmett's Theorem 11.11,
the bond critical probability of the square lattice:

```lean
Percolation.cubicCriticalProbability 2 = (1 : ℝ) / 2
```

`Challenge.lean` imports only `Percolation.Critical.Basic`, the layer defining
`cubicCriticalProbability`, and contains the one intentional open proof permitted by the
Comparator protocol. `Solution.lean` imports the production theorem and is a direct wrapper
around `Percolation.cubicCriticalProbability_two_eq_half`.

The challenge SHA-256 was recorded before `Solution.lean` was created in this worktree:

```text
e22fddedb743edba69e00b5bcf94b715e2414cbc5776e1cc86cc302a4b9e9787  Challenge.lean
```

## Status

Comparator, Lean, and Lake were **not run** for this preparation. The files are therefore
unvalidated source artifacts, not evidence of a Comparator pass or axiom-freedom. The challenge
was prepared within the implementation effort; its hash establishes file identity, not
independent source authorship.

Before a trusted verdict, an independent reviewer must validate or freshly author the challenge
from Grimmett's source and freeze its hash at an immutable review revision. Then run the pinned
upstream Comparator workflow in a clean, unprivileged Linux environment with compatible
`landrun` and `lean4export`, the documented restricted `systemd-run` wrapper, and no prior
out-of-sandbox compilation of the solution. Record the pinned tool revisions, exact command,
network restrictions, exit status, and stable log location. Until that gate succeeds, the
Comparator verdict is **NOT RUN / INCONCLUSIVE**.
