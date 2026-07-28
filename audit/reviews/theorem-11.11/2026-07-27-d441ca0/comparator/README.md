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

## Trusted Comparator result

The dedicated GitHub Actions workflow ran this one-theorem bundle successfully on commit
`6f9a681d72c9a0c1513e65e4f78ff3c126150ef6`:

- run: [Theorem 11.11 Comparator #30322302015](https://github.com/random-fields/percolation/actions/runs/30322302015);
- runner: clean `ubuntu-24.04` GitHub-hosted runner;
- Comparator revision: `099775bf2e6073fcb22aacd3a2809fdeac3fc84a`;
- Landrun revision: `5ed4a3db3a4ad930d577215c6b9abaa19df7f99f`;
- Lean toolchain: `leanprover/lean4:v4.30.0`;
- challenge hash: `e22fddedb743edba69e00b5bcf94b715e2414cbc5776e1cc86cc302a4b9e9787`;
- exit status: `0`;
- verdict: **PASS** — `Lean default kernel accepts the solution` and
  `Your solution is okay!`.

The comparison was wrapped in the restricted service used by the repository's pinned workflows:

```bash
systemd-run \
  --property=RestrictAddressFamilies=~AF_UNIX \
  --user --pipe --wait --collect \
  -E PATH="$PATH" \
  -E COMPARATOR_LANDRUN="$COMPARATOR_LANDRUN" \
  -E COMPARATOR_LEAN4EXPORT="$COMPARATOR_LEAN4EXPORT" \
  -E COMPARATOR_BIN="$COMPARATOR_BIN" \
  --working-directory "$(pwd)" \
  -- bash -c 'lake env "$COMPARATOR_BIN" config.json'
```

Comparator exported only `ComparatorChallenge.grimmett_theorem_11_11` together with the
configured standard axioms `propext`, `Quot.sound`, and `Classical.choice` (plus Lean's listed
primitive operations). It accepted both the challenge and solution exports.

For reproducibility, a macOS internal-mode run with the same pinned Comparator and `lean4export`
also exited successfully, but it used upstream's fake-Landrun helper and is not treated as a
trusted sandbox verdict.

This pass establishes that the production theorem has exactly the configured challenge statement
and stays within the permitted axiom set. As always, Comparator does not itself establish that the
reviewer-authored challenge is a faithful translation of Grimmett; the challenge was prepared
within the implementation effort, so its frozen hash establishes file identity rather than
independent source authorship.
