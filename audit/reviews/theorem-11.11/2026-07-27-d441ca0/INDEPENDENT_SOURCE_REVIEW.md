# Independent source review: Grimmett Theorem 11.11

Review date: 2026-07-27. Scope: source fidelity and challenge shape only. I did not invoke Lean,
Lake, Comparator, or inspect a mechanical axiom certificate.

## Source finding

The primary source is `grimmett-percolation-1999`,
`kg/textbooks/Grimmett-Percolation-2ed-1999.pdf`, SHA-256
`dd81586d5bc88581bb166c9df230d78cca6e13033aef995ba4f2da94c3c43df6`.
Grimmett's Theorem (11.11) is on printed p. 287, PDF p. 300. It states that the critical
probability of bond percolation on the two-dimensional square lattice is one half.

The earlier definitions support that reading directly. In Sections 1.3--1.4 Grimmett takes the
vertices to be `Z^d`, joins vertices at lattice distance one, and independently opens every bond
with probability `p`. Equation (1.6) defines `theta(p)` as the probability that the origin cluster
is infinite, and equation (1.8) defines `p_c(d)` as the supremum of parameters for which
`theta(p)` is zero.

The uploaded Bollobas--Riordan paper is identical to the catalogued repository copy (both have
SHA-256 `bbf6c49ae64f821aa62159272b93dd643f17e3ff4dce00a3285709fd9b6fbef2`). It independently
corroborates the target, but is correctly secondary: Theorem 8 on journal p. 477 proves the
critical-extinction half, Theorem 10 on p. 479 proves percolation for every `p > 1/2`, and the
paper then combines them to obtain the exact critical probability.

## Lean translation

The challenged proposition is

```lean
Percolation.cubicCriticalProbability 2 = (1 : ℝ) / 2
```

This is a faithful translation using the canonical production definitions below the theorem proof:

- `Cubic 2 = Fin 2 -> Z`, with `cubicGraph 2` the undirected signed-unit-step graph, represents
  the nearest-neighbour square lattice `Z^2`.
- `CubicEdge 2` and `EdgeConfiguration 2 = Set (CubicEdge 2)` encode bonds and their open states.
- `bernoulliBondMeasure 2 p` is `setBer` on all cubic bonds, so bonds are independently open with
  common parameter `p`.
- `theta 2 p` is the real probability that the open cluster of `cubicOrigin` is infinite.
- `cubicCriticalProbability 2` is the real `sSup` of the image of those `p : I = [0,1]` for which
  `theta 2 p = 0`, matching Grimmett's equation (1.8), including its endpoint convention.
- `(1 : ℝ) / 2` gives the source's numerical value in the definition's codomain.

The source theorem has no hypotheses, and neither does the challenge.

## Challenge audit and verdict

`comparator/Challenge.lean` imports `Percolation.Critical.Basic`, the lower layer that defines the
quantity without importing the production exact-threshold theorem. Its only declaration is
`ComparatorChallenge.grimmett_theorem_11_11`; its sole open proof is the intentional challenge
`sorry`. `comparator/config.json` lists exactly that one theorem. The recorded challenge hash,
`e22fddedb743edba69e00b5bcf94b715e2414cbc5776e1cc86cc302a4b9e9787`, matches the file reviewed.

**Source-fidelity and one-theorem-shape verdict: PASS.** I found no semantic discrepancy in the
source citation or Lean proposition. **Mechanical Comparator verdict: NOT RUN / INCONCLUSIVE.**

There is one process discrepancy. The bundle says that the challenge was prepared inside the
implementation effort, and `Solution.lean` already exists; therefore this review independently
validates the statement but does not retroactively establish the stricter provenance of a
reviewer-authored challenge frozen before the solution was exposed. The bundle is also still in a
dirty, non-immutable worktree. A trusted final run should either use a freshly frozen
reviewer-owned challenge at an immutable revision or explicitly record acceptance of this
independent content validation, then run Comparator under the protocol's pinned sandbox.
