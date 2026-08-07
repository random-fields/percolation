# Independent review of the Figure 2.3 proof expansion

Date: 2026-08-04

Scope: read-only review of the source pages, the coordinate/event definitions in
`Percolation/TheoremsForExperiment.lean`, and `PICTORIAL_PROOF_EXPANSION.md`. The reviewer was
not the author of the proposed expansion and made no repository edits.

## Verdict

`BLOCKED_MISSING_GEOMETRY`, not `REJECTED_FALSE`.

The source argument and the Lean rectangle/bridge coordinates are consistent. The proposed
V2--V5 expansion is not yet precise enough to discharge the no-axiom proof.

## Required repairs

1. Normalize the selected left--right crossing: its start is the last left-side visit, its
   finish is the first subsequent right-side visit, and every interior vertex has `0 < x < n`.
   A merely self-avoiding path is insufficient. For `n = 2`, the path
   `(0,0),(1,0),(1,1),(0,1),(0,2),(1,2),(2,2)` revisits the left side, and its union with its
   reflection branches and contains a loop.
2. Use one coherent fiber design. The accepted design is a finite family of good reached-face
   fibers `F_R`, with a deterministic normalized boundary `gamma_R`. Prove the finite partition,
   pairwise disjointness, openness of `gamma_R` on `F_R`, and dependence on a sufficient exposed
   support `E_R`. Do not claim `E_R` is precisely the queried bonds.
3. Generic finite reachability gives dependence on all edges incident to the reached set. It
   does not prove one-sided primal locality or extract a highest boundary path. The current
   `BRDualExploration` API explicitly does not make that extraction; a deterministic
   interface/extraction theorem is still required.
4. Define `S(gamma_R)` edgewise. Its fresh support must include the final below-to-barrier edge
   and exclude barrier edges and exposed above-side edges. Prove that every bottom--top walk has
   a first barrier contact whose entire prefix edge finset lies in this support, including turns,
   axis contacts, side endpoints, boundary-running paths, and degree-four interface vertices.
5. Prove explicitly that vertical-axis reflection maps the fresh support and contact events, and
   that the full lower-square vertical crossing event is contained in their union. Supply the
   standard-axiom half-probability placement separately.
6. Prove `F_R inter contact(gamma_R) subset B_n`, dependence, disjoint-support factorization, the
   measurable finite partition, and ratio-free summation.

## Coordinate findings

- The inclusive vertex regions and internal-edge filters for the target rectangle, `Q_n`, the
  lower square, and the upper rectangle are correct.
- The vertical transport is the integer map `y |-> n - y`. For odd `n` it has no fixed lattice
  vertex, so the prose must not say that it fixes a lattice line pointwise.
- The V1 placement generally proves event/image inclusion, not equality with the full target
  edge finset.
- Lower-to-upper event inclusion is sufficient for the probability comparison; event equality
  is unnecessary.

The public theorem still had a `sorry` at review time. No trust or axiom-free completion verdict
was issued.
