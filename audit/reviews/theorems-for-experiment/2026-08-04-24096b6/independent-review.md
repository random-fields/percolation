# Independent read-only review

The following report is preserved from the first independent pass over the reviewed file hash.

## Report

Independent review result: no substantive statement mismatch found.

Review context:

- Lean file SHA256: `ba5acadf97dfb5db3704e69d6274fe1302be6aebe9497863c02afce3041438fa`
- Git HEAD and `origin/main`: `24096b6f4fcd30c1aba1beffcf0baaa4148c9629`
- Grimmett PDF SHA256: `dd81586d5bc88581bb166c9df230d78cca6e13033aef995ba4f2da94c3c43df6`
- Duminil-Copin PDF SHA256: `c29e39e3600e76530efcb150ba211d3b1ca5373f6b190b99495da84cc6630e1d`

### 1. `grimmett_theorem_3_7` — faithful

Source: Grimmett, printed p. 59 / PDF p. 72:

`p_c(T) < p_c(L^2)`.

The Lean triangular graph is the square lattice with all north-east/south-west diagonals, hence
the standard triangular lattice used in Figure 3.4. Its measure assigns the same Bernoulli
parameter independently to horizontal, vertical, and diagonal bonds. `triangularTheta` is the
probability that the origin cluster is infinite, and its critical probability uses Grimmett's
exact normalization `sup {p : theta(p) = 0}`. `cubicCriticalProbability 2` is the corresponding
bond threshold of `L^2`.

No correction needed.

### 2. `grimmett_theorem_11_70` — faithful with representational caveats

Source: Grimmett, printed p. 315 / PDF p. 328:

`P_p(LR(l)) = tau` implies
`P_p(O(l)) >= {tau (1 - sqrt(1 - tau))^4}^12`.

The formula, exponents, inequality, parameters, and positive-integral condition on `l` match
exactly. The crossing event removes edges joining two boundary vertices, exactly as Grimmett
requires. Lean translates `B(l) = [-l,l]^2` to `[0,2l] x [-l,l]`; its Bernoulli probability is
unchanged by translation.

The annulus condition is exactly `l < ||z||_infinity <= 3l`. “Surrounding the lattice origin” is
encoded by odd face parity at the face whose lower-left corner is `(0,0)`, geometrically the point
`(1/2,1/2)`. Since `l >= 1` and the circuit is disjoint from all of `B(l)`, this point and the
vertex origin lie in the same complementary component, so this does not change the event. It
would nevertheless be useful for the docstring to state this equivalence explicitly.

No mathematical correction needed.

### 3. `duminilCopin_proposition_2_14` — faithful

Source: Duminil-Copin, printed p. 19 / PDF p. 27; crossing notation is defined on printed p. 18 /
PDF p. 26:

For every `n >= 1`,
`P_(1/2)[C_v([-n,n] x [-n,2n])] >= 1/128`.

The Lean rectangle, bottom and top sides, homogeneous square-lattice bond measure at `p = 1/2`,
quantifier, constant, and inequality all match. Filtering `cubicBoxEdges` by membership of both
endpoints produces exactly all nearest-neighbor bonds internal to the rectangle. Existence of an
open walk between the bottom and top sides is extensionally the same crossing event as the
source's open-path formulation.

No correction needed.

Proof status is separate: all three declarations still rely on intentional `sorry`, hence on
`sorryAx`. This review establishes statement fidelity only; it does not certify any proof.

## Producer disposition

Accepted. No production statement was changed. The central-face representation caveat for
Theorem 11.70 is recorded in `correspondence.md`; it does not alter the event for positive `l`.
