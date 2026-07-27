# Source selection audit for Grimmett Theorem 11.11

Audit date: 2026-07-26. Rubric: `kg/TextbookCriterion/autoformalization-source-audit-prompt.md`
v2, applied without weakening its grounding or verdict gates.

## Decision

Use **Grimmett, Theorem 11.11, as the primary statement source and comparator**. Use the
Bollobás--Riordan finite-planar segment (Lemma 3, Lemma 6, Corollary 7, and Theorem 8) only as a
secondary proof source for discharging the remaining RSW/lowest-crossing obligation. Do not switch
the primary proof route to the complete Bollobás--Riordan paper: its short upper-bound argument is
short only after importing the Friedgut--Kalai sharp-threshold theorem, for which the pinned
Mathlib and this repository have no implementation.

This choice is driven by the current formal frontier, not by page count. The repository already
contains `Percolation.cubicCriticalProbability_two_eq_half`; its only recorded nonstandard
transitive dependency is the precisely stated axiom
`Percolation.rswThreeHalvesCrossingProbability_ge`. The finite duality, FKG gluing, annular
incidence, shifted barriers, barrier independence, and upper-bound route are proved declarations.

## Source custody and reproducibility

| Source id | Source and role | Repository path | SHA-256 | Provenance / rights status |
|---|---|---|---|---|
| `grimmett-percolation-1999` | Geoffrey Grimmett, *Percolation*, 2nd ed. (1999), primary theorem and comparator | `kg/textbooks/Grimmett-Percolation-2ed-1999.pdf` | `dd81586d5bc88581bb166c9df230d78cca6e13033aef995ba4f2da94c3c43df6` | Existing project source; no new redistribution conclusion is made here |
| `bollobas-riordan-harris-kesten-2006` | Béla Bollobás and Oliver Riordan, “A Short Proof of the Harris--Kesten Theorem”, *BLMS* 38 (2006), 470--484, secondary finite-planar source | `kg/textbooks/Bollobas-Riordan-Harris-Kesten-2006.pdf` | `bbf6c49ae64f821aa62159272b93dd643f17e3ff4dce00a3285709fd9b6fbef2` | User-provided `/Users/aaron/Downloads/bollobas.pdf`, copied into the source catalog on 2026-07-26; **redistribution rights unreviewed** |

Local possession, a DOI, or a catalog entry is not evidence of permission to redistribute the
Bollobás--Riordan PDF. The repository should not publish that binary until its redistribution
status has been reviewed.

## Environment and grounding method

- Repository revision inspected: `13da9d47fed5e6d8bfcf839df4154d5356c55216`.
- Lean toolchain: `leanprover/lean4:v4.30.0`.
- Mathlib pin: `c5ea00351c28e24afc9f0f84379aa41082b1188f`.
- Tools actually used: `rg` 15.2.0 over project and pinned Mathlib sources; Lean LSP local
  declaration search; LeanSearch; Loogle; `pdftotext`; `pdfinfo`; `sha256sum`; and the pinned
  `lake`/Lean compiler.
- The live LSP declaration index answered local searches. An initial `lean_run_code`/`lean_verify`
  attempt reported stale or missing object files in this integration worktree, so those failed
  calls are not counted as confirmation. A target build was started to refresh those objects; its
  status and the scope of the current mechanical certificate are recorded below.
- A declaration is called “present” below only when an exact source/index query found it. A
  declaration whose implementation is an `axiom` is reported as such; mere elaboration of its
  name is not counted as a proof.

All Mathlib and repository availability claims in this audit are relative to the pins above.

## Criterion 0: provisional units of work

The cheap structural pre-pass gives three units:

1. **G — Grimmett exact-threshold route in the current scaffold.** The statement is Theorem 11.11
   on printed p. 287. The selected proof strata are Lemma 11.21 and subcritical decay for
   `p_c <= 1/2`, together with the finite RSW/annular-barrier route to Lemma 11.12 for
   `p_c >= 1/2`. Grimmett's later Theorem 11.70 and Lemmas 11.73/11.75 supply that RSW stratum.
2. **BR-all — the complete Bollobás--Riordan paper route.** This includes Sections 2--6, from
   Harris/FKG and finite planar duality through the sharp-threshold torus argument and one of the
   final percolation deductions.
3. **BR-finite — Bollobás--Riordan's finite-planar segment.** This is the part on pp. 473--477:
   Lemma 3, Corollaries 4--5, Lemma 6, Corollary 7, and Theorem 8.

The fault line is foundational: BR-finite uses finite graph geometry, independence, and FKG;
BR-all additionally depends on the external Friedgut--Kalai theorem and torus symmetrization.
BR-finite is therefore scored separately even though it is literally a subsegment of BR-all.
The split is provisional pending the scores and is revisited at the end.

## Dependency comparison

The selected formal dependency graph is:

```text
Grimmett Theorem 11.11 / cubicCriticalProbability_two_eq_half
├── p_c(Z²) ≤ 1/2
│   ├── finite rectangle primal/dual alternative (Grimmett Lemma 11.21)
│   └── subcritical exponential decay (Grimmett Theorem 5.4 / 6.1 route)
└── p_c(Z²) ≥ 1/2
    └── theta(2, 1/2) = 0
        ├── half-density finite crossing lower bound
        ├── positive long-rectangle crossing bound
        │   ├── lowest/leftmost crossing stopping-set lemma  ← remaining kernel
        │   └── FKG plus deterministic crossing incidence
        ├── four crossings imply a dual annular barrier
        └── independent barriers force theta = 0
```

The complete Bollobás--Riordan graph has a different upper branch:

```text
Lemma 1 (Harris/FKG) + Lemma 3 (duality)
├── Corollaries 4--5
└── Lemma 6 → Corollary 7 → Theorem 8: theta(1/2) = 0

Corollary 7 + Theorem 2 (Friedgut--Kalai)
→ Lemma 9 (high-probability torus/rectangle crossings)
→ Theorem 10, or Lemma 11 plus a renormalization alternative
→ p_c(Z²) ≤ 1/2
→ exact threshold
```

The second graph explains why the complete paper is not a shortcut in the present environment.

## Scorecard G — Grimmett exact-threshold route

**SOURCE:** `kg/textbooks/Grimmett-Percolation-2ed-1999.pdf`, Chapter 11, especially printed
pp. 287--294 and 315--323; primary comparator id `grimmett-percolation-1999`.

**ENVIRONMENT:** Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`; Lean
`leanprover/lean4:v4.30.0`; project `13da9d47...`; local declaration index, project/Mathlib source
search, LeanSearch, Loogle, and pinned Lean compiler available as qualified above.

**UNIT OF WORK:** Theorem 11.11 through the already selected finite-duality, subcritical-decay,
RSW, and independent-annulus implementation path.

**FAULT LINE:** The selected route crosses from already proved finite/measure-theoretic layers to
one unproved lowest-crossing probability inequality, Grimmett Lemma 11.73. Split is provisional.

**SIZE/EFFORT:** The final theorem plus approximately eight load-bearing interfaces. The present
formal shell is complete; discharging the one RSW axiom is estimated at roughly 8--15 substantive
human proof interventions, principally definitions and stopping-set support lemmas rather than
final algebra.

### Grounding evidence for criteria 2, 5, and 6

Here `a/b/c` means existence / right generality / same source statement (or a proved bridge).

| Object or prerequisite | Query and tool | Result at the pinned revisions | Axes | Location |
|---|---|---|---|---|
| Percolation probability | LSP local search `theta`; exact `rg` of project declarations | `Percolation.theta (d : ℕ) (p : I)`, probability of an infinite origin cluster | a ✓ · b ✓ at cubic dimension 2 · c ✓ | our repo, `Bernoulli/Basic.lean` |
| Critical probability | LSP local search `cubicCriticalProbability`; exact source search | `Percolation.cubicCriticalProbability`, defined as the supremum of zero-`theta` parameters | a ✓ · b ✓ · c ✓ | our repo, `Critical/Basic.lean` |
| Grimmett finite crossing | local search `grimmettRectangleCrossingEvent`; source inspection | `Percolation.grimmettRectangleCrossingEvent`; `half_le_grimmettRectangleCrossingProbability_even` supplies the half-density bound | a ✓ · b ✓ · c ~ boundary conventions are connected by proved graph-isomorphism/duality bridges | our repo, `SquareCritical.lean`, `BondCrossingDuality.lean` |
| Bernoulli product measure | exact source query `setBernoulli` and `bernoulliBondMeasure` | Mathlib `ProbabilityTheory.setBernoulli`; project specialization `Percolation.bernoulliBondMeasure` | a ✓ · b ✓ · c ✓ | Mathlib `Probability/Distributions/SetBernoulli.lean`; our repo |
| FKG | LeanSearch natural-language query returned Mathlib `fkg`; local search `setBernoulli_real_fkg` returned the directly usable project theorem | `fkg`; `Percolation.setBernoulli_real_fkg` | a ✓ · b ✓ for measurable increasing Bernoulli events · c ✓ | Mathlib and our repo, `Bernoulli/FKGInfinite.lean` |
| Deterministic RSW gluing | exact project queries `rswGluingThreeIntersection_subset`, `rswCircuitGluingIntersection_subset` | Both are proved theorems; their probability consequences are in `RSWGluing.lean` | a ✓ · b ✓ · c ✓ | our repo |
| Lowest-crossing bound | local search and source query `rswThreeHalvesCrossingProbability_ge` | Exact desired inequality exists **only as an axiom** in `Planar/External.lean` and is used by `RSWNumeric.lean` | a ~ declaration only · b ✓ · c ✓; proof absent | our repo axiom |
| Annular separation | exact source queries `dualRSWAnnulusOpenCircuitEvent_subset_barrier` and `iIndepSet_expandedCriticalAnnulusBarrierEvent` | Both are proved theorems | a ✓ · b ✓ · c ✓ | our repo, `Planar/AnnulusDuality.lean` |
| Independent-barrier limit | exact source query `theta_eq_zero_of_iIndep_barriers`; Mathlib source query `iIndepSet.meas_biInter` | Project theorem reduces to Mathlib's `iIndepSet` finite-intersection product formula | a ✓ · b ✓ · c ✓ | our repo plus Mathlib `Probability/Independence/Basic.lean` |
| Final statement | local search `cubicCriticalProbability_two_eq_half`; exact source inspection | `Percolation.cubicCriticalProbability_two_eq_half : cubicCriticalProbability 2 = 1 / 2` | a ✓ · b ✓ · c ✓ | our repo, `Planar/SquareThresholdExact.lean` |

### Five-lemma explicit-proof probe

The five nontrivial middle/load-bearing results sampled were Lemma 11.21, Lemma 11.73,
Lemma 11.75, Theorem 11.70, and the two-inequality assembly in Theorem 11.11. Lemma 11.73
explicitly delegates the existence, uniqueness, and stopping-set behavior of the lowest crossing
to topological reasoning/Russo; Lemma 11.21 invokes a minor variant of Proposition 11.2. Lemma
11.75 gives its FKG gluing steps, Theorem 11.70 is explicit algebra from Lemmas 11.73/11.75, and
Theorem 11.11 names its upper-bound inputs. Thus two of five require a secondary justification,
but both have exact formal interfaces and only Lemma 11.73 remains unproved locally.

### Nine criteria

1. **Explicit proofs — Yellow.** Two sampled results invoke a secondary planar/topological
   justification, with Lemma 11.73 the sole unresolved one on the selected formal route.
2. **Unusual conventions — Green.** Tool-confirmed project definitions of `theta`, critical
   probability, Bernoulli bond measure, and rectangle crossing match the source; finite-boundary
   differences have proved bridges.
3. **Logical structure — Green.** The selected DAG has explicit interfaces: finite duality and
   decay prove the upper bound, while RSW plus independent barriers prove `theta(1/2)=0` and the
   lower bound.
4. **Left-to-reader gaps — Yellow.** The lowest-crossing topology/stopping-set claim is genuinely
   omitted in Grimmett and is not supplied by Mathlib; it is isolated as one exact project axiom.
5. **Mathlib proximity — Yellow.** Most representative prerequisites are directly proved in the
   project on top of Mathlib, but the load-bearing lowest-crossing inequality is still an axiom.
6. **Definition uniqueness — Green.** The canonical infinite-origin-cluster and supremum
   definitions match; competing finite rectangle encodings are reconciled by proved bridges.
7. **Constructive content — Green.** The route uses ordinary classical finite choices, product
   measure, and countable probability arguments supported by Lean/Mathlib.
8. **Figure-dependent arguments — Yellow.** Figures 11.10 and 11.21--11.27 motivate genuine
   incidence facts; the project has formalized the duality and gluing facts, leaving only the
   lowest-crossing stopping-set content.
9. **Tower structure — Green.** The theorem naturally separates into duality/decay, RSW,
   annular incidence, and independent-barrier layers with stable formal interfaces.

**VERDICT: NEEDS SCAFFOLDING** — the v2 gate requires this verdict for more than two Yellow
criteria. In practical repository terms, that scaffolding is already almost complete: the
remaining work is the single RSW kernel rather than a new formalization of Theorem 11.11. Expect
roughly 8--15 focused human interventions.

**Key risks:**

- Treating an axiom with the exact desired type as if it were an implemented prerequisite.
- Reintroducing a general discrete Jordan curve theorem instead of proving the smaller canonical
  crossing/stopping-set statement.
- Mixing Grimmett's several finite-boundary rectangle conventions without using the existing
  bridge declarations.

## Scorecard BR-all — complete Bollobás--Riordan route

**SOURCE:** `kg/textbooks/Bollobas-Riordan-Harris-Kesten-2006.pdf`, complete paper, source id
`bollobas-riordan-harris-kesten-2006`.

**ENVIRONMENT:** Same pinned environment and tools as Scorecard G.

**UNIT OF WORK:** Sections 2--6, including Theorem 2 (Friedgut--Kalai), Lemma 9, and Theorem 10 or
the qualitative/renormalization alternatives after Lemma 11.

**FAULT LINE:** Section 5 changes foundation from finite planar percolation to a general sharp
threshold theorem on symmetric monotone Boolean events. Split is provisional.

**SIZE/EFFORT:** Fifteen paper pages, but a new sharp-threshold library dominates the cost. A
realistic estimate is more than 35--60 substantive human interventions, with significant theorem
design before the paper proof can be replayed.

### Grounding evidence for criteria 2, 5, and 6

| Object or prerequisite | Query and tool | Result at the pinned revisions | Axes | Location |
|---|---|---|---|---|
| Product Bernoulli events and monotonicity | exact Mathlib source query `setBernoulli`; project source search | Mathlib `ProbabilityTheory.setBernoulli` and project increasing-event APIs | a ✓ · b ✓ · c ✓ | Mathlib / our repo |
| Harris/FKG inequality | LeanSearch query for monotone events; local query `setBernoulli_real_fkg` | Mathlib `fkg`; directly usable `Percolation.setBernoulli_real_fkg` | a ✓ · b ✓ · c ✓ | Mathlib / our repo |
| Finite rectangle duality | project queries `grimmettRectangleCrossingEvent`, `half_le_grimmettRectangleCrossingProbability_even` | Exact finite crossing and proved half-density lower bound | a ✓ · b ✓ · c ~ minor rectangle normalization bridge already proved | our repo |
| Friedgut--Kalai sharp threshold | `rg -ni` over all `Percolation` and pinned `Mathlib`; LSP local searches `friedgut`, `sharpThreshold`; LeanSearch “Friedgut Kalai sharp threshold for symmetric monotone Boolean events”; Loogle name queries `"Friedgut"`, `"sharpThreshold"` | No source/index/Loogle hit; LeanSearch returned FKG and unrelated declarations, not a sharp-threshold theorem | a × · b × · c × | nowhere in searched environment |
| Lemma 9 high-probability crossing | source/index queries for sharp-threshold and torus-crossing consequences | No independent local theorem matching BR Lemma 9; its source proof calls Theorem 2 | a × as this route's theorem · b/c blocked | nowhere as a proved BR-route interface |
| Final threshold statement | local search `cubicCriticalProbability_two_eq_half` | Exact final statement exists, but its proof follows the Grimmett/RSW scaffold rather than BR's sharp-threshold route | a ✓ · b ✓ · c ✓ statement, route differs | our repo |

The Friedgut--Kalai absence claim uses four independent query modes and two phrasings; it is not
inferred from a single failed search.

### Five-lemma explicit-proof probe

The middle-third probe used Lemma 6, Corollary 7, Theorem 8, Lemma 9, and Theorem 10. The finite
planar first three are substantially argued in the paper. Lemma 9 is load-bearing for the upper
bound and invokes Theorem 2, which the authors explicitly import from Friedgut--Kalai (and trace
to KKL). Theorem 10 then depends on Lemma 9. Consequently the paper is intentionally not
self-contained at exactly the point that is absent from the formal environment.

### Nine criteria

1. **Explicit proofs — Red.** The load-bearing upper-bound step imports the external
   Friedgut--Kalai theorem rather than proving it, and every Section 6 completion depends on that
   sharp-transition input.
2. **Unusual conventions — Yellow.** Bernoulli and crossing conventions align, but the finite
   torus symmetric event and the paper's `p_H` presentation need nontrivial bridges to the current
   cubic-lattice critical-probability API.
3. **Logical structure — Green.** The paper clearly separates self-duality, Harris's theorem,
   sharp threshold, and three final deductions.
4. **Left-to-reader gaps — Yellow.** Lemma 6 says a conditional crossing estimate is easy, and
   Lemma 9 sketches extensions in aspect ratio; these are plausible but formal work.
5. **Mathlib proximity — Red.** Friedgut--Kalai/KKL at the required quantitative generality is in
   neither pinned Mathlib nor this repository after multi-query search.
6. **Definition uniqueness — Green.** Product percolation and critical threshold are canonical;
   torus events are auxiliary definitions rather than competing foundations.
7. **Constructive content — Green.** The arguments are classical but standard once the
   sharp-threshold theorem is available.
8. **Figure-dependent arguments — Yellow.** Figures guide several gluing and renormalization
   constructions, but the intended event implications are mostly stated in prose.
9. **Tower structure — Green.** The strata and dependency on Theorem 2 are unusually explicit.

**VERDICT: DO NOT PROCEED** — criterion 1 is a hard Red, and criterion 5 independently identifies
the missing load-bearing library. Formalizing the complete route is a separate sharp-threshold
project, not the shortest path to Theorem 11.11 here.

**Key risks:**

- Underestimating Theorem 2 because it occupies only a few lines in the paper.
- Building torus/symmetry infrastructure before discovering that the quantitative influence
  theorem is absent.
- Duplicating an already completed exact-threshold shell with a strictly larger dependency base.

## Scorecard BR-finite — Lemma 3 through Theorem 8

**SOURCE:** The same Bollobás--Riordan PDF, pp. 473--477 (paper Sections 3--4), used only as a
secondary proof source.

**ENVIRONMENT:** Same pinned environment and tools as Scorecard G.

**UNIT OF WORK:** Lemma 3, Corollaries 4--5, Lemma 6, Corollary 7, and Theorem 8. This segment ends
before the Friedgut--Kalai application.

**FAULT LINE:** The segment uses only finite planar geometry, FKG, independence, and disjoint
annuli; Section 5 begins the absent sharp-threshold layer. Split is provisional.

**SIZE/EFFORT:** Roughly five paper pages and six main results. Because most downstream
infrastructure already exists, estimate roughly 10--20 substantive interventions, concentrated
on a canonical leftmost crossing and its support/conditional-independence properties.

### Grounding evidence for criteria 2, 5, and 6

| Object or prerequisite | Query and tool | Result at the pinned revisions | Axes | Location |
|---|---|---|---|---|
| Primal/dual rectangle alternative (Lemma 3) | project source queries for rectangle duality and crossing traces | `grimmettRectangleDualTraceEquiv`, `half_le_grimmettRectangleCrossingProbability_even`, and the surrounding finite interface are proved | a ✓ · b ✓ · c ~ BR coordinates need a routine bridge | our repo, `BondCrossingDuality.lean` |
| Increasing-event FKG (Lemma 1 uses) | local search `setBernoulli_real_fkg`; exact source inspection | `Percolation.setBernoulli_real_fkg` | a ✓ · b ✓ · c ✓ | our repo |
| Rectangle and annulus events | local/source queries `rswRectangleCrossingEvent`, `rswAnnulusOpenCircuitEvent` | Exact measurable increasing crossing events and circuit event exist | a ✓ · b ✓ · c ~ coordinate/aspect-ratio normalization only | our repo, `RSWEvents.lean` |
| Canonical leftmost crossing and stopping-set support (Lemma 6) | `rg` queries `left.?most`, `lowest.*crossing`, `stopping.?set`; LSP local searches `leftMost`, `lowestCrossing` | Only comments and the large probability axiom were found; no canonical-crossing/stopping-set declaration | a × · b × · c × | nowhere in searched project/Mathlib-facing index |
| Gluing incidence for Corollary 7 | exact project queries `rswGluingThreeIntersection_subset`, `rswCircuitGluingIntersection_subset` | Both deterministic inclusions are proved | a ✓ · b ✓ · c ✓ | our repo |
| Annular barrier and disjointness for Theorem 8 | exact queries `dualRSWAnnulusOpenCircuitEvent_subset_barrier`, `iIndepSet_expandedCriticalAnnulusBarrierEvent` | Both are proved; expanded annulus edge sets are pairwise disjoint | a ✓ · b ✓ · c ✓ | our repo, `AnnulusDuality.lean` |
| Infinite-cluster conclusion | exact query `theta_eq_zero_of_iIndep_barriers` | Proved general theorem turns uniform independent barriers into `theta = 0` | a ✓ · b ✓ · c ✓ | our repo, `IndependentBarriers.lean` |

### Five-lemma explicit-proof probe

The probe used Lemma 3, Corollary 4, Corollary 5, Lemma 6, and Corollary 7; Theorem 8 was checked
as the segment endpoint. Lemma 3 gives an explicit finite middle-graph construction but appeals to
the easy separation part of Jordan for exclusivity. Corollaries 4--5 are explicit. Lemma 6 gives
the conditioning strategy but compresses construction of the leftmost path and the key
first-meeting estimate. Corollary 7 and Theorem 8 state their FKG and independence calculations.
This is substantially better targeted than the complete-paper route, but it is not push-button.

### Nine criteria

1. **Explicit proofs — Yellow.** Lemma 3 and Lemma 6 each compress one planar/stopping-set fact,
   while the probability calculations and segment endpoint are explicit.
2. **Unusual conventions — Green.** The project has tool-confirmed matching bond configurations,
   crossing events, dual traces, and `theta`; coordinate differences have existing bridges.
3. **Logical structure — Green.** Lemma 3 gives self-duality, Lemma 6 gives the extension step,
   Corollary 7 gives long crossings, and Theorem 8 gives independent annular blocking.
4. **Left-to-reader gaps — Yellow.** The leftmost-path measurability/support assertion and the
   conditional half-probability estimate in Lemma 6 require original formal scaffolding.
5. **Mathlib proximity — Yellow.** FKG, product measures, finite paths, independence, and all
   downstream barriers are present, but the canonical-crossing stopping-set API is absent.
6. **Definition uniqueness — Green.** The mathematical events are canonical up to finite boundary
   conventions, and the project already centralizes those conventions.
7. **Constructive content — Green.** All path choices are over finite graphs; classical choice and
   finite minimization are standard Lean techniques.
8. **Figure-dependent arguments — Yellow.** Figures 2--5 carry incidence intuition, but
   `PICTORIAL_PROOF_EXPANSION.md` gives rigorous finite replacements and the repository already
   proves the annular incidence portion.
9. **Tower structure — Green.** The segment has a short linear tower and a clean handoff at a
   positive long-crossing constant.

**VERDICT: NEEDS SCAFFOLDING** — multiple Yellow criteria remain, but the missing scaffold is
narrow and directly targets the one axiom in Scorecard G. This segment is therefore the chosen
secondary source, with roughly 10--20 focused interventions expected.

**Key risks:**

- Defining “leftmost” geometrically without proving that its selection event depends only on the
  correct side of the path.
- Accidentally importing a full Jordan theorem when finite reachability/parity or a direct barrier
  formulation suffices.
- Formalizing BR's exact constants when Theorem 11.11 needs only some uniform positive constant.

## Closing re-segmentation check

The provisional source split **survives** the scoring.

- BR-finite really does stop before the red foundation: neither Lemma 3 through Theorem 8 nor the
  independent-annulus conclusion uses Friedgut--Kalai. It is not, however, a proof of the whole
  exact-threshold theorem; it supplies only `theta(1/2)=0` and hence the lower bound on the critical
  probability.
- BR-all remains Red after separating BR-finite because its upper branch still runs through
  Theorem 2, Lemma 9, and Theorem 10 (or a later alternative with the same sharp-transition
  input). No boundary move can make the complete route suitable without first formalizing the
  sharp-threshold theorem.
- Scorecard G did not hide a red dependency inside a Green segment: it was scored Yellow exactly
  where the unproved RSW kernel occurs. For implementation scheduling it is useful to view G as
  “completed exact-threshold shell” plus “remaining lowest-crossing kernel”, but these are not
  separate source candidates. The shell is only conditionally complete until that kernel is
  discharged, so no optimistic re-score is warranted.

Final units are therefore unchanged: **G as primary comparator**, **BR-finite as secondary RSW
discharge source**, and **BR-all rejected as the implementation route**.

## Operational consequence

The next source-driven task should not re-formalize the final equality. It should replace
`rswThreeHalvesCrossingProbability_ge` with a theorem. Start from the smaller BR Lemma 6 interface:

1. define a finite canonical leftmost top--bottom crossing;
2. prove existence/uniqueness and a finite edge-support characterization;
3. prove that selection of a particular crossing is insensitive to edges on its right;
4. define the reflected first-hit extension event and its disjoint support;
5. derive a uniform positive long-rectangle crossing bound (BR Corollary 7), without preserving
   BR's exact numerical constant unless it is free;
6. feed that bound through the already proved RSW gluing, annular barrier, and independence stack;
7. rerun `#print axioms Percolation.theta_two_half_eq_zero` and
   `#print axioms Percolation.cubicCriticalProbability_two_eq_half`.

This preserves Grimmett Theorem 11.11 as the comparator while using the shorter paper only where
it actually reduces the remaining formal burden.

## Validation note

The source hashes, metadata, page locations, declaration names, and no-hit claims above were
checked in the pinned worktree. At the time this audit was finalized, the integration target build
was still in progress, so this document claims no fresh compiler-level axiom certificate for
integration revision `13da9d47...`. The existing mechanical axiom certificate remains pinned to
revision `fa86568` until the integration build completes and the two `#print axioms` commands above
are rerun. The “one remaining RSW axiom” statement is therefore the current recorded audit status,
corroborated here by the exact source dependency, not a newly issued integration certificate.
