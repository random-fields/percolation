# Autoformalization plan for Grimmett, Theorem 11.11

## 1. Scope, completion criterion, and status vocabulary

The source target is Grimmett, *Percolation*, second edition (1999), Theorem 11.11:

> For independent bond percolation on the square lattice, the critical probability is
> \(p_c(\mathbb Z^2)=1/2\).

The intended public Lean theorem is:

```lean
theorem Percolation.cubicCriticalProbability_two_eq_half :
    cubicCriticalProbability 2 = 1 / 2
```

“Completely formalized” means that this declaration is kernel-checked, its transitive axiom set
contains only the standard Lean/Mathlib axioms permitted by this project, its source-to-formal
correspondence has passed independent review, and the one-theorem Comparator challenge passes.
A green build while the theorem still depends on a project axiom is not completion.

This plan uses the following labels throughout:

- **[PROVED]**: a declaration exists and was checked in the audited Chapter 12 proof stack.
- **[AXIOM]**: the declaration exists as a project axiom and is the remaining logical gap.
- **[PROPOSED]**: a declaration name and type shape proposed by this plan; it does not yet exist.
- **[CHECK]**: existing code that must be rechecked after the integration branch is frozen.

The proof stack was independently checked at Chapter 12 commit `fa86568`. At that revision:

```text
#print axioms Percolation.cubicCriticalProbability_two_eq_half
#print axioms Percolation.theta_two_half_eq_zero
```

reported exactly:

```text
[propext, Classical.choice, Quot.sound,
 Percolation.rswThreeHalvesCrossingProbability_ge]
```

All other declarations in the target's transitive closure were checked without project axioms.
In particular, the upper bound, RSW gluing/incidence results, annulus transfer, shifted-annulus
independence, and the independent-barrier limit are already assumption-free. The current
integration tree was observed at commit `13da9d47fed5e6d8bfcf839df4154d5356c55216`, with Lean
`4.30.0` and Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`; these are observations,
not a frozen final review. Every gate below must be rerun on the final integrated revision.

There may be `sorry` in temporary design or Comparator challenge files as allowed by
`AUTOMATED_REVIEW.md`, but no production theorem, review case, counterexample, Comparator
solution, or final target may contain `sorry` or `admit`.

## 2. Source inventory and source choice

### 2.1 Sources under consideration

The source inventory for the final claim is deliberately narrow:

1. `grimmett-1999`, Chapter 11, especially Lemmas 11.12, 11.21, 11.70, 11.73, 11.75 and
   Theorem 11.11, in `kg/textbooks/Grimmett-Percolation-2ed-1999.pdf`.
2. Bollobás and Riordan, “A short proof of the Harris–Kesten theorem” (2006), in
   `kg/textbooks/Bollobas-Riordan-Harris-Kesten-2006.pdf`, especially Lemma 6, Corollary 7,
   and Theorem 8. The complete paper also uses Theorem 2 (Friedgut–Kalai, via KKL) and its
   later sharp-threshold argument.

The final Comparator challenge will contain only Grimmett's Theorem 11.11. Supporting source
results remain in the correspondence inventory because they explain the proof, but they are not
additional Comparator challenge theorems.

### 2.2 Evaluation criteria

The repository's nine source-audit criteria are:

1. explicitness of proofs;
2. unusual conventions and how well they are grounded;
3. logical structure;
4. gaps left to the reader;
5. proximity to verified Mathlib/local APIs;
6. uniqueness and stability of definitions;
7. constructive content;
8. dependence on figures or pictorial reasoning;
9. theorem-tower structure.

Criteria 1, 2, 6, and 8 are hard-red criteria. The source must first be segmented into actual
formalization units; a favorable score for a downstream corollary does not erase a red gap in an
upstream lemma.

### 2.3 Complete-source scorecard

| Criterion | Grimmett Chapter 11 route | Complete Bollobás–Riordan route |
|---|---|---|
| 1. Explicit proofs | **Red.** The lowest-crossing measurability/locality argument behind Lemma 11.73 is delegated or compressed. | **Red.** Theorem 2 is external; Lemma 6 says key leftmost-crossing facts are easy to see. |
| 2. Conventions | **Yellow.** The source critical probability and rectangle conventions must be related to the repository's `sSup` zero-set definition and boundary-free events. | **Yellow.** The paper's `p_H`, finite middle graph, and rectangle boundary conventions differ from the repository encodings. |
| 3. Logical structure | **Green.** The 11.12 → 11.11 tower and the RSW sub-tower are clear and already mirrored by declarations. | **Green.** Duality, box crossing, annuli, sharp threshold, and the two inequalities are clearly staged. |
| 4. Reader gaps | **Red.** Canonical lowest crossing, the explored region, and stopping-set locality are not fully proved. | **Red.** Lemma 6 locality and several figure-based splicings are compressed; Theorem 2 is imported. |
| 5. Mathlib/local proximity | **Yellow.** Every target dependency except the canonical-crossing RSW step is now locally available. | **Red.** Two searches found no Friedgut–Kalai/KKL sharp-threshold theorem in the project or Mathlib. |
| 6. Definition uniqueness | **Yellow.** Several rectangle/circuit encodings exist, although proved incidence and duality bridges connect them. | **Yellow.** Paper paths/cycles, the finite middle graph, and the repository's boundary-free crossings require explicit bridges. |
| 7. Constructive content | **Yellow.** Finite path selection is constructive after enumeration, but the measure layer uses classical choice. | **Yellow.** Finite combinatorics is constructive in principle; probability and selector layers are classical. |
| 8. Figure dependence | **Red.** Figures 11.21–11.27 carry significant planar intuition. | **Red.** Figures 3–9 carry extension, gluing, annulus, and renormalization steps. |
| 9. Tower structure | **Green.** Named results form a clean dependency tower. | **Green.** Named lemmas and corollaries form a clean tower. |
| Standalone verdict | **DO NOT PROCEED standalone.** Proceed only with the existing formal scaffold and an explicit locality work package. | **DO NOT PROCEED complete.** The external sharp-threshold theorem would add a large unrelated foundation. |

The Mathlib-proximity judgment for the complete Bollobás–Riordan route is grounded by two
independent repository-plus-Mathlib searches: one for `friedgut|kalai|kahn|kkl`, and one for
sharp-threshold/transitive-influence formulations. They found no usable Friedgut–Kalai theorem.
The local `influence_eq_of_permFamilyTransitive` is not a sharp-threshold theorem.

### 2.4 Segmented Bollobás–Riordan scorecard

| Criterion | Lemma 6 | Corollary 7, conditional on Lemma 6 | Theorem 8, conditional on Corollary 7 and using repo annulus replacement |
|---|---|---|---|
| 1. Explicit proofs | **Red:** the leftmost crossing and its locality are asserted. | **Green:** the recurrence and iteration are short once Lemma 6 is available. | **Yellow:** the four-crossing surrounding-cycle claim is compressed. |
| 2. Conventions | **Yellow:** “leftmost” and the explored lower region need a formal convention. | **Yellow:** `2ρn × 2n` must be translated to the repository's centered boundary-free event. | **Yellow:** source open circuits are transferred to the repository's shifted closed-barrier encoding. |
| 3. Logical structure | **Green.** | **Green.** | **Green.** |
| 4. Reader gaps | **Red:** stopping-fiber measurability is load-bearing. | **Yellow:** Figure 4 supplies a geometric incidence, but a matching local API exists. | **Yellow:** Figure 5 is replaced by already-proved circuit incidence and annulus duality. |
| 5. Mathlib/local proximity | **Red standalone:** no canonical-lowest-crossing API exists yet; the surrounding finite-path, FKG, and measure APIs do exist. | **Green:** FKG, graph isomorphisms, crossing intersections, and measure bounds are verified locally. | **Green:** circuit gluing, barrier transfer, disjoint-support independence, and the limiting argument are verified locally. |
| 6. Definition uniqueness | **Yellow:** the canonical crossing and its lower support are new public concepts. | **Yellow:** an explicit bridge to `rswRectangleCrossingEvent` is required. | **Yellow:** the source circuit is not definitionally the repository barrier, so the existing transfer theorem must be cited. |
| 7. Constructive content | **Yellow:** finite enumeration gives a selector, but the chosen canonical witness is noncomputable. | **Green:** finite algebra and monotonicity after Lemma 6. | **Yellow:** the product-measure limit is classical but already formal. |
| 8. Figure dependence | **Red:** Figure 3 is the core geometry. | **Yellow:** Figure 4 is replaceable by proved incidence lemmas. | **Red as written:** Figure 5 is essential in the paper; operationally **Yellow** after the documented repository replacement. |
| 9. Tower structure | **Green.** | **Green.** | **Green.** |
| Verdict | **NEEDS SCAFFOLDING.** This is the bounded missing formalization unit. | **PROCEED/CHECKPOINTS** after Lemma 6 and the event bridge. | **PROCEED/CHECKPOINTS** only with the explicit annulus/barrier divergence recorded. |

This re-segmentation is decisive: the complete short paper is not the short formalization route.
The useful short route is only Lemma 6 → Corollary 7 → the already-formal annulus/barrier
argument. Sections using Friedgut–Kalai and the paper's upper-bound proof are excluded.

### 2.5 Selected source policy

Use **Grimmett Chapter 11 as the primary source** for the theorem statement, theorem numbering,
and the source-to-formal dependency inventory. It aligns with the existing declarations and
already-formal upper-bound proof.

Use **Bollobás–Riordan Lemma 6, Corollary 7, and Theorem 8 as a secondary discharge route** for
the sole missing Harris/RSW input. The operational proof will use Lemma 6 and the `ρ = 3` instance
of Corollary 7, then reuse the repository's proved circuit/barrier implementation of Theorem 8.
This is a documented proof divergence, not a claim that the repository formalizes every sentence
of the short paper.

Do not formalize the complete Bollobás–Riordan paper for this goal. In particular, do not add
Friedgut–Kalai/KKL merely to reprove an upper bound already proved axiom-free by the bond-interface
and subcritical-decay stack.

## 3. Source-to-formal theorem map

| Source role | Lean declaration | Status | Important divergence |
|---|---|---|---|
| Grimmett Theorem 11.11 | `Percolation.cubicCriticalProbability_two_eq_half` | **[PROVED modulo one axiom]** | `cubicCriticalProbability` is the repository's real-valued `sSup`-based definition. |
| Grimmett Lemma 11.12 | `Percolation.theta_two_half_eq_zero` | **[PROVED modulo one axiom]** | Infinite-cluster probability is `theta 2 squareHalfDensity`. |
| Lower critical bound from critical extinction | `half_le_cubicCriticalProbability_two_of_theta_half_eq_zero` | **[PROVED]** | Repository order-theoretic bridge. |
| Upper critical bound | `cubicCriticalProbability_two_le_half` and `..._via_bond_interface` | **[PROVED]** | Uses the local interface/subcritical-decay route, not the short paper's sharp threshold. |
| Grimmett RSW input, Lemma 11.73 role | `rswThreeHalvesCrossingProbability_ge` | **[AXIOM]** | Current statement is a uniform explicit function-of-square-probability inequality. |
| Grimmett RSW gluing consequences | `rswRectangleCrossingProbability_two_ge`, `...three_ge`, `rswAnnulusOpenCircuitProbability_ge` | **[PROVED]** | Boundary-free centered events and explicit numeric bounds. |
| Critical square crossing | `one_sixteenth_le_rswSquareCrossingProbability_half` | **[PROVED]** | Constant is `1/16`, not the paper's convention-dependent `1/2`; it suffices. |
| Annular open circuit from four crossings | `rswAnnulusOpenCircuitProbability_ge_rectanglePowFour` | **[PROVED]** | Exact event-incidence implementation. |
| Critical open-circuit/closed-barrier transfer | `rswAnnulusOpenCircuitProbability_le_half_expandedBarrier` | **[PROVED]** | Uses shifted duality and enlarged annuli. |
| Independence and blocking | `iIndepSet_expandedCriticalAnnulusBarrierEvent`, `hasInfiniteOpenCluster_subset_iInter_expandedCriticalAnnulusBarrierEvent_compl` | **[PROVED]** | Replaces informal “independent annuli surround the origin.” |
| Infinite product/limit step | `theta_eq_zero_of_iIndep_barriers` | **[PROVED]** | General reusable independent-barrier theorem. |
| BR Lemma 6 | proposed canonical-crossing extension theorem below | **[PROPOSED]** | Must be adapted to boundary-free rectangle events and the `1/16` square bound. |
| BR Corollary 7, `ρ = 3` | proposed uniform `k = 3` crossing bound below | **[PROPOSED]** | Only scales used by expanded annuli are needed. |

## 4. Verified dependency graphs

### 4.1 Current target closure

The current proof has the following mathematical DAG. A star marks the one project axiom.

```text
cubicCriticalProbability_two_eq_half
├── cubicCriticalProbability_two_le_half                         [PROVED]
│   ├── cubicCriticalProbability_two_le_half_via_bond_interface [PROVED]
│   └── radiusTail_exponential_decay_of_lt_critical             [PROVED]
└── half_le_cubicCriticalProbability_two_of_theta_half_eq_zero  [PROVED]
    └── theta_two_half_eq_zero                                  [modulo *]
        ├── one_sixteenth_le_rswSquareCrossingProbability_half  [PROVED]
        ├── rswAnnulusOpenCircuitProbability_ge                 [PROVED modulo *]
        │   ├── rswRectangleCrossingProbability_two_ge          [PROVED modulo *]
        │   ├── rswRectangleCrossingProbability_three_ge        [PROVED modulo *]
        │   ├── RSW incidence/gluing inequalities               [PROVED]
        │   └── * rswThreeHalvesCrossingProbability_ge          [AXIOM]
        ├── rswAnnulusOpenCircuitProbability_le_half_expandedBarrier [PROVED]
        ├── iIndepSet_expandedCriticalAnnulusBarrierEvent       [PROVED]
        ├── hasInfiniteOpenCluster_subset_iInter_..._compl       [PROVED]
        └── theta_eq_zero_of_iIndep_barriers                    [PROVED]
```

All gluing and barrier inputs once described as axiomatic in older audit prose must be reclassified:
they are proved. `AXIOM_AUDIT.md` must be updated to name only the live RSW axiom and, after its
discharge, to record no project axiom in the target closure.

### 4.2 Shortest specialized discharge DAG

The fastest completion does not need to prove the current general Lemma 11.73-shaped axiom. It
needs only a uniform positive lower bound for a `6l × 2l` crossing at density `1/2`:

```text
finite crossing candidate enumeration + planar meet/boundary lemma
                  │
                  ▼
canonical leftmost crossing + stopping-fiber locality            [PROPOSED]
                  │
                  ▼
BR Lemma 6, adapted to boundary-free events                       [PROPOSED]
                  │
                  ▼
BR Corollary 7 at ρ = 3, using square crossing ≥ 1/16             [PROPOSED]
                  │
                  ▼
∃ c > 0, ∀ l ≥ 3, c ≤ rswRectangleCrossingProbability 1/2 3 l  [PROPOSED]
                  │
                  ├── rswAnnulusOpenCircuitProbability_ge_rectanglePowFour [PROVED]
                  ▼
uniform open-annulus probability ≥ c^4
                  │
                  ├── rswAnnulusOpenCircuitProbability_le_half_expandedBarrier [PROVED]
                  ▼
uniform shifted closed-barrier probability ≥ c^4
                  │
                  ├── independent shifted annuli/blocking                         [PROVED]
                  └── theta_eq_zero_of_iIndep_barriers                           [PROVED]
                  ▼
theta 2 squareHalfDensity = 0
                  │
                  ▼
cubicCriticalProbability 2 = 1/2
```

This route bypasses these declarations in the final target closure:

- `rswThreeHalvesCrossingProbability_ge`;
- `rswRectangleCrossingProbability_two_ge`;
- `rswRectangleCrossingProbability_three_ge`;
- the explicit `RSWNumeric` expression used by the current proof.

They may remain useful proved infrastructure, but the target must not transitively use the axiom.

## 5. Existing definitions and verified APIs by proof node

### 5.1 Critical probability and the two inequalities

- `Percolation.theta` is defined in `Percolation/Bernoulli/Basic.lean`.
- `Percolation.cubicCriticalProbability` is defined in `Percolation/Critical/Basic.lean`.
- `Percolation.squareHalfDensity` is defined in `Percolation/Planar/SquareCritical.lean`.
- `half_le_cubicCriticalProbability_two_of_theta_half_eq_zero` converts the critical extinction
  statement to `1/2 ≤ p_c`.
- `cubicCriticalProbability_two_le_half` supplies `p_c ≤ 1/2` without the RSW axiom.
- The upper route already uses the local bond-interface and
  `radiusTail_exponential_decay_of_lt_critical` APIs. It should be reused unchanged.
- `le_antisymm` closes the final equality.

No new order-theoretic critical-probability development is planned. If a proof touches the
definition, useful Mathlib APIs include `le_csSup` and `csSup_le`, but the public bridge above is
preferred because it already handles the repository conventions.

### 5.2 Rectangle and annulus events

Reuse these definitions from `Percolation/Planar/RSWEvents.lean`:

- `squareBoundaryFreeRectangleCrossingEvent`;
- `rswRectangleCrossingEvent`;
- `rswSquareCrossingEvent`;
- `rswThreeHalvesCrossingEvent`;
- `rswRectangleCrossingProbability`;
- `rswSquareCrossingProbability`;
- `rswAnnulusOpenCircuitEvent` and `rswAnnulusOpenCircuitProbability`.

Reuse `squareAnnulusBarrierEvent` and `expandedCriticalAnnulusBarrierEvent` from the annulus
modules. Do not introduce a third competing public definition of a rectangle crossing or annular
barrier. New canonical-crossing structures should carry a theorem identifying their existence
event with the existing boundary-free event.

Verified local incidence APIs include:

- `squareWalk_support_inter_of_left_right_and_bottom_top` and its generalized `..._of_le` and
  `..._of_le_int` forms;
- `rswGluingTwoIntersection_subset` and `rswGluingThreeIntersection_subset`;
- `rswCircuitGluingIntersection_subset`;
- the square-graph normalization/frame isomorphisms in `RSWIncidence.lean` and
  `RSWCircuitIncidence.lean`.

These APIs should discharge Corollary 7's Figure 4 splicing and the annular four-crossing
incidence; do not rebuild those pictures from coordinates unless an exact event bridge fails.

### 5.3 Finite paths, canonical witnesses, and parity

The lowest-crossing construction should enumerate finite, self-avoiding rectangle crossings.
Verified Mathlib APIs:

- `SimpleGraph.Walk.toPath`;
- the support and edge-set subset lemmas for `Walk.toPath`;
- finite `Fintype` instances for bounded walks/paths from
  `Mathlib/Combinatorics/SimpleGraph/Walk/Counting.lean`.

Verified local planar/combinatorial APIs:

- existing square-walk boundary/intersection lemmas in `RectangleIntersection.lean`;
- `SimpleGraph.exists_reachable_between_of_odd_degree_partition`, already used in
  `SiteCrossingInterface.lean`, for a finite odd-degree boundary argument.

The planned region proof is combinatorial. It should construct a finite face graph below two
candidate crossings and use odd-degree parity to obtain the boundary/meet crossing needed for
minimality. It must not import or postulate a discrete Jordan curve theorem.

### 5.4 FKG, support dependence, and exact probability decomposition

Reuse:

- `bernoulliBondMeasure_real_fkg` for increasing events;
- `bernoulliBondMeasure_real_fkg_of_decreasing` where complements are used;
- `bernoulliBondMeasure_real_fkg_of_dependsOn` when a finite support is explicit;
- `indep_generateFrom_coordinateEvents` for disjoint coordinate supports;
- `setBernoulli_real_eq_sum_splice` for exact conditioning on a finite set;
- the coordinate `iIndepSet` results in `FKGInfinite.lean`.

Useful Mathlib real-measure APIs include:

- `map_measureReal_apply` for graph-automorphism transport;
- `measureReal_biUnion_finset` for a disjoint finite fiber decomposition;
- `measureReal_biUnion_finset_le` if only a union bound is needed;
- `measureReal_le_one`, nonnegativity, and monotonicity of `Measure.real`.

The main new analytic obligation is not FKG itself. It is the exact event-locality theorem saying
that the fiber “the canonical crossing is `P`” depends only on the finite set of edges on or below
`P`. Once stated as `DependsOn`, the existing independence/FKG layer should apply directly.

### 5.5 Annulus independence and extinction

Reuse without reproving:

- `rswAnnulusOpenCircuitProbability_ge_rectanglePowFour`;
- `rswAnnulusOpenCircuitProbability_le_half_expandedBarrier`;
- `measurableSet_expandedCriticalAnnulusBarrierEvent`;
- `iIndepSet_expandedCriticalAnnulusBarrierEvent`;
- `hasInfiniteOpenCluster_subset_iInter_expandedCriticalAnnulusBarrierEvent_compl`;
- `theta_eq_zero_of_iIndep_barriers`.

The limit theorem is already general. Its Mathlib core uses a product bound and convergence of
powers; `tendsto_pow_atTop_nhds_zero_of_lt_one` is available if a specialized wrapper needs it.
Do not reprove Borel–Cantelli or an infinite-product theorem for this target.

## 6. Proposed declaration-level implementation

Names below are proposed and may be adjusted to local naming conventions after `/lean4:review`.
Each source-facing declaration must receive a docstring and comparator/source annotation in the
topic card. Helper definitions may remain private when no later theorem needs them.

### 6.1 Finite crossing candidates and existing-event bridge

In a new module such as `Percolation/Planar/CanonicalCrossing.lean`:

```lean
/-- A self-avoiding left-to-right crossing contained in the selected finite rectangle. -/
structure SquareRectangleCrossingPath (m n : ℕ) where
  source target : SquareVertex
  walk : squareGraph.Walk source target
  isPath : walk.IsPath
  support_subset : ...
  source_mem_left : ...
  target_mem_right : ...

noncomputable def squareRectangleCrossingPaths (m n : ℕ) :
    Finset (SquareRectangleCrossingPath m n)

def SquareRectangleCrossingPath.IsOpen
    (P : SquareRectangleCrossingPath m n) (omega : EdgeConfiguration 2) : Prop := ...

theorem mem_squareBoundaryFreeRectangleCrossingEvent_iff_exists_open_path :
    omega ∈ squareBoundaryFreeRectangleCrossingEvent ... ↔
      ∃ P ∈ squareRectangleCrossingPaths m n, P.IsOpen omega
```

Required facts, in order:

1. every walk witness can be converted with `Walk.toPath` without leaving the rectangle;
2. the candidate set is finite and contains every converted witness;
3. openness is an increasing event depending only on `P.path.edges`;
4. the existential event is exactly the existing boundary-free crossing event, including small
   and degenerate dimensions used by tests.

Do not define canonical order before this bridge passes. It is the guard against silently proving
a theorem about a new, narrower crossing convention.

### 6.2 Stopped dual exploration and its finite fibers

Use a stopped dual flood-fill rather than ordering all primal crossing candidates.  In the
dual configuration, an open dual edge crosses a closed primal edge.  Flood-fill a finite framed
dual rectangle from its left exterior faces.  If `R` is the set of reached faces, every edge on
the edge boundary of `R` is dual-closed and therefore crosses a primal-open edge.  The resolved
boundary of `R` is the canonical primal interface.

The first implementation unit is:

```lean
abbrev BRLeftmostDualVertex (n : ℕ) := ...

noncomputable def brLeftmostDualGraph (n : ℕ) :
    SimpleGraph (BRLeftmostDualVertex n) := ...

noncomputable def brLeftmostDualSources (n : ℕ) :
    Finset (BRLeftmostDualVertex n) := ...

def brClosedDualExplorationConfiguration
    (n : ℕ) (omega : EdgeConfiguration 2) :
    (brLeftmostDualGraph n).edgeSet → Prop := ...

noncomputable def brLeftReachableFaces
    (n : ℕ) (omega : EdgeConfiguration 2) :
    Finset (BRLeftmostDualVertex n) := ...

def brReachableFaceFiber (n : ℕ)
    (R : Finset (BRLeftmostDualVertex n)) : Set (EdgeConfiguration 2) :=
  {omega | brLeftReachableFaces n omega = R}
```

Reuse `finiteGraphReachableVertices` and
`dependsOn_finiteGraphReachableVertices_fiber`.  Define
`brReachableFaceFiberSupport n R` as all dual graph edges incident to a vertex in `R`, pulled back
to primal edges by `squareEdgeDualCrossingEquiv`.  Prove:

```lean
theorem dependsOn_brReachableFaceFiber (n : ℕ) (R : ...) :
    DependsOn (brReachableFaceFiberSupport n R) (brReachableFaceFiber n R)
```

Then prove the finite fibers are measurable, pairwise disjoint, and partition the vertical square
crossing event after filtering to the reachable sets whose resolved boundary crosses the square.
The partition proof must be an equality of the repository's existing event, not a new convention.

### 6.3 Resolved boundary and genuinely fresh extension edges

An ordinary cell-interface graph has degree four at a checkerboard cell and forgets the planar
pairing.  `ResolvedRectangleInterface.lean` splits such a cell by its reachable corner.  Its local
checkpoint is: for every incident boundary edge `b`, there is exactly one distinct incident edge
`c` with the same split tag.  Use this to build the finite resolved interface graph, prove its
interior vertices have degree two, classify its boundary degree-one vertices, and extract the
unique component selected by the stopped exploration.  Expose:

```lean
noncomputable def brLeftmostBoundaryPath
    (n : ℕ) (R : Finset (BRLeftmostDualVertex n)) :
    Option (SquareBoundaryFreeCrossingPath ... ) := ...

theorem brLeftmostBoundaryPath_isOpen_of_mem_fiber ...
theorem brSquareVerticalCrossingEvent_eq_biUnion_reachableFaceFiber ...
```

The local pairing and the global endpoint argument replace both an informal Jordan-curve appeal
and the earlier proposed meet/lexicographic selector.  Keep the finite candidate/event bridge in
`CanonicalCrossing.lean` as the semantic guard for the extracted path.

For the Lemma 6 extension, reflect `R` across the horizontal midline and let `B_R` be the union of
the two stopped regions.  Define `brRightOfBarrierEdges m n R` using only primal edges whose
crossed dual edge has **both** incident faces outside `B_R`, further restricted to the appropriate
right component of the large rectangle.  Prove the exact disjointness statement

```lean
Disjoint (brReachableFaceFiberSupport n R) (brRightOfBarrierEdges m n R)
```

and define the lower extension event with `connectionEventIn` on precisely that edge finset.
Trim a horizontal crossing at its first contact with the stopped interface: every random edge in
the prefix must lie in `brRightOfBarrierEdges`; concatenate the final already-known-open interface
edge only after the fresh prefix.

This distinction is load-bearing.  Dual boundary edges incident to `R` are exposed by the fiber
and their crossed primal edges are fixed open.  They may be used deterministically to splice the
selected interface, but they are not fresh coordinates.  An event stated merely as “connect to
the selected path from the right” is too large and cannot be declared independent of the fiber.
The proof must use `dependsOn_connectionEventIn` for the constrained prefix and
`setBernoulli_real_inter_eq_mul_of_dependsOnCoordinates` for exact factorization.

### 6.4 Adapted Bollobás–Riordan Lemma 6

In a separate module such as `Percolation/Planar/BRCrossingExtension.lean`, state the source lemma
first in event/probability notation close enough to audit. A proposed public form is:

```lean
/-- Bollobás–Riordan (2006), Lemma 6, adapted to the repository's
boundary-free square-lattice rectangle events. -/
theorem br_crossing_extension_probability
    (p : I) (m n : ℕ) (hn : 1 ≤ n) (hnm : n ≤ m) :
    rswRectangleCrossingProbability p ... *
        verticalRectangleCrossingProbability p ... / 2 ≤
      rswRectangleCrossingProbability p ... := by
  ...
```

The final parameters must be copied from the PDF's exact rectangles, not guessed from this
schematic type. Before proving it, add a diagram-free coordinate table listing each source
rectangle, its Lean center/half-widths, and its transformed event.

Proof structure:

1. partition the relevant vertical-crossing event into the finite, pairwise-disjoint stopped-dual
   reachable-set fibers `F_R`;
2. for each `R`, form the reflected barrier and the lower outside-extension event `Y_R`;
3. trim each horizontal crossing at first contact with the barrier and use reflection to prove
   `mu(H) / 2 <= mu(Y_R)`;
4. prove the support of `Y_R` is disjoint from the fiber support and factor
   `mu(F_R ∩ Y_R) = mu(F_R) * mu(Y_R)` exactly;
5. splice the fresh prefix with the exposed-open interface boundary and prove
   `F_R ∩ Y_R` is contained in the larger crossing event;
6. sum with `mul_measureReal_le_biUnion_inter_of_partition`, avoiding conditional probabilities
   and division by possibly-zero fiber masses;
7. transport normalized/translated events with graph isomorphisms and `map_measureReal_apply`.

Checkpoint tests must verify the inequality has the correct direction and the factor `1/2`, and
that no rectangle dimension underflows in `Nat` subtraction.

### 6.5 Corollary 7 specialized to aspect ratio three

In `Percolation/Planar/BRUniformCrossing.lean`, formalize only the recurrence and the instance the
target needs. The paper's recurrence should be transcribed as a power-of-two denominator (the PDF
typography for `2^5` must not be misread as decimal `25`). Prove a checked recurrence of the form:

```lean
theorem br_crossing_recurrence ... :
    h (2 * m - n) (2 * n) ≥ h (2 * m) (2 * n) ^ 2 / 2 ^ 5 := by
  ...
```

Then expose the target-facing theorem:

```lean
/-- BR Corollary 7 at `ρ = 3`, adapted to the repository events. -/
theorem exists_pos_le_rswRectangleCrossingProbability_half_three :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧
      ∀ l : ℕ, 3 ≤ l →
        c ≤ rswRectangleCrossingProbability squareHalfDensity 3 l := by
  ...
```

The proof starts from
`one_sixteenth_le_rswSquareCrossingProbability_half`, not an unproved `1/2` square bound. A worse
explicit constant is harmless; strict positivity and uniformity are the only downstream needs.
If the recurrence naturally covers only dyadic or padded rectangles, use event monotonicity and
integer rounding to cover all `l ≥ 3`. Every rounding inequality should be a named arithmetic
lemma checked by `omega`, with the geometric inclusion proved separately.

The actual target evaluates this theorem only at `expandedCriticalAnnulusScale k`, for which the
repository proves `16 ≤ l`. If covering every `l ≥ 3` creates irrelevant boundary work, use the
narrower but still source-auditable theorem:

```lean
theorem exists_pos_le_rswRectangleCrossingProbability_half_three_expanded :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧
      ∀ k : ℕ,
        c ≤ rswRectangleCrossingProbability squareHalfDensity 3
          (expandedCriticalAnnulusScale k)
```

This specialization is acceptable only if correspondence records that it is a target-specific
corollary, not a complete formalization of BR Corollary 7.

### 6.6 Specialized annulus-to-extinction assembly

In a small integration module, preferably `Percolation/Planar/SquareThresholdBR.lean`, prove:

```lean
theorem exists_uniform_expandedCriticalAnnulusBarrier_probability_half :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      ∀ k : ℕ,
        δ ≤ (bernoulliBondMeasure 2 squareHalfDensity).real
          (expandedCriticalAnnulusBarrierEvent k) := by
  ...
```

Take `δ = c ^ 4`. For each expanded scale:

1. apply `rswAnnulusOpenCircuitProbability_ge_rectanglePowFour` to the `k = 3` crossing;
2. raise the uniform crossing lower bound to the fourth power using nonnegativity;
3. apply `rswAnnulusOpenCircuitProbability_le_half_expandedBarrier`;
4. discharge scale hypotheses from `expandedCriticalAnnulusScale_ge_sixteen`;
5. prove `0 < c^4` and `c^4 ≤ 1` by elementary ordered-ring lemmas.

Then add an assumption-free replacement:

```lean
theorem theta_two_half_eq_zero_via_br :
    theta 2 squareHalfDensity = 0 := by
  ...
```

using `theta_eq_zero_of_iIndep_barriers`, the existing measurability/independence theorem, and the
existing blocking inclusion. Finally either change the body of the existing
`theta_two_half_eq_zero` to this proof or make it a wrapper around the new declaration. The public
`cubicCriticalProbability_two_eq_half` should remain source-named and use `le_antisymm` exactly as
it does now.

An even shorter direct proof could form a barrier from four shifted-dual crossings. Do not choose
that variant initially: the circuit incidence and annulus transfer are already proved and reviewed.
Use the direct-barrier variant only if the BR Corollary 7 event cannot be bridged to the existing
`rswRectangleCrossingProbability` without changing boundary conventions.

## 7. Fallback: full formalization of Grimmett Lemma 11.73

If the specialized BR recurrence cannot be made to match the existing boundary-free event, retain
the canonical-crossing scaffold and discharge the current axiom directly. This is the larger but
semantically exact fallback.

The endpoint `l = 0` must be separated first. Existing exploration showed
`rswThreeHalvesCrossingEvent 0 = Set.univ`; the production proof should prove this explicitly rather
than allowing arithmetic side conditions to hide the case.

For `l ≥ 1`, implement:

1. enumerate finite self-avoiding square-crossing candidates using `Walk.toPath`;
2. define the finite face region below a path and its lower support;
3. prove the meet/boundary crossing lemma with the finite odd-degree parity API;
4. define the canonical lowest crossing and prove uniqueness after path normalization;
5. partition the crossing event into its canonical fibers;
6. prove each fiber `DependsOn` the lower support;
7. define the extension event with disjoint upper support and apply coordinate independence;
8. sum the disjoint fibers and splice paths with the rectangle-intersection theorem;
9. apply the square-root trick and horizontal/vertical/reflection symmetry;
10. derive the exact existing statement
   `rswThreeHalvesCrossingProbability_ge`, including its explicit cubic lower bound.

The proposed work product is a theorem replacing the axiom with the identical name and exact type.
Run a type-only Comparator between the old declaration signature and the new theorem before
removing the axiom. Then rerun `#print axioms` for every downstream theorem.

The fallback must follow `docs/theorem-11.11/PICTORIAL_PROOF_EXPANSION.md`. When a picture suggests
a path intersection, boundary, or separation statement, first state a finite graph lemma with all
coordinate bounds. No discrete Jordan curve theorem may be introduced unless an independent
source/API audit proves the elementary parity route impossible.

## 8. Implementation order and checkpoints

1. **Freeze baseline.** Record commit, dirty diff/tree hash, Lean, Mathlib, source hashes, and run
   `lake build`, `rg` checks for `sorry`/`axiom`, and the current `#print axioms` audit.
2. **Preserve the proved upper branch.** Add application tests for
   `cubicCriticalProbability_two_le_half`; do not refactor it while RSW work is active.
3. **Crossing candidate bridge.** Implement finite path candidates and prove exact equivalence to
   `squareBoundaryFreeRectangleCrossingEvent`.
4. **Stopped dual fibers.** Instantiate the generic finite-reachability fiber API on the framed
   dual rectangle and prove the pulled-back primal support theorem.
5. **Resolved boundary.** Build the split-cell interface graph, prove the degree/endpoints facts,
   and extract the open boundary crossing. This is the first independent geometric-review
   checkpoint.
6. **Fresh extension support.** Define the symmetric barrier, both-outside edge set, and first-hit
   prefix; prove support disjointness and the exact fiber/extension factorization.
7. **BR Lemma 6.** Prove the adapted extension inequality and test symmetry/factor/dimensions.
8. **BR Corollary 7 at `ρ = 3`.** Prove a uniform positive constant using the existing `1/16`
   square lower bound.
9. **Specialized annulus assembly.** Convert the long-crossing lower bound to a uniform barrier
   lower bound with the two proved annulus theorems.
10. **Critical extinction and exact threshold.** Replace the axiom-dependent critical proof; run
   both `#print axioms` commands immediately.
11. **Fallback decision.** Only if step 7 or 8 fails for an essential event mismatch, formalize the
    full Lemma 11.73 statement using the same selector infrastructure.
12. **Review artifacts.** Run all cases, counterexamples, Comparator, axiom, correspondence, and
    independent-review gates below.
13. **Repository records.** Update `docs/HISTORY.md`, `docs/VERIFICATION.md`, `AXIOM_AUDIT.md`, and
    the relevant `audit/topics/` comparator card only after the frozen review passes.

At every checkpoint run the edited module directly with `lake env lean <file>`, then the relevant
module build, then full `lake build`. Use Lean LSP when available; if it is unavailable, record
that fact and do not claim interactive-goal evidence.

## 9. Parallel work packages and ownership

The work is suitable for subagents only with disjoint file ownership. The integration agent owns
imports, theorem renames, and final edits to `SquareThresholdExact.lean`; no two agents edit the
same production file concurrently.

| Package | Inputs | Owned output | Dependency | Required handoff evidence |
|---|---|---|---|---|
| WP0: source/freeze | both PDFs, integration branch | review manifest and correspondence draft only | none | page-level source inventory, hashes, exact environment |
| WP1: finite candidates | existing RSW event definitions, `Walk.toPath` | `CanonicalCrossing.lean`, candidate/event bridge section | WP0 | direct Lean build plus boundary cases |
| WP2: generic stopped fibers | finite graph/reachability and product-measure APIs | `FiniteReachability.lean`, `FiniteFiberIndependence.lean` | WP0 | direct build, support sufficiency review, no conditional division |
| WP3: dual exploration | WP2, square duality APIs | `BRDualExploration.lean` | WP2 | pulled-back support theorem and finite disjoint partition |
| WP4: resolved boundary | WP1, WP3, cell parity/interface APIs | `ResolvedRectangleInterface.lean`, `BRResolvedBoundary.lean` | WP1, WP3 | unique local partner, degree/endpoints proof, independent pictorial review |
| WP5: fresh extension | WP3–WP4, `connectionEventIn` locality | `BRFreshExtension.lean` | WP4 | both-outside support and first-hit-prefix proof |
| WP6: BR Lemma 6 | WP5, independence/isomorphism APIs | `BRCrossingExtension.lean` | WP5 | source coordinate table, exact factor and inequality test |
| WP7: BR Corollary 7 | WP6, square `1/16` bound | `BRUniformCrossing.lean` | WP6 | recurrence algebra and `ρ=3` theorem |
| WP8: target assembly | WP7, proved annulus/barrier APIs | `SquareThresholdBR.lean` | WP7 | axiom-free theta theorem |
| WP9: fallback h73 | WP4–WP6 | a replacement theorem matching `External.lean` | only if WP7 is blocked | exact type comparison and `l=0` test |
| WP10: review suite | frozen production commit | `audit/reviews/...` only | WP8 or WP9 | all mandatory protocol artifacts |
| WP11: independent review | frozen source and commit | read-only first-pass report | WP10 manifest | falsification attempts and verdict, unedited |

WP1 and WP2 can run in parallel after WP0. WP3 through WP8 are
sequential because each statement depends on the exact previous event encoding. WP10 may prepare
templates early but must run against the frozen final commit. The main integration agent should
cherry-pick or copy only after inspecting each handoff and should rerun builds rather than trusting
agent-reported success.

## 10. Mandatory tests and adversarial cases

### 10.1 Application cases

Create three to seven meaningful cases for each new major public theorem. At minimum:

1. apply the final theorem directly to prove
   `cubicCriticalProbability 2 = (1 : ℝ) / 2` with no independent proof;
2. separately apply the proved upper bound and the new theta/lower-bound branch;
3. apply `theta_two_half_eq_zero` at the exact `squareHalfDensity` definition;
4. test the smallest nontrivial rectangle admitted by BR Lemma 6;
5. test the `l = 0` RSW event if the full Lemma 11.73 fallback is used;
6. test an expanded annulus at `k = 0`, including the scale arithmetic;
7. test the event bridge on a small finite rectangle with an independent finite oracle where
   feasible.

Application tests must visibly invoke the reviewed declaration, preferably with `exact` and named
arguments. Narrow `simpa only` is acceptable; unrestricted automation that could prove the case
without the target is not.

### 10.2 Counterexamples and anti-targets

The adversarial suite must try to refute or reject at least:

- `cubicCriticalProbability 2 < 1 / 2` and `1 / 2 < cubicCriticalProbability 2`;
- `0 < theta 2 squareHalfDensity`;
- a fake uniform crossing statement that includes an invalid degenerate dimension;
- a version of BR Lemma 6 with the inequality reversed or the `1/2` factor omitted;
- a locality claim using only the path edges rather than the entire explored lower support;
- a bridge equating boundary-free crossings to a stricter fixed-corner event;
- an annulus statement with overlapping “independent” supports;
- accidental `Nat` underflow in `2 * m - n` outside the source hypothesis.

For tiny rectangles, enumerate configurations when practical and independently check the event
normalization. A failed search is evidence only when the search domain, command, and bounds are
recorded. Each abstract test must include a satisfiability witness; vacuous proofs from inconsistent
hypotheses do not count.

## 11. Comparator and review gates

Follow `AUTOMATED_REVIEW.md` in full. The following details are mandatory for this theorem.

### 11.1 Frozen manifest and inventory

Create `audit/reviews/theorem-11.11/<date>-<short-commit>/MANIFEST.md` containing:

- review id and exact scope;
- source ids, editions, pages/sections, and PDF hashes;
- git commit plus dirty-tree hash if unavoidable;
- Lean, Mathlib, and Comparator revisions;
- internal/adversarial review mode and timestamps;
- honest time/token telemetry, with unavailable values marked `not measured`.

The correspondence row for Theorem 11.11 must include the exact Lean type, all important
dependencies, the critical-probability and event-encoding divergences, application/adversarial
tests, Comparator result, transitive axioms, and independent verdict. Supporting lemmas get rows
when the completion claim names them as formalized source results.

### 11.2 One-theorem Comparator challenge

The challenge file must be intentionally simple:

```lean
import Percolation

namespace ComparatorChallenge

/-- Grimmett, Percolation (2nd ed.), Theorem 11.11. -/
theorem grimmett_theorem_11_11 :
    Percolation.cubicCriticalProbability 2 = 1 / 2 := by
  sorry

end ComparatorChallenge
```

The trusted challenge is authored from the source before looking at the production wrapper, then
hashed/frozen. `Solution.lean` must prove exactly this statement by applying
`Percolation.cubicCriticalProbability_two_eq_half` and may not contain `sorry` or `admit`.
Record the isolated `lakefile.toml`, pinned Comparator revision, exact command, trust mode, exit
status, and stable log path. On macOS run the internal Comparator gate; the final adversarial gate
must run in the required Linux/sandbox environment. Comparator success establishes formal
statement equivalence, not source fidelity; the correspondence review remains mandatory.

### 11.3 Axiom and sorry gate

`AxiomAudit.lean` must contain at least:

```lean
#print axioms Percolation.theta_two_half_eq_zero
#print axioms Percolation.cubicCriticalProbability_two_eq_half
```

The accepted final result is exactly the project's permitted standard set, expected here to be
`propext`, `Classical.choice`, and `Quot.sound`. Any occurrence of
`Percolation.rswThreeHalvesCrossingProbability_ge` fails completion, even if that axiom remains in
an unused compatibility module. Also run transitive searches for `axiom`, `sorry`, `admit`, and
unsafe declarations in the reviewed closure. A textual search supplements but does not replace
`#print axioms`.

### 11.4 Independent read-only review

Give a fresh reviewer the frozen source pages, exact Lean types, build commands, and a prompt to
falsify—not confirm—the claimed correspondence. The first pass is read-only and must check:

- both inequality directions and the normalization of `1 / 2`;
- the definition of `cubicCriticalProbability` and endpoint conventions;
- the event bridge used in BR Lemma 6/Corollary 7;
- whether the canonical-fiber locality theorem really includes all deciding edges;
- whether annulus supports are disjoint and every infinite path is blocked by a barrier;
- exact transitive axioms and absence of hidden source assumptions;
- all documented proof divergences from Grimmett and Bollobás–Riordan.

Store the unedited first-pass report and the producer's disposition in `independent-review.md`.
If a defect is repaired, freeze a new revision and rerun every affected downstream gate.

### 11.5 Gate summary

Completion requires all of the following:

- full `lake build` passes on the frozen revision;
- every production/review solution file is sorry-free;
- the exact final and theta declarations have only permitted standard axioms;
- all source inventory rows have a disposition;
- application, boundary, finite-oracle, and adversarial cases pass;
- the one-theorem Comparator passes in the required modes;
- the independent review verdict is accepted or every objection is repaired and re-reviewed;
- `docs/HISTORY.md`, `docs/VERIFICATION.md`, `AXIOM_AUDIT.md`, and the comparator topic card agree
  with the mechanical evidence;
- the PR summary lists exact commands and does not call the result assumption-free before these
  gates pass.

## 12. Definition of done

The shortest successful endpoint is:

1. the adapted BR Lemma 6 canonical-crossing locality argument is formal;
2. BR Corollary 7 supplies a uniform positive `k = 3` rectangle-crossing constant at `p = 1/2`;
3. existing annulus, duality, independence, and barrier theorems give
   `theta 2 squareHalfDensity = 0`;
4. the existing upper bound and critical-probability bridge give
   `cubicCriticalProbability 2 = 1 / 2`;
5. `#print axioms` shows no project axiom in either theorem;
6. the one-theorem Comparator and the independent review pass.

If the specialized source/event bridge fails, the fallback endpoint is the exact same final state
after proving the full existing `rswThreeHalvesCrossingProbability_ge` statement. Either endpoint
completely formalizes Grimmett Theorem 11.11; neither endpoint is complete while the current RSW
axiom remains in the final theorem's transitive closure.
