# HISTORY — percolation

Dated milestones and anti-library notes.

1. **Repo bootstrapped (2026-06-28).** Created `random-fields/percolation` as a Lean 4 /
   Mathlib v4.30.0 project for percolation and random-cluster autoformalization. Added the
   Grimmett source corpus, `lean4-skills` agent contract, comparator/audit docs, a source-ordered
   seed plan, and compile-light Lean scaffolding for core configurations, Bernoulli percolation,
   critical parameters, planar duality, and random-cluster parameters.

2. **Grimmett Theorem 1.10 interface (2026-06-28).** Added a Mathlib-native cubic lattice graph,
   fixed-edge Bernoulli measure, the origin percolation interface, `cubicCriticalProbability`, and
   `cubicConnectiveConstant`. The later repair records the primary event as infinitude of
   Grimmett's open cluster `C_0(ω)` and uses arbitrarily long open self-avoiding walks only through
   a proved equivalence. Proved the Theorem 1.10 and Equation (1.12) reductions from
   `GrimmettTheorem110Inputs`; the connective-constant and Peierls proof obligations are explicit
   and not axiomatized.

3. **Finite `σ(n)` counting model (2026-06-28).** Replaced the preliminary `Nat.card` graph-walk
   count with a finite signed-direction-word model for self-avoiding walks. Proved adjacency of
   signed coordinate steps, prefix self-avoidance, the ambient bound
   `selfAvoidingWalkCount_le_directionWords`, and the split bound
   `selfAvoidingWalkCount_le_mul_directionWords`.

4. **Self-avoiding-walk submultiplicativity (2026-06-28).** Proved the suffix-translation lemma
   for direction words and discharged Grimmett's `σ(m+n) ≤ σ(m)σ(n)` counting ingredient as
   `selfAvoidingWalkCount_submultiplicative`. Removed this item from the conditional
   `GrimmettTheorem110Inputs` package.

5. **Connective-constant upper bound (2026-06-28).** Proved
   `cubicConnectiveConstant_le_two_mul`, the direct consequence `λ(d) ≤ 2d` of the ambient
   direction-word bound `σ(n) ≤ (2d)^n`.

6. **Connective-constant positivity (2026-06-28).** Constructed straight positive-coordinate
   self-avoiding walks of every length, proved `one_le_selfAvoidingWalkCount`, and discharged
   `one_le_cubicConnectiveConstant` / `cubicConnectiveConstant_pos`. Removed connective positivity
   from `GrimmettTheorem110Inputs`.

7. **Finite Bernoulli cylinder probabilities (2026-06-28).** Proved the `setBernoulli` finite
   cylinder calculations used in Grimmett's Theorem 1.10 proof: fixed finite open edge sets have
   mass `p^n`, fixed finite closed edge sets have mass `(1-p)^n`, and an open trail of length
   `n` has probability `p^n`. Added `walkEdgeFinset` to connect Mathlib graph walks to cubic
   edge configurations.

8. **Finite SAW union bound (2026-06-28).** Added the signed-step realization
   `selfAvoidingWalkWalk`, proved its represented graph walk is a Mathlib path, proved the
   one-word event probability `bernoulliBondMeasure_real_selfAvoidingWalkIsOpen`, and discharged
   the finite union estimate `bernoulliBondMeasure_real_existsOpenSelfAvoidingWalk_le`. Added
   `cubicGraph_adj_iff_exists_stepFrom` as the inverse lattice-adjacency bridge needed for the
   remaining arbitrary-path-to-counted-word direction.

9. **Exact graph-path counting bound (2026-06-28).** Discharged the arbitrary-path-to-signed-word
   direction for exact lengths via `exists_cubicWalkFrom_copy_eq` and
   `hasOpenPathOfLengthExactly_imp_existsOpenSelfAvoidingWalk`. Proved
   `bernoulliBondMeasure_real_hasOpenPathOfLengthExactly_le`, giving the finite Grimmett bound
   `P(∃ open self-avoiding graph path of length n) ≤ σ(n)p^n`.

10. **Length-at-least path tail bound (2026-06-28).** Proved that openness passes to initial
    segments and that the length-at-least and exact-length open path events are equivalent via
    `hasOpenPathOfLengthAtLeast_iff_hasOpenPathOfLengthExactly`. Discharged
    `bernoulliBondMeasure_real_hasOpenPathOfLengthAtLeast_le` and the finite `θ` estimate
    `theta_le_selfAvoidingWalkCount_mul_pow`, plus the analytic bridge
    `theta_eq_zero_of_tendsto_selfAvoidingWalkCount_mul_pow` and the eventual-exponential
    criterion `theta_eq_zero_of_eventually_selfAvoidingWalkCount_le_pow`.

11. **Connective-constant lower bound (2026-06-28).** Extracted an eventual exponential bound
    from the `sInf` definition of `cubicConnectiveConstant` to prove
    `theta_eq_zero_of_mul_cubicConnectiveConstant_lt_one`, then formalized the supremum argument
    as `connectiveConstant_inv_le_cubicCriticalProbability`. Removed the path-counting lower
    bound from `GrimmettTheorem110Inputs`.

12. **Dimension monotonicity for Theorem 1.10 (2026-06-28).** Added the coordinate embedding
    `cubicEmbed`, the induced edge embedding, and configuration pullback. Proved Bernoulli product
    projection along embeddings, measurability of finite open-path and infinite-cluster events,
    `theta_le_theta_of_le_dimension`, and the critical antitonicity theorem
    `cubicCriticalProbability_antitone_dimension`. Removed dimension monotonicity from
    `GrimmettTheorem110Inputs`; only the planar Peierls upper bound remains conditional.

13. **Square-lattice dual crossing cylinders (2026-06-28).** Added production square-lattice
    aliases, positive-edge normal forms, the primal/dual crossing equivalence
    `squareEdgeDualCrossingEquiv`, and the dual configuration
    `dualSquareConfiguration` in which a dual edge is open exactly when the crossed primal edge is
    closed. Proved the finite dual-open cylinder probability
    `bernoulliBondMeasure_real_dualSquareConfiguration_openOn_finset`, then packaged it for fixed
    shifted-dual trails and circuits as `bernoulliBondMeasure_real_dualWalkIsOpen` and
    `bernoulliBondMeasure_real_dualCircuitIsOpen`.

14. **Finite Peierls circuit union bound (2026-06-28).** Added the bundled `DualCircuit` type and
    proved finite-family union bounds
    `bernoulliBondMeasure_real_existsOpenDualCircuit_le`,
    `bernoulliBondMeasure_real_existsOpenDualCircuit_of_length_le`, and
    `bernoulliBondMeasure_real_existsOpenDualCircuit_of_length_le_of_card_le`. These theorems
    isolate the probabilistic half of Grimmett's Peierls estimate. Added the encoding corollary
    `bernoulliBondMeasure_real_existsOpenDualCircuit_of_encoding_le`, whose remaining input is the
    geometric injection behind `ρ(n) ≤ n * σ(n - 1)`.

15. **Peierls circuit-tail convergence (2026-06-28).** Proved the analytic convergence and
    summability step for Grimmett's closed-dual-circuit estimate:
    `tendsto_succ_mul_selfAvoidingWalkCount_mul_pow_succ_of_eventually_le_pow`,
    `tendsto_peierlsCircuitBound_of_eventually_selfAvoidingWalkCount_le_pow`, and
    `tendsto_peierlsCircuitBound_of_mul_cubicConnectiveConstant_lt_one`, plus the summability
    counterparts `summable_peierlsCircuitBound_of_eventually_selfAvoidingWalkCount_le_pow` and
    `summable_peierlsCircuitBound_of_mul_cubicConnectiveConstant_lt_one`. In particular, if
    `q * λ(d) < 1`, then the Peierls majorant `n * σ(n - 1) * q^n` is summable.

16. **Peierls finite windows and tail sums (2026-06-28).** Proved
    `bernoulliBondMeasure_real_existsOpenDualCircuit_window_of_encoding_le`, the finite-window
    version of Grimmett's `ρ(n) ≤ n * σ(n - 1)` Peierls union estimate, conditional only on the
    lengthwise circuit encodings. Proved the countable-tail bound
    `bernoulliBondMeasure_real_existsOpenDualCircuit_tail_of_encoding_le`, which passes from
    finite windows to the event that some encoded circuit of length at least `N` is open under the
    summability hypothesis. Added `tendsto_tsum_nat_add_zero_of_summable` and the specialized
    theorem `tendsto_peierlsCircuitTail_tsum_of_mul_cubicConnectiveConstant_lt_one`, showing that
    the sum of the closed-circuit majorants over all lengths at least `N` tends to zero whenever
    `q * λ(d) < 1`.

17. **Encoded Peierls tail-to-zero bridge (2026-06-28).** Added
    `Percolation.Planar.Peierls`, importing both the planar dual-circuit estimates and the
    critical connective-constant tail theorem. Proved
    `tendsto_bernoulliBondMeasure_real_encodedOpenDualCircuitTail`, which says that encoded
    closed-dual-circuit tails have probability tending to zero when `(1-p) * λ(2) < 1`, and
    `bernoulliBondMeasure_real_eq_zero_of_subset_encodedOpenDualCircuitTails`, the abstract
    zero-probability criterion that the future planar separation lemma should feed. Also proved
    `bernoulliBondMeasure_real_inter_compl_pos_of_indepSet`, the probability algebra behind
    Grimmett's `G_m ∧ ¬F_m` step: an independent positive-probability finite event survives
    outside any event of probability strictly less than one.

18. **Named Peierls tail events (2026-06-28).** Promoted the anonymous encoded
    closed-dual-circuit windows and tails to named events
    `encodedOpenDualCircuitWindow` and `encodedOpenDualCircuitTail`. Proved their membership,
    window-to-tail containment, tail antitonicity, and measurability via the finite dual-cylinder
    measurability lemmas
    `measurableSet_dualSquareConfiguration_openOn_finset`,
    `measurableSet_dualWalkIsOpen`, and `DualCircuit.measurableSet_isOpen`. Added named-event
    wrappers for the finite-window bound, countable-tail bound, tail convergence, and
    zero-probability criterion so the forthcoming geometric separation and `F_m`/`G_m` lemmas can
    refer to Grimmett's Peierls tail directly.

19. **Peierls `F_m`/`G_m` probability bridge (2026-06-28).** Added named finite open/closed edge
    events `openEdgeSetEvent` and `closedEdgeSetEvent`, with measurability, exact Bernoulli
    probabilities, and positivity of `openEdgeSetEvent` when `p > 0`. Proved
    `eventually_bernoulliBondMeasure_real_encodedOpenDualCircuitTail_lt_one` and
    `exists_bernoulliBondMeasure_real_encodedOpenDualCircuitTail_lt_one`, extracting the
    `P(F_m) < 1` step from Peierls tail convergence. Proved
    `unitInterval_pos_of_one_sub_mul_cubicConnectiveConstant_lt_one`, so `p > 0` follows from the
    same Peierls hypothesis `(1-p)λ(2) < 1`. Combined these with the existing independence algebra
    in
    `exists_bernoulliBondMeasure_real_openEdgeSetEvent_inter_compl_encodedOpenDualCircuitTail_pos`,
    and the wrapper
    `exists_bernoulliBondMeasure_real_openEdgeSetEvent_inter_compl_encodedOpenDualCircuitTail_pos_of_mul_lt_one`,
    abstract versions of Grimmett's `P(G_m ∩ F_mᶜ) > 0` argument, conditional on the geometric
    independence input still to be proved.

20. **Source-shaped planar Peierls upper-bound reduction (2026-06-28).** Added
    `PlanarPeierlsGeometry`, a structured package of the remaining concrete geometric ingredients:
    length-indexed closed dual circuits, Grimmett's `ρ(n) ≤ n * σ(n - 1)` encoding, finite open
    events `G_m`, independence from the encoded tail `F_m`, and the implication
    `G_m ∩ F_mᶜ ⊆ {0 ↔ ∞}`. Proved
    `PlanarPeierlsGeometry.theta_pos_of_one_sub_mul_lt_one`, showing positive percolation
    probability whenever `(1-p)λ(2)<1`; then proved
    `PlanarPeierlsGeometry.cubicCriticalProbability_le_one_sub_inv`, deriving
    `p_c(2) ≤ 1 - 1/λ(2)` from those source-shaped inputs. Added public corollaries
    `cubicCriticalProbability_two_bounds_of_planarPeierlsGeometry` and
    `cubicCriticalProbability_pos_lt_one_of_planarPeierlsGeometry`, so the final Theorem 1.10
    reductions no longer need to assume the planar upper bound directly when a
    `PlanarPeierlsGeometry` instance is available.

21. **Finite `G_m`/closed-cylinder independence (2026-06-28).** Generalized the Bernoulli
    finite-cylinder calculation to arbitrary finite coordinate assignments as
    `setBernoulli_real_eqOn_finset_univ`, then proved the mixed open/closed cylinder formula
    `setBernoulli_real_open_closed_on_finset_univ` and its cubic-lattice specialization
    `bernoulliBondMeasure_real_openEdgeSetEvent_inter_closedEdgeSetEvent`. Proved finite
    independence of disjoint open and closed edge cylinders as
    `bernoulliBondMeasure_indepSet_openEdgeSetEvent_closedEdgeSetEvent`. Transported this through
    the square-lattice crossing bijection to finite shifted-dual edge sets, walks, and circuits via
    `bernoulliBondMeasure_indepSet_openEdgeSetEvent_dualSquareConfiguration_openOn_finset`,
    `bernoulliBondMeasure_indepSet_openEdgeSetEvent_dualWalkIsOpen`, and
    `bernoulliBondMeasure_indepSet_openEdgeSetEvent_dualCircuitIsOpen`, advancing the finite
    support independence part of Grimmett's `G_m`/`F_m` Peierls step.

22. **Finite-window to tail independence bridge (2026-06-28).** Proved that encoded Peierls
    windows increase to the encoded closed-dual-circuit tail via
    `encodedOpenDualCircuitWindow_monotone` and
    `iUnion_encodedOpenDualCircuitWindow_eq_tail`. Added the measure-continuity lemma
    `indepSet_iUnion_of_monotone`, then specialized it as
    `indepSet_openEdgeSetEvent_encodedOpenDualCircuitTail_of_windows`: if a finite open event
    `G_m` is independent of every finite encoded window `F_{m,M}`, it is independent of the
    countable tail `F_m`. Added `PlanarPeierlsWindowGeometry`, a source-shaped package that
    assumes only finite-window independence and automatically yields the existing
    `PlanarPeierlsGeometry`, together with Equation (1.12) and Theorem (1.10) reductions from this
    finite-window package.

23. **Finite-support Peierls independence package (2026-06-28).** Added the coordinate-level
    Bernoulli independence API `setBernoulli_iIndepSet_mem_univ`,
    `bernoulliBondMeasure_iIndepSet_edgeOpen`,
    `edgeCoordinateMeasurableSpace`, and
    `bernoulliBondMeasure_indepSet_of_measurableSet_edgeCoordinateMeasurableSpace`. Named the
    crossed primal support of a shifted-dual circuit as `DualCircuit.crossedPrimalEdgeFinset` and
    proved `DualCircuit.isOpen_event_eq_closedEdgeSetEvent`. For encoded finite Peierls windows,
    added `encodedOpenDualCircuitWindowPrimalSupport`,
    `measurableSet_encodedOpenDualCircuitWindow_edgeCoordinateMeasurableSpace`, and
    `indepSet_openEdgeSetEvent_encodedOpenDualCircuitWindow_of_disjoint_support`, so finite-window
    independence now follows from concrete support disjointness. Added `PlanarPeierlsSupportGeometry`
    and Equation (1.12)/Theorem (1.10) reductions from that support-level package.

24. **Concrete straight `G_m` Peierls event (2026-06-28).** Specialized Grimmett's finite open event
    to the straight coordinate path from the origin as `peierlsStraightOpenPathEdges`. Proved its
    cardinality and probability formulas in `peierlsStraightOpenPathEdges_card` and
    `bernoulliBondMeasure_real_peierlsStraightOpenPathEdges`, and proved that the event
    `openEdgeSetEvent 2 (peierlsStraightOpenPathEdges N)` gives an open path of length at least `N`.
    Added the concrete straight-event probability bridge
    `exists_bernoulliBondMeasure_real_peierlsStraightOpenPathEdges_inter_compl_encodedOpenDualCircuitTail_pos_of_mul_lt_one`.
    Added `PlanarPeierlsStraightGeometry`, reducing Equation (1.12) and Theorem (1.10) to closed
    dual-circuit families, Grimmett's circuit encoding, disjointness from this concrete straight
    path, and the planar separation implication.

25. **Coded Peierls circuit-count interface (2026-06-28).** Added the explicit Grimmett code type
    `PeierlsCircuitCode n = Fin n × SelfAvoidingWalk 2 (n - 1)` and proved
    `peierlsCircuitCode_card`, the exact cardinality `n * σ(n - 1)` used in the
    `ρ(n) ≤ n * σ(n - 1)` estimate. Added `PlanarPeierlsCodedStraightGeometry`, whose relevant
    closed dual circuits are indexed directly by these codes, so the encoding map used by the
    straight-path Peierls package is just subtype projection rather than an arbitrary field.

26. **Source-faithful box `G_m` Peierls event (2026-06-28).** Rechecked Grimmett's §1.4 proof and
    added the actual finite open event used after (1.18): all bonds of the square box
    `B(m) = [-m,m]^2 ∩ ℤ²` are open. Added `squareVertex`, `squareBoxVertices`,
    `squareBoxPositiveEdges`, and `squareBoxEdges`, then packaged the event as
    `peierlsBoxOpenEdges`. Proved its exact Bernoulli probability and positivity, plus the
    box-event version of the `G_m ∩ F_mᶜ` probability bridge. Added `PlanarPeierlsBoxGeometry`
    and `PlanarPeierlsCodedBoxGeometry`, reducing Equation (1.12) and Theorem (1.10) to closed
    dual circuits enclosing `B(m)`, Grimmett's circuit code, support disjointness from the box
    bonds, and the planar separation implication. The earlier straight-path package remains only
    an auxiliary finite-open bridge, not the source-faithful `G_m`.

27. **Per-circuit box support reduction (2026-06-28).** Added
    `DualCircuit.AvoidsBoxEdges` and
    `disjoint_encodedOpenDualCircuitWindowPrimalSupport_of_forall`, reducing finite-window
    support disjointness to a per-circuit geometric fact. Added `PlanarPeierlsBoxCircuitGeometry`
    and `PlanarPeierlsCodedBoxCircuitGeometry`, so the sharpest remaining Peierls interface now
    asks for relevant closed dual circuits decoded from Grimmett's codes, each avoiding the bonds
    of `B(m)`, together with the planar separation implication. This narrows the unfinished
    geometry to the concrete circuit-surrounds-box construction rather than a whole-window
    support assumption.

28. **Box-vertex Peierls separation split (2026-06-28).** Added vertex-rooted open-path and
    infinite-cluster predicates `hasOpenPathOfLengthAtLeastFrom`,
    `hasOpenPathOfLengthExactlyFrom`, and `hasInfiniteOpenClusterFrom`, with exact/at-least
    equivalences and origin specializations. Added the box-edge membership lemmas
    `mem_squareBoxVertices_iff_coords`, `mem_squareBoxPositiveEdges_iff`,
    `SquarePositiveEdge.toEdge_mem_squareBoxEdges_iff`, `signedStepEdge_mem_squareBoxEdges`,
    `squareEdge_mem_squareBoxEdges_of_adj`,
    `walkEdgeFinset_subset_squareBoxEdges_of_support_subset`, and
    `walkIsOpen_of_mem_openEdgeSetEvent_squareBoxEdges_of_support_subset`, plus the reusable
    Bernoulli helper `walkIsOpen_of_mem_openEdgeSetEvent_of_walkEdgeFinset_subset`. These prove
    that Grimmett's box-open event opens every concrete connector walk whose vertices stay inside
    `B(m)`. In the Peierls layer, added `boxVertexInfiniteOpenClusterEvent`,
    `openBox_inter_tail_compl_subset_origin_infinite_of_box_vertex`,
    `walkIsOpen_of_mem_openEdgeSetEvent_peierlsBoxOpenEdges_of_support_subset`,
    `PlanarPeierlsBoxSeparationGeometry`, and
    `PlanarPeierlsCodedBoxSeparationGeometry`, splitting Grimmett's final geometric step into:
    no surrounding closed dual circuit gives an infinite cluster from some vertex of `B(m)`, and
    all box bonds open connect that cluster back to the origin.

29. **Open connector path surgery (2026-06-28).** Added core graph-walk openness lemmas
    `walkIsOpen_of_edges_subset`, `walkIsOpen_append`, `walkIsOpen_reverse`, `walkIsOpen_drop`,
    `walkIsOpen_bypass`, and `walkIsOpen_toPath`, plus
    `walk_isPath_append_of_disjoint_tail` and
    `hasOpenPathOfLengthAtLeastFrom_of_append_disjoint_tail`. Specialized these to Grimmett's
    box event as `hasOpenPathOfLengthAtLeast_of_peierlsBoxOpenEdges_append_outside_tail` and
    `hasInfiniteOpenCluster_of_peierlsBoxOpenEdges_and_outside_tails`: under `G_m`, an in-box
    connector followed by an open self-avoiding path whose tail avoids `B(m)` gives an open
    self-avoiding path from the origin. This is the finite-deletion/path-surgery component needed
    to turn the future no-closed-dual-circuit separation into the origin-infinite event.

30. **Concrete Manhattan connectors inside `B(m)` (2026-06-28).** Added signed-step endpoint and
    support-control lemmas for repeated coordinate moves:
    `cubicEndpointFrom_replicate_pos`, `cubicEndpointFrom_replicate_neg`,
    `cubicVerticesFrom_replicate_pos_coord_between`,
    `cubicVerticesFrom_replicate_neg_coord_between`, and the corresponding other-coordinate
    preservation lemmas. Used them to prove explicit square-box connector theorems:
    `exists_squareBoxHorizontalPosConnector`, `exists_squareBoxHorizontalNegConnector`,
    `exists_squareBoxVerticalPosConnectorFrom`, `exists_squareBoxVerticalNegConnectorFrom`, and
    the full `exists_squareBoxConnector`, showing every vertex of `B(m)` is connected to the
    origin by a walk staying in `B(m)`. In the Peierls layer, proved
    `exists_open_peierlsBoxConnector`,
    `hasOpenPathOfLengthAtLeast_of_peierlsBoxOpenEdges_box_vertex_outside_tail`, and
    `hasInfiniteOpenCluster_of_peierlsBoxOpenEdges_and_box_vertex_outside_tails`, eliminating the
    connector assumption from the box-open transfer step.

31. **Outside-tail Peierls separation interface (2026-06-28).** Added
    `boxVertexOutsideTailsEvent`, the direct no-circuit separation output needed after Grimmett's
    Peierls tail estimate: for every length, some vertex of `B(m)` starts an open self-avoiding
    path whose tail avoids `B(m)`. Proved
    `openBox_inter_boxVertexOutsideTailsEvent_subset_origin_infinite` and
    `openBox_inter_tail_compl_subset_origin_infinite_of_box_vertex_outside_tails`, using the
    concrete Manhattan connector and path-surgery lemmas to turn `G_m ∩ F_mᶜ` into the
    origin-infinite event. Added `PlanarPeierlsBoxOutsideTailsGeometry` and
    `PlanarPeierlsCodedBoxOutsideTailsGeometry`, so Equation (1.12) and Theorem (1.10) now reduce
    to the source-faithful box event, Grimmett's circuit code, per-circuit box avoidance, and the
    actual planar no-circuit-to-outside-tail separation theorem.

32. **Finite box-exit to outside-tail adapter (2026-06-28).** Added generic contiguous-subwalk
    tools `walk_isPath_of_isSubwalk`, `walkIsOpen_of_isSubwalk`, and
    `exists_isSubwalk_suffix_from_last_region`, plus cubic coordinate-distance lemmas showing a
    walk changes each coordinate by at most its length. Specialized these in the planar layer as
    `squareBoxVertices_mono` and `squareBox_exit_walk_length_ge`. In the Peierls layer, added
    `boxVertexReachesOutsideBoxEvent` and proved
    `boxVertexReachesOutsideBoxEvent_subset_boxVertexOutsideTailsEvent`: an open path from
    `B(m)` to outside every `B(m+n)` can be trimmed at its last visit to `B(m)` to produce the
    outside-tail paths used by the `G_m` connector step. Added `PlanarPeierlsBoxExitGeometry` and
    `PlanarPeierlsCodedBoxExitGeometry`, so the remaining planar separation theorem may now be
    stated in the natural finite-box exit form.

33. **Finite open-reachable boundary for Peierls separation (2026-06-29).** Added the
    finite-scale event `boxReachesOutsideBoxAtScaleEvent` and the finite cluster
    `boxOpenReachableVertices m M ω` of vertices in `B(M)` reachable from `B(m)` by open walks
    staying in `B(M)`. Proved `squareBox_subset_boxOpenReachableVertices`,
    `boxOpenReachableVertices_step`,
    `not_edgeOpen_of_boxOpenReachableVertices_boundary`, and
    `not_edgeOpen_of_boxOpenReachableVertices_boundary_to_outside`: if an edge could open from
    this cluster to another vertex in the box, that vertex would be reachable, and if the
    finite-scale box-exit event fails then any edge from the cluster to outside `B(m+n)` is closed.
    Added the finite oriented boundary
    `boxOpenReachableBoundaryPositiveEdges` and proved
    `not_edgeOpen_of_mem_boxOpenReachableBoundaryPositiveEdges`. This is the graph-theoretic
    cluster-boundary half of Grimmett's Peierls separation proof; the remaining planar work is to
    transport this closed boundary to a shifted-dual circuit surrounding `B(m)`.

34. **Shifted-dual boundary opened by closed primal boundary (2026-06-29).** Added
    `squarePositiveEdgeDualCrossingEmbedding`, the finite-boundary version of the square
    primal/dual crossing bijection, and defined `boxOpenReachableBoundaryDualEdges` as the
    shifted-dual bonds crossing the open-reachable boundary. Proved
    `edgeOpen_dualSquareConfiguration_of_mem_boxOpenReachableBoundaryDualEdges` and
    `boxOpenReachableBoundaryDualEdges_subset_dualSquareConfiguration`: the entire shifted-dual
    boundary is open in the induced dual configuration because every crossed primal boundary bond
    is closed. This moves the remaining Peierls separation work from closed primal-boundary
    algebra to the combinatorial extraction of a surrounding shifted-dual circuit.

35. **One-step enlarged Peierls frontier (2026-06-29).** Added
    `boxOpenReachableFrontierPositiveEdges`, the finite frontier in `B(M+1)` crossing from the
    open-reachable cluster in `B(M)` to its complement. Proved
    `boxOpenReachableBoundaryPositiveEdges_subset_frontier` and
    `not_edgeOpen_of_mem_boxOpenReachableFrontierPositiveEdges_of_not_boxReachesOutside`: under
    failure of the finite exit event, every frontier bond is closed, whether the other endpoint is
    still inside `B(m+n)` or has just left it. Transported this to shifted-dual bonds with
    `boxOpenReachableFrontierDualEdges`,
    `edgeOpen_dualSquareConfiguration_of_mem_boxOpenReachableFrontierDualEdges_of_not_boxReachesOutside`,
    and
    `boxOpenReachableFrontierDualEdges_subset_dualSquareConfiguration_of_not_boxReachesOutside`.
    This gives the future circuit-extraction proof a finite dual-open frontier that includes the
    one-step exterior boundary of the failed box-exit event.

36. **Frontier crossing cut lemma (2026-06-29).** Added
    `exists_boundary_edge_of_walk_leaves`, a finite walk cut lemma locating the first edge on a
    walk from a predicate to its complement. Specialized it to the Peierls reachable cluster with
    `squareBox_adj_mem_succ`,
    `exists_mem_boxOpenReachableFrontierPositiveEdges_of_adj`, and
    `exists_mem_boxOpenReachableFrontierPositiveEdges_of_walk_to_outside`: any walk from the
    open-reachable cluster to outside the ambient box crosses a positive frontier bond. Transported
    the statement across the shifted square primal/dual crossing bijection as
    `exists_mem_boxOpenReachableFrontierDualEdges_of_walk_to_outside`. The remaining planar
    separation work is now the combinatorial step turning this crossed dual-open frontier into a
    closed dual circuit surrounding `B(m)`.

37. **Frontier-circuit Peierls reduction (2026-06-29).** Added
    `DualCircuit.isOpen_of_walkEdgeFinset_subset_dualSquareConfiguration` and the package
    `PlanarPeierlsCodedFrontierGeometry`. Its primitive remaining field is exactly the finite
    frontier extraction statement: if a finite exit from `B(N)` to outside `B(N+scale)` fails,
    some relevant Grimmett-coded shifted-dual circuit of length at least `N` has all its edges in
    the finite dual frontier. Proved
    `PlanarPeierlsCodedFrontierGeometry.toPlanarPeierlsCodedBoxExitGeometry`, which uses the
    already-proved closed-frontier/dual-open lemmas to turn that frontier-supported circuit into
    membership in the encoded Peierls tail. Added the corresponding Equation (1.12) and Theorem
    (1.10) reductions
    `cubicCriticalProbability_two_bounds_of_planarPeierlsCodedFrontierGeometry` and
    `cubicCriticalProbability_pos_lt_one_of_planarPeierlsCodedFrontierGeometry`.

38. **Frontier support disjointness from `G_m` (2026-06-29).** Proved
    `not_mem_peierlsBoxOpenEdges_of_mem_boxOpenReachableFrontierPositiveEdges` and
    `not_mem_peierlsBoxOpenEdges_of_mem_boxOpenReachableFrontierDualEdges`: a frontier bond, or
    the primal bond crossed by a shifted-dual frontier bond, cannot be one of the box bonds in
    `G_m`, because all vertices of `B(m)` are already in the open-reachable cluster. Lifted this
    to circuits as
    `DualCircuit.avoidsBoxEdges_of_walkEdgeFinset_subset_boxOpenReachableFrontierDualEdges`.
    Thus any circuit extracted from the finite dual frontier automatically satisfies the
    box-support disjointness needed for Grimmett's `G_m`/`F_m` independence step.

39. **Box-indexed Peierls tail interface (2026-06-29).** Added
    `boxIndexedOpenDualCircuitTail`, allowing the relevant closed dual circuit family `F_N` to
    depend on the box scale `N`, as in Grimmett's proof. Proved measurability, the countable
    Peierls tail bound
    `bernoulliBondMeasure_real_boxIndexedOpenDualCircuitTail_of_encoding_le`, convergence to zero
    under `(1-p)λ(2)<1`, and the indexed `G_N ∩ F_Nᶜ` probability bridge
    `exists_bernoulliBondMeasure_real_peierlsBoxOpenEdges_inter_compl_boxIndexedOpenDualCircuitTail_pos_of_mul_lt_one`.
    Added `PlanarPeierlsBoxIndexedGeometry` and the corresponding Equation (1.12)/Theorem (1.10)
    reductions. This removes an artificial global-relevance constraint from the remaining planar
    frontier/circuit extraction target.

40. **Box-indexed coded frontier reduction (2026-06-29).** Added
    `PlanarPeierlsBoxIndexedCodedFrontierGeometry`, whose relevant Grimmett code predicate may
    depend on both the source box scale `N` and the circuit length. Proved the adapter
    `PlanarPeierlsBoxIndexedCodedFrontierGeometry.toPlanarPeierlsBoxIndexedGeometry`: per-circuit
    box avoidance supplies `G_N`/`F_N` independence through the finite-window support theorem, and
    a failed finite box exit would yield a frontier-supported dual-open circuit in the indexed tail.
    Added the corresponding Equation (1.12)/Theorem (1.10) public reductions. The remaining
    planar target is now the concrete extraction of such an `N`-relevant circuit from the finite
    shifted-dual frontier.

41. **Nonempty open dual frontier (2026-06-29).** Proved
    `exists_mem_boxOpenReachableFrontierDualEdges`: a deterministic horizontal walk from the
    origin to just outside `B(m+n)` must cross the enlarged finite open-reachable frontier. Under
    failure of the finite exit event, this yields
    `exists_open_mem_boxOpenReachableFrontierDualEdges_of_not_boxReachesOutside`, an actual
    dual-open edge in the shifted-dual frontier. This is the first concrete nonemptiness input for
    the remaining step that upgrades the finite open dual frontier to a surrounding circuit.

42. **Frontier cut/support strengthening (2026-06-29).** Added
    `exists_mem_boxOpenReachableFrontierDualEdges_of_box_walk_to_outside`, the source-box version
    of the finite cut lemma: any walk from `B(m)` to outside the ambient box crosses the
    shifted-dual frontier. Also proved
    `disjoint_peierlsBoxOpenEdges_boxOpenReachableFrontierDualEdges_crossedPrimal`, saying that
    the entire frontier's crossed primal support is disjoint from the box-open support `G_m`.
    These are the path-crossing and support facts the final surrounding-circuit extraction theorem
    should reuse directly.

43. **Primal frontier cut representation (2026-06-29).** Added
    `boxOpenReachableFrontierPrimalEdges` and its membership lemma, packaging the crossed primal
    bonds of the shifted-dual frontier as an explicit finite edge cut. Proved the corresponding
    walk and source-box crossing lemmas
    `exists_mem_boxOpenReachableFrontierPrimalEdges_of_walk_to_outside` and
    `exists_mem_boxOpenReachableFrontierPrimalEdges_of_box_walk_to_outside`, plus
    `disjoint_peierlsBoxOpenEdges_boxOpenReachableFrontierPrimalEdges`. This gives the remaining
    dual-circuit extraction step a direct primal/dual cut interface faithful to Grimmett's
    finite-frontier Peierls proof.

44. **Primal frontier boundary characterization (2026-06-29).** Proved
    `mem_boxOpenReachableFrontierPrimalEdges_iff_positive`,
    `boxOpenReachableFrontierPrimalEdges_subset_squareBoxEdges_succ`,
    `mem_boxOpenReachableFrontierPrimalEdges_of_adj`, and
    `mem_boxOpenReachableFrontierPrimalEdges_iff_boundary_adj`. The explicit primal frontier cut is
    now characterized exactly as the finite set of nearest-neighbour bonds crossing from the
    open-reachable cluster to its complement, and every such bond lies in the one-step enlarged box.
    This is the local finite-boundary structure needed before extracting the surrounding shifted-dual
    circuit in Grimmett's Peierls argument.

45. **Closed primal frontier cut under failed exit (2026-06-29).** Proved
    `not_edgeOpen_of_mem_boxOpenReachableFrontierPrimalEdges_of_not_boxReachesOutside` and
    `disjoint_boxOpenReachableFrontierPrimalEdges_configuration_of_not_boxReachesOutside`. When the
    finite box-exit event fails, the entire explicit primal frontier cut is disjoint from the open
    configuration. This records Grimmett's closed finite boundary directly on the primal cut before
    transporting it through the shifted-dual crossing bijection.

46. **Finite shifted-dual frontier graph interface (2026-06-29).** Added
    `boxOpenReachableFrontierDualGraph`, its edge-set characterization, and the proof
    `boxOpenReachableFrontierDualGraph_le_dualSquareGraph`. A walk in this finite frontier graph can
    be viewed as a shifted-dual square-lattice walk via `boxOpenReachableFrontierDualGraphWalk`, with
    all traversed bonds supported by `boxOpenReachableFrontierDualEdges`. Packaged frontier-graph
    circuits as `DualCircuit`s using
    `dualCircuitOfBoxOpenReachableFrontierDualGraphCircuit`, preserving length, frontier support,
    dual-openness under failed box exit, and box-edge avoidance. The remaining extraction theorem can
    now target the purely graph-theoretic task of finding a circuit in this finite frontier graph.

47. **Frontier graph crossing/separation bridge (2026-06-29).** Proved
    `exists_mem_boxOpenReachableFrontierDualGraph_edgeSet_of_walk_to_outside` and
    `exists_mem_boxOpenReachableFrontierDualGraph_edgeSet_of_box_walk_to_outside`: any primal walk
    from the open-reachable cluster, in particular from `B(m)`, to outside the ambient box crosses a
    primal bond dual to an edge of the finite shifted-dual frontier graph. The remaining extraction
    theorem can now use this graph-level separation statement directly.

48. **Graph-level open frontier separation (2026-06-29).** Proved
    `edgeOpen_dualSquareConfiguration_of_mem_boxOpenReachableFrontierDualGraph_edgeSet_of_not_boxReachesOutside`,
    `exists_open_mem_boxOpenReachableFrontierDualGraph_edgeSet_of_not_boxReachesOutside`,
    `dualWalkIsOpen_boxOpenReachableFrontierDualGraphWalk_of_not_boxReachesOutside`, and the
    reachable/source-box crossing forms
    `exists_open_mem_boxOpenReachableFrontierDualGraph_edgeSet_of_walk_to_outside_of_not_boxReachesOutside`
    and
    `exists_open_mem_boxOpenReachableFrontierDualGraph_edgeSet_of_box_walk_to_outside_of_not_boxReachesOutside`.
    Under a failed finite box exit, frontier graph edges and walks are dual-open, and any primal
    walk to the exterior crosses such a dual-open graph edge. The remaining planar task is still to
    extract a surrounding relevant circuit inside this graph.

49. **Frontier edge-connectivity to circuit bridge (2026-06-29).** Imported Mathlib's acyclic graph
    cycle criterion and proved
    `exists_isCycle_boxOpenReachableFrontierDualGraph_of_adj_isEdgeReachable_two` plus
    `exists_open_dualCircuit_of_boxOpenReachableFrontierDualGraph_adj_isEdgeReachable_two`. Thus an
    adjacent pair in the finite shifted-dual frontier graph that is `2`-edge-reachable yields a
    frontier-supported cycle; under failed finite exit, this cycle packages as an open shifted-dual
    `DualCircuit` avoiding `G_m`'s box support. The remaining extraction proof is reduced further
    to finding a surrounding frontier edge with this local non-bridge/edge-connectivity property.

50. **Dual-cycle tail coding for Grimmett's `ρ(n)` bound (2026-06-29).** Added
    `cubicTranslate_injective`, `cubicVectorSelfAvoiding_of_cubicWalkFrom_isPath`, and
    `selfAvoidingWalkOfPathWord`, so any signed direction word that realizes a graph path from an
    arbitrary translated start is counted as a self-avoiding walk from the origin. Packaged the
    cycle tail as `DualCycleTailCodeData`, with endpoint and copy equalities showing that the
    selected word reconstructs the original tail; `dualCycle_eq_cons_selfAvoidingWalkOfDualCycleTail`
    reconstructs the whole cycle from its first edge and this word. Also introduced the concrete
    positive-axis dual crossing edge and
    `dualCycleStartsWithPositiveXAxisCrossing`, the source-shaped mark used in Grimmett's
    `ρ(n) ≤ n * σ(n - 1)` count. Proved injectivity of the lower endpoint, upper endpoint, and
    positive-axis crossing edge as functions of the crossing coordinate, and packaged
    `PositiveXAxisMarkedDualCycle n` with its `DualCircuit` view and `PeierlsCircuitCode n` code.
    Added `PositiveXAxisMarkedDualCycle.ofWalkStartsWith`,
    `PositiveXAxisMarkedDualCycle.ofDualCircuitStartsWith`, and
    `PositiveXAxisMarkedDualCycle.ofWalkSndEq` as the bridge from a rotated simple dual cycle to
    the normalized positive-axis package.
    Added `PositiveXAxisMarkedDualCycle.k_eq_of_code_eq` and
    `PositiveXAxisMarkedDualCycle.tail_toList_eq_of_code_eq`, proving that equality of Grimmett
    codes recovers both the positive-axis crossing coordinate and the underlying direction word of
    the reconstructible tail. Finally proved `PositiveXAxisMarkedDualCycle.code_injective` and
    packaged `PositiveXAxisMarkedDualCycle.codeEmbedding`, using support extensionality to cancel
    the endpoint copies from `Walk.tail_cons`. Finally added the finite-family form of the count,
    `PositiveXAxisMarkedDualCycle.card_le_mul_selfAvoidingWalkCount`, and its Peierls probability
    estimate `PositiveXAxisMarkedDualCycle.bernoulliBondMeasure_real_openEvent_le` for the
    normalized open-event family. The remaining counting task is now to normalize relevant
    surrounding frontier cycles into this positive-axis package.

51. **Positive-axis frontier package for Equation (1.12) (2026-06-29).** Added
    `PlanarPeierlsBoxIndexedPositiveAxisFrontierGeometry`, a box-indexed Peierls interface whose
    relevant circuits are indexed directly by `PositiveXAxisMarkedDualCycle n` rather than by
    arbitrary code subtypes. Its adapter `toPlanarPeierlsBoxIndexedGeometry` uses
    `PositiveXAxisMarkedDualCycle.code_injective` as Grimmett's marked-edge/self-avoiding-tail
    encoding, while the support and frontier fields match the existing `G_N`/`F_N` proof stack.
    Exposed the corresponding reductions
    `cubicCriticalProbability_two_bounds_of_planarPeierlsBoxIndexedPositiveAxisFrontierGeometry`
    and `cubicCriticalProbability_pos_lt_one_of_planarPeierlsBoxIndexedPositiveAxisFrontierGeometry`.
    The remaining geometric theorem is now precisely the normalization/extraction of a relevant
    positive-axis marked circuit from the failed finite box-exit frontier.

52. **Positive-axis frontier edge (2026-06-29).** Added crossing normal forms
    `primalToDualCrossingPositiveEdge_positiveXAxis`,
    `dualPositiveXAxisPositiveEdge_toEdge`, and
    `squarePositiveEdgeDualCrossingEmbedding_positiveXAxis`, plus the discrete boundary lemma
    `exists_nat_true_false_boundary`. Used them to prove
    `exists_dualPositiveXAxisCrossingEdge_mem_boxOpenReachableFrontierDualEdges`: the enlarged
    finite shifted-dual frontier always contains some `dualPositiveXAxisCrossingEdge k`, obtained
    from the first place where the open-reachable set along the positive x-axis stops before
    exiting the ambient box. The graph form
    `exists_dualPositiveXAxisCrossingEdge_adj_boxOpenReachableFrontierDualGraph` packages this
    edge as an adjacency in the finite shifted-dual frontier graph. The remaining planar extraction
    task now has a concrete positive-axis frontier edge to feed into the cycle/edge-connectivity
    and normalization steps.

53. **Oriented positive-axis frontier cycle bridge (2026-06-29).** Strengthened the
    edge-connectivity bridge so it preserves Grimmett's marked edge. Added
    `exists_isCycle_mem_edge_boxOpenReachableFrontierDualGraph_of_adj_isEdgeReachable_two` and
    `exists_isCycle_startsWith_boxOpenReachableFrontierDualGraph_of_adj_isEdgeReachable_two`,
    using Mathlib's delete-edge reachability criterion to produce a finite-frontier simple cycle
    that either contains the chosen edge or is oriented to start with it. Transported this to the
    shifted-dual lattice via `boxOpenReachableFrontierDualGraphWalk_snd`, proving
    `exists_dualSquare_isCycle_startsWith_positiveXAxisCrossing_of_isEdgeReachable_two` and the
    dual-open wrapper
    `exists_open_dualCircuit_startsWith_positiveXAxisCrossing_of_isEdgeReachable_two`. The
    remaining local planar graph input is now the 2-edge-reachability/non-bridge condition for
    the concrete positive-axis frontier adjacency.

54. **Positive-axis extraction normalization adapter (2026-06-29).** Proved the remaining
    arithmetic pieces needed to turn a source-surrounding positive-axis frontier cycle into
    Grimmett's normalized countable family. Added
    `PositiveXAxisMarkedDualCycle.positiveXAxisCrossing_k_lt_length_of_mem_support_left`, showing
    that an oriented positive-axis dual walk that reaches the left side of the origin has
    `k < length`, and `le_of_dualPositiveXAxisCrossingEdge_mem_boxOpenReachableFrontierDualEdges`
    plus its graph-adjacency form, showing that a positive-axis frontier crossing has coordinate
    at least the source-box radius. Also packaged the deterministic bounded crossing statement
    `exists_dualPositiveXAxisCrossingEdge_adj_boxOpenReachableFrontierDualGraph_between`, giving
    `m ≤ k < m+n+1` for the concrete positive-axis frontier edge. Combined these in
    `exists_positiveXAxisMarkedDualCycle_of_isEdgeReachable_two_of_mem_support_left`, which turns a
    2-edge-reachable positive-axis frontier edge plus the left-excursion surround fact into a
    frontier-supported, dual-open `PositiveXAxisMarkedDualCycle (m + r)`. Added
    `PlanarPeierlsPositiveAxisFrontierExtraction` and its adapter to
    `PlanarPeierlsBoxIndexedPositiveAxisFrontierGeometry`, with public Equation (1.12)/Theorem
    (1.10) reductions. The remaining planar theorem is now isolated as: failed finite exit gives a
    non-bridge positive-axis frontier edge, and its oriented frontier cycle makes the left
    excursion around the origin.

55. **Source-faithful positive-axis cycle extraction interface (2026-06-29).** Added
    `exists_positiveXAxisMarkedDualCycle_of_cycle_mem_support_left`, a direct adapter from the
    actual oriented frontier cycle Grimmett constructs to a normalized
    `PositiveXAxisMarkedDualCycle (m + r)`. This avoids requiring an all-cycles left-excursion
    hypothesis: the future planar proof may now produce one simple frontier cycle, already rotated
    to start with the positive-axis crossing, supported by the finite closed dual frontier and
    making the left excursion around the origin. Added
    `PlanarPeierlsPositiveAxisFrontierCycleExtraction` and its adapter to
    `PlanarPeierlsBoxIndexedPositiveAxisFrontierGeometry`, plus public Equation (1.12)/Theorem
    (1.10) reductions from this sharper package. Also provided
    `PlanarPeierlsPositiveAxisFrontierExtraction.toCycleExtraction`, showing that the earlier
    2-edge-reachability package still implies the sharper source-facing cycle package.

56. **Parity-crossing Peierls extraction interface (2026-06-29).** Added the discrete
    positive-ray crossing count
    `dualWalkPositiveXAxisCrossingEdges` / `dualWalkPositiveXAxisCrossingCount` and the parity
    predicate `dualWalkSurroundsOriginByParity`. This records the suggested replacement for
    topological "interior" language: a shifted-dual cycle surrounds the origin when it crosses the
    positive horizontal ray an odd number of times. Added
    `exists_positiveXAxisMarkedDualCycle_of_cycle_k_lt_length`, a counting-only normalization
    bridge for an already oriented positive-axis frontier cycle once the parity argument supplies
    `k < length`; the older left-excursion bridge now factors through it. Added
    `PlanarPeierlsParityFrontierCycleExtraction`, whose fields ask for a normalized
    frontier-supported simple cycle with odd crossing number and the finite parity-line lemma that
    this odd crossing makes the positive-axis mark one of the `length` choices in Grimmett's
    `n * σ(n - 1)` count. Its adapter feeds the existing box-indexed positive-axis Peierls stack,
    yielding direct Equation (1.12)/Theorem (1.10) reductions from the parity formulation without
    introducing any new axiom.

57. **Positive-axis finite parity core (2026-06-29).** Proved the finite one-dimensional parity
    lemma `odd_card_filter_nat_changes_iff`: along a finite line, the number of adjacent truth
    changes is odd exactly when the endpoint truth values differ, plus the true-to-false corollary
    `odd_card_filter_nat_changes_of_true_false`. Specialized this to the Peierls finite
    open-reachable set as `positiveXAxisOpenReachableChangeIndices` and
    `positiveXAxisOpenReachableChangeIndices_odd`: on the positive horizontal axis, reachability
    starts true at the origin and is false just outside `B(m+n)`, so the total number of
    positive-axis frontier changes is odd. Added
    `dualPositiveXAxisCrossingEdge_mem_frontier_of_mem_positiveXAxisOpenReachableChangeIndices`,
    showing that every such change is represented by the corresponding shifted-dual frontier
    edge. This proves the parity core of the proposed replacement for the planar
    interior/Jordan-curve language; the remaining extraction step is to decompose the finite dual
    frontier into cycles and select an odd-crossing cycle.

58. **Frontier positive-ray crossing parity (2026-06-29).** Strengthened the finite parity bridge
    from existence to exact frontier counting. Added
    `mem_positiveXAxisOpenReachableChangeIndices_of_dualPositiveXAxisCrossingEdge_mem_frontier`
    and
    `dualPositiveXAxisCrossingEdge_mem_frontier_iff_mem_positiveXAxisOpenReachableChangeIndices`,
    proving that a shifted-dual positive-axis frontier edge occurs exactly at a positive-axis
    reachability change. Packaged the frontier crossing finset
    `boxOpenReachableFrontierPositiveXAxisCrossingEdges`, proved its image identity
    `boxOpenReachableFrontierPositiveXAxisCrossingEdges_eq_map_changes`, and derived
    `boxOpenReachableFrontierPositiveXAxisCrossingEdges_odd`. Also added the walk-support
    connector
    `dualWalkPositiveXAxisCrossingEdges_subset_frontierPositiveXAxisCrossingEdges_of_subset`.
    The remaining parity extraction work is now squarely the finite graph step: decompose the
    even dual frontier into cycles and choose one cycle carrying odd positive-ray crossing parity.

59. **Odd-component selection for parity frontier decompositions (2026-06-29).** Added the finite
    parity selection lemma `exists_odd_card_of_odd_card_biUnion`: an odd cardinality
    pairwise-disjoint finite union has an odd component. Specialized it to the Peierls frontier as
    `exists_odd_card_of_frontierPositiveXAxisCrossingEdges_decomposition`, and added the
    circuit-level selector
    `exists_dualCircuit_surroundsOriginByParity_of_frontier_decomposition`. Also recorded the
    local consequences that parity-surrounding walks have positive crossing count and contain a
    positive-axis crossing edge. Finally introduced
    `PlanarPeierlsParityFrontierCircuitDecomposition`, a source-shaped package for a finite
    edge-disjoint normalized cycle decomposition of the frontier positive-ray crossings, and proved
    its adapter to `PlanarPeierlsParityFrontierCycleExtraction` plus Equation (1.12)/Theorem
    (1.10) reductions. This formalizes the proposed odd-crossing component-selection route without
    invoking a Jordan-curve theorem; the remaining finite geometric work is to prove the actual
    frontier decomposition.

60. **Closed-walk cut parity for the positive-axis mark (2026-06-29).** Proved the discrete
    parity-to-mark bridge requested in the planar-duality replacement. Added a generic cut-crossing
    parity lemma for graph walks,
    `Percolation.SimpleGraph.Walk.even_countP_edges_edgeCrossesSet_of_closed`, plus shifted-dual
    horizontal axis crossing edges at all integer coordinates. Proved
    `dualWalkPositiveXAxisCrossingCount_eq_countP_edges_of_isTrail` and
    `exists_negative_dualXAxisCrossingEdge_mem_walkEdgeFinset_of_surroundsOriginByParity`: an odd
    positive-ray crossing closed dual cycle must also cross the horizontal axis at a negative
    coordinate. This gives a left support vertex and proves
    `PositiveXAxisMarkedDualCycle.positiveXAxisCrossing_k_lt_length_of_surroundsOriginByParity`,
    so the parity-cycle Peierls adapter no longer needs a separate topological left-excursion or
    parity-to-mark assumption.

61. **Even incidence of the finite dual frontier (2026-06-29).** Proved the local discrete
    boundary parity lemma behind the suggested Peierls replacement for the Jordan-curve sentence.
    Added `squareCellPositiveEdgeList` / `squareCellPositiveEdges` for the four primal bonds
    around a shifted-dual vertex, proved
    `even_card_squareCellPositiveEdges_boundary`, and proved the crossing classification
    `mem_squareCellPositiveEdges_iff_mem_crossing`. For the finite open-reachable frontier, proved
    `mem_boxOpenReachableFrontierPositiveEdges_iff_boundary`, showing that the one-step enlarged
    box condition follows from a reachability change across the bond. Finally defined incident
    shifted-dual frontier bonds as `boxOpenReachableFrontierDualEdgesIncident` and proved
    `even_card_boxOpenReachableFrontierDualEdgesIncident`: every shifted-dual vertex sees an even
    number of frontier edges. This formalizes the "membership changes around each primal square an
    even number of times" step; the remaining finite graph work is to turn even incidence plus odd
    positive-ray crossing into the required cycle decomposition/extraction.

62. **No-bridge extraction for the finite dual frontier (2026-06-29).** Proved the finite graph
    step that an all-even finite-support graph has no bridges:
    `SimpleGraph.isEdgeReachable_two_of_forall_even_degree_of_finite_support`. Specialized this
    to the Peierls frontier via `boxOpenReachableFrontierDualGraph_support_finite` and
    `boxOpenReachableFrontierDualGraph_isEdgeReachable_two_of_adj`, so every shifted-dual
    frontier edge is now `2`-edge-reachable. This removes the earlier edge-connectivity
    placeholder from positive-axis circuit extraction and proves
    `exists_dualSquare_isCycle_startsWith_positiveXAxisCrossing_of_frontier` plus
    `exists_open_dualCircuit_startsWith_positiveXAxisCrossing_of_not_boxReachesOutside`. The
    remaining planar/parity work is now the selection/decomposition step: choose a frontier cycle
    with odd positive-ray crossing parity, equivalently the surrounding component in Grimmett's
    Peierls argument.

63. **Direct parity frontier cycle extraction (2026-06-29).** Proved the finite graph selection
    step behind the suggested Jordan-curve-free Peierls argument. Added
    `SimpleGraph.exists_isCycle_odd_card_filter_of_odd_edge_finset`: in a locally finite graph
    with finite support and all degrees even, any finite odd edge set is met oddly by some simple
    cycle. Applied this to the shifted-dual frontier and its odd positive-ray crossing finset,
    yielding `exists_dualSquare_isCycle_surroundsOriginByParity_of_frontier` and the normalized
    positive-axis form
    `exists_dualSquare_isCycle_startsWith_positiveXAxisCrossing_surroundsOriginByParity_of_frontier`.
    Also proved rotation/reversal invariance for the parity predicate and packaged the concrete
    `planarPeierlsParityFrontierCycleExtraction`, `grimmettTheorem110Inputs`,
    `cubicCriticalProbability_two_bounds_grimmett`, and
    `cubicCriticalProbability_pos_lt_one_grimmett`. This supplies the source-shaped Peierls upper
    bound without invoking a Jordan curve theorem.

64. **Final public Theorem 1.10 API (2026-06-29).** Promoted the completed Grimmett results to
    the planned public names `cubicCriticalProbability_two_bounds` and
    `cubicCriticalProbability_pos_lt_one`. The older input-package reductions are now named
    `cubicCriticalProbability_two_bounds_of_grimmettTheorem110Inputs` and
    `cubicCriticalProbability_pos_lt_one_of_grimmettTheorem110Inputs`, while the `_grimmett`
    declarations remain compatibility aliases. Also included the root `Percolation` module in the
    Lake library globs, so `import Percolation` exposes the final theorem statements.

65. **Textbook infinite-cluster event repair (2026-06-29).** Replaced the path-tail definition of
    `hasInfiniteOpenCluster` with Grimmett's literal event that the origin open cluster
    `cubicOpenCluster d ω` is infinite, and added the vertex-rooted cluster
    `cubicOpenClusterFrom`. Kept the path-counting interface as separate predicates
    `hasArbitrarilyLongOpenPaths` and `hasArbitrarilyLongOpenPathsFrom`, then proved
    `hasInfiniteOpenCluster_iff_hasArbitrarilyLongOpenPaths` and
    `hasInfiniteOpenClusterFrom_iff_hasArbitrarilyLongOpenPathsFrom` using finite support bounds
    for locally finite cubic walks. Updated `theta`, measurability, dimension monotonicity, and the
    Peierls box-open transfer proofs to pass through those equivalences, so the public
    percolation probability now matches the textbook definition while retaining the existing
    Grimmett path-counting estimates.

66. **Chapter 2 vocabulary and finite-cube transfer pack (2026-07-03).** Started the fresh
    Chapter 2 formalization on `codex/grimmett-chapter-2-followup`. Added
    `Percolation/Bernoulli/Increasing.lean` with the §2.1 vocabulary on `Set ι`
    configurations (`IsIncreasingEvent`, `IsDecreasingEvent`, `IsIncreasingRandomVariable`,
    `DependsOn`, `DependsOnFun`, `restrictTo`, `spliceOn`) and
    `Percolation/Bernoulli/FiniteCube.lean` with the finite cube model
    (`finiteBernoulliWeight`/`finiteBernoulliWeightFamily`, `finiteBernoulliExpectation`,
    `finiteBernoulliProbability`, `finiteCylinder`, `eventTrace`) and the transfer pack:
    finitely supported events are finite disjoint unions of cylinders, hence measurable
    (`DependsOn.measurableSet`), and ambient `setBernoulli` probabilities/integrals equal the
    finite-cube weighted powerset sums
    (`DependsOn.setBernoulli_real_eq_finiteBernoulliProbability`,
    `DependsOnFun.integral_setBernoulli`). All headline declarations use only the three
    standard axioms. This is the shared substrate for FKG, BK, Russo, and the reliability
    inequalities.

67. **Finite-support FKG inequality (2026-07-03).** Added
    `Percolation/Bernoulli/FKG.lean`: Grimmett Theorem (2.4) restricted to finite supports,
    with the finite core `finiteBernoulliExpectation_mul_fkg` proved by bridging to
    Mathlib's Ahlswede–Daykin `Finset.four_functions_theorem` on the powerset algebra —
    the Bernoulli weight is log-supermodular with equality
    (`finiteBernoulliWeight_mul_weight`). Sign hypotheses are removed by shifting at `∅`
    (`finiteBernoulliExpectation_mul_fkg_of_monotone`); indicators give the event form
    `finiteBernoulliProbability_fkg` with decreasing and mixed-monotonicity variants; the
    transfer pack lifts everything to `setBer(univ, p)`
    (`setBernoulli_real_fkg_of_dependsOn` and friends), including the iterated corollary
    (2.7) `setBernoulli_prod_le_real_biInter_fkg`, the observable form
    `setBernoulli_integral_fkg_of_dependsOnFun`, and cubic-lattice wrappers. Divergence
    from the book's coordinate induction recorded on the topic card. All headline
    declarations use only the three standard axioms.

68. **Uniform coupling and Theorem 2.1 (2026-07-03).** Added
    `Percolation/Bernoulli/Coupling.lean`: Grimmett's i.i.d.-uniform coupling
    (`couplingMeasure` on `ι → ℝ` via `Measure.infinitePi` of `volume.restrict (Icc 0 1)`),
    threshold configurations `thresholdConfiguration p = {e | X e < p}` monotone in `p`,
    and the marginal-law identification
    `couplingMeasure_map_thresholdConfiguration : map η_p = setBer(univ, p)` (single
    coordinate law computed by hand on `Prop`, coordinatewise product via
    `Measure.infinitePi_map_pi`). Theorem (2.1) follows in both forms —
    `IsIncreasingEvent.setBernoulli_real_mono` and
    `IsIncreasingRandomVariable.setBernoulli_integral_mono` — for all increasing
    measurable events/integrable variables, plus the motivating application `theta_mono`.
    Standard axioms only.

69. **BK inequality (2026-07-04).** Added `Percolation/Bernoulli/BK.lean`: Grimmett
    Theorems (2.12)/(2.15) and the iterated inequality (2.14) by the faithful van den Berg
    two-copy method — the doubled cube on `ι ⊕ ι`, the interpolated events `bkEvent S`
    reading Grimmett's `B'_k` through the mixed projection `bkMixRead`, the coordinate swap
    `bkSwap` with the C₁/C₂′/C₂″ collision analysis
    (`bkEvent_swap_collision`, `finiteBernoulliProbability_bkEvent_le_insert`), and the
    endpoint factorizations. Disjoint occurrence is provided in both the general `Forces`
    form and the open-witness form, proved equal for increasing events; measure-level
    statements `setBernoulli_real_disjointOccurrence_le_mul` (+ `Forces` variant, cubic
    wrapper, and the k-fold `FiniteDisjointOccurrence` product bound). Reimer's Theorem
    (2.19) is recorded on the topic card as a rejected anti-target with the citation, per
    the book (stated there without proof). Standard axioms only.

70. **Russo's formula (2026-07-04).** Added `Percolation/Bernoulli/Russo.lean`: pivotal
    coordinates (`IsPivotal`, trace analogue, pivotal counts) and Grimmett §2.4 — the
    finite Russo derivative in both the `Σ_e P_p(e pivotal)` form (2.27) and the
    `E_p(N(A))` form (2.26) by induction on the support with the one-coordinate insert
    split; the measure-level Theorem (2.25)
    `IsIncreasingEvent.hasDerivAt_setBernoulli_real` through the projIcc-clamped density
    with cubic wrapper; corollary (2.29) `P(A ∩ {e piv}) = p·P(e piv)`; the growth bound
    (2.31) `P_{p₂}(A) ≤ (p₂/p₁)^{|E|} P_{p₁}(A)`; Theorem (2.32)
    `d/dp E_p(X) = Σ_e E_p(δ_e X)` (finite and measure level); and the second-derivative
    double-sum form of (2.33) with the diagonal-vanishing lemma. Standard axioms only.

71. **General FKG inequality (2026-07-04).** Added
    `Percolation/Bernoulli/FKGInfinite.lean`: Grimmett Theorem (2.4b) for arbitrary
    increasing measurable events, `setBernoulli_real_fkg`, with decreasing, mixed and
    iterated (2.7) corollaries and cubic wrappers. Proof by measure-density approximation
    (recorded divergence from the book's martingale route, statements unchanged and valid
    without countability): the finitely supported events form a set algebra generating the
    ambient σ-algebra (`measurableSpace_eq_generateFrom_finiteSupportEvents`, via the
    coordinate-evaluation `iSup` and propext), Mathlib's
    `MeasureDense.of_generateFrom_isSetAlgebra_finite` gives `ε`-approximation, disjoint
    coordinate blocks are independent (`indep_generateFrom_coordinateEvents`), the splice
    factorization `setBernoulli_real_inter_finiteCylinder` and decomposition
    `setBernoulli_real_eq_sum_splice` realize conditioning on a finite trace, and the slice
    probability `sliceProbability` (tower identity, exactness on supported events, pointwise
    `L¹` contraction, monotone in the configuration) reduces the general inequality to the
    finite FKG of `FKG.lean` plus an `ε → 0` limit. Standard axioms only.

72. **Vertex-independence of `p_c` (2026-07-04).** Added
    `Percolation/Critical/VertexIndependence.lean`: Grimmett Theorem (2.8) for cubic bond
    percolation. Vertex-rooted `thetaFrom`/`cubicCriticalProbabilityFrom`; measurability of
    the vertex-rooted infinite-cluster and two-point connection events by reindexing lattice
    walks with their direction words (`exists_cubicWalkFrom_copy_eq`); lattice connectivity
    `nonempty_cubicWalk` by coordinatewise descent on the Manhattan distance; positivity of
    connections through `Walk.toPath`; the FKG surgery step
    `P_p(y ↔ x)·θ(p,x) ≤ θ(p,y)` via the general `bernoulliBondMeasure_real_fkg`; vanishing
    of `θ(p,·)` at `p = 0`; and the zero-set identification giving
    `cubicCriticalProbabilityFrom_eq`. Also registered the global
    `IsProbabilityMeasure (bernoulliBondMeasure d p)` instance. Standard axioms only.

73. **Disjoint open connections (2.17) (2026-07-04).** Added
    `Percolation/Bernoulli/DisjointConnections.lean`: truncated connection events
    `connectionEventIn` (increasing, supported on their edge set), the witness inclusion of
    pairwise edge-disjoint open walks into the iterated disjoint occurrence, exhaustion of
    the full disjoint-occurrence event by the directed family of finite supports, and
    continuity from below (`Directed.measure_iUnion`) combined with the iterated BK bound,
    giving `bernoulliBondMeasure_real_existsPairwiseDisjointOpenWalks_le_prod`. Standard
    axioms only.

74. **Reliability inequalities (2026-07-04).** Added
    `Percolation/Bernoulli/Reliability.lean`: Grimmett §2.5. Theorem (2.34) — the
    covariance derivative identity `d/dp P_p(A) = cov(N, 1_A)/(p(1−p))` for arbitrary
    finitely supported events, by differentiating the Bernoulli weights
    (`hasDerivAt_finiteBernoulliWeight`), with measure-level and cubic forms; Theorem
    (2.36)(a) via finite Cauchy–Schwarz and the binomial moments `E N = mp`,
    `Var N = mp(1−p)`; (2.36)(b) via (2.41) and finite FKG on `N − 1_A`; the scalar
    inequality (2.44) by rpow calculus; and Theorem (2.38) — `h(p^γ) ≤ h(p)^γ` by induction
    on the support, with the log-ratio antitonicity corollary at measure level and on the
    cubic lattice. Standard axioms only.

75. **Sprinkling inequality (2026-07-04).** Added
    `Percolation/Bernoulli/Sprinkling.lean`: Grimmett Theorem (2.45)/(2.46) for arbitrary
    increasing measurable events over a countable index set — spheres `WithinRadius`,
    interiors `interiorDepth` with measurability via override-map preimages, the
    downward-witness lemma, least-code witness selection (`minimalWitness` via `Nat.sInf`),
    the countable disjoint witness partition with block-independence factorization on the
    coupling space (`couplingMeasure_pi_inter`), the per-witness estimate in division-free
    ℝ≥0∞ form, and the headline
    `IsIncreasingEvent.one_sub_setBernoulli_real_interiorDepth_le` with cubic wrapper. This
    completes the Chapter 2 milestone plan M1–M10; stretch targets (2.28), (2.30), (2.49)
    and the L² form of 2.4(a) remain recorded on the topic card. Standard axioms only.

76. **Grimmett Chapter 4 open-cluster density (2026-07-09).** Added
    `Percolation/Critical/OpenClusterDensity.lean`, `LatticeAnimals.lean`, and
    `ClusterDensityDerivative.lean`. For Theorem (4.2), proved the exact finite-graph identity
    `Σ_v |C(v)|⁻¹ = #components`, boundary/escaping-component squeeze inequalities, the cubic
    open-graph/production-cluster equivalence, `κ(p) = E_p(|C|⁻¹)`, and the almost-sure normalized
    finite-volume limit conditional on the explicitly named multiparameter box-ergodic and
    boundary inputs. For Theorem (4.20), proved an elementary binary-relative-entropy bound and
    the finite exceptional-pair sum at coefficient-table level, conditional on (4.25), with the
    recorded weaker exponent `-n x² p²(1-p)²/18` and `n ≥ 2`. For Theorem (4.31), formalized the
    animal expansion, exact derivative summand (4.32), and a Mathlib uniform-limit theorem giving
    `ContDiffOn ℝ 1` on `[0,1]` under an explicit summable derivative majorant. The three measured
    autoformalization windows used 312,517 / 318,792 / 55,995 tokens and 14m44s / 14m51s / 3m10s,
    respectively. Full build green, zero `sorry`, standard axioms only; all uninstantiated source
    inputs and constant/endpoint divergences are recorded in `topic-04-cluster-density.md`.

77. **Unconditional Chapter 4 animal and differentiability theorems (2026-07-10).** Replaced the
    conditional 4.20/4.31 endpoints by concrete source-facing declarations. `CubicBondAnimal` and
    its exact cluster cylinders discharge (4.25); `cubicAnimal_largeDeviation_sharp_one_le` proves
    Grimmett's prefactor and exponent for every `n ≥ 1`, with `x ≤ 1/100` as an explicit witness
    for the book's uniform small-`x` range. `concreteClusterDensitySeries_eq_openClustersPerVertex`
    identifies the actual coefficient series, while
    `concreteClusterDensitySeries_contDiffOn_unitInterval` proves `C¹` on `[0,1]`: sharp 4.20
    controls the interior, a two-sided animal majorant handles `p=0`, and periodic component counts
    plus a square detour handle `p=1`. Theorem 4.2 remains conditional exactly as recorded on the
    Chapter 4 comparator card.

78. **Grimmett Chapter 5 exponential decay (2026-07-10).** Added the complete selected Chapter 5
    scope in `Percolation/Critical/`: the cubic L¹ metric/radius/susceptibility layer; finite
    two-edge Menger and pivotal-sausage exploration; finite Wald renewal comparison; direct
    Lemmas 5.12, 5.17, 5.24 and master inequality (5.22); Menshikov's source-order proof of
    Theorem 5.4 and its 5.2/5.7 consequences; right continuity and Theorem 5.8; the mixed
    edge/green product model and equations (5.42)–(5.47); periodic cubic tori, inhomogeneous BK,
    concrete torus animals, and Appendix I limits (5.64)–(5.66); infinite-volume Lemmas 5.51 and
    5.53; Proposition 5.49; Theorem 5.48; and the independent ghost-field proof of Theorem 5.2.
    The public threshold theorem proves (5.3). Both routes are assumption-free, all headline axiom
    audits use only `propext`, `Classical.choice`, and `Quot.sound`, and the full measured ledger is
    in `audit/topics/topic-05-exponential-decay.md`.

79. **Grimmett Chapter 6 exponential decay and analyticity (2026-07-10).** Added the complete
    declared Chapter 6 scope: coordinate-box geometry and decay rate; Theorems 6.1, 6.10, 6.14,
    6.44, corrected 6.75, 6.78, and 6.108; Propositions 6.47 and 6.49; finite correction of Lemma
    6.87, Lemmas 6.89 and 6.102; tree-graph/skeleton moment estimates (6.93)–(6.97); exact finite
    cluster-size rates; and genuine complex animal-series proofs of analyticity for `κ` and `χ`.
    The literal all-`n≥1` reading after 6.75 and the infinite-terminal reading of 6.87 are false
    and are preserved as rejected anti-targets with proved corrected theorems. The automated review
    records application tests, counterexamples, a 39-declaration axiom audit, a failed first pass
    and repair rerun, and the unavailable local Comparator prerequisite. Standard axioms only.

80. **Grimmett Lemma 7.24, adaptive site exploration (2026-07-12).** Added the rooted
    site-percolation, finite induced-site, region-shell, history-embedding, and finite/ambient
    compatibility layers needed to prove the source exploration lemma without a whole-output
    domination assumption. The public theorems
    `cubicRegionSiteExploration_infinite_probability_pos_of_adaptiveLowerBound` and
    `cubicRegionSiteExploration_hasInfiniteSiteCluster_probability_pos_of_adaptiveLowerBound`
    start from an exact ratio-free success lower bound after every post-root history, transport
    finite Bellman bounds through induced metric balls, and conclude respectively that the
    explored occupied set and its root component are infinite with positive probability. Null
    histories require no division, the root-open convention is explicit, the full build passes,
    and the transitive axiom audit contains only `propext`, `Classical.choice`, and `Quot.sound`.
    Chapter 7 remains in progress; the concrete Grimmett--Marstrand history law required by
    Theorem 7.2 is the next target.

81. **Chapter 7 dynamic reveal-fiber freshness (2026-07-12).** Added the exact internal-edge
    support of a frozen explored region and proved it disjoint from the boundary/exterior/seed
    support read by the next restart, both in the reference frame and after signed-direction
    transport. The common-uniform-label event reconstructing the region is measurable on those
    internal coordinates. Its intersection with the closed-boundary event is exactly the full
    explored-region fiber. Impossible finite indices are filtered by a proved realizability
    predicate, every actual schedule cell is valid, and the factorization is transported to an
    arbitrary block center and signed direction. The constructor
    `PartitionedOrientedRestartStage.ofOrientedScheduleRealization` now builds a complete stage
    from any finitely supported outer history known fresh from the current restart. This removes
    the random-region semantic gap in Theorem 7.2; proving that global freshness property for the
    actual adaptive coarse history remains.

82. **Chapter 7 adaptive-history support calculus (2026-07-12).** Added the literal finite
    union of coordinate supports read while replaying an adaptive Boolean history. Pointwise
    answer-fiber support certificates now imply coordinate-sigma measurability of the complete
    exact history cell. A recursive freshness predicate proves that if every earlier prefix
    query is fresh from the current restart, then their whole union is fresh. This reduces the
    remaining Theorem 7.2 history-law gap to the concrete block-placement disjointness proof.

## Axiom Ledger

Empty.

## Anti-Library

- **Reimer's inequality (Grimmett Thm. (2.19), p. 39).** Rejected as a formalization
  target (2026-07-04): the source states it without proof, citing Reimer (1997), and no
  Chapter 2–11 result needs it — the increasing-event case is exactly the BK inequality,
  and the `A □ B = A ∘ B` reduction for increasing events is proved
  (`disjointOccurrence_eq_openWitnessDisjointOccurrence`). Lesson: when the book itself
  defers a proof, record an anti-target instead of importing research-level scope.
