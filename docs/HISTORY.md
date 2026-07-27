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
    query is fresh from the current restart, then their whole union is fresh. Later direct
    source review showed this is a sufficient special case, not the final Theorem 7.2 route:
    equations (7.31)--(7.34) intentionally reuse some coordinates at larger thresholds.

83. **Chapter 7 multi-restart outer-history support (2026-07-12).** Added the finite union of
    supports read by the first `j` restart stages and combined it with the exact adaptive coarse
    history support. The literal outer event appearing in the partitioned-program equation is
    measurable on this union. A bundled freshness predicate proves the genuinely disjoint case.
    It is not applied to overlapping source stages: those require the current-coordinate interval
    information to be factored into the reveal cell before an independence argument.

84. **Chapter 7 explicit LSS numerical parameters (2026-07-12).** Formalized the parameter
    choice behind (7.114)--(7.115). For any desired iid density `q<1` and finite dependence
    neighbourhood cardinality `B`, the explicit auxiliary choice `a=p=(1+q)/2` has product at
    least `q`; an explicit marginal threshold strictly below one makes both source inequalities
    hold uniformly. The probabilistic dilution induction of Theorem 7.65 remains separate.

85. **Chapter 7 measurable LSS dilution (2026-07-12).** Defined the law of `Z^pY` as the
    pushforward of the product of an arbitrary site law and an independent iid Bernoulli law.
    Its one-site marginal is the original marginal multiplied by `p`. The canonical coupling
    pairs `Y` with the subset `Z^pY`, proving the exact stochastic comparison `Y ≥st Z^pY`
    used before (7.116). The reverse comparison with iid density `ap` remains the LSS induction.

86. **Chapter 7 event form of finite sequential domination (2026-07-12).** Identified the
    atomic `boolPrefixMass` and `boolPrefixOpenMass` definitions exactly with probabilities of
    literal finite prefix events. The finite ratio-free criterion (7.64) is now available as an
    iff in event language, including null histories.

87. **Chapter 7 dilution-to-sequential bridge (2026-07-12).** Encoded (7.117) as a ratio-free
    lower bound for the original next coordinate after an exact diluted prefix and separated the
    independent current retention-bit factor. Proved that these two statements imply the finite
    sequential lower bound for `Z^pY` at density `ap`. The LSS induction must now derive the first
    premise from `k`-dependence; iid coordinate independence must discharge the second.

88. **Chapter 7 automatic LSS retention factorization (2026-07-12).** Proved by finite Fubini
    and coordinate-sigma independence that an exact diluted prefix uses only earlier retention
    coordinates, so the current retention bit contributes exactly the factor `p`. Consequently
    (7.117) alone now yields the finite sequential lower bound for `Z^pY`; the remaining LSS
    probability step is precisely the induction deriving (7.117) from finite-range dependence.

89. **Chapter 7 source-faithful LSS history partition (2026-07-12).** Encoded the exact
    `N⁰ ∪ N¹ ∪ M` split from (7.119)--(7.122), proved its disjointness and neighborhood
    cardinal bound, and decomposed every diluted-history cylinder into product-zero, original-one,
    independent-retention-one, and far-history factors. The proof also formalizes `B⁰ ⊆ A⁰`
    and the far-coordinate support statement. No conditional-probability claim is attached to
    this checkpoint; the strong induction and its measure inequalities remain next.

90. **Chapter 7 LSS far-history and retention-zero factors (2026-07-12).** Proved the
    ratio-free content of (7.120) directly from `KDependent`: after fixing the auxiliary field,
    a far diluted-history section reads only coordinates beyond distance `k`, so the current
    original bit factors exactly. The marginal hypothesis then supplies the `1-δ` bound.
    Separately, coordinate independence gives the exact `(1-p)^|N⁰|` factor in (7.121), with
    explicit density-zero and density-one behavior. The `A¹` lower bound (7.122) and the strong
    induction assembling (7.117) remain.

91. **Chapter 7 LSS original-one induction kernel (2026-07-12).** Proved the exact
    `p^|N¹|` factor for independently retained original-one conditions and identified this event
    with the enlarged diluted history used by the source. For positive retention density, these
    factors cancel on both sides of each strictly smaller instance of (7.117). Finset induction
    then proves the complete multiplicative estimate (7.122), including the empty-`N¹` endpoint.
    This is an induction kernel: the outer strong induction establishing (7.117) from
    (7.119)--(7.121) is still required before Theorem 7.65 is complete.

92. **Chapter 7 mixed LSS exponent comparison (2026-07-12).** Proved the scalar step that
    closes the source induction after the neighborhood partition: if the two endpoint bounds
    (7.114)--(7.115) hold and `|N⁰|+|N¹|≤B`, then `1-δ` is bounded by
    `(1-a)(1-p)^|N⁰|a^|N¹|`. The proof handles both possible orders of `1-p` and `a` and
    uses the antitonicity of powers on `[0,1]`; no hidden comparison between those bases is
    assumed.

93. **Chapter 7 finite-volume LSS theorem (2026-07-12).** Completed the outer strong
    induction (7.117). The proof combines the exact `N⁰/N¹/M` partition, `k`-dependent
    far-field factorization (7.120), retention-zero factor (7.121), original-one induction
    (7.122), and the mixed exponent comparison, then restores the canceled `N¹` retention
    bits. Exact Boolean prefixes are identified with the general finite constraint event, so
    the result feeds the finite sequential criterion and proves `finite_lssDomination` with
    the explicit parameter choice (7.114)--(7.115). The remaining Theorem 7.65 work is the
    countable finite-prefix/projective lift, not the finite LSS probability argument.

94. **Chapter 7 countable LSS finite-cylinder lift (2026-07-12).** Introduced a prefix
    dependency graph that joins two enumerated sites exactly when their original distance is
    at most `k`; unlike the induced prefix graph, this cannot miss a short path leaving the
    prefix. Proved that prefix laws are one-dependent on this graph, preserve one-site
    marginals, and commute exactly with independent dilution. Consequently every increasing
    finite-cylinder event satisfies the LSS iid lower bound. The remaining headline 7.65
    obligation is the regularity/monotone-class extension to every bounded increasing
    measurable observable in the definition of `StochasticallyDominates`.

95. **Chapter 7 cubic LSS neighborhood adapter (2026-07-12).** Instantiated the abstract
    prefix dependency graph on `ℤ^d`. The graph-metric ball of radius `k` covers every
    dependence neighbor and has cardinality at most `3^d(k+1)^d`, yielding a concrete
    `cubic_lss_finiteCylinder_measureReal_le` theorem with no ad hoc prefix-cardinality
    hypothesis. This is the form needed by finite-support good-block crossing events.

96. **Chapter 7 good-block LSS application (2026-07-12).** Combined stationarity of the
    `ε`-good block field, its proved `3d`-dependence, and the cubic neighborhood bound. A
    single origin marginal bound now implies iid domination for every increasing
    finite-cylinder event of the good-block law. This closes the precise LSS input needed by
    finite coarse crossing events while keeping the still-missing all-observable extension of
    headline Theorem 7.65 explicit.

97. **Chapter 7 source-style finite-cylinder LSS threshold (2026-07-12).** Repackaged the
    explicit parameter choice as the source quantifier order: for every requested iid density
    `q<1`, there exists a marginal threshold `δ<1` which works uniformly for every
    `k`-dependent law and every increasing finite-cylinder event. A cubic corollary hides both
    the enumeration and the `3^d(k+1)^d` neighborhood bound. This is not labelled as the full
    expectation-form Theorem 7.65.

98. **Chapter 7 planar good-block slice crossing (2026-07-12).** Embedded the square lattice
    into the first two coarse coordinates, proved exact preservation of iid site-crossing
    probabilities, and applied the good-block LSS theorem to the resulting finite-cylinder
    event. A deterministic companion maps the witnessed square walk into `ℤ^d` and lifts it
    through neighboring selected good clusters to an actual open-bond connection between the
    endpoint block faces. This formalizes the LSS/path-lifting core of (7.73)--(7.74); the
    exponential site-crossing input (7.70) remains.

99. **Chapter 7 full LSS stochastic domination (2026-07-12).** Closed the semantic gap between
    finite-cylinder inequalities and Grimmett's expectation definition. Configurations are
    transported measurably to the compact Boolean product space; inner/outer regularity and two
    finite-subcover arguments insert an increasing finite union of positive cylinders between
    compact and open approximants. This proves the countable sequential criterion (7.64), the
    full fixed-target `lss_stochasticallyDominates` and `exists_lssDominationThreshold`, with
    cubic and stationary good-block corollaries. A test applies the theorem to the increasing
    event of infinitely many occupied sites, which cannot have finite support. This work occurred
    after the tracker pause and therefore has no measured theorem telemetry.

100. **Chapter 7 literal function-valued LSS theorem and adversarial repair (2026-07-12).** An
    independent read-only review correctly rejected the earlier claim that
    `∀ q < 1, ∃ δ < 1` had the literal quantifier order of Theorem 7.65. The repair constructs
    one explicit monotone `lssDominationDensityUnit B : I → I`, proves its limit is one at input
    density one, and proves simultaneous stochastic domination for every input density. The
    zero-output branch is the universal all-closed comparison; the input-one branch proves that
    countably many unit marginals concentrate the law on the all-open configuration. The failed
    first-pass report is preserved unedited in the review record. This repair occurred after the
    tracker pause and has no measured theorem telemetry.

101. **Chapter 7 site-crossing closed-frontier kernel (2026-07-12).** Defined the set of open
    rectangle vertices reachable from the left face and its corrected internal outer boundary.
    The boundary includes closed left-face sites when no open site is reachable, so the fully
    closed configuration is handled rather than producing an empty separator. Every boundary
    site is proved closed, and every rectangle-confined left-right walk is proved to meet the
    boundary whenever the site crossing fails. The remaining deterministic part of (7.70) is the
    planar extraction of a top-bottom star-lattice path from this separator. This post-pause work
    has no measured telemetry.

102. **Chapter 7 degree-eight star-walk code (2026-07-12).** Constructed the square star lattice
    as the exact `L∞`-distance-one graph, proved its neighbor set is the radius-one coordinate box
    with the center erased and hence has degree eight, and fixed a reversible direction-word code
    for every star walk. The counted self-avoiding length-`n` codes have cardinality at most
    `8^n`. This is the literal combinatorial factor needed after the top-bottom closed-star-path
    extraction in (7.70). This post-pause work has no measured telemetry.

103. **Chapter 7 closed-star-path Peierls probability bound (2026-07-12).** For a fixed start,
    defined the finite union of events that a counted self-avoiding length-`n` star walk is closed.
    Its support has exactly `n+1` distinct sites, each event has mass `(1-p)^(n+1)`, and the
    degree-eight code count yields the explicit bound `8^n(1-p)^(n+1)`. The probability half of
    the high-density site crossing estimate (7.70) is now complete; the top-bottom star-path
    extraction remains. This post-pause work has no measured telemetry.

104. **Chapter 7 high-density site-crossing estimate (7.70) (2026-07-15).** Constructed the
    finite framed primal interface between vertices reachable from the left and its complement,
    mapped it to the shifted-dual square lattice, and proved the interior-degree and boundary
    parity statements needed by the handshaking argument. A failed left-right crossing therefore
    supplies a bottom-top self-avoiding star path of closed sites. Combining this certificate
    with the degree-eight path count proves the explicit failure bound
    `(2n+1) * 8^(2n) * (1-p)^(2n+1)` for a square and the source-facing estimate
    `P_p(A_n) ≥ 1 - exp (-ρ n)` above a concrete `α < 1`, with a positive rate uniform in `p`.
    This post-pause work has no measured telemetry.

105. **Chapter 7 multi-slice crossing and sprinkling kernel (7.72–7.75) (2026-07-15).**
    Embedded a source-aligned family of planar good-block slices in `B(N(K+1))`, proved their
    queried bond-coordinate supports pairwise disjoint, and multiplied the single-slice LSS
    estimate to obtain the ambient-box exponential crossing bound (7.74). Constructed the finite
    induced open-box graph, proved its edges embed injectively into cubic bond coordinates, and
    established the exact equivalence between crossing-event Hamming depth `s` and `s+1`
    edge-disjoint left-right crossings by arbitrary terminal-set Menger. This yields the ACCFR
    sprinkling product bound (7.75) and a guarded maximum with correct radius-zero and closed-box
    behavior. Source review exposed a printed-index issue in dimensions above three: divisibility
    of only one transverse coordinate does not imply disjoint thickened slices, so the formal
    family separates every transverse coordinate while preserving order `K^(d-2)`. The final
    proportional-threshold and arbitrary-radius optimization for Theorem 7.68 remains. This
    post-pause work has no measured telemetry.

106. **Chapter 7 aligned surface-order many-crossings estimate (2026-07-15).** Optimized the
    ACCFR factor in (7.75) at the integer threshold
    `⌊β(N(K+1))^(d-1)⌋`, proved explicit positive density and exponential-rate constants, and
    converted the result to the literal source event comparing the real-coerced maximum crossing
    count with `βr^(d-1)`. An explicit cofinal block threshold removes the nonzero-floor side
    condition. Thus Theorem 7.68 is complete on all sufficiently large aligned radii; deriving
    its hypotheses from `p>p_c` and treating non-aligned/small radii remain. This post-pause work
    has no measured telemetry.

107. **Chapter 7 quarter-slab-to-many-crossings composition (2026-07-15).** Fixed a site density
    strictly between the proved Peierls threshold and one, used the conditional good-box limit
    from Theorem 7.61 to choose an LSS-compatible block scale, and composed it with the aligned
    surface-order estimate. Thus a single strict finite-quarter-slab critical comparison now
    yields the literal aligned Theorem 7.68 inequality with automatically chosen positive
    constants. The remaining probabilistic input is exactly the output expected from Theorem
    7.2; arbitrary radii still require a separate geometric assembly. This post-pause work has no
    measured telemetry.

108. **Chapter 7 dynamic-block bond assembly (2026-07-15).** Proved that positive scale makes
    the `4Nx` site-center map injective, converted infinite-cluster events under the common
    uniform coupling exactly to their Bernoulli bond probabilities, and composed the concrete
    partitioned restart program with the literal thickening. Once the program proves its
    accepted-center open-connection invariant, Lean now supplies root membership, distinct
    anchors, thickening containment, positive bond percolation, and the final critical upper
    bound of Theorem 7.2(a). This early unconditioned `4d` adapter was subsequently superseded by
    the source-counted initialized interface in entry 114. This post-pause work has no measured
    telemetry.

109. **Chapter 7 upper adaptive Bellman comparison (2026-07-15).** Added the ratio-free dual of
    the adaptive lower-bound kernel: an upper mass bound on every true history extension now
    bounds the entire decision tree by its iid continuation value. Specialized recursion on the
    strictly decreasing undecided set yields the corresponding finite site-completion theorem.
    Every sample is proved to select a concrete decision leaf, so the Bellman win event is exactly
    the actual finite target-hit event, rather than merely a subset. This is the reusable
    probabilistic half of Grimmett's bond-to-site comparison needed by Theorem 7.2; the directed
    edge construction remains. This post-pause work has no measured telemetry.

110. **Finite bond-to-site transformation for the Chapter 7 dynamic stack (2026-07-15).**
    Implemented the directed-edge construction behind Grimmett Theorem 1.33 on an arbitrary
    finite simple graph. A boundary exploration now exactly recovers the root's ordinary bond
    component, while its independent directed version reaches only vertices in the copy-zero
    incoming-green site field. Each vertex answer reads a finite block of incoming darts; an
    occurrence-indexed reserve of independent copies makes every next block fresh even on
    malformed repeated-query histories. The fresh-block factorization proves the ratio-free
    upper adaptive law with density `1-(1-p)^Delta`, and the actual rooted exploration is proved
    state-for-state equal to static site exploration on the physical green field. Consequently
    `setBernoulli_bondHitsTarget_le_rootedCompletion` gives the complete finite-graph comparison,
    including exact removal of the enlarged dummy coordinates. Endpoint and repeated-query tests
    compile, and the transitive axiom audit reports only `propext`, `Classical.choice`, and
    `Quot.sound`. The remaining Theorem 7.2 prerequisite is the increasing finite-ball/infinite-
    volume passage to the site critical-probability inequality. This post-pause work has no
    measured telemetry.

111. **Infinite-volume bond-to-site critical comparison (2026-07-15).** Exposed the exact root
    factor `P(site target hit)=q·P(root-forced completion)` and strengthened the finite theorem to
    an unconditioned bond-to-site inequality. Removed dummy nonedges, embedded actual induced-ball
    edges into `CubicEdge d`, and proved that an infinite regional bond cluster crosses every
    finite metric shell. The matching antitone site-shell exhaustion converts the resulting
    uniform finite lower bound into a rooted infinite site cluster. This proves
    `siteTheta_densityI_pos_of_regionCriticalProbability_lt` at
    `q=1-(1-p)^(2d)` and the strict critical adapter
    `siteCriticalProbability_lt_one_of_regionCriticalProbability_lt_one`. The dynamic-block
    assembly now discharges its former site-critical premise automatically from `p_c(F)<1`.
    Endpoint tests compile and all new transitive axiom audits contain only `propext`,
    `Classical.choice`, and `Quot.sound`. This post-pause work has no measured telemetry.

112. **Pathwise dynamic-restart certificate (2026-07-15).** Proved the deterministic content
    missing between Lemma 7.17's success event and Theorem 7.2's bond-path invariant. Reachability
    in an induced finite open box now converts back to a box-supported ambient open walk. A
    successful threshold increment gives a final-density connection from the explored region to
    a genuinely seeded target; when the region is the heterogeneous explored component, this
    connection begins at an inlet-seed vertex. Signed-coordinate/translation transport gives the
    literal physical connection used by oriented reveal cells, and those automorphisms map the
    reference box-edge support exactly onto the physical centered box. The remaining work is to
    compose these per-cell extensions through the concrete source-counted program and identify
    its final target seed with the neighboring coarse-site seed. Post-pause telemetry remains
    unmeasured.

113. **Source-faithful steering frames and finite seed witnesses (2026-07-15).** Source inspection
    of pp. 159--162 exposed that an exit direction alone is insufficient: the construction also
    reverses selected transverse coordinates. Added full signed restart frames, proved exact
    transport of box-edge supports, identified the first reversed quadrant with `T*(n)`, and
    formalized the later inlet-compensating sign condition. Restart events, history cells,
    ratio-free probability bounds, and pathwise certificates now transport through the complete
    frame; the old oriented API is proved to be its no-transverse-flip specialization. A finite
    deterministic witness table now retains both the successful boundary contact and its actual
    open seed center, depends on no labels beyond `seedConnectionSupport`, and is packaged with
    the explored-region/multiplicity cell. Thus a subsequent stage can compute its physical seed
    center and compensating sign mask from revealed finite data. Application tests compile and
    the new declarations use only standard axioms. The remaining Theorem 7.2 work is the global
    source-counted non-root stage schedule, its interval-fiber reuse proof, and the accepted-center
    path induction.
    This post-pause work has no measured telemetry.

114. **Source-counted non-root blocks and positive root initialization (2026-07-15).** A direct
    audit of pp. 156--162 corrected the provisional `4d` narrative. The root has one simultaneous
    `2d`-branch event with factor `1-2dε` and then `2d` extensions; every later coarse site uses
    exactly two inlet extensions and `2d-1` fresh branches, hence `2d+1` Lemma 7.17 factors. Added
    the corresponding strict numerical theorem and changed the reusable non-root program and
    bond-assembly adapters to that exact count. The root seed/root branches are now represented
    by a positive measurable outer initialization event. Ratio-free history inequalities inside
    this event are converted to Lemma 7.24 through an actual conditional probability measure,
    and the resulting positive initialized infinite exploration is passed to bond percolation and
    the critical-probability conclusion. No null history is divided by its mass. The concrete root
    event and non-root interval-fiber schedule remain to be constructed. This post-pause work has
    no measured telemetry.

115. **Literal common-radius root radial construction (2026-07-15).** Strengthened seed amplification
    so one inner/outer radius pair works simultaneously for every coordinate face, and packaged
    the resulting all-coordinate, all-admissible-region ratio-free Lemma 7.17 bounds. Proved that
    the central box together with its exterior vertex boundary avoids every target quadrant at
    these radii. Defined the common-uniform central-seed event and every signed root branch,
    proved the seed support is disjoint from each framed restart support, and factored each
    branch inequality through the exact positive seed mass. The `2d` branch intersection now has
    the source factor `1-2dε`; `exists_dynamicBlockRestartPackage` returns the same radii with
    both the positive literal radial event and the uniform bounds needed by later blocks. Oracle
    tests and transitive axiom audits compile with only `propext`, `Classical.choice`, and
    `Quot.sound`. A subsequent line-by-line source check showed that this is only the first root
    phase; the root still needs `2d` post-radial extensions before it is occupied. This post-pause
    work has no measured telemetry.

116. **Two-phase root correction and exact completion law (2026-07-15).** Corrected the public
    vocabulary after checking equations (7.30)--(7.33): the central seed and `2d` radial targets
    form `rootRadialEvent` with factor `1-2dε`, while the root becomes occupied only after one
    further extension from each selected radial seed. Added `RootExtensionProgram`, whose exact
    prefix partitions imply the second factor `(1-ε)^(2d)`, positivity of the completed event,
    and `CompletedRootBlockPackage` for feeding only that completed event to the initialized
    exploration. No concrete post-radial interval-fiber stage is assumed by this interface; that
    construction and the later-site `2d+1` program remain. This post-pause work has no measured
    telemetry.

117. **Full-frame finite restart partitions (2026-07-15).** A semantic audit found that the
    earlier partitioned program stored only the signed exit coordinate even though pp. 159--162
    choose an additional transverse steering mask. Added `PartitionedFramedRestartStage`, its
    exact and validity-filtered finite-realization constructors, and its null-safe summed
    Lemma 7.17 bound. The initialized `2d+1` program and the completed-root interface now use
    full `FramedRestartQuery` data at every stage. The same audit moved the all-transverse `T*`
    reversal from the simultaneous radial phase to the subsequent root extension, matching the
    literal order on pp. 157--160. This post-pause work has no measured telemetry.

118. **Source-order schedules and actual-seed steering (2026-07-15).** Encoded the literal
    post-radial root order of `2d` signed directions and the later-site order of two inlet
    extensions followed by the `2d-1` non-backtracking branches. Both concrete support lists
    have the source overlap bound `2d+1`. Added full-frame exact reveal-cell transport, including
    the explored-region fiber and boundary-history factorization. The radial event now selects
    a finite witness profile containing one actual seed in every signed direction. A new
    coordinate theorem derives the axial identity and transverse bounds of an arbitrary selected
    seed directly from `SeedBoxWithinBoundaryLayer`; consequently every selected seed's `T*`
    restart—not a canonical substitute—lies in the prescribed two endpoint boxes. The composed
    certificate supplies all selected seeds, their final-density central connections, and their
    steering containments simultaneously. The remaining dynamic gap is the algorithm-specific
    interval-fiber factorization for label coordinates deliberately reused at increased
    thresholds, followed by the accepted-center path induction. This post-pause work has no
    measured telemetry.

119. **Reused-coordinate interval histories (2026-07-15).** Added
    `FiniteRevealIntervalProfile`, which records separately the finite edges known
    `beta`-closed and `gamma`-open, proves the exact decomposition obtained by peeling a
    current closed boundary from an earlier history, and isolates the residual freshness
    obligation. `DynamicFramedRevealIntervals` transports the boundary thresholds through a
    full restart frame and constructs a complete finite framed-stage partition from exact
    interval fibers. The regression and transitive axiom audits pass with only the standard
    axioms. Concrete equations (7.31)--(7.32), including their edge-set update and geometric
    residual-freshness invariant, remain to be instantiated. This post-pause work is recorded
    as unmeasured rather than assigned reconstructed telemetry.

120. **Literal first edge update and interval realization (2026-07-15).** Instantiated the
    source edge-line graph, finite reachable closure, `E₁`, `ΔE₁`, `E₂`, and `ΔE₂`. Direct
    inspection of printed page 158 corrected an OCR reversal in (7.31): an unabsorbed old
    boundary edge receives `β₁(e)+δ`, while a genuinely new boundary edge receives `p`.
    Equations (7.31)--(7.32) are now exact first-update declarations, and the closure proof
    establishes the full semantic interval cell: absorbed exits are open below the incremented
    threshold, newly explored interior edges are open below `p`, rejected exits are closed at
    the incremented threshold, and new line-boundary edges are closed at `p`. The root-specific
    line boundary is proved to lie in the Lemma 7.17 vertex boundary, so every realization of
    `rootRadialEvent` belongs to the resulting post-radial interval profile. The same proof is
    generalized to the source's edge-dependent `β_k(e)+δ`: `FiniteEdgeRevealState` derives its
    boundary from the line graph, proves the two closed-support cases equal the entire successor
    boundary, and carries realizations through arbitrary finite recursive updates. Regression
    and transitive axiom audits use only `propext`, `Classical.choice`, and `Quot.sound`.
    Attaching these recursive states to the concrete post-radial/later-site steering schedules
    and proving accepted-center induction remain. This post-pause work is unmeasured; no
    telemetry was reconstructed.

121. **Global-boundary source recursion and framed-stage adapter (2026-07-15).** A second
    line-by-line audit corrected an overstatement in the preceding entry: the finite helper
    `FiniteEdgeRevealState` derives a boundary only inside one fixed ambient support, whereas
    Grimmett's `ΔE_k` is the boundary of `E_k` in the whole cubic edge-line graph and the
    finite region `E_Z` changes with the stage. Added the literal global `cubicEdgeBoundary`,
    proved its intersection with a stage region recovers the local boundary, and introduced
    `SourceFiniteEdgeRevealState`. Its successor reads only active global-boundary exits in the
    current `E_Z`, preserves zero lower thresholds off all previously exposed coordinates, and
    carries exact interval realizations through changing regions with explicit probability-one
    nonnegative-label cylinders. The special root radial exploration is now proved equal to
    this source successor on its active support. Finally,
    `PartitionedFramedRestartStage.ofSourceEdgeStateRealization` peels exactly the intersection
    of the global boundary with a framed query and proves all residual closed constraints fresh
    automatically. Concrete steering geometry must still identify that intersection and prove
    the exact realization fibers at every root-extension and later-site stage. Regression tests
    and transitive axiom audits pass with only `propext`, `Classical.choice`, and `Quot.sound`.
    This post-pause work is unmeasured; no telemetry was reconstructed.

122. **Endpoint-fresh canonical source stages (2026-07-15).** The source-shaped framed query
    is now constructed directly from a `SourceFiniteEdgeRevealState`: its random vertex region
    is the endpoint set of the explored edges pulled back through the steering frame, and its
    boundary threshold is the state's physical lower threshold under that same frame. Exact
    edge-line-boundary and exterior-edge arguments prove that the query boundary is precisely
    `ΔE_k` intersected with the current restart support; internal closed chords are therefore
    excluded exactly as on printed pp. 159--160. More importantly, a single vertex-level
    separation condition—no endpoint of the new target-seed support was previously incident to
    an explored edge—now implies both target-boundary freshness and disjointness of all earlier
    open edges from the restart. The fully reduced canonical partition constructor consequently
    asks the steering layer only for this source statement, the exact finite history fiber, and
    the already-proved Lemma 7.17 probability bound. Regression examples compile and all new
    transitive audits contain only `propext`, `Classical.choice`, and `Quot.sound`. The remaining
    dynamic task is to prove this endpoint separation for the concrete source-order placements
    and construct their exact state fibers. This post-pause work is unmeasured; no telemetry was
    reconstructed.

123. **Exact target support and first concrete post-radial freshness (2026-07-15).** A source
    audit found that `seedConnectionSupport` still contained seed boxes around every center in
    a coarse ambient box, including centers that cannot satisfy the defining
    `SeedBoxWithinBoundaryLayer` certificate. That set was a valid measurability over-support but
    was too large for the printed claim that a new target had not been examined. The support now
    ranges only over `seededBoundaryAdmissibleCenters`; every endpoint in the resulting target
    support lies on or beyond the selected `n`-face, and every complete restart support lies in
    `B(n+2m+1)`. The simultaneous root radial support has the same wide-box bound. Combining these
    exact bounds with the selected seed's axial identity proves that the actual source state
    immediately after the radial phase has no endpoint incident to the first post-radial target.
    Consequently its canonical framed query has exactly `Delta E_2` intersected with its restart
    support as boundary and is disjoint from all already explored radial edges. Regression tests
    compile, and the transitive audits for all new declarations contain only `propext`,
    `Classical.choice`, and `Quot.sound`. Sequential separation after earlier root extensions and
    the exact finite state fibers remain. This post-pause work is unmeasured; no telemetry was
    reconstructed.

124. **Sequential freshness for all root extensions (2026-07-15).** The restart support now
    carries its sharp anisotropic geometry: it has the wide `n+2m+1` bound only along its exit
    axis and remains inside `[-n,n]` in every transverse coordinate. This proves pairwise
    separation for distinct selected root directions, including the two opposite signs on one
    axis. Added the literal changing-region recursion through the noduplicated `2d` source
    order, with a state-dependent threshold policy. An induction over every prefix proves that
    the next target is endpoint-fresh; hence at every root slot the framed query boundary is
    exactly the current global `Delta E_k` intersected with its restart support, and no explored
    open edge is reread. Regression examples compile, and all new transitive axiom audits use
    only `propext`, `Classical.choice`, and `Quot.sound`. Exact probability-one interval fibers
    through the completed root run and the later-site accepted-center induction remain. This
    post-pause work is unmeasured; no telemetry was reconstructed.

125. **Root-schedule interval preservation and exact stage adapter (2026-07-15).** Added an
    induction that preserves the literal source lower/upper interval profile through the
    state-dependent `2d` root-extension run. The common-uniform label space now has an explicit
    measurable event on which every coordinate is nonnegative; its coupling probability is
    proved to be one by the countable infinite-product formula, so one support hypothesis
    discharges every random new-boundary side condition. Consequently the radial event
    initializes the exact completed-root profile on that probability-one support. For every
    root slot, a new finite-cell constructor takes representative interval fibers and the
    ratio-free Lemma 7.17 estimate, obtains both freshness obligations from the sequential
    steering theorem, and proves that its framed cells cover the supplied prefix history
    exactly. A canonical total threshold policy implements `beta(e)+delta` on budget-valid
    states without clamping junk values. Regression tests compile, and the new transitive axiom
    audits contain only `propext`, `Classical.choice`, and `Quot.sound`. Constructing the actual
    finite realized-cell family for every prefix and the later-site accepted-center induction
    remain. This post-pause work is unmeasured; no telemetry was reconstructed.

126. **Canonical interval-profile classifier (2026-07-15).** A finite pairwise-disjoint
    family of interval profiles covering a history now canonically classifies every realization:
    each profile event is proved equal to the corresponding exact classifier fiber. The root
    extension constructor uses this theorem directly, so a concrete source stage no longer has
    to invent a `realizedCell` function or prove all of its fibers separately; it supplies only
    the finite profile partition and the ratio-free Lemma 7.17 estimates. The resulting stage is
    proved to retain exactly the complete supplied history. Regression compilation and
    transitive axiom audits pass with only `propext`, `Classical.choice`, and `Quot.sound`.
    Establishing finiteness, coverage, and disjointness for the actual root-prefix state family
    remains substantive work rather than being hidden in a classifier hypothesis. This
    post-pause work is unmeasured; no telemetry was reconstructed.

127. **Current-state versus accumulated-history interval cells (2026-07-15).** An adversarial
    review of the source recursion found that the previous `profile` should not be described as
    the full reveal history: when an old boundary edge is absorbed into the explored set, that
    current-state profile retains its new upper threshold but no longer states the old lower
    threshold. Added `SourceFiniteEdgeRevealState.historyProfile`, whose closed support is the
    union of explored and boundary edges, and proved that one source update preserves this
    stronger accumulated cell on the probability-one common-uniform support. The ordinary
    `profile` remains useful and is now proved to be a deterministic Markov cell: every label
    realization in a successor profile reproduces the same reachable closure and the entire
    successor state. All source-state framed-partition and root-extension adapters now use
    `historyProfile`; the fixed-ambient `FiniteEdgeRevealState` adapters correctly continue to
    use their original profile. Regression examples compile, and the transitive axiom audit for
    the closure, stability, history-preservation, and completed-root declarations contains only
    `propext`, `Classical.choice`, and `Quot.sound`. This post-pause work is unmeasured; no
    telemetry was reconstructed.

128. **Canonical finite partition of reachable root-prefix states (2026-07-15).** Proved that
    one source update has finite range whenever its input state ranges over a finite set, and
    iterated this through the literal state-dependent root-extension schedule. Membership in a
    reachable state's accumulated `historyProfile` now reproduces the entire remaining schedule,
    so distinct reachable states have disjoint accumulated-history cells. Packaged the resulting
    finite range as `RootExtensionPrefixStateIndex`, selected canonical representatives, and
    constructed `rootExtensionPrefixHistory` as the pairwise-disjoint union of all reachable
    cells. The radial-success event on the probability-one nonnegative coupling support is proved
    to lie in this union, and `partitionedRootExtensionStageOfReachableHistory` generates the
    corresponding exact finite classifier and framed stage without user-supplied realization
    witnesses. Steering geometry was also separated from random realization, since prefix
    finiteness and freshness depend only on the retained seed-box geometry. Regression tests and
    the full repository build pass; every new transitive axiom audit contains only `propext`,
    `Classical.choice`, and `Quot.sound`. The remaining source-fidelity obligation is sharper than
    mere coverage: prove that the selected radial-success history is itself a union of these
    accumulated-history cells, or refine the finite index by the selected radial witnesses. Only
    then may the exact radial history be composed through all root stages and the accepted-center
    induction. This post-pause work is unmeasured; no telemetry was reconstructed.

129. **Adversarial refinement of the radial-success history (2026-07-15).** Added a generic
    finite threshold-pattern refinement for interval profiles and proved exact event semantics,
    realized-cell membership, and disjointness.  Specialized stability theorems show that the
    radial event and its canonical selected seeds are determined by the background, first
    increment, and final-density Boolean patterns on the finite radial support.  This yields a
    finite family of compatible refined cells whose union is exactly the radial-success event
    with a prescribed selected-seed profile after intersection with the probability-one
    nonnegative coupling support.  Regression examples compile, the dependency build passes,
    and every new transitive axiom audit contains only `propext`, `Classical.choice`, and
    `Quot.sound`.  A second review deliberately tried to feed these cells into the conditional
    restart constructor and rejected that step: a full radial-support pattern can constrain a
    later restart coordinate and can raise the closed lower bound on its current boundary, so it
    is not the residual-fresh source history required by Lemma 7.17.  The refinement remains a
    valid semantic oracle and counterexample detector.  Added the source-faithful replacement:
    `stableRootExtensionPrefixHistory` filters the unchanged canonical state cells by semantic
    containment, proves their exact-union and pairwise-disjointness laws, and constructs the
    corresponding framed stage while reusing the established boundary thresholds and freshness.
    The central-seed half of that local theorem is now proved: every realization in the
    post-radial accumulated cell keeps the original seed open at density `p`, and the property
    propagates through every root-prefix history cell.  Exact root composition is therefore
    reduced to preservation of a directional restart witness on each canonical reachable cell.
    This post-pause work is unmeasured; no telemetry was reconstructed.

130. **Source-faithful radial witness stability on unchanged history cells (2026-07-15).**
    Proved generic line-graph closure transport along an open cubic walk and through every edge
    of an entered coordinate box.  Signed root-frame lemmas then classify transported boundary,
    exterior-walk, outward, and seed edges in the physical simultaneous radial reveal.  Every
    successful directional radial branch consequently supplies an explicit explored
    certificate consisting of its last exit, its original exterior walk, its outward edge, and
    every edge of one target seed.  The accumulated source history keeps the exit open at the
    first increment and all exterior/seed coordinates open at density `p`, so directional
    success—and hence the complete radial event—is constant on each unchanged post-radial cell.
    The result propagates through every root-prefix history.  Finally,
    `stablePrefixHistory_inter_nonnegative_eq_rootRadial` proves that the unchanged stable-cell
    union, restricted to the probability-one common-uniform support, is exactly radial success.
    This closes the semantic stability gate without exposing any extra restart coordinate or
    strengthening any boundary threshold.  Executable regression cases compile, and transitive
    audits for the closure, certificate, branch stability, prefix stability, and exact identity
    contain only `propext`, `Classical.choice`, and `Quot.sound`.  Root completion must now compose
    these stable framed stages through all `2d` directions before the accepted-center induction.
    This post-pause work is unmeasured; no telemetry was reconstructed.

131. **Arbitrary root-prefix success stability (2026-07-15).**  Proved a generic successor
    certificate showing that a successful source-state framed restart remains successful
    throughout its literal accumulated successor-history cell.  The proof reconstructs the
    same exit, exterior path, outward edge, and target seed from the interval endpoints and
    line-graph closure; it does not reveal an extra coordinate.  Defined the recursive semantic
    predicate `runPostRadialExtensionSuccesses` and proved its append law and stability under an
    arbitrary accumulated prefix cell.  Consequently `rootExtensionPrefixSuccessEvent k`—the
    radial event together with success of the first `k` framed restarts—is constant on every
    canonical `k`-prefix history cell.  Its stable-cell union agrees exactly with that event
    after intersection with the probability-one nonnegative coupling support, for every `k`.
    Executable prefix cases and transitive audits pass with only `propext`,
    `Classical.choice`, and `Quot.sound`; the full repository build is green.  Remaining work is
    genuinely probabilistic and arithmetic: convert these stage-specific almost-sure
    partitions into the `(1-ε)^(2d)` measure recurrence, prove `HasIncrementBudget` on reachable
    states so the canonical policy really adds `δ`, instantiate the cellwise Lemma 7.17 bound,
    and then perform the accepted-center induction.  This post-pause work is unmeasured; no
    telemetry was reconstructed.

132. **Measure composition and reachable root-increment budget (2026-07-15).**  Added a
    probability-one support-transfer lemma and used it to turn the stage-specific stable
    history partitions into an exact one-step probability recurrence for the semantic root
    prefix-success events.  Positivity of the preceding event supplies an actual stable cell,
    so the proof neither assumes a common classifier at every stage nor inserts a junk default
    state.  Iteration gives the literal `(1 - epsilon)^(2 * d)` lower bound after the `2d` root
    extensions.  Separately, proved uniform upper bounds on every reachable lower threshold for
    the canonical clamped policy.  Under the single explicit total-budget inequality, that
    policy therefore takes its exact `+ delta` branch at every reachable prefix.  The semantic
    stability and composition interfaces were correspondingly weakened from the false global
    assertion that every arbitrary state increments exactly to the source-faithful assertion
    `PolicyAddsOnPrefixes` on reachable states.  The final budgeted composition theorem compiles,
    and all new transitive axiom audits contain only `propext`, `Classical.choice`, and
    `Quot.sound`.  The remaining local obligation is to instantiate the cellwise Lemma 7.17
    inequality.  A source audit found that the canonical query currently records the entire
    explored endpoint region, which need not lie in the one restart box.  The next proof must
    crop that region (and prove the restart events invariant under cropping) or otherwise prove
    the exact admissibility hypotheses; it may not assert the false whole-region containment.
    Accepted-center induction remains after this local bridge.  This post-pause work is
    unmeasured; no telemetry was reconstructed.

133. **Reachable final-density replay and random-anchor assembly (2026-07-16).** Completed the
    pathwise connectivity layer for the concrete root and later-site runtimes. Successful
    steering slots now preserve a `RootedOpen` invariant: every explored edge is open at the
    supplied final density and every explored endpoint is connected to one physical anchor.
    History replay transports this invariant through the actual finite source states and proves
    that every published outgoing seed is connected to the root. A semantic review rejected the
    false global premise that the total threshold policy is bounded on arbitrary junk states;
    the replacement certificates quantify only over prefixes actually reached by the root run
    and by the realized non-root runtime. The canonical root policy satisfies this prefix bound
    from the explicit arithmetic budget. The infinite-cluster assembly now accepts random
    physical anchors selected by the exploration instead of incorrectly identifying them with
    deterministic coarse-site centers. Finally, every non-initial limiting occupied site is
    traced to its first successful finite query, and initialized histories are split into the
    forced root prefix plus the exact realized suffix event. Targeted builds and the transitive
    Chapter 7 axiom audit pass with only `propext`, `Classical.choice`, and `Quot.sound`. The
    remaining Theorem 7.2 certificate must prove injectivity and thickening containment for these
    selected anchors, the concrete non-root `2d+1` overlap budget, and equality between the
    realized exploration state and the corresponding replay state. This work occurred after the
    goal tracker was paused and is therefore unmeasured; no telemetry was reconstructed.

134. **Finite-fibre anchors and exact accepted replay states (2026-07-17).** Repaired two final
    Theorem 7.2 interface gaps found while preparing Chapter 8. Random selected seed anchors no
    longer carry an unnecessarily strong injectivity obligation: an infinite coarse set has an
    infinite physical image whenever every anchor fibre is finite, and uniform containment in a
    radius-`2N` box about the injectively spaced coarse center proves those fibres finite while
    also placing every anchor in `4NF+B(2N)`. Separately, every finite history-dependent site
    execution is now proved equal to the deterministic replay of its realized suffix. The new
    chronological trace certificate proves that every earlier history entry was the actual next
    frontier query. Consequently every non-root vertex in the limiting occupied set has an exact
    finite accepted replay query, belongs to the literal adaptive answer cell, and supplies all
    prefix-admissibility facts required by the final-density replay theorem. The integrated build
    passes without new axioms. The remaining global Chapter 7 obligations are the non-root
    reveal-overlap budget and containment of the replay connection paths inside the thickening.
    The separate Chapter-8-enablement tracker measured this window as 1045 seconds and 443,988
    tokens.

135. **Region-confined dynamic replay and exact root steering support (2026-07-17).** Added a
    region-indexed open-connectivity invariant from individual source edges through root and
    non-root runtime steps, reachable prefixes, and complete deterministic replay.  The root
    phase now has a literal containment theorem in `4NF+B(2N)` whenever the corresponding coarse
    root and signed neighbor are present, using the selected seed's retained boundary-layer
    geometry rather than a deterministic surrogate.  Total later-site witnesses now retain the
    same geometry even on failed restarts, and every framed query has an explicit deterministic
    endpoint-support bound.  The integrated replay-connectivity build passes with standard
    axioms only.  The final Theorem 7.2 certificate still requires the concrete non-root overlap
    budget and the sharper non-root two-endpoint containment; a larger-radius shortcut is invalid
    because changing the thickening radius also changes its dilation centers.

135. **Chapter 8 uniqueness, continuity, and qualitative geometry (2026-07-16).**  Formalized
    the compatible-three-partition lemma and the complete Burton–Keane proof that positive
    percolation probability implies almost-sure uniqueness of the infinite open cluster.
    Finite multiplicities are eliminated by measurable finite-energy splicing; infinite
    multiplicity produces trifurcations, whose exact finite-box incidence count is bounded by
    the boundary.  The common-uniform coupling and uniqueness then prove left continuity of
    `theta` above criticality, completing Theorem 8.8.  The same uniqueness/coalescence layer,
    together with face FKG, proves the qualitative left-right crossing limit of Theorem 8.97.

136. **Chapter 8 finite radius, truncated connectivity, and lower size tail (2026-07-16).**
    Added finite coordinate-box radius and diameter events with exact measurability and positive
    finite-energy witnesses.  A source-faithful shifted gluing inequality and a generic corrected
    quasi-subadditive limit theorem prove Theorem 8.18, including the polynomial-times-exponential
    bound.  Separate even and odd animal splices prove equations 8.59 and 8.60 with their exact
    weights and denominator, and a parity squeeze proves the full Theorem 8.53.  Independently,
    the density-forcing, selected-scale, bounded-radix, and animal-concatenation chain proves
    Lemmas 8.68/8.72/8.82 and the all-size stretched-exponential lower bound of Theorem 8.61.

137. **Chapter 8 finite-cluster tail checkpoint and dependency audit (2026-07-16).**  Proved the
    exact volume-to-coordinate-radius reduction and equation 8.64 from the positivity conclusion
    `0 < a(p)`, including `n=0`, small-size, and vanishing-tail cases.  Production builds of the
    new rate, gluing, and tail modules pass, and `Chapter8AxiomAudit` reports only `propext`,
    `Classical.choice`, and `Quot.sound`.  The new comparator card records the genuine remaining
    boundary: Theorem 8.21 requires the still-unfinished unconditional Chapter 7 slab
    approximation; Theorem 8.65 and the smoothness theorem 8.92 transitively require that
    renormalization/topological input; Theorem 8.99 requires a multiparameter pointwise ergodic
    theorem not present in Mathlib or the repository.  No theorem parameter or Chapter 11
    external axiom is presented as an unconditional Chapter 8 result.

138. **Chapter 8 infinite-cluster edge balance (2026-07-16).**  Defined the off-edge infinite
    continuation event and proved that its open and closed trace extensions have probabilities
    `p q_e` and `(1-p) q_e`.  A one-edge deletion lemma identifies these events exactly with
    Grimmett's open edges whose two endpoints lie in the infinite cluster and closed edges having
    an infinite-cluster endpoint.  This yields an endpoint-safe cross-multiplied version of the
    local balance behind Theorem 8.99.  The full almost-sure box-density ratio remains explicitly
    open because Mathlib and the repository lack the required multiparameter pointwise ergodic
    theorem.  The new transitive axiom audit again reports only standard Lean axioms.

139. **Chapter 8 conditional edge-density ratio assembly (2026-07-16).**  Added the exact
    finite-box counts for infinite-cluster interior and boundary edges, their directional
    infinite-volume intensities, the summed balance identity, and a strict positivity theorem
    for the interior intensity when `p theta(p)>0`.  The complete finite-box ratio conclusion of
    Theorem 8.99 now follows from the single specialized proposition
    `InfiniteClusterEdgeDensityLimits`; this isolates precisely the missing multiparameter
    pointwise ergodic theorem and leaves no other probabilistic or algebraic step hidden.  The
    strict production build and expanded transitive axiom audit pass with only `propext`,
    `Classical.choice`, and `Quot.sound`.

140. **Chapter 8 signed-hyperplane radius reduction (2026-07-16).**  Defined the exact finite
    cluster event of hitting a signed coordinate hyperplane, proved its measurability, and used a
    first-hit path to cover the finite box-radius event by the `2d` signed events.  Coordinate
    permutations and reflections preserve their Bernoulli probabilities, yielding Grimmett's
    exact factor `2d` in equation 8.43.  The logarithmic radius-rate limit then proves
    `a(p) ≥ γ > 0` from the source exponential hyperplane estimate.  The remaining content of
    Theorem 8.21 is now isolated to the strip-exploration contraction 8.44–8.48 after the
    unconditional Chapter 7 slab approximation.  Strict builds and the expanded transitive axiom
    audit pass with only standard Lean axioms.

141. **Chapter 8 pointwise infinite-cluster edge densities (2026-07-16).**  Replaced the former
    multiparameter-ergodic placeholder in Theorem 8.99 by a proved finite-cylinder strong law.
    Exponentially small finite-cluster continuation errors are summable along square boxes, so
    Borel–Cantelli transfers independent finite-cylinder averages to the infinite-cluster edge
    fields.  Exact oriented-edge enumeration, a vanishing surface correction, and monotone
    square-to-all-radius interpolation yield both interior and boundary edge-density limits.
    The ratio theorem is therefore proved conditional only on the positive finite-cluster radius
    exponent, exactly the remaining conclusion of Theorem 8.21.  The measured theorem and shared
    infrastructure window was 42m40s and 907,656 tokens.  Strict builds and the transitive audit
    pass with only `propext`, `Classical.choice`, and `Quot.sound`.

142. **Chapter 8 supercritical smoothness analytic core (2026-07-16).**  Formalized the
    higher-derivative argument in Theorem 8.92.  Exact Leibniz formulas give an explicit
    polynomial derivative cost for every rooted animal; after summing within a fixed size, the
    majorant is expressed using the physical probability `Pₚ(|C|=n)`.  A general theorem proves
    summability of every polynomial times `exp(-eta*n^alpha)`, and termwise differentiation then
    gives `C∞` exact-size series with arbitrary polynomial weights.  The instantiated weights
    `1`, `n`, and `1/n` yield the animal extensions of `theta`, finite susceptibility, and cluster
    density, together with their physical identifications.  The theorem assumes the exact
    compact-uniform form of (8.91); deriving it unconditionally remains tied to Theorem 8.21, and
    the `p=1` endpoint remains tied to (8.88).  The measured analytic-core window was 38m40s and
    503,373 tokens.  Strict compilation and the expanded transitive audit pass with only standard
    Lean axioms.

143. **Chapter 8 aggregate-build integration (2026-07-16).**  Renamed Chapter 11's old
    dimension-two helper to `squareTruncatedTwoPointConnectivity`, avoiding a namespace collision
    with Chapter 8's genuine dimension-uniform `truncatedTwoPointConnectivity`.  The source-facing
    Chapter 11 limit theorem keeps its existing name and now refers to the square-specific helper.
    The complete `lake build` succeeds (8,750 jobs), and the Chapter 8 transitive audit still
    reports only `propext`, `Classical.choice`, and `Quot.sound`.

144. **Chapter 8 strip contraction and compact-uniform consequences (2026-07-16).**  Formalized
    equations 8.44--8.48 without conditional-probability division: arbitrary-coordinate support
    and product independence, canonical first strip entrances determined by strict-past bonds,
    exact avoidance probability, one-step factorization, and recursively iterated histories give
    `P(G_n) ≤ (1-θ_strip)^(n/k)`.  An endpoint-safe logarithmic rate absorbs quotient rounding and
    all small radii, proving `a(p)>0` from a supercritical coordinate strip.  For `d≥3`, slab
    inclusion and coordinate permutation reduce the only upstream premise to the named
    `SlabCriticalApproximation d`.  Rooted region monotonicity then fixes one strip at a compact
    interval's left endpoint and proves the uniform form of (8.91), closing the former uniformity
    gap in the interior of Theorem 8.92 and assembling (8.64) and 8.99 from the same Chapter 7
    premise.  The measured strip window was 29m32s/438,557 tokens and the uniform-consequence
    window 11m52s/559,110 tokens.  Strict builds and the transitive audit use only standard axioms.
    The final Chapter 8 audit build succeeds in 8,603 jobs, the repository-wide build succeeds in
    8,757 jobs, and the measured verification/documentation closeout window was
    22m34s/234,108 tokens.

145. **Grimmett Chapter 11 two-dimensional bond percolation (2026-07-16).** Added the literal
    `[0,n+1] × [0,n]` rectangle and disjoint-crossing maximum, finite self-dual trace weights,
    the RSW event/gluing/numerical stack, independent annular barriers, and proved
    `cubicCriticalProbability_two_eq_half`.  Also proved the centered form of Lemma 11.22 and the
    complete finite-tube decay package of Lemma 11.27.  Added exact source-facing declarations
    for every named Chapter 11 result, concrete rooted inhomogeneous square/triangular models,
    semantic application tests, and transitive axiom audits.  In accordance with the user's
    policy, Kesten/Russo planar topology and the results which the book delegates to outside
    literature are explicit named project axioms; the chapter is complete modulo those audited
    boundaries, not assumption-free.  See
    `audit/topics/topic-11-bond-percolation-two-dimensions.md` and
    `audit/vetting/chapter-11-external-results.md`.

146. **Literal non-root confinement and acceptance-time anchor bridge (2026-07-17).** Closed
    the geometric and infinite-cluster assembly gaps left by the previous checkpoint.  Both
    slots of every expanded outgoing branch are now localized in the two endpoint boxes of the
    corresponding coarse bond, and this localization is propagated through every genuine
    adaptive replay history.  Consequently the final-density rooted walks and every published
    seed connection stay inside the literal `4NF+B(2N)` thickening.  For a limiting occupied
    coarse site, the chosen physical anchor is the inlet seed published by its accepted parent;
    it lies within radius `3N` of the destination site center.  These uniformly local anchors
    have finite fibres, so an infinite occupied coarse cluster yields an infinite open cluster
    in the thickening without a false injectivity premise.  The resulting probability theorem
    and critical-value adapter are unconditional once the concrete replay-stage and
    final-threshold certificates are supplied.  The full 8,709-job build and the expanded
    transitive axiom audit pass with only `propext`, `Classical.choice`, and `Quot.sound`.
    The unique remaining Theorem 7.2 construction issue is the source's global overlap claim
    behind (7.34): a per-site `4d` attempt bound does not prove that a persistent edge is charged
    only finitely many times across the whole adaptive exploration.

147. **Scale-uniform non-root reveal accounting (2026-07-17).** Separated the source's `4d`
    within-site restart attempts from its global spatial overlap accounting.  A fixed physical
    vertex now has at most `2^d(2d+1)` influencing coarse query sites, independently of the block
    scale. Canonical replay queries are proved distinct, every literal runtime support is confined
    to the query's influence region, and pointwise threshold induction charges an edge only when
    that query can affect its canonical endpoint.  This yields an explicit global replay cap,
    exact `lower + delta` behavior on every reached runtime prefix, and a concrete
    `ReplayProgramFinalThresholdCertificate` for the budgeted policy.  The cap is a safe internal
    packing bound; the public Theorem 7.2 statement and final density are unchanged.  The remaining
    Theorem 7.2 construction task is the mutually history-indexed stable stage certificate (and
    thereby concrete adaptive-answer measurability), not final-threshold accounting. No telemetry
    was reconstructed for this continuation.

## Axiom Ledger

Chapter 11 contains the explicitly cited external-reference axioms listed in
`AXIOM_AUDIT.md`.  No other project axiom is present.  Their common vetting and discharge plan is
`audit/vetting/chapter-11-external-results.md`.

## Anti-Library

- **Reimer's inequality (Grimmett Thm. (2.19), p. 39).** Rejected as a formalization
  target (2026-07-04): the source states it without proof, citing Reimer (1997), and no
  Chapter 2–11 result needs it — the increasing-event case is exactly the BK inequality,
  and the `A □ B = A ∘ B` reduction for increasing events is proved
  (`disjointOccurrence_eq_openWitnessDisjointOccurrence`). Lesson: when the book itself
  defers a proof, record an anti-target instead of importing research-level scope.
