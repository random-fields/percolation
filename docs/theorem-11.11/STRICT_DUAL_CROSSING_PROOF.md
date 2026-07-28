# Strict-dual proof of Grimmett Theorem 11.11

## Status and axiom audit

This note gives a rigorous, standard-axiom replacement for the unresolved outermost-path step in
the Bollobás--Riordan/RSW route. It proves nonpercolation at density one half without constructing
a canonical leftmost crossing and without invoking a Jordan-curve theorem.

The Lean implementation is complete. The public `theta_two_half_eq_zero` theorem is rewired to
`theta_two_half_eq_zero_via_strictDualCrossing`, and
`cubicCriticalProbability_two_eq_half` now closes through that standard-only route. The full
`lake build` succeeded through job `8877/8877`. Exact `#print axioms` checks of
`one_thirty_second_le_strictDualHorizontalCrossingEvent_half`,
`dualWalkIsOpen_not_mem_fullVerticalCrossingEvent`,
`theta_two_half_eq_zero_via_strictDualCrossing`, `theta_two_half_eq_zero`, and
`cubicCriticalProbability_two_eq_half` each reported exactly
`[propext, Classical.choice, Quot.sound]`. Comparator and independent review were explicitly
deferred and are outside this formalization result.

There are two superficially similar strict-dual kernels:

- An odd-source, three-fresh-edge kernel has probability exactly 1/16.
- An even-source, four-fresh-edge kernel has probability at least 1/32.

Only the second kernel is accepted for the final theorem. The exact 1/16 calculation uses
**bernoulliBondMeasure_real_grimmettRectangleCrossingEvent_half**, whose transitive closure
contains the custom axiom **grimmettRectangleDualTraceEquiv**. Kernel output does not list the
nearby cardinality-complement axiom **card_grimmettRectangleDualTraceEquiv_apply** for this
particular theorem, although that axiom is used by the more general complementary-density
identity in the same module. The final standard-axiom proof must therefore use
the axiom-free even-source lower bound
**half_le_grimmettRectangleCrossingProbability_even**.

The accepted argument has two ingredients.

1. At density one half, construct with probability at least 1/32 a strict shifted-dual
   horizontal crossing of the face frame surrounding [0,2N] x [-N,N].
2. Such a strict dual crossing cannot coexist with a full primal bottom-to-top crossing of that
   square. The incompatibility is proved by the already formalized mod-two face-parity argument.

If **theta 2 squareHalfDensity** were positive, the full-box crossing theorem would make the
probability of the primal crossing tend to one. The strict dual event keeps probability at least
1/32, so the primal crossing probability is at most 31/32 on a cofinal sequence of scales, a
contradiction. Consequently

~~~text
theta 2 squareHalfDensity = 0.
~~~

Combining this with the existing standard-axiom upper bound on the critical probability gives

~~~text
cubicCriticalProbability 2 = 1 / 2.
~~~

## Coordinate conventions

Primal square-lattice vertices are integer pairs. A shifted-dual vertex z = (i,j) denotes the
face whose Euclidean centre is (i+1/2,j+1/2). The equivalence
**squareEdgeDualCrossingEquiv** identifies each primal bond with the unique shifted-dual bond
crossing it.

For a scale N, the finite face frame used in the parity argument is

~~~text
F_N = { (x,y) : -1 <= x <= 2N and -N <= y < N }.
~~~

This is exactly **brLeftmostDualFaces N**. Its left source column is x = -1, and its right target
column is x = 2N.

The strict inequality y < N matters. A generic walk in a closed rectangle may touch the top row
y = N. The explicit witness below has a vertical buffer, so no path-simplification or
boundary-touching argument is needed.

## 1. The accepted axiom-free four-fresh-edge event

Fix l >= 1 and put

~~~text
m = 2l,
N = l + 2.
~~~

Consider Grimmett's rectangle with vertex set

~~~text
[0,m+1] x [0,m]
~~~

and internal bond set **grimmettRectangleEdges m**. Its left and right sides are x = 0 and
x = m+1.

The finite bond-interface theorem already proves, using only standard axioms,

~~~text
P(grimmettRectangleCrossingEvent (2l)) >= 1/2.
~~~

The Lean declaration is **half_le_grimmettRectangleCrossingProbability_even l hl**. It is
important that this is the theorem used here; the exact odd-rectangle trace count is not in the
accepted dependency closure.

### Trace-dependent selected crossing

Let E_m = **grimmettRectangleEdges m**. Partition the crossing event according to the exact trace
s = omega intersect E_m. The crossing traces form the finite set
**grimmettRectangleCrossingTraces m**. For every crossing trace s, choose the existing
deterministic witness

~~~text
W_s = selectedGrimmettRectangleTraceCrossing m s.
~~~

Write its endpoints as

~~~text
W_s.start  = (0,a),
W_s.finish = (m+1,b).
~~~

The witness walk uses only bonds in E_m, and all of its bonds belong to s.

The existing even-source construction adds three fresh bonds:

~~~text
e_L1 = {(-1,a), (0,a)},
e_R1 = {(m+1,b), (m+2,b)},
e_R2 = {(m+2,b), (m+3,b)}.
~~~

These are the bonds in **grimmettRectangleFreshExtensionEdgesThree m s**. Add one further bond

~~~text
e_L2 = {(-2,a), (-1,a)}.
~~~

It should be represented by a definition such as
**grimmettTraceLeftSecondExtensionEdge W_s**. The resulting four-edge fresh set is

~~~text
{e_L2} union grimmettRectangleFreshExtensionEdgesThree m s.
~~~

All four bonds lie outside E_m. They are pairwise distinct: the two left bonds have
first-coordinate endpoint sets {-2,-1} and {-1,0}, while the two right bonds have endpoint sets
{m+1,m+2} and {m+2,m+3}. Thus the fresh set is disjoint from E_m and has cardinality four.

The extended walk is

~~~text
(-2,a) -- (-1,a) -- W_s.start -- W_s.walk
       -- W_s.finish -- (m+2,b) -- (m+3,b).
~~~

Equivalently, prepend the second-left step to **grimmettTraceExtendedWalkThree W_s**. On the
cylinder with trace s, this walk is open whenever the four selected fresh bonds are open.

### Probability calculation

Conditionally on a fixed trace s, the four fresh bonds are independent of the observed trace and
are all open with probability

~~~text
(1/2)^4 = 1/16.
~~~

The trace cylinders are pairwise disjoint. The adaptive-fresh-extension identity therefore gives

~~~text
P(four-edge source event)
  = (1/2)^4
      * sum_{s crossing trace} finiteBernoulliWeight(E_m, 1/2, s)
  = (1/16) * P(grimmettRectangleCrossingEvent (2l))
  >= (1/16) * (1/2)
  = 1/32.                                                    (1)
~~~

The formal probability engine is
**bernoulliBondMeasure_real_adaptiveFreshOpenExtensionEvent**. Its inputs are:

- every crossing trace is a subset of E_m;
- the trace-dependent four-edge set is disjoint from E_m;
- its cardinality is four;
- **half_le_grimmettRectangleCrossingProbability_even** supplies the final lower bound on the
  trace-weight sum.

This entire calculation uses only standard axioms.

## 2. Translation into the strict shifted-dual frame

Apply the lattice translation

~~~text
T_l(x,y) = (x+1, y-l).
~~~

This is **grimmettFreshSquareIso l**. Since m = 2l, the endpoints of the four-edge extended walk
become

~~~text
T_l(-2,a)  = (-1, a-l),
T_l(m+3,b) = (m+4, b-l) = (2l+4, b-l) = (2N, b-l).
~~~

Every vertex of the selected crossing lies in

~~~text
0 <= x <= m+1,   0 <= y <= m.
~~~

The four added bonds enlarge only the horizontal range. Hence every vertex of the extended walk
satisfies

~~~text
-2 <= x <= m+3,   0 <= y <= m.
~~~

After applying T_l, this becomes

~~~text
-1 <= x <= m+4 = 2N,
-l <= y <= m-l = l.
~~~

Since N = l+2,

~~~text
[-l,l] is a subset of [-N,N-1] = [-l-2,l+1].
~~~

Thus the whole translated walk, including both endpoints of every bond, lies in
**brLeftmostDualFaces N**. Its start is on x = -1 and its finish is on x = 2N.

Let A_l be the translated four-fresh-edge event, now viewed as an event for a configuration on
the shifted-dual copy of the square lattice. Translation invariance and (1) give

~~~text
P(A_l) >= 1/32.
~~~

Define the corresponding primal event

~~~text
D_l = { omega : dualSquareConfiguration omega belongs to A_l }.
~~~

At density one half, **dualSquareConfiguration** preserves the Bernoulli law. It complements the
crossed primal coordinates, changing p to 1-p, and 1-(1/2)=1/2. Formally the transfer uses

~~~text
bernoulliBondMeasure_map_dualSquareConfiguration
map_measureReal_apply
sigma squareHalfDensity = squareHalfDensity.
~~~

Consequently

~~~text
P(D_l) >= 1/32.                                             (2)
~~~

Membership in D_l supplies a walk q with the exact data

~~~text
q : dualSquareGraph.Walk x y
x 0 = -1
y 0 = 2N
for every z in q.support, z belongs to brLeftmostDualFaces N
dualWalkIsOpen omega q.
~~~

The last statement means that every primal bond crossed by q is closed in omega, by
**dualSquareConfiguration_open_iff**.

## 3. Full primal vertical crossings

Let V_N be the event that [0,2N] x [-N,N] has a bottom-to-top open crossing using every box bond,
including bonds along the boundary. In Lean this is **fullVerticalCrossingEvent N**, obtained by
translating

~~~text
leftRightCrossingEvent 2 N (1 : Fin 2)
~~~

from the radius-N box centred at the origin to the box centred at (N,0).

Translation preserves its probability. Therefore the existing qualitative supercritical
crossing theorem gives

~~~text
theta 2 p > 0  implies  P_p(V_N) tends to 1 as N tends to infinity.   (3)
~~~

The relevant declarations are **leftRightCrossing_probability_tendsto_one** and its translated
wrapper **fullVerticalCrossing_probability_tendsto_one**.

The use of the full edge support is deliberate. It is exactly the event covered by the existing
supercritical theorem, and the strict dual walk blocks it even when the primal witness runs along
the boundary.

## 4. The parity/exterior-closure intersection argument

We prove the deterministic exclusion

~~~text
D_l is a subset of the complement of V_(l+2).               (4)
~~~

Suppose both events occur. Choose an open primal walk p from (a,-N) to (b,N), supported in
[0,2N] x [-N,N], and choose the strict dual walk q supplied above.

### Close the primal walk outside on the left

Append to p the explicit exterior walk L which:

1. goes from (b,N) left along the top boundary to (-1,N);
2. goes down the exterior column x = -1 to (-1,-N);
3. goes right along the bottom boundary to (a,-N).

This is **brLeftExteriorClosureWalk N a b**. The concatenation

~~~text
c = p.append (brLeftExteriorClosureWalk N a b)
~~~

is a closed primal walk. It need not be simple.

### Face parity differs at the two endpoints

For a shifted-dual face z, let I_c(z) be the number modulo two of bonds of c crossing the
horizontal ray from z to the right. This is **closedSquareWalkFaceParity c z**.

At the start of q, whose first coordinate is -1 and whose second coordinate lies in [-N,N-1],
the bottom-to-top walk p crosses the ray an odd number of times. The exterior closure contributes
zero modulo two. At the finish of q, whose first coordinate is 2N, the closed walk is weakly to
the left and the parity is zero. Therefore

~~~text
closedSquareWalkFaceParity c q.start
  != closedSquareWalkFaceParity c q.finish.
~~~

The exact formal theorem is **brClosedBottomTopWalk_faceParity_ne**.

### A dual bond crosses the closed primal walk

Across one adjacent dual step, face parity can change only when that dual bond crosses a bond of
the closed primal walk. Induction along q gives a dual bond ed of q such that

~~~text
squareEdgeDualCrossingEquiv.symm ed belongs to walkEdgeFinset c.
~~~

This is
**exists_dualWalk_edge_crossing_closedWalk_of_faceParity_ne**.

### The crossed bond belongs to p, not to the artificial closure

Every endpoint of ed lies in the strict face frame

~~~text
-1 <= x <= 2N,   -N <= y < N.
~~~

A coordinate check shows that such a dual bond cannot cross any bond of the artificial
left/top/bottom closure. Crossing a top or bottom closure bond would require a dual endpoint
outside the strict vertical range; crossing the exterior-column part would require a dual
endpoint to the left of x = -1. The formal lemma is

~~~text
squareEdgeDualCrossingEquiv_symm_not_mem_brLeftExteriorClosureWalk.
~~~

The crossed primal bond therefore belongs to p itself.

Because p is open, this primal bond belongs to omega. Because ed is open in
**dualSquareConfiguration omega**, the same primal bond does not belong to omega. This is a
contradiction.

No simple-cycle extraction and no Jordan separation theorem occurs here. All planar topology has
been reduced to a finite mod-two ray count. The reusable formal wrapper is
**dualWalkIsOpen_not_mem_fullVerticalCrossingEvent**.

## 5. The supercritical contradiction

From (2) and (4), monotonicity of measure gives

~~~text
1/32
  <= P(D_l)
  <= P(complement of V_(l+2))
  = 1 - P(V_(l+2)).
~~~

Thus, for every l >= 1,

~~~text
P(V_(l+2)) <= 31/32.                                       (5)
~~~

Assume **theta 2 squareHalfDensity > 0**. By (3), P(V_N) tends to one. In particular it is
eventually larger than 31/32. Since the scales N = l+2 with l >= 1 are cofinal, this contradicts
(5). Since theta is nonnegative,

~~~text
theta 2 squareHalfDensity = 0.                              (6)
~~~

The critical-probability assembly is then immediate. The standard-only declarations

~~~text
cubicCriticalProbability_two_le_half_via_bond_interface
half_le_cubicCriticalProbability_two_of_theta_half_eq_zero (6)
~~~

give opposite inequalities. Antisymmetry gives
**cubicCriticalProbability_two_eq_half**.

## 6. The rejected odd-source 1/16 calculation

For completeness, here is the shorter calculation requested during route selection.

Take l >= 1, m = 2l-1, and N = l+1. Start with a selected crossing of the odd Grimmett rectangle.
The existing extension uses e_L1 and e_R1. Add only e_L2. There are then three fresh bonds, and
the translated walk runs from x = -1 to x = 2N with vertical range

~~~text
-l <= y <= l-1,
~~~

which is contained in the frame range [-N,N-1].

If one uses the exact identity

~~~text
P(grimmettRectangleCrossingEvent (2l-1)) = 1/2,
~~~

then the adaptive event has probability

~~~text
(1/2)^3 * (1/2) = 1/16.
~~~

The geometry and the parity argument are correct. The calculation is nevertheless unacceptable
for the final goal because the exact identity is
**bernoulliBondMeasure_real_grimmettRectangleCrossingEvent_half**, and kernel output reports:

~~~text
grimmettRectangleDualTraceEquiv
~~~

This is a custom axiom declared in **Percolation/Planar/External.lean** and recorded in
**AXIOM_AUDIT.md**. The separate axiom **card_grimmettRectangleDualTraceEquiv_apply** is not in
this theorem's transitive closure. Therefore the live odd-source strict event must not be used to claim
standard-axiom completion. It may remain only as a documented conditional or design result.

The even-source four-edge kernel loses a factor of two, changing 1/16 to 1/32, but removes the
custom trace-equivalence axiom. Any fixed positive constant suffices for the limiting
contradiction.

## 7. Dependency and implementation order

Implement the accepted route in this order.

1. **Four-edge trace extension.**
   Define the second-left edge and endpoint, prepend it to
   **grimmettTraceExtendedWalkThree**, and insert it into
   **grimmettRectangleFreshExtensionEdgesThree**. Prove freshness, distinctness, cardinality
   four, and openness on every trace cylinder.
2. **Axiom-free probability lower bound.**
   Apply **bernoulliBondMeasure_real_adaptiveFreshOpenExtensionEvent** and
   **half_le_grimmettRectangleCrossingProbability_even** to get 1/32.
3. **Strict frame witness.**
   Translate by **grimmettFreshSquareIso l** and prove the range
   [-1,2(l+2)] x [-(l+2),l+1], the endpoint-column identities, and dual openness.
4. **Dual-law transfer.**
   Pull the event back through **dualSquareConfiguration** and use its half-density map theorem.
5. **Full vertical event.**
   Translate **leftRightCrossingEvent 2 N 1** and transfer measurability, probability, and the
   supercritical limit.
6. **Deterministic exclusion.**
   Reuse the exterior closure and face-parity APIs to show strict dual and full primal crossings
   are disjoint.
7. **Limit contradiction and threshold assembly.**
   Deduce (6), then combine the standard-only lower and upper critical-probability bounds.

There is no dependency on **rswThreeHalvesCrossingProbability_ge**, a canonical leftmost path,
the BR fresh-cover premise, annulus gluing, or a discrete Jordan-curve theorem.

## 8. Lean API map

| Mathematical role | Lean declaration/API | Module |
|---|---|---|
| Axiom-free even-rectangle lower bound | **half_le_grimmettRectangleCrossingProbability_even** | **Percolation.Planar.BondCrossingDuality** |
| Crossing trace family | **grimmettRectangleCrossingTraces** | **Percolation.Planar.SquareCritical** |
| Selected trace crossing | **GrimmettRectangleTraceCrossing**, **selectedGrimmettRectangleTraceCrossing** | **Percolation.Planar.RSWHalf** |
| Existing three fresh edges | **grimmettRectangleFreshExtensionEdgesThree**, **grimmettTraceExtendedWalkThree** | **Percolation.Planar.RSWHalf** |
| Adaptive extension probability | **bernoulliBondMeasure_real_adaptiveFreshOpenExtensionEvent** | **Percolation.Bernoulli.AdaptiveFreshExtension** |
| Source-to-frame translation | **grimmettFreshSquareIso** | **Percolation.Planar.RSWHalf** |
| Dual open iff crossed primal bond closed | **dualSquareConfiguration_open_iff** | **Percolation.Planar.Basic** |
| Dual-law map | **bernoulliBondMeasure_map_dualSquareConfiguration** | **Percolation.Planar.BondCrossingDuality** |
| Measure of a map preimage | **map_measureReal_apply** | Mathlib measure API |
| Full translated vertical event | **fullVerticalCrossingEvent** | **Percolation.Planar.FullVerticalCrossing** |
| Supercritical full-box limit | **leftRightCrossing_probability_tendsto_one**, **fullVerticalCrossing_probability_tendsto_one** | **Percolation.Critical.SupercriticalCrossing**, **Percolation.Planar.FullVerticalCrossing** |
| Exterior closure | **brLeftExteriorClosureWalk** | **Percolation.Planar.BRExplorationAlternative** |
| Endpoint parity difference | **brClosedBottomTopWalk_faceParity_ne** | **Percolation.Planar.BRExplorationAlternative** |
| Parity forces a crossed edge | **exists_dualWalk_edge_crossing_closedWalk_of_faceParity_ne** | **Percolation.Planar.BRExplorationAlternative** |
| Frame edges avoid closure | **squareEdgeDualCrossingEquiv_symm_not_mem_brLeftExteriorClosureWalk** | **Percolation.Planar.BRExplorationAlternative** |
| Packaged primal/dual exclusion | **dualWalkIsOpen_not_mem_fullVerticalCrossingEvent** | **Percolation.Planar.FullVerticalDuality** |
| Lower critical bound from nonpercolation | **half_le_cubicCriticalProbability_two_of_theta_half_eq_zero** | **Percolation.Planar.SquareCritical** |
| Standard-only upper critical bound | **cubicCriticalProbability_two_le_half_via_bond_interface** | **Percolation.Planar.BondCrossingDuality** |

## 9. Rejected boundary-free shortcut and counterexample

The following tempting shortcut is false:

~~~text
a translated full vertical box crossing at scale N
  is contained in brSquareVerticalCrossingEvent N.
~~~

The left event uses every bond of the box. The right event uses
**squareBoundaryFreeRectangleEdges (2*N) N**, which deletes every bond whose two endpoints are on
the rectangle boundary.

For a concrete counterexample, let N >= 1 and let omega contain exactly the vertical bonds

~~~text
{(0,y),(0,y+1)} for -N <= y < N.
~~~

These bonds give a full bottom-to-top crossing along the left side. Every bond has both endpoints
on the boundary x = 0, so every bond is absent from the boundary-free support. With no other open
bonds, no boundary-free bottom-to-top crossing exists.

A second proposed inclusion is also false:

~~~text
a translated radius-(N-1) crossing
  is contained in brSquareVerticalCrossingEvent N.
~~~

That path ends on y = -(N-1) and y = N-1, not on the required rows y = -N and y = N. Adding one
bond at each end repairs the geometry only after paying a factor 1/4; it gives a fixed positive
lower bound, not a probability tending to one, and cannot contradict a fixed upper bound below
one.

One could try to prove that supercritical full crossings avoid the deleted boundary with
probability tending to one, but that is a new robustness or many-crossings theorem. It does not
follow from **leftRightCrossing_probability_tendsto_one** and is substantially more work than the
strict-dual construction.

The strict-dual route fixes the geometry on the dual side. Its extra adaptive left bond extends
the dual path far enough to block even a primal path running along x = 0, while its explicit
vertical buffer keeps the whole dual path in the parity frame.

## 10. Completed Lean audit checklist

The completed implementation satisfies all of the following.

- The accepted strict event uses the even source m = 2l and four fresh edges.
- Its probability proof depends on **half_le_grimmettRectangleCrossingProbability_even**, not
  **bernoulliBondMeasure_real_grimmettRectangleCrossingEvent_half**.
- The event exports the open dual walk, both endpoint-column identities, and the full
  support-in-frame statement; a probability bound alone is not enough.
- The primal event in the exclusion theorem is **fullVerticalCrossingEvent**, not the
  boundary-free BR event.
- The crossed edge supplied by parity is proved not to belong to the artificial closure before
  primal openness is used.
- The final upper bound uses
  **cubicCriticalProbability_two_le_half_via_bond_interface** or another independently checked
  standard-only wrapper.
- Kernel output for all five audited declarations, including the final nonpercolation theorem and
  **cubicCriticalProbability_two_eq_half**, is exactly
  `[propext, Classical.choice, Quot.sound]`.
- The full public project builds successfully through job `8877/8877` after rewiring. Comparator
  and independent review are deferred external processes, not Lean proof obligations left open.
