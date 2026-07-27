import Percolation.Planar.BRSelectedCrossing
import Percolation.Planar.BRFreshSupport
import Percolation.Planar.BRProbability
import Percolation.Planar.BRSourceXEvent
import Percolation.Planar.RectangleIntersection

/-!
# First contact with a selected Bollobás--Riordan interface

This file separates the sound deterministic part of the first-contact argument from a missing
stopping-set invariant.  A horizontal crossing of the doubled rectangle meets the selected
bottom--top interface or its reflection.  Consequently it contains a right-side arm to one of
the two walks.  This conclusion initially uses the full doubled-rectangle edge support.

The corresponding genuinely fresh events are also defined.  They use
`brFreshExtensionEdges`, are interchanged by reflection, and a fresh lower arm combines with the
fiber-open selected walk to give `brSourceXEvent`.

## Audit of the tempting freshness claim

The specifications of `brSelectedResolvedBoundaryPortPair` and `brSelectedPrimalWalk` only say
that an arbitrarily chosen component joins an odd bottom port to an odd top port.  They do *not*
say that this component is the outer (rightmost) boundary of the whole reached set.  A reached
set can have a rightward finger joined to its left-reachable body by a one-cell neck.  Its
resolved boundary then has cut bonds strictly to the right of a parity-admissible bottom--top
component.  A right-to-left open crossing can cross those cut bonds, traverse queried incident
bonds around the finger, and only later meet the selected component.  Trimming at that later
contact therefore need not avoid `brReachableFaceFiberSupport`; reflecting the picture gives the
same obstruction for the reflected support.

Thus the inclusion of the rectangle crossing event in the union of the *fresh* lower and upper
events does not follow from the current selector API.  What is required is a stronger selector
theorem: every vertex of the reached set and every primal bond in
`brSymmetricReachableFaceFiberSupport` must lie on the non-right side of the selected doubled
walk, equivalently the segment of every right-to-left rectangle crossing before its first hit of
that doubled walk must avoid the symmetric fiber support.  This is the finite stopping-set /
outer-boundary property of the canonical leftmost crossing in Bollobás--Riordan Lemma 6.  The
theorems below deliberately expose the exact remaining implication rather than assuming it.
-/

namespace Percolation

open SimpleGraph
open MeasureTheory ProbabilityTheory
open scoped unitInterval

noncomputable section

/-! ### Reflected and doubled selected walks -/

/-- Reflection of the selected source-square crossing across its top side. -/
def brReflectedSelectedPrimalWalk
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    squareGraph.Walk
      (brSelectedTopPrimalVertex hn hR)
      (brPrimalTopReflectionIso n (brSelectedBottomPrimalVertex hn hR)) :=
  ((brSelectedPrimalWalk hn hR).map (brPrimalTopReflectionIso n).toHom).reverse.copy
    (by
      ext i
      fin_cases i
      · simp
      · have ht := mem_brSquareTopSide_iff.mp
          (brSelectedTopPrimalVertex_mem_topSide hn hR)
        simp
        omega)
    rfl

/-- The selected crossing followed by its reflected copy.  It joins height `-n` to height
`3n` and is the finite barrier used in the intersection argument. -/
def brDoubledSelectedPrimalWalk
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    squareGraph.Walk
      (brSelectedBottomPrimalVertex hn hR)
      (brPrimalTopReflectionIso n (brSelectedBottomPrimalVertex hn hR)) :=
  (brSelectedPrimalWalk hn hR).append (brReflectedSelectedPrimalWalk hn hR)

@[simp]
theorem brPrimalTopReflectionIso_selectedTop
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    brPrimalTopReflectionIso n (brSelectedTopPrimalVertex hn hR) =
      brSelectedTopPrimalVertex hn hR := by
  ext i
  fin_cases i
  · simp
  · have ht := mem_brSquareTopSide_iff.mp
      (brSelectedTopPrimalVertex_mem_topSide hn hR)
    simp
    omega

theorem brReflectedSelectedPrimalWalk_support_iff
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R)
    {z : SquareVertex} :
    z ∈ (brReflectedSelectedPrimalWalk hn hR).support ↔
      brPrimalTopReflectionIso n z ∈ (brSelectedPrimalWalk hn hR).support := by
  simp only [brReflectedSelectedPrimalWalk, SimpleGraph.Walk.support_copy,
    SimpleGraph.Walk.support_reverse, SimpleGraph.Walk.support_map, List.mem_reverse,
    List.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    change brPrimalTopReflectionIso n (brPrimalTopReflectionIso n x) ∈
      (brSelectedPrimalWalk hn hR).support
    simpa only [brPrimalTopReflectionIso_involutive] using hx
  · intro hz
    refine ⟨brPrimalTopReflectionIso n z, hz, ?_⟩
    exact brPrimalTopReflectionIso_involutive n z

@[simp]
theorem brDoubledSelectedPrimalWalk_support_iff
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R)
    {z : SquareVertex} :
    z ∈ (brDoubledSelectedPrimalWalk hn hR).support ↔
      z ∈ (brSelectedPrimalWalk hn hR).support ∨
        z ∈ (brReflectedSelectedPrimalWalk hn hR).support := by
  simp [brDoubledSelectedPrimalWalk]

/-! ### Full-support and fresh contact events -/

/-- A right-side arm to the selected lower crossing, using the full doubled-rectangle support.
This is the unconditional conclusion supplied by first-contact trimming. -/
def brLowerContactEvent
    (m : ℕ) {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    Set (EdgeConfiguration 2) :=
  {omega | ∃ z ∈ (brSelectedPrimalWalk hn hR).support,
    ∃ r ∈ brExtensionRectangleRightSide m n,
      omega ∈ connectionEventIn 2 (brExtensionRectangleEdges m n) z r}

/-- The upper full-support contact event is the reflected lower event. -/
def brUpperContactEvent
    (m : ℕ) {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    Set (EdgeConfiguration 2) :=
  cubicGraphIsoEvent (brPrimalTopReflectionIso n)
    (brLowerContactEvent m hn hR)

/-- A genuinely fresh right-side arm to the selected lower crossing. -/
def brLowerFreshExtensionEvent
    (m : ℕ) {n : ℕ} (R : Finset (BRLeftmostDualVertex n))
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    Set (EdgeConfiguration 2) :=
  {omega | ∃ z ∈ (brSelectedPrimalWalk hn hR).support,
    ∃ r ∈ brExtensionRectangleRightSide m n,
      omega ∈ connectionEventIn 2 (brFreshExtensionEdges m n R) z r}

/-- The genuinely fresh upper event, defined by exact reflection of the lower event. -/
def brUpperFreshExtensionEvent
    (m : ℕ) {n : ℕ} (R : Finset (BRLeftmostDualVertex n))
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    Set (EdgeConfiguration 2) :=
  cubicGraphIsoEvent (brPrimalTopReflectionIso n)
    (brLowerFreshExtensionEvent m R hn hR)

theorem cubicGraphIsoEvent_brPrimalTopReflectionIso_involutive
    (n : ℕ) (A : Set (EdgeConfiguration 2)) :
    cubicGraphIsoEvent (brPrimalTopReflectionIso n)
        (cubicGraphIsoEvent (brPrimalTopReflectionIso n) A) = A := by
  ext omega
  change cubicGraphIsoConfigurationPullback (brPrimalTopReflectionIso n)
      (cubicGraphIsoConfigurationPullback (brPrimalTopReflectionIso n) omega) ∈ A ↔
    omega ∈ A
  have hsymm := cubicGraphIsoConfigurationPullback_symm
    (brPrimalTopReflectionIso n) omega
  rw [brPrimalTopReflectionIso_symm] at hsymm
  rw [hsymm]

theorem cubicGraphIsoEvent_brLowerContactEvent_eq_upper
    (m : ℕ) {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    cubicGraphIsoEvent (brPrimalTopReflectionIso n)
        (brLowerContactEvent m hn hR) =
      brUpperContactEvent m hn hR :=
  rfl

theorem cubicGraphIsoEvent_brUpperContactEvent_eq_lower
    (m : ℕ) {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    cubicGraphIsoEvent (brPrimalTopReflectionIso n)
        (brUpperContactEvent m hn hR) =
      brLowerContactEvent m hn hR := by
  exact cubicGraphIsoEvent_brPrimalTopReflectionIso_involutive n _

theorem cubicGraphIsoEvent_brLowerFreshExtensionEvent_eq_upper
    (m : ℕ) {n : ℕ} (R : Finset (BRLeftmostDualVertex n))
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    cubicGraphIsoEvent (brPrimalTopReflectionIso n)
        (brLowerFreshExtensionEvent m R hn hR) =
      brUpperFreshExtensionEvent m R hn hR :=
  rfl

theorem cubicGraphIsoEvent_brUpperFreshExtensionEvent_eq_lower
    (m : ℕ) {n : ℕ} (R : Finset (BRLeftmostDualVertex n))
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    cubicGraphIsoEvent (brPrimalTopReflectionIso n)
        (brUpperFreshExtensionEvent m R hn hR) =
      brLowerFreshExtensionEvent m R hn hR := by
  exact cubicGraphIsoEvent_brPrimalTopReflectionIso_involutive n _

theorem brLowerFreshExtensionEvent_subset_brLowerContactEvent
    (m : ℕ) {n : ℕ} (R : Finset (BRLeftmostDualVertex n))
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    brLowerFreshExtensionEvent m R hn hR ⊆ brLowerContactEvent m hn hR := by
  rintro omega ⟨z, hz, r, hr, w, hwOpen, hwFresh⟩
  exact ⟨z, hz, r, hr, w, hwOpen,
    hwFresh.trans (brFreshExtensionEdges_subset_extensionRectangleEdges m n R)⟩

/-- The lower fresh extension event reads only genuinely fresh coordinates. -/
theorem dependsOn_brLowerFreshExtensionEvent
    (m : ℕ) {n : ℕ} (R : Finset (BRLeftmostDualVertex n))
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    DependsOn (brFreshExtensionEdges m n R)
      (brLowerFreshExtensionEvent m R hn hR) := by
  intro omega eta hagree
  constructor
  · rintro ⟨z, hz, r, hr, hzr⟩
    exact ⟨z, hz, r, hr,
      (dependsOn_connectionEventIn 2 (brFreshExtensionEdges m n R) z r hagree).mp hzr⟩
  · rintro ⟨z, hz, r, hr, hzr⟩
    exact ⟨z, hz, r, hr,
      (dependsOn_connectionEventIn 2 (brFreshExtensionEdges m n R) z r hagree).mpr hzr⟩

theorem measurableSet_brLowerFreshExtensionEvent
    (m : ℕ) {n : ℕ} (R : Finset (BRLeftmostDualVertex n))
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    MeasurableSet (brLowerFreshExtensionEvent m R hn hR) :=
  (dependsOn_brLowerFreshExtensionEvent m R hn hR).measurableSet

theorem measurableSet_brUpperFreshExtensionEvent
    (m : ℕ) {n : ℕ} (R : Finset (BRLeftmostDualVertex n))
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    MeasurableSet (brUpperFreshExtensionEvent m R hn hR) :=
  measurableSet_cubicGraphIsoEvent _
    (measurableSet_brLowerFreshExtensionEvent m R hn hR)

theorem isIncreasingEvent_brLowerFreshExtensionEvent
    (m : ℕ) {n : ℕ} (R : Finset (BRLeftmostDualVertex n))
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    IsIncreasingEvent (brLowerFreshExtensionEvent m R hn hR) := by
  intro omega eta hmono
  rintro ⟨z, hz, r, hr, hzr⟩
  exact ⟨z, hz, r, hr,
    isIncreasingEvent_connectionEventIn 2 (brFreshExtensionEdges m n R) z r hmono hzr⟩

theorem isIncreasingEvent_brUpperFreshExtensionEvent
    (m : ℕ) {n : ℕ} (R : Finset (BRLeftmostDualVertex n))
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    IsIncreasingEvent (brUpperFreshExtensionEvent m R hn hR) :=
  isIncreasingEvent_cubicGraphIsoEvent _
    (isIncreasingEvent_brLowerFreshExtensionEvent m R hn hR)

/-- Bernoulli bond percolation gives the reflected upper and lower fresh events exactly the same
probability. -/
theorem bernoulliBondMeasure_real_brUpperFreshExtensionEvent_eq_lower
    (p : I) (m : ℕ) {n : ℕ} (R : Finset (BRLeftmostDualVertex n))
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    (bernoulliBondMeasure 2 p).real (brUpperFreshExtensionEvent m R hn hR) =
      (bernoulliBondMeasure 2 p).real (brLowerFreshExtensionEvent m R hn hR) :=
  bernoulliBondMeasure_real_cubicGraphIsoEvent p _
    (measurableSet_brLowerFreshExtensionEvent m R hn hR)

/-! ### A fresh lower arm gives the source `X(R)` event on its fiber -/

private theorem walk_support_mem_rectangle_of_boundaryFree_edges
    {m n : ℕ} {u v : SquareVertex} (w : squareGraph.Walk u v)
    (hv : v ∈ squareRectangleVertices m n)
    (hw : walkEdgeFinset w ⊆ squareBoundaryFreeRectangleEdges m n) :
    ∀ z ∈ w.support, z ∈ squareRectangleVertices m n := by
  classical
  intro z hz
  rw [SimpleGraph.Walk.mem_support_iff_exists_mem_edges] at hz
  rcases hz with rfl | ⟨e, he, hze⟩
  · exact hv
  · let ee : SquareEdge := ⟨e, w.edges_subset_edgeSet he⟩
    have heAllowed : ee ∈ squareBoundaryFreeRectangleEdges m n :=
      hw ((mem_walkEdgeFinset_iff w ee).mpr he)
    exact endpoint_mem_squareRectangle_of_edge_mem
      (Finset.mem_filter.mp heAllowed).1 hze

private theorem walkEdgeFinset_takeUntil_subset
    {u v z : SquareVertex} (w : squareGraph.Walk u v) (hz : z ∈ w.support) :
    walkEdgeFinset (w.takeUntil z hz) ⊆ walkEdgeFinset w := by
  intro e he
  rw [mem_walkEdgeFinset_iff] at he
  rw [mem_walkEdgeFinset_iff]
  exact w.edges_takeUntil_subset hz he

private theorem walkEdgeFinset_dropUntil_subset
    {u v z : SquareVertex} (w : squareGraph.Walk u v) (hz : z ∈ w.support) :
    walkEdgeFinset (w.dropUntil z hz) ⊆ walkEdgeFinset w := by
  intro e he
  rw [mem_walkEdgeFinset_iff] at he
  rw [mem_walkEdgeFinset_iff]
  exact w.edges_dropUntil_subset hz he

private theorem walkEdgeFinset_reverse_subset
    {u v : SquareVertex} (w : squareGraph.Walk u v) :
    walkEdgeFinset w.reverse ⊆ walkEdgeFinset w := by
  intro e he
  rw [mem_walkEdgeFinset_iff, SimpleGraph.Walk.edges_reverse, List.mem_reverse] at he
  exact (mem_walkEdgeFinset_iff w e).mpr he

theorem inter_fiber_brLowerFreshExtensionEvent_subset_brSourceXEvent
    (m : ℕ) {n : ℕ} (R : Finset (BRLeftmostDualVertex n))
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    brReachableFaceFiber n R ∩ brLowerFreshExtensionEvent m R hn hR ⊆
      brSourceXEvent m n := by
  rintro omega ⟨homega, z, hz, r, hr, wr, hwrOpen, hwrFresh⟩
  let p := brSelectedPrimalWalk hn hR
  have hpOpen : walkIsOpen omega p :=
    walkIsOpen_brSelectedPrimalWalk_of_mem_fiber hn hR homega
  have hpEdges : walkEdgeFinset p ⊆ brSourceSquareEdges n := by
    simpa [p, brSourceSquareEdges] using
      walkEdgeFinset_brSelectedPrimalWalk_subset_boundaryFree hn hR
  have htRect : brSelectedTopPrimalVertex hn hR ∈
      squareRectangleVertices (2 * n) n := by
    have ht := mem_brSquareTopSide_iff.mp
      (brSelectedTopPrimalVertex_mem_topSide hn hR)
    rw [mem_squareRectangleVertices_iff]
    omega
  have hzRect : z ∈ brSourceSquareVertices n := by
    exact walk_support_mem_rectangle_of_boundaryFree_edges p htRect
      (by simpa [p] using
        walkEdgeFinset_brSelectedPrimalWalk_subset_boundaryFree hn hR) z hz
  let wb := (p.takeUntil z hz).reverse
  let wt := p.dropUntil z hz
  have hwbOpen : walkIsOpen omega wb :=
    walkIsOpen_reverse
      (walkIsOpen_of_edges_subset hpOpen (p.edges_takeUntil_subset hz))
  have hwtOpen : walkIsOpen omega wt :=
    walkIsOpen_of_edges_subset hpOpen (p.edges_dropUntil_subset hz)
  have hwbSupport : walkEdgeFinset wb ⊆ brSourceSquareEdges n :=
    (walkEdgeFinset_reverse_subset (p.takeUntil z hz)).trans
      ((walkEdgeFinset_takeUntil_subset p hz).trans hpEdges)
  have hwtSupport : walkEdgeFinset wt ⊆ brSourceSquareEdges n :=
    (walkEdgeFinset_dropUntil_subset p hz).trans hpEdges
  apply mem_brSourceXEvent_of_walks hzRect
    (brSelectedBottomPrimalVertex_mem_bottomSide hn hR)
    (brSelectedTopPrimalVertex_mem_topSide hn hR) hr
    wb hwbOpen hwbSupport wt hwtOpen hwtSupport wr hwrOpen
  exact hwrFresh.trans (brFreshExtensionEdges_subset_extensionRectangleEdges m n R)

/-! ### Rectangular intersection without an aspect-ratio restriction -/

/-- Coordinate swap, used only to remove the `height ≤ width` normalization imposed by the
existing rectangle-intersection adapter. -/
private def brFirstContactCoordinateSwapIso : squareGraph ≃g squareGraph :=
  cubicCoordinatePermutationIso squareCoordinateSwap

@[simp]
private theorem brFirstContactCoordinateSwapIso_zero (x : SquareVertex) :
    brFirstContactCoordinateSwapIso x 0 = x 1 := by
  simp [brFirstContactCoordinateSwapIso, cubicCoordinatePermutationIso,
    cubicCoordinatePermutationEquiv_apply, squareCoordinateSwap]

@[simp]
private theorem brFirstContactCoordinateSwapIso_one (x : SquareVertex) :
    brFirstContactCoordinateSwapIso x 1 = x 0 := by
  simp [brFirstContactCoordinateSwapIso, cubicCoordinatePermutationIso,
    cubicCoordinatePermutationEquiv_apply, squareCoordinateSwap]

/-- Any left--right and bottom--top walks in an integer rectangle intersect, with no comparison
between width and height.  When the height is larger, swap coordinates and apply the existing
`height ≤ width` theorem. -/
private theorem squareWalk_support_inter_rectangle_int
    {m h : ℕ} {a b c d : ℤ}
    (ha0 : 0 ≤ a) (hah : a ≤ h) (hb0 : 0 ≤ b) (hbh : b ≤ h)
    (hc0 : 0 ≤ c) (hcm : c ≤ m) (hd0 : 0 ≤ d) (hdm : d ≤ m)
    (p : squareGraph.Walk (squareVertex 0 a) (squareVertex (m : ℤ) b))
    (q : squareGraph.Walk (squareVertex c 0) (squareVertex d (h : ℤ)))
    (hpbox : ∀ z ∈ p.support,
      0 ≤ z 0 ∧ z 0 ≤ m ∧ 0 ≤ z 1 ∧ z 1 ≤ h)
    (hqbox : ∀ z ∈ q.support,
      0 ≤ z 0 ∧ z 0 ≤ m ∧ 0 ≤ z 1 ∧ z 1 ≤ h) :
    ∃ z, z ∈ p.support ∧ z ∈ q.support := by
  by_cases hhm : h ≤ m
  · exact squareWalk_support_inter_of_left_right_and_bottom_top_of_le_int hhm
      ha0 hah hb0 hbh hc0 hcm hd0 hdm p q hpbox hqbox
  · have hmh : m ≤ h := le_of_not_ge hhm
    let ps : squareGraph.Walk (squareVertex 0 c) (squareVertex (h : ℤ) d) :=
      (q.map brFirstContactCoordinateSwapIso.toHom).copy
        (by ext i; fin_cases i <;> simp [squareVertex])
        (by ext i; fin_cases i <;> simp [squareVertex])
    let qs : squareGraph.Walk (squareVertex a 0) (squareVertex b (m : ℤ)) :=
      (p.map brFirstContactCoordinateSwapIso.toHom).copy
        (by ext i; fin_cases i <;> simp [squareVertex])
        (by ext i; fin_cases i <;> simp [squareVertex])
    have hpsbox : ∀ z ∈ ps.support,
        0 ≤ z 0 ∧ z 0 ≤ h ∧ 0 ≤ z 1 ∧ z 1 ≤ m := by
      intro z hz
      simp only [ps, SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map,
        List.mem_map] at hz
      rcases hz with ⟨x, hx, rfl⟩
      have hxbox := hqbox x hx
      change 0 ≤ brFirstContactCoordinateSwapIso x 0 ∧
        brFirstContactCoordinateSwapIso x 0 ≤ h ∧
        0 ≤ brFirstContactCoordinateSwapIso x 1 ∧
        brFirstContactCoordinateSwapIso x 1 ≤ m
      rw [brFirstContactCoordinateSwapIso_zero,
        brFirstContactCoordinateSwapIso_one]
      omega
    have hqsbox : ∀ z ∈ qs.support,
        0 ≤ z 0 ∧ z 0 ≤ h ∧ 0 ≤ z 1 ∧ z 1 ≤ m := by
      intro z hz
      simp only [qs, SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map,
        List.mem_map] at hz
      rcases hz with ⟨x, hx, rfl⟩
      have hxbox := hpbox x hx
      change 0 ≤ brFirstContactCoordinateSwapIso x 0 ∧
        brFirstContactCoordinateSwapIso x 0 ≤ h ∧
        0 ≤ brFirstContactCoordinateSwapIso x 1 ∧
        brFirstContactCoordinateSwapIso x 1 ≤ m
      rw [brFirstContactCoordinateSwapIso_zero,
        brFirstContactCoordinateSwapIso_one]
      omega
    obtain ⟨z, hzps, hzqs⟩ :=
      squareWalk_support_inter_of_left_right_and_bottom_top_of_le_int hmh
        hc0 hcm hd0 hdm ha0 hah hb0 hbh ps qs hpsbox hqsbox
    simp only [ps, SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map,
      List.mem_map] at hzps
    simp only [qs, SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map,
      List.mem_map] at hzqs
    rcases hzps with ⟨zq, hzq, hzqMap⟩
    rcases hzqs with ⟨zp, hzp, hzpMap⟩
    have hzpzq : zp = zq := brFirstContactCoordinateSwapIso.injective
      (hzpMap.trans hzqMap.symm)
    exact ⟨zp, hzp, hzpzq ▸ hzq⟩

/-! ### The deterministic full-support contact cover -/

/-- Translate the doubled rectangle `[0,m] × [-n,3n]` to
`[0,m] × [0,4n]`. -/
private def brFirstContactNormalizeIso (n : ℕ) : squareGraph ≃g squareGraph :=
  cubicTranslationIso (squareVertex 0 (-(n : ℤ))) cubicOrigin

@[simp]
private theorem brFirstContactNormalizeIso_zero (n : ℕ) (x : SquareVertex) :
    brFirstContactNormalizeIso n x 0 = x 0 := by
  simp [brFirstContactNormalizeIso, cubicTranslationIso_apply, cubicTranslate,
    cubicOrigin, squareVertex]

@[simp]
private theorem brFirstContactNormalizeIso_one (n : ℕ) (x : SquareVertex) :
    brFirstContactNormalizeIso n x 1 = x 1 + (n : ℤ) := by
  simp [brFirstContactNormalizeIso, cubicTranslationIso_apply, cubicTranslate,
    cubicOrigin, squareVertex]

/-- Every vertex of the selected crossing stays in the centered source square. -/
theorem brSelectedPrimalWalk_support_coordinates
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R)
    {z : SquareVertex} (hz : z ∈ (brSelectedPrimalWalk hn hR).support) :
    0 ≤ z 0 ∧ z 0 ≤ 2 * (n : ℤ) ∧
      -(n : ℤ) ≤ z 1 ∧ z 1 ≤ (n : ℤ) := by
  have ht := mem_brSquareTopSide_iff.mp
    (brSelectedTopPrimalVertex_mem_topSide hn hR)
  have htRect : brSelectedTopPrimalVertex hn hR ∈
      squareRectangleVertices (2 * n) n := by
    rw [mem_squareRectangleVertices_iff]
    omega
  have hzRect := walk_support_mem_rectangle_of_boundaryFree_edges
    (brSelectedPrimalWalk hn hR) htRect
      (walkEdgeFinset_brSelectedPrimalWalk_subset_boundaryFree hn hR) z hz
  exact mem_squareRectangleVertices_iff.mp hzRect

/-- Every vertex of the reflected crossing lies in the upper copy of the source square. -/
theorem brReflectedSelectedPrimalWalk_support_coordinates
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R)
    {z : SquareVertex} (hz : z ∈ (brReflectedSelectedPrimalWalk hn hR).support) :
    0 ≤ z 0 ∧ z 0 ≤ 2 * (n : ℤ) ∧
      (n : ℤ) ≤ z 1 ∧ z 1 ≤ 3 * (n : ℤ) := by
  have hreflected : brPrimalTopReflectionIso n z ∈
      (brSelectedPrimalWalk hn hR).support :=
    (brReflectedSelectedPrimalWalk_support_iff hn hR).mp hz
  have hcoords := brSelectedPrimalWalk_support_coordinates hn hR hreflected
  simp only [brPrimalTopReflectionIso_zero, brPrimalTopReflectionIso_one] at hcoords
  omega

/-- The doubled selected walk stays in the doubled rectangle. -/
theorem brDoubledSelectedPrimalWalk_support_coordinates
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R)
    {z : SquareVertex} (hz : z ∈ (brDoubledSelectedPrimalWalk hn hR).support) :
    0 ≤ z 0 ∧ z 0 ≤ 2 * (n : ℤ) ∧
      -(n : ℤ) ≤ z 1 ∧ z 1 ≤ 3 * (n : ℤ) := by
  rw [brDoubledSelectedPrimalWalk_support_iff hn hR] at hz
  rcases hz with hz | hz
  · have h := brSelectedPrimalWalk_support_coordinates hn hR hz
    omega
  · have h := brReflectedSelectedPrimalWalk_support_coordinates hn hR hz
    omega

/-- The doubled selected walk after vertical normalization. -/
private def brNormalizedDoubledSelectedPrimalWalk
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    squareGraph.Walk
      (squareVertex ((brSelectedBottomPrimalVertex hn hR) 0) 0)
      (squareVertex ((brSelectedBottomPrimalVertex hn hR) 0) (4 * (n : ℤ))) :=
  ((brDoubledSelectedPrimalWalk hn hR).map
      (brFirstContactNormalizeIso n).toHom).copy
    (by
      ext i
      fin_cases i
      · simp [squareVertex]
      · have hb := mem_brSquareBottomSide_iff.mp
          (brSelectedBottomPrimalVertex_mem_bottomSide hn hR)
        simp [squareVertex]
        omega)
    (by
      ext i
      fin_cases i
      · simp [squareVertex]
      · have hb := mem_brSquareBottomSide_iff.mp
          (brSelectedBottomPrimalVertex_mem_bottomSide hn hR)
        simp [squareVertex]
        omega)

private theorem brNormalizedDoubledSelectedPrimalWalk_support_coordinates
    {m n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hm : 2 * n ≤ m) (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R)
    {z : SquareVertex}
    (hz : z ∈ (brNormalizedDoubledSelectedPrimalWalk hn hR).support) :
    0 ≤ z 0 ∧ z 0 ≤ (m : ℤ) ∧
      0 ≤ z 1 ∧ z 1 ≤ 4 * (n : ℤ) := by
  simp only [brNormalizedDoubledSelectedPrimalWalk, SimpleGraph.Walk.support_copy,
    SimpleGraph.Walk.support_map, List.mem_map] at hz
  rcases hz with ⟨x, hx, rfl⟩
  have hxcoords := brDoubledSelectedPrimalWalk_support_coordinates hn hR hx
  change 0 ≤ brFirstContactNormalizeIso n x 0 ∧
    brFirstContactNormalizeIso n x 0 ≤ (m : ℤ) ∧
    0 ≤ brFirstContactNormalizeIso n x 1 ∧
    brFirstContactNormalizeIso n x 1 ≤ 4 * (n : ℤ)
  rw [brFirstContactNormalizeIso_zero, brFirstContactNormalizeIso_one]
  omega

private theorem walkEdgeFinset_map_extensionTranslate_subset
    {m n : ℕ} {u v : SquareVertex} (w : squareGraph.Walk u v)
    (hw : walkEdgeFinset w ⊆ squareBoundaryFreeRectangleEdges m (2 * n)) :
    walkEdgeFinset
        (w.map (brExtensionRectangleTranslateIso n).toHom) ⊆
      brExtensionRectangleEdges m n := by
  classical
  intro e he
  rw [mem_walkEdgeFinset_iff, SimpleGraph.Walk.edges_map] at he
  rcases List.mem_map.mp he with ⟨f, hf, hfe⟩
  let ef : SquareEdge := ⟨f, w.edges_subset_edgeSet hf⟩
  have hef : ef ∈ squareBoundaryFreeRectangleEdges m (2 * n) :=
    hw ((mem_walkEdgeFinset_iff w ef).mpr hf)
  rw [brExtensionRectangleEdges, Finset.mem_map]
  refine ⟨ef, hef, ?_⟩
  apply Subtype.ext
  exact hfe

/-- A horizontal crossing of the doubled rectangle, traversed from right to left, can be trimmed
at its first contact with the selected doubled walk.  The retained arm is open and uses the full
doubled-rectangle support.  Its only doubled-walk vertex is its terminal contact vertex.

The theorem intentionally does not claim that this support is fresh; the module-level audit
explains why that conclusion requires an outermost selector invariant. -/
theorem exists_brFirstContactWalk
    (m : ℕ) {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hm : 2 * n ≤ m) (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R)
    {omega : EdgeConfiguration 2}
    (hcross : omega ∈ brExtensionRectangleCrossingEvent m n) :
    ∃ z ∈ (brDoubledSelectedPrimalWalk hn hR).support,
      ∃ r ∈ brExtensionRectangleRightSide m n,
        ∃ arm : squareGraph.Walk r z,
          walkIsOpen omega arm ∧
          walkEdgeFinset arm ⊆ brExtensionRectangleEdges m n ∧
          ∀ t ∈ (brDoubledSelectedPrimalWalk hn hR).support,
            t ∈ arm.support → t = z := by
  change cubicGraphIsoConfigurationPullback
      (brExtensionRectangleTranslateIso n) omega ∈
    squareBoundaryFreeRectangleCrossingEvent m (2 * n) at hcross
  simp only [squareBoundaryFreeRectangleCrossingEvent, Set.mem_iUnion] at hcross
  rcases hcross with ⟨x, hx, y, hy, w, hwOpen, hwEdges⟩
  let F := brExtensionRectangleTranslateIso n
  let N := brFirstContactNormalizeIso n
  let wa := w.map F.toHom
  have hwaOpen : walkIsOpen omega wa := by
    exact walkIsOpen_map_cubicGraphIso F w hwOpen
  have hwaEdges : walkEdgeFinset wa ⊆ brExtensionRectangleEdges m n := by
    exact walkEdgeFinset_map_extensionTranslate_subset w hwEdges
  have hyRect : y ∈ squareRectangleVertices m (2 * n) :=
    (Finset.mem_filter.mp hy).1
  have hwRect : ∀ z ∈ w.support, z ∈ squareRectangleVertices m (2 * n) :=
    walk_support_mem_rectangle_of_boundaryFree_edges w hyRect hwEdges
  let a : ℤ := N (F x) 1
  let b : ℤ := N (F y) 1
  let ph : squareGraph.Walk (squareVertex 0 a) (squareVertex (m : ℤ) b) :=
    (wa.map N.toHom).copy
      (by
        ext i
        fin_cases i
        · have hx0 := (mem_squareRectangleLeft_iff.mp hx).1
          simp [F, N, squareVertex, hx0]
        · simp [a, squareVertex])
      (by
        ext i
        fin_cases i
        · have hy0 := (mem_squareRectangleRight_iff.mp hy).1
          simp [F, N, squareVertex, hy0]
        · simp [b, squareVertex])
  have haBounds : 0 ≤ a ∧ a ≤ 4 * (n : ℤ) := by
    have hxcoords := mem_squareRectangleLeft_iff.mp hx
    simp [a, F, N]
    omega
  have hbBounds : 0 ≤ b ∧ b ≤ 4 * (n : ℤ) := by
    have hycoords := mem_squareRectangleRight_iff.mp hy
    simp [b, F, N]
    omega
  have hphBox : ∀ z ∈ ph.support,
      0 ≤ z 0 ∧ z 0 ≤ (m : ℤ) ∧
        0 ≤ z 1 ∧ z 1 ≤ 4 * (n : ℤ) := by
    intro z hz
    have hzMap : z ∈ (wa.map N.toHom).support := by
      simpa [ph] using hz
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hzMap
    rcases hzMap with ⟨za, hza, rfl⟩
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hza
    rcases hza with ⟨zs, hzs, rfl⟩
    have hzsCoords := mem_squareRectangleVertices_iff.mp (hwRect zs hzs)
    change 0 ≤ N (F zs) 0 ∧ N (F zs) 0 ≤ (m : ℤ) ∧
      0 ≤ N (F zs) 1 ∧ N (F zs) 1 ≤ 4 * (n : ℤ)
    simp [F, N]
    omega
  let qv := brNormalizedDoubledSelectedPrimalWalk hn hR
  have hcBounds :
      0 ≤ (brSelectedBottomPrimalVertex hn hR) 0 ∧
        (brSelectedBottomPrimalVertex hn hR) 0 ≤ (m : ℤ) := by
    have hb := mem_brSquareBottomSide_iff.mp
      (brSelectedBottomPrimalVertex_mem_bottomSide hn hR)
    omega
  obtain ⟨zn, hznPh, hznQv⟩ := squareWalk_support_inter_rectangle_int
    haBounds.1 haBounds.2 hbBounds.1 hbBounds.2
    hcBounds.1 hcBounds.2 hcBounds.1 hcBounds.2 ph qv hphBox
      (fun z hz ↦ brNormalizedDoubledSelectedPrimalWalk_support_coordinates
        hm hn hR hz)
  have hznMapH : zn ∈ (wa.map N.toHom).support := by
    simpa [ph] using hznPh
  rw [SimpleGraph.Walk.support_map, List.mem_map] at hznMapH
  rcases hznMapH with ⟨zh, hzhWa, hzhNorm⟩
  have hznMapV : zn ∈
      ((brDoubledSelectedPrimalWalk hn hR).map N.toHom).support := by
    simpa [qv, brNormalizedDoubledSelectedPrimalWalk] using hznQv
  rw [SimpleGraph.Walk.support_map, List.mem_map] at hznMapV
  rcases hznMapV with ⟨zv, hzvDoubled, hzvNorm⟩
  have hzhzv : zh = zv := N.injective (hzhNorm.trans hzvNorm.symm)
  subst zv
  let barrier : Finset SquareVertex :=
    (brDoubledSelectedPrimalWalk hn hR).support.toFinset
  let war := wa.reverse
  have hinter : {t ∈ barrier | t ∈ war.support}.Nonempty := by
    refine ⟨zh, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
    · exact List.mem_toFinset.mpr hzvDoubled
    · simpa [war] using hzhWa
  obtain ⟨z, hzBarrier, hzWar, hzFirst⟩ :=
    war.exists_mem_support_forall_mem_support_imp_eq barrier hinter
  have hr : F y ∈ brExtensionRectangleRightSide m n := by
    rw [brExtensionRectangleRightSide, Finset.mem_map]
    exact ⟨y, hy, rfl⟩
  refine ⟨z, List.mem_toFinset.mp hzBarrier, F y, hr,
    war.takeUntil z hzWar, ?_, ?_, ?_⟩
  · exact walkIsOpen_of_edges_subset (walkIsOpen_reverse hwaOpen)
      (war.edges_takeUntil_subset hzWar)
  · exact (walkEdgeFinset_takeUntil_subset war hzWar).trans
      ((walkEdgeFinset_reverse_subset wa).trans hwaEdges)
  · intro t htDoubled htArm
    exact hzFirst t (List.mem_toFinset.mpr htDoubled) htArm

/-- Forgetting first-contact minimality gives a connection from the contact vertex to the right
side on the full doubled-rectangle support. -/
private theorem exists_fullSupport_right_arm_to_doubledSelected
    (m : ℕ) {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hm : 2 * n ≤ m) (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R)
    {omega : EdgeConfiguration 2}
    (hcross : omega ∈ brExtensionRectangleCrossingEvent m n) :
    ∃ z ∈ (brDoubledSelectedPrimalWalk hn hR).support,
      ∃ r ∈ brExtensionRectangleRightSide m n,
        omega ∈ connectionEventIn 2 (brExtensionRectangleEdges m n) z r := by
  obtain ⟨z, hz, r, hr, arm, harmOpen, harmEdges, _hfirst⟩ :=
    exists_brFirstContactWalk m hm hn hR hcross
  exact ⟨z, hz, r, hr, arm.reverse, walkIsOpen_reverse harmOpen,
    (walkEdgeFinset_reverse_subset arm).trans harmEdges⟩

/-- The sound first-contact cover: every doubled-rectangle crossing makes full-support contact
with the selected lower crossing or with its reflected upper copy. -/
theorem brExtensionRectangleCrossingEvent_subset_contact_union
    (m : ℕ) {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hm : 2 * n ≤ m) (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    brExtensionRectangleCrossingEvent m n ⊆
      brLowerContactEvent m hn hR ∪ brUpperContactEvent m hn hR := by
  intro omega hcross
  obtain ⟨z, hzDoubled, r, hr, hzr⟩ :=
    exists_fullSupport_right_arm_to_doubledSelected m hm hn hR hcross
  rw [brDoubledSelectedPrimalWalk_support_iff hn hR] at hzDoubled
  rcases hzDoubled with hzLower | hzUpper
  · exact Or.inl ⟨z, hzLower, r, hr, hzr⟩
  · right
    change cubicGraphIsoConfigurationPullback
        (brPrimalTopReflectionIso n) omega ∈ brLowerContactEvent m hn hR
    refine ⟨brPrimalTopReflectionIso n z,
      (brReflectedSelectedPrimalWalk_support_iff hn hR).mp hzUpper,
      brPrimalTopReflectionIso n r, ?_, ?_⟩
    · rw [mem_brExtensionRectangleRightSide_iff]
      have hrCoords := mem_brExtensionRectangleRightSide_iff.mp hr
      simp only [brPrimalTopReflectionIso_zero, brPrimalTopReflectionIso_one]
      omega
    · rw [cubicGraphIsoConfigurationPullback_mem_connectionEventIn_iff,
        brPrimalTopReflectionIso_image_extensionRectangleEdges,
        brPrimalTopReflectionIso_involutive,
        brPrimalTopReflectionIso_involutive]
      exact hzr

/-- Exact bridge required from an outermost/stopping-set selector: if every full lower contact
can be witnessed on fresh coordinates, reflection supplies the upper statement and the genuine
fresh cover follows.  The current arbitrary parity selector does not provide `hfresh`. -/
theorem brExtensionRectangleCrossingEvent_subset_fresh_union_of_contact_fresh
    (m : ℕ) {n : ℕ} (R : Finset (BRLeftmostDualVertex n))
    (hm : 2 * n ≤ m) (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R)
    (hfresh : brLowerContactEvent m hn hR ⊆
      brLowerFreshExtensionEvent m R hn hR) :
    brExtensionRectangleCrossingEvent m n ⊆
      brLowerFreshExtensionEvent m R hn hR ∪
        brUpperFreshExtensionEvent m R hn hR := by
  intro omega hcross
  rcases brExtensionRectangleCrossingEvent_subset_contact_union m hm hn hR hcross with
    hLower | hUpper
  · exact Or.inl (hfresh hLower)
  · right
    change cubicGraphIsoConfigurationPullback
        (brPrimalTopReflectionIso n) omega ∈
      brLowerFreshExtensionEvent m R hn hR
    exact hfresh hUpper

/-- Conditional Bollobás--Riordan half estimate.  The sole geometric premise `hfresh` is the
outermost-selector/stopping-set implication isolated by the audit; no such implication is
asserted for the current arbitrary parity selector. -/
theorem bernoulliBondMeasure_real_extensionCrossing_div_two_le_lowerFresh_of_contact_fresh
    (p : I) (m : ℕ) {n : ℕ} (R : Finset (BRLeftmostDualVertex n))
    (hm : 2 * n ≤ m) (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R)
    (hfresh : brLowerContactEvent m hn hR ⊆
      brLowerFreshExtensionEvent m R hn hR) :
    (bernoulliBondMeasure 2 p).real (brExtensionRectangleCrossingEvent m n) / 2 ≤
      (bernoulliBondMeasure 2 p).real
        (brLowerFreshExtensionEvent m R hn hR) := by
  exact measureReal_div_two_le_of_subset_union_of_eq
    (bernoulliBondMeasure 2 p)
    (brExtensionRectangleCrossingEvent_subset_fresh_union_of_contact_fresh
      m R hm hn hR hfresh)
    (bernoulliBondMeasure_real_brUpperFreshExtensionEvent_eq_lower
      p m R hn hR)

end

end Percolation
