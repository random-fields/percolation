import Percolation.Bernoulli.ForcedOpenConditioning
import Percolation.Planar.RSWStoppedTail

/-!
# Fiber-safe stopped-tail conditioning

This file isolates the exact finite-coordinate content of Grimmett's `H`/`J` correction.  A
stopped-square edge is retained when it was not exposed by the stopped dual fiber, or when every
configuration in that fiber forces it open.  Consequently a tail-contact event on this support
is positively correlated with the fiber without assuming that the fiber itself is increasing.

The remaining planar obligation is now the literal safe-contact cover: every stopped-square
crossing can be trimmed or rewired to one of the two reflected safe supports.  No probabilistic
or measure-theoretic claim is hidden in that obligation.
-/

namespace Percolation

open SimpleGraph MeasureTheory ProbabilityTheory
open scoped unitInterval

noncomputable section

/-- Stopped-square bonds which are either unexposed by the fiber or forced open throughout it. -/
def rswStoppedFiberSafeEdges
    (n : ℕ) (R : Finset (BRLeftmostDualVertex n)) : Finset SquareEdge := by
  classical
  exact (rswStoppedSquareEdges n).filter fun e ↦
    e ∉ brReachableFaceFiberSupport n R ∨
      ∀ omega ∈ brReachableFaceFiber n R, e ∈ omega

theorem rswStoppedFiberSafeEdges_subset_stoppedSquare
    (n : ℕ) (R : Finset (BRLeftmostDualVertex n)) :
    rswStoppedFiberSafeEdges n R ⊆ rswStoppedSquareEdges n :=
  by
    classical
    exact Finset.filter_subset _ _

/-- Any safe coordinate also exposed by the fiber is open on the entire fiber. -/
theorem mem_of_mem_fiber_of_mem_safe_of_mem_fiberSupport
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    {omega : EdgeConfiguration 2} (homega : omega ∈ brReachableFaceFiber n R)
    {e : SquareEdge} (heSafe : e ∈ rswStoppedFiberSafeEdges n R)
    (heFiber : e ∈ brReachableFaceFiberSupport n R) : e ∈ omega := by
  classical
  rw [rswStoppedFiberSafeEdges, Finset.mem_filter] at heSafe
  exact heSafe.2.elim (fun h ↦ (h heFiber).elim) (fun h ↦ h omega homega)

/-- Contact from the selected stopped tail to the right side using only fiber-safe bonds. -/
def brStoppedLowerSafeTailContactEvent
    {n : ℕ} (R : Finset (BRLeftmostDualVertex n))
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    Set (EdgeConfiguration 2) :=
  ⋃ z ∈ (brFilledHullSelectedUpperTailPath hn hR).support.toFinset,
    ⋃ r ∈ rswStoppedSquareRightSide n,
      connectionEventIn 2 (rswStoppedFiberSafeEdges n R) z r

/-- The reflected safe-tail event, used only for the square-root split. -/
def brStoppedUpperSafeTailContactEvent
    {n : ℕ} (R : Finset (BRLeftmostDualVertex n))
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    Set (EdgeConfiguration 2) :=
  cubicGraphIsoEvent (brPrimalTopReflectionIso n)
    (brStoppedLowerSafeTailContactEvent R hn hR)

theorem dependsOn_brStoppedLowerSafeTailContactEvent
    {n : ℕ} (R : Finset (BRLeftmostDualVertex n))
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    DependsOn (rswStoppedFiberSafeEdges n R)
      (brStoppedLowerSafeTailContactEvent R hn hR) := by
  intro omega eta hagree
  simp only [brStoppedLowerSafeTailContactEvent, Set.mem_iUnion]
  constructor
  · rintro ⟨z, hz, r, hr, hzr⟩
    exact ⟨z, hz, r, hr,
      (dependsOn_connectionEventIn 2 (rswStoppedFiberSafeEdges n R) z r hagree).mp hzr⟩
  · rintro ⟨z, hz, r, hr, hzr⟩
    exact ⟨z, hz, r, hr,
      (dependsOn_connectionEventIn 2 (rswStoppedFiberSafeEdges n R) z r hagree).mpr hzr⟩

theorem measurableSet_brStoppedLowerSafeTailContactEvent
    {n : ℕ} (R : Finset (BRLeftmostDualVertex n))
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    MeasurableSet (brStoppedLowerSafeTailContactEvent R hn hR) :=
  (dependsOn_brStoppedLowerSafeTailContactEvent R hn hR).measurableSet

theorem isIncreasingEvent_brStoppedLowerSafeTailContactEvent
    {n : ℕ} (R : Finset (BRLeftmostDualVertex n))
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    IsIncreasingEvent (brStoppedLowerSafeTailContactEvent R hn hR) := by
  intro omega eta hmono
  simp only [brStoppedLowerSafeTailContactEvent, Set.mem_iUnion]
  rintro ⟨z, hz, r, hr, hzr⟩
  exact ⟨z, hz, r, hr,
    isIncreasingEvent_connectionEventIn 2 (rswStoppedFiberSafeEdges n R) z r hmono hzr⟩

theorem measurableSet_brStoppedUpperSafeTailContactEvent
    {n : ℕ} (R : Finset (BRLeftmostDualVertex n))
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    MeasurableSet (brStoppedUpperSafeTailContactEvent R hn hR) :=
  measurableSet_cubicGraphIsoEvent _
    (measurableSet_brStoppedLowerSafeTailContactEvent R hn hR)

theorem isIncreasingEvent_brStoppedUpperSafeTailContactEvent
    {n : ℕ} (R : Finset (BRLeftmostDualVertex n))
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    IsIncreasingEvent (brStoppedUpperSafeTailContactEvent R hn hR) :=
  isIncreasingEvent_cubicGraphIsoEvent _
    (isIncreasingEvent_brStoppedLowerSafeTailContactEvent R hn hR)

theorem bernoulliBondMeasure_real_brStoppedUpperSafeTailContactEvent_eq_lower
    (p : I) {n : ℕ} (R : Finset (BRLeftmostDualVertex n))
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    (bernoulliBondMeasure 2 p).real
        (brStoppedUpperSafeTailContactEvent R hn hR) =
      (bernoulliBondMeasure 2 p).real
        (brStoppedLowerSafeTailContactEvent R hn hR) :=
  bernoulliBondMeasure_real_cubicGraphIsoEvent p _
    (measurableSet_brStoppedLowerSafeTailContactEvent R hn hR)

/-- A safe contact is, in particular, an ordinary stopped-tail contact. -/
theorem brStoppedLowerSafeTailContactEvent_subset_tailContact
    {n : ℕ} (R : Finset (BRLeftmostDualVertex n))
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    brStoppedLowerSafeTailContactEvent R hn hR ⊆
      brStoppedLowerTailContactEvent R hn hR := by
  intro omega homega
  simp only [brStoppedLowerSafeTailContactEvent,
    brStoppedLowerTailContactEvent, Set.mem_iUnion] at homega ⊢
  obtain ⟨z, hz, r, hr, hzr⟩ := homega
  exact ⟨z, hz, r, hr, connectionEventIn_mono
    (rswStoppedFiberSafeEdges_subset_stoppedSquare n R) z r hzr⟩

/-- The square-root probability estimate follows from the exact safe-contact cover. -/
theorem one_sub_sqrt_rswSquare_le_brStoppedLowerSafeTailContactProbability_of_cover
    (p : I) {n : ℕ} (R : Finset (BRLeftmostDualVertex n))
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R)
    (hcover : rswStoppedSquareCrossingEvent n ⊆
      brStoppedLowerSafeTailContactEvent R hn hR ∪
        brStoppedUpperSafeTailContactEvent R hn hR) :
    1 - Real.sqrt (1 - rswSquareCrossingProbability p n) ≤
      (bernoulliBondMeasure 2 p).real
        (brStoppedLowerSafeTailContactEvent R hn hR) := by
  rw [← bernoulliBondMeasure_real_rswStoppedSquareCrossingEvent p n]
  exact one_sub_sqrt_one_sub_measureReal_le_of_subset_union_of_eq (d := 2) p
    (H := rswStoppedSquareCrossingEvent n)
    (L := brStoppedLowerSafeTailContactEvent R hn hR)
    (U := brStoppedUpperSafeTailContactEvent R hn hR)
    hcover
    (bernoulliBondMeasure_real_brStoppedUpperSafeTailContactEvent_eq_lower p R hn hR)
    (isIncreasingEvent_brStoppedLowerSafeTailContactEvent R hn hR)
    (isIncreasingEvent_brStoppedUpperSafeTailContactEvent R hn hR)
    (measurableSet_brStoppedLowerSafeTailContactEvent R hn hR)
    (measurableSet_brStoppedUpperSafeTailContactEvent R hn hR)

/-- The fiber is positively correlated with its safe stopped-tail event. -/
theorem fiber_mul_safeTailContactProbability_le_inter
    (p : I) {n : ℕ} (R : Finset (BRLeftmostDualVertex n))
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    (bernoulliBondMeasure 2 p).real (brReachableFaceFiber n R) *
        (bernoulliBondMeasure 2 p).real
          (brStoppedLowerSafeTailContactEvent R hn hR) ≤
      (bernoulliBondMeasure 2 p).real
        (brReachableFaceFiber n R ∩
          brStoppedLowerSafeTailContactEvent R hn hR) := by
  exact setBernoulli_real_mul_le_inter_of_forces_open p
    (dependsOn_brReachableFaceFiber n R)
    (dependsOn_brStoppedLowerSafeTailContactEvent R hn hR)
    (isIncreasingEvent_brStoppedLowerSafeTailContactEvent R hn hR)
    (fun omega homega e heFiber heSafe ↦
      mem_of_mem_fiber_of_mem_safe_of_mem_fiberSupport
        homega heSafe heFiber)

/-- Ratio-free fixed-fiber estimate, conditional only on the safe-contact cover. -/
theorem one_sub_sqrt_rswSquare_mul_fiber_le_inter_safeTailContact_of_cover
    (p : I) {n : ℕ} (R : Finset (BRLeftmostDualVertex n))
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R)
    (hcover : rswStoppedSquareCrossingEvent n ⊆
      brStoppedLowerSafeTailContactEvent R hn hR ∪
        brStoppedUpperSafeTailContactEvent R hn hR) :
    (1 - Real.sqrt (1 - rswSquareCrossingProbability p n)) *
        (bernoulliBondMeasure 2 p).real (brReachableFaceFiber n R) ≤
      (bernoulliBondMeasure 2 p).real
        (brReachableFaceFiber n R ∩
          brStoppedLowerSafeTailContactEvent R hn hR) := by
  calc
    (1 - Real.sqrt (1 - rswSquareCrossingProbability p n)) *
          (bernoulliBondMeasure 2 p).real (brReachableFaceFiber n R) ≤
        (bernoulliBondMeasure 2 p).real
            (brStoppedLowerSafeTailContactEvent R hn hR) *
          (bernoulliBondMeasure 2 p).real (brReachableFaceFiber n R) :=
      mul_le_mul_of_nonneg_right
        (one_sub_sqrt_rswSquare_le_brStoppedLowerSafeTailContactProbability_of_cover
          p R hn hR hcover) measureReal_nonneg
    _ = (bernoulliBondMeasure 2 p).real (brReachableFaceFiber n R) *
          (bernoulliBondMeasure 2 p).real
            (brStoppedLowerSafeTailContactEvent R hn hR) := mul_comm _ _
    _ ≤ (bernoulliBondMeasure 2 p).real
          (brReachableFaceFiber n R ∩
            brStoppedLowerSafeTailContactEvent R hn hR) :=
      fiber_mul_safeTailContactProbability_le_inter p R hn hR

end

end Percolation
