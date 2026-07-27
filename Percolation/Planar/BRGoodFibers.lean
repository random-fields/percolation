import Percolation.Bernoulli.FiniteFiberIndependence
import Percolation.Planar.BRFiberGeometry

/-!
# Good fibers of the stopped dual exploration

This module packages the configurations whose stopped exploration does not reach the right
target column as an exact finite disjoint union of reached-face fibers.  It contains no planar
separation claim: identifying this event with a primal vertical crossing is a later deterministic
geometry theorem.
-/

namespace Percolation

open MeasureTheory

noncomputable section

/-- Reached-face sets which avoid the right target column. -/
def brGoodReachableFaceFiberIndices (n : ℕ) :
    Finset (Finset (BRLeftmostDualVertex n)) :=
  (brReachableFaceFiberIndices n).filter fun R ↦
    Disjoint R (brRightmostDualTargets n)

@[simp]
theorem mem_brGoodReachableFaceFiberIndices_iff
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)} :
    R ∈ brGoodReachableFaceFiberIndices n ↔
      Disjoint R (brRightmostDualTargets n) := by
  simp [brGoodReachableFaceFiberIndices]

/-- The event that the stopped dual flood fill does not reach the right target column. -/
def brRightTargetsUnreachedEvent (n : ℕ) : Set (EdgeConfiguration 2) :=
  {ω | Disjoint (brLeftReachableFaces n ω) (brRightmostDualTargets n)}

/-- The complementary event that some right target is reached by the stopped exploration. -/
def brRightTargetsReachedEvent (n : ℕ) : Set (EdgeConfiguration 2) :=
  {ω | ∃ y ∈ brRightmostDualTargets n, y ∈ brLeftReachableFaces n ω}

@[simp]
theorem mem_brRightTargetsUnreachedEvent_iff
    {n : ℕ} {ω : EdgeConfiguration 2} :
    ω ∈ brRightTargetsUnreachedEvent n ↔
      Disjoint (brLeftReachableFaces n ω) (brRightmostDualTargets n) :=
  Iff.rfl

@[simp]
theorem mem_brRightTargetsReachedEvent_iff
    {n : ℕ} {ω : EdgeConfiguration 2} :
    ω ∈ brRightTargetsReachedEvent n ↔
      ∃ y ∈ brRightmostDualTargets n, y ∈ brLeftReachableFaces n ω :=
  Iff.rfl

/-- Reaching and avoiding the right target column are exact complementary events. -/
theorem brRightTargetsReachedEvent_eq_compl_unreached (n : ℕ) :
    brRightTargetsReachedEvent n = (brRightTargetsUnreachedEvent n)ᶜ := by
  ext ω
  rw [Set.mem_compl_iff, mem_brRightTargetsUnreachedEvent_iff,
    mem_brRightTargetsReachedEvent_iff, Finset.not_disjoint_iff]
  constructor
  · rintro ⟨y, hyTarget, hyReach⟩
    exact ⟨y, hyReach, hyTarget⟩
  · rintro ⟨y, hyReach, hyTarget⟩
    exact ⟨y, hyTarget, hyReach⟩

/-- A reached right target is witnessed by an exploration-open frame walk from a left source. -/
theorem mem_brRightTargetsReachedEvent_iff_exists_open_walk
    {n : ℕ} {ω : EdgeConfiguration 2} :
    ω ∈ brRightTargetsReachedEvent n ↔
      ∃ y ∈ brRightmostDualTargets n,
        ∃ x ∈ brLeftmostDualSources n,
          ∃ w : (brLeftmostDualGraph n).Walk x y,
            finiteGraphWalkIsOpen
              (brClosedDualExplorationConfiguration n ω) w := by
  simp only [mem_brRightTargetsReachedEvent_iff, brLeftReachableFaces,
    mem_finiteGraphReachableVertices_iff, finiteGraphReachableFrom]

/-- Avoidance of the right target column is exactly the union of the good stopped fibers. -/
theorem brRightTargetsUnreachedEvent_eq_biUnion_good_fibers (n : ℕ) :
    brRightTargetsUnreachedEvent n =
      ⋃ R ∈ brGoodReachableFaceFiberIndices n, brReachableFaceFiber n R := by
  ext ω
  simp only [mem_brRightTargetsUnreachedEvent_iff, Set.mem_iUnion]
  constructor
  · intro hgood
    refine ⟨brLeftReachableFaces n ω, ?_, mem_brReachableFaceFiber_self n ω⟩
    exact mem_brGoodReachableFaceFiberIndices_iff.mpr hgood
  · rintro ⟨R, hR, hω⟩
    have hgood := mem_brGoodReachableFaceFiberIndices_iff.mp hR
    change brLeftReachableFaces n ω = R at hω
    simpa [hω] using hgood

/-- Good stopped fibers remain pairwise disjoint after restricting the full fiber partition. -/
theorem pairwiseDisjoint_brGoodReachableFaceFiber (n : ℕ) :
    Set.PairwiseDisjoint
      (brGoodReachableFaceFiberIndices n :
        Set (Finset (BRLeftmostDualVertex n)))
      (brReachableFaceFiber n) := by
  intro R hR S hS hRS
  exact pairwiseDisjoint_brReachableFaceFiber n
    (mem_brReachableFaceFiberIndices R)
    (mem_brReachableFaceFiberIndices S) hRS

/-- Every nonempty good fiber is an admissible separating fiber. -/
theorem brAdmissibleSeparatingFiber_of_mem_good_of_mem_fiber
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    {ω : EdgeConfiguration 2}
    (hR : R ∈ brGoodReachableFaceFiberIndices n)
    (hω : ω ∈ brReachableFaceFiber n R) :
    BRAdmissibleSeparatingFiber n R :=
  ⟨⟨ω, hω⟩, mem_brGoodReachableFaceFiberIndices_iff.mp hR⟩

/-- The event of avoiding the right target column is measurable. -/
theorem measurableSet_brRightTargetsUnreachedEvent (n : ℕ) :
    MeasurableSet (brRightTargetsUnreachedEvent n) := by
  rw [brRightTargetsUnreachedEvent_eq_biUnion_good_fibers]
  exact (brGoodReachableFaceFiberIndices n).measurableSet_biUnion fun R _hR ↦
    measurableSet_brReachableFaceFiber n R

/-- The event that the exploration reaches the right target column is measurable. -/
theorem measurableSet_brRightTargetsReachedEvent (n : ℕ) :
    MeasurableSet (brRightTargetsReachedEvent n) := by
  rw [brRightTargetsReachedEvent_eq_compl_unreached]
  exact (measurableSet_brRightTargetsUnreachedEvent n).compl

/-- Real measure of the good event is the finite sum of its fiber measures. -/
theorem measureReal_brRightTargetsUnreachedEvent_eq_sum_fibers
    (μ : Measure (EdgeConfiguration 2)) [IsFiniteMeasure μ] (n : ℕ) :
    μ.real (brRightTargetsUnreachedEvent n) =
      ∑ R ∈ brGoodReachableFaceFiberIndices n,
        μ.real (brReachableFaceFiber n R) := by
  rw [brRightTargetsUnreachedEvent_eq_biUnion_good_fibers]
  exact measureReal_biUnion_finset
    (pairwiseDisjoint_brGoodReachableFaceFiber n)
    (fun R _hR ↦ measurableSet_brReachableFaceFiber n R)

/-- Sum per-fiber extension estimates and then use a deterministic event inclusion.

This is the ratio-free probability step used by the adapted Bollobás--Riordan lemma.  Geometry
enters only through `hsubset`; no conditioning on a possibly null fiber is required. -/
theorem mul_measureReal_brRightTargetsUnreachedEvent_le_of_fiber_extensions
    (μ : Measure (EdgeConfiguration 2)) [IsFiniteMeasure μ]
    (n : ℕ)
    (extension : Finset (BRLeftmostDualVertex n) → Set (EdgeConfiguration 2))
    (target : Set (EdgeConfiguration 2)) (q : ℝ)
    (hextension : ∀ R ∈ brGoodReachableFaceFiberIndices n,
      MeasurableSet (extension R))
    (hlower : ∀ R ∈ brGoodReachableFaceFiberIndices n,
      q * μ.real (brReachableFaceFiber n R) ≤
        μ.real (brReachableFaceFiber n R ∩ extension R))
    (hsubset :
      (⋃ R ∈ brGoodReachableFaceFiberIndices n,
        brReachableFaceFiber n R ∩ extension R) ⊆ target) :
    q * μ.real (brRightTargetsUnreachedEvent n) ≤ μ.real target := by
  apply (mul_measureReal_le_biUnion_inter_of_partition μ
    (brGoodReachableFaceFiberIndices n)
    (brRightTargetsUnreachedEvent n)
    (brReachableFaceFiber n) extension q
    (brRightTargetsUnreachedEvent_eq_biUnion_good_fibers n)
    (pairwiseDisjoint_brGoodReachableFaceFiber n)
    (fun R _hR ↦ measurableSet_brReachableFaceFiber n R)
    hextension hlower).trans
  exact measureReal_mono hsubset

end

end Percolation
