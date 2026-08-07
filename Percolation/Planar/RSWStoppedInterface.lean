import Percolation.Core.CubicWalkLevel
import Percolation.Planar.BRCrossingExtension
import Percolation.Planar.RSWEndpointSplit

/-!
# Stopped outer interfaces for Grimmett's lowest-crossing estimate

This file refines the filled Bollobas--Riordan outer interface at its last visit to the
horizontal midline.  After a quarter-turn, this is the tail of Grimmett's lowest crossing from
its last visit to the vertical axis.  Keeping the tail as a fiber-determined object is the key
deterministic input for Lemma 11.73.
-/

namespace Percolation

open SimpleGraph MeasureTheory ProbabilityTheory
open scoped unitInterval

noncomputable section

/-- The first visit to height zero when the filled-hull interface is traversed backwards from
its top endpoint.  Equivalently, this is the last height-zero visit in the bottom-to-top
orientation. -/
private theorem exists_brFilledHullSelectedUpperTailData
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    ∃ z : SquareVertex, ∃ q : squareGraph.Walk
        (brSelectedTopPrimalVertex hn hR.filledHull) z,
      z 1 = 0 ∧
        (∀ x ∈ q.support, 0 ≤ x 1) ∧
        (∀ x ∈ q.support,
          x ∈ (brSelectedPrimalWalk hn hR.filledHull).support) ∧
        q.edges <+: (brSelectedPrimalWalk hn hR.filledHull).reverse.edges ∧
        ∀ x ∈ q.support, x 1 = 0 → x = z := by
  let w := (brSelectedPrimalWalk hn hR.filledHull).reverse
  have htop := mem_brSquareTopSide_iff.mp
    (brSelectedTopPrimalVertex_mem_topSide hn hR.filledHull)
  have hbottom := mem_brSquareBottomSide_iff.mp
    (brSelectedBottomPrimalVertex_mem_bottomSide hn hR.filledHull)
  obtain ⟨z, q, hz, hqSide, hqSupport, hqPrefix, hqUnique⟩ :=
    exists_cubicWalk_edgePrefix_to_level_of_end_le_unique
      (G := squareGraph) le_rfl w (1 : Fin 2) 0 (by omega) (by omega)
  refine ⟨z, q, hz, hqSide, ?_, hqPrefix, hqUnique⟩
  intro x hx
  have hx' := hqSupport x hx
  simpa only [w, SimpleGraph.Walk.support_reverse, List.mem_reverse] using hx'

/-- Last midline vertex of the filled outer interface. -/
def brFilledHullLastMidlineVertex
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) : SquareVertex :=
  Classical.choose (exists_brFilledHullSelectedUpperTailData hn hR)

/-- The filled outer-interface tail, traversed from its top endpoint back to its last midline
vertex. -/
def brFilledHullSelectedUpperTail
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    squareGraph.Walk (brSelectedTopPrimalVertex hn hR.filledHull)
      (brFilledHullLastMidlineVertex hn hR) :=
  Classical.choose (Classical.choose_spec
    (exists_brFilledHullSelectedUpperTailData hn hR))

/-- The loop-erased stopped upper tail.  Unlike the ambient resolved-boundary traversal this is
an actual simple path, while retaining the same endpoints and using only edges of the stopped
tail. -/
def brFilledHullSelectedUpperTailPath
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    squareGraph.Walk (brSelectedTopPrimalVertex hn hR.filledHull)
      (brFilledHullLastMidlineVertex hn hR) :=
  (brFilledHullSelectedUpperTail hn hR).toPath

theorem brFilledHullSelectedUpperTailPath_isPath
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    (brFilledHullSelectedUpperTailPath hn hR).IsPath :=
  (brFilledHullSelectedUpperTail hn hR).toPath.property

theorem brFilledHullLastMidlineVertex_one
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    brFilledHullLastMidlineVertex hn hR 1 = 0 :=
  (Classical.choose_spec (Classical.choose_spec
    (exists_brFilledHullSelectedUpperTailData hn hR))).1

theorem brFilledHullSelectedUpperTail_support_nonnegative
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R)
    {x : SquareVertex} (hx : x ∈ (brFilledHullSelectedUpperTail hn hR).support) :
    0 ≤ x 1 :=
  (Classical.choose_spec (Classical.choose_spec
    (exists_brFilledHullSelectedUpperTailData hn hR))).2.1 x hx

theorem brFilledHullSelectedUpperTail_support_subset_selected
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    ∀ x ∈ (brFilledHullSelectedUpperTail hn hR).support,
      x ∈ (brSelectedPrimalWalk hn hR.filledHull).support :=
  (Classical.choose_spec (Classical.choose_spec
    (exists_brFilledHullSelectedUpperTailData hn hR))).2.2.1

theorem brFilledHullSelectedUpperTail_edges_prefix_reverse
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    (brFilledHullSelectedUpperTail hn hR).edges <+:
      (brSelectedPrimalWalk hn hR.filledHull).reverse.edges :=
  (Classical.choose_spec (Classical.choose_spec
    (exists_brFilledHullSelectedUpperTailData hn hR))).2.2.2.1

theorem brFilledHullSelectedUpperTail_midline_unique
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R)
    {x : SquareVertex} (hx : x ∈ (brFilledHullSelectedUpperTail hn hR).support)
    (hx0 : x 1 = 0) :
    x = brFilledHullLastMidlineVertex hn hR :=
  (Classical.choose_spec (Classical.choose_spec
    (exists_brFilledHullSelectedUpperTailData hn hR))).2.2.2.2 x hx hx0

theorem brFilledHullSelectedUpperTailPath_support_nonnegative
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R)
    {x : SquareVertex}
    (hx : x ∈ (brFilledHullSelectedUpperTailPath hn hR).support) :
    0 ≤ x 1 := by
  apply brFilledHullSelectedUpperTail_support_nonnegative hn hR
  exact (brFilledHullSelectedUpperTail hn hR).support_toPath_subset hx

theorem brFilledHullSelectedUpperTailPath_support_subset_selected
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    ∀ x ∈ (brFilledHullSelectedUpperTailPath hn hR).support,
      x ∈ (brSelectedPrimalWalk hn hR.filledHull).support := by
  intro x hx
  apply brFilledHullSelectedUpperTail_support_subset_selected hn hR
  exact (brFilledHullSelectedUpperTail hn hR).support_toPath_subset hx

theorem brFilledHullSelectedUpperTailPath_midline_unique
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R)
    {x : SquareVertex}
    (hx : x ∈ (brFilledHullSelectedUpperTailPath hn hR).support)
    (hx0 : x 1 = 0) :
    x = brFilledHullLastMidlineVertex hn hR := by
  apply brFilledHullSelectedUpperTail_midline_unique hn hR
  · exact (brFilledHullSelectedUpperTail hn hR).support_toPath_subset hx
  · exact hx0

theorem walkEdgeFinset_brFilledHullSelectedUpperTailPath_subset_boundaryFree
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    walkEdgeFinset (brFilledHullSelectedUpperTailPath hn hR) ⊆
      squareBoundaryFreeRectangleEdges (2 * n) n := by
  intro e he
  rw [mem_walkEdgeFinset_iff] at he
  have heTail : (e : Sym2 SquareVertex) ∈
      (brFilledHullSelectedUpperTail hn hR).edges :=
    (brFilledHullSelectedUpperTail hn hR).edges_toPath_subset he
  have heSelectedReverse : (e : Sym2 SquareVertex) ∈
      (brSelectedPrimalWalk hn hR.filledHull).reverse.edges :=
    (brFilledHullSelectedUpperTail_edges_prefix_reverse hn hR).sublist.subset heTail
  have heSelected : (e : Sym2 SquareVertex) ∈
      (brSelectedPrimalWalk hn hR.filledHull).edges := by
    simpa only [SimpleGraph.Walk.edges_reverse, List.mem_reverse] using heSelectedReverse
  exact walkEdgeFinset_brSelectedPrimalWalk_subset_boundaryFree hn hR.filledHull
    ((mem_walkEdgeFinset_iff _ e).mpr heSelected)

theorem walkIsOpen_brFilledHullSelectedUpperTailPath_of_mem_fiber
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R)
    {omega : EdgeConfiguration 2} (homega : omega ∈ brReachableFaceFiber n R) :
    walkIsOpen omega (brFilledHullSelectedUpperTailPath hn hR) := by
  apply walkIsOpen_toPath
  apply walkIsOpen_of_edges_subset
    (walkIsOpen_brSelectedPrimalWalk_filledHull_of_mem_fiber hn hR homega)
  intro e he
  have heReverse :=
    (brFilledHullSelectedUpperTail_edges_prefix_reverse hn hR).sublist.subset he
  simpa only [SimpleGraph.Walk.edges_reverse, List.mem_reverse] using heReverse

/-! ### The doubled stopped barrier -/

/-- Reflection of the simple stopped tail across the line `y = n`. -/
def brReflectedFilledHullSelectedUpperTailPath
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    squareGraph.Walk (brSelectedTopPrimalVertex hn hR.filledHull)
      (brPrimalTopReflectionIso n (brFilledHullLastMidlineVertex hn hR)) :=
  ((brFilledHullSelectedUpperTailPath hn hR).map
      (brPrimalTopReflectionIso n).toHom).copy
    (brPrimalTopReflectionIso_selectedTop hn hR.filledHull) rfl

/-- The stopped tail from the midline to the top side, followed by its reflection.  This is the
bottom--top barrier in `[0,2n] × [0,2n]` used for the conditional contact event in Grimmett,
Lemma 11.73. -/
def brFilledHullStoppedBarrier
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    squareGraph.Walk (brFilledHullLastMidlineVertex hn hR)
      (brPrimalTopReflectionIso n (brFilledHullLastMidlineVertex hn hR)) :=
  (brFilledHullSelectedUpperTailPath hn hR).reverse.append
    (brReflectedFilledHullSelectedUpperTailPath hn hR)

@[simp]
theorem mem_brReflectedFilledHullSelectedUpperTailPath_support_iff
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R)
    {z : SquareVertex} :
    z ∈ (brReflectedFilledHullSelectedUpperTailPath hn hR).support ↔
      brPrimalTopReflectionIso n z ∈
        (brFilledHullSelectedUpperTailPath hn hR).support := by
  simp only [brReflectedFilledHullSelectedUpperTailPath,
    SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map, List.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    change brPrimalTopReflectionIso n (brPrimalTopReflectionIso n x) ∈
      (brFilledHullSelectedUpperTailPath hn hR).support
    simpa only [brPrimalTopReflectionIso_involutive] using hx
  · intro hz
    refine ⟨brPrimalTopReflectionIso n z, hz, ?_⟩
    exact brPrimalTopReflectionIso_involutive n z

@[simp]
theorem mem_brFilledHullStoppedBarrier_support_iff
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R)
    {z : SquareVertex} :
    z ∈ (brFilledHullStoppedBarrier hn hR).support ↔
      z ∈ (brFilledHullSelectedUpperTailPath hn hR).support ∨
        z ∈ (brReflectedFilledHullSelectedUpperTailPath hn hR).support := by
  simp [brFilledHullStoppedBarrier]

theorem brFilledHullStoppedBarrier_start_coordinates
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    0 ≤ brFilledHullLastMidlineVertex hn hR 0 ∧
      brFilledHullLastMidlineVertex hn hR 0 ≤ 2 * (n : ℤ) ∧
      brFilledHullLastMidlineVertex hn hR 1 = 0 := by
  have hmem : brFilledHullLastMidlineVertex hn hR ∈
      (brSelectedPrimalWalk hn hR.filledHull).support :=
    brFilledHullSelectedUpperTail_support_subset_selected hn hR _
      (brFilledHullSelectedUpperTail hn hR).end_mem_support
  have hcoords := brSelectedPrimalWalk_support_coordinates hn hR.filledHull hmem
  exact ⟨hcoords.1, hcoords.2.1, brFilledHullLastMidlineVertex_one hn hR⟩

theorem brFilledHullStoppedBarrier_end_coordinates
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    0 ≤ brPrimalTopReflectionIso n
        (brFilledHullLastMidlineVertex hn hR) 0 ∧
      brPrimalTopReflectionIso n
          (brFilledHullLastMidlineVertex hn hR) 0 ≤ 2 * (n : ℤ) ∧
      brPrimalTopReflectionIso n
          (brFilledHullLastMidlineVertex hn hR) 1 = 2 * (n : ℤ) := by
  have hz := brFilledHullStoppedBarrier_start_coordinates hn hR
  simp only [brPrimalTopReflectionIso_zero, brPrimalTopReflectionIso_one]
  omega

theorem brFilledHullStoppedBarrier_support_coordinates
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R)
    {z : SquareVertex} (hz : z ∈ (brFilledHullStoppedBarrier hn hR).support) :
    0 ≤ z 0 ∧ z 0 ≤ 2 * (n : ℤ) ∧
      0 ≤ z 1 ∧ z 1 ≤ 2 * (n : ℤ) := by
  rw [mem_brFilledHullStoppedBarrier_support_iff hn hR] at hz
  rcases hz with hz | hz
  · have hselected := brFilledHullSelectedUpperTailPath_support_subset_selected
        hn hR z hz
    have hcoords := brSelectedPrimalWalk_support_coordinates hn hR.filledHull hselected
    have hzNonnegative := brFilledHullSelectedUpperTailPath_support_nonnegative hn hR hz
    omega
  · have hreflected :=
      (mem_brReflectedFilledHullSelectedUpperTailPath_support_iff hn hR).mp hz
    have hselected := brFilledHullSelectedUpperTailPath_support_subset_selected
      hn hR _ hreflected
    have hcoords := brSelectedPrimalWalk_support_coordinates hn hR.filledHull hselected
    have hy := brFilledHullSelectedUpperTailPath_support_nonnegative hn hR hreflected
    change 0 ≤ z 0 ∧ z 0 ≤ 2 * (n : ℤ) ∧
      0 ≤ z 1 ∧ z 1 ≤ 2 * (n : ℤ)
    simp only [brPrimalTopReflectionIso_zero,
      brPrimalTopReflectionIso_one] at hcoords hy
    omega

/-- Every left--right walk in the translated square `[0,2n] × [0,2n]` meets the doubled
stopped barrier.  This is the literal finite incidence statement behind `Mπ⁻ ∪ Mπ⁺` in
Grimmett's proof. -/
theorem squareWalk_support_inter_brFilledHullStoppedBarrier
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R)
    {u v : SquareVertex} (p : squareGraph.Walk u v)
    (hu : u 0 = 0) (hv : v 0 = 2 * (n : ℤ))
    (hp : ∀ z ∈ p.support,
      0 ≤ z 0 ∧ z 0 ≤ 2 * (n : ℤ) ∧
        0 ≤ z 1 ∧ z 1 ≤ 2 * (n : ℤ)) :
    ∃ z, z ∈ p.support ∧ z ∈ (brFilledHullStoppedBarrier hn hR).support := by
  let q := brFilledHullStoppedBarrier hn hR
  let p' : squareGraph.Walk (squareVertex 0 (u 1))
      (squareVertex (2 * (n : ℤ)) (v 1)) :=
    p.copy (by ext i; fin_cases i <;> simp [squareVertex, hu])
      (by ext i; fin_cases i <;> simp [squareVertex, hv])
  let q' : squareGraph.Walk
      (squareVertex (brFilledHullLastMidlineVertex hn hR 0) 0)
      (squareVertex
        (brPrimalTopReflectionIso n (brFilledHullLastMidlineVertex hn hR) 0)
        (2 * (n : ℤ))) :=
    q.copy (by
      ext i
      fin_cases i
      · simp [squareVertex]
      · simpa [q] using (brFilledHullStoppedBarrier_start_coordinates hn hR).2.2)
      (by
        ext i
        fin_cases i
        · simp [squareVertex]
        · simpa [q] using (brFilledHullStoppedBarrier_end_coordinates hn hR).2.2)
  have huData := hp u p.start_mem_support
  have hvData := hp v p.end_mem_support
  have hqStart := brFilledHullStoppedBarrier_start_coordinates hn hR
  have hqEnd := brFilledHullStoppedBarrier_end_coordinates hn hR
  obtain ⟨z, hzp, hzq⟩ :=
    squareWalk_support_inter_of_left_right_and_bottom_top_of_le_int
      (m := 2 * n) (n := 2 * n) le_rfl
      huData.2.2.1 huData.2.2.2 hvData.2.2.1 hvData.2.2.2
      hqStart.1 hqStart.2.1 hqEnd.1 hqEnd.2.1 p' q'
      (by intro z hz; exact hp z (by simpa [p'] using hz))
      (by
        intro z hz
        exact brFilledHullStoppedBarrier_support_coordinates hn hR
          (by simpa [q', q] using hz))
  exact ⟨z, by simpa [p'] using hzp, by simpa [q', q] using hzq⟩

/-- The stopped tail and its reflection are contained in the full doubled selected interface. -/
theorem brFilledHullStoppedBarrier_support_subset_doubledSelected
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    ∀ z ∈ (brFilledHullStoppedBarrier hn hR).support,
      z ∈ (brDoubledSelectedPrimalWalk hn hR.filledHull).support := by
  intro z hz
  rw [mem_brFilledHullStoppedBarrier_support_iff] at hz
  rw [brDoubledSelectedPrimalWalk_support_iff]
  rcases hz with hzLower | hzUpper
  · exact Or.inl
      (brFilledHullSelectedUpperTailPath_support_subset_selected
        hn hR z hzLower)
  · right
    apply (brReflectedSelectedPrimalWalk_support_iff hn hR.filledHull).2
    apply brFilledHullSelectedUpperTailPath_support_subset_selected hn hR
    exact (mem_brReflectedFilledHullSelectedUpperTailPath_support_iff
      hn hR).1 hzUpper

theorem brFilledHullLastMidlineVertex_mem_selected
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    brFilledHullLastMidlineVertex hn hR ∈
      (brSelectedPrimalWalk hn hR.filledHull).support :=
  brFilledHullSelectedUpperTail_support_subset_selected hn hR _
    (brFilledHullSelectedUpperTail hn hR).end_mem_support

theorem brFilledHullLastMidlineVertex_coordinates
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    0 ≤ brFilledHullLastMidlineVertex hn hR 0 ∧
      brFilledHullLastMidlineVertex hn hR 0 ≤ 2 * (n : ℤ) ∧
      brFilledHullLastMidlineVertex hn hR 1 = 0 := by
  have hcoords := brSelectedPrimalWalk_support_coordinates hn hR.filledHull
    (brFilledHullLastMidlineVertex_mem_selected hn hR)
  exact ⟨hcoords.1, hcoords.2.1,
    brFilledHullLastMidlineVertex_one hn hR⟩

/-- The lower-axis case `T⁻` after quarter-turning Grimmett's Figure 11.10. -/
def BRFilledHullLastMidlineLeft
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) : Prop :=
  brFilledHullLastMidlineVertex hn hR 0 ≤ (n : ℤ)

instance instDecidableBRFilledHullLastMidlineLeft
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    Decidable (BRFilledHullLastMidlineLeft hn hR) :=
  Classical.propDecidable _

end

end Percolation
