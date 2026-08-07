import Percolation.Planar.BRProbability
import Percolation.Planar.BRReflection
import Percolation.Core.CubicWalkLevel

/-!
# Endpoint square-root split for RSW squares

This file formalizes the first elementary square-root step in Grimmett, Lemma 11.73.  A
left--right square crossing starts on either the lower or upper half of the left side.  The two
restricted events are reflected copies, are increasing, and cover the unrestricted crossing.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval

noncomputable section

/-- Lower half of the left side of the translated RSW square. -/
def rswSquareLowerLeftSide (n : ℕ) : Finset SquareVertex :=
  (squareRectangleLeft (2 * n) n).filter fun x ↦ x 1 ≤ 0

/-- Upper half of the left side of the translated RSW square. -/
def rswSquareUpperLeftSide (n : ℕ) : Finset SquareVertex :=
  (squareRectangleLeft (2 * n) n).filter fun x ↦ 0 ≤ x 1

@[simp]
theorem mem_rswSquareLowerLeftSide_iff {n : ℕ} {x : SquareVertex} :
    x ∈ rswSquareLowerLeftSide n ↔
      x 0 = 0 ∧ -(n : ℤ) ≤ x 1 ∧ x 1 ≤ 0 := by
  simp only [rswSquareLowerLeftSide, Finset.mem_filter,
    mem_squareRectangleLeft_iff]
  omega

@[simp]
theorem mem_rswSquareUpperLeftSide_iff {n : ℕ} {x : SquareVertex} :
    x ∈ rswSquareUpperLeftSide n ↔
      x 0 = 0 ∧ 0 ≤ x 1 ∧ x 1 ≤ (n : ℤ) := by
  simp only [rswSquareUpperLeftSide, Finset.mem_filter,
    mem_squareRectangleLeft_iff]
  omega

/-- A square crossing whose first endpoint lies on the lower half of the left side. -/
def rswSquareLowerStartCrossingEvent (n : ℕ) : Set (EdgeConfiguration 2) :=
  ⋃ x ∈ rswSquareLowerLeftSide n, ⋃ y ∈ squareRectangleRight (2 * n) n,
    connectionEventIn 2 (squareBoundaryFreeRectangleEdges (2 * n) n) x y

/-- A square crossing whose first endpoint lies on the upper half of the left side. -/
def rswSquareUpperStartCrossingEvent (n : ℕ) : Set (EdgeConfiguration 2) :=
  ⋃ x ∈ rswSquareUpperLeftSide n, ⋃ y ∈ squareRectangleRight (2 * n) n,
    connectionEventIn 2 (squareBoundaryFreeRectangleEdges (2 * n) n) x y

/-! The endpoint split used after path normalization must remember that the displayed starting
vertex is the *last* visit to the left side.  Merely restricting the first endpoint is not
enough, since a crossing may return to that side. -/

/-- Boundary-free square bonds, with every endpoint on the left side forced to be `x`. -/
def rswSquareCleanStartEdges (n : ℕ) (x : SquareVertex) : Finset SquareEdge := by
  classical
  exact (squareBoundaryFreeRectangleEdges (2 * n) n).filter fun e ↦
    ∀ z ∈ (e : Sym2 SquareVertex), z 0 = 0 → z = x

/-- A normalized square crossing whose unique left-side vertex lies in the lower half. -/
def rswSquareCleanLowerStartCrossingEvent (n : ℕ) : Set (EdgeConfiguration 2) :=
  ⋃ x ∈ rswSquareLowerLeftSide n, ⋃ y ∈ squareRectangleRight (2 * n) n,
    connectionEventIn 2 (rswSquareCleanStartEdges n x) x y

/-- A normalized square crossing whose unique left-side vertex lies in the upper half. -/
def rswSquareCleanUpperStartCrossingEvent (n : ℕ) : Set (EdgeConfiguration 2) :=
  ⋃ x ∈ rswSquareUpperLeftSide n, ⋃ y ∈ squareRectangleRight (2 * n) n,
    connectionEventIn 2 (rswSquareCleanStartEdges n x) x y

/-- Lower half of the central vertical axis of the RSW square. -/
def rswSquareLowerMidline (n : ℕ) : Finset SquareVertex :=
  (squareRectangleVertices (2 * n) n).filter fun z ↦
    z 0 = (n : ℤ) ∧ z 1 ≤ 0

/-- Upper half of the central vertical axis of the RSW square. -/
def rswSquareUpperMidline (n : ℕ) : Finset SquareVertex :=
  (squareRectangleVertices (2 * n) n).filter fun z ↦
    z 0 = (n : ℤ) ∧ 0 ≤ z 1

@[simp] theorem mem_rswSquareLowerMidline_iff {n : ℕ} {z : SquareVertex} :
    z ∈ rswSquareLowerMidline n ↔
      z 0 = (n : ℤ) ∧ -(n : ℤ) ≤ z 1 ∧ z 1 ≤ 0 := by
  simp only [rswSquareLowerMidline, Finset.mem_filter,
    mem_squareRectangleVertices_iff]
  omega

@[simp] theorem mem_rswSquareUpperMidline_iff {n : ℕ} {z : SquareVertex} :
    z ∈ rswSquareUpperMidline n ↔
      z 0 = (n : ℤ) ∧ 0 ≤ z 1 ∧ z 1 ≤ (n : ℤ) := by
  simp only [rswSquareUpperMidline, Finset.mem_filter,
    mem_squareRectangleVertices_iff]
  omega

/-- Boundary-free bonds in the right half-square, with every endpoint on the central axis
forced to be the displayed last-axis vertex. -/
def rswSquareCleanMidlineTailEdges (n : ℕ) (z : SquareVertex) : Finset SquareEdge := by
  classical
  exact (squareBoundaryFreeRectangleEdges (2 * n) n).filter fun e ↦
    ∀ a ∈ (e : Sym2 SquareVertex), a 0 = (n : ℤ) → a = z

/-- A square crossing whose last visit to the central axis is in its lower half.  The auxiliary
walk `t`, read from the right endpoint back toward the left, is an actual edge-prefix of the
reverse of the simple crossing and has `z` as its unique central-axis vertex.  This rules out
the redundant-detour witnesses admitted by a mere pair of connection events. -/
def rswSquareLowerLastMidlineCrossingEvent (n : ℕ) : Set (EdgeConfiguration 2) :=
  {omega | ∃ x ∈ squareRectangleLeft (2 * n) n,
    ∃ y ∈ squareRectangleRight (2 * n) n,
      ∃ q : squareGraph.Walk x y,
        q.IsPath ∧ walkIsOpen omega q ∧
          walkEdgeFinset q ⊆ squareBoundaryFreeRectangleEdges (2 * n) n ∧
          (∀ a ∈ q.support, a 0 = 0 → a = x) ∧
          (∀ a ∈ q.support, a 0 = 2 * (n : ℤ) → a = y) ∧
          ∃ z ∈ rswSquareLowerMidline n,
            ∃ t : squareGraph.Walk y z,
              t.edges <+: q.reverse.edges ∧
                (∀ a ∈ t.support, a ∈ q.reverse.support) ∧
                ∀ a ∈ t.support, a 0 = (n : ℤ) → a = z}

/-- A square crossing whose last visit to the central axis is in its upper half, with the same
genuine reversed-prefix convention as the lower event. -/
def rswSquareUpperLastMidlineCrossingEvent (n : ℕ) : Set (EdgeConfiguration 2) :=
  {omega | ∃ x ∈ squareRectangleLeft (2 * n) n,
    ∃ y ∈ squareRectangleRight (2 * n) n,
      ∃ q : squareGraph.Walk x y,
        q.IsPath ∧ walkIsOpen omega q ∧
          walkEdgeFinset q ⊆ squareBoundaryFreeRectangleEdges (2 * n) n ∧
          (∀ a ∈ q.support, a 0 = 0 → a = x) ∧
          (∀ a ∈ q.support, a 0 = 2 * (n : ℤ) → a = y) ∧
          ∃ z ∈ rswSquareUpperMidline n,
            ∃ t : squareGraph.Walk y z,
              t.edges <+: q.reverse.edges ∧
                (∀ a ∈ t.support, a ∈ q.reverse.support) ∧
                ∀ a ∈ t.support, a 0 = (n : ℤ) → a = z}

private theorem dependsOn_rswSquareLowerLastMidlineCrossingEvent (n : ℕ) :
    DependsOn (squareBoundaryFreeRectangleEdges (2 * n) n)
      (rswSquareLowerLastMidlineCrossingEvent n) := by
  intro omega eta hagree
  constructor
  · rintro ⟨x, hx, y, hy, q, hqPath, hqOpen, hqEdges, hqLeft, hqRight, z, hz, t,
      htPrefix, htSupport, htUnique⟩
    refine ⟨x, hx, y, hy, q, hqPath, ?_, hqEdges, hqLeft, hqRight, z, hz, t,
      htPrefix, htSupport, htUnique⟩
    intro e he
    let ee : SquareEdge := ⟨e, q.edges_subset_edgeSet he⟩
    exact (hagree ee (hqEdges ((mem_walkEdgeFinset_iff q ee).mpr he))).mp
      (hqOpen e he)
  · rintro ⟨x, hx, y, hy, q, hqPath, hqOpen, hqEdges, hqLeft, hqRight, z, hz, t,
      htPrefix, htSupport, htUnique⟩
    refine ⟨x, hx, y, hy, q, hqPath, ?_, hqEdges, hqLeft, hqRight, z, hz, t,
      htPrefix, htSupport, htUnique⟩
    intro e he
    let ee : SquareEdge := ⟨e, q.edges_subset_edgeSet he⟩
    exact (hagree ee (hqEdges ((mem_walkEdgeFinset_iff q ee).mpr he))).mpr
      (hqOpen e he)

private theorem dependsOn_rswSquareUpperLastMidlineCrossingEvent (n : ℕ) :
    DependsOn (squareBoundaryFreeRectangleEdges (2 * n) n)
      (rswSquareUpperLastMidlineCrossingEvent n) := by
  intro omega eta hagree
  constructor
  · rintro ⟨x, hx, y, hy, q, hqPath, hqOpen, hqEdges, hqLeft, hqRight, z, hz, t,
      htPrefix, htSupport, htUnique⟩
    refine ⟨x, hx, y, hy, q, hqPath, ?_, hqEdges, hqLeft, hqRight, z, hz, t,
      htPrefix, htSupport, htUnique⟩
    intro e he
    let ee : SquareEdge := ⟨e, q.edges_subset_edgeSet he⟩
    exact (hagree ee (hqEdges ((mem_walkEdgeFinset_iff q ee).mpr he))).mp
      (hqOpen e he)
  · rintro ⟨x, hx, y, hy, q, hqPath, hqOpen, hqEdges, hqLeft, hqRight, z, hz, t,
      htPrefix, htSupport, htUnique⟩
    refine ⟨x, hx, y, hy, q, hqPath, ?_, hqEdges, hqLeft, hqRight, z, hz, t,
      htPrefix, htSupport, htUnique⟩
    intro e he
    let ee : SquareEdge := ⟨e, q.edges_subset_edgeSet he⟩
    exact (hagree ee (hqEdges ((mem_walkEdgeFinset_iff q ee).mpr he))).mpr
      (hqOpen e he)

theorem measurableSet_rswSquareLowerLastMidlineCrossingEvent (n : ℕ) :
    MeasurableSet (rswSquareLowerLastMidlineCrossingEvent n) :=
  (dependsOn_rswSquareLowerLastMidlineCrossingEvent n).measurableSet

theorem measurableSet_rswSquareUpperLastMidlineCrossingEvent (n : ℕ) :
    MeasurableSet (rswSquareUpperLastMidlineCrossingEvent n) :=
  (dependsOn_rswSquareUpperLastMidlineCrossingEvent n).measurableSet

theorem isIncreasingEvent_rswSquareLowerLastMidlineCrossingEvent (n : ℕ) :
    IsIncreasingEvent (rswSquareLowerLastMidlineCrossingEvent n) := by
  intro omega eta hmono
  rintro ⟨x, hx, y, hy, q, hqPath, hqOpen, hqEdges, hqLeft, hqRight, z, hz, t,
    htPrefix, htSupport, htUnique⟩
  refine ⟨x, hx, y, hy, q, hqPath, ?_, hqEdges, hqLeft, hqRight, z, hz, t,
    htPrefix, htSupport, htUnique⟩
  exact fun e he ↦ hmono (hqOpen e he)

theorem isIncreasingEvent_rswSquareUpperLastMidlineCrossingEvent (n : ℕ) :
    IsIncreasingEvent (rswSquareUpperLastMidlineCrossingEvent n) := by
  intro omega eta hmono
  rintro ⟨x, hx, y, hy, q, hqPath, hqOpen, hqEdges, hqLeft, hqRight, z, hz, t,
    htPrefix, htSupport, htUnique⟩
  refine ⟨x, hx, y, hy, q, hqPath, ?_, hqEdges, hqLeft, hqRight, z, hz, t,
    htPrefix, htSupport, htUnique⟩
  exact fun e he ↦ hmono (hqOpen e he)

theorem measurableSet_rswSquareCleanLowerStartCrossingEvent (n : ℕ) :
    MeasurableSet (rswSquareCleanLowerStartCrossingEvent n) := by
  apply (rswSquareLowerLeftSide n).measurableSet_biUnion
  intro x _hx
  apply (squareRectangleRight (2 * n) n).measurableSet_biUnion
  intro y _hy
  exact (dependsOn_connectionEventIn 2 (rswSquareCleanStartEdges n x) x y).measurableSet

theorem measurableSet_rswSquareCleanUpperStartCrossingEvent (n : ℕ) :
    MeasurableSet (rswSquareCleanUpperStartCrossingEvent n) := by
  apply (rswSquareUpperLeftSide n).measurableSet_biUnion
  intro x _hx
  apply (squareRectangleRight (2 * n) n).measurableSet_biUnion
  intro y _hy
  exact (dependsOn_connectionEventIn 2 (rswSquareCleanStartEdges n x) x y).measurableSet

theorem isIncreasingEvent_rswSquareCleanLowerStartCrossingEvent (n : ℕ) :
    IsIncreasingEvent (rswSquareCleanLowerStartCrossingEvent n) := by
  intro omega eta hmono
  simp only [rswSquareCleanLowerStartCrossingEvent, Set.mem_iUnion]
  rintro ⟨x, hx, y, hy, hxy⟩
  exact ⟨x, hx, y, hy,
    isIncreasingEvent_connectionEventIn 2 (rswSquareCleanStartEdges n x) x y hmono hxy⟩

theorem isIncreasingEvent_rswSquareCleanUpperStartCrossingEvent (n : ℕ) :
    IsIncreasingEvent (rswSquareCleanUpperStartCrossingEvent n) := by
  intro omega eta hmono
  simp only [rswSquareCleanUpperStartCrossingEvent, Set.mem_iUnion]
  rintro ⟨x, hx, y, hy, hxy⟩
  exact ⟨x, hx, y, hy,
    isIncreasingEvent_connectionEventIn 2 (rswSquareCleanStartEdges n x) x y hmono hxy⟩

/-- Every square crossing has a last-left-side normalized witness, hence belongs to one of the
two clean half-start events. -/
theorem rswSquareCrossingEvent_subset_cleanLower_union_cleanUpper (n : ℕ) :
    rswSquareCrossingEvent n ⊆
      rswSquareCleanLowerStartCrossingEvent n ∪
        rswSquareCleanUpperStartCrossingEvent n := by
  classical
  intro omega homega
  simp only [rswSquareCrossingEvent, rswRectangleCrossingEvent,
    squareBoundaryFreeRectangleCrossingEvent, Set.mem_iUnion] at homega
  obtain ⟨u, hu, v, hv, w, hwOpen, hwEdges⟩ := homega
  have hu' := mem_squareRectangleLeft_iff.mp hu
  have hv' := mem_squareRectangleRight_iff.mp hv
  obtain ⟨x, y, q, hxLevel, hyLevel, hqOpen, hqPath,
      hqEdgesOriginal, hqSupport, hxUnique, _hyUnique⟩ :=
    exists_open_cubicPath_between_levels_normalized w hwOpen
      (0 : Fin 2) 0 (2 * (n : ℤ)) (by omega) (by omega) (by omega)
  have hvRect : v ∈ squareRectangleVertices (2 * n) n :=
    (Finset.mem_filter.mp hv).1
  have hwRect : ∀ z ∈ w.support, z ∈ squareRectangleVertices (2 * n) n :=
      by
    intro z hz
    rw [SimpleGraph.Walk.mem_support_iff_exists_mem_edges] at hz
    rcases hz with rfl | ⟨e, he, hze⟩
    · exact hvRect
    · let ee : SquareEdge := ⟨e, w.edges_subset_edgeSet he⟩
      exact endpoint_mem_squareRectangle_of_edge_mem
        (Finset.mem_filter.mp
          (hwEdges ((mem_walkEdgeFinset_iff w ee).mpr he))).1 hze
  have hxRect := mem_squareRectangleVertices_iff.mp
    (hwRect x (hqSupport x q.start_mem_support).2.2)
  have hyRect := mem_squareRectangleVertices_iff.mp
    (hwRect y (hqSupport y q.end_mem_support).2.2)
  have hyRight : y ∈ squareRectangleRight (2 * n) n := by
    rw [mem_squareRectangleRight_iff]
    omega
  have hqClean : walkEdgeFinset q ⊆ rswSquareCleanStartEdges n x := by
    intro e he
    rw [rswSquareCleanStartEdges, Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · exact hwEdges ((mem_walkEdgeFinset_iff w e).mpr
        (hqEdgesOriginal ((mem_walkEdgeFinset_iff q e).mp he)))
    · intro z hz hz0
      apply hxUnique z
      · apply q.mem_support_of_mem_edges ((mem_walkEdgeFinset_iff q e).mp he) hz
      · exact hz0
  rw [Set.mem_union]
  by_cases hxSign : x 1 ≤ 0
  · apply Or.inl
    simp only [rswSquareCleanLowerStartCrossingEvent, Set.mem_iUnion]
    refine ⟨x, ?_, y, hyRight, q, hqOpen, hqClean⟩
    rw [mem_rswSquareLowerLeftSide_iff]
    omega
  · apply Or.inr
    simp only [rswSquareCleanUpperStartCrossingEvent, Set.mem_iUnion]
    refine ⟨x, ?_, y, hyRight, q, hqOpen, hqClean⟩
    rw [mem_rswSquareUpperLeftSide_iff]
    omega

/-- Every square crossing has a last visit to the central axis, classified by its height. -/
theorem rswSquareCrossingEvent_subset_lowerLastMidline_union_upperLastMidline (n : ℕ) :
    rswSquareCrossingEvent n ⊆
      rswSquareLowerLastMidlineCrossingEvent n ∪
        rswSquareUpperLastMidlineCrossingEvent n := by
  classical
  intro omega homega
  simp only [rswSquareCrossingEvent, rswRectangleCrossingEvent,
    squareBoundaryFreeRectangleCrossingEvent, Set.mem_iUnion] at homega
  obtain ⟨u, hu, v, hv, w, hwOpen, hwEdges⟩ := homega
  have hu' := mem_squareRectangleLeft_iff.mp hu
  have hv' := mem_squareRectangleRight_iff.mp hv
  obtain ⟨x, y, q, hxLevel, hyLevel, hqOpen, hqPath,
      hqEdgesOriginal, hqSupport, hxUnique, hyUnique⟩ :=
    exists_open_cubicPath_between_levels_normalized w hwOpen
      (0 : Fin 2) 0 (2 * (n : ℤ)) (by omega) (by omega) (by omega)
  have hvRect : v ∈ squareRectangleVertices (2 * n) n :=
    (Finset.mem_filter.mp hv).1
  have hwRect : ∀ a ∈ w.support, a ∈ squareRectangleVertices (2 * n) n := by
    intro a ha
    rw [SimpleGraph.Walk.mem_support_iff_exists_mem_edges] at ha
    rcases ha with rfl | ⟨e, he, hae⟩
    · exact hvRect
    · let ee : SquareEdge := ⟨e, w.edges_subset_edgeSet he⟩
      exact endpoint_mem_squareRectangle_of_edge_mem
        (Finset.mem_filter.mp
          (hwEdges ((mem_walkEdgeFinset_iff w ee).mpr he))).1 hae
  have hxRect := mem_squareRectangleVertices_iff.mp
    (hwRect x (hqSupport x q.start_mem_support).2.2)
  have hyRect := mem_squareRectangleVertices_iff.mp
    (hwRect y (hqSupport y q.end_mem_support).2.2)
  have hxLeft : x ∈ squareRectangleLeft (2 * n) n := by
    rw [mem_squareRectangleLeft_iff]
    omega
  have hyRight : y ∈ squareRectangleRight (2 * n) n := by
    rw [mem_squareRectangleRight_iff]
    omega
  have hqAllowed : walkEdgeFinset q ⊆
      squareBoundaryFreeRectangleEdges (2 * n) n := by
    intro e he
    exact hwEdges ((mem_walkEdgeFinset_iff w e).mpr
      (hqEdgesOriginal ((mem_walkEdgeFinset_iff q e).mp he)))
  obtain ⟨z, t, hzLevel, _htSide, htSupport, htPrefix, htUnique⟩ :=
    exists_cubicWalk_edgePrefix_to_level_of_end_le_unique
      (G := squareGraph) le_rfl q.reverse (0 : Fin 2) (n : ℤ)
        (by simpa [hyLevel] using (show (n : ℤ) ≤ 2 * (n : ℤ) by omega))
        (by simpa [hxLevel] using (show (0 : ℤ) ≤ (n : ℤ) by omega))
  have hzQReverse : z ∈ q.reverse.support := htSupport z t.end_mem_support
  have hzQ : z ∈ q.support := by
    simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hzQReverse
  have hzRect := mem_squareRectangleVertices_iff.mp
    (hwRect z (hqSupport z hzQ).2.2)
  rw [Set.mem_union]
  by_cases hzSign : z 1 ≤ 0
  · apply Or.inl
    refine ⟨x, hxLeft, y, hyRight, q, hqPath, hqOpen, hqAllowed,
      hxUnique, hyUnique,
      z, ?_, t, htPrefix, htSupport, htUnique⟩
    rw [mem_rswSquareLowerMidline_iff]
    omega
  · apply Or.inr
    refine ⟨x, hxLeft, y, hyRight, q, hqPath, hqOpen, hqAllowed,
      hxUnique, hyUnique,
      z, ?_, t, htPrefix, htSupport, htUnique⟩
    rw [mem_rswSquareUpperMidline_iff]
    omega

theorem measurableSet_rswSquareLowerStartCrossingEvent (n : ℕ) :
    MeasurableSet (rswSquareLowerStartCrossingEvent n) := by
  apply (rswSquareLowerLeftSide n).measurableSet_biUnion
  intro x _hx
  apply (squareRectangleRight (2 * n) n).measurableSet_biUnion
  intro y _hy
  exact (dependsOn_connectionEventIn 2
    (squareBoundaryFreeRectangleEdges (2 * n) n) x y).measurableSet

theorem measurableSet_rswSquareUpperStartCrossingEvent (n : ℕ) :
    MeasurableSet (rswSquareUpperStartCrossingEvent n) := by
  apply (rswSquareUpperLeftSide n).measurableSet_biUnion
  intro x _hx
  apply (squareRectangleRight (2 * n) n).measurableSet_biUnion
  intro y _hy
  exact (dependsOn_connectionEventIn 2
    (squareBoundaryFreeRectangleEdges (2 * n) n) x y).measurableSet

theorem isIncreasingEvent_rswSquareLowerStartCrossingEvent (n : ℕ) :
    IsIncreasingEvent (rswSquareLowerStartCrossingEvent n) := by
  intro omega eta hmono
  simp only [rswSquareLowerStartCrossingEvent, Set.mem_iUnion]
  rintro ⟨x, hx, y, hy, hxy⟩
  exact ⟨x, hx, y, hy,
    isIncreasingEvent_connectionEventIn 2
      (squareBoundaryFreeRectangleEdges (2 * n) n) x y hmono hxy⟩

theorem isIncreasingEvent_rswSquareUpperStartCrossingEvent (n : ℕ) :
    IsIncreasingEvent (rswSquareUpperStartCrossingEvent n) := by
  intro omega eta hmono
  simp only [rswSquareUpperStartCrossingEvent, Set.mem_iUnion]
  rintro ⟨x, hx, y, hy, hxy⟩
  exact ⟨x, hx, y, hy,
    isIncreasingEvent_connectionEventIn 2
      (squareBoundaryFreeRectangleEdges (2 * n) n) x y hmono hxy⟩

theorem brHorizontalAxisReflectionIso_involutive (x : SquareVertex) :
    brHorizontalAxisReflectionIso (brHorizontalAxisReflectionIso x) = x := by
  ext i
  fin_cases i <;> simp

private theorem brHorizontalAxisReflectionIso_mem_right_iff
    (n : ℕ) (x : SquareVertex) :
    brHorizontalAxisReflectionIso x ∈ squareRectangleRight (2 * n) n ↔
      x ∈ squareRectangleRight (2 * n) n := by
  rw [mem_squareRectangleRight_iff, mem_squareRectangleRight_iff]
  simp only [brHorizontalAxisReflectionIso_zero,
    brHorizontalAxisReflectionIso_one]
  omega

private theorem brHorizontalAxisReflectionIso_image_cleanStartEdges_subset
    (n : ℕ) (x : SquareVertex) :
    (rswSquareCleanStartEdges n x).image
        brHorizontalAxisReflectionIso.mapEdgeSet ⊆
      rswSquareCleanStartEdges n (brHorizontalAxisReflectionIso x) := by
  classical
  intro e he
  rw [Finset.mem_image] at he
  obtain ⟨f, hf, rfl⟩ := he
  rw [rswSquareCleanStartEdges, Finset.mem_filter] at hf ⊢
  refine ⟨?_, ?_⟩
  · rw [← brHorizontalAxisReflectionIso_image_boundaryFreeRectangleEdges]
    exact Finset.mem_image.mpr ⟨f, hf.1, rfl⟩
  · intro z hz hz0
    change z ∈ Sym2.map brHorizontalAxisReflectionIso (f : Sym2 SquareVertex) at hz
    obtain ⟨a, ha, haz⟩ := Sym2.mem_map.mp hz
    have ha0 : a 0 = 0 := by
      rw [← haz] at hz0
      simpa only [brHorizontalAxisReflectionIso_zero] using hz0
    have hax : a = x := hf.2 a ha ha0
    calc
      z = brHorizontalAxisReflectionIso a := haz.symm
      _ = brHorizontalAxisReflectionIso x := congrArg _ hax

/-- Horizontal reflection transports the last-left-side clean support exactly. -/
theorem brHorizontalAxisReflectionIso_image_cleanStartEdges
    (n : ℕ) (x : SquareVertex) :
    (rswSquareCleanStartEdges n x).image
        brHorizontalAxisReflectionIso.mapEdgeSet =
      rswSquareCleanStartEdges n (brHorizontalAxisReflectionIso x) := by
  classical
  apply Finset.eq_of_subset_of_card_le
  · exact brHorizontalAxisReflectionIso_image_cleanStartEdges_subset n x
  · calc
      (rswSquareCleanStartEdges n (brHorizontalAxisReflectionIso x)).card =
          ((rswSquareCleanStartEdges n (brHorizontalAxisReflectionIso x)).image
            brHorizontalAxisReflectionIso.mapEdgeSet).card := by
              rw [Finset.card_image_of_injective _
                brHorizontalAxisReflectionIso.mapEdgeSet.injective]
      _ ≤ (rswSquareCleanStartEdges n x).card := by
        apply Finset.card_le_card
        simpa only [brHorizontalAxisReflectionIso_involutive] using
          (brHorizontalAxisReflectionIso_image_cleanStartEdges_subset n
            (brHorizontalAxisReflectionIso x))
      _ = ((rswSquareCleanStartEdges n x).image
          brHorizontalAxisReflectionIso.mapEdgeSet).card := by
            rw [Finset.card_image_of_injective _
              brHorizontalAxisReflectionIso.mapEdgeSet.injective]

private theorem brHorizontalAxisReflectionIso_image_cleanMidlineTailEdges_subset
    (n : ℕ) (z : SquareVertex) :
    (rswSquareCleanMidlineTailEdges n z).image
        brHorizontalAxisReflectionIso.mapEdgeSet ⊆
      rswSquareCleanMidlineTailEdges n (brHorizontalAxisReflectionIso z) := by
  classical
  intro e he
  rw [Finset.mem_image] at he
  obtain ⟨f, hf, rfl⟩ := he
  rw [rswSquareCleanMidlineTailEdges, Finset.mem_filter] at hf ⊢
  refine ⟨?_, ?_⟩
  · rw [← brHorizontalAxisReflectionIso_image_boundaryFreeRectangleEdges]
    exact Finset.mem_image.mpr ⟨f, hf.1, rfl⟩
  · intro a ha ha0
    change a ∈ Sym2.map brHorizontalAxisReflectionIso (f : Sym2 SquareVertex) at ha
    obtain ⟨b, hb, hba⟩ := Sym2.mem_map.mp ha
    have hb0 : b 0 = (n : ℤ) := by
      rw [← hba] at ha0
      simpa only [brHorizontalAxisReflectionIso_zero] using ha0
    have hbz : b = z := hf.2 b hb hb0
    calc
      a = brHorizontalAxisReflectionIso b := hba.symm
      _ = brHorizontalAxisReflectionIso z := congrArg _ hbz

theorem brHorizontalAxisReflectionIso_image_cleanMidlineTailEdges
    (n : ℕ) (z : SquareVertex) :
    (rswSquareCleanMidlineTailEdges n z).image
        brHorizontalAxisReflectionIso.mapEdgeSet =
      rswSquareCleanMidlineTailEdges n (brHorizontalAxisReflectionIso z) := by
  classical
  apply Finset.eq_of_subset_of_card_le
  · exact brHorizontalAxisReflectionIso_image_cleanMidlineTailEdges_subset n z
  · calc
      (rswSquareCleanMidlineTailEdges n
          (brHorizontalAxisReflectionIso z)).card =
          ((rswSquareCleanMidlineTailEdges n
            (brHorizontalAxisReflectionIso z)).image
              brHorizontalAxisReflectionIso.mapEdgeSet).card := by
                rw [Finset.card_image_of_injective _
                  brHorizontalAxisReflectionIso.mapEdgeSet.injective]
      _ ≤ (rswSquareCleanMidlineTailEdges n z).card := by
        apply Finset.card_le_card
        simpa only [brHorizontalAxisReflectionIso_involutive] using
          (brHorizontalAxisReflectionIso_image_cleanMidlineTailEdges_subset n
            (brHorizontalAxisReflectionIso z))
      _ = ((rswSquareCleanMidlineTailEdges n z).image
          brHorizontalAxisReflectionIso.mapEdgeSet).card := by
            rw [Finset.card_image_of_injective _
              brHorizontalAxisReflectionIso.mapEdgeSet.injective]

/-- Horizontal-axis reflection exchanges the two clean half-start square events. -/
theorem cubicGraphIsoEvent_rswSquareCleanLowerStartCrossingEvent_eq_upper (n : ℕ) :
    cubicGraphIsoEvent brHorizontalAxisReflectionIso
        (rswSquareCleanLowerStartCrossingEvent n) =
      rswSquareCleanUpperStartCrossingEvent n := by
  let F := brHorizontalAxisReflectionIso
  ext omega
  change cubicGraphIsoConfigurationPullback F omega ∈
      rswSquareCleanLowerStartCrossingEvent n ↔
    omega ∈ rswSquareCleanUpperStartCrossingEvent n
  simp only [rswSquareCleanLowerStartCrossingEvent,
    rswSquareCleanUpperStartCrossingEvent, Set.mem_iUnion]
  constructor
  · rintro ⟨x, hx, y, hy, hxy⟩
    have hxy' :=
      (cubicGraphIsoConfigurationPullback_mem_connectionEventIn_iff F
        (rswSquareCleanStartEdges n x) omega x y).mp hxy
    rw [brHorizontalAxisReflectionIso_image_cleanStartEdges] at hxy'
    refine ⟨F x, ?_, F y, ?_, hxy'⟩
    · rw [mem_rswSquareUpperLeftSide_iff]
      have hx' := mem_rswSquareLowerLeftSide_iff.mp hx
      simp only [F, brHorizontalAxisReflectionIso_zero,
        brHorizontalAxisReflectionIso_one]
      omega
    · exact (brHorizontalAxisReflectionIso_mem_right_iff n y).2 hy
  · rintro ⟨x, hx, y, hy, hxy⟩
    refine ⟨F x, ?_, F y, ?_, ?_⟩
    · rw [mem_rswSquareLowerLeftSide_iff]
      have hx' := mem_rswSquareUpperLeftSide_iff.mp hx
      simp only [F, brHorizontalAxisReflectionIso_zero,
        brHorizontalAxisReflectionIso_one]
      omega
    · apply (brHorizontalAxisReflectionIso_mem_right_iff n (F y)).1
      simpa only [F, brHorizontalAxisReflectionIso_involutive] using hy
    · apply (cubicGraphIsoConfigurationPullback_mem_connectionEventIn_iff F
        (rswSquareCleanStartEdges n (F x)) omega (F x) (F y)).mpr
      rw [brHorizontalAxisReflectionIso_image_cleanStartEdges]
      simpa only [F, brHorizontalAxisReflectionIso_involutive] using hxy

/-- Horizontal reflection exchanges the two possible signs of the last central-axis visit. -/
theorem cubicGraphIsoEvent_rswSquareLowerLastMidlineCrossingEvent_eq_upper (n : ℕ) :
    cubicGraphIsoEvent brHorizontalAxisReflectionIso
        (rswSquareLowerLastMidlineCrossingEvent n) =
      rswSquareUpperLastMidlineCrossingEvent n := by
  let F := brHorizontalAxisReflectionIso
  have hFsymm : F.symm = F := by
    ext x i
    apply congrFun
    apply F.injective
    simpa only [F, F.apply_symm_apply,
      brHorizontalAxisReflectionIso_involutive]
  ext omega
  change cubicGraphIsoConfigurationPullback F omega ∈
      rswSquareLowerLastMidlineCrossingEvent n ↔
    omega ∈ rswSquareUpperLastMidlineCrossingEvent n
  constructor
  · rintro ⟨x, hx, y, hy, q, hqPath, hqOpen, hqEdges, hqLeft, hqRight, z, hz, t,
      htPrefix, htSupport, htUnique⟩
    let q' := q.map F.toHom
    let t' := t.map F.toHom
    have hqEdges' : walkEdgeFinset q' ⊆
        squareBoundaryFreeRectangleEdges (2 * n) n := by
      intro e he
      simp only [mem_walkEdgeFinset_iff, q', SimpleGraph.Walk.edges_map,
        List.mem_map] at he
      rcases he with ⟨f, hf, hfe⟩
      let fe : SquareEdge := ⟨f, q.edges_subset_edgeSet hf⟩
      have hfeAllowed : fe ∈ squareBoundaryFreeRectangleEdges (2 * n) n :=
        hqEdges ((mem_walkEdgeFinset_iff q fe).mpr hf)
      rw [← brHorizontalAxisReflectionIso_image_boundaryFreeRectangleEdges]
      refine Finset.mem_image.mpr ⟨fe, hfeAllowed, ?_⟩
      apply Subtype.ext
      exact hfe
    have htPrefix' : t'.edges <+: q'.reverse.edges := by
      simp only [t', q', SimpleGraph.Walk.edges_map,
        SimpleGraph.Walk.reverse_map]
      exact htPrefix.map _
    have htSupport' : ∀ a ∈ t'.support, a ∈ q'.reverse.support := by
      intro a ha
      simp only [t', SimpleGraph.Walk.support_map, List.mem_map] at ha
      rcases ha with ⟨b, hb, rfl⟩
      simp only [q', SimpleGraph.Walk.reverse_map,
        SimpleGraph.Walk.support_map, List.mem_map]
      exact ⟨b, htSupport b hb, rfl⟩
    have hqLeft' : ∀ a ∈ q'.support, a 0 = 0 → a = F x := by
      intro a ha ha0
      simp only [q', SimpleGraph.Walk.support_map, List.mem_map] at ha
      rcases ha with ⟨b, hb, rfl⟩
      have hb0 : b 0 = 0 := by
        simpa only [F, brHorizontalAxisReflectionIso_zero] using ha0
      exact congrArg F (hqLeft b hb hb0)
    have hqRight' : ∀ a ∈ q'.support, a 0 = 2 * (n : ℤ) → a = F y := by
      intro a ha ha0
      simp only [q', SimpleGraph.Walk.support_map, List.mem_map] at ha
      rcases ha with ⟨b, hb, rfl⟩
      have hb0 : b 0 = 2 * (n : ℤ) := by
        simpa only [F, brHorizontalAxisReflectionIso_zero] using ha0
      exact congrArg F (hqRight b hb hb0)
    have htUnique' : ∀ a ∈ t'.support, a 0 = (n : ℤ) → a = F z := by
      intro a ha ha0
      simp only [t', SimpleGraph.Walk.support_map, List.mem_map] at ha
      rcases ha with ⟨b, hb, rfl⟩
      have hb0 : b 0 = (n : ℤ) := by
        simpa only [F, brHorizontalAxisReflectionIso_zero] using ha0
      exact congrArg F (htUnique b hb hb0)
    refine ⟨F x, ?_, F y, ?_, q', ?_, ?_, hqEdges', hqLeft', hqRight',
      F z, ?_, t', htPrefix', htSupport', htUnique'⟩
    · rw [mem_squareRectangleLeft_iff]
      have hx' := mem_squareRectangleLeft_iff.mp hx
      simp only [F, brHorizontalAxisReflectionIso_zero,
        brHorizontalAxisReflectionIso_one]
      omega
    · exact (brHorizontalAxisReflectionIso_mem_right_iff n y).2 hy
    · exact (SimpleGraph.Walk.map_isPath_iff_of_injective F.injective).2 hqPath
    · exact walkIsOpen_map_cubicGraphIso F q hqOpen
    · rw [mem_rswSquareUpperMidline_iff]
      have hz' := mem_rswSquareLowerMidline_iff.mp hz
      simp only [F, brHorizontalAxisReflectionIso_zero,
        brHorizontalAxisReflectionIso_one]
      omega
  · rintro ⟨x, hx, y, hy, q, hqPath, hqOpen, hqEdges, hqLeft, hqRight, z, hz, t,
      htPrefix, htSupport, htUnique⟩
    let q' := q.map F.toHom
    let t' := t.map F.toHom
    have hqOpenSource : walkIsOpen
        (cubicGraphIsoConfigurationPullback F omega) q' := by
      have h := walkIsOpen_map_cubicGraphIso
        (ω := cubicGraphIsoConfigurationPullback F omega) F.symm q (by
          simpa using hqOpen)
      simpa only [q', hFsymm] using h
    have hqEdges' : walkEdgeFinset q' ⊆
        squareBoundaryFreeRectangleEdges (2 * n) n := by
      intro e he
      simp only [mem_walkEdgeFinset_iff, q', SimpleGraph.Walk.edges_map,
        List.mem_map] at he
      rcases he with ⟨f, hf, hfe⟩
      let fe : SquareEdge := ⟨f, q.edges_subset_edgeSet hf⟩
      have hfeAllowed : fe ∈ squareBoundaryFreeRectangleEdges (2 * n) n :=
        hqEdges ((mem_walkEdgeFinset_iff q fe).mpr hf)
      rw [← brHorizontalAxisReflectionIso_image_boundaryFreeRectangleEdges]
      refine Finset.mem_image.mpr ⟨fe, hfeAllowed, ?_⟩
      apply Subtype.ext
      exact hfe
    have htPrefix' : t'.edges <+: q'.reverse.edges := by
      simp only [t', q', SimpleGraph.Walk.edges_map,
        SimpleGraph.Walk.reverse_map]
      exact htPrefix.map _
    have htSupport' : ∀ a ∈ t'.support, a ∈ q'.reverse.support := by
      intro a ha
      simp only [t', SimpleGraph.Walk.support_map, List.mem_map] at ha
      rcases ha with ⟨b, hb, rfl⟩
      simp only [q', SimpleGraph.Walk.reverse_map,
        SimpleGraph.Walk.support_map, List.mem_map]
      exact ⟨b, htSupport b hb, rfl⟩
    have hqLeft' : ∀ a ∈ q'.support, a 0 = 0 → a = F x := by
      intro a ha ha0
      simp only [q', SimpleGraph.Walk.support_map, List.mem_map] at ha
      rcases ha with ⟨b, hb, rfl⟩
      have hb0 : b 0 = 0 := by
        simpa only [F, brHorizontalAxisReflectionIso_zero] using ha0
      exact congrArg F (hqLeft b hb hb0)
    have hqRight' : ∀ a ∈ q'.support, a 0 = 2 * (n : ℤ) → a = F y := by
      intro a ha ha0
      simp only [q', SimpleGraph.Walk.support_map, List.mem_map] at ha
      rcases ha with ⟨b, hb, rfl⟩
      have hb0 : b 0 = 2 * (n : ℤ) := by
        simpa only [F, brHorizontalAxisReflectionIso_zero] using ha0
      exact congrArg F (hqRight b hb hb0)
    have htUnique' : ∀ a ∈ t'.support, a 0 = (n : ℤ) → a = F z := by
      intro a ha ha0
      simp only [t', SimpleGraph.Walk.support_map, List.mem_map] at ha
      rcases ha with ⟨b, hb, rfl⟩
      have hb0 : b 0 = (n : ℤ) := by
        simpa only [F, brHorizontalAxisReflectionIso_zero] using ha0
      exact congrArg F (htUnique b hb hb0)
    refine ⟨F x, ?_, F y, ?_, q', ?_, hqOpenSource, hqEdges', hqLeft', hqRight',
      F z, ?_, t', htPrefix', htSupport', htUnique'⟩
    · rw [mem_squareRectangleLeft_iff]
      have hx' := mem_squareRectangleLeft_iff.mp hx
      simp only [F, brHorizontalAxisReflectionIso_zero,
        brHorizontalAxisReflectionIso_one]
      omega
    · apply (brHorizontalAxisReflectionIso_mem_right_iff n (F y)).1
      simpa only [F, brHorizontalAxisReflectionIso_involutive] using hy
    · exact (SimpleGraph.Walk.map_isPath_iff_of_injective F.injective).2 hqPath
    · rw [mem_rswSquareLowerMidline_iff]
      have hz' := mem_rswSquareUpperMidline_iff.mp hz
      simp only [F, brHorizontalAxisReflectionIso_zero,
        brHorizontalAxisReflectionIso_one]
      omega

theorem bernoulliBondMeasure_real_rswSquareUpperLastMidline_eq_lower
    (p : I) (n : ℕ) :
    (bernoulliBondMeasure 2 p).real (rswSquareUpperLastMidlineCrossingEvent n) =
      (bernoulliBondMeasure 2 p).real (rswSquareLowerLastMidlineCrossingEvent n) := by
  rw [← cubicGraphIsoEvent_rswSquareLowerLastMidlineCrossingEvent_eq_upper]
  exact bernoulliBondMeasure_real_cubicGraphIsoEvent p _
    (measurableSet_rswSquareLowerLastMidlineCrossingEvent n)

theorem one_sub_sqrt_rswSquare_le_lowerLastMidlineCrossingProbability
    (p : I) (n : ℕ) :
    1 - Real.sqrt (1 - rswSquareCrossingProbability p n) ≤
      (bernoulliBondMeasure 2 p).real
        (rswSquareLowerLastMidlineCrossingEvent n) := by
  unfold rswSquareCrossingProbability
  exact one_sub_sqrt_one_sub_measureReal_le_of_subset_union_of_eq (d := 2) p
    (H := rswSquareCrossingEvent n)
    (L := rswSquareLowerLastMidlineCrossingEvent n)
    (U := rswSquareUpperLastMidlineCrossingEvent n)
    (rswSquareCrossingEvent_subset_lowerLastMidline_union_upperLastMidline n)
    (bernoulliBondMeasure_real_rswSquareUpperLastMidline_eq_lower p n)
    (isIncreasingEvent_rswSquareLowerLastMidlineCrossingEvent n)
    (isIncreasingEvent_rswSquareUpperLastMidlineCrossingEvent n)
    (measurableSet_rswSquareLowerLastMidlineCrossingEvent n)
    (measurableSet_rswSquareUpperLastMidlineCrossingEvent n)

theorem bernoulliBondMeasure_real_rswSquareCleanUpperStart_eq_lower
    (p : I) (n : ℕ) :
    (bernoulliBondMeasure 2 p).real (rswSquareCleanUpperStartCrossingEvent n) =
      (bernoulliBondMeasure 2 p).real (rswSquareCleanLowerStartCrossingEvent n) := by
  rw [← cubicGraphIsoEvent_rswSquareCleanLowerStartCrossingEvent_eq_upper]
  exact bernoulliBondMeasure_real_cubicGraphIsoEvent p _
    (measurableSet_rswSquareCleanLowerStartCrossingEvent n)

/-- Square-root lower bound for a prescribed half of the normalized last-side endpoint. -/
theorem one_sub_sqrt_rswSquare_le_cleanUpperStartCrossingProbability
    (p : I) (n : ℕ) :
    1 - Real.sqrt (1 - rswSquareCrossingProbability p n) ≤
      (bernoulliBondMeasure 2 p).real
        (rswSquareCleanUpperStartCrossingEvent n) := by
  rw [bernoulliBondMeasure_real_rswSquareCleanUpperStart_eq_lower p n]
  unfold rswSquareCrossingProbability
  exact one_sub_sqrt_one_sub_measureReal_le_of_subset_union_of_eq (d := 2) p
    (H := rswSquareCrossingEvent n)
    (L := rswSquareCleanLowerStartCrossingEvent n)
    (U := rswSquareCleanUpperStartCrossingEvent n)
    (rswSquareCrossingEvent_subset_cleanLower_union_cleanUpper n)
    (bernoulliBondMeasure_real_rswSquareCleanUpperStart_eq_lower p n)
    (isIncreasingEvent_rswSquareCleanLowerStartCrossingEvent n)
    (isIncreasingEvent_rswSquareCleanUpperStartCrossingEvent n)
    (measurableSet_rswSquareCleanLowerStartCrossingEvent n)
    (measurableSet_rswSquareCleanUpperStartCrossingEvent n)

/-- Horizontal-axis reflection exchanges the lower- and upper-start square events. -/
theorem cubicGraphIsoEvent_rswSquareLowerStartCrossingEvent_eq_upper (n : ℕ) :
    cubicGraphIsoEvent brHorizontalAxisReflectionIso
        (rswSquareLowerStartCrossingEvent n) =
      rswSquareUpperStartCrossingEvent n := by
  let F := brHorizontalAxisReflectionIso
  ext omega
  change cubicGraphIsoConfigurationPullback F omega ∈
      rswSquareLowerStartCrossingEvent n ↔
    omega ∈ rswSquareUpperStartCrossingEvent n
  simp only [rswSquareLowerStartCrossingEvent,
    rswSquareUpperStartCrossingEvent, Set.mem_iUnion]
  constructor
  · rintro ⟨x, hx, y, hy, hxy⟩
    have hxy' :=
      (cubicGraphIsoConfigurationPullback_mem_connectionEventIn_iff F
        (squareBoundaryFreeRectangleEdges (2 * n) n) omega x y).mp hxy
    rw [brHorizontalAxisReflectionIso_image_boundaryFreeRectangleEdges] at hxy'
    refine ⟨F x, ?_, F y, ?_, hxy'⟩
    · rw [mem_rswSquareUpperLeftSide_iff]
      have hx' := mem_rswSquareLowerLeftSide_iff.mp hx
      simp only [F, brHorizontalAxisReflectionIso_zero,
        brHorizontalAxisReflectionIso_one]
      omega
    · exact (brHorizontalAxisReflectionIso_mem_right_iff n y).2 hy
  · rintro ⟨x, hx, y, hy, hxy⟩
    refine ⟨F x, ?_, F y, ?_, ?_⟩
    · rw [mem_rswSquareLowerLeftSide_iff]
      have hx' := mem_rswSquareUpperLeftSide_iff.mp hx
      simp only [F, brHorizontalAxisReflectionIso_zero,
        brHorizontalAxisReflectionIso_one]
      omega
    · apply (brHorizontalAxisReflectionIso_mem_right_iff n (F y)).1
      simpa only [F, brHorizontalAxisReflectionIso_involutive] using hy
    · apply (cubicGraphIsoConfigurationPullback_mem_connectionEventIn_iff F
        (squareBoundaryFreeRectangleEdges (2 * n) n) omega (F x) (F y)).mpr
      rw [brHorizontalAxisReflectionIso_image_boundaryFreeRectangleEdges]
      simpa only [F, brHorizontalAxisReflectionIso_involutive] using hxy

theorem bernoulliBondMeasure_real_rswSquareUpperStart_eq_lower
    (p : I) (n : ℕ) :
    (bernoulliBondMeasure 2 p).real (rswSquareUpperStartCrossingEvent n) =
      (bernoulliBondMeasure 2 p).real (rswSquareLowerStartCrossingEvent n) := by
  rw [← cubicGraphIsoEvent_rswSquareLowerStartCrossingEvent_eq_upper]
  exact bernoulliBondMeasure_real_cubicGraphIsoEvent p _
    (measurableSet_rswSquareLowerStartCrossingEvent n)

theorem rswSquareCrossingEvent_subset_lowerStart_union_upperStart (n : ℕ) :
    rswSquareCrossingEvent n ⊆
      rswSquareLowerStartCrossingEvent n ∪
        rswSquareUpperStartCrossingEvent n := by
  intro omega homega
  simp only [rswSquareCrossingEvent, rswRectangleCrossingEvent,
    squareBoundaryFreeRectangleCrossingEvent, Set.mem_iUnion] at homega
  obtain ⟨x, hx, y, hy, hxy⟩ := homega
  have hx' := mem_squareRectangleLeft_iff.mp hx
  rw [Set.mem_union]
  by_cases hs : x 1 ≤ 0
  · apply Or.inl
    simp only [rswSquareLowerStartCrossingEvent, Set.mem_iUnion]
    exact ⟨x, mem_rswSquareLowerLeftSide_iff.mpr
      ⟨hx'.1, hx'.2.1, hs⟩, y, hy, hxy⟩
  · apply Or.inr
    simp only [rswSquareUpperStartCrossingEvent, Set.mem_iUnion]
    exact ⟨x, mem_rswSquareUpperLeftSide_iff.mpr
      ⟨hx'.1, by omega, hx'.2.2⟩, y, hy, hxy⟩

/-- Grimmett's square-root lower bound for either prescribed half of the starting side. -/
theorem one_sub_sqrt_rswSquare_le_upperStartCrossingProbability
    (p : I) (n : ℕ) :
    1 - Real.sqrt (1 - rswSquareCrossingProbability p n) ≤
      (bernoulliBondMeasure 2 p).real
        (rswSquareUpperStartCrossingEvent n) := by
  rw [bernoulliBondMeasure_real_rswSquareUpperStart_eq_lower p n]
  unfold rswSquareCrossingProbability
  exact one_sub_sqrt_one_sub_measureReal_le_of_subset_union_of_eq (d := 2) p
    (H := rswSquareCrossingEvent n)
    (L := rswSquareLowerStartCrossingEvent n)
    (U := rswSquareUpperStartCrossingEvent n)
    (rswSquareCrossingEvent_subset_lowerStart_union_upperStart n)
    (bernoulliBondMeasure_real_rswSquareUpperStart_eq_lower p n)
    (isIncreasingEvent_rswSquareLowerStartCrossingEvent n)
    (isIncreasingEvent_rswSquareUpperStartCrossingEvent n)
    (measurableSet_rswSquareLowerStartCrossingEvent n)
    (measurableSet_rswSquareUpperStartCrossingEvent n)

end

end Percolation
