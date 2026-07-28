import Percolation.Planar.BRGoodFibers

/-!
# Vertical boundary-free square crossings for the BR exploration

The stopped dual frame is oriented so that failure to reach its right target column produces a
bottom-to-top primal crossing.  This module gives that literal target event using exactly the
same finite edge support as `rswSquareCrossingEvent`; a later theorem identifies it with the
quarter-turned RSW square event.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory

noncomputable section

/-- Bottom side of the centered square `[0,2n] × [-n,n]`. -/
def brSquareBottomSide (n : ℕ) : Finset SquareVertex :=
  (squareRectangleVertices (2 * n) n).filter fun x ↦ x 1 = -(n : ℤ)

/-- Top side of the centered square `[0,2n] × [-n,n]`. -/
def brSquareTopSide (n : ℕ) : Finset SquareVertex :=
  (squareRectangleVertices (2 * n) n).filter fun x ↦ x 1 = (n : ℤ)

@[simp]
theorem mem_brSquareBottomSide_iff
    {n : ℕ} {x : SquareVertex} :
    x ∈ brSquareBottomSide n ↔
      0 ≤ x 0 ∧ x 0 ≤ 2 * (n : ℤ) ∧ x 1 = -(n : ℤ) := by
  simp only [brSquareBottomSide, Finset.mem_filter,
    mem_squareRectangleVertices_iff]
  omega

@[simp]
theorem mem_brSquareTopSide_iff
    {n : ℕ} {x : SquareVertex} :
    x ∈ brSquareTopSide n ↔
      0 ≤ x 0 ∧ x 0 ≤ 2 * (n : ℤ) ∧ x 1 = (n : ℤ) := by
  simp only [brSquareTopSide, Finset.mem_filter,
    mem_squareRectangleVertices_iff]
  omega

/-- A bottom-to-top open crossing using the boundary-free RSW square bonds. -/
def brSquareVerticalCrossingEvent (n : ℕ) : Set (EdgeConfiguration 2) :=
  ⋃ x ∈ brSquareBottomSide n, ⋃ y ∈ brSquareTopSide n,
    connectionEventIn 2 (squareBoundaryFreeRectangleEdges (2 * n) n) x y

theorem dependsOn_brSquareVerticalCrossingEvent (n : ℕ) :
    DependsOn (squareBoundaryFreeRectangleEdges (2 * n) n)
      (brSquareVerticalCrossingEvent n) := by
  intro ω η hagree
  simp only [brSquareVerticalCrossingEvent, Set.mem_iUnion]
  constructor
  · rintro ⟨x, hx, y, hy, hxy⟩
    exact ⟨x, hx, y, hy,
      (dependsOn_connectionEventIn 2
        (squareBoundaryFreeRectangleEdges (2 * n) n) x y hagree).mp hxy⟩
  · rintro ⟨x, hx, y, hy, hxy⟩
    exact ⟨x, hx, y, hy,
      (dependsOn_connectionEventIn 2
        (squareBoundaryFreeRectangleEdges (2 * n) n) x y hagree).mpr hxy⟩

theorem measurableSet_brSquareVerticalCrossingEvent (n : ℕ) :
    MeasurableSet (brSquareVerticalCrossingEvent n) :=
  (dependsOn_brSquareVerticalCrossingEvent n).measurableSet

theorem isIncreasingEvent_brSquareVerticalCrossingEvent (n : ℕ) :
    IsIncreasingEvent (brSquareVerticalCrossingEvent n) := by
  intro ω η hωη
  simp only [brSquareVerticalCrossingEvent, Set.mem_iUnion]
  rintro ⟨x, hx, y, hy, hxy⟩
  exact ⟨x, hx, y, hy,
    isIncreasingEvent_connectionEventIn 2
      (squareBoundaryFreeRectangleEdges (2 * n) n) x y hωη hxy⟩

/-- At scale zero the bottom and top sides coincide, so the zero-length walk witnesses the
vertical crossing for every configuration. -/
theorem brSquareVerticalCrossingEvent_zero :
    brSquareVerticalCrossingEvent 0 =
      (Set.univ : Set (EdgeConfiguration 2)) := by
  ext ω
  simp only [brSquareVerticalCrossingEvent, Set.mem_iUnion, Set.mem_univ, iff_true]
  let z : SquareVertex := squareVertex 0 0
  refine ⟨z, ?_, z, ?_, ?_⟩
  · rw [mem_brSquareBottomSide_iff]
    norm_num [z, cubicOrigin]
  · rw [mem_brSquareTopSide_iff]
    norm_num [z, cubicOrigin]
  · refine ⟨.nil, by simp [walkIsOpen], ?_⟩
    intro e he
    simp at he

end

end Percolation
