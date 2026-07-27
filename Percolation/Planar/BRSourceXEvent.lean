import Percolation.Planar.BRFreshSupport
import Percolation.Planar.BRVerticalEvents

/-!
# The source `X(R)` event for the Bollobás--Riordan extension

The event has one junction vertex in the centered source square.  That junction is connected,
using only source-square bonds, to both horizontal sides of the square, and using only bonds of
the translated extension rectangle to its right side.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory

noncomputable section

/-- Vertices of the centered source square `[0,2n] × [-n,n]`. -/
def brSourceSquareVertices (n : ℕ) : Finset SquareVertex :=
  squareRectangleVertices (2 * n) n

@[simp]
theorem mem_brSourceSquareVertices_iff
    {n : ℕ} {x : SquareVertex} :
    x ∈ brSourceSquareVertices n ↔
      0 ≤ x 0 ∧ x 0 ≤ 2 * (n : ℤ) ∧
        -(n : ℤ) ≤ x 1 ∧ x 1 ≤ (n : ℤ) := by
  simp [brSourceSquareVertices]

/-- Boundary-free bonds available inside the centered source square. -/
def brSourceSquareEdges (n : ℕ) : Finset SquareEdge :=
  squareBoundaryFreeRectangleEdges (2 * n) n

/-- The right side of the extension rectangle `[0,m] × [-n,3n]`, obtained by translating the
right side of `[0,m] × [-2n,2n]` upward by `n`. -/
def brExtensionRectangleRightSide (m n : ℕ) : Finset SquareVertex :=
  (squareRectangleRight m (2 * n)).map
    (brExtensionRectangleTranslateIso n).toEquiv.toEmbedding

@[simp]
theorem mem_brExtensionRectangleRightSide_iff
    {m n : ℕ} {x : SquareVertex} :
    x ∈ brExtensionRectangleRightSide m n ↔
      x 0 = (m : ℤ) ∧ -(n : ℤ) ≤ x 1 ∧ x 1 ≤ 3 * (n : ℤ) := by
  classical
  rw [brExtensionRectangleRightSide, Finset.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' := mem_squareRectangleRight_iff.mp hy
    change brExtensionRectangleTranslateIso n y 0 = (m : ℤ) ∧
      -(n : ℤ) ≤ brExtensionRectangleTranslateIso n y 1 ∧
        brExtensionRectangleTranslateIso n y 1 ≤ 3 * (n : ℤ)
    rw [brExtensionRectangleTranslateIso_zero, brExtensionRectangleTranslateIso_one]
    push_cast at hy'
    omega
  · rintro ⟨hx0, hx1Lower, hx1Upper⟩
    let y : SquareVertex := squareVertex (x 0) (x 1 - (n : ℤ))
    refine ⟨y, ?_, ?_⟩
    · rw [mem_squareRectangleRight_iff]
      dsimp [y]
      simp only [squareVertex]
      push_cast
      omega
    · ext i
      fin_cases i
      · simp [y, squareVertex, hx0]
      · simp [y, squareVertex]

/-- All random coordinates queried by the source `X(R)` event. -/
def brSourceXSupport (m n : ℕ) : Finset SquareEdge :=
  brSourceSquareEdges n ∪ brExtensionRectangleEdges m n

@[simp]
theorem mem_brSourceXSupport_iff
    {m n : ℕ} {e : SquareEdge} :
    e ∈ brSourceXSupport m n ↔
      e ∈ brSourceSquareEdges n ∨ e ∈ brExtensionRectangleEdges m n := by
  simp [brSourceXSupport]

/-- Concrete finite witness for the source `X(R)` event. -/
structure BRSourceXWitness (m n : ℕ) (omega : EdgeConfiguration 2) where
  junction : SquareVertex
  junction_mem_source : junction ∈ brSourceSquareVertices n
  bottom : SquareVertex
  bottom_mem : bottom ∈ brSquareBottomSide n
  top : SquareVertex
  top_mem : top ∈ brSquareTopSide n
  right : SquareVertex
  right_mem : right ∈ brExtensionRectangleRightSide m n
  connected_bottom :
    omega ∈ connectionEventIn 2 (brSourceSquareEdges n) junction bottom
  connected_top :
    omega ∈ connectionEventIn 2 (brSourceSquareEdges n) junction top
  connected_right :
    omega ∈ connectionEventIn 2 (brExtensionRectangleEdges m n) junction right

/-- Source `X(R)`: a source-square bottom--top junction with an arm to the translated right
side of the extension rectangle. -/
def brSourceXEvent (m n : ℕ) : Set (EdgeConfiguration 2) :=
  {omega | Nonempty (BRSourceXWitness m n omega)}

namespace BRSourceXWitness

theorem junction_coordinates
    {m n : ℕ} {omega : EdgeConfiguration 2} (W : BRSourceXWitness m n omega) :
    0 ≤ W.junction 0 ∧ W.junction 0 ≤ 2 * (n : ℤ) ∧
      -(n : ℤ) ≤ W.junction 1 ∧ W.junction 1 ≤ (n : ℤ) :=
  mem_brSourceSquareVertices_iff.mp W.junction_mem_source

theorem bottom_coordinates
    {m n : ℕ} {omega : EdgeConfiguration 2} (W : BRSourceXWitness m n omega) :
    0 ≤ W.bottom 0 ∧ W.bottom 0 ≤ 2 * (n : ℤ) ∧
      W.bottom 1 = -(n : ℤ) :=
  mem_brSquareBottomSide_iff.mp W.bottom_mem

theorem top_coordinates
    {m n : ℕ} {omega : EdgeConfiguration 2} (W : BRSourceXWitness m n omega) :
    0 ≤ W.top 0 ∧ W.top 0 ≤ 2 * (n : ℤ) ∧
      W.top 1 = (n : ℤ) :=
  mem_brSquareTopSide_iff.mp W.top_mem

theorem right_coordinates
    {m n : ℕ} {omega : EdgeConfiguration 2} (W : BRSourceXWitness m n omega) :
    W.right 0 = (m : ℤ) ∧ -(n : ℤ) ≤ W.right 1 ∧
      W.right 1 ≤ 3 * (n : ℤ) :=
  mem_brExtensionRectangleRightSide_iff.mp W.right_mem

theorem mem_event
    {m n : ℕ} {omega : EdgeConfiguration 2} (W : BRSourceXWitness m n omega) :
    omega ∈ brSourceXEvent m n :=
  ⟨W⟩

end BRSourceXWitness

@[simp]
theorem mem_brSourceXEvent_iff
    {m n : ℕ} {omega : EdgeConfiguration 2} :
    omega ∈ brSourceXEvent m n ↔
      ∃ z ∈ brSourceSquareVertices n,
        ∃ b ∈ brSquareBottomSide n,
          ∃ t ∈ brSquareTopSide n,
            ∃ r ∈ brExtensionRectangleRightSide m n,
              omega ∈ connectionEventIn 2 (brSourceSquareEdges n) z b ∧
              omega ∈ connectionEventIn 2 (brSourceSquareEdges n) z t ∧
              omega ∈ connectionEventIn 2 (brExtensionRectangleEdges m n) z r := by
  constructor
  · rintro ⟨W⟩
    exact ⟨W.junction, W.junction_mem_source,
      W.bottom, W.bottom_mem, W.top, W.top_mem, W.right, W.right_mem,
      W.connected_bottom, W.connected_top, W.connected_right⟩
  · rintro ⟨z, hz, b, hb, t, ht, r, hr, hzb, hzt, hzr⟩
    exact ⟨⟨z, hz, b, hb, t, ht, r, hr, hzb, hzt, hzr⟩⟩

/-- Package three finite connections with their geometric endpoints into the source event. -/
theorem mem_brSourceXEvent_of_connections
    {m n : ℕ} {omega : EdgeConfiguration 2}
    {z b t r : SquareVertex}
    (hz : z ∈ brSourceSquareVertices n)
    (hb : b ∈ brSquareBottomSide n)
    (ht : t ∈ brSquareTopSide n)
    (hr : r ∈ brExtensionRectangleRightSide m n)
    (hzb : omega ∈ connectionEventIn 2 (brSourceSquareEdges n) z b)
    (hzt : omega ∈ connectionEventIn 2 (brSourceSquareEdges n) z t)
    (hzr : omega ∈ connectionEventIn 2 (brExtensionRectangleEdges m n) z r) :
    omega ∈ brSourceXEvent m n :=
  mem_brSourceXEvent_iff.mpr ⟨z, hz, b, hb, t, ht, r, hr, hzb, hzt, hzr⟩

/-- Build the event directly from three explicit open walks with the required finite supports. -/
theorem mem_brSourceXEvent_of_walks
    {m n : ℕ} {omega : EdgeConfiguration 2}
    {z b t r : SquareVertex}
    (hz : z ∈ brSourceSquareVertices n)
    (hb : b ∈ brSquareBottomSide n)
    (ht : t ∈ brSquareTopSide n)
    (hr : r ∈ brExtensionRectangleRightSide m n)
    (wb : squareGraph.Walk z b) (hwbOpen : walkIsOpen omega wb)
    (hwbSupport : walkEdgeFinset wb ⊆ brSourceSquareEdges n)
    (wt : squareGraph.Walk z t) (hwtOpen : walkIsOpen omega wt)
    (hwtSupport : walkEdgeFinset wt ⊆ brSourceSquareEdges n)
    (wr : squareGraph.Walk z r) (hwrOpen : walkIsOpen omega wr)
    (hwrSupport : walkEdgeFinset wr ⊆ brExtensionRectangleEdges m n) :
    omega ∈ brSourceXEvent m n :=
  mem_brSourceXEvent_of_connections hz hb ht hr
    ⟨wb, hwbOpen, hwbSupport⟩ ⟨wt, hwtOpen, hwtSupport⟩
    ⟨wr, hwrOpen, hwrSupport⟩

/-- Walk-level witness form of the source event. -/
theorem mem_brSourceXEvent_iff_exists_walks
    {m n : ℕ} {omega : EdgeConfiguration 2} :
    omega ∈ brSourceXEvent m n ↔
      ∃ z ∈ brSourceSquareVertices n,
        ∃ b ∈ brSquareBottomSide n,
          ∃ t ∈ brSquareTopSide n,
            ∃ r ∈ brExtensionRectangleRightSide m n,
              (∃ wb : squareGraph.Walk z b,
                walkIsOpen omega wb ∧ walkEdgeFinset wb ⊆ brSourceSquareEdges n) ∧
              (∃ wt : squareGraph.Walk z t,
                walkIsOpen omega wt ∧ walkEdgeFinset wt ⊆ brSourceSquareEdges n) ∧
              (∃ wr : squareGraph.Walk z r,
                walkIsOpen omega wr ∧
                  walkEdgeFinset wr ⊆ brExtensionRectangleEdges m n) := by
  rw [mem_brSourceXEvent_iff]
  simp only [connectionEventIn, Set.mem_setOf_eq]

/-- The source `X(R)` event reads only its explicit finite source-and-extension support. -/
theorem dependsOn_brSourceXEvent (m n : ℕ) :
    DependsOn (brSourceXSupport m n) (brSourceXEvent m n) := by
  intro omega eta hagree
  simp only [mem_brSourceXEvent_iff]
  constructor
  · rintro ⟨z, hz, b, hb, t, ht, r, hr, hzb, hzt, hzr⟩
    refine ⟨z, hz, b, hb, t, ht, r, hr, ?_, ?_, ?_⟩
    · exact (dependsOn_connectionEventIn 2 (brSourceSquareEdges n) z b
        (fun e he ↦ hagree e (mem_brSourceXSupport_iff.mpr (Or.inl he)))).mp hzb
    · exact (dependsOn_connectionEventIn 2 (brSourceSquareEdges n) z t
        (fun e he ↦ hagree e (mem_brSourceXSupport_iff.mpr (Or.inl he)))).mp hzt
    · exact (dependsOn_connectionEventIn 2 (brExtensionRectangleEdges m n) z r
        (fun e he ↦ hagree e (mem_brSourceXSupport_iff.mpr (Or.inr he)))).mp hzr
  · rintro ⟨z, hz, b, hb, t, ht, r, hr, hzb, hzt, hzr⟩
    refine ⟨z, hz, b, hb, t, ht, r, hr, ?_, ?_, ?_⟩
    · exact (dependsOn_connectionEventIn 2 (brSourceSquareEdges n) z b
        (fun e he ↦ (hagree e (mem_brSourceXSupport_iff.mpr (Or.inl he))).symm)).mp hzb
    · exact (dependsOn_connectionEventIn 2 (brSourceSquareEdges n) z t
        (fun e he ↦ (hagree e (mem_brSourceXSupport_iff.mpr (Or.inl he))).symm)).mp hzt
    · exact (dependsOn_connectionEventIn 2 (brExtensionRectangleEdges m n) z r
        (fun e he ↦ (hagree e (mem_brSourceXSupport_iff.mpr (Or.inr he))).symm)).mp hzr

theorem measurableSet_brSourceXEvent (m n : ℕ) :
    MeasurableSet (brSourceXEvent m n) :=
  (dependsOn_brSourceXEvent m n).measurableSet

theorem isIncreasingEvent_brSourceXEvent (m n : ℕ) :
    IsIncreasingEvent (brSourceXEvent m n) := by
  intro omega eta hmono
  rw [mem_brSourceXEvent_iff, mem_brSourceXEvent_iff]
  rintro ⟨z, hz, b, hb, t, ht, r, hr, hzb, hzt, hzr⟩
  refine ⟨z, hz, b, hb, t, ht, r, hr, ?_, ?_, ?_⟩
  · exact isIncreasingEvent_connectionEventIn 2 (brSourceSquareEdges n) z b hmono hzb
  · exact isIncreasingEvent_connectionEventIn 2 (brSourceSquareEdges n) z t hmono hzt
  · exact isIncreasingEvent_connectionEventIn 2 (brExtensionRectangleEdges m n) z r hmono hzr

end

end Percolation
