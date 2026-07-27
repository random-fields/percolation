import Percolation.Critical.CubicSymmetry
import Percolation.Planar.RSWEvents

/-!
# Symmetric placements of RSW crossing events

The gluing argument in Grimmett, Lemma 11.75 uses translated horizontal crossings and
quarter-turned crossings.  This file defines those events as pullbacks along concrete cubic-graph
automorphisms.  Consequently measurability, increasingness, and equality of their Bernoulli
probabilities are proved once and do not rely on an informal appeal to lattice symmetry.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval

/-- Swap the two square-lattice coordinates. -/
def squareCoordinateSwap : Fin 2 ≃ Fin 2 := Equiv.swap 0 1

/-- Translate `sourceCenter` to the origin, swap the two coordinates, and translate the origin
to `targetCenter`.  A horizontal crossing centered at `sourceCenter` is thereby placed as a
vertical crossing centered at `targetCenter`. -/
def squareCrossingQuarterTurnIso (sourceCenter targetCenter : SquareVertex) :
    squareGraph ≃g squareGraph :=
  (cubicTranslationIso sourceCenter cubicOrigin).trans
    ((cubicCoordinatePermutationIso squareCoordinateSwap).trans
      (cubicTranslationIso cubicOrigin targetCenter))

/-- Translate a source crossing whose centre is `sourceCenter` to `targetCenter`. -/
def squareCrossingTranslateIso (sourceCenter targetCenter : SquareVertex) :
    squareGraph ≃g squareGraph :=
  cubicTranslationIso sourceCenter targetCenter

/-- A horizontal placement of a source event. -/
def rswHorizontalPlacementEvent (sourceCenter targetCenter : SquareVertex)
    (A : Set (EdgeConfiguration 2)) : Set (EdgeConfiguration 2) :=
  cubicGraphIsoEvent (squareCrossingTranslateIso sourceCenter targetCenter) A

/-- A vertical placement of a source event. -/
def rswVerticalPlacementEvent (sourceCenter targetCenter : SquareVertex)
    (A : Set (EdgeConfiguration 2)) : Set (EdgeConfiguration 2) :=
  cubicGraphIsoEvent (squareCrossingQuarterTurnIso sourceCenter targetCenter) A

theorem measurableSet_rswHorizontalPlacementEvent
    (sourceCenter targetCenter : SquareVertex) {A : Set (EdgeConfiguration 2)}
    (hA : MeasurableSet A) :
    MeasurableSet (rswHorizontalPlacementEvent sourceCenter targetCenter A) :=
  measurableSet_cubicGraphIsoEvent _ hA

theorem measurableSet_rswVerticalPlacementEvent
    (sourceCenter targetCenter : SquareVertex) {A : Set (EdgeConfiguration 2)}
    (hA : MeasurableSet A) :
    MeasurableSet (rswVerticalPlacementEvent sourceCenter targetCenter A) :=
  measurableSet_cubicGraphIsoEvent _ hA

theorem isIncreasingEvent_rswHorizontalPlacementEvent
    (sourceCenter targetCenter : SquareVertex) {A : Set (EdgeConfiguration 2)}
    (hA : IsIncreasingEvent A) :
    IsIncreasingEvent (rswHorizontalPlacementEvent sourceCenter targetCenter A) :=
  isIncreasingEvent_cubicGraphIsoEvent _ hA

theorem isIncreasingEvent_rswVerticalPlacementEvent
    (sourceCenter targetCenter : SquareVertex) {A : Set (EdgeConfiguration 2)}
    (hA : IsIncreasingEvent A) :
    IsIncreasingEvent (rswVerticalPlacementEvent sourceCenter targetCenter A) :=
  isIncreasingEvent_cubicGraphIsoEvent _ hA

theorem bernoulliBondMeasure_real_rswHorizontalPlacementEvent
    (p : I) (sourceCenter targetCenter : SquareVertex)
    {A : Set (EdgeConfiguration 2)} (hA : MeasurableSet A) :
    (bernoulliBondMeasure 2 p).real
        (rswHorizontalPlacementEvent sourceCenter targetCenter A) =
      (bernoulliBondMeasure 2 p).real A :=
  bernoulliBondMeasure_real_cubicGraphIsoEvent p _ hA

theorem bernoulliBondMeasure_real_rswVerticalPlacementEvent
    (p : I) (sourceCenter targetCenter : SquareVertex)
    {A : Set (EdgeConfiguration 2)} (hA : MeasurableSet A) :
    (bernoulliBondMeasure 2 p).real
        (rswVerticalPlacementEvent sourceCenter targetCenter A) =
      (bernoulliBondMeasure 2 p).real A :=
  bernoulliBondMeasure_real_cubicGraphIsoEvent p _ hA

/-! ### The placements in equations (11.76)--(11.78) -/

/-- The source centre of `LR(kl,l)` in the translated coordinates `[0,2kl] × [-l,l]`. -/
def rswRectangleCenter (k l : ℕ) : SquareVertex :=
  squareVertex (k * l : ℕ) 0

/-- The left `3l × 2l` horizontal crossing in Figure 11.25. -/
def rswGluingTwoLeftEvent (l : ℕ) : Set (EdgeConfiguration 2) :=
  rswThreeHalvesCrossingEvent l

/-- The translate by `(l,0)` of the right `3l × 2l` crossing in Figure 11.25. -/
def rswGluingTwoRightEvent (l : ℕ) : Set (EdgeConfiguration 2) :=
  rswHorizontalPlacementEvent cubicOrigin (squareVertex (l : ℕ) 0)
    (rswThreeHalvesCrossingEvent l)

/-- The top-bottom crossing of `[l,3l] × [-l,l]` in Figure 11.25. -/
def rswGluingTwoVerticalEvent (l : ℕ) : Set (EdgeConfiguration 2) :=
  rswVerticalPlacementEvent (rswRectangleCenter 1 l)
    (squareVertex (2 * l : ℕ) 0) (rswSquareCrossingEvent l)

/-- Simultaneous occurrence of the three crossings in Figure 11.25. -/
def rswGluingTwoIntersection (l : ℕ) : Set (EdgeConfiguration 2) :=
  rswGluingTwoLeftEvent l ∩ rswGluingTwoRightEvent l ∩ rswGluingTwoVerticalEvent l

/-- The left `4l × 2l` crossing in Figure 11.26. -/
def rswGluingThreeLeftEvent (l : ℕ) : Set (EdgeConfiguration 2) :=
  rswRectangleCrossingEvent 2 l

/-- The translate by `(2l,0)` of the right `4l × 2l` crossing in Figure 11.26. -/
def rswGluingThreeRightEvent (l : ℕ) : Set (EdgeConfiguration 2) :=
  rswHorizontalPlacementEvent cubicOrigin (squareVertex (2 * l : ℕ) 0)
    (rswRectangleCrossingEvent 2 l)

/-- The top-bottom crossing of `[2l,4l] × [-l,l]` in Figure 11.26. -/
def rswGluingThreeVerticalEvent (l : ℕ) : Set (EdgeConfiguration 2) :=
  rswVerticalPlacementEvent (rswRectangleCenter 1 l)
    (squareVertex (3 * l : ℕ) 0) (rswSquareCrossingEvent l)

/-- Simultaneous occurrence of the three crossings in Figure 11.26. -/
def rswGluingThreeIntersection (l : ℕ) : Set (EdgeConfiguration 2) :=
  rswGluingThreeLeftEvent l ∩ rswGluingThreeRightEvent l ∩
    rswGluingThreeVerticalEvent l

/-- Horizontal crossing of the upper `6l × 2l` rectangle in Figure 11.27. -/
def rswCircuitTopEvent (l : ℕ) : Set (EdgeConfiguration 2) :=
  rswHorizontalPlacementEvent (rswRectangleCenter 3 l)
    (squareVertex 0 (2 * l : ℕ)) (rswRectangleCrossingEvent 3 l)

/-- Horizontal crossing of the lower `6l × 2l` rectangle in Figure 11.27. -/
def rswCircuitBottomEvent (l : ℕ) : Set (EdgeConfiguration 2) :=
  rswHorizontalPlacementEvent (rswRectangleCenter 3 l)
    (squareVertex 0 (-(2 * l : ℕ) : ℤ)) (rswRectangleCrossingEvent 3 l)

/-- Vertical crossing of the right `2l × 6l` rectangle in Figure 11.27. -/
def rswCircuitRightEvent (l : ℕ) : Set (EdgeConfiguration 2) :=
  rswVerticalPlacementEvent (rswRectangleCenter 3 l)
    (squareVertex (2 * l : ℕ) 0) (rswRectangleCrossingEvent 3 l)

/-- Vertical crossing of the left `2l × 6l` rectangle in Figure 11.27. -/
def rswCircuitLeftEvent (l : ℕ) : Set (EdgeConfiguration 2) :=
  rswVerticalPlacementEvent (rswRectangleCenter 3 l)
    (squareVertex (-(2 * l : ℕ) : ℤ) 0) (rswRectangleCrossingEvent 3 l)

/-- Simultaneous occurrence of the four rectangle crossings in Figure 11.27. -/
def rswCircuitGluingIntersection (l : ℕ) : Set (EdgeConfiguration 2) :=
  rswCircuitTopEvent l ∩ rswCircuitRightEvent l ∩
    rswCircuitBottomEvent l ∩ rswCircuitLeftEvent l

end Percolation
