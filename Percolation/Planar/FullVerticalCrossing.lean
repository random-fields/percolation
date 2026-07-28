import Percolation.Critical.SupercriticalCrossing
import Percolation.Planar.RSWPlacements

/-!
# Full vertical square crossings

This module transports the qualitative supercritical box-crossing theorem into the coordinate
frame `[0, 2n] x [-n, n]` used by the planar parity argument.  Unlike the RSW events, these
crossings use every bond of the box; this distinction is essential near the boundary.
-/

namespace Percolation

open Filter MeasureTheory
open scoped unitInterval

/-- Translate the centred radius-`n` square to `[0, 2n] x [-n, n]`. -/
def fullVerticalCrossingPlacementIso (n : ℕ) : squareGraph ≃g squareGraph :=
  cubicTranslationIso cubicOrigin (squareVertex (n : ℤ) 0)

@[simp]
theorem fullVerticalCrossingPlacementIso_zero (n : ℕ) (x : SquareVertex) :
    fullVerticalCrossingPlacementIso n x 0 = x 0 + n := by
  simp [fullVerticalCrossingPlacementIso, cubicTranslationIso_apply, cubicTranslate,
    cubicOrigin, squareVertex]

@[simp]
theorem fullVerticalCrossingPlacementIso_one (n : ℕ) (x : SquareVertex) :
    fullVerticalCrossingPlacementIso n x 1 = x 1 := by
  simp [fullVerticalCrossingPlacementIso, cubicTranslationIso_apply, cubicTranslate,
    cubicOrigin, squareVertex]

/-- A full bottom-to-top crossing of `[0, 2n] x [-n, n]`. -/
def fullVerticalCrossingEvent (n : ℕ) : Set (EdgeConfiguration 2) :=
  cubicGraphIsoEvent (fullVerticalCrossingPlacementIso n)
    (leftRightCrossingEvent 2 n (1 : Fin 2))

theorem measurableSet_fullVerticalCrossingEvent (n : ℕ) :
    MeasurableSet (fullVerticalCrossingEvent n) :=
  measurableSet_cubicGraphIsoEvent _
    (measurableSet_leftRightCrossingEvent 2 n (1 : Fin 2))

/-- Translation does not change the Bernoulli probability of the full vertical crossing. -/
theorem bernoulliBondMeasure_real_fullVerticalCrossingEvent (p : I) (n : ℕ) :
    (bernoulliBondMeasure 2 p).real (fullVerticalCrossingEvent n) =
      (bernoulliBondMeasure 2 p).real
        (leftRightCrossingEvent 2 n (1 : Fin 2)) :=
  bernoulliBondMeasure_real_cubicGraphIsoEvent p _
    (measurableSet_leftRightCrossingEvent 2 n (1 : Fin 2))

/-- If the percolation probability is positive, translated full vertical crossings tend to
probability one. -/
theorem fullVerticalCrossing_probability_tendsto_one (p : I) (htheta : 0 < theta 2 p) :
    Tendsto (fun n ↦ (bernoulliBondMeasure 2 p).real
      (fullVerticalCrossingEvent n)) atTop (nhds 1) := by
  simpa only [bernoulliBondMeasure_real_fullVerticalCrossingEvent] using
    leftRightCrossing_probability_tendsto_one (d := 2) (by omega) p htheta (1 : Fin 2)

end Percolation
