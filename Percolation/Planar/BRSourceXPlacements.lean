import Percolation.Bernoulli.FKGInfinite
import Percolation.Planar.BRSourceXEvent

/-!
# Symmetric placement and FKG gluing input for the BR source event

The second copy of `X(R)` is reflected across the vertical midline of the source square.  This
module records the exact transported event and the FKG lower bound for its intersection with a
horizontal crossing of the source square.  The deterministic inclusion of this intersection in
the wider rectangle crossing is kept in a separate geometry module.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval

noncomputable section

/-- The horizontally reflected copy of `X(R)`. -/
def brReflectedSourceXEvent (m n : ℕ) : Set (EdgeConfiguration 2) :=
  cubicGraphIsoEvent (brPrimalSourceVerticalAxisReflectionIso n)
    (brSourceXEvent m n)

theorem measurableSet_brReflectedSourceXEvent (m n : ℕ) :
    MeasurableSet (brReflectedSourceXEvent m n) :=
  measurableSet_cubicGraphIsoEvent _ (measurableSet_brSourceXEvent m n)

theorem isIncreasingEvent_brReflectedSourceXEvent (m n : ℕ) :
    IsIncreasingEvent (brReflectedSourceXEvent m n) :=
  isIncreasingEvent_cubicGraphIsoEvent _ (isIncreasingEvent_brSourceXEvent m n)

theorem bernoulliBondMeasure_real_brReflectedSourceXEvent
    (p : I) (m n : ℕ) :
    (bernoulliBondMeasure 2 p).real (brReflectedSourceXEvent m n) =
      (bernoulliBondMeasure 2 p).real (brSourceXEvent m n) :=
  bernoulliBondMeasure_real_cubicGraphIsoEvent p _
    (measurableSet_brSourceXEvent m n)

/-- The three increasing events used in BR Corollary 7. -/
def brSourceXGluingIntersection (m n : ℕ) : Set (EdgeConfiguration 2) :=
  brSourceXEvent m n ∩ brReflectedSourceXEvent m n ∩
    rswSquareCrossingEvent n

theorem measurableSet_brSourceXGluingIntersection (m n : ℕ) :
    MeasurableSet (brSourceXGluingIntersection m n) :=
  ((measurableSet_brSourceXEvent m n).inter
    (measurableSet_brReflectedSourceXEvent m n)).inter
      (measurableSet_rswSquareCrossingEvent n)

theorem isIncreasingEvent_brSourceXGluingIntersection (m n : ℕ) :
    IsIncreasingEvent (brSourceXGluingIntersection m n) :=
  ((isIncreasingEvent_brSourceXEvent m n).inter
    (isIncreasingEvent_brReflectedSourceXEvent m n)).inter
      (isIncreasingEvent_rswSquareCrossingEvent n)

/-- FKG part of Bollobás--Riordan Corollary 7, before the deterministic gluing inclusion. -/
theorem brSourceXGluingIntersection_probability_ge
    (p : I) (m n : ℕ) :
    rswSquareCrossingProbability p n *
        (bernoulliBondMeasure 2 p).real (brSourceXEvent m n) ^ 2 ≤
      (bernoulliBondMeasure 2 p).real
        (brSourceXGluingIntersection m n) := by
  let μ := bernoulliBondMeasure 2 p
  let X := brSourceXEvent m n
  let X' := brReflectedSourceXEvent m n
  let H := rswSquareCrossingEvent n
  have hXX := bernoulliBondMeasure_real_fkg p
    (isIncreasingEvent_brSourceXEvent m n)
    (isIncreasingEvent_brReflectedSourceXEvent m n)
    (measurableSet_brSourceXEvent m n)
    (measurableSet_brReflectedSourceXEvent m n)
  have hXXH := bernoulliBondMeasure_real_fkg p
    ((isIncreasingEvent_brSourceXEvent m n).inter
      (isIncreasingEvent_brReflectedSourceXEvent m n))
    (isIncreasingEvent_rswSquareCrossingEvent n)
    ((measurableSet_brSourceXEvent m n).inter
      (measurableSet_brReflectedSourceXEvent m n))
    (measurableSet_rswSquareCrossingEvent n)
  have hX' : μ.real X' = μ.real X :=
    bernoulliBondMeasure_real_brReflectedSourceXEvent p m n
  calc
    rswSquareCrossingProbability p n * μ.real X ^ 2 =
        (μ.real X * μ.real X') * μ.real H := by
      rw [hX']
      change μ.real H * μ.real X ^ 2 =
        (μ.real X * μ.real X) * μ.real H
      ring
    _ ≤ μ.real (X ∩ X') * μ.real H := by
      exact mul_le_mul_of_nonneg_right hXX measureReal_nonneg
    _ ≤ μ.real ((X ∩ X') ∩ H) := hXXH
    _ = μ.real (brSourceXGluingIntersection m n) := rfl

end

end Percolation
