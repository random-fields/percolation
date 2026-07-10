import Percolation.Critical.PivotalSausage
import Percolation.Bernoulli.Reliability

/-!
# Menshikov's differential inequalities

This file develops equations 5.9--5.24 and the exponential-decay consequences from Grimmett
§5.2.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal unitInterval BigOperators

/-- The real function to which Russo's formula is applied; densities outside `[0,1]` are
clamped back to the unit interval. -/
noncomputable def clampedRadiusTail (d n : ℕ) (x : Cubic d) (p : ℝ) : ℝ :=
  (bernoulliBondMeasure d (Set.projIcc 0 1 zero_le_one p)).real
    (radiusConnectionEvent d x n)

/-- The conditional mean pivotal count, written as its finite probability ratio. -/
noncomputable def conditionalExpectedRadiusPivotalCount
    (d : ℕ) (p : I) (x : Cubic d) (n : ℕ) : ℝ :=
  (∑ e ∈ cubicMetricBallEdges d x n,
      (bernoulliBondMeasure d p).real
        (radiusConnectionEvent d x n ∩ pivotalEvent (radiusConnectionEvent d x n) e)) /
    (bernoulliBondMeasure d p).real (radiusConnectionEvent d x n)

/-- Russo's formula (5.9) for `Aₙ(x)`. -/
theorem radiusTail_russo_hasDerivAt {d n : ℕ} {x : Cubic d} {p : I}
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    HasDerivAt (clampedRadiusTail d n x)
      (∑ e ∈ cubicMetricBallEdges d x n,
        (bernoulliBondMeasure d p).real
          (pivotalEvent (radiusConnectionEvent d x n) e)) (p : ℝ) := by
  exact (isIncreasingEvent_radiusConnectionEvent d x n).bernoulliBondMeasure_real_russo_hasDerivAt
    (dependsOn_radiusConnectionEvent d x n) hp0 hp1

/-- Equation (5.10): the logarithmic derivative of the radius tail is the conditional
expected pivotal count divided by `p`. -/
theorem radiusTail_logDeriv_eq_conditionalExpectedPivotalCount {d n : ℕ}
    {x : Cubic d} {p : I} (hp0 : 0 < (p : ℝ))
    (hg : 0 < (bernoulliBondMeasure d p).real (radiusConnectionEvent d x n)) :
    (∑ e ∈ cubicMetricBallEdges d x n,
        (bernoulliBondMeasure d p).real
          (pivotalEvent (radiusConnectionEvent d x n) e)) /
      (bernoulliBondMeasure d p).real (radiusConnectionEvent d x n) =
      conditionalExpectedRadiusPivotalCount d p x n / (p : ℝ) := by
  let A := radiusConnectionEvent d x n
  let E := cubicMetricBallEdges d x n
  have hsum :
      (∑ e ∈ E, (bernoulliBondMeasure d p).real (A ∩ pivotalEvent A e)) =
        (p : ℝ) * ∑ e ∈ E, (bernoulliBondMeasure d p).real (pivotalEvent A e) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    exact (isIncreasingEvent_radiusConnectionEvent d x n).bernoulliBondMeasure_real_inter_pivotalEvent
        (dependsOn_radiusConnectionEvent d x n) he p
  rw [conditionalExpectedRadiusPivotalCount]
  change _ / _ = ((∑ e ∈ E, (bernoulliBondMeasure d p).real (A ∩ pivotalEvent A e)) /
    (bernoulliBondMeasure d p).real A) / (p : ℝ)
  rw [hsum]
  have hg0 : (bernoulliBondMeasure d p).real A ≠ 0 := by
    dsimp [A]
    linarith
  field_simp [hg0, ne_of_gt hp0]
  rw [mul_comm]

theorem radiusTail_log_hasDerivAt {d n : ℕ} {x : Cubic d} {p : I}
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hg : 0 < (bernoulliBondMeasure d p).real (radiusConnectionEvent d x n)) :
    HasDerivAt (fun q : ℝ ↦ Real.log (clampedRadiusTail d n x q))
      (conditionalExpectedRadiusPivotalCount d p x n / (p : ℝ)) (p : ℝ) := by
  have hclamp : Set.projIcc (0 : ℝ) 1 zero_le_one (p : ℝ) = p := by
    apply Subtype.ext
    simp
  have hvalue : clampedRadiusTail d n x (p : ℝ) =
      (bernoulliBondMeasure d p).real (radiusConnectionEvent d x n) := by
    simp [clampedRadiusTail, hclamp]
  have hlog := (radiusTail_russo_hasDerivAt (x := x) hp0 hp1).log (by
    rw [hvalue]
    exact ne_of_gt hg)
  convert hlog using 1
  rw [hvalue]
  exact (radiusTail_logDeriv_eq_conditionalExpectedPivotalCount hp0 hg).symm

end Percolation
