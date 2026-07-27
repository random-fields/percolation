import Percolation.Planar.Inhomogeneous

/-! Source-facing application and endpoint cases for the frozen Chapter 11 review. -/

namespace Review.Chapter11Cases

open Percolation Filter MeasureTheory
open scoped ENNReal Real unitInterval

private noncomputable def threeQuarterDensity : I :=
  ⟨3 / 4, by norm_num, by norm_num⟩

private noncomputable def quarterDensity : I :=
  ⟨1 / 4, by norm_num, by norm_num⟩

example : cubicCriticalProbability 2 = (1 / 2 : ℝ) :=
  cubicCriticalProbability_two_eq_half

example (n : ℕ) :
    (bernoulliBondMeasure 2 squareHalfDensity).real
        (grimmettRectangleCrossingEvent n) = 1 / 2 :=
  bernoulliBondMeasure_real_grimmettRectangleCrossingEvent_half n

example :
    ∃ β γ : ℝ, 0 < β ∧ 0 < γ ∧ ∀ n : ℕ, 1 ≤ n →
      (bernoulliBondMeasure 2 threeQuarterDensity).real
          {ω | (maxEdgeDisjointGrimmettRectangleCrossings n ω : ℝ) ≤ β * n} ≤
        Real.exp (-γ * n) := by
  apply maxEdgeDisjointGrimmettRectangleCrossings_probability_le_exp
  norm_num [threeQuarterDensity]

example :
    0 < finiteCorrelationLength threeQuarterDensity ∧
      finiteCorrelationLength threeQuarterDensity < ⊤ := by
  apply finiteCorrelationLength_pos_lt_top
  · norm_num [threeQuarterDensity]
  · norm_num [threeQuarterDensity]

example :
    Tendsto (fun n : ℕ ↦
        -Real.log (tubeTwoPointConnectivity squareHalfDensity 1 n) / n)
        atTop (nhds (tubeConnectivityDecayRate squareHalfDensity 1)) ∧
      (∀ n : ℕ, 1 ≤ n → tubeTwoPointConnectivity squareHalfDensity 1 n ≤
        Real.exp (-(n : ℝ) * tubeConnectivityDecayRate squareHalfDensity 1)) ∧
      0 < tubeConnectivityDecayRate squareHalfDensity 1 ∧
      tubeConnectivityDecayRate squareHalfDensity 1 ≤
        -Real.log (squareHalfDensity : ℝ) ∧
      Antitone (tubeConnectivityDecayRate squareHalfDensity) ∧
      Tendsto (tubeConnectivityDecayRate squareHalfDensity) atTop
        (nhds (axisConnectivityDecayRate 2 squareHalfDensity)) := by
  apply tubeConnectivityDecayRate_properties (k := 1)
  · norm_num
  · norm_num

example : inhomogeneousSquareTheta quarterDensity threeQuarterDensity = 0 := by
  exact (inhomogeneousSquare_criticalSurface
    (pₕ := quarterDensity) (pᵥ := threeQuarterDensity)
    (by norm_num [quarterDensity]) (by norm_num [threeQuarterDensity])).1
      (by norm_num [quarterDensity, threeQuarterDensity,
        inhomogeneousSquareCriticalPolynomial])

example : 0 < inhomogeneousSquareTheta threeQuarterDensity threeQuarterDensity := by
  exact (inhomogeneousSquare_criticalSurface
    (pₕ := threeQuarterDensity) (pᵥ := threeQuarterDensity)
    (by norm_num [threeQuarterDensity]) (by norm_num [threeQuarterDensity])).2
      (by norm_num [threeQuarterDensity, inhomogeneousSquareCriticalPolynomial])

end Review.Chapter11Cases
