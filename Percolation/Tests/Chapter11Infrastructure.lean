import Percolation.Planar.Inhomogeneous

/-!
# Chapter 11 semantic application checks

These small declarations exercise the source-facing interfaces with concrete parameters.  They
are intentionally narrow wrappers: each application test visibly invokes the declaration under
review, while arithmetic endpoint checks are proved independently by `norm_num`.
-/

namespace Percolation.Tests.Chapter11

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Real unitInterval

private noncomputable def quarterDensity : I :=
  ⟨1 / 4, by norm_num, by norm_num⟩

private noncomputable def threeQuarterDensity : I :=
  ⟨3 / 4, by norm_num, by norm_num⟩

private noncomputable def halfDensity : I :=
  ⟨1 / 2, by norm_num, by norm_num⟩

@[simp] private theorem coe_quarterDensity : (quarterDensity : ℝ) = 1 / 4 := rfl
@[simp] private theorem coe_threeQuarterDensity : (threeQuarterDensity : ℝ) = 3 / 4 := rfl
@[simp] private theorem coe_halfDensity : (halfDensity : ℝ) = 1 / 2 := rfl

/-! ## Exact threshold and critical RSW stack -/

example : cubicCriticalProbability 2 = (1 / 2 : ℝ) := by
  exact cubicCriticalProbability_two_eq_half

example : theta 2 squareHalfDensity = 0 := by
  exact theta_two_half_eq_zero

example (n : ℕ) :
    (bernoulliBondMeasure 2 squareHalfDensity).real
        (grimmettRectangleCrossingEvent n) = 1 / 2 := by
  exact bernoulliBondMeasure_real_grimmettRectangleCrossingEvent_half n

example (l : ℕ) (hl : 1 ≤ l) :
    rswSquareCrossingProbability squareHalfDensity l ^ 12 *
        (1 - Real.sqrt
          (1 - rswSquareCrossingProbability squareHalfDensity l)) ^ 48 ≤
      rswAnnulusOpenCircuitProbability squareHalfDensity l := by
  exact rswAnnulusOpenCircuitProbability_ge squareHalfDensity l hl

example (l : ℕ) (hl : 1 ≤ l) :
    (rswSquareCrossingProbability squareHalfDensity l *
          rswThreeHalvesCrossingProbability squareHalfDensity l ^ 2 ≤
        rswRectangleCrossingProbability squareHalfDensity 2 l) ∧
      (rswSquareCrossingProbability squareHalfDensity l *
          rswRectangleCrossingProbability squareHalfDensity 2 l ^ 2 ≤
        rswRectangleCrossingProbability squareHalfDensity 3 l) ∧
      (rswRectangleCrossingProbability squareHalfDensity 3 l ^ 4 ≤
        rswAnnulusOpenCircuitProbability squareHalfDensity l) := by
  exact rsw_gluing_inequalities squareHalfDensity l hl

/-! ## Exact source rectangle and supercritical tails -/

example :
    ∃ β γ : ℝ, 0 < β ∧ 0 < γ ∧ ∀ n : ℕ, 1 ≤ n →
      (bernoulliBondMeasure 2 threeQuarterDensity).real
          {ω | (maxEdgeDisjointGrimmettRectangleCrossings n ω : ℝ) ≤ β * n} ≤
        Real.exp (-γ * n) := by
  apply maxEdgeDisjointGrimmettRectangleCrossings_probability_le_exp
  norm_num

example (n : ℕ) :
    HasEdgeDisjointGrimmettRectangleCrossings n 0 (∅ : EdgeConfiguration 2) := by
  exact hasEdgeDisjointGrimmettRectangleCrossings_zero n ∅

example : 0 < theta 2 threeQuarterDensity := by
  apply theta_pos_of_criticalProbability_lt
  rw [cubicCriticalProbability_two_eq_half]
  norm_num

example (n : ℕ) :
    (bernoulliBondMeasure 2 threeQuarterDensity).real
        (eventuallySurroundingOpenCircuitEvent n) = 1 := by
  exact eventuallySurroundingOpenCircuit_probability_one
    (show 0 < theta 2 threeQuarterDensity by
      apply theta_pos_of_criticalProbability_lt
      rw [cubicCriticalProbability_two_eq_half]
      norm_num) n

example :
    finiteCorrelationLength threeQuarterDensity =
      (2 : ℝ≥0∞)⁻¹ * correlationLength 2 (σ threeQuarterDensity) := by
  apply finiteCorrelationLength_eq_half_correlationLength_complement
  · norm_num
  · norm_num

example :
    0 < finiteCorrelationLength threeQuarterDensity ∧
      finiteCorrelationLength threeQuarterDensity < ⊤ := by
  apply finiteCorrelationLength_pos_lt_top
  · norm_num
  · norm_num

example : ∃ η : ℝ, 0 < η ∧ ∀ n : ℕ,
    finiteClusterSizeProbability 2 threeQuarterDensity n ≤
      Real.exp (-η * Real.sqrt n) := by
  apply finiteClusterSizeProbability_le_exp_neg_sqrt_of_supercritical
  · norm_num
  · norm_num

/-! ## Tube decay -/

example :
    Tendsto (fun n : ℕ ↦
        -Real.log (tubeTwoPointConnectivity halfDensity 1 n) / n)
        atTop (nhds (tubeConnectivityDecayRate halfDensity 1)) ∧
      (∀ n : ℕ, 1 ≤ n → tubeTwoPointConnectivity halfDensity 1 n ≤
        Real.exp (-(n : ℝ) * tubeConnectivityDecayRate halfDensity 1)) ∧
      0 < tubeConnectivityDecayRate halfDensity 1 ∧
      tubeConnectivityDecayRate halfDensity 1 ≤ -Real.log (halfDensity : ℝ) ∧
      Antitone (tubeConnectivityDecayRate halfDensity) ∧
      Tendsto (tubeConnectivityDecayRate halfDensity) atTop
        (nhds (axisConnectivityDecayRate 2 halfDensity)) := by
  apply tubeConnectivityDecayRate_properties (k := 1)
  · norm_num
  · norm_num

/-! ## Externally sourced source-facing statements -/

example (G : FiniteConnectedSquareSubgraph) :
    ∃! E : Finset SquareEdge,
      ∃ c : DualCircuit,
        c.crossedPrimalEdgeFinset = E ∧ G.IsBoundaryCircuit c := by
  exact existsUnique_boundaryCircuitCrossedEdges G

example :
    openClustersPerVertex 2 squareHalfDensity =
      openClustersPerVertex 2 (σ squareHalfDensity) + 1 -
        2 * (squareHalfDensity : ℝ) := by
  exact openClustersPerVertex_square_duality squareHalfDensity

example :
    ∃ A₁ a₁ A₂ a₂ a₃ : ℝ,
      0 < A₁ ∧ 0 < a₁ ∧ 0 < A₂ ∧ 0 < a₂ ∧ 0 < a₃ ∧
      (∀ n : ℕ, 1 ≤ n →
        (1 / 2 : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ)) ≤
          boxRadiusTail 2 squareHalfDensity n ∧
        boxRadiusTail 2 squareHalfDensity n ≤ A₁ * (n : ℝ) ^ (-a₁) ∧
        (1 / 2 : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ)) ≤
          clusterSizeAtLeast 2 squareHalfDensity n ∧
        clusterSizeAtLeast 2 squareHalfDensity n ≤ A₂ * (n : ℝ) ^ (-a₂)) ∧
      Integrable (fun ω ↦ (clusterSizeENNReal 2 ω).toReal ^ a₃)
        (bernoulliBondMeasure 2 squareHalfDensity) := by
  exact squareCritical_powerLaw_bounds

/-! ## Inhomogeneous critical surfaces and arithmetic oracles -/

example :
    inhomogeneousSquareCriticalPolynomial quarterDensity threeQuarterDensity = 1 := by
  norm_num [inhomogeneousSquareCriticalPolynomial]

example : inhomogeneousSquareTheta quarterDensity threeQuarterDensity = 0 := by
  exact (inhomogeneousSquare_criticalSurface
    (pₕ := quarterDensity) (pᵥ := threeQuarterDensity) (by norm_num) (by norm_num)).1
      (by norm_num [inhomogeneousSquareCriticalPolynomial])

example : 0 < inhomogeneousSquareTheta threeQuarterDensity threeQuarterDensity := by
  exact (inhomogeneousSquare_criticalSurface
    (pₕ := threeQuarterDensity) (pᵥ := threeQuarterDensity) (by norm_num) (by norm_num)).2
      (by norm_num [inhomogeneousSquareCriticalPolynomial])

example :
    inhomogeneousTriangularCriticalPolynomial halfDensity halfDensity halfDensity = 11 / 8 := by
  norm_num [inhomogeneousTriangularCriticalPolynomial]

example :
    0 < inhomogeneousTriangularTheta halfDensity halfDensity halfDensity := by
  exact (inhomogeneousTriangular_criticalSurface
    (pₕ := halfDensity) (pᵥ := halfDensity) (pₑ := halfDensity)
    (by norm_num) (by norm_num) (by norm_num)).2
      (by norm_num [inhomogeneousTriangularCriticalPolynomial])

end Percolation.Tests.Chapter11
