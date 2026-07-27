import Percolation.Planar.Inhomogeneous

namespace Review.Chapter11

open Percolation Filter MeasureTheory
open scoped ENNReal Real unitInterval

theorem theorem_11_11 : cubicCriticalProbability 2 = (1 / 2 : ℝ) :=
  cubicCriticalProbability_two_eq_half

theorem lemma_11_12 : theta 2 squareHalfDensity = 0 :=
  theta_two_half_eq_zero

theorem lemma_11_21 (n : ℕ) :
    (bernoulliBondMeasure 2 squareHalfDensity).real
        (grimmettRectangleCrossingEvent n) = 1 / 2 :=
  bernoulliBondMeasure_real_grimmettRectangleCrossingEvent_half n

theorem lemma_11_22 {p : I} (hp : (1 / 2 : ℝ) < p) :
    ∃ β γ : ℝ, 0 < β ∧ 0 < γ ∧ ∀ n : ℕ, 1 ≤ n →
      (bernoulliBondMeasure 2 p).real
          {ω | (maxEdgeDisjointGrimmettRectangleCrossings n ω : ℝ) ≤ β * n} ≤
        Real.exp (-γ * n) :=
  maxEdgeDisjointGrimmettRectangleCrossings_probability_le_exp hp

theorem theorem_11_24 {p : I} (hpHalf : (1 / 2 : ℝ) < p) (hpOne : (p : ℝ) < 1) :
    Tendsto (fun n : ℕ ↦ -Real.log (truncatedTwoPointConnectivity p n) / n)
        atTop (nhds (truncatedConnectivityDecayRate p)) ∧
      finiteCorrelationLength p = (2 : ℝ≥0∞)⁻¹ * correlationLength 2 (σ p) ∧
      0 < finiteCorrelationLength p ∧ finiteCorrelationLength p < ⊤ := by
  exact ⟨truncatedTwoPointConnectivity_logRate_tendsto hpHalf hpOne,
    finiteCorrelationLength_eq_half_correlationLength_complement hpHalf hpOne,
    finiteCorrelationLength_pos_lt_top hpHalf hpOne⟩

theorem lemma_11_27 {p : I} (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    {k : ℕ} (_hk : 1 ≤ k) :
    Tendsto (fun n : ℕ ↦ -Real.log (tubeTwoPointConnectivity p k n) / n)
        atTop (nhds (tubeConnectivityDecayRate p k)) ∧
      (∀ n : ℕ, 1 ≤ n → tubeTwoPointConnectivity p k n ≤
        Real.exp (-(n : ℝ) * tubeConnectivityDecayRate p k)) ∧
      0 < tubeConnectivityDecayRate p k ∧
      tubeConnectivityDecayRate p k ≤ -Real.log (p : ℝ) ∧
      Antitone (tubeConnectivityDecayRate p) ∧
      Tendsto (tubeConnectivityDecayRate p) atTop
        (nhds (axisConnectivityDecayRate 2 p)) :=
  tubeConnectivityDecayRate_properties hp0 hp1 k

theorem lemma_11_75 (p : I) (l : ℕ) (hl : 1 ≤ l) :
    (rswSquareCrossingProbability p l *
          rswThreeHalvesCrossingProbability p l ^ 2 ≤
        rswRectangleCrossingProbability p 2 l) ∧
      (rswSquareCrossingProbability p l *
          rswRectangleCrossingProbability p 2 l ^ 2 ≤
        rswRectangleCrossingProbability p 3 l) ∧
      (rswRectangleCrossingProbability p 3 l ^ 4 ≤
        rswAnnulusOpenCircuitProbability p l) :=
  rsw_gluing_inequalities p l hl

theorem theorem_11_70 (p : I) (l : ℕ) (hl : 1 ≤ l) :
    rswSquareCrossingProbability p l ^ 12 *
        (1 - Real.sqrt (1 - rswSquareCrossingProbability p l)) ^ 48 ≤
      rswAnnulusOpenCircuitProbability p l :=
  rswAnnulusOpenCircuitProbability_ge p l hl

theorem theorem_11_115 {pₕ pᵥ : I} (hpₕ : (pₕ : ℝ) < 1) (hpᵥ : (pᵥ : ℝ) < 1) :
    (inhomogeneousSquareCriticalPolynomial pₕ pᵥ ≤ 1 →
        inhomogeneousSquareTheta pₕ pᵥ = 0) ∧
      (1 < inhomogeneousSquareCriticalPolynomial pₕ pᵥ →
        0 < inhomogeneousSquareTheta pₕ pᵥ) :=
  inhomogeneousSquare_criticalSurface hpₕ hpᵥ

theorem theorem_11_116 {pₕ pᵥ pₑ : I}
    (hpₕ : (pₕ : ℝ) < 1) (hpᵥ : (pᵥ : ℝ) < 1) (hpₑ : (pₑ : ℝ) < 1) :
    (inhomogeneousTriangularCriticalPolynomial pₕ pᵥ pₑ ≤ 1 →
        inhomogeneousTriangularTheta pₕ pᵥ pₑ = 0) ∧
      (1 < inhomogeneousTriangularCriticalPolynomial pₕ pᵥ pₑ →
        0 < inhomogeneousTriangularTheta pₕ pᵥ pₑ) :=
  inhomogeneousTriangular_criticalSurface hpₕ hpᵥ hpₑ

end Review.Chapter11
