import Percolation.Planar.Inhomogeneous

namespace Review.Chapter11

open Percolation Filter MeasureTheory
open scoped ENNReal Real unitInterval

/-- Grimmett, Theorem 11.11: the bond critical probability of ℤ² equals ½. -/
theorem theorem_11_11 : cubicCriticalProbability 2 = (1 / 2 : ℝ) := by
  sorry

/-- Grimmett, Lemma 11.12: θ(½)=0 (whence p_c ≥ ½). -/
theorem lemma_11_12 : theta 2 squareHalfDensity = 0 := by
  sorry

/-- Grimmett, Lemma 11.21: a left–right crossing of the rectangle [0,n+1]×[0,n]
has probability exactly ½ at density ½. -/
theorem lemma_11_21 (n : ℕ) :
    (bernoulliBondMeasure 2 squareHalfDensity).real
        (grimmettRectangleCrossingEvent n) = 1 / 2 := by
  sorry

/-- Grimmett, Lemma 11.22: for p>½ there are positive β,γ with
P_p(M_{n+1} ≤ βn) ≤ e^{−γn} for all n≥1, where M_{n+1} is the maximal number of
edge-disjoint open left–right crossings of the *literal* box [0,n+1]×[0,n]. -/
theorem lemma_11_22 {p : I} (hp : (1 / 2 : ℝ) < p) :
    ∃ β γ : ℝ, 0 < β ∧ 0 < γ ∧ ∀ n : ℕ, 1 ≤ n →
      (bernoulliBondMeasure 2 p).real
          {ω | (maxEdgeDisjointGrimmettRectangleCrossings n ω : ℝ) ≤ β * n} ≤
        Real.exp (-γ * n) := by
  sorry

/-- Grimmett, Theorem 11.24: for 1/2 < p < 1 the truncated two-point logarithmic
rate converges, finite-cluster correlation length is one half its complementary
subcritical counterpart, and that correlation length is positive and finite. -/
theorem theorem_11_24 {p : I} (hpHalf : (1 / 2 : ℝ) < p) (hpOne : (p : ℝ) < 1) :
    Tendsto (fun n : ℕ ↦ -Real.log (truncatedTwoPointConnectivity p n) / n)
        atTop (nhds (truncatedConnectivityDecayRate p)) ∧
      finiteCorrelationLength p = (2 : ℝ≥0∞)⁻¹ * correlationLength 2 (σ p) ∧
      0 < finiteCorrelationLength p ∧ finiteCorrelationLength p < ⊤ := by
  sorry

/-- Grimmett, Lemma 11.27 (source form, k ≥ 1): the finite-tube log rate exists,
gives the exponential upper bound, is strictly positive and finite (bounded by −log p),
decreases in the tube width, and converges to the unrestricted axis rate. -/
theorem lemma_11_27 {p : I} (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    {k : ℕ} (hk : 1 ≤ k) :
    Tendsto (fun n : ℕ ↦ -Real.log (tubeTwoPointConnectivity p k n) / n)
        atTop (nhds (tubeConnectivityDecayRate p k)) ∧
      (∀ n : ℕ, 1 ≤ n → tubeTwoPointConnectivity p k n ≤
        Real.exp (-(n : ℝ) * tubeConnectivityDecayRate p k)) ∧
      0 < tubeConnectivityDecayRate p k ∧
      tubeConnectivityDecayRate p k ≤ -Real.log (p : ℝ) ∧
      Antitone (tubeConnectivityDecayRate p) ∧
      Tendsto (tubeConnectivityDecayRate p) atTop
        (nhds (axisConnectivityDecayRate 2 p)) := by
  sorry

/-- Grimmett, Lemma 11.75: the three FKG gluing inequalities (11.76)–(11.78). -/
theorem lemma_11_75 (p : I) (l : ℕ) (hl : 1 ≤ l) :
    (rswSquareCrossingProbability p l *
          rswThreeHalvesCrossingProbability p l ^ 2 ≤
        rswRectangleCrossingProbability p 2 l) ∧
      (rswSquareCrossingProbability p l *
          rswRectangleCrossingProbability p 2 l ^ 2 ≤
        rswRectangleCrossingProbability p 3 l) ∧
      (rswRectangleCrossingProbability p 3 l ^ 4 ≤
        rswAnnulusOpenCircuitProbability p l) := by
  sorry

/-- Grimmett, Theorem 11.70 (RSW, eq. 11.71): if the square-crossing probability is r,
the annular open-circuit probability is at least r^12 (1 − √(1 − r))^48. -/
theorem theorem_11_70 (p : I) (l : ℕ) (hl : 1 ≤ l) :
    rswSquareCrossingProbability p l ^ 12 *
        (1 - Real.sqrt (1 - rswSquareCrossingProbability p l)) ^ 48 ≤
      rswAnnulusOpenCircuitProbability p l := by
  sorry

/-- Grimmett, Theorem 11.115: for p_h,p_v<1, rooted inhomogeneous square percolation
has θ=0 iff p_h+p_v ≤ 1 and θ>0 iff p_h+p_v > 1. -/
theorem theorem_11_115 {pₕ pᵥ : I} (hpₕ : (pₕ : ℝ) < 1) (hpᵥ : (pᵥ : ℝ) < 1) :
    (inhomogeneousSquareCriticalPolynomial pₕ pᵥ ≤ 1 →
        inhomogeneousSquareTheta pₕ pᵥ = 0) ∧
      (1 < inhomogeneousSquareCriticalPolynomial pₕ pᵥ →
        0 < inhomogeneousSquareTheta pₕ pᵥ) := by
  sorry

/-- Grimmett, Theorem 11.116: for p_h,p_v,p_d<1, rooted inhomogeneous triangular
percolation has θ=0 iff p_h+p_v+p_d−p_h p_v p_d ≤ 1 and θ>0 iff it exceeds 1. -/
theorem theorem_11_116 {pₕ pᵥ pₑ : I}
    (hpₕ : (pₕ : ℝ) < 1) (hpᵥ : (pᵥ : ℝ) < 1) (hpₑ : (pₑ : ℝ) < 1) :
    (inhomogeneousTriangularCriticalPolynomial pₕ pᵥ pₑ ≤ 1 →
        inhomogeneousTriangularTheta pₕ pᵥ pₑ = 0) ∧
      (1 < inhomogeneousTriangularCriticalPolynomial pₕ pᵥ pₑ →
        0 < inhomogeneousTriangularTheta pₕ pᵥ pₑ) := by
  sorry

end Review.Chapter11
