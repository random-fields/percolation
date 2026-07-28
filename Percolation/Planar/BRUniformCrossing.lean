import Percolation.Planar.BRCrossingExtension
import Percolation.Planar.BRSourceXGluing
import Percolation.Planar.RSWHalf
import Percolation.Planar.SquareThresholdUniform

/-!
# Uniform critical rectangle crossings from conditional BR freshness

At `m = 4n`, the conditional Bollobás--Riordan extension estimate and the reflected source-event
gluing estimate give a lower bound for the `3(2n) × 2(2n)` crossing probability.  Thus one
freshness assumption at each half-scale gives the missing three-halves input at every even scale.
The two existing RSW gluing inequalities then produce a uniform aspect-three crossing bound.

For audit purposes, the former full-contact-to-fresh implication is retained below only as a
conditional algebraic scaffold.  It is false without a stronger selector and is not proposed as
a dischargeable geometric lemma.  The source-probability theorem isolates the sound rewiring
seam: a future direct fresh-cover or half-probability estimate can supply that premise without
changing the recurrence or the downstream RSW algebra.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval

noncomputable section

/-- Sound probability-algebra seam for the even-scale BR recurrence.  The premise is exactly the
assembled source-event estimate that a correct direct fresh-cover or half-probability theorem
must provide. -/
theorem brThreeHalvesCrossingProbability_even_ge_of_sourceX_lower
    (p : I) (n : ℕ)
    (hsource : rswSquareCrossingProbability p (2 * n) *
        rswSquareCrossingProbability p n / 2 ≤
      (bernoulliBondMeasure 2 p).real (brSourceXEvent (4 * n) n)) :
    rswSquareCrossingProbability p (2 * n) ^ 2 *
          rswSquareCrossingProbability p n ^ 3 / 4 ≤
      rswThreeHalvesCrossingProbability p (2 * n) := by
  let μ := bernoulliBondMeasure 2 p
  let a := rswSquareCrossingProbability p (2 * n)
  let b := rswSquareCrossingProbability p n
  let x := μ.real (brSourceXEvent (4 * n) n)
  have hx : a * b / 2 ≤ x := by simpa [a, b, x, μ] using hsource
  have hglue : b * x ^ 2 ≤ rswThreeHalvesCrossingProbability p (2 * n) := by
    have h := brSourceXGluing_probability_le_unionCrossing p
      (m := 4 * n) (n := n) (by omega)
    have hwidth : 2 * (4 * n) - 2 * n = 3 * (2 * n) := by omega
    simpa [b, x, μ, rswThreeHalvesCrossingProbability, rswThreeHalvesCrossingEvent,
      hwidth] using h
  have ha0 : 0 ≤ a := measureReal_nonneg
  have hb0 : 0 ≤ b := measureReal_nonneg
  have hab0 : 0 ≤ a * b / 2 := div_nonneg (mul_nonneg ha0 hb0) (by norm_num)
  calc
    rswSquareCrossingProbability p (2 * n) ^ 2 *
          rswSquareCrossingProbability p n ^ 3 / 4 =
        b * (a * b / 2) ^ 2 := by
      dsimp [a, b]
      ring
    _ ≤ b * x ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hab0 hx 2) hb0
    _ ≤ rswThreeHalvesCrossingProbability p (2 * n) := hglue

/-- Conditional compatibility wrapper for the former contact-to-fresh scaffold.

The hypothesis is deliberately not advertised as a future geometry target: the corresponding
unrestricted selector claim has a finite counterexample.  The theorem remains useful for
auditing the already completed probability algebra while the source-faithful direct half estimate
is constructed. -/
theorem brThreeHalvesCrossingProbability_even_ge_of_contact_fresh
    (p : I) (n : ℕ) (hn : 0 < n)
    (hfresh : ∀ (R : Finset (BRLeftmostDualVertex n))
        (_hgood : R ∈ brGoodReachableFaceFiberIndices n)
        (hR : BRAdmissibleSeparatingFiber n R),
      brLowerContactEvent (4 * n) hn hR ⊆
        brLowerFreshExtensionEvent (4 * n) R hn hR) :
    rswSquareCrossingProbability p (2 * n) ^ 2 *
          rswSquareCrossingProbability p n ^ 3 / 4 ≤
      rswThreeHalvesCrossingProbability p (2 * n) := by
  apply brThreeHalvesCrossingProbability_even_ge_of_sourceX_lower
  have h := brLemmaSix_probability_of_contact_fresh p (4 * n) n (by omega) hn hfresh
  have hwidth : 4 * n = 2 * (2 * n) := by omega
  simpa [rswSquareCrossingProbability, rswSquareCrossingEvent,
    rswRectangleCrossingEvent, hwidth] using h

/-- Explicit lower bound obtained by one BR recurrence followed by the two RSW rectangle gluings.
-/
noncomputable def brAspectThreeCrossingLowerBound : ℝ :=
  (1 / 16 : ℝ) ^ 23 / 256

theorem brAspectThreeCrossingLowerBound_pos : 0 < brAspectThreeCrossingLowerBound := by
  unfold brAspectThreeCrossingLowerBound
  positivity

/-- Uniform aspect-three crossing bound under the explicit former contact-to-fresh scaffold.

This implication is retained as a conditional input for algebra auditing, not claimed as a valid
selector theorem.  It is restricted to the only instances read by the calculation: `m = 4n` and
`n ≥ 3`. -/
theorem brAspectThreeCrossingLowerBound_le_expandedCriticalAnnulusScale_of_contact_fresh
    (hfresh : ∀ (n : ℕ) (hn : 0 < n), 3 ≤ n →
      ∀ (R : Finset (BRLeftmostDualVertex n))
        (_hgood : R ∈ brGoodReachableFaceFiberIndices n)
        (hR : BRAdmissibleSeparatingFiber n R),
          brLowerContactEvent (4 * n) hn hR ⊆
            brLowerFreshExtensionEvent (4 * n) R hn hR)
    (k : ℕ) :
    brAspectThreeCrossingLowerBound ≤
      rswRectangleCrossingProbability squareHalfDensity 3
        (expandedCriticalAnnulusScale k) := by
  let c₀ : ℝ := 1 / 16
  let l := expandedCriticalAnnulusScale k
  let n := 2 * 4 ^ (k + 1)
  have hl16 : 16 ≤ l := by
    simpa [l] using expandedCriticalAnnulusScale_ge_sixteen k
  have hln : l = 2 * n := by
    dsimp [l, n, expandedCriticalAnnulusScale]
    rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
    ring
  have hn3 : 3 ≤ n := by omega
  have hn : 0 < n := by omega
  have hl3 : 3 ≤ l := by omega
  have hl1 : 1 ≤ l := by omega
  have hc₀0 : 0 ≤ c₀ := by norm_num [c₀]
  have hsN : c₀ ≤ rswSquareCrossingProbability squareHalfDensity n := by
    simpa [c₀] using one_sixteenth_le_rswSquareCrossingProbability_half n hn3
  have hsL : c₀ ≤ rswSquareCrossingProbability squareHalfDensity l := by
    simpa [c₀] using one_sixteenth_le_rswSquareCrossingProbability_half l hl3
  have hthreeRecurrence :
      rswSquareCrossingProbability squareHalfDensity l ^ 2 *
            rswSquareCrossingProbability squareHalfDensity n ^ 3 / 4 ≤
        rswThreeHalvesCrossingProbability squareHalfDensity l := by
    simpa [hln] using
      brThreeHalvesCrossingProbability_even_ge_of_contact_fresh
        squareHalfDensity n hn (hfresh n hn hn3)
  let t : ℝ := c₀ ^ 5 / 4
  have ht0 : 0 ≤ t := by
    dsimp [t]
    positivity
  have ht : t ≤ rswThreeHalvesCrossingProbability squareHalfDensity l := by
    have hpowTwo : c₀ ^ 2 ≤
        rswSquareCrossingProbability squareHalfDensity l ^ 2 :=
      pow_le_pow_left₀ hc₀0 hsL 2
    have hpowThree : c₀ ^ 3 ≤
        rswSquareCrossingProbability squareHalfDensity n ^ 3 :=
      pow_le_pow_left₀ hc₀0 hsN 3
    have hmul : c₀ ^ 2 * c₀ ^ 3 ≤
        rswSquareCrossingProbability squareHalfDensity l ^ 2 *
          rswSquareCrossingProbability squareHalfDensity n ^ 3 :=
      mul_le_mul hpowTwo hpowThree (pow_nonneg hc₀0 3)
        (pow_nonneg measureReal_nonneg 2)
    calc
      t = (c₀ ^ 2 * c₀ ^ 3) / 4 := by
        dsimp [t]
        ring
      _ ≤ (rswSquareCrossingProbability squareHalfDensity l ^ 2 *
            rswSquareCrossingProbability squareHalfDensity n ^ 3) / 4 :=
        div_le_div_of_nonneg_right hmul (by norm_num)
      _ ≤ rswThreeHalvesCrossingProbability squareHalfDensity l := hthreeRecurrence
  let r₂ : ℝ := c₀ * t ^ 2
  have hr₂0 : 0 ≤ r₂ := mul_nonneg hc₀0 (pow_nonneg ht0 2)
  have hr₂ : r₂ ≤ rswRectangleCrossingProbability squareHalfDensity 2 l := by
    have htPow : t ^ 2 ≤ rswThreeHalvesCrossingProbability squareHalfDensity l ^ 2 :=
      pow_le_pow_left₀ ht0 ht 2
    calc
      r₂ ≤ rswSquareCrossingProbability squareHalfDensity l *
          rswThreeHalvesCrossingProbability squareHalfDensity l ^ 2 := by
        exact mul_le_mul hsL htPow (pow_nonneg ht0 2) measureReal_nonneg
      _ ≤ rswRectangleCrossingProbability squareHalfDensity 2 l :=
        rswRectangleCrossingProbability_two_ge squareHalfDensity l hl1
  have hr₂Pow : r₂ ^ 2 ≤ rswRectangleCrossingProbability squareHalfDensity 2 l ^ 2 :=
    pow_le_pow_left₀ hr₂0 hr₂ 2
  calc
    brAspectThreeCrossingLowerBound = c₀ * r₂ ^ 2 := by
      dsimp [brAspectThreeCrossingLowerBound, c₀, r₂, t]
      ring
    _ ≤ rswSquareCrossingProbability squareHalfDensity l *
        rswRectangleCrossingProbability squareHalfDensity 2 l ^ 2 := by
      exact mul_le_mul hsL hr₂Pow (pow_nonneg hr₂0 2) measureReal_nonneg
    _ ≤ rswRectangleCrossingProbability squareHalfDensity 3 l :=
      rswRectangleCrossingProbability_three_ge squareHalfDensity l hl1
    _ = rswRectangleCrossingProbability squareHalfDensity 3
        (expandedCriticalAnnulusScale k) := by
      rfl

/-- Algebraically conditional self-dual nonpercolation under the former contact-to-fresh
scaffold.  A source-faithful theorem should instead be rewired through a direct fresh-cover or
half-probability estimate. -/
theorem theta_two_half_eq_zero_of_br_contact_fresh
    (hfresh : ∀ (n : ℕ) (hn : 0 < n), 3 ≤ n →
      ∀ (R : Finset (BRLeftmostDualVertex n))
        (_hgood : R ∈ brGoodReachableFaceFiberIndices n)
        (hR : BRAdmissibleSeparatingFiber n R),
          brLowerContactEvent (4 * n) hn hR ⊆
            brLowerFreshExtensionEvent (4 * n) R hn hR) :
    theta 2 squareHalfDensity = 0 := by
  apply theta_two_half_eq_zero_of_uniform_rswRectangleCrossingProbability
    brAspectThreeCrossingLowerBound_pos
  exact fun k ↦
    brAspectThreeCrossingLowerBound_le_expandedCriticalAnnulusScale_of_contact_fresh hfresh k

end

end Percolation
