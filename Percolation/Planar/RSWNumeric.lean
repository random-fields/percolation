import Percolation.Planar.RSWGluing

/-!
# Numerical core of the RSW theorem

This module performs the exact algebra in Grimmett, Theorem 11.70.  The lowest-crossing input is
the externally sourced Lemma 11.73 declaration.  The three hypotheses are precisely the FKG
gluing inequalities (11.76)--(11.78), kept explicit here so the planar event geometry is audited
separately from the numerical calculation.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval

/-- The numerical conclusion of Grimmett's RSW theorem from Lemmas 11.73 and 11.75. -/
theorem rswAnnulusOpenCircuitProbability_ge_of_gluing
    (p : I) (l : ℕ)
    (h76 : rswSquareCrossingProbability p l *
        rswThreeHalvesCrossingProbability p l ^ 2 ≤
      rswRectangleCrossingProbability p 2 l)
    (h77 : rswSquareCrossingProbability p l *
        rswRectangleCrossingProbability p 2 l ^ 2 ≤
      rswRectangleCrossingProbability p 3 l)
    (h78 : rswRectangleCrossingProbability p 3 l ^ 4 ≤
      rswAnnulusOpenCircuitProbability p l) :
    rswSquareCrossingProbability p l ^ 12 *
        (1 - Real.sqrt (1 - rswSquareCrossingProbability p l)) ^ 48 ≤
      rswAnnulusOpenCircuitProbability p l := by
  let r := rswSquareCrossingProbability p l
  let s := rswThreeHalvesCrossingProbability p l
  let a := rswRectangleCrossingProbability p 2 l
  let b := rswRectangleCrossingProbability p 3 l
  let u := 1 - Real.sqrt (1 - r)
  have hr0 : 0 ≤ r := measureReal_nonneg
  have hr1 : r ≤ 1 := measureReal_le_one
  have hs0 : 0 ≤ s := measureReal_nonneg
  have ha0 : 0 ≤ a := measureReal_nonneg
  have hb0 : 0 ≤ b := measureReal_nonneg
  have hu0 : 0 ≤ u := by
    dsimp [u]
    exact sub_nonneg.mpr ((Real.sqrt_le_one).2 (by linarith))
  have h73 : u ^ 3 ≤ s := by
    simpa [u, r, s] using rswThreeHalvesCrossingProbability_ge p l
  have hA : r * (u ^ 3) ^ 2 ≤ a := by
    calc
      r * (u ^ 3) ^ 2 ≤ r * s ^ 2 := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (pow_nonneg hu0 3) h73 2) hr0
      _ ≤ a := by simpa [r, s, a] using h76
  have hB : r * (r * (u ^ 3) ^ 2) ^ 2 ≤ b := by
    calc
      r * (r * (u ^ 3) ^ 2) ^ 2 ≤ r * a ^ 2 := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀
            (mul_nonneg hr0 (pow_nonneg (pow_nonneg hu0 3) 2)) hA 2) hr0
      _ ≤ b := by simpa [r, a, b] using h77
  calc
    rswSquareCrossingProbability p l ^ 12 *
        (1 - Real.sqrt (1 - rswSquareCrossingProbability p l)) ^ 48 =
        (r * (r * (u ^ 3) ^ 2) ^ 2) ^ 4 := by
      dsimp [r, u]
      ring
    _ ≤ b ^ 4 :=
      pow_le_pow_left₀
        (mul_nonneg hr0
          (pow_nonneg (mul_nonneg hr0 (pow_nonneg (pow_nonneg hu0 3) 2)) 2)) hB 4
    _ ≤ rswAnnulusOpenCircuitProbability p l := by
      simpa [b] using h78

/-- **Grimmett, Theorem 11.70 (RSW).**  A square-crossing probability `r` gives the
explicit annular-circuit lower bound from equation (11.71). -/
theorem rswAnnulusOpenCircuitProbability_ge
    (p : I) (l : ℕ) (hl : 1 ≤ l) :
    rswSquareCrossingProbability p l ^ 12 *
        (1 - Real.sqrt (1 - rswSquareCrossingProbability p l)) ^ 48 ≤
      rswAnnulusOpenCircuitProbability p l := by
  apply rswAnnulusOpenCircuitProbability_ge_of_gluing p l
  · exact rswRectangleCrossingProbability_two_ge p l hl
  · exact rswRectangleCrossingProbability_three_ge p l hl
  · exact rswAnnulusOpenCircuitProbability_ge_rectanglePowFour p l hl

end Percolation
