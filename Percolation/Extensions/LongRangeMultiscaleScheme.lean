import Percolation.Extensions.LongRangeMultiscale

/-!
# Variable-scale schemes and probability induction

The scale data are bundled so that the quantifier order in Theorem 12.8 remains auditable.
No probabilistic conclusion is stored in the structure: every bound is proved from the literal
one-step recursion.
-/

namespace Percolation

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology unitInterval

/-- A sequence of interval lengths and retained component targets. -/
structure LongRangeMultiscaleScheme where
  length : ℕ → ℕ
  target : ℕ → ℕ
  arity : ℕ → ℕ
  quota : ℕ → ℕ
  length_succ : ∀ k, length (k + 1) = length k * arity k
  target_succ : ∀ k, target (k + 1) = quota k * target k
  length_pos : ∀ k, 0 < length k
  target_pos : ∀ k, 0 < target k
  arity_pos : ∀ k, 0 < arity k
  quota_pos : ∀ k, 0 < quota k
  quota_le_arity : ∀ k, quota k ≤ arity k

namespace LongRangeMultiscaleScheme

/-- The large-component event at scale `k`. -/
def goodEvent (S : LongRangeMultiscaleScheme) (k : ℕ) (z : ℤ) :
    Set LongRangeConfiguration :=
  longRangeIntervalLargeComponentEvent (S.length k) (S.target k) z

theorem measurableSet_goodEvent (S : LongRangeMultiscaleScheme) (k : ℕ) (z : ℤ) :
    MeasurableSet (S.goodEvent k z) :=
  measurableSet_longRangeIntervalLargeComponentEvent _ _ _

/-- A numerical error profile is admissible when it dominates the exact renormalization
recursion at every level. -/
def ErrorAdmissible {β α : ℝ} (S : LongRangeMultiscaleScheme)
    (ε : ℕ → ℝ) : Prop :=
  (∀ k, 0 ≤ ε k) ∧ ∀ k,
    (2 : ℝ) ^ S.arity k * ε k ^ (S.arity k - S.quota k + 1) +
      (S.arity k : ℝ) ^ 2 *
        Real.exp (-β /
          ((S.length k * S.arity k : ℕ) : ℝ) ^ α) ^ (S.target k ^ 2) ≤
      ε (k + 1)

/-- Induction of uniform block-error bounds from a numerical admissible profile. -/
theorem measureReal_goodEvent_compl_le
    {β α : ℝ} (F : LongRangePowerLawFamily β α) (q : I)
    (hβ : 0 < β) (hα : 0 < α)
    (hq : longRangePowerLawTailProbability β α 1 ≤ q)
    (S : LongRangeMultiscaleScheme) (ε : ℕ → ℝ)
    (hε : S.ErrorAdmissible (β := β) (α := α) ε)
    (hzero : ∀ z : ℤ, (longRangeMeasure (F q)).real
      (S.goodEvent 0 z)ᶜ ≤ ε 0) :
    ∀ k z, (longRangeMeasure (F q)).real (S.goodEvent k z)ᶜ ≤ ε k := by
  intro k
  induction k with
  | zero => exact hzero
  | succ k ih =>
      intro z
      rw [goodEvent, S.length_succ k, S.target_succ k]
      exact (longRangeMeasure_real_intervalLargeComponent_mul_compl_le
        F q hβ hα hq (S.length_pos k) (S.arity_pos k)
        (S.quota_pos k) (S.target_pos k) (S.quota_le_arity k)
        (hε.1 k) (fun w ↦ ih w) z).trans (hε.2 k)

/-- If the error profile tends to zero, good-block probabilities tend to one uniformly in the
block index. -/
theorem tendsto_measureReal_goodEvent
    {β α : ℝ} (F : LongRangePowerLawFamily β α) (q : I)
    (hβ : 0 < β) (hα : 0 < α)
    (hq : longRangePowerLawTailProbability β α 1 ≤ q)
    (S : LongRangeMultiscaleScheme) (ε : ℕ → ℝ)
    (hε : S.ErrorAdmissible (β := β) (α := α) ε)
    (hzero : ∀ z : ℤ, (longRangeMeasure (F q)).real
      (S.goodEvent 0 z)ᶜ ≤ ε 0)
    (hεlim : Tendsto ε atTop (𝓝 0)) (z : ℤ) :
    Tendsto (fun k ↦ (longRangeMeasure (F q)).real (S.goodEvent k z))
      atTop (𝓝 1) := by
  have hcomp (k : ℕ) : (longRangeMeasure (F q)).real (S.goodEvent k z) =
      1 - (longRangeMeasure (F q)).real (S.goodEvent k z)ᶜ := by
    have hc := measureReal_compl (μ := longRangeMeasure (F q))
      (S.measurableSet_goodEvent k z)
    rw [measureReal_univ_eq_one] at hc
    linarith
  have hsqueeze : Tendsto (fun k ↦
      (longRangeMeasure (F q)).real (S.goodEvent k z)ᶜ) atTop (𝓝 0) := by
    apply squeeze_zero
    · exact fun k ↦ measureReal_nonneg
    · exact fun k ↦ S.measureReal_goodEvent_compl_le
        F q hβ hα hq ε hε hzero k z
    · exact hεlim
  have ht : Tendsto (fun k : ℕ ↦ (1 : ℝ) -
      (longRangeMeasure (F q)).real (S.goodEvent k z)ᶜ) atTop (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub hsqueeze
  simpa only [hcomp, sub_zero] using ht

end LongRangeMultiscaleScheme

end Percolation
