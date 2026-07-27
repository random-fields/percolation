import Mathlib.Probability.Moments.Variance

/-!
# Variance bounds for finite-range random fields

The Chapter 7 box-density argument approximates the infinite-cluster indicator by a finite
cylinder.  Translates of that cylinder have covariance zero outside a uniformly bounded
neighborhood.  This file isolates the resulting deterministic covariance-sum estimate.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- A finite average has variance at most `D / |s|` when each summand can have nonzero
covariance with at most `D` indices and every covariance is at most one. -/
theorem variance_finset_average_le_of_finite_covariance_neighborhood
    {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (s : Finset ι) (hs : s.Nonempty) (X : ι → Ω → ℝ)
    (hX : ∀ i ∈ s, MemLp (X i) 2 μ)
    (N : ι → Finset ι) (D : ℕ)
    (hNcard : ∀ i ∈ s, (N i).card ≤ D)
    (hcovZero : ∀ i ∈ s, ∀ j ∈ s, j ∉ N i → cov[X i, X j; μ] = 0)
    (hcovLe : ∀ i ∈ s, ∀ j ∈ s, cov[X i, X j; μ] ≤ 1) :
    Var[fun ω ↦ (∑ i ∈ s, X i ω) / (s.card : ℝ); μ] ≤
      (D : ℝ) / s.card := by
  have hsCard : 0 < s.card := Finset.card_pos.mpr hs
  have hsCardReal : (0 : ℝ) < s.card := by exact_mod_cast hsCard
  have hrow (i : ι) (hi : i ∈ s) :
      (∑ j ∈ s, cov[X i, X j; μ]) ≤ (D : ℝ) := by
    have hEq : (∑ j ∈ s, cov[X i, X j; μ]) =
        ∑ j ∈ s ∩ N i, cov[X i, X j; μ] := by
      symm
      apply Finset.sum_subset (Finset.inter_subset_left)
      intro j hjs hjnot
      apply hcovZero i hi j hjs
      intro hjN
      exact hjnot (Finset.mem_inter.mpr ⟨hjs, hjN⟩)
    rw [hEq]
    calc
      (∑ j ∈ s ∩ N i, cov[X i, X j; μ]) ≤
          ((s ∩ N i).card : ℝ) := by
        simpa using Finset.sum_le_card_nsmul (s ∩ N i)
          (fun j ↦ cov[X i, X j; μ]) (1 : ℝ)
          (fun j hj ↦ hcovLe i hi j (Finset.mem_inter.mp hj).1)
      _ ≤ (N i).card := by
        exact_mod_cast Finset.card_le_card Finset.inter_subset_right
      _ ≤ D := by exact_mod_cast hNcard i hi
  have hvarSum :
      Var[fun ω ↦ ∑ i ∈ s, X i ω; μ] ≤ (s.card : ℝ) * D := by
    rw [variance_fun_sum' hX]
    calc
      (∑ i ∈ s, ∑ j ∈ s, cov[X i, X j; μ]) ≤
          ∑ _i ∈ s, (D : ℝ) :=
        Finset.sum_le_sum fun i hi ↦ hrow i hi
      _ = (s.card : ℝ) * D := by simp
  have hform :
      (fun ω ↦ (∑ i ∈ s, X i ω) / (s.card : ℝ)) =
        fun ω ↦ ((s.card : ℝ)⁻¹) * (∑ i ∈ s, X i ω) := by
    funext ω
    rw [div_eq_inv_mul]
  rw [hform, variance_const_mul]
  calc
    ((s.card : ℝ)⁻¹) ^ 2 * Var[fun ω ↦ ∑ i ∈ s, X i ω; μ] ≤
        ((s.card : ℝ)⁻¹) ^ 2 * ((s.card : ℝ) * D) := by
      exact mul_le_mul_of_nonneg_left hvarSum (sq_nonneg _)
    _ = (D : ℝ) / s.card := by
      field_simp

/-- Chebyshev consequence of the finite-range variance estimate. -/
theorem measure_average_deviation_le_of_finite_covariance_neighborhood
    {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (s : Finset ι) (hs : s.Nonempty) (X : ι → Ω → ℝ)
    (hX : ∀ i ∈ s, MemLp (X i) 2 μ)
    (N : ι → Finset ι) (D : ℕ)
    (hNcard : ∀ i ∈ s, (N i).card ≤ D)
    (hcovZero : ∀ i ∈ s, ∀ j ∈ s, j ∉ N i → cov[X i, X j; μ] = 0)
    (hcovLe : ∀ i ∈ s, ∀ j ∈ s, cov[X i, X j; μ] ≤ 1)
    {ε : ℝ} (hε : 0 < ε) :
    μ {ω | ε ≤
        |(∑ i ∈ s, X i ω) / (s.card : ℝ) -
          ∫ ω, (∑ i ∈ s, X i ω) / (s.card : ℝ) ∂μ|} ≤
      ENNReal.ofReal (((D : ℝ) / s.card) / ε ^ 2) := by
  let A : Ω → ℝ := fun ω ↦ (∑ i ∈ s, X i ω) / (s.card : ℝ)
  have hform : A = fun ω ↦ ((s.card : ℝ)⁻¹) * (∑ i ∈ s, X i ω) := by
    funext ω
    simp [A, div_eq_inv_mul]
  have hA : MemLp A 2 μ := by
    rw [hform]
    have hsum : MemLp (fun ω ↦ ∑ i ∈ s, X i ω) 2 μ := by
      convert memLp_finsetSum' s hX using 1
      ext ω
      simp
    exact hsum.const_mul _
  have hCheb := meas_ge_le_variance_div_sq hA hε
  change μ {ω | ε ≤ |A ω - ∫ ω, A ω ∂μ|} ≤ _
  refine hCheb.trans ?_
  apply ENNReal.ofReal_le_ofReal
  apply div_le_div_of_nonneg_right
  · exact variance_finset_average_le_of_finite_covariance_neighborhood
      μ s hs X hX N D hNcard hcovZero hcovLe
  · exact (sq_nonneg ε)

end Percolation
