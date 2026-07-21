import Percolation.Extensions.LongRangeQuadraticScheme

/-!
# Error profile for the quadratic multiscale scheme
-/

namespace Percolation

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology unitInterval

/-- Target error `exp(-4 (N+k)^2)`. -/
noncomputable def longRangeQuadraticError (N k : ℕ) : ℝ :=
  Real.exp (-4 * (longRangeQuadraticArity N k : ℝ))

theorem longRangeQuadraticError_pos (N k : ℕ) :
    0 < longRangeQuadraticError N k := Real.exp_pos _

theorem longRangeQuadraticError_nonneg (N k : ℕ) :
    0 ≤ longRangeQuadraticError N k := (longRangeQuadraticError_pos N k).le

theorem tendsto_longRangeQuadraticError_zero (N : ℕ) :
    Tendsto (longRangeQuadraticError N) atTop (𝓝 0) := by
  apply Real.tendsto_exp_atBot.comp
  have hsq : Tendsto (fun k : ℕ ↦ ((N + k : ℕ) : ℝ) ^ 2) atTop atTop := by
    have hlin : Tendsto (fun k : ℕ ↦ ((N + k : ℕ) : ℝ)) atTop atTop := by
      convert (tendsto_natCast_atTop_atTop (R := ℝ)).comp
        (tendsto_add_atTop_nat N) using 1
      ext k
      simp [Function.comp_apply, Nat.add_comm]
    exact (tendsto_pow_atTop (α := ℝ) (by norm_num : (2 : ℕ) ≠ 0)).comp hlin
  have hneg : Tendsto (fun k : ℕ ↦ -4 * ((N + k : ℕ) : ℝ) ^ 2)
      atTop atBot :=
    (tendsto_const_mul_atBot_of_neg (by norm_num)).2 hsq
  simpa [longRangeQuadraticError, longRangeQuadraticArity] using hneg

/-- The independent-child contribution consumes at most half of the next error budget. -/
theorem quadratic_child_error_le_half
    {N : ℕ} (hN : 4 ≤ N) (k : ℕ) :
    (2 : ℝ) ^ longRangeQuadraticArity N k *
        longRangeQuadraticError N k ^
          (longRangeQuadraticArity N k - longRangeQuadraticQuota N k + 1) ≤
      (1 / 2 : ℝ) * longRangeQuadraticError N (k + 1) := by
  let n : ℕ := N + k
  have hn : 4 ≤ n := by omega
  have haPos : 0 < longRangeQuadraticArity N k :=
    longRangeQuadraticArity_pos (by omega) k
  have hpowCount : longRangeQuadraticArity N k -
      longRangeQuadraticQuota N k + 1 = 2 := by
    unfold longRangeQuadraticQuota
    omega
  rw [hpowCount]
  have htwoexp : (2 : ℝ) ≤ Real.exp 1 := by
    convert Real.add_one_le_exp 1 using 1 <;> norm_num
  have htwoPow : (2 : ℝ) ^ longRangeQuadraticArity N k ≤
      Real.exp (longRangeQuadraticArity N k : ℝ) := by
    calc
      (2 : ℝ) ^ longRangeQuadraticArity N k ≤
          Real.exp 1 ^ longRangeQuadraticArity N k := by
        gcongr
      _ = Real.exp (longRangeQuadraticArity N k : ℝ) := by
        rw [← Real.exp_nat_mul]
        simp
  have hmain : (2 : ℝ) ^ longRangeQuadraticArity N k *
      longRangeQuadraticError N k ^ 2 ≤
      Real.exp (-1) * longRangeQuadraticError N (k + 1) := by
    calc
      (2 : ℝ) ^ longRangeQuadraticArity N k *
          longRangeQuadraticError N k ^ 2 ≤
          Real.exp (longRangeQuadraticArity N k : ℝ) *
            longRangeQuadraticError N k ^ 2 := by
        exact mul_le_mul_of_nonneg_right htwoPow
          (sq_nonneg (longRangeQuadraticError N k))
      _ = Real.exp (-7 * (n : ℝ) ^ 2) := by
        simp only [longRangeQuadraticError, longRangeQuadraticArity,
          Nat.cast_pow, Nat.cast_add]
        rw [← Real.exp_nat_mul]
        rw [← Real.exp_add]
        congr 1
        simp only [n]
        push_cast
        ring
      _ ≤ Real.exp (-1 - 4 * ((n + 1 : ℕ) : ℝ) ^ 2) := by
        rw [Real.exp_le_exp]
        push_cast
        have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
        nlinarith [mul_nonneg (show (0 : ℝ) ≤ n by positivity)
          (sub_nonneg.mpr hnR)]
      _ = Real.exp (-1) * longRangeQuadraticError N (k + 1) := by
        rw [longRangeQuadraticError]
        rw [← Real.exp_add]
        congr 1
        simp only [longRangeQuadraticArity, n,
          Nat.cast_pow, Nat.cast_add, Nat.cast_one]
        ring
  have hexpNegOne : Real.exp (-1) ≤ (1 / 2 : ℝ) := by
    rw [Real.exp_neg]
    simpa [one_div] using one_div_le_one_div_of_le (by norm_num) htwoexp
  exact hmain.trans (mul_le_mul_of_nonneg_right hexpNegOne
    (longRangeQuadraticError_nonneg N (k + 1)))

/-- The remaining half-budget condition for cross bonds. -/
def QuadraticCrossControlled (β α : ℝ) (base N : ℕ) : Prop :=
  ∀ k,
    (longRangeQuadraticArity N k : ℝ) ^ 2 *
        Real.exp (-β /
          ((longRangeQuadraticLength base N k *
            longRangeQuadraticArity N k : ℕ) : ℝ) ^ α) ^
          (longRangeQuadraticTarget base N k ^ 2) ≤
      (1 / 2 : ℝ) * longRangeQuadraticError N (k + 1)

/-- A convenient logarithmic sufficient condition for the cross-bond half-budget. -/
theorem quadraticCrossControlled_of_exponent
    {β α : ℝ} {base N : ℕ}
    (hlarge : ∀ k,
      (8 : ℝ) * (N + k + 1 : ℕ) ^ 2 ≤
        β * (longRangeQuadraticTarget base N k : ℝ) ^ 2 /
          (((longRangeQuadraticLength base N k *
            longRangeQuadraticArity N k : ℕ) : ℝ) ^ α)) :
    QuadraticCrossControlled β α base N := by
  intro k
  let n : ℕ := N + k
  let a : ℕ := longRangeQuadraticArity N k
  let L : ℕ := longRangeQuadraticLength base N k
  let M : ℕ := longRangeQuadraticTarget base N k
  have ha : (a : ℝ) ≤ Real.exp (a : ℝ) := by
    calc
      (a : ℝ) ≤ (a : ℝ) + 1 := by linarith
      _ ≤ Real.exp (a : ℝ) := Real.add_one_le_exp _
  have ha2 : (a : ℝ) ^ 2 ≤ Real.exp (2 * (a : ℝ)) := by
    calc
      (a : ℝ) ^ 2 ≤ Real.exp (a : ℝ) ^ 2 := by gcongr
      _ = Real.exp (2 * (a : ℝ)) := by
        rw [← Real.exp_nat_mul]
        congr 1
  have hrewrite :
      Real.exp (-β / (((L * a : ℕ) : ℝ) ^ α)) ^ (M ^ 2) =
        Real.exp (-β * (M : ℝ) ^ 2 /
          (((L * a : ℕ) : ℝ) ^ α)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hbudget :
      β * (M : ℝ) ^ 2 / (((L * a : ℕ) : ℝ) ^ α) ≥
        8 * (n + 1 : ℕ) ^ 2 := by
    simpa only [L, a, M, n, Nat.cast_pow] using hlarge k
  have haEq : a = n ^ 2 := by
    simp [a, n, longRangeQuadraticArity]
  calc
    (a : ℝ) ^ 2 *
        Real.exp (-β / (((L * a : ℕ) : ℝ) ^ α)) ^ (M ^ 2) ≤
        Real.exp (2 * (a : ℝ)) *
          Real.exp (-β * (M : ℝ) ^ 2 / (((L * a : ℕ) : ℝ) ^ α)) := by
      rw [hrewrite]
      exact mul_le_mul_of_nonneg_right ha2 (Real.exp_pos _).le
    _ = Real.exp (2 * (a : ℝ) -
        β * (M : ℝ) ^ 2 / (((L * a : ℕ) : ℝ) ^ α)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-1 - 4 * ((n + 1 : ℕ) : ℝ) ^ 2) := by
      rw [Real.exp_le_exp]
      have hn : (0 : ℝ) ≤ n := by positivity
      rw [haEq] at hbudget ⊢
      push_cast at hbudget ⊢
      nlinarith [sq_nonneg (n : ℝ)]
    _ = Real.exp (-1) * longRangeQuadraticError N (k + 1) := by
      rw [longRangeQuadraticError, ← Real.exp_add]
      congr 1
      simp only [longRangeQuadraticArity, n, Nat.cast_pow, Nat.cast_add,
        Nat.cast_one]
      ring
    _ ≤ (1 / 2 : ℝ) * longRangeQuadraticError N (k + 1) := by
      apply mul_le_mul_of_nonneg_right _ (longRangeQuadraticError_nonneg _ _)
      rw [Real.exp_neg]
      have htwoexp : (2 : ℝ) ≤ Real.exp 1 := by
        convert Real.add_one_le_exp 1 using 1 <;> norm_num
      simpa [one_div] using one_div_le_one_div_of_le (by norm_num) htwoexp

/-- Child and cross half-budgets imply numerical admissibility. -/
theorem quadratic_errorAdmissible
    {β α : ℝ} {base N : ℕ} (hbase : 0 < base) (hN : 4 ≤ N)
    (hcross : QuadraticCrossControlled β α base N) :
    (longRangeQuadraticScheme base N hbase (by omega)).ErrorAdmissible
      (β := β) (α := α) (longRangeQuadraticError N) := by
  constructor
  · exact longRangeQuadraticError_nonneg N
  · intro k
    dsimp [longRangeQuadraticScheme]
    calc
      (2 : ℝ) ^ longRangeQuadraticArity N k *
          longRangeQuadraticError N k ^
            (longRangeQuadraticArity N k - longRangeQuadraticQuota N k + 1) +
          (longRangeQuadraticArity N k : ℝ) ^ 2 *
            Real.exp (-β /
              ((longRangeQuadraticLength base N k *
                longRangeQuadraticArity N k : ℕ) : ℝ) ^ α) ^
              (longRangeQuadraticTarget base N k ^ 2) ≤
          (1 / 2 : ℝ) * longRangeQuadraticError N (k + 1) +
            (1 / 2 : ℝ) * longRangeQuadraticError N (k + 1) :=
        add_le_add (quadratic_child_error_le_half hN k) (hcross k)
      _ = longRangeQuadraticError N (k + 1) := by ring

end Percolation
