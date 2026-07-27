import Percolation.Extensions.LongRangeQuadraticError

/-!
# Choosing parameters for the quadratic long-range scheme

This file turns the qualitative inequality `1 < α < 2` into the uniform numerical
cross-bond estimate required at every level of the Newman--Schulman recursion.
-/

namespace Percolation

open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators Topology unitInterval

/-- Exponential growth uniformly dominates a shifted polynomial sequence. -/
theorem exists_shifted_pow_le_const_mul_geometric
    (shift degree : ℕ) {r : ℝ} (hr : 1 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ,
      (((shift + k : ℕ) : ℝ) ^ degree) ≤ C * r ^ k := by
  have hraw := tendsto_pow_const_div_const_pow_of_one_lt degree hr
  have hshift : Tendsto
      (fun k : ℕ ↦ (((k + shift : ℕ) : ℝ) ^ degree) / r ^ (k + shift))
      atTop (𝓝 0) := hraw.comp (tendsto_add_atTop_nat shift)
  have hr0 : r ≠ 0 := ne_of_gt (lt_trans zero_lt_one hr)
  have hseq : Tendsto
      (fun k : ℕ ↦ (((shift + k : ℕ) : ℝ) ^ degree) / r ^ k)
      atTop (𝓝 0) := by
    convert (tendsto_const_nhds.mul hshift :
      Tendsto
        (fun k : ℕ ↦ r ^ shift *
          ((((k + shift : ℕ) : ℝ) ^ degree) / r ^ (k + shift)))
        atTop (𝓝 (r ^ shift * 0))) using 1
    · ext k
      rw [Nat.add_comm shift k, pow_add]
      field_simp
    · simp
  have hbdd := (Metric.isBounded_range_of_tendsto _ hseq).bddAbove
  obtain ⟨C₀, hC₀⟩ := hbdd
  refine ⟨max 1 C₀, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro k
  have hk : (((shift + k : ℕ) : ℝ) ^ degree) / r ^ k ≤ C₀ :=
    hC₀ ⟨k, rfl⟩
  have hrk : 0 < r ^ k := pow_pos (lt_trans zero_lt_one hr) _
  have := (div_le_iff₀ hrk).mp hk
  exact this.trans (mul_le_mul_of_nonneg_right (le_max_right 1 C₀) hrk.le)

/-- With a positive exponent, a sufficiently large integer base absorbs any fixed constant. -/
theorem exists_nat_rpow_ge {δ A : ℝ} (hδ : 0 < δ) :
    ∃ base : ℕ, 0 < base ∧ A ≤ (base : ℝ) ^ δ := by
  have ht : Tendsto (fun base : ℕ ↦ (base : ℝ) ^ δ) atTop atTop :=
    (tendsto_rpow_atTop hδ).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  obtain ⟨base, hbase⟩ := (tendsto_atTop_atTop.mp ht (max A 1))
  refine ⟨max base 1, by omega, ?_⟩
  have h := hbase (max base 1) (Nat.le_max_left _ _)
  exact (le_max_left A 1).trans h

/-- Every quadratic-scheme length contains at least the fixed factor `16^k`. -/
theorem base_mul_pow_sixteen_le_quadraticLength
    (base : ℕ) : ∀ k : ℕ,
    base * 16 ^ k ≤ longRangeQuadraticLength base 4 k
  | 0 => by simp
  | k + 1 => by
      rw [longRangeQuadraticLength_succ, pow_succ]
      have ih := base_mul_pow_sixteen_le_quadraticLength base k
      have harity : 16 ≤ longRangeQuadraticArity 4 k := by
        simpa [longRangeQuadraticArity, pow_two] using
          Nat.mul_self_le_mul_self (show 4 ≤ 4 + k by omega)
      calc
        base * (16 ^ k * 16) = (base * 16 ^ k) * 16 := by ring
        _ ≤ longRangeQuadraticLength base 4 k * 16 :=
          Nat.mul_le_mul_right 16 ih
        _ ≤ longRangeQuadraticLength base 4 k *
            longRangeQuadraticArity 4 k :=
          Nat.mul_le_mul_left _ harity

/-- For `1 < α < 2` and `β > 0`, a sufficiently large base makes every cross-bond
term fit in its half-budget. -/
theorem exists_base_quadraticCrossControlled
    {β α : ℝ} (hβ : 0 < β) (hα1 : 1 < α) (hα2 : α < 2) :
    ∃ base : ℕ, 0 < base ∧ QuadraticCrossControlled β α base 4 := by
  let δ : ℝ := 2 - α
  have hδ : 0 < δ := sub_pos.mpr hα2
  let r : ℝ := (16 : ℝ) ^ δ
  have hr : 1 < r := by
    exact Real.one_lt_rpow (by norm_num) hδ
  obtain ⟨C, hCpos, hC⟩ :=
    exists_shifted_pow_le_const_mul_geometric 5 6 hr
  obtain ⟨base, hbase, hbaseC⟩ :=
    exists_nat_rpow_ge (δ := δ) (A := 32 * C / β) hδ
  refine ⟨base, hbase, quadraticCrossControlled_of_exponent ?_⟩
  intro k
  let L : ℕ := longRangeQuadraticLength base 4 k
  let M : ℕ := longRangeQuadraticTarget base 4 k
  let a : ℕ := longRangeQuadraticArity 4 k
  have hLnat : base * 16 ^ k ≤ L :=
    base_mul_pow_sixteen_le_quadraticLength base k
  have hLpos : 0 < L := longRangeQuadraticLength_pos hbase (by norm_num) k
  have hMpos : 0 < M := longRangeQuadraticTarget_pos hbase (by norm_num) k
  have hdensity := quadratic_target_density_lower hbase (by norm_num : 2 ≤ 4) k
  have hhalf : (L : ℝ) / 2 ≤ M := by
    have hLr : 0 < (L : ℝ) := by positivity
    norm_num at hdensity
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 4) hLr] at hdensity
    nlinarith
  have hM2 : (L : ℝ) ^ 2 / 4 ≤ (M : ℝ) ^ 2 := by
    have hL0 : 0 ≤ (L : ℝ) / 2 := by positivity
    have hm := pow_le_pow_left₀ hL0 hhalf 2
    nlinarith
  have hα0 : 0 ≤ α := le_trans (by norm_num) hα1.le
  have ha1 : (1 : ℝ) ≤ a := by
    exact_mod_cast (show 1 ≤ a by
      apply Nat.one_le_iff_ne_zero.mpr
      simp [a, longRangeQuadraticArity])
  have haPow : (a : ℝ) ^ α ≤ (a : ℝ) ^ 2 := by
    simpa only [Real.rpow_two] using
      Real.rpow_le_rpow_of_exponent_le ha1 hα2.le
  have hLr : 0 < (L : ℝ) := by positivity
  have haR : 0 < (a : ℝ) := by positivity
  have hden : 0 < (((L * a : ℕ) : ℝ) ^ α) := by
    have hLaNat : 0 < L * a := Nat.mul_pos hLpos (by
      simp [a, longRangeQuadraticArity])
    exact Real.rpow_pos_of_pos (by exact_mod_cast hLaNat) _
  have hsplit : (((L * a : ℕ) : ℝ) ^ α) =
      (L : ℝ) ^ α * (a : ℝ) ^ α := by
    push_cast
    exact Real.mul_rpow hLr.le haR.le
  have hpoly : (32 : ℝ) * (4 + k + 1 : ℕ) ^ 6 ≤
      β * (L : ℝ) ^ δ := by
    have hgeom := hC k
    have hbaseGeom : (32 : ℝ) * C / β * r ^ k ≤
        (base : ℝ) ^ δ * r ^ k :=
      mul_le_mul_of_nonneg_right hbaseC (pow_nonneg (le_of_lt (lt_trans zero_lt_one hr)) _)
    have hfirst : (32 : ℝ) * (4 + k + 1 : ℕ) ^ 6 / β ≤
        (32 * C / β) * r ^ k := by
      rw [div_le_iff₀ hβ]
      have := mul_le_mul_of_nonneg_left hgeom (show (0 : ℝ) ≤ 32 by norm_num)
      rw [show 4 + k + 1 = 5 + k by omega]
      calc
        32 * ↑(5 + k) ^ 6 ≤ 32 * (C * r ^ k) := this
        _ = (32 * C / β * r ^ k) * β := by field_simp
    have hlengthPow : (base : ℝ) ^ δ * r ^ k ≤ (L : ℝ) ^ δ := by
      have hcast : (base : ℝ) * (16 : ℝ) ^ k ≤ L := by exact_mod_cast hLnat
      have hp := Real.rpow_le_rpow (by positivity) hcast hδ.le
      rw [Real.mul_rpow (by positivity) (by positivity)] at hp
      have hrpow : ((16 : ℝ) ^ k) ^ δ = r ^ k := by
        calc
          (((16 : ℝ) ^ k) ^ δ) = (((16 : ℝ) ^ (k : ℝ)) ^ δ) := by
            rw [Real.rpow_natCast]
          _ = (16 : ℝ) ^ ((k : ℝ) * δ) :=
            (Real.rpow_mul (by norm_num) _ _).symm
          _ = (16 : ℝ) ^ (δ * (k : ℝ)) := by ring_nf
          _ = ((16 : ℝ) ^ δ) ^ (k : ℝ) :=
            Real.rpow_mul (by norm_num) _ _
          _ = ((16 : ℝ) ^ δ) ^ k := Real.rpow_natCast _ _
      simpa [hrpow] using hp
    have hdiv : (32 : ℝ) * ↑(4 + k + 1) ^ 6 / β ≤ (L : ℝ) ^ δ :=
      hfirst.trans (hbaseGeom.trans hlengthPow)
    simpa [mul_comm] using (div_le_iff₀ hβ).mp hdiv
  rw [hsplit] at hden ⊢
  have hfactor : (8 : ℝ) * ↑(4 + k + 1) ^ 2 *
      ((L : ℝ) ^ α * (a : ℝ) ^ α) ≤ β * (M : ℝ) ^ 2 := by
    have haEq : (a : ℝ) = (4 + k : ℕ) ^ 2 := by
      simp [a, longRangeQuadraticArity]
    have hsmall : (4 + k : ℕ) ^ 4 ≤ (4 + k + 1 : ℕ) ^ 4 := by
      exact Nat.pow_le_pow_left (by omega) 4
    have hneeded : (32 : ℝ) * ↑(4 + k + 1) ^ 2 * (a : ℝ) ^ 2 ≤
        β * (L : ℝ) ^ δ := by
      rw [haEq]
      have hcast : ((4 + k : ℕ) : ℝ) ^ 4 ≤
          ((4 + k + 1 : ℕ) : ℝ) ^ 4 := by exact_mod_cast hsmall
      calc
        (32 : ℝ) * ↑(4 + k + 1) ^ 2 * (↑(4 + k) ^ 2) ^ 2 =
            32 * ↑(4 + k + 1) ^ 2 * ↑(4 + k) ^ 4 := by ring
        _ ≤
            32 * ↑(4 + k + 1) ^ 2 * ↑(4 + k + 1) ^ 4 := by
          exact mul_le_mul_of_nonneg_left hcast (by positivity)
        _ = 32 * ↑(4 + k + 1) ^ 6 := by ring
        _ ≤ β * ↑L ^ δ := hpoly
    have hLa : (L : ℝ) ^ α * (L : ℝ) ^ δ = (L : ℝ) ^ 2 := by
      rw [← Real.rpow_add hLr]
      simp [δ]
    have hleft : (32 : ℝ) * ↑(4 + k + 1) ^ 2 *
        ((L : ℝ) ^ α * (a : ℝ) ^ α) ≤
        β * (L : ℝ) ^ 2 := by
      calc
        32 * ↑(4 + k + 1) ^ 2 * ((L : ℝ) ^ α * (a : ℝ) ^ α) ≤
            32 * ↑(4 + k + 1) ^ 2 * ((L : ℝ) ^ α * (a : ℝ) ^ 2) := by
          gcongr
        _ = (L : ℝ) ^ α *
            (32 * ↑(4 + k + 1) ^ 2 * (a : ℝ) ^ 2) := by ring
        _ ≤ (L : ℝ) ^ α * (β * (L : ℝ) ^ δ) := by
          gcongr
        _ = β * (L : ℝ) ^ 2 := by rw [← hLa]; ring
    nlinarith [hleft, mul_le_mul_of_nonneg_left hM2 hβ.le]
  exact (le_div_iff₀ hden).mpr hfactor

end Percolation
