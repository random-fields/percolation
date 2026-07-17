import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Data.Finsupp.Basic

/-!
# Bounded-radix decompositions for supercritical cluster sizes

This file isolates the arithmetic content of Grimmett's Lemma 8.82.  The input is a sequence
whose successive terms grow by a factor between two and a real constant `delta`.  The output is
a finite expansion with digits at most `delta`.  Keeping this argument independent of
percolation makes the endpoint
and junk-value conditions explicit before it is used in Theorem 8.61.
-/

namespace Percolation

open scoped BigOperators

/-- The surface-order exponent `(d - 1) / d` appearing in the supercritical finite-cluster
estimates. -/
noncomputable def supercriticalClusterSizeExponent (d : ℕ) : ℝ := ((d : ℝ) - 1) / d

/-- A finite expansion of `n` in the (not necessarily divisibility-based) scale `r`, with digits
bounded by the real number `delta`.  The support condition records that no scale larger than
`n` is used. -/
def IsBoundedRadixRepresentation (delta : ℝ) (r : ℕ → ℕ) (n : ℕ)
    (w : ℕ →₀ ℕ) : Prop :=
  (∀ i, (w i : ℝ) ≤ delta) ∧
    w.sum (fun i a ↦ a * r i) = n ∧
      ∀ i ∈ w.support, r i ≤ n

theorem rapidlyGrowingSequence_pos
    {r : ℕ → ℕ} (hr0 : r 0 = 1)
    (hrLower : ∀ i, 2 * r i ≤ r (i + 1)) :
    ∀ i, 0 < r i := by
  intro i
  induction i with
  | zero => simp [hr0]
  | succ i ih =>
      exact lt_of_lt_of_le (by omega : 0 < 2 * r i) (hrLower i)

theorem rapidlyGrowingSequence_strictMono
    {r : ℕ → ℕ} (hr0 : r 0 = 1)
    (hrLower : ∀ i, 2 * r i ≤ r (i + 1)) :
    StrictMono r := by
  apply strictMono_nat_of_lt_succ
  intro i
  have hpos := rapidlyGrowingSequence_pos hr0 hrLower i
  exact (lt_two_mul_self hpos).trans_le (hrLower i)

theorem rapidlyGrowingSequence_index_lt
    {r : ℕ → ℕ} (hr0 : r 0 = 1)
    (hrLower : ∀ i, 2 * r i ≤ r (i + 1)) (i : ℕ) :
    i < r i + 1 := by
  have hmono := rapidlyGrowingSequence_strictMono hr0 hrLower
  have hbase : i + 1 ≤ r i := by
    induction i with
    | zero => simp [hr0]
    | succ i ih =>
        have hlt : r i < r (i + 1) := hmono (Nat.lt_succ_self i)
        have hstep : r i + 1 ≤ r (i + 1) := by omega
        omega
  omega

theorem rapidlyGrowingSequence_unbounded
    {r : ℕ → ℕ} (hr0 : r 0 = 1)
    (hrLower : ∀ i, 2 * r i ≤ r (i + 1)) (n : ℕ) :
    ∃ i, n < r i := by
  refine ⟨n + 1, ?_⟩
  have h := rapidlyGrowingSequence_index_lt hr0 hrLower (n + 1)
  omega

theorem rapidlyGrowingSequence_pow_mul_le
    {r : ℕ → ℕ} (hrLower : ∀ i, 2 * r i ≤ r (i + 1)) (i k : ℕ) :
    2 ^ k * r i ≤ r (i + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        2 ^ (k + 1) * r i = 2 * (2 ^ k * r i) := by ring
        _ ≤ 2 * r (i + k) := Nat.mul_le_mul_left 2 ih
        _ ≤ r (i + k + 1) := hrLower (i + k)
        _ = r (i + (k + 1)) := by rw [Nat.add_assoc]

theorem half_le_supercriticalClusterSizeExponent {d : ℕ} (hd : 2 ≤ d) :
    (1 / 2 : ℝ) ≤ supercriticalClusterSizeExponent d := by
  have hd0 : (0 : ℝ) < d := by positivity
  rw [supercriticalClusterSizeExponent]
  apply (le_div_iff₀ hd0).2
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  nlinarith

theorem supercriticalClusterSizeExponent_le_one {d : ℕ} :
    supercriticalClusterSizeExponent d ≤ 1 := by
  by_cases hd0 : d = 0
  · simp [hd0, supercriticalClusterSizeExponent]
  · have hdpos : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd0
    rw [supercriticalClusterSizeExponent, div_le_iff₀ hdpos]
    linarith

private theorem half_rpow_supercriticalClusterSizeExponent_le_three_quarters
    {d : ℕ} (hd : 2 ≤ d) :
    (1 / 2 : ℝ) ^ supercriticalClusterSizeExponent d ≤ 3 / 4 := by
  calc
    (1 / 2 : ℝ) ^ supercriticalClusterSizeExponent d ≤ (1 / 2 : ℝ) ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num)
        (half_le_supercriticalClusterSizeExponent hd)
    _ = √(1 / 2 : ℝ) := (Real.sqrt_eq_rpow _).symm
    _ ≤ 3 / 4 := by rw [Real.sqrt_le_iff]; norm_num

private theorem sum_three_quarters_pow_le (n : ℕ) :
    (∑ i ∈ Finset.range n, (3 / 4 : ℝ) ^ i) ≤ 4 := by
  have h := geom_sum_Ico_le_of_lt_one (m := 0) (n := n) (x := (3 / 4 : ℝ))
    (by norm_num) (by norm_num)
  convert h using 1 <;> norm_num [Nat.Ico_zero_eq_range]

/-- The bounded-digit part of Grimmett Lemma 8.82.  No divisibility hypothesis on `r` is
required: the proof is the greedy Euclidean algorithm at the largest scale not exceeding `n`. -/
theorem exists_boundedRadixRepresentation
    {delta : ℝ} (hdelta : 0 ≤ delta) {r : ℕ → ℕ} (hr0 : r 0 = 1)
    (hrLower : ∀ i, 2 * r i ≤ r (i + 1))
    (hrUpper : ∀ i, (r (i + 1) : ℝ) ≤ delta * r i) :
    ∀ n : ℕ, ∃ w : ℕ →₀ ℕ, IsBoundedRadixRepresentation delta r n w := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn0 : n = 0
      · subst n
        refine ⟨0, ?_⟩
        exact ⟨fun i ↦ by simpa using hdelta, by simp, by simp⟩
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
        let J := Nat.find (rapidlyGrowingSequence_unbounded hr0 hrLower n)
        have hnJ : n < r J := Nat.find_spec (rapidlyGrowingSequence_unbounded hr0 hrLower n)
        have hJpos : 0 < J := by
          by_contra hnot
          have hJ0 : J = 0 := Nat.eq_zero_of_not_pos hnot
          rw [hJ0, hr0] at hnJ
          omega
        let I := J - 1
        have hJI : J = I + 1 := by
          dsimp [I]
          omega
        have hrIle : r I ≤ n := by
          by_contra hnot
          have hnlt : n < r I := Nat.lt_of_not_ge hnot
          have hmin : J ≤ I := by
            exact Nat.find_min'
              (rapidlyGrowingSequence_unbounded hr0 hrLower n) hnlt
          omega
        have hrIpos : 0 < r I := rapidlyGrowingSequence_pos hr0 hrLower I
        let a := n / r I
        let b := n % r I
        have hb_lt_rI : b < r I := by
          exact Nat.mod_lt n hrIpos
        have hb_lt_n : b < n := hb_lt_rI.trans_le hrIle
        obtain ⟨v, hvDigits, hvSum, hvSupport⟩ := ih b hb_lt_n
        have hvI : v I = 0 := by
          by_contra hvIne
          have hmem : I ∈ v.support := Finsupp.mem_support_iff.mpr hvIne
          have := hvSupport I hmem
          omega
        have haPos : 0 < a := by
          dsimp [a]
          exact Nat.div_pos hrIle hrIpos
        have haMul : a * r I ≤ n := by
          dsimp [a]
          exact Nat.div_mul_le_self n (r I)
        have haLt : (a : ℝ) < delta := by
          have haMulReal : (a : ℝ) * r I ≤ n := by exact_mod_cast haMul
          have hnJReal : (n : ℝ) < r J := by exact_mod_cast hnJ
          have hupper := hrUpper I
          rw [hJI] at hnJReal
          have hrIReal : (0 : ℝ) < r I := by exact_mod_cast hrIpos
          nlinarith
        let w : ℕ →₀ ℕ := v + Finsupp.single I a
        refine ⟨w, ?_, ?_, ?_⟩
        · intro i
          by_cases hi : i = I
          · subst i
            simp [w, hvI, haLt.le]
          · simpa [w, Finsupp.single_apply, hi] using hvDigits i
        · have hdecomp : b + a * r I = n := by
            dsimp [a, b]
            exact Nat.mod_add_div' n (r I)
          calc
            w.sum (fun i c ↦ c * r i) =
                v.sum (fun i c ↦ c * r i) + a * r I := by
              change (v + Finsupp.single I a).sum (fun i c ↦ c * r i) = _
              rw [Finsupp.sum_add_index']
              · simp [Finsupp.sum_single_index]
              · intro i
                simp
              · intro i x y
                exact Nat.add_mul x y (r i)
            _ = b + a * r I := by rw [hvSum]
            _ = n := hdecomp
        · intro i hi
          by_cases hiI : i = I
          · subst i
            exact hrIle
          · have hvi : v i ≠ 0 := by
              intro hzero
              have : w i = 0 := by simp [w, hiI, hzero]
              exact (Finsupp.mem_support_iff.mp hi) this
            exact (hvSupport i (Finsupp.mem_support_iff.mpr hvi)).trans
              (Nat.le_of_lt hb_lt_n)

/-- The weighted estimate in Grimmett Lemma 8.82.  Its exact source constant is `4 * delta`. -/
theorem boundedRadixRepresentation_weighted_sum_le
    {d : ℕ} (hd : 2 ≤ d) {delta : ℝ} (hdelta : 0 ≤ delta) {r : ℕ → ℕ}
    (hrLower : ∀ i, 2 * r i ≤ r (i + 1)) {n : ℕ} (hn : 0 < n) {w : ℕ →₀ ℕ}
    (hw : IsBoundedRadixRepresentation delta r n w) :
    w.sum (fun i a ↦ (a : ℝ) * (r i : ℝ) ^ supercriticalClusterSizeExponent d) ≤
      (4 * delta) * (n : ℝ) ^ supercriticalClusterSizeExponent d := by
  rcases hw with ⟨hwDigit, hwSum, hwSupport⟩
  have hwne : w ≠ 0 := by
    intro hzero
    subst w
    simp at hwSum
    omega
  have hsupport : w.support.Nonempty := Finsupp.support_nonempty_iff.mpr hwne
  let I := w.support.max' hsupport
  have hImem : I ∈ w.support := by exact Finset.max'_mem _ _
  have hrIle : r I ≤ n := hwSupport I hImem
  have hα0 : 0 ≤ supercriticalClusterSizeExponent d :=
    (by norm_num : (0 : ℝ) ≤ 1 / 2).trans (half_le_supercriticalClusterSizeExponent hd)
  have hterm : ∀ i ∈ w.support,
      (w i : ℝ) * (r i : ℝ) ^ supercriticalClusterSizeExponent d ≤
        delta * (n : ℝ) ^ supercriticalClusterSizeExponent d *
          (3 / 4 : ℝ) ^ (I - i) := by
    intro i hi
    have hiI : i ≤ I := Finset.le_max' w.support i hi
    have hscale : 2 ^ (I - i) * r i ≤ n := by
      calc
        2 ^ (I - i) * r i ≤ r (i + (I - i)) :=
          rapidlyGrowingSequence_pow_mul_le hrLower i (I - i)
        _ = r I := by rw [Nat.add_sub_of_le hiI]
        _ ≤ n := hrIle
    have hscaleReal : (2 : ℝ) ^ (I - i) * (r i : ℝ) ≤ n := by exact_mod_cast hscale
    have hpowPos : (0 : ℝ) < 2 ^ (I - i) := pow_pos (by norm_num) _
    have hratio : (r i : ℝ) ≤ (n : ℝ) * (1 / 2 : ℝ) ^ (I - i) := by
      rw [one_div, inv_pow, ← div_eq_mul_inv]
      apply (le_div_iff₀ hpowPos).2
      simpa [mul_comm] using hscaleReal
    have hpower : ((1 / 2 : ℝ) ^ (I - i)) ^ supercriticalClusterSizeExponent d =
        ((1 / 2 : ℝ) ^ supercriticalClusterSizeExponent d) ^ (I - i) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 2), mul_comm,
        Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    calc
      (w i : ℝ) * (r i : ℝ) ^ supercriticalClusterSizeExponent d ≤
          delta * (r i : ℝ) ^ supercriticalClusterSizeExponent d := by
        gcongr
        exact hwDigit i
      _ ≤ delta * ((n : ℝ) * (1 / 2 : ℝ) ^ (I - i)) ^
          supercriticalClusterSizeExponent d := by
        gcongr
      _ = delta * (n : ℝ) ^ supercriticalClusterSizeExponent d *
          ((1 / 2 : ℝ) ^ supercriticalClusterSizeExponent d) ^ (I - i) := by
        rw [Real.mul_rpow (by positivity) (by positivity), hpower]
        ring
      _ ≤ delta * (n : ℝ) ^ supercriticalClusterSizeExponent d *
          (3 / 4 : ℝ) ^ (I - i) := by
        gcongr
        exact half_rpow_supercriticalClusterSizeExponent_le_three_quarters hd
  have hsubset : w.support ⊆ Finset.range (I + 1) := by
    intro i hi
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_max' w.support i hi))
  change (∑ i ∈ w.support,
    (w i : ℝ) * (r i : ℝ) ^ supercriticalClusterSizeExponent d) ≤ _
  calc
    (∑ i ∈ w.support, (w i : ℝ) * (r i : ℝ) ^ supercriticalClusterSizeExponent d) ≤
        ∑ i ∈ w.support,
          delta * (n : ℝ) ^ supercriticalClusterSizeExponent d *
            (3 / 4 : ℝ) ^ (I - i) := by
      exact Finset.sum_le_sum fun i hi ↦ hterm i hi
    _ ≤ ∑ i ∈ Finset.range (I + 1),
        delta * (n : ℝ) ^ supercriticalClusterSizeExponent d *
          (3 / 4 : ℝ) ^ (I - i) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (by intros; positivity)
    _ = delta * (n : ℝ) ^ supercriticalClusterSizeExponent d *
        ∑ i ∈ Finset.range (I + 1), (3 / 4 : ℝ) ^ (I - i) := by
      rw [Finset.mul_sum]
    _ = delta * (n : ℝ) ^ supercriticalClusterSizeExponent d *
        ∑ i ∈ Finset.range (I + 1), (3 / 4 : ℝ) ^ i := by
      congr 1
      simpa using Finset.sum_range_reflect (fun i ↦ (3 / 4 : ℝ) ^ i) (I + 1)
    _ ≤ delta * (n : ℝ) ^ supercriticalClusterSizeExponent d * 4 := by
      gcongr
      exact sum_three_quarters_pow_le (I + 1)
    _ = (4 * delta) * (n : ℝ) ^ supercriticalClusterSizeExponent d := by ring

/-- Full source-facing form of Grimmett Lemma 8.82: every positive integer admits a bounded
scale representation satisfying the uniform surface-order estimate. -/
theorem exists_boundedRadixRepresentation_weighted
    {d : ℕ} (hd : 2 ≤ d) {delta : ℝ} (hdelta : 0 ≤ delta)
    {r : ℕ → ℕ} (hr0 : r 0 = 1)
    (hrLower : ∀ i, 2 * r i ≤ r (i + 1))
    (hrUpper : ∀ i, (r (i + 1) : ℝ) ≤ delta * r i)
    {n : ℕ} (hn : 0 < n) :
    ∃ w : ℕ →₀ ℕ,
      IsBoundedRadixRepresentation delta r n w ∧
        w.sum (fun i a ↦ (a : ℝ) * (r i : ℝ) ^ supercriticalClusterSizeExponent d) ≤
          (4 * delta) * (n : ℝ) ^ supercriticalClusterSizeExponent d := by
  obtain ⟨w, hw⟩ := exists_boundedRadixRepresentation hdelta hr0 hrLower hrUpper n
  exact ⟨w, hw,
    boundedRadixRepresentation_weighted_sum_le hd hdelta hrLower hn hw⟩

end Percolation
