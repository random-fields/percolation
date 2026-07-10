import Percolation.Critical.FiniteRenewal

/-!
# Finite conditional stochastic domination

Discrete CDF comparison and iid renewal-fit identities used to transfer
Grimmett's sausage domination lemma to the bounded Wald calculation.
-/

namespace Percolation

open scoped BigOperators

noncomputable section

/-! ### Finite CDF comparison -/

/-- Discrete summation by parts: domination of every initial partial sum
implies domination against every nonnegative antitone test function. -/
theorem sum_mul_le_sum_mul_of_partialSums_le
    (N : ℕ) (u v φ : ℕ → ℝ)
    (hpartial : ∀ r < N,
      (∑ i ∈ Finset.range (r + 1), u i) ≤
        ∑ i ∈ Finset.range (r + 1), v i)
    (hφanti : Antitone φ) (hφ0 : ∀ i < N, 0 ≤ φ i) :
    (∑ i ∈ Finset.range N, φ i * u i) ≤
      ∑ i ∈ Finset.range N, φ i * v i := by
  induction N generalizing u v φ with
  | zero => simp
  | succ N ih =>
      let ψ : ℕ → ℝ := fun i ↦ φ i - φ N
      have hψanti : Antitone ψ := fun _ _ hij ↦ sub_le_sub_right (hφanti hij) _
      have hψ0 : ∀ i < N, 0 ≤ ψ i := by
        intro i hi
        exact sub_nonneg.mpr (hφanti (by omega))
      have hpartial' : ∀ r < N,
          (∑ i ∈ Finset.range (r + 1), u i) ≤
            ∑ i ∈ Finset.range (r + 1), v i :=
        fun r hr ↦ hpartial r (by omega)
      have hψ := ih u v ψ hpartial' hψanti hψ0
      have hφN : 0 ≤ φ N := hφ0 N (by omega)
      have htotal := hpartial N (by omega)
      have hscaled := mul_le_mul_of_nonneg_left htotal hφN
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      calc
        (∑ i ∈ Finset.range N, φ i * u i) + φ N * u N =
            (∑ i ∈ Finset.range N, ψ i * u i) +
              φ N * (∑ i ∈ Finset.range (N + 1), u i) := by
                simp only [ψ, Finset.sum_range_succ]
                simp_rw [sub_mul]
                rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
                ring
        _ ≤ (∑ i ∈ Finset.range N, ψ i * v i) +
              φ N * (∑ i ∈ Finset.range (N + 1), v i) :=
          add_le_add hψ hscaled
        _ = (∑ i ∈ Finset.range N, φ i * v i) + φ N * v N := by
          simp only [ψ, Finset.sum_range_succ]
          simp_rw [sub_mul]
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
          ring

/-- Probability that `k` iid gaps with tail `g` fit in a remaining radial
budget `b`, where each gap consumes its value plus one pivotal edge. -/
noncomputable def renewalFitProbability (g : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, _ => 1
  | k + 1, b => ∑ t ∈ Finset.range b,
      (g t - g (t + 1)) * renewalFitProbability g k (b - (t + 1))

@[simp]
theorem renewalFitProbability_zero (g : ℕ → ℝ) (b : ℕ) :
    renewalFitProbability g 0 b = 1 := rfl

theorem renewalFitProbability_succ (g : ℕ → ℝ) (k b : ℕ) :
    renewalFitProbability g (k + 1) b =
      ∑ t ∈ Finset.range b,
        (g t - g (t + 1)) * renewalFitProbability g k (b - (t + 1)) := rfl

theorem renewalFitProbability_nonneg {g : ℕ → ℝ}
    (hg : Antitone g) : ∀ k b, 0 ≤ renewalFitProbability g k b := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      intro b
      rw [renewalFitProbability_succ]
      exact Finset.sum_nonneg fun t _ ↦
        mul_nonneg (sub_nonneg.mpr (hg (Nat.le_succ t))) (ih _)

theorem renewalFitProbability_mono_budget {g : ℕ → ℝ}
    (hg : Antitone g) (k : ℕ) : Monotone (renewalFitProbability g k) := by
  induction k with
  | zero => intro b c _; simp
  | succ k ih =>
      intro b c hbc
      rw [renewalFitProbability_succ, renewalFitProbability_succ]
      calc
        (∑ t ∈ Finset.range b,
            (g t - g (t + 1)) * renewalFitProbability g k (b - (t + 1))) ≤
            ∑ t ∈ Finset.range b,
              (g t - g (t + 1)) * renewalFitProbability g k (c - (t + 1)) := by
                apply Finset.sum_le_sum
                intro t _ht
                exact mul_le_mul_of_nonneg_left (ih (Nat.sub_le_sub_right hbc _))
                  (sub_nonneg.mpr (hg (Nat.le_succ t)))
        _ ≤ ∑ t ∈ Finset.range c,
              (g t - g (t + 1)) * renewalFitProbability g k (c - (t + 1)) := by
                refine Finset.sum_le_sum_of_subset_of_nonneg
                  (Finset.range_mono hbc) ?_
                intro t _htc _htb
                exact mul_nonneg (sub_nonneg.mpr (hg (Nat.le_succ t)))
                  (renewalFitProbability_nonneg hg k _)

theorem sum_range_tail_differences_eq_one_sub
    {g : ℕ → ℝ} (hg0 : g 0 = 1) (r : ℕ) :
    (∑ t ∈ Finset.range (r + 1), (g t - g (t + 1))) = 1 - g (r + 1) := by
  have h := sum_range_tail_differences_add g (r + 1)
  rw [hg0] at h
  linarith

/-- One backward step of conditional stochastic domination.  `P rs` is the
mass of an actual history `rs`; the hypotheses say that the next actual gap
has every finite CDF at least as large as the iid law with tail `g`. -/
theorem renewalFitProbability_mul_le_sum_extensions
    (g : ℕ → ℝ) (hg0 : g 0 = 1) (hg : Antitone g)
    (P : List ℕ → ℝ) (rs : List ℕ) (k b : ℕ)
    (hcdf : ∀ r < b,
      (1 - g (r + 1)) * P rs ≤
        ∑ t ∈ Finset.range (r + 1), P (rs ++ [t])) :
    renewalFitProbability g (k + 1) b * P rs ≤
      ∑ t ∈ Finset.range b,
        renewalFitProbability g k (b - (t + 1)) * P (rs ++ [t]) := by
  rw [renewalFitProbability_succ, Finset.sum_mul]
  have hcomp := sum_mul_le_sum_mul_of_partialSums_le b
    (fun t ↦ (g t - g (t + 1)) * P rs)
    (fun t ↦ P (rs ++ [t]))
    (fun t ↦ renewalFitProbability g k (b - (t + 1)))
    (by
      intro r hr
      rw [← Finset.sum_mul, sum_range_tail_differences_eq_one_sub hg0]
      exact hcdf r hr)
    (by
      intro i j hij
      apply renewalFitProbability_mono_budget hg k
      omega)
    (by
      intro i hi
      exact renewalFitProbability_nonneg hg k _)
  simpa [mul_assoc, mul_left_comm, mul_comm] using hcomp

/-- Direct finite-product probability that `k` iid increments fit in budget
`b`. -/
def finiteIIDFitProbability {α : Type*} [Fintype α]
    (v : α → ℕ) (w : α → ℝ) (k b : ℕ) : ℝ :=
  ∑ ω : Fin k → α, finiteIIDWeight w ω *
    if (∑ i : Fin k, (v (ω i) + 1)) ≤ b then 1 else 0

theorem finiteIIDWeight_insertNth {α : Type*} [Fintype α]
    {N : ℕ} (j : Fin (N + 1)) (w : α → ℝ) (a : α) (η : Fin N → α) :
    finiteIIDWeight w (j.insertNth a η : Fin (N + 1) → α) =
      w a * finiteIIDWeight w η := by
  unfold finiteIIDWeight
  rw [j.prod_univ_succAbove]
  simp

theorem sum_increments_insertNth_last {α : Type*} [Fintype α]
    (N : ℕ) (v : α → ℕ) (a : α) (η : Fin N → α) :
    (∑ i : Fin (N + 1),
        (v (((Fin.last N).insertNth a η : Fin (N + 1) → α) i) + 1)) =
      (∑ i : Fin N, (v (η i) + 1)) + (v a + 1) := by
  rw [Fin.sum_univ_castSucc]
  simp

/-- Recursion for the direct finite-product fit probability. -/
theorem finiteIIDFitProbability_succ {α : Type*} [Fintype α]
    (v : α → ℕ) (w : α → ℝ) (k b : ℕ) :
    finiteIIDFitProbability v w (k + 1) b =
      ∑ a : α, w a *
        if v a + 1 ≤ b then finiteIIDFitProbability v w k (b - (v a + 1)) else 0 := by
  let e : α × (Fin k → α) ≃ (Fin (k + 1) → α) :=
    Fin.insertNthEquiv (fun _ ↦ α) (Fin.last k)
  rw [finiteIIDFitProbability]
  rw [← Fintype.sum_equiv e
    (fun q : α × (Fin k → α) ↦
      finiteIIDWeight w ((Fin.last k).insertNth q.1 q.2 : Fin (k + 1) → α) *
        if (∑ i : Fin (k + 1),
          (v (((Fin.last k).insertNth q.1 q.2 : Fin (k + 1) → α) i) + 1)) ≤ b
          then 1 else 0)
    (fun ω : Fin (k + 1) → α ↦ finiteIIDWeight w ω *
      if (∑ i : Fin (k + 1), (v (ω i) + 1)) ≤ b then 1 else 0)]
  · rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro a _ha
    by_cases hab : v a + 1 ≤ b
    · simp only [hab, if_true]
      rw [finiteIIDFitProbability]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro η _hη
      rw [finiteIIDWeight_insertNth, sum_increments_insertNth_last]
      have hiff : (∑ i : Fin k, (v (η i) + 1)) + (v a + 1) ≤ b ↔
          (∑ i : Fin k, (v (η i) + 1)) ≤ b - (v a + 1) := by omega
      rw [if_congr hiff rfl rfl]
      ring
    · simp only [hab, if_false, mul_zero]
      apply Finset.sum_eq_zero
      intro η _hη
      rw [finiteIIDWeight_insertNth, sum_increments_insertNth_last]
      have hnot : ¬(∑ i : Fin k, (v (η i) + 1)) + (v a + 1) ≤ b := by omega
      simp [hnot]
  · intro q
    rfl

theorem finiteIIDFitProbability_truncatedTail_eq_renewalFitProbability
    (n k b : ℕ) (g : ℕ → ℝ) (hb : b ≤ n) :
    finiteIIDFitProbability (fun a : Fin (n + 1) ↦ a.1)
        (truncatedTailWeight n g) k b = renewalFitProbability g k b := by
  induction k generalizing b with
  | zero => simp [finiteIIDFitProbability, finiteIIDWeight]
  | succ k ih =>
      rw [finiteIIDFitProbability_succ, renewalFitProbability_succ]
      rw [show (∑ a : Fin (n + 1), truncatedTailWeight n g a *
          if a.1 + 1 ≤ b then
            finiteIIDFitProbability (fun a : Fin (n + 1) ↦ a.1)
              (truncatedTailWeight n g) k (b - (a.1 + 1)) else 0) =
          ∑ t ∈ Finset.range (n + 1),
            (if t < n then g t - g (t + 1) else g n) *
              if t + 1 ≤ b then
                finiteIIDFitProbability (fun a : Fin (n + 1) ↦ a.1)
                  (truncatedTailWeight n g) k (b - (t + 1)) else 0 by
        simpa [truncatedTailWeight] using
          (sum_fin_val_eq_sum_range_real (n + 1) (fun t ↦
            (if t < n then g t - g (t + 1) else g n) *
              if t + 1 ≤ b then
                finiteIIDFitProbability (fun a : Fin (n + 1) ↦ a.1)
                  (truncatedTailWeight n g) k (b - (t + 1)) else 0))]
      rw [← Finset.sum_subset (Finset.range_mono (show b ≤ n + 1 by omega))]
      · apply Finset.sum_congr rfl
        intro t ht
        have htb := Finset.mem_range.mp ht
        simp only [htb.trans_le hb, if_true]
        rw [if_pos (by omega), ih (b - (t + 1)) (by omega)]
      · intro t htn htb
        have htge : b ≤ t := by
          simpa only [Finset.mem_range, not_lt] using htb
        simp [htge]

def finiteIIDPrefixFitProbability {α : Type*} [Fintype α]
    (v : α → ℕ) (w : α → ℝ) (N k b : ℕ) : ℝ :=
  ∑ ω : Fin N → α, finiteIIDWeight w ω *
    if (∑ i : Fin N, (if i.1 < k then v (ω i) + 1 else 0)) ≤ b then 1 else 0

theorem prefixIncrementSum_removeLast {α : Type*} [Fintype α]
    (v : α → ℕ) (k m : ℕ) (ω : Fin (k + m + 1) → α) :
    (∑ i : Fin (k + m),
      (if i.1 < k then v ((Fin.last (k + m)).removeNth ω i) + 1 else 0)) =
      ∑ i : Fin (k + m + 1), (if i.1 < k then v (ω i) + 1 else 0) := by
  rw [Fin.removeNth_last, Fin.sum_univ_castSucc]
  have hlast : ¬(Fin.last (k + m)).1 < k := by simp
  rw [if_neg hlast, add_zero]
  exact Fintype.sum_congr _ _ fun i ↦ rfl

theorem finiteIIDPrefixFitProbability_add
    {α : Type*} [Fintype α] (v : α → ℕ) (w : α → ℝ)
    (hw : ∑ a, w a = 1) (k m b : ℕ) :
    finiteIIDPrefixFitProbability v w (k + m) k b =
      finiteIIDFitProbability v w k b := by
  induction m with
  | zero =>
      simp only [Nat.add_zero, finiteIIDPrefixFitProbability, finiteIIDFitProbability]
      apply Finset.sum_congr rfl
      intro ω _hω
      have hsum : (∑ i : Fin k, (if i.1 < k then v (ω i) + 1 else 0)) =
          ∑ i : Fin k, (v (ω i) + 1) := by
        apply Fintype.sum_congr _ _
        intro i
        rw [if_pos i.2]
      rw [hsum]
  | succ m ih =>
      let B : (Fin (k + m) → α) → ℝ := fun η ↦
        if (∑ i : Fin (k + m), (if i.1 < k then v (η i) + 1 else 0)) ≤ b
          then 1 else 0
      have hsplit := sum_finiteIIDWeight_split_coordinate
        (Fin.last (k + m)) w (fun _ ↦ (1 : ℝ)) B
      simp only [mul_one] at hsplit
      have hleft :
          ∑ ω : Fin (k + m + 1) → α,
              finiteIIDWeight w ω * B ((Fin.last (k + m)).removeNth ω) =
            finiteIIDPrefixFitProbability v w (k + m + 1) k b := by
        rw [finiteIIDPrefixFitProbability]
        apply Finset.sum_congr rfl
        intro ω _hω
        dsimp only [B]
        rw [prefixIncrementSum_removeLast]
      have hright :
          ∑ η : Fin (k + m) → α, finiteIIDWeight w η * B η =
            finiteIIDPrefixFitProbability v w (k + m) k b := rfl
      rw [hleft, hright, hw, one_mul] at hsplit
      simpa [Nat.add_assoc] using hsplit.trans ih

theorem finiteRenewalContinuationProbability_eq_renewalFitProbability
    (n k : ℕ) (g : ℕ → ℝ) (hk : k ≤ n + 1) (hg0 : g 0 = 1) :
    finiteRenewalContinuationProbability n (fun a : Fin (n + 1) ↦ a.1)
        (truncatedTailWeight n g) k = renewalFitProbability g k n := by
  have hw := sum_truncatedTailWeight n g hg0
  have hprefix :
      finiteRenewalContinuationProbability n (fun a : Fin (n + 1) ↦ a.1)
          (truncatedTailWeight n g) k =
        finiteIIDPrefixFitProbability (fun a : Fin (n + 1) ↦ a.1)
          (truncatedTailWeight n g) (n + 1) k n := by
    rfl
  rw [hprefix]
  have hadd : k + (n + 1 - k) = n + 1 := Nat.add_sub_of_le hk
  calc
    finiteIIDPrefixFitProbability (fun a : Fin (n + 1) ↦ a.1)
        (truncatedTailWeight n g) (n + 1) k n =
        finiteIIDPrefixFitProbability (fun a : Fin (n + 1) ↦ a.1)
          (truncatedTailWeight n g) (k + (n + 1 - k)) k n := by rw [hadd]
    _ = finiteIIDFitProbability (fun a : Fin (n + 1) ↦ a.1)
          (truncatedTailWeight n g) k n :=
      finiteIIDPrefixFitProbability_add _ _ hw _ _ _
    _ = renewalFitProbability g k n :=
      finiteIIDFitProbability_truncatedTail_eq_renewalFitProbability n k n g le_rfl


end

end Percolation
