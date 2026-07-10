import Mathlib
import Mathlib.Data.Fintype.Fin

/-!
# Finite iid renewal estimates

This file supplies the bounded finite-sample Wald argument used in Grimmett's Lemma 5.17.
Everything is expressed as finite weighted sums, avoiding a general stopping-time API.
-/

namespace Percolation

open scoped BigOperators

noncomputable section

variable {α : Type*} [Fintype α]

theorem sum_fin_val_eq_sum_range_real (n : ℕ) (f : ℕ → ℝ) :
    ∑ i : Fin n, f i.1 = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Fin.sum_univ_castSucc, Finset.sum_range_succ]
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [ih]

theorem sum_indicator_one_eq_card_filter (s : Finset ℕ) (P : ℕ → Prop)
    [DecidablePred P] :
    (∑ k ∈ s, if P k then (1 : ℝ) else 0) = (s.filter P).card := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, ih]

def finiteIIDWeight {N : ℕ} (w : α → ℝ) (ω : Fin N → α) : ℝ :=
  ∏ i, w (ω i)

theorem sum_finiteIIDWeight {N : ℕ} (w : α → ℝ) (hw : ∑ a, w a = 1) :
    ∑ ω : Fin N → α, finiteIIDWeight w ω = 1 := by
  unfold finiteIIDWeight
  rw [← Fintype.prod_sum]
  simp [hw]

/-- Splitting one coordinate from a finite product sum. -/
theorem sum_finiteIIDWeight_split_coordinate {N : ℕ} (j : Fin (N + 1))
    (w f : α → ℝ) (B : (Fin N → α) → ℝ) :
    ∑ ω : Fin (N + 1) → α,
        finiteIIDWeight w ω * B (j.removeNth ω) * f (ω j) =
      (∑ a : α, w a * f a) *
        ∑ η : Fin N → α, finiteIIDWeight w η * B η := by
  let e : α × (Fin N → α) ≃ (Fin (N + 1) → α) :=
    Fin.insertNthEquiv (fun _ ↦ α) j
  rw [← Fintype.sum_equiv e
    (fun q : α × (Fin N → α) ↦
      (w q.1 * finiteIIDWeight w q.2) * B q.2 * f q.1)
    (fun ω : Fin (N + 1) → α ↦
      finiteIIDWeight w ω * B (j.removeNth ω) * f (ω j))]
  · rw [Fintype.sum_prod_type]
    calc
      ∑ a : α, ∑ η : Fin N → α,
          (w a * finiteIIDWeight w η) * B η * f a =
          ∑ a : α, ∑ η : Fin N → α,
            (w a * f a) * (finiteIIDWeight w η * B η) := by
        apply Finset.sum_congr rfl
        intro a _ha
        apply Finset.sum_congr rfl
        intro η _hη
        ring
      _ = ( ∑ a : α, w a * f a) *
          ∑ η : Fin N → α, finiteIIDWeight w η * B η := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro a _ha
        rw [Finset.mul_sum]
  · intro q
    rcases q with ⟨a, η⟩
    simp only [e, Fin.insertNthEquiv, Equiv.coe_fn_mk, Fin.removeNth_insertNth,
      Fin.insertNth_apply_same]
    unfold finiteIIDWeight
    rw [j.prod_univ_succAbove]
    simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]

theorem sum_finiteIIDWeight_mul_coordinate {N : ℕ} (j : Fin (N + 1))
    (w f : α → ℝ) (B : (Fin N → α) → ℝ) (hw : ∑ a, w a = 1) :
    ∑ ω : Fin (N + 1) → α,
        finiteIIDWeight w ω * B (j.removeNth ω) * f (ω j) =
      (∑ a : α, w a * f a) *
        ∑ ω : Fin (N + 1) → α, finiteIIDWeight w ω * B (j.removeNth ω) := by
  rw [sum_finiteIIDWeight_split_coordinate]
  have hone := sum_finiteIIDWeight_split_coordinate j w (fun _ ↦ (1 : ℝ)) B
  simp only [mul_one] at hone
  rw [hone, hw, one_mul]

/-! ### Bounded first passage -/

def renewalPartialSum (n : ℕ) (v : α → ℕ) (ω : Fin (n + 1) → α) (k : ℕ) : ℕ :=
  ∑ i : Fin (n + 1), if i.1 < k then v (ω i) else 0

theorem renewalPartialSum_mono {n : ℕ} {v : α → ℕ} {ω : Fin (n + 1) → α}
    {k l : ℕ} (hkl : k ≤ l) :
    renewalPartialSum n v ω k ≤ renewalPartialSum n v ω l := by
  apply Finset.sum_le_sum
  intro i _hi
  by_cases hik : i.1 < k
  · simp [renewalPartialSum, hik, hik.trans_le hkl]
  · simp [renewalPartialSum, hik]

theorem renewalPartialSum_full_ge {n : ℕ} {v : α → ℕ} (hv : ∀ a, 1 ≤ v a)
    (ω : Fin (n + 1) → α) :
    n + 1 ≤ renewalPartialSum n v ω (n + 1) := by
  calc
    n + 1 = ∑ _i : Fin (n + 1), 1 := by simp
    _ ≤ ∑ i : Fin (n + 1), v (ω i) := Finset.sum_le_sum fun i _hi ↦ hv (ω i)
    _ = renewalPartialSum n v ω (n + 1) := by
      apply Finset.sum_congr rfl
      intro i _hi
      simp [renewalPartialSum, i.2]

theorem exists_renewalPartialSum_gt {n : ℕ} {v : α → ℕ} (hv : ∀ a, 1 ≤ v a)
    (ω : Fin (n + 1) → α) :
    ∃ k : ℕ, n < renewalPartialSum n v ω k := by
  exact ⟨n + 1, lt_of_lt_of_le (Nat.lt_succ_self n) (renewalPartialSum_full_ge hv ω)⟩

noncomputable def renewalFirstPassage (n : ℕ) (v : α → ℕ)
    (ω : Fin (n + 1) → α) : ℕ :=
  Nat.find (exists_renewalPartialSum_gt (fun a ↦ Nat.zero_lt_succ (v a)) ω)

theorem renewalFirstPassage_spec (n : ℕ) (v : α → ℕ) (ω : Fin (n + 1) → α) :
    n < renewalPartialSum n (fun a ↦ v a + 1) ω
      (renewalFirstPassage n v ω) :=
  Nat.find_spec (exists_renewalPartialSum_gt (fun a ↦ Nat.zero_lt_succ (v a)) ω)

theorem renewalFirstPassage_le (n : ℕ) (v : α → ℕ) (ω : Fin (n + 1) → α) :
    renewalFirstPassage n v ω ≤ n + 1 := by
  exact Nat.find_min' (exists_renewalPartialSum_gt (fun a ↦ Nat.zero_lt_succ (v a)) ω)
    (lt_of_lt_of_le (Nat.lt_succ_self n)
      (renewalPartialSum_full_ge (fun a ↦ Nat.zero_lt_succ (v a)) ω))

theorem renewalPartialSum_le_of_lt_firstPassage (n : ℕ) (v : α → ℕ)
    (ω : Fin (n + 1) → α) {k : ℕ} (hk : k < renewalFirstPassage n v ω) :
    renewalPartialSum n (fun a ↦ v a + 1) ω k ≤ n := by
  exact le_of_not_gt (Nat.find_min
    (exists_renewalPartialSum_gt (fun a ↦ Nat.zero_lt_succ (v a)) ω) hk)

theorem lt_renewalFirstPassage_iff_partialSum_le (n : ℕ) (v : α → ℕ)
    (ω : Fin (n + 1) → α) (k : ℕ) :
    k < renewalFirstPassage n v ω ↔
      renewalPartialSum n (fun a ↦ v a + 1) ω k ≤ n := by
  constructor
  · exact renewalPartialSum_le_of_lt_firstPassage n v ω
  · intro hsum
    by_contra hnot
    have hKk : renewalFirstPassage n v ω ≤ k := le_of_not_gt hnot
    have hmono := renewalPartialSum_mono (v := fun a ↦ v a + 1) (ω := ω) hKk
    have hspec := renewalFirstPassage_spec n v ω
    omega

theorem renewalPartialSum_eq_of_eq_off {n k : ℕ} {v : α → ℕ}
    {ω η : Fin (n + 1) → α}
    (hωη : ∀ i : Fin (n + 1), i.1 < k → ω i = η i) :
    renewalPartialSum n v ω k = renewalPartialSum n v η k := by
  apply Finset.sum_congr rfl
  intro i _hi
  by_cases hik : i.1 < k
  · simp [renewalPartialSum, hik, hωη i hik]
  · simp [renewalPartialSum, hik]

def renewalBeforeIndicator (n : ℕ) (v : α → ℕ) (j : Fin (n + 1)) (a₀ : α)
    (η : Fin n → α) : ℝ :=
  if renewalPartialSum n (fun a ↦ v a + 1) (j.insertNth a₀ η) j.1 ≤ n then 1 else 0

theorem renewalBeforeIndicator_removeNth (n : ℕ) (v : α → ℕ)
    (j : Fin (n + 1)) (a₀ : α) (ω : Fin (n + 1) → α) :
    renewalBeforeIndicator n v j a₀ (j.removeNth ω) =
      if j.1 < renewalFirstPassage n v ω then 1 else 0 := by
  have hoff : ∀ i : Fin (n + 1), i.1 < j.1 →
      (j.insertNth a₀ (j.removeNth ω)) i = ω i := by
    intro i hi
    rw [Fin.insertNth_removeNth]
    have hij : i ≠ j := fun hij ↦ by subst i; exact (Nat.lt_irrefl j.1 hi)
    simp [Function.update, hij]
  have hsum : renewalPartialSum n (fun a ↦ v a + 1)
      (j.insertNth a₀ (j.removeNth ω)) j.1 =
      renewalPartialSum n (fun a ↦ v a + 1) ω j.1 :=
    renewalPartialSum_eq_of_eq_off hoff
  rw [renewalBeforeIndicator, hsum]
  by_cases h : j.1 < renewalFirstPassage n v ω
  · simp [h, (lt_renewalFirstPassage_iff_partialSum_le n v ω j.1).mp h]
  · have hsum' : ¬renewalPartialSum n (fun a ↦ v a + 1) ω j.1 ≤ n :=
      fun hle ↦ h ((lt_renewalFirstPassage_iff_partialSum_le n v ω j.1).mpr hle)
    simp [h, hsum']

theorem renewalStoppedSum_eq_sum_before (n : ℕ) (v : α → ℕ)
    (ω : Fin (n + 1) → α) :
    (renewalPartialSum n (fun a ↦ v a + 1) ω (renewalFirstPassage n v ω) : ℝ) =
      ∑ j : Fin (n + 1),
        if j.1 < renewalFirstPassage n v ω then ((v (ω j) + 1 : ℕ) : ℝ) else 0 := by
  simp only [renewalPartialSum, Nat.cast_sum, Nat.cast_ite, Nat.cast_add, Nat.cast_one,
    Nat.cast_zero]

theorem sum_before_firstPassage (n : ℕ) (v : α → ℕ)
    (ω : Fin (n + 1) → α) :
    ∑ j : Fin (n + 1),
        (if j.1 < renewalFirstPassage n v ω then (1 : ℝ) else 0) =
      renewalFirstPassage n v ω := by
  have hK := renewalFirstPassage_le n v ω
  have hfilter : (Finset.range (n + 1)).filter
      (fun j ↦ j < renewalFirstPassage n v ω) =
      Finset.range (renewalFirstPassage n v ω) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  calc
    _ = ∑ j ∈ Finset.range (n + 1),
        if j < renewalFirstPassage n v ω then (1 : ℝ) else 0 :=
      sum_fin_val_eq_sum_range_real (n + 1)
        (fun j ↦ if j < renewalFirstPassage n v ω then (1 : ℝ) else 0)
    _ = ((Finset.range (n + 1)).filter
        (fun j ↦ j < renewalFirstPassage n v ω)).card :=
      sum_indicator_one_eq_card_filter _ _
    _ = renewalFirstPassage n v ω := by rw [hfilter, Finset.card_range]

/-- The bounded finite-sample Wald identity used in Lemma 5.17. -/
theorem finiteRenewal_wald (n : ℕ) (v : α → ℕ) (w : α → ℝ)
    (hw : ∑ a, w a = 1) (a₀ : α) :
    ∑ ω : Fin (n + 1) → α,
        finiteIIDWeight w ω *
          renewalPartialSum n (fun a ↦ v a + 1) ω (renewalFirstPassage n v ω) =
      (∑ a : α, w a * (v a + 1 : ℕ)) *
        ∑ ω : Fin (n + 1) → α,
          finiteIIDWeight w ω * renewalFirstPassage n v ω := by
  simp_rw [renewalStoppedSum_eq_sum_before]
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have hcoordinate : ∀ j : Fin (n + 1),
      ∑ ω : Fin (n + 1) → α,
          finiteIIDWeight w ω *
            (if j.1 < renewalFirstPassage n v ω then ((v (ω j) + 1 : ℕ) : ℝ) else 0) =
        (∑ a : α, w a * (v a + 1 : ℕ)) *
          ∑ ω : Fin (n + 1) → α,
            finiteIIDWeight w ω *
              (if j.1 < renewalFirstPassage n v ω then (1 : ℝ) else 0) := by
    intro j
    have hfactor := sum_finiteIIDWeight_mul_coordinate j w
      (fun a ↦ (v a + 1 : ℕ)) (renewalBeforeIndicator n v j a₀) hw
    simpa only [renewalBeforeIndicator_removeNth, ite_mul, mul_ite, mul_one, mul_zero,
      zero_mul, Nat.cast_add, Nat.cast_one, Nat.cast_zero] using hfactor
  have htail :
      ∑ j : Fin (n + 1), ∑ ω : Fin (n + 1) → α,
          finiteIIDWeight w ω *
            (if j.1 < renewalFirstPassage n v ω then (1 : ℝ) else 0) =
        ∑ ω : Fin (n + 1) → α,
          finiteIIDWeight w ω * renewalFirstPassage n v ω := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro ω _hω
    rw [← Finset.mul_sum, sum_before_firstPassage]
  simp_rw [hcoordinate]
  rw [← Finset.mul_sum, htail]
  conv_lhs => rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _ha
  conv_lhs => rw [Finset.mul_sum]

def finiteRenewalMean (v : α → ℕ) (w : α → ℝ) : ℝ :=
  ∑ a : α, w a * (v a + 1 : ℕ)

def finiteRenewalExpectedFirstPassage (n : ℕ) (v : α → ℕ) (w : α → ℝ) : ℝ :=
  ∑ ω : Fin (n + 1) → α,
    finiteIIDWeight w ω * renewalFirstPassage n v ω

theorem finiteIIDWeight_nonneg {N : ℕ} {w : α → ℝ} (hw0 : ∀ a, 0 ≤ w a)
    (ω : Fin N → α) :
    0 ≤ finiteIIDWeight w ω := by
  exact Finset.prod_nonneg fun i _hi ↦ hw0 (ω i)

theorem finiteRenewalMean_ge_one (v : α → ℕ) (w : α → ℝ)
    (hw0 : ∀ a, 0 ≤ w a) (hw : ∑ a, w a = 1) :
    1 ≤ finiteRenewalMean v w := by
  calc
    1 = ∑ a : α, w a := hw.symm
    _ = ∑ a : α, w a * 1 := by simp
    _ ≤ ∑ a : α, w a * (v a + 1 : ℕ) := by
      apply Finset.sum_le_sum
      intro a _ha
      exact mul_le_mul_of_nonneg_left (by norm_num) (hw0 a)
    _ = finiteRenewalMean v w := rfl

/-- First-passage expectation bound following from the finite Wald identity. -/
theorem finiteRenewal_expectedFirstPassage_gt (n : ℕ) (v : α → ℕ) (w : α → ℝ)
    (hw0 : ∀ a, 0 ≤ w a) (hw : ∑ a, w a = 1) (a₀ : α) :
    (n : ℝ) / finiteRenewalMean v w < finiteRenewalExpectedFirstPassage n v w := by
  have hsumWeight : ∑ ω : Fin (n + 1) → α, finiteIIDWeight w ω = 1 :=
    sum_finiteIIDWeight w hw
  have hstopped : (n : ℝ) <
      ∑ ω : Fin (n + 1) → α,
        finiteIIDWeight w ω *
          renewalPartialSum n (fun a ↦ v a + 1) ω (renewalFirstPassage n v ω) := by
    calc
      (n : ℝ) < (n + 1 : ℕ) := by exact_mod_cast Nat.lt_succ_self n
      _ = (n + 1 : ℕ) * ∑ ω : Fin (n + 1) → α, finiteIIDWeight w ω := by
        rw [hsumWeight, mul_one]
      _ ≤ ∑ ω : Fin (n + 1) → α,
          finiteIIDWeight w ω *
            renewalPartialSum n (fun a ↦ v a + 1) ω (renewalFirstPassage n v ω) := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro ω _hω
        have hweight := finiteIIDWeight_nonneg hw0 ω
        have hspec := renewalFirstPassage_spec n v ω
        have hcast : (n + 1 : ℝ) ≤
            renewalPartialSum n (fun a ↦ v a + 1) ω (renewalFirstPassage n v ω) := by
          exact_mod_cast (Nat.succ_le_iff.mpr hspec)
        simpa [mul_comm] using mul_le_mul_of_nonneg_left hcast hweight
  rw [finiteRenewal_wald n v w hw a₀] at hstopped
  change (n : ℝ) < finiteRenewalMean v w * finiteRenewalExpectedFirstPassage n v w at hstopped
  have hmean : 0 < finiteRenewalMean v w :=
    lt_of_lt_of_le zero_lt_one (finiteRenewalMean_ge_one v w hw0 hw)
  exact (div_lt_iff₀ hmean).mpr (by simpa [mul_comm] using hstopped)

/-! ### Distribution encoded by a truncated tail -/

def truncatedTailWeight (n : ℕ) (g : ℕ → ℝ) (a : Fin (n + 1)) : ℝ :=
  if a.1 < n then g a.1 - g (a.1 + 1) else g n

theorem sum_range_tail_differences_add (g : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range n, (g i - g (i + 1))) + g n = g 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      linarith

theorem sum_truncatedTailWeight (n : ℕ) (g : ℕ → ℝ) (hg0 : g 0 = 1) :
    ∑ a : Fin (n + 1), truncatedTailWeight n g a = 1 := by
  have hsplit :
      ∑ i ∈ Finset.range (n + 1),
          (if i < n then g i - g (i + 1) else g n) =
        (∑ i ∈ Finset.range n, (g i - g (i + 1))) + g n := by
    rw [Finset.sum_range_succ]
    apply congrArg₂ (· + ·)
    · apply Finset.sum_congr rfl
      intro i hi
      simp [Finset.mem_range.mp hi]
    · simp
  calc
    ∑ a : Fin (n + 1), truncatedTailWeight n g a =
        ∑ i ∈ Finset.range (n + 1),
          (if i < n then g i - g (i + 1) else g n) := by
      simpa only [truncatedTailWeight] using
        sum_fin_val_eq_sum_range_real (n + 1)
          (fun i ↦ if i < n then g i - g (i + 1) else g n)
    _ = 1 := by rw [hsplit, sum_range_tail_differences_add, hg0]

theorem truncatedTailWeight_nonneg (n : ℕ) {g : ℕ → ℝ}
    (hg_nonneg : ∀ i, 0 ≤ g i) (hg_anti : Antitone g) (a : Fin (n + 1)) :
    0 ≤ truncatedTailWeight n g a := by
  rw [truncatedTailWeight]
  split
  · exact sub_nonneg.mpr (hg_anti (Nat.le_succ a.1))
  · exact hg_nonneg n

theorem sum_range_tail_weight_mul (g : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range n, (g i - g (i + 1)) * (i + 1 : ℕ)) +
        g n * (n + 1 : ℕ) =
      ∑ i ∈ Finset.range (n + 1), g i := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      norm_num [Nat.cast_succ] at ih ⊢
      linarith

theorem finiteRenewalMean_truncatedTailWeight (n : ℕ) (g : ℕ → ℝ) :
    finiteRenewalMean (fun a : Fin (n + 1) ↦ a.1)
        (truncatedTailWeight n g) =
      ∑ i ∈ Finset.range (n + 1), g i := by
  have hsplit :
      ∑ i ∈ Finset.range (n + 1),
          (if i < n then g i - g (i + 1) else g n) * (i + 1 : ℕ) =
        (∑ i ∈ Finset.range n, (g i - g (i + 1)) * (i + 1 : ℕ)) +
          g n * (n + 1 : ℕ) := by
    rw [Finset.sum_range_succ]
    apply congrArg₂ (· + ·)
    · apply Finset.sum_congr rfl
      intro i hi
      simp [Finset.mem_range.mp hi]
    · simp
  calc
    finiteRenewalMean (fun a : Fin (n + 1) ↦ a.1)
        (truncatedTailWeight n g) =
        ∑ i ∈ Finset.range (n + 1),
          (if i < n then g i - g (i + 1) else g n) * (i + 1 : ℕ) := by
      simpa only [finiteRenewalMean, truncatedTailWeight] using
        sum_fin_val_eq_sum_range_real (n + 1)
          (fun i ↦ (if i < n then g i - g (i + 1) else g n) * (i + 1 : ℕ))
    _ = _ := by rw [hsplit, sum_range_tail_weight_mul]

/-- Wald's lower bound with a distribution specified only by its truncated tail. -/
theorem finiteRenewal_expectedFirstPassage_truncatedTail_gt
    (n : ℕ) (g : ℕ → ℝ) (hg0 : g 0 = 1)
    (hg_nonneg : ∀ i, 0 ≤ g i) (hg_anti : Antitone g) :
    (n : ℝ) / (∑ i ∈ Finset.range (n + 1), g i) <
      finiteRenewalExpectedFirstPassage n (fun a : Fin (n + 1) ↦ a.1)
        (truncatedTailWeight n g) := by
  let a₀ : Fin (n + 1) := ⟨0, by omega⟩
  have h := finiteRenewal_expectedFirstPassage_gt n (fun a : Fin (n + 1) ↦ a.1)
    (truncatedTailWeight n g) (truncatedTailWeight_nonneg n hg_nonneg hg_anti)
    (sum_truncatedTailWeight n g hg0) a₀
  rwa [finiteRenewalMean_truncatedTailWeight] at h

def finiteRenewalContinuationProbability (n : ℕ) (v : α → ℕ) (w : α → ℝ)
    (k : ℕ) : ℝ :=
  ∑ ω : Fin (n + 1) → α, finiteIIDWeight w ω *
    if renewalPartialSum n (fun a ↦ v a + 1) ω k ≤ n then 1 else 0

def finiteRenewalExpectedRenewalCount (n : ℕ) (v : α → ℕ) (w : α → ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 n, finiteRenewalContinuationProbability n v w k

theorem renewalFirstPassage_pos (n : ℕ) (v : α → ℕ) (ω : Fin (n + 1) → α) :
    0 < renewalFirstPassage n v ω := by
  have hspec := renewalFirstPassage_spec n v ω
  by_contra h
  have hzero : renewalFirstPassage n v ω = 0 := Nat.eq_zero_of_not_pos h
  simp [hzero, renewalPartialSum] at hspec

theorem sum_continuations_eq_firstPassage_sub_one
    (n : ℕ) (v : α → ℕ) (ω : Fin (n + 1) → α) :
    ∑ k ∈ Finset.Icc 1 n,
        (if renewalPartialSum n (fun a ↦ v a + 1) ω k ≤ n then (1 : ℝ) else 0) =
      renewalFirstPassage n v ω - 1 := by
  simp_rw [← lt_renewalFirstPassage_iff_partialSum_le]
  have hK1 : 1 ≤ renewalFirstPassage n v ω := renewalFirstPassage_pos n v ω
  have hcast : (renewalFirstPassage n v ω : ℝ) - 1 =
      ((renewalFirstPassage n v ω - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hK1]
    norm_num
  rw [hcast]
  rw [sum_indicator_one_eq_card_filter]
  have hKle := renewalFirstPassage_le n v ω
  have hfilter : (Finset.Icc 1 n).filter
      (fun k ↦ k < renewalFirstPassage n v ω) =
      Finset.Icc 1 (renewalFirstPassage n v ω - 1) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  rw [hfilter, Nat.card_Icc]
  norm_cast

theorem finiteRenewalExpectedRenewalCount_eq (n : ℕ) (v : α → ℕ) (w : α → ℝ)
    (hw : ∑ a, w a = 1) :
    finiteRenewalExpectedRenewalCount n v w =
      finiteRenewalExpectedFirstPassage n v w - 1 := by
  unfold finiteRenewalExpectedRenewalCount finiteRenewalContinuationProbability
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  simp_rw [sum_continuations_eq_firstPassage_sub_one]
  simp_rw [mul_sub, mul_one]
  rw [Finset.sum_sub_distrib]
  simp only [finiteRenewalExpectedFirstPassage]
  rw [sum_finiteIIDWeight (N := n + 1) w hw]

/-- Expected renewal-count lower bound in the exact form used after (5.21). -/
theorem finiteRenewal_expectedRenewalCount_ge (n : ℕ) (v : α → ℕ) (w : α → ℝ)
    (hw0 : ∀ a, 0 ≤ w a) (hw : ∑ a, w a = 1) (a₀ : α) :
    (n : ℝ) / finiteRenewalMean v w - 1 ≤
      finiteRenewalExpectedRenewalCount n v w := by
  rw [finiteRenewalExpectedRenewalCount_eq n v w hw]
  exact sub_le_sub_right (finiteRenewal_expectedFirstPassage_gt n v w hw0 hw a₀).le 1

theorem finiteRenewal_expectedRenewalCount_truncatedTail_ge
    (n : ℕ) (g : ℕ → ℝ) (hg0 : g 0 = 1)
    (hg_nonneg : ∀ i, 0 ≤ g i) (hg_anti : Antitone g) :
    (n : ℝ) / (∑ i ∈ Finset.range (n + 1), g i) - 1 ≤
      finiteRenewalExpectedRenewalCount n (fun a : Fin (n + 1) ↦ a.1)
        (truncatedTailWeight n g) := by
  let a₀ : Fin (n + 1) := ⟨0, by omega⟩
  have h := finiteRenewal_expectedRenewalCount_ge n (fun a : Fin (n + 1) ↦ a.1)
    (truncatedTailWeight n g) (truncatedTailWeight_nonneg n hg_nonneg hg_anti)
    (sum_truncatedTailWeight n g hg0) a₀
  rwa [finiteRenewalMean_truncatedTailWeight] at h

end

end Percolation
