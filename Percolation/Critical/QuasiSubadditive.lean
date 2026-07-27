import Mathlib.Analysis.Subadditive

/-!
# Two-sided corrected subadditivity

Grimmett's proof of Theorem 6.10 applies Fekete's lemma twice: once to a logarithmic
box-connection probability and once to its negative, after adding the same sublinear correction.
This file isolates that analytic argument from percolation.
-/

namespace Percolation

open Filter Set Topology

/-- The positively signed corrected sequence.  Defining its value at zero separately lets us use
Mathlib's `Subadditive`, whose definition quantifies over all natural numbers. -/
noncomputable def correctedLogSequence (f g : ℕ → ℝ) (c : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else g n + c + f n

/-- The negatively signed corrected sequence. -/
noncomputable def correctedNegLogSequence (f g : ℕ → ℝ) (c : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else g n + c - f n

@[simp]
theorem correctedLogSequence_zero (f g : ℕ → ℝ) (c : ℝ) :
    correctedLogSequence f g c 0 = 0 := by
  simp [correctedLogSequence]

@[simp]
theorem correctedNegLogSequence_zero (f g : ℕ → ℝ) (c : ℝ) :
    correctedNegLogSequence f g c 0 = 0 := by
  simp [correctedNegLogSequence]

theorem correctedLogSequence_apply_of_pos {f g : ℕ → ℝ} {c : ℝ} {n : ℕ} (hn : 0 < n) :
    correctedLogSequence f g c n = g n + c + f n := by
  simp [correctedLogSequence, hn.ne']

theorem correctedNegLogSequence_apply_of_pos {f g : ℕ → ℝ} {c : ℝ} {n : ℕ}
    (hn : 0 < n) :
    correctedNegLogSequence f g c n = g n + c - f n := by
  simp [correctedNegLogSequence, hn.ne']

/-- An upper quasi-additivity inequality and a doubling bound on the correction produce a
genuinely subadditive corrected sequence. -/
theorem correctedLogSequence_subadditive {f g : ℕ → ℝ} {c : ℝ}
    (hupper : ∀ m n : ℕ, 0 < m → 0 < n →
      f (m + n) ≤ f m + f n + g (min m n))
    (hgrowth : ∀ m n : ℕ, 0 < m → 0 < n →
      g (m + n) ≤ g (max m n) + c) :
    Subadditive (correctedLogSequence f g c) := by
  intro m n
  rcases eq_or_lt_of_le (Nat.zero_le m) with rfl | hm
  · simp
  rcases eq_or_lt_of_le (Nat.zero_le n) with rfl | hn
  · simp
  rw [correctedLogSequence_apply_of_pos hm,
    correctedLogSequence_apply_of_pos hn,
    correctedLogSequence_apply_of_pos (Nat.add_pos_left hm n)]
  have hf := hupper m n hm hn
  have hg := hgrowth m n hm hn
  rcases le_total m n with hmn | hnm
  · rw [Nat.min_eq_left hmn] at hf
    rw [Nat.max_eq_right hmn] at hg
    linarith
  · rw [Nat.min_eq_right hnm] at hf
    rw [Nat.max_eq_left hnm] at hg
    linarith

/-- A lower quasi-additivity inequality gives subadditivity after negating the main sequence. -/
theorem correctedNegLogSequence_subadditive {f g : ℕ → ℝ} {c : ℝ}
    (hlower : ∀ m n : ℕ, 0 < m → 0 < n →
      f m + f n - g (min m n) ≤ f (m + n))
    (hgrowth : ∀ m n : ℕ, 0 < m → 0 < n →
      g (m + n) ≤ g (max m n) + c) :
    Subadditive (correctedNegLogSequence f g c) := by
  intro m n
  rcases eq_or_lt_of_le (Nat.zero_le m) with rfl | hm
  · simp
  rcases eq_or_lt_of_le (Nat.zero_le n) with rfl | hn
  · simp
  rw [correctedNegLogSequence_apply_of_pos hm,
    correctedNegLogSequence_apply_of_pos hn,
    correctedNegLogSequence_apply_of_pos (Nat.add_pos_left hm n)]
  have hf := hlower m n hm hn
  have hg := hgrowth m n hm hn
  rcases le_total m n with hmn | hnm
  · rw [Nat.min_eq_left hmn] at hf
    rw [Nat.max_eq_right hmn] at hg
    linarith
  · rw [Nat.min_eq_right hnm] at hf
    rw [Nat.max_eq_left hnm] at hg
    linarith

section TwoSided

variable {f g : ℕ → ℝ} {c : ℝ}

variable
  (hplus : Subadditive (correctedLogSequence f g c))
  (hminus : Subadditive (correctedNegLogSequence f g c))
  (hplusBdd : BddBelow (range fun n ↦ correctedLogSequence f g c n / n))
  (hminusBdd : BddBelow (range fun n ↦ correctedNegLogSequence f g c n / n))
  (herror : Tendsto (fun n : ℕ ↦ (g n + c) / n) atTop (𝓝 0))

include hplusBdd hminusBdd herror in
/-- The two Fekete limits are negatives of each other because their sum is twice the sublinear
correction. -/
theorem correctedSubadditive_lim_add_eq_zero :
    hplus.lim + hminus.lim = 0 := by
  have hplusLim := hplus.tendsto_lim hplusBdd
  have hminusLim := hminus.tendsto_lim hminusBdd
  have hsum : Tendsto
      (fun n : ℕ ↦ correctedLogSequence f g c n / n +
        correctedNegLogSequence f g c n / n)
      atTop (𝓝 (hplus.lim + hminus.lim)) :=
    hplusLim.add hminusLim
  have htwiceError : Tendsto (fun n : ℕ ↦ 2 * ((g n + c) / n)) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul herror
  have heventually : ∀ᶠ n : ℕ in atTop,
      correctedLogSequence f g c n / n + correctedNegLogSequence f g c n / n =
        2 * ((g n + c) / n) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hnpos : 0 < n := zero_lt_one.trans_le hn
    rw [correctedLogSequence_apply_of_pos hnpos,
      correctedNegLogSequence_apply_of_pos hnpos]
    ring
  have hsumZero : Tendsto
      (fun n : ℕ ↦ correctedLogSequence f g c n / n +
        correctedNegLogSequence f g c n / n)
      atTop (𝓝 0) := by
    apply htwiceError.congr'
    filter_upwards [heventually] with n hn
    exact hn.symm
  exact tendsto_nhds_unique hsum hsumZero

/-- The common decay rate is the Fekete limit of the corrected negative-log sequence. -/
noncomputable def correctedSubadditiveRate : ℝ := hminus.lim

include hminusBdd herror in
/-- Removing the sublinear correction leaves the same negative-logarithmic limit. -/
theorem tendsto_neg_div_correctedSubadditiveRate :
    Tendsto (fun n : ℕ ↦ -f n / n) atTop
      (𝓝 (correctedSubadditiveRate hminus)) := by
  have hminusLim := hminus.tendsto_lim hminusBdd
  have hdiff : Tendsto
      (fun n : ℕ ↦ correctedNegLogSequence f g c n / n - (g n + c) / n)
      atTop (𝓝 (hminus.lim - 0)) := hminusLim.sub herror
  have heventually : ∀ᶠ n : ℕ in atTop,
      correctedNegLogSequence f g c n / n - (g n + c) / n = -f n / n := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hnpos : 0 < n := zero_lt_one.trans_le hn
    rw [correctedNegLogSequence_apply_of_pos hnpos]
    ring
  simpa [correctedSubadditiveRate] using hdiff.congr' heventually

include hplus hplusBdd hminusBdd herror in
/-- The two Fekete inequalities give a uniform finite-index error estimate around the limiting
rate.  This is the abstract form of Grimmett's equation (6.36). -/
theorem abs_natCast_mul_correctedSubadditiveRate_add_le
    {n : ℕ} (hn : 0 < n) :
    |(n : ℝ) * correctedSubadditiveRate hminus + f n| ≤ g n + c := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hplusLe := hplus.lim_le_div hplusBdd hn.ne'
  have hminusLe := hminus.lim_le_div hminusBdd hn.ne'
  rw [correctedLogSequence_apply_of_pos hn] at hplusLe
  rw [correctedNegLogSequence_apply_of_pos hn] at hminusLe
  have hplusMul : hplus.lim * (n : ℝ) ≤ g n + c + f n :=
    (le_div_iff₀ hnreal).mp hplusLe
  have hminusMul : hminus.lim * (n : ℝ) ≤ g n + c - f n :=
    (le_div_iff₀ hnreal).mp hminusLe
  have hlimits := correctedSubadditive_lim_add_eq_zero
    hplus hminus hplusBdd hminusBdd herror
  rw [abs_le]
  constructor <;> dsimp only [correctedSubadditiveRate] <;> nlinarith

end TwoSided

end Percolation
