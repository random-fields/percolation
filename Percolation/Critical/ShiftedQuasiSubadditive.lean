import Mathlib.Analysis.Subadditive

/-!
# A shifted generalized subadditive limit theorem

This is the precise analytic lemma used after Grimmett's inequality (8.36).  The binary operation
on diameter indices is `m + n + 2`, and the error depends on the second input.  Iterating a fixed
second input advances along arithmetic progressions of step `n + 2`; this gives the same Fekete
argument without changing the source indexing.
-/

namespace Percolation

open Filter Set Topology

/-- Candidate rate for a shifted quasi-subadditive sequence. -/
noncomputable def shiftedQuasiSubadditiveRate (δ h : ℕ → ℝ) : ℝ :=
  sInf (range fun k : ℕ ↦ (δ k + h k) / (k + 2))

theorem shiftedQuasiSubadditiveRate_le_ratio
    {δ h : ℕ → ℝ} (hδ : ∀ n, 0 ≤ δ n) (hh : ∀ n, 0 ≤ h n) (k : ℕ) :
    shiftedQuasiSubadditiveRate δ h ≤ (δ k + h k) / (k + 2) := by
  rw [shiftedQuasiSubadditiveRate]
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact div_nonneg (add_nonneg (hδ n) (hh n)) (by positivity)
  · exact ⟨k, rfl⟩

/-- Repeatedly gluing a fixed second input advances by `k+2`. -/
theorem shiftedQuasiSubadditive_iterate
    {δ h : ℕ → ℝ}
    (hrec : ∀ m n, δ (m + n + 2) ≤ δ m + δ n + h n)
    (k q r : ℕ) :
    δ (q * (k + 2) + r) ≤ q * (δ k + h k) + δ r := by
  induction q with
  | zero => simp
  | succ q ih =>
      calc
        δ ((q + 1) * (k + 2) + r) =
            δ ((q * (k + 2) + r) + k + 2) := by
              rw [Nat.succ_mul]
              congr 1 <;> omega
        _ ≤ δ (q * (k + 2) + r) + δ k + h k := hrec _ k
        _ ≤ (q * (δ k + h k) + δ r) + δ k + h k := by
          gcongr
        _ = ((q + 1 : ℕ) : ℝ) * (δ k + h k) + δ r := by
          rw [Nat.cast_add, Nat.cast_one]
          ring

/-- A single rate ratio strictly below `L` gives an eventual upper bound along every index. -/
theorem shiftedQuasiSubadditive_eventually_div_lt
    {δ h : ℕ → ℝ}
    (hrec : ∀ m n, δ (m + n + 2) ≤ δ m + δ n + h n)
    {L : ℝ} {k : ℕ} (hk : (δ k + h k) / (k + 2) < L) :
    ∀ᶠ n : ℕ in atTop, δ n / n < L := by
  let s : ℕ := k + 2
  have hs : s ≠ 0 := by omega
  refine .atTop_of_arithmetic hs fun r _hr ↦ ?_
  have A : Tendsto
      (fun x : ℝ ↦ ((δ k + h k) + δ r / x) / ((s : ℝ) + r / x))
      atTop (nhds (((δ k + h k) + 0) / ((s : ℝ) + 0))) :=
    (tendsto_const_nhds.add (tendsto_const_nhds.div_atTop tendsto_id)).div
      (tendsto_const_nhds.add (tendsto_const_nhds.div_atTop tendsto_id)) (by
        simpa [s] using (show (s : ℝ) ≠ 0 by positivity))
  have B : Tendsto
      (fun x : ℝ ↦ (x * (δ k + h k) + δ r) / (x * s + r))
      atTop (nhds ((δ k + h k) / s)) := by
    simpa only [add_zero] using A.congr' ((eventually_ne_atTop 0).mono fun x hx ↦ by
      simp only [add_div' _ _ _ hx, div_div_div_cancel_right₀ hx, mul_comm])
  have hk' : (δ k + h k) / (s : ℝ) < L := by simpa [s] using hk
  filter_upwards [
      (B.comp tendsto_natCast_atTop_atTop).eventually (Iio_mem_nhds hk'),
      eventually_ge_atTop (1 : ℕ)] with q hq hqpos
  refine lt_of_le_of_lt ?_ hq
  have hiter := shiftedQuasiSubadditive_iterate hrec k q r
  have hden : (0 : ℝ) < (q * s + r : ℕ) := by positivity
  change δ (s * q + r) / (s * q + r : ℕ) ≤
    ((q : ℝ) * (δ k + h k) + δ r) / ((q : ℝ) * s + r)
  rw [Nat.mul_comm s q]
  have hdenEq : (q : ℝ) * (s : ℝ) + (r : ℝ) = (q * s + r : ℕ) := by
    norm_num
  rw [hdenEq]
  exact div_le_div_of_nonneg_right (by simpa [s] using hiter) hden.le

/-- Shifted generalized Fekete lemma, in the exact form required by (8.36). -/
theorem tendsto_div_shiftedQuasiSubadditiveRate
    {δ h : ℕ → ℝ}
    (hδ : ∀ n, 0 ≤ δ n) (hh : ∀ n, 0 ≤ h n)
    (hrec : ∀ m n, δ (m + n + 2) ≤ δ m + δ n + h n)
    (hsublinear : Tendsto (fun n : ℕ ↦ h n / n) atTop (nhds 0)) :
    Tendsto (fun n : ℕ ↦ δ n / n) atTop
      (nhds (shiftedQuasiSubadditiveRate δ h)) := by
  let a := shiftedQuasiSubadditiveRate δ h
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro l hl
    have hsmall : Tendsto (fun n : ℕ ↦ (2 * a) / (n : ℝ)) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    have hlower : Tendsto
        (fun n : ℕ ↦ a + (2 * a) / (n : ℝ) - h n / n) atTop (nhds a) := by
      simpa using (tendsto_const_nhds.add hsmall).sub hsublinear
    filter_upwards [hlower.eventually (Ioi_mem_nhds hl), eventually_ge_atTop (1 : ℕ)]
      with n hnlim hnpos
    apply hnlim.trans_le
    have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
    have hrate := shiftedQuasiSubadditiveRate_le_ratio hδ hh n
    change a ≤ (δ n + h n) / (n + 2) at hrate
    have hmul := (le_div_iff₀ (show (0 : ℝ) < n + 2 by positivity)).mp hrate
    apply (le_div_iff₀ hnreal).2
    calc
      (a + 2 * a / (n : ℝ) - h n / n) * (n : ℝ) =
          a * ((n : ℝ) + 2) - h n := by field_simp
      _ ≤ δ n := by linarith
  · intro L hL
    change a < L at hL
    dsimp [a] at hL
    rw [shiftedQuasiSubadditiveRate] at hL
    obtain ⟨x, ⟨k, rfl⟩, hk⟩ := exists_lt_of_csInf_lt (range_nonempty _) hL
    exact shiftedQuasiSubadditive_eventually_div_lt hrec hk

/-- The rate lies below every corrected finite-index slope; equivalently, this is Grimmett's
finite-index lower bound on the negative logarithm. -/
theorem add_mul_shiftedQuasiSubadditiveRate_sub_error_le
    {δ h : ℕ → ℝ} (hδ : ∀ n, 0 ≤ δ n) (hh : ∀ n, 0 ≤ h n) (k : ℕ) :
    (k + 2 : ℝ) * shiftedQuasiSubadditiveRate δ h - h k ≤ δ k := by
  have hrate := shiftedQuasiSubadditiveRate_le_ratio hδ hh k
  have hpos : (0 : ℝ) < k + 2 := by positivity
  rw [le_div_iff₀ hpos] at hrate
  linarith

end Percolation
