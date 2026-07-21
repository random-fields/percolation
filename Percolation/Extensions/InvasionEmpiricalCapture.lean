import Percolation.Extensions.InvasionCapture
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Empirical consequence of invasion capture

This file closes the deterministic half of Grimmett's heuristic (12.29): once the invasion has
met an infinite `y`-sublevel cluster, every later selected edge has label at most `y`, and hence
the empirical distribution function converges to one at `y`.
-/

namespace Percolation

open Set Filter

/-- The edge selected at time `k` belongs to every later invasion cluster. -/
theorem invasionEdge_mem_clusterAt_of_lt
    {d : ℕ} (hd : 0 < d) (label : CubicEdge d → ℝ) {k n : ℕ} (hkn : k < n) :
    invasionEdge hd label k ∈ invasionClusterAt label n := by
  have hfirst : invasionEdge hd label k ∈ invasionClusterAt label (k + 1) := by
    rw [invasionClusterAt_succ hd]
    simp
  exact invasionClusterAt_mono label (Nat.succ_le_iff.mpr hkn) hfirst

/-- If every edge selected from time `N` onward is `y`-sublevel, then by time `n` at least
`n-N` selected edges are `y`-sublevel. -/
theorem invasionClusterAt_good_card_ge_sub
    {d : ℕ} (hd : 0 < d) (label : CubicEdge d → ℝ) (y : ℝ) (N : ℕ)
    (hgood : ∀ n, N ≤ n → label (invasionEdge hd label n) ≤ y) :
    ∀ n, N ≤ n → n - N ≤
      ((invasionClusterAt label n).filter fun e ↦ label e ≤ y).card := by
  intro n hNn
  induction n, hNn using Nat.le_induction with
  | base => simp
  | succ n hNn ih =>
      rw [invasionClusterAt_succ hd]
      have hfilter :
          (insert (invasionEdge hd label n) (invasionClusterAt label n)).filter
              (fun e ↦ label e ≤ y) =
            insert (invasionEdge hd label n)
              ((invasionClusterAt label n).filter fun e ↦ label e ≤ y) := by
        ext e
        simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨he | he, hle⟩
          · exact Or.inl he
          · exact Or.inr ⟨he, hle⟩
        · rintro (he | ⟨he, hle⟩)
          · subst e
            exact ⟨Or.inl rfl, hgood n hNn⟩
          · exact ⟨Or.inr he, hle⟩
      rw [hfilter, Finset.card_insert_of_notMem]
      · omega
      · simp only [Finset.mem_filter, not_and_or]
        exact Or.inl (invasionEdge_not_mem_clusterAt hd label n)

/-- Ratio form of the preceding counting estimate. -/
theorem one_sub_natCast_div_le_invasionEmpiricalCDF
    {d : ℕ} (hd : 0 < d) (label : CubicEdge d → ℝ) (y : ℝ) (N n : ℕ)
    (hNn : N ≤ n) (hn : 0 < n)
    (hgood : ∀ k, N ≤ k → label (invasionEdge hd label k) ≤ y) :
    1 - (N : ℝ) / n ≤ invasionEmpiricalCDF label n y := by
  have hcard := invasionClusterAt_good_card_ge_sub hd label y N hgood n hNn
  unfold invasionEmpiricalCDF
  have hcardReal : ((n - N : ℕ) : ℝ) ≤
      (((invasionClusterAt label n).filter fun e ↦ label e ≤ y).card : ℝ) := by
    exact_mod_cast hcard
  have hratio : ((n - N : ℕ) : ℝ) / n ≤
      (((invasionClusterAt label n).filter fun e ↦ label e ≤ y).card : ℝ) / n := by
    exact div_le_div_of_nonneg_right hcardReal (by positivity)
  calc
    1 - (N : ℝ) / n = ((n - N : ℕ) : ℝ) / n := by
      rw [Nat.cast_sub hNn]
      field_simp
    _ ≤ _ := hratio

/-- An eventual `y`-sublevel selection rule forces the empirical CDF at `y` to converge to one. -/
theorem invasionEmpiricalCDF_tendsto_one_of_eventually_edge_label_le
    {d : ℕ} (hd : 0 < d) (label : CubicEdge d → ℝ) (y : ℝ) (N : ℕ)
    (hgood : ∀ n, N ≤ n → label (invasionEdge hd label n) ≤ y) :
    Tendsto (fun n ↦ invasionEmpiricalCDF label n y) atTop (nhds 1) := by
  have hzero : Tendsto (fun n : ℕ ↦ (N : ℝ) / n) atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (N : ℝ)
  have hlower : Tendsto (fun n : ℕ ↦ 1 - (N : ℝ) / n) atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub hzero
  apply hlower.squeeze' tendsto_const_nhds
  · filter_upwards [eventually_ge_atTop N, eventually_gt_atTop 0] with n hNn hn
    exact one_sub_natCast_div_le_invasionEmpiricalCDF hd label y N n hNn hn hgood
  · exact Filter.Eventually.of_forall fun n ↦ invasionEmpiricalCDF_le_one hd label n y

/-- Source-facing deterministic capture theorem: after the invaded state meets an infinite
`y`-sublevel cluster, its empirical distribution converges to one at `y`. -/
theorem invasionEmpiricalCDF_tendsto_one_of_state_meets_infiniteSublevelCluster
    {d : ℕ} (hd : 0 < d) (label : CubicEdge d → ℝ) (y : ℝ) (N : ℕ)
    {x : Cubic d} (hxS : x ∈ (invasionState label N).vertices)
    (hinfinite : (cubicOpenClusterFrom d (invasionSublevelConfiguration label y) x).Infinite) :
    Tendsto (fun n ↦ invasionEmpiricalCDF label n y) atTop (nhds 1) :=
  invasionEmpiricalCDF_tendsto_one_of_eventually_edge_label_le hd label y N
    (invasionEdge_eventually_label_le_of_state_meets_infiniteSublevelCluster
      hd label y N hxS hinfinite)

end Percolation
