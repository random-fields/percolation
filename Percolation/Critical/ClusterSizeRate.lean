import Percolation.Critical.AnchoredAnimals
import Percolation.Critical.QuasiSubadditive

/-!
# Exponential rate of exact cluster-size probabilities

This module formalizes Grimmett's Theorem 6.78.  Lemma 6.102 is converted into a genuinely
subadditive negative-log sequence, to which Mathlib's Fekete theorem applies.
-/

namespace Percolation

open Set MeasureTheory Filter Topology
open scoped BigOperators ENNReal unitInterval Topology

namespace CubicBondAnimal

/-- The one-vertex animal at the origin. -/
noncomputable def originAnimal (d : ℕ) : CubicBondAnimal d 1 where
  vertices := {cubicOrigin}
  vertices_subset := by
    intro x hx
    simp only [Finset.mem_singleton] at hx
    subst x
    rw [mem_cubicMetricBall_iff_l1Dist_le]
    simp
  edges := ∅
  edges_subset := by simp
  origin_mem := by simp
  vertices_card := by simp
  edge_endpoints := by simp
  connected := by
    intro x hx
    simp only [Finset.mem_singleton] at hx
    subst x
    refine ⟨SimpleGraph.Walk.nil, ?_⟩
    intro e he
    rw [mem_walkEdgeFinset_iff] at he
    simp at he

theorem originAnimal_isBottomLeftAnchored (d : ℕ) :
    (originAnimal d).IsBottomLeftAnchored := by
  have h := (originAnimal d).bottomLeft_mem
  change (originAnimal d).bottomLeft ∈ ({cubicOrigin} : Finset (Cubic d)) at h
  simpa [IsBottomLeftAnchored] using h

noncomputable def originAnchored (d : ℕ) : Anchored d 1 :=
  ⟨originAnimal d, originAnimal_isBottomLeftAnchored d⟩

theorem anchoredMass_nonneg (d n : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ anchoredMass d n p := by
  rw [anchoredMass]
  exact Finset.sum_nonneg fun A _ ↦
    mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (sub_nonneg.mpr hp1) _)

theorem anchoredMass_one_pos (d : ℕ) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    0 < anchoredMass d 1 p := by
  rw [anchoredMass]
  apply Finset.sum_pos'
  · intro A _
    exact mul_nonneg (pow_nonneg hp0.le _) (pow_nonneg (sub_nonneg.mpr hp1.le) _)
  · refine ⟨originAnchored d, Finset.mem_univ _, ?_⟩
    rw [weight]
    exact mul_pos (pow_pos hp0 _) (pow_pos (sub_pos.mpr hp1) _)

theorem anchoredMass_pos (d n : ℕ) {p : ℝ} (hd : 0 < d) (hn : 0 < n)
    (hp0 : 0 < p) (hp1 : p < 1) :
    0 < anchoredMass d n p := by
  induction n using Nat.case_strong_induction_on with
  | hz => omega
  | hi n ih =>
      by_cases hn0 : n = 0
      · subst n
        simpa using anchoredMass_one_pos d hp0 hp1
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
        have hmass : 0 < anchoredMass d n p := ih n (by omega) hnpos
        have hmul := anchoredMass_supermultiplicative d n 1 p hd hp0 hp1
        have hleft : 0 <
            p * (1 - p)⁻¹ ^ 2 * anchoredMass d n p * anchoredMass d 1 p := by
          exact mul_pos (mul_pos (mul_pos hp0 (pow_pos (inv_pos.mpr (sub_pos.mpr hp1)) _))
            hmass) (anchoredMass_one_pos d hp0 hp1)
        exact hleft.trans_le hmul

theorem finiteClusterSizeProbability_pos (d n : ℕ) (p : I)
    (hd : 0 < d) (hn : 0 < n) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    0 < finiteClusterSizeProbability d p n := by
  rw [finiteClusterSizeProbability_eq_nat_mul_anchoredMass]
  exact mul_pos (Nat.cast_pos.mpr hn) (anchoredMass_pos d n hd hn hp0 hp1)

end CubicBondAnimal

open CubicBondAnimal

/-- The constant-corrected normalized exact-size mass.  The value at zero is set to one so that
the supermultiplicative law holds on all natural indices. -/
noncomputable def clusterSizeFeketeWeight (d : ℕ) (p : I) (n : ℕ) : ℝ :=
  if n = 0 then 1 else
    (p : ℝ) * (1 - (p : ℝ))⁻¹ ^ 2 * anchoredMass d n p

theorem clusterSizeFeketeWeight_zero (d : ℕ) (p : I) :
    clusterSizeFeketeWeight d p 0 = 1 := by simp [clusterSizeFeketeWeight]

theorem clusterSizeFeketeWeight_of_pos (d : ℕ) (p : I) {n : ℕ} (hn : 0 < n) :
    clusterSizeFeketeWeight d p n =
      (p : ℝ) * (1 - (p : ℝ))⁻¹ ^ 2 * anchoredMass d n p := by
  simp [clusterSizeFeketeWeight, hn.ne']

theorem clusterSizeFeketeWeight_pos (d : ℕ) (p : I) (hd : 0 < d)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (n : ℕ) :
    0 < clusterSizeFeketeWeight d p n := by
  by_cases hn : n = 0
  · subst n
    simp [clusterSizeFeketeWeight]
  · rw [clusterSizeFeketeWeight_of_pos d p (Nat.pos_of_ne_zero hn)]
    exact mul_pos (mul_pos hp0 (pow_pos (inv_pos.mpr (sub_pos.mpr hp1)) _))
      (anchoredMass_pos d n hd (Nat.pos_of_ne_zero hn) hp0 hp1)

theorem clusterSizeFeketeWeight_supermultiplicative
    (d : ℕ) (p : I) (hd : 0 < d) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    ∀ m n, clusterSizeFeketeWeight d p m * clusterSizeFeketeWeight d p n ≤
      clusterSizeFeketeWeight d p (m + n) := by
  intro m n
  by_cases hm : m = 0
  · subst m
    simp [clusterSizeFeketeWeight]
  · by_cases hn : n = 0
    · subst n
      simp [clusterSizeFeketeWeight]
    · have hmpos := Nat.pos_of_ne_zero hm
      have hnpos := Nat.pos_of_ne_zero hn
      rw [clusterSizeFeketeWeight_of_pos d p hmpos,
        clusterSizeFeketeWeight_of_pos d p hnpos,
        clusterSizeFeketeWeight_of_pos d p (by omega)]
      let c : ℝ := (p : ℝ) * (1 - (p : ℝ))⁻¹ ^ 2
      have hc : 0 ≤ c := by positivity
      have h := anchoredMass_supermultiplicative d m n p hd hp0 hp1
      change (c * anchoredMass d m p) * (c * anchoredMass d n p) ≤
        c * anchoredMass d (m + n) p
      calc
        (c * anchoredMass d m p) * (c * anchoredMass d n p) =
            c * (c * anchoredMass d m p * anchoredMass d n p) := by ring
        _ ≤ c * anchoredMass d (m + n) p := mul_le_mul_of_nonneg_left h hc

/-- Subadditive negative logarithm of the corrected exact-size masses. -/
noncomputable def clusterSizeNegLog (d : ℕ) (p : I) (n : ℕ) : ℝ :=
  -Real.log (clusterSizeFeketeWeight d p n)

theorem clusterSizeNegLog_subadditive
    (d : ℕ) (p : I) (hd : 0 < d) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    Subadditive (clusterSizeNegLog d p) := by
  intro m n
  have hm := clusterSizeFeketeWeight_pos d p hd hp0 hp1 m
  have hn := clusterSizeFeketeWeight_pos d p hd hp0 hp1 n
  have hmul := clusterSizeFeketeWeight_supermultiplicative d p hd hp0 hp1 m n
  have hlog := Real.log_le_log (mul_pos hm hn) hmul
  rw [Real.log_mul hm.ne' hn.ne'] at hlog
  dsimp only [clusterSizeNegLog]
  linarith

theorem anchoredMass_le_one (d n : ℕ) (p : I) (hn : 0 < n) :
    anchoredMass d n p ≤ 1 := by
  have hprob := finiteClusterSizeProbability_le_one d p n
  rw [finiteClusterSizeProbability_eq_nat_mul_anchoredMass] at hprob
  have hmass := anchoredMass_nonneg d n (p := (p : ℝ)) p.2.1 p.2.2
  have hncast : (1 : ℝ) ≤ n := by exact_mod_cast hn
  nlinarith

theorem clusterSizeFeketeWeight_le_factor (d n : ℕ) (p : I) (hn : 0 < n) :
    clusterSizeFeketeWeight d p n ≤ (p : ℝ) * (1 - (p : ℝ))⁻¹ ^ 2 := by
  rw [clusterSizeFeketeWeight_of_pos d p hn]
  exact mul_le_of_le_one_right (mul_nonneg p.2.1 (sq_nonneg _))
    (anchoredMass_le_one d n p hn)

theorem clusterSizeNegLog_div_bddBelow
    (d : ℕ) (p : I) (hd : 0 < d) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    BddBelow (Set.range fun n : ℕ ↦ clusterSizeNegLog d p n / n) := by
  let c : ℝ := (p : ℝ) * (1 - (p : ℝ))⁻¹ ^ 2
  let L : ℝ := -|Real.log c|
  have hc : 0 < c := by
    exact mul_pos hp0 (pow_pos (inv_pos.mpr (sub_pos.mpr hp1)) _)
  refine ⟨L, ?_⟩
  rintro _ ⟨n, rfl⟩
  by_cases hn : n = 0
  · subst n
    simp [clusterSizeNegLog, clusterSizeFeketeWeight, L]
  · have hnpos := Nat.pos_of_ne_zero hn
    have hu := clusterSizeFeketeWeight_pos d p hd hp0 hp1 n
    have hule : clusterSizeFeketeWeight d p n ≤ c :=
      clusterSizeFeketeWeight_le_factor d n p hnpos
    have hlog := Real.log_le_log hu hule
    have hbase : L ≤ clusterSizeNegLog d p n := by
      dsimp only [L, clusterSizeNegLog]
      have habs := le_abs_self (Real.log c)
      linarith
    have hL : L ≤ 0 := neg_nonpos.mpr (abs_nonneg _)
    by_cases ha : 0 ≤ clusterSizeNegLog d p n
    · exact hL.trans (div_nonneg ha (Nat.cast_nonneg n))
    · have hncast : (1 : ℝ) ≤ n := by exact_mod_cast hnpos
      have hncastPos : (0 : ℝ) < n := by positivity
      have hdiv : clusterSizeNegLog d p n ≤ clusterSizeNegLog d p n / n := by
        rw [le_div_iff₀ hncastPos]
        have hale : clusterSizeNegLog d p n ≤ 0 := le_of_not_ge ha
        nlinarith
      exact hbase.trans hdiv

/-- Exponential decay rate `ζ(p)` of exact finite-cluster probabilities. -/
noncomputable def clusterSizeDecayRate (d : ℕ) (p : I) : ℝ :=
  sInf ((fun n : ℕ ↦ clusterSizeNegLog d p n / n) '' Set.Ici 1)

theorem clusterSizeNegLog_div_tendsto
    (d : ℕ) (p : I) (hd : 0 < d) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    Tendsto (fun n : ℕ ↦ clusterSizeNegLog d p n / n) atTop
      (𝓝 (clusterSizeDecayRate d p)) := by
  have hsub := clusterSizeNegLog_subadditive d p hd hp0 hp1
  have hlim := hsub.tendsto_lim (clusterSizeNegLog_div_bddBelow d p hd hp0 hp1)
  simpa [clusterSizeDecayRate, Subadditive.lim] using hlim

theorem tendsto_log_natCast_div_natCast :
    Tendsto (fun n : ℕ ↦ Real.log (n : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
  have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
    tendsto_natCast_atTop_atTop
  simpa using h

/-- The exact-size part of Theorem 6.78: `-n⁻¹ log P(|C|=n)` converges. -/
theorem clusterSizeProbability_logRate_tendsto
    (d : ℕ) (p : I) (hd : 0 < d) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    Tendsto (fun n : ℕ ↦
      -Real.log (finiteClusterSizeProbability d p n) / n) atTop
      (𝓝 (clusterSizeDecayRate d p)) := by
  let c : ℝ := (p : ℝ) * (1 - (p : ℝ))⁻¹ ^ 2
  have hc : 0 < c := mul_pos hp0 (pow_pos (inv_pos.mpr (sub_pos.mpr hp1)) _)
  have hmain := clusterSizeNegLog_div_tendsto d p hd hp0 hp1
  have hconst : Tendsto (fun n : ℕ ↦ Real.log c / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have herr : Tendsto (fun n : ℕ ↦
      (Real.log c - Real.log (n : ℝ)) / (n : ℝ)) atTop (𝓝 0) := by
    convert hconst.sub tendsto_log_natCast_div_natCast using 1
    · funext n
      ring
    · simp
  have hsum := hmain.add herr
  have hevent : ∀ᶠ n : ℕ in atTop,
      clusterSizeNegLog d p n / n +
          (Real.log c - Real.log (n : ℝ)) / n =
        -Real.log (finiteClusterSizeProbability d p n) / n := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hnpos : 0 < n := zero_lt_one.trans_le hn
    have hprob := finiteClusterSizeProbability_pos d n p hd hnpos hp0 hp1
    rw [clusterSizeNegLog, clusterSizeFeketeWeight_of_pos d p hnpos,
      anchoredMass_eq_finiteClusterSizeProbability_div d n p hnpos]
    change (-Real.log (c * (finiteClusterSizeProbability d p n / n)) / n +
        (Real.log c - Real.log (n : ℝ)) / n) = _
    rw [Real.log_mul hc.ne' (div_ne_zero hprob.ne' (Nat.cast_ne_zero.mpr hnpos.ne')),
      Real.log_div hprob.ne' (Nat.cast_ne_zero.mpr hnpos.ne')]
    field_simp
    ring
  simpa using hsum.congr' hevent

/-- Fekete's finite-index estimate for the corrected normalized mass. -/
theorem clusterSizeFeketeWeight_le_exp_rate
    (d : ℕ) (p : I) (hd : 0 < d) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    {n : ℕ} (hn : 0 < n) :
    clusterSizeFeketeWeight d p n ≤
      Real.exp (-(n : ℝ) * clusterSizeDecayRate d p) := by
  have hsub := clusterSizeNegLog_subadditive d p hd hp0 hp1
  have hle := hsub.lim_le_div (clusterSizeNegLog_div_bddBelow d p hd hp0 hp1) hn.ne'
  rw [Subadditive.lim] at hle
  have hrate : clusterSizeDecayRate d p ≤ clusterSizeNegLog d p n / n := by
    simpa [clusterSizeDecayRate] using hle
  have hnreal : (0 : ℝ) < n := by positivity
  have hmul := (le_div_iff₀ hnreal).mp hrate
  have hu := clusterSizeFeketeWeight_pos d p hd hp0 hp1 n
  apply (Real.log_le_iff_le_exp hu).mp
  dsimp only [clusterSizeNegLog] at hmul
  nlinarith

/-- Grimmett's finite-index bound (6.80), including its exact polynomial prefactor. -/
theorem finiteClusterSizeProbability_le_rate
    (d : ℕ) (p : I) (hd : 0 < d) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    {n : ℕ} (hn : 0 < n) :
    finiteClusterSizeProbability d p n ≤
      (n : ℝ) * (p : ℝ)⁻¹ * (1 - (p : ℝ)) ^ 2 *
        Real.exp (-(n : ℝ) * clusterSizeDecayRate d p) := by
  let c : ℝ := (p : ℝ) * (1 - (p : ℝ))⁻¹ ^ 2
  have hc : 0 < c := mul_pos hp0 (pow_pos (inv_pos.mpr (sub_pos.mpr hp1)) _)
  have hnreal : (0 : ℝ) < n := by positivity
  have h := clusterSizeFeketeWeight_le_exp_rate d p hd hp0 hp1 hn
  rw [clusterSizeFeketeWeight_of_pos d p hn,
    anchoredMass_eq_finiteClusterSizeProbability_div d n p hn] at h
  change c * (finiteClusterSizeProbability d p n / n) ≤ _ at h
  calc
    finiteClusterSizeProbability d p n =
        ((n : ℝ) / c) * (c * (finiteClusterSizeProbability d p n / n)) := by
      field_simp
    _ ≤ ((n : ℝ) / c) * Real.exp (-(n : ℝ) * clusterSizeDecayRate d p) :=
      mul_le_mul_of_nonneg_left h (div_nonneg hnreal.le hc.le)
    _ = (n : ℝ) * (p : ℝ)⁻¹ * (1 - (p : ℝ)) ^ 2 *
        Real.exp (-(n : ℝ) * clusterSizeDecayRate d p) := by
      dsimp only [c]
      field_simp

theorem finiteClusterSizeProbability_le_clusterSizeAtLeast
    (d : ℕ) (p : I) (n : ℕ) :
    finiteClusterSizeProbability d p n ≤ clusterSizeAtLeast d p n := by
  unfold finiteClusterSizeProbability clusterSizeAtLeast
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro ω hω
  change clusterSizeENNReal d ω = (n : ℝ≥0∞) at hω
  change (n : ℝ≥0∞) ≤ clusterSizeENNReal d ω
  rw [hω]

theorem clusterSizeDecayRate_pos_of_lt_critical
    (d : ℕ) (hd : 2 ≤ d) (p : I) (hp0 : 0 < (p : ℝ))
    (hp : (p : ℝ) < cubicCriticalProbability d) :
    0 < clusterSizeDecayRate d p := by
  have hp1 : (p : ℝ) < 1 := hp.trans (cubicCriticalProbability_pos_lt_one hd).2
  obtain ⟨lambda, hlambda, N, hN⟩ :=
    clusterSizeAtLeast_exponential_decay_of_lt_critical d hd p hp0 hp
  have hevent : ∀ᶠ n : ℕ in atTop,
      lambda ≤ -Real.log (finiteClusterSizeProbability d p n) / n := by
    filter_upwards [eventually_ge_atTop (max N 1)] with n hn
    have hnN : N ≤ n := (le_max_left N 1).trans hn
    have hnpos : 0 < n := zero_lt_one.trans_le ((le_max_right N 1).trans hn)
    have hprob := finiteClusterSizeProbability_pos d n p (Nat.zero_lt_of_lt hd) hnpos hp0 hp1
    have hle := (finiteClusterSizeProbability_le_clusterSizeAtLeast d p n).trans (hN n hnN)
    have hlog := Real.log_le_log hprob hle
    rw [Real.log_exp] at hlog
    have hnreal : (0 : ℝ) < n := by positivity
    apply (le_div_iff₀ hnreal).mpr
    nlinarith
  have hconst : Tendsto (fun _ : ℕ ↦ lambda) atTop (𝓝 lambda) := tendsto_const_nhds
  have hlimit := clusterSizeProbability_logRate_tendsto d p (Nat.zero_lt_of_lt hd) hp0 hp1
  have hle := le_of_tendsto_of_tendsto hconst hlimit hevent
  exact hlambda.trans_le hle

/-- Finite-cluster tail `Σ_{k≥n} P(|C|=k)`.  Infinite clusters are deliberately excluded. -/
noncomputable def finiteClusterSizeTail (d : ℕ) (p : I) (n : ℕ) : ℝ :=
  ∑' k : ℕ, finiteClusterSizeProbability d p (k + n)

theorem summable_finiteClusterSizeProbability_nat_add (d : ℕ) (p : I) (n : ℕ) :
    Summable (fun k : ℕ ↦ finiteClusterSizeProbability d p (k + n)) := by
  simpa [Nat.add_comm] using
    (summable_nat_add_iff n).mpr (summable_finiteClusterSizeProbability d p)

theorem finiteClusterSizeProbability_le_finiteClusterSizeTail
    (d : ℕ) (p : I) (n : ℕ) :
    finiteClusterSizeProbability d p n ≤ finiteClusterSizeTail d p n := by
  let f : ℕ → ℝ := fun k ↦ finiteClusterSizeProbability d p (k + n)
  have hf : Summable f := summable_finiteClusterSizeProbability_nat_add d p n
  have hsum := hf.sum_le_tsum ({0} : Finset ℕ) (fun k _ ↦
    finiteClusterSizeProbability_nonneg d p (k + n))
  simpa [finiteClusterSizeTail, f] using hsum

theorem finiteClusterSizeTail_pos
    (d : ℕ) (p : I) (hd : 0 < d) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    {n : ℕ} (hn : 0 < n) :
    0 < finiteClusterSizeTail d p n :=
  (finiteClusterSizeProbability_pos d n p hd hn hp0 hp1).trans_le
    (finiteClusterSizeProbability_le_finiteClusterSizeTail d p n)

noncomputable def geometricFirstMoment (r : ℝ) : ℝ :=
  ∑' k : ℕ, (k + 1 : ℝ) * r ^ k

theorem summable_geometricFirstMoment {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun k : ℕ ↦ (k + 1 : ℝ) * r ^ k) := by
  have hrnorm : ‖r‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hr0]
  have hmul := (hasSum_coe_mul_geometric_of_norm_lt_one hrnorm).summable
  have hgeom := summable_geometric_of_norm_lt_one hrnorm
  convert hmul.add hgeom using 1
  ext k
  ring

theorem geometricFirstMoment_pos {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    0 < geometricFirstMoment r := by
  rw [geometricFirstMoment]
  have hs := summable_geometricFirstMoment hr0 hr1
  apply lt_of_lt_of_le zero_lt_one
  have hle := hs.sum_le_tsum ({0} : Finset ℕ) (fun k _ ↦ by positivity)
  simpa using hle

theorem finiteClusterSizeTail_le_rate_prefactor
    (d : ℕ) (p : I) (hd : 0 < d) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hzeta : 0 < clusterSizeDecayRate d p) {n : ℕ} (hn : 0 < n) :
    finiteClusterSizeTail d p n ≤
      (p : ℝ)⁻¹ * (1 - (p : ℝ)) ^ 2 *
        geometricFirstMoment (Real.exp (-clusterSizeDecayRate d p)) * (n + 1 : ℝ) *
          Real.exp (-(n : ℝ) * clusterSizeDecayRate d p) := by
  let zeta := clusterSizeDecayRate d p
  let r := Real.exp (-zeta)
  let K := (p : ℝ)⁻¹ * (1 - (p : ℝ)) ^ 2
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := by
    dsimp only [r]
    rw [Real.exp_lt_one_iff]
    linarith
  have hK : 0 ≤ K := mul_nonneg (inv_nonneg.mpr hp0.le) (sq_nonneg _)
  have hsource := summable_finiteClusterSizeProbability_nat_add d p n
  have hmoment := summable_geometricFirstMoment hr0 hr1
  have htarget : Summable (fun k : ℕ ↦
      (K * (n + 1 : ℝ) * r ^ n) * ((k + 1 : ℝ) * r ^ k)) :=
    hmoment.mul_left _
  have hterm (k : ℕ) :
      finiteClusterSizeProbability d p (k + n) ≤
        (K * (n + 1 : ℝ) * r ^ n) * ((k + 1 : ℝ) * r ^ k) := by
    have hkn : 0 < k + n := by omega
    have hrate := finiteClusterSizeProbability_le_rate d p hd hp0 hp1 hkn
    have hexp : Real.exp (-(k + n : ℝ) * zeta) = r ^ (k + n) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    have hExpTerm : Real.exp (-((k + n : ℕ) : ℝ) * clusterSizeDecayRate d p) =
        r ^ (k + n) := by
      rw [Nat.cast_add]
      exact hexp
    rw [hExpTerm, pow_add] at hrate
    have hrate' : finiteClusterSizeProbability d p (k + n) ≤
        (((k : ℝ) + (n : ℝ)) * K) * r ^ k * r ^ n := by
      dsimp only [K]
      rw [← Nat.cast_add]
      convert hrate using 1 <;> ring
    change finiteClusterSizeProbability d p (k + n) ≤
      (K * (n + 1 : ℝ) * r ^ n) * ((k + 1 : ℝ) * r ^ k)
    have hcast : (k + n : ℝ) ≤ (k + 1 : ℝ) * (n + 1 : ℝ) := by
      nlinarith
    calc
      finiteClusterSizeProbability d p (k + n) ≤
          ((k + n : ℝ) * K) * r ^ k * r ^ n := hrate'
      _ ≤ (((k + 1 : ℝ) * (n + 1 : ℝ)) * K) * r ^ k * r ^ n := by
        gcongr
      _ = (K * (n + 1 : ℝ) * r ^ n) * ((k + 1 : ℝ) * r ^ k) := by ring
  calc
    finiteClusterSizeTail d p n =
        ∑' k : ℕ, finiteClusterSizeProbability d p (k + n) := rfl
    _ ≤ ∑' k : ℕ, (K * (n + 1 : ℝ) * r ^ n) * ((k + 1 : ℝ) * r ^ k) :=
      hsource.tsum_le_tsum hterm htarget
    _ = (K * (n + 1 : ℝ) * r ^ n) * geometricFirstMoment r := by
      rw [hmoment.tsum_mul_left]
      rfl
    _ = (p : ℝ)⁻¹ * (1 - (p : ℝ)) ^ 2 * geometricFirstMoment r * (n + 1 : ℝ) *
        Real.exp (-(n : ℝ) * clusterSizeDecayRate d p) := by
      have hpow : r ^ n = Real.exp (-(n : ℝ) * zeta) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      rw [hpow]
      dsimp only [K, zeta]
      ring

theorem tendsto_log_natCast_succ_div_natCast :
    Tendsto (fun n : ℕ ↦ Real.log ((n + 1 : ℕ) : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
  have hupper : Tendsto (fun n : ℕ ↦
      (Real.log 2 + Real.log (n : ℝ)) / (n : ℝ)) atTop (𝓝 0) := by
    have hc := tendsto_const_div_atTop_nhds_zero_nat (Real.log 2)
    convert hc.add tendsto_log_natCast_div_natCast using 1
    · funext n
      ring
    · simp
  have hnonneg : ∀ᶠ n : ℕ in atTop,
      0 ≤ Real.log ((n + 1 : ℕ) : ℝ) / (n : ℝ) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast Nat.succ_pos n)) (by positivity)
  have hle : ∀ᶠ n : ℕ in atTop,
      Real.log ((n + 1 : ℕ) : ℝ) / (n : ℝ) ≤
        (Real.log 2 + Real.log (n : ℝ)) / (n : ℝ) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hnpos : 0 < n := zero_lt_one.trans_le hn
    have hcast : (((n + 1 : ℕ) : ℝ)) ≤ 2 * (n : ℝ) := by exact_mod_cast (by omega : n + 1 ≤ 2 * n)
    have hlog := Real.log_le_log (by positivity : (0 : ℝ) < ((n + 1 : ℕ) : ℝ)) hcast
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (Nat.cast_ne_zero.mpr hnpos.ne')] at hlog
    exact div_le_div_of_nonneg_right hlog (by positivity)
  exact squeeze_zero' hnonneg hle hupper

/-- The finite-cluster tail has the same logarithmic decay rate as the exact-size law (6.82). -/
theorem finiteClusterSizeTail_logRate_tendsto
    (d : ℕ) (hd : 2 ≤ d) (p : I) (hp0 : 0 < (p : ℝ))
    (hp : (p : ℝ) < cubicCriticalProbability d) :
    Tendsto (fun n : ℕ ↦ -Real.log (finiteClusterSizeTail d p n) / n) atTop
      (𝓝 (clusterSizeDecayRate d p)) := by
  let zeta := clusterSizeDecayRate d p
  let r := Real.exp (-zeta)
  let D := (p : ℝ)⁻¹ * (1 - (p : ℝ)) ^ 2 * geometricFirstMoment r
  have hp1 : (p : ℝ) < 1 := hp.trans (cubicCriticalProbability_pos_lt_one hd).2
  have hzeta : 0 < zeta := clusterSizeDecayRate_pos_of_lt_critical d hd p hp0 hp
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := by
    dsimp only [r]
    rw [Real.exp_lt_one_iff]
    linarith
  have hD : 0 < D := mul_pos
    (mul_pos (inv_pos.mpr hp0) (pow_pos (sub_pos.mpr hp1) _))
    (geometricFirstMoment_pos hr0 hr1)
  have hlogPref : Tendsto (fun n : ℕ ↦
      Real.log (D * (n + 1 : ℝ)) / (n : ℝ)) atTop (𝓝 0) := by
    have hconst := tendsto_const_div_atTop_nhds_zero_nat (Real.log D)
    have hadd := hconst.add tendsto_log_natCast_succ_div_natCast
    have hevent : ∀ᶠ n : ℕ in atTop,
        Real.log D / (n : ℝ) + Real.log ((n + 1 : ℕ) : ℝ) / (n : ℝ) =
          Real.log (D * (n + 1 : ℝ)) / (n : ℝ) := by
      filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
      rw [Real.log_mul hD.ne' (by positivity : (n + 1 : ℝ) ≠ 0)]
      simp only [Nat.cast_add, Nat.cast_one]
      ring
    simpa using hadd.congr' hevent
  have hlowerT : Tendsto (fun n : ℕ ↦
      zeta - Real.log (D * (n + 1 : ℝ)) / (n : ℝ)) atTop (𝓝 zeta) := by
    simpa using tendsto_const_nhds.sub hlogPref
  have hupperT := clusterSizeProbability_logRate_tendsto d p
    (Nat.zero_lt_of_lt hd) hp0 hp1
  have hlower : ∀ᶠ n : ℕ in atTop,
      zeta - Real.log (D * (n + 1 : ℝ)) / (n : ℝ) ≤
        -Real.log (finiteClusterSizeTail d p n) / n := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hnpos : 0 < n := zero_lt_one.trans_le hn
    have htail := finiteClusterSizeTail_pos d p (Nat.zero_lt_of_lt hd) hp0 hp1 hnpos
    have hbound := finiteClusterSizeTail_le_rate_prefactor d p
      (Nat.zero_lt_of_lt hd) hp0 hp1 hzeta hnpos
    change finiteClusterSizeTail d p n ≤
      D * (n + 1 : ℝ) * Real.exp (-(n : ℝ) * zeta) at hbound
    have hright : 0 < D * (n + 1 : ℝ) * Real.exp (-(n : ℝ) * zeta) := by positivity
    have hlog := Real.log_le_log htail hbound
    rw [Real.log_mul (mul_ne_zero hD.ne' (by positivity : (n + 1 : ℝ) ≠ 0))
        (Real.exp_ne_zero _), Real.log_mul hD.ne' (by positivity : (n + 1 : ℝ) ≠ 0),
      Real.log_exp] at hlog
    have hnreal : (0 : ℝ) < n := by positivity
    rw [Real.log_mul hD.ne' (by positivity : (n + 1 : ℝ) ≠ 0)]
    rw [le_div_iff₀ hnreal]
    field_simp
    nlinarith
  have hupper : ∀ᶠ n : ℕ in atTop,
      -Real.log (finiteClusterSizeTail d p n) / n ≤
        -Real.log (finiteClusterSizeProbability d p n) / n := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hnpos : 0 < n := zero_lt_one.trans_le hn
    have hprob := finiteClusterSizeProbability_pos d n p (Nat.zero_lt_of_lt hd) hnpos hp0 hp1
    have hle := finiteClusterSizeProbability_le_finiteClusterSizeTail d p n
    have hlog := Real.log_le_log hprob hle
    exact div_le_div_of_nonneg_right (neg_le_neg hlog) (by positivity)
  exact hlowerT.squeeze' hupperT hlower hupper

theorem finiteClusterAtLeastEvent_eq_iUnion_size (d n : ℕ) :
    finiteClusterEvent d ∩ clusterSizeAtLeastEvent d n =
      ⋃ k : ℕ, finiteClusterSizeEvent d (k + n) := by
  ext ω
  constructor
  · rintro ⟨hfinite, hAtLeast⟩
    let j := (cubicOpenCluster d ω).ncard
    have hsize : clusterSizeENNReal d ω = (j : ℝ≥0∞) :=
      clusterSizeENNReal_eq_ncard_of_finite hfinite
    have hnj : n ≤ j := by
      change (n : ℝ≥0∞) ≤ clusterSizeENNReal d ω at hAtLeast
      rw [hsize] at hAtLeast
      exact_mod_cast hAtLeast
    apply Set.mem_iUnion.mpr
    refine ⟨j - n, ?_⟩
    change clusterSizeENNReal d ω = ((j - n + n : ℕ) : ℝ≥0∞)
    rw [hsize]
    congr 1
    omega
  · intro hω
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hω
    have hfinite : (cubicOpenCluster d ω).Finite := by
      by_contra hinfinite
      have htop := (clusterSizeENNReal_eq_top_iff d ω).mpr hinfinite
      change clusterSizeENNReal d ω = ((k + n : ℕ) : ℝ≥0∞) at hk
      exact ENNReal.natCast_ne_top (k + n) (hk.symm.trans htop)
    refine ⟨hfinite, ?_⟩
    change (n : ℝ≥0∞) ≤ clusterSizeENNReal d ω
    change clusterSizeENNReal d ω = ((k + n : ℕ) : ℝ≥0∞) at hk
    rw [hk]
    exact_mod_cast Nat.le_add_left n k

theorem finiteClusterSizeTail_eq_measure_inter (d : ℕ) (p : I) (n : ℕ) :
    finiteClusterSizeTail d p n =
      (bernoulliBondMeasure d p).real
        (finiteClusterEvent d ∩ clusterSizeAtLeastEvent d n) := by
  rw [finiteClusterAtLeastEvent_eq_iUnion_size]
  unfold finiteClusterSizeTail finiteClusterSizeProbability
  have hpw : Pairwise (Function.onFun Disjoint fun k : ℕ ↦
      finiteClusterSizeEvent d (k + n)) := by
    intro k l hkl
    exact pairwiseDisjoint_finiteClusterSizeEvent d (by omega)
  have hmeas : ∀ k : ℕ, MeasurableSet (finiteClusterSizeEvent d (k + n)) :=
    fun k ↦ measurableSet_finiteClusterSizeEvent d (k + n)
  rw [measureReal_def,
    measure_iUnion (μ := bernoulliBondMeasure d p) hpw hmeas,
    ENNReal.tsum_toReal_eq]
  · rfl
  · intro k
    exact measure_ne_top _ _

theorem clusterSizeAtLeast_eq_finiteClusterSizeTail_of_theta_eq_zero
    (d : ℕ) (p : I) (n : ℕ) (htheta : theta d p = 0) :
    clusterSizeAtLeast d p n = finiteClusterSizeTail d p n := by
  let μ := bernoulliBondMeasure d p
  let A := clusterSizeAtLeastEvent d n
  let F := finiteClusterEvent d
  let InfEvent := hasInfiniteOpenCluster d
  have hsub : A ⊆ (F ∩ A) ∪ InfEvent := by
    intro ω hω
    by_cases hfinite : ω ∈ F
    · exact Or.inl ⟨hfinite, hω⟩
    · exact Or.inr (by
        change ω ∉ finiteClusterEvent d at hfinite
        rw [finiteClusterEvent_eq_compl_infinite] at hfinite
        simpa using hfinite)
  have hAF : μ.real A ≤ μ.real (F ∩ A) := by
    calc
      μ.real A ≤ μ.real ((F ∩ A) ∪ InfEvent) := measureReal_mono hsub
      _ ≤ μ.real (F ∩ A) + μ.real InfEvent := measureReal_union_le _ _
      _ = μ.real (F ∩ A) := by
        change _ + theta d p = _
        rw [htheta, add_zero]
  have hFA : μ.real (F ∩ A) ≤ μ.real A :=
    measureReal_mono (Set.inter_subset_right)
  rw [clusterSizeAtLeast, finiteClusterSizeTail_eq_measure_inter]
  exact le_antisymm hAF hFA

theorem hasOpenPathOfLengthAtLeast_subset_clusterSizeAtLeastEvent (d n : ℕ) :
    {ω : EdgeConfiguration d | hasOpenPathOfLengthAtLeast d ω n} ⊆
      clusterSizeAtLeastEvent d (n + 1) := by
  rintro ω ⟨v, w, hpath, hlen, hopen⟩
  have hsub : (w.support.toFinset : Set (Cubic d)) ⊆ cubicOpenCluster d ω := by
    intro x hx
    exact mem_cubicOpenClusterFrom_of_mem_support hopen (by simpa using hx)
  have hencard := Set.encard_mono hsub
  have hsupport : w.support.toFinset.card = w.length + 1 := by
    rw [List.toFinset_card_of_nodup hpath.support_nodup, SimpleGraph.Walk.length_support]
  have hnat : n + 1 ≤ w.support.toFinset.card := by omega
  have henat : ((n + 1 : ℕ) : ℕ∞) ≤ (cubicOpenCluster d ω).encard := by
    have h₁ : ((n + 1 : ℕ) : ℕ∞) ≤ (w.support.toFinset.card : ℕ∞) := by
      exact_mod_cast hnat
    have h₂ : (w.support.toFinset.card : ℕ∞) ≤ (cubicOpenCluster d ω).encard := by
      simpa only [Set.encard_coe_eq_coe_finsetCard] using hencard
    exact h₁.trans h₂
  change ((n + 1 : ℕ) : ℝ≥0∞) ≤ clusterSizeENNReal d ω
  rw [clusterSizeENNReal_eq_encard]
  simpa using ENat.toENNReal_mono henat

theorem boxRadiusTail_le_clusterSizeAtLeast_succ (d : ℕ) (p : I) (n : ℕ) :
    boxRadiusTail d p n ≤ clusterSizeAtLeast d p (n + 1) := by
  unfold boxRadiusTail clusterSizeAtLeast
  exact measureReal_mono
    ((boxRadiusConnectionEvent_subset_hasOpenPathOfLengthAtLeast d n).trans
      (hasOpenPathOfLengthAtLeast_subset_clusterSizeAtLeastEvent d n))
    (measure_ne_top _ _)

theorem boxRadiusTail_le_finiteClusterSizeTail_succ_of_lt_critical
    (d : ℕ) (p : I) (n : ℕ) (hp : (p : ℝ) < cubicCriticalProbability d) :
    boxRadiusTail d p n ≤ finiteClusterSizeTail d p (n + 1) := by
  rw [← clusterSizeAtLeast_eq_finiteClusterSizeTail_of_theta_eq_zero d p (n + 1)
    (theta_eq_zero_of_lt_criticalProbability hp)]
  exact boxRadiusTail_le_clusterSizeAtLeast_succ d p n

theorem finiteClusterSizeTail_succ_logRate_tendsto
    (d : ℕ) (hd : 2 ≤ d) (p : I) (hp0 : 0 < (p : ℝ))
    (hp : (p : ℝ) < cubicCriticalProbability d) :
    Tendsto (fun n : ℕ ↦ -Real.log (finiteClusterSizeTail d p (n + 1)) / n) atTop
      (𝓝 (clusterSizeDecayRate d p)) := by
  have htail := finiteClusterSizeTail_logRate_tendsto d hd p hp0 hp
  have hshift := htail.comp (tendsto_add_atTop_nat 1)
  have hratio : Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ) / (n : ℝ)) atTop (𝓝 1) := by
    have hadd : Tendsto (fun n : ℕ ↦ (1 : ℝ) + 1 / (n : ℝ)) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds.add
        (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)))
    have hevent : ∀ᶠ n : ℕ in atTop,
        (1 : ℝ) + 1 / (n : ℝ) = ((n + 1 : ℕ) : ℝ) / (n : ℝ) := by
      filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
      have hn0 : (n : ℝ) ≠ 0 := by positivity
      field_simp
      norm_cast
    exact hadd.congr' hevent
  have hmul := hshift.mul hratio
  have hevent : ∀ᶠ n : ℕ in atTop,
      (((fun k : ℕ ↦ -Real.log (finiteClusterSizeTail d p k) / k) ∘
          fun a ↦ a + 1) n) * (((n + 1 : ℕ) : ℝ) / (n : ℝ)) =
        -Real.log (finiteClusterSizeTail d p (n + 1)) / n := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    have hs0 : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    simp only [Function.comp_apply]
    field_simp [hs0]
  simpa using hmul.congr' hevent

/-- Equation (6.83): the exact cluster-size decay rate is no larger than the box-radius rate. -/
theorem clusterSizeDecayRate_le_boxRadiusDecayRate
    (d : ℕ) (hd : 2 ≤ d) (p : I) (hp0 : 0 < (p : ℝ))
    (hp : (p : ℝ) < cubicCriticalProbability d) :
    clusterSizeDecayRate d p ≤ boxRadiusDecayRate d p := by
  have htail := finiteClusterSizeTail_succ_logRate_tendsto d hd p hp0 hp
  have hbox := boxRadiusTail_logRate_tendsto d (Nat.zero_lt_of_lt hd) p hp0
  apply le_of_tendsto_of_tendsto htail hbox
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hboxPos := boxRadiusTail_pos_of_pos_density (Nat.zero_lt_of_lt hd) hp0 (n := n)
  have hle := boxRadiusTail_le_finiteClusterSizeTail_succ_of_lt_critical d p n hp
  have hlog := Real.log_le_log hboxPos hle
  exact div_le_div_of_nonneg_right (neg_le_neg hlog) (by positivity)

#print axioms clusterSizeProbability_logRate_tendsto
#print axioms finiteClusterSizeProbability_le_rate
#print axioms clusterSizeDecayRate_pos_of_lt_critical
#print axioms finiteClusterSizeTail_logRate_tendsto
#print axioms clusterSizeDecayRate_le_boxRadiusDecayRate

end Percolation
