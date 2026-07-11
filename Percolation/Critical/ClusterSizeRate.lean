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

#print axioms clusterSizeProbability_logRate_tendsto
#print axioms finiteClusterSizeProbability_le_rate
#print axioms clusterSizeDecayRate_pos_of_lt_critical

end Percolation
