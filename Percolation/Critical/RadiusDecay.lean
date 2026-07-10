import Percolation.Critical.MenshikovBootstrap
import Percolation.Critical.RadiusBlock
import Percolation.Critical.SusceptibilityThreshold
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Exponential decay of the radius tail

This file first records the block proof of exponential decay from finite
susceptibility.  It supplies the exact conclusion of Grimmett's Theorem 5.4 and
will remain as an independent cross-check when the Menshikov derivation through
Lemmas 5.12, 5.17, 5.22, and 5.24 is closed.
-/

namespace Percolation

open MeasureTheory
open Filter
open scoped unitInterval ENNReal BigOperators

private theorem one_div_sqrt_succ_le (i : ℕ) :
    1 / Real.sqrt (i + 1 : ℕ) ≤
      2 * (Real.sqrt (i + 1 : ℕ) - Real.sqrt i) := by
  have hi : (0 : ℝ) ≤ i := by positivity
  have his : (0 : ℝ) < (i + 1 : ℕ) := by exact_mod_cast Nat.succ_pos i
  have hspos : 0 < Real.sqrt (i + 1 : ℕ) := Real.sqrt_pos.2 his
  have hsmono : Real.sqrt i ≤ Real.sqrt (i + 1 : ℕ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_succ i)
  have hcast : ((i + 1 : ℕ) : ℝ) = (i : ℝ) + 1 := by norm_num
  rw [div_le_iff₀ hspos]
  nlinarith [Real.sq_sqrt hi, Real.sq_sqrt his.le]

private theorem sum_one_div_sqrt_succ_le (n : ℕ) :
    (∑ i ∈ Finset.range n, 1 / Real.sqrt (i + 1 : ℕ)) ≤ 2 * Real.sqrt n := by
  have htel : (∑ i ∈ Finset.range n,
      (Real.sqrt (i + 1 : ℕ) - Real.sqrt i)) = Real.sqrt n - Real.sqrt 0 := by
    simpa using Finset.sum_range_sub (fun i : ℕ ↦ Real.sqrt i) n
  calc
    (∑ i ∈ Finset.range n, 1 / Real.sqrt (i + 1 : ℕ)) ≤
        ∑ i ∈ Finset.range n,
          2 * (Real.sqrt (i + 1 : ℕ) - Real.sqrt i) := by
      apply Finset.sum_le_sum
      intro i _hi
      exact one_div_sqrt_succ_le i
    _ = 2 * Real.sqrt n := by
      rw [← Finset.mul_sum, htel]
      simp

/-- Equation (5.26): Lemma 5.24 makes the radius-tail partial sums grow at most like
the square root of the radius. -/
theorem radiusTailPartialSum_le_sqrt
    {d : ℕ} {p : I} {delta : ℝ} (hdelta : 0 ≤ delta)
    (hbound : ∀ n : ℕ, 1 ≤ n → radiusTail d p n ≤ delta / Real.sqrt n) :
    ∀ n : ℕ, 1 ≤ n →
      radiusTailPartialSum d p n ≤ (1 + 2 * delta) * Real.sqrt n := by
  intro n hn
  have hsqrtn : 1 ≤ Real.sqrt n := by
    have hs := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ n by exact_mod_cast hn)
    simpa using hs
  have htail : (∑ i ∈ Finset.range n, radiusTail d p (i + 1)) ≤
      delta * ∑ i ∈ Finset.range n, 1 / Real.sqrt (i + 1 : ℕ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _hi
    simpa [div_eq_mul_inv, mul_assoc] using hbound (i + 1) (by omega)
  have hinvsum := sum_one_div_sqrt_succ_le n
  rw [radiusTailPartialSum, Finset.sum_range_succ']
  rw [radiusTail_zero]
  calc
    (∑ i ∈ Finset.range n, radiusTail d p (i + 1)) + 1 ≤
        delta * (∑ i ∈ Finset.range n, 1 / Real.sqrt (i + 1 : ℕ)) + 1 := by
      linarith
    _ ≤ delta * (2 * Real.sqrt n) + 1 := by
      gcongr
    _ ≤ (1 + 2 * delta) * Real.sqrt n := by
      nlinarith

private theorem summable_exp_neg_mul_sqrt {a : ℝ} (ha : 0 < a) :
    Summable fun n : ℕ ↦ Real.exp (-a * Real.sqrt n) := by
  have hlo : (fun x : ℝ ↦ Real.log x) =o[atTop]
      (fun x : ℝ ↦ x ^ (1 / 2 : ℝ)) :=
    isLittleO_log_rpow_atTop (by norm_num)
  have hloNat := hlo.comp_tendsto tendsto_natCast_atTop_atTop
  have hbound := hloNat.bound (half_pos ha)
  have hevent : ∀ᶠ n : ℕ in atTop,
      ‖Real.exp (-a * Real.sqrt n)‖ ≤ (n : ℝ) ^ (-2 : ℝ) := by
    filter_upwards [hbound, eventually_ge_atTop (1 : ℕ)] with n hnlog hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hlog0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
    have hrpow0 : 0 ≤ (n : ℝ) ^ (1 / 2 : ℝ) := by positivity
    have hlog : 2 * Real.log (n : ℝ) ≤ a * Real.sqrt n := by
      have hnlog' : Real.log (n : ℝ) ≤
          a / 2 * (n : ℝ) ^ (1 / 2 : ℝ) := by
        dsimp [Function.comp_def] at hnlog
        rw [abs_of_nonneg hlog0, abs_of_nonneg hrpow0] at hnlog
        exact hnlog
      rw [Real.sqrt_eq_rpow]
      nlinarith
    have hexp : Real.exp (-a * Real.sqrt n) ≤ (n : ℝ) ^ (-2 : ℝ) := by
      rw [Real.rpow_def_of_pos hnpos]
      apply Real.exp_le_exp.mpr
      nlinarith
    simpa [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hexp
  have hs : Summable fun n : ℕ ↦ (n : ℝ) ^ (-2 : ℝ) :=
    (Real.summable_nat_rpow).2 (by norm_num)
  exact hs.of_norm_bounded_eventually_nat hevent

/-- The first use of the master inequality after Lemma 5.24: an intermediate density has a
summable stretched-exponential radius tail. -/
theorem radiusTail_stretched_exponential
    {d : ℕ} {α β : I} (hd : 2 ≤ d)
    (hα0 : 0 < (α : ℝ)) (hαβ : α < β)
    (hβpc : (β : ℝ) < cubicCriticalProbability d) :
    ∃ a : ℝ, 0 < a ∧ ∀ n : ℕ, 1 ≤ n →
      radiusTail d α n ≤ Real.exp (1 - a * Real.sqrt n) := by
  obtain ⟨delta, hdelta, htail⟩ :=
    radiusTail_le_inv_sqrt_of_lt_critical d hd β hβpc
  let D : ℝ := 1 + 2 * delta
  have hD : 0 < D := by dsimp [D]; linarith
  let a : ℝ := ((β : ℝ) - (α : ℝ)) / D
  have hgap : 0 < (β : ℝ) - (α : ℝ) := sub_pos.mpr (by exact_mod_cast hαβ)
  have ha : 0 < a := div_pos hgap hD
  refine ⟨a, ha, ?_⟩
  intro n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hspos : 0 < Real.sqrt n := Real.sqrt_pos.2 hnpos
  have hsum := radiusTailPartialSum_le_sqrt hdelta.le htail n hn
  have hsumPos := radiusTailPartialSum_pos d β n
  have hratio : Real.sqrt n / D ≤
      (n : ℝ) / radiusTailPartialSum d β n := by
    rw [div_le_div_iff₀ hD hsumPos]
    have hsnonneg : 0 ≤ Real.sqrt n := hspos.le
    have hmul := mul_le_mul_of_nonneg_left hsum hsnonneg
    nlinarith [Real.sq_sqrt hnpos.le]
  have hβ1 : (β : ℝ) < 1 :=
    hβpc.trans_le (cubicCriticalProbability_le_one d)
  have hmaster := radiusTail_master_inequality (d := d) (n := n)
    (α := α) (β := β) (by omega) hα0 (by exact_mod_cast hαβ.le) hβ1
  have hgapOne : (β : ℝ) - (α : ℝ) ≤ 1 := by
    linarith [β.2.2, α.2.1]
  have hexponent :
      -(((β : ℝ) - (α : ℝ)) *
          ((n : ℝ) / radiusTailPartialSum d β n - 1)) ≤
        1 - a * Real.sqrt n := by
    have hmul := mul_le_mul_of_nonneg_left hratio hgap.le
    calc
      -(((β : ℝ) - (α : ℝ)) *
          ((n : ℝ) / radiusTailPartialSum d β n - 1)) =
          ((β : ℝ) - (α : ℝ)) -
            ((β : ℝ) - (α : ℝ)) *
              ((n : ℝ) / radiusTailPartialSum d β n) := by ring
      _ ≤ ((β : ℝ) - (α : ℝ)) -
          ((β : ℝ) - (α : ℝ)) * (Real.sqrt n / D) :=
        sub_le_sub_left hmul _
      _ ≤ 1 - a * Real.sqrt n := by
        dsimp [a]
        have heq : ((β : ℝ) - (α : ℝ)) * (Real.sqrt n / D) =
            (((β : ℝ) - (α : ℝ)) / D) * Real.sqrt n := by ring
        rw [heq]
        linarith
  calc
    radiusTail d α n ≤ radiusTail d β n *
        Real.exp (-(((β : ℝ) - (α : ℝ)) *
          ((n : ℝ) / radiusTailPartialSum d β n - 1))) := hmaster
    _ ≤ 1 * Real.exp (1 - a * Real.sqrt n) := by
      exact mul_le_mul measureReal_le_one (Real.exp_le_exp.mpr hexponent)
        (Real.exp_pos _).le zero_le_one
    _ = Real.exp (1 - a * Real.sqrt n) := one_mul _

theorem summable_radiusTail_of_stretched_exponential
    {d : ℕ} {p : I} {a : ℝ} (ha : 0 < a)
    (hbound : ∀ n : ℕ, 1 ≤ n →
      radiusTail d p n ≤ Real.exp (1 - a * Real.sqrt n)) :
    Summable (radiusTail d p) := by
  have hmajorant : Summable fun n : ℕ ↦ Real.exp 1 * Real.exp (-a * Real.sqrt n) :=
    (summable_exp_neg_mul_sqrt ha).mul_left (Real.exp 1)
  apply hmajorant.of_nonneg_of_le
  · intro n
    exact measureReal_nonneg
  · intro n
    by_cases hn : n = 0
    · subst n
      simp [radiusTail_zero]
    · calc
        radiusTail d p n ≤ Real.exp (1 - a * Real.sqrt n) :=
          hbound n (Nat.one_le_iff_ne_zero.mpr hn)
        _ = Real.exp 1 * Real.exp (-a * Real.sqrt n) := by
          rw [← Real.exp_add]
          congr 1
          ring

/-- Exponential radius decay obtained from finite susceptibility by the
translation-invariant BK block argument. -/
theorem radiusTail_exponential_decay_of_lt_critical_via_susceptibility
    (d : ℕ) (hd : 2 ≤ d) (p : I)
    (hp : (p : ℝ) < cubicCriticalProbability d) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ,
      radiusTail d p n ≤ Real.exp (-c * n) := by
  have hp1 : (p : ℝ) < 1 := hp.trans_le (cubicCriticalProbability_le_one d)
  exact radiusTail_exponential_decay_of_susceptibility_lt_top hp1
    (susceptibility_lt_top_of_lt_critical d hd p hp)

/-- Grimmett, Theorem 5.4: below `p_c`, the radius tail decays
exponentially.  The non-strict inequality is valid also at `n = 0`. -/
theorem radiusTail_exponential_decay_of_lt_critical
    (d : ℕ) (hd : 2 ≤ d) (p : I)
    (hp : (p : ℝ) < cubicCriticalProbability d) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ,
      radiusTail d p n ≤ Real.exp (-c * n) := by
  let pc := cubicCriticalProbability d
  let ρr : ℝ := (3 * (p : ℝ) + pc) / 4
  let αr : ℝ := ((p : ℝ) + pc) / 2
  let βr : ℝ := ((p : ℝ) + 3 * pc) / 4
  have hpρ : (p : ℝ) < ρr := by dsimp [ρr, pc]; linarith
  have hρα : ρr < αr := by dsimp [ρr, αr, pc]; linarith
  have hαβ : αr < βr := by dsimp [αr, βr, pc]; linarith
  have hβpc : βr < pc := by dsimp [βr, pc]; linarith
  have hρ0 : 0 ≤ ρr := p.2.1.trans hpρ.le
  have hα0 : 0 ≤ αr := hρ0.trans hρα.le
  have hβ0 : 0 ≤ βr := hα0.trans hαβ.le
  have hρ1 : ρr ≤ 1 := hρα.le.trans
    (hαβ.le.trans (hβpc.le.trans (cubicCriticalProbability_le_one d)))
  have hα1 : αr ≤ 1 := hαβ.le.trans (hβpc.le.trans (cubicCriticalProbability_le_one d))
  have hβ1 : βr ≤ 1 := hβpc.le.trans (cubicCriticalProbability_le_one d)
  let ρ : I := ⟨ρr, hρ0, hρ1⟩
  let α : I := ⟨αr, hα0, hα1⟩
  let β : I := ⟨βr, hβ0, hβ1⟩
  have hpρI : p < ρ := by exact_mod_cast hpρ
  have hραI : ρ < α := by exact_mod_cast hρα
  have hαβI : α < β := by exact_mod_cast hαβ
  have hβpcI : (β : ℝ) < cubicCriticalProbability d := by simpa [β, βr, pc] using hβpc
  have hρpos : 0 < (ρ : ℝ) := lt_of_le_of_lt p.2.1 (by exact_mod_cast hpρI)
  obtain ⟨a, ha, hstretch⟩ :=
    radiusTail_stretched_exponential (d := d) (α := α) (β := β)
      hd (lt_of_lt_of_le hρpos (by exact_mod_cast hραI.le)) hαβI hβpcI
  have hsumα : Summable (radiusTail d α) :=
    summable_radiusTail_of_stretched_exponential ha hstretch
  let C : ℝ := ∑' n : ℕ, radiusTail d α n
  have hCge : 1 ≤ C := by
    have hsingle := hsumα.sum_le_tsum ({0} : Finset ℕ)
      (fun _i _hi ↦ measureReal_nonneg)
    simpa [C, radiusTail_zero] using hsingle
  have hC : 0 < C := zero_lt_one.trans_le hCge
  have hpartial : ∀ n : ℕ, radiusTailPartialSum d α n ≤ C := by
    intro n
    simpa [radiusTailPartialSum, C] using
      hsumα.sum_le_tsum (Finset.range (n + 1))
        (fun _i _hi ↦ measureReal_nonneg)
  let gap : ℝ := (α : ℝ) - (ρ : ℝ)
  have hgap : 0 < gap := sub_pos.mpr (by exact_mod_cast hραI)
  let c₀ : ℝ := gap / (2 * C)
  have hc₀ : 0 < c₀ := div_pos hgap (mul_pos (by norm_num) hC)
  let N : ℕ := ⌈2 * C⌉₊ + 1
  have hNpos : 0 < N := by dsimp [N]; omega
  have htwoC : 2 * C ≤ (N : ℝ) := by
    dsimp [N]
    exact (Nat.le_ceil (2 * C)).trans (by norm_num)
  have hαlt1 : (α : ℝ) < 1 := by
    have hαβreal : (α : ℝ) < (β : ℝ) := by exact_mod_cast hαβI
    exact hαβreal.trans (hβpcI.trans_le (cubicCriticalProbability_le_one d))
  have heventual : ∀ n : ℕ, N ≤ n →
      radiusTail d ρ n ≤ Real.exp (-c₀ * n) := by
    intro n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hNpos.trans_le hn
    have hsumPos := radiusTailPartialSum_pos d α n
    have hratio : (n : ℝ) / C ≤ (n : ℝ) / radiusTailPartialSum d α n :=
      div_le_div_of_nonneg_left hnpos.le hsumPos (hpartial n)
    have hmaster := radiusTail_master_inequality (d := d) (n := n)
      (α := ρ) (β := α) (by omega) hρpos (by exact_mod_cast hραI.le) hαlt1
    have hnTwoC : 2 * C ≤ (n : ℝ) := htwoC.trans (by exact_mod_cast hn)
    have hexponent :
        -(gap * ((n : ℝ) / radiusTailPartialSum d α n - 1)) ≤ -c₀ * n := by
      have hmul := mul_le_mul_of_nonneg_left hratio hgap.le
      have hhalf : gap ≤ gap * (n : ℝ) / (2 * C) := by
        rw [le_div_iff₀ (mul_pos (by norm_num) hC)]
        nlinarith
      dsimp [c₀]
      calc
        -(gap * ((n : ℝ) / radiusTailPartialSum d α n - 1)) =
            gap - gap * ((n : ℝ) / radiusTailPartialSum d α n) := by ring
        _ ≤ gap - gap * ((n : ℝ) / C) := sub_le_sub_left hmul _
        _ ≤ -(gap / (2 * C) * (n : ℝ)) := by
          field_simp [hC.ne'] at hhalf ⊢
          nlinarith
        _ = -(gap / (2 * C)) * (n : ℝ) := by ring
    calc
      radiusTail d ρ n ≤ radiusTail d α n *
          Real.exp (-(gap * ((n : ℝ) / radiusTailPartialSum d α n - 1))) := by
        simpa [gap] using hmaster
      _ ≤ 1 * Real.exp (-c₀ * n) := by
        exact mul_le_mul measureReal_le_one (Real.exp_le_exp.mpr hexponent)
          (Real.exp_pos _).le zero_le_one
      _ = Real.exp (-c₀ * n) := one_mul _
  let g₁ : ℝ := radiusTail d ρ 1
  have hg₁0 : 0 < g₁ := radiusTail_pos_of_pos_density (by omega) hρpos
  have hg₁1 : g₁ < 1 := by
    have hρlt1 : (ρ : ℝ) < 1 :=
      (show (ρ : ℝ) < (α : ℝ) by exact_mod_cast hραI).trans hαlt1
    exact radiusTail_one_lt_one hρlt1
  let b : ℝ := -Real.log g₁ / (N : ℝ)
  have hb : 0 < b := div_pos (neg_pos.mpr (Real.log_neg hg₁0 hg₁1)) (by positivity)
  let c : ℝ := min c₀ b
  have hc : 0 < c := lt_min hc₀ hb
  refine ⟨c, hc, ?_⟩
  intro n
  have htarget : radiusTail d p n ≤ radiusTail d ρ n :=
    radiusTail_mono_density d n hpρI.le
  by_cases hn0 : n = 0
  · subst n
    simpa [radiusTail_zero]
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
  by_cases hnN : N ≤ n
  · exact htarget.trans ((heventual n hnN).trans (Real.exp_le_exp.mpr (by
      have hc₀le : c ≤ c₀ := min_le_left _ _
      have hnreal : (0 : ℝ) ≤ n := by positivity
      nlinarith)))
  · have hnle : (n : ℝ) ≤ N := by exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge hnN))
    have hcb : c ≤ b := min_le_right _ _
    have hlog : Real.log g₁ ≤ -c * (n : ℝ) := by
      have hmul : c * (n : ℝ) ≤ b * (N : ℝ) := by
        exact mul_le_mul hcb hnle (by positivity) hb.le
      have hbN : b * (N : ℝ) = -Real.log g₁ := by
        dsimp [b]
        field_simp
      linarith
    calc
      radiusTail d p n ≤ radiusTail d ρ n := htarget
      _ ≤ g₁ := radiusTail_antitone d ρ hn1
      _ = Real.exp (Real.log g₁) := (Real.exp_log hg₁0).symm
      _ ≤ Real.exp (-c * n) := Real.exp_le_exp.mpr hlog

/-- The strict positive-radius form of Theorem 5.4 displayed by Grimmett.  The rate is
slightly reduced because the source's strict inequality cannot hold at radius zero. -/
theorem radiusTail_lt_exp_neg_of_lt_critical
    (d : ℕ) (hd : 2 ≤ d) (p : I)
    (hp : (p : ℝ) < cubicCriticalProbability d) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
      radiusTail d p n < Real.exp (-c * n) := by
  obtain ⟨c, hc, hdecay⟩ := radiusTail_exponential_decay_of_lt_critical d hd p hp
  refine ⟨c / 2, half_pos hc, ?_⟩
  intro n hn
  exact (hdecay n).trans_lt (Real.exp_lt_exp.mpr (by
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    nlinarith))

/-- A two-point connection reaches the metric sphere at the distance of its
endpoint. -/
theorem connectionEvent_subset_radiusConnectionEvent_dist
    (d : ℕ) (x y : Cubic d) :
    connectionEvent d x y ⊆ radiusConnectionEvent d x (cubicL1Dist x y) := by
  intro omega homega
  rw [mem_radiusConnectionEvent_iff_exists_connection]
  exact ⟨y, mem_cubicMetricSphere_iff_l1Dist_eq.mpr rfl, homega⟩

theorem bernoulliBondMeasure_real_connection_le_radiusTail
    (d : ℕ) (p : I) (y : Cubic d) :
    (bernoulliBondMeasure d p).real (connectionEvent d cubicOrigin y) ≤
      radiusTail d p (cubicL1Dist cubicOrigin y) := by
  calc
    (bernoulliBondMeasure d p).real (connectionEvent d cubicOrigin y) ≤
        (bernoulliBondMeasure d p).real
          (radiusConnectionEvent d cubicOrigin (cubicL1Dist cubicOrigin y)) :=
      measureReal_mono (μ := bernoulliBondMeasure d p)
        (connectionEvent_subset_radiusConnectionEvent_dist d cubicOrigin y)
        (measure_ne_top _ _)
    _ = radiusTail d p (cubicL1Dist cubicOrigin y) := rfl

private theorem summable_shifted_pow_mul_exp_neg {d : ℕ} {c : ℝ} (hc : 0 < c) :
    Summable fun n : ℕ ↦ (n + 1 : ℝ) ^ d * Real.exp (-c * n) := by
  let r := Real.exp (-c)
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hr0, Real.exp_lt_one_iff]
    linarith
  have hbase : Summable fun n : ℕ ↦ (n : ℝ) ^ d * r ^ n :=
    summable_pow_mul_geometric_of_norm_lt_one d hr1
  have hgeom : Summable fun n : ℕ ↦ r ^ n := summable_geometric_of_norm_lt_one hr1
  have hmajorant : Summable fun n : ℕ ↦
      r ^ n + (2 : ℝ) ^ d * ((n : ℝ) ^ d * r ^ n) :=
    hgeom.add (hbase.mul_left ((2 : ℝ) ^ d))
  apply hmajorant.of_nonneg_of_le
  · intro n
    positivity
  · intro n
    have hexp : Real.exp (-c * (n : ℝ)) = r ^ n := by
      dsimp only [r]
      rw [show -c * (n : ℝ) = (n : ℝ) * (-c) by ring, Real.exp_nat_mul]
    rw [hexp]
    by_cases hn : n = 0
    · subst n
      simp
    · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
      have hadd : (n + 1 : ℝ) ≤ 2 * n := by
        linarith
      have hpow : (n + 1 : ℝ) ^ d ≤ (2 * n : ℝ) ^ d :=
        pow_le_pow_left₀ (by positivity) hadd d
      rw [mul_pow] at hpow
      have hmul := mul_le_mul_of_nonneg_right hpow (pow_nonneg hr0.le n)
      calc
        (n + 1 : ℝ) ^ d * r ^ n ≤
            ((2 : ℝ) ^ d * (n : ℝ) ^ d) * r ^ n := hmul
        _ ≤ r ^ n + (2 : ℝ) ^ d * ((n : ℝ) ^ d * r ^ n) := by
          rw [mul_assoc]
          exact le_add_of_nonneg_left (pow_nonneg hr0.le n)

/-- Exponential radius decay alone implies finite susceptibility.  This is the
source implication used after Theorem 5.4 in the radius proof of Theorem 5.2. -/
theorem susceptibility_lt_top_of_radiusTail_exponential_decay
    (d : ℕ) (p : I) {c : ℝ} (hc : 0 < c)
    (hdecay : ∀ n : ℕ, radiusTail d p n ≤ Real.exp (-c * n)) :
    susceptibility d p < ⊤ := by
  let mu := bernoulliBondMeasure d p
  let M : ℕ → ℝ := fun n ↦
    (3 : ℝ) ^ d * (n + 1 : ℝ) ^ d * Real.exp (-c * n)
  have hMnonneg : ∀ n, 0 ≤ M n := by
    intro n
    positivity
  have hMsum : Summable M := by
    simpa [M, mul_assoc] using
      (summable_shifted_pow_mul_exp_neg (d := d) hc).mul_left ((3 : ℝ) ^ d)
  have hmass : ∀ n : ℕ, radiusSphereConnectionMass d p n ≤ ENNReal.ofReal (M n) := by
    intro n
    unfold radiusSphereConnectionMass
    calc
      ∑ y ∈ cubicMetricSphere d cubicOrigin n,
          mu (connectionEvent d cubicOrigin y) ≤
          ∑ _y ∈ cubicMetricSphere d cubicOrigin n,
            ENNReal.ofReal (Real.exp (-c * n)) := by
        apply Finset.sum_le_sum
        intro y hy
        have hydist : cubicL1Dist cubicOrigin y = n :=
          mem_cubicMetricSphere_iff_l1Dist_eq.mp hy
        have hreal : mu.real (connectionEvent d cubicOrigin y) ≤
            Real.exp (-c * n) := by
          exact (bernoulliBondMeasure_real_connection_le_radiusTail d p y).trans
            (by simpa [hydist] using hdecay n)
        have htoReal : (mu (connectionEvent d cubicOrigin y)).toReal ≤
            (ENNReal.ofReal (Real.exp (-c * n))).toReal := by
          change mu.real (connectionEvent d cubicOrigin y) ≤
            (ENNReal.ofReal (Real.exp (-c * n))).toReal
          rw [ENNReal.toReal_ofReal (Real.exp_pos _).le]
          exact hreal
        exact (ENNReal.toReal_le_toReal (measure_ne_top mu _)
          ENNReal.ofReal_ne_top).mp htoReal
      _ = (cubicMetricSphere d cubicOrigin n).card *
          ENNReal.ofReal (Real.exp (-c * n)) := by simp
      _ ≤ (3 ^ d * (n + 1) ^ d : ℕ) *
          ENNReal.ofReal (Real.exp (-c * n)) := by
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast
            (Finset.card_le_card (cubicMetricSphere_subset_ball d cubicOrigin n)).trans
              (cubicMetricBall_card_le d cubicOrigin n)
        · exact bot_le
      _ = ENNReal.ofReal (M n) := by
        rw [← ENNReal.ofReal_natCast]
        rw [← ENNReal.ofReal_mul (by positivity :
          0 ≤ ((3 ^ d * (n + 1) ^ d : ℕ) : ℝ))]
        congr 1
        dsimp only [M]
        push_cast
        ring
  have hmajorantNeTop : (∑' n : ℕ, ENNReal.ofReal (M n)) ≠ ⊤ := by
    rw [← ENNReal.ofReal_tsum_of_nonneg hMnonneg hMsum]
    exact ENNReal.ofReal_ne_top
  have hchiLe : susceptibility d p ≤ ∑' n : ℕ, ENNReal.ofReal (M n) := by
    rw [← tsum_radiusSphereConnectionMass]
    exact ENNReal.tsum_le_tsum hmass
  exact (lt_top_iff_ne_top.mpr
    (ne_top_of_le_ne_top hmajorantNeTop hchiLe))

/-- Grimmett, Theorem 5.2 via the radius-decay conclusion.  Its proof after the
decay estimate is independent of the ghost field. -/
theorem susceptibility_lt_top_of_lt_critical_via_radius
    (d : ℕ) (hd : 2 ≤ d) (p : I)
    (hp : (p : ℝ) < cubicCriticalProbability d) :
    susceptibility d p < ⊤ := by
  obtain ⟨c, hc, hdecay⟩ := radiusTail_exponential_decay_of_lt_critical d hd p hp
  exact susceptibility_lt_top_of_radiusTail_exponential_decay d p hc hdecay

#print axioms radiusTail_exponential_decay_of_lt_critical
#print axioms susceptibility_lt_top_of_lt_critical_via_radius

end Percolation
