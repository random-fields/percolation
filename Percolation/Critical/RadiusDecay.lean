import Percolation.Critical.RadiusBlock
import Percolation.Critical.SusceptibilityThreshold

/-!
# Exponential decay of the radius tail

This file first records the block proof of exponential decay from finite
susceptibility.  It supplies the exact conclusion of Grimmett's Theorem 5.4 and
will remain as an independent cross-check when the Menshikov derivation through
Lemmas 5.12, 5.17, 5.22, and 5.24 is closed.
-/

namespace Percolation

open MeasureTheory
open scoped unitInterval ENNReal BigOperators

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
      radiusTail d p n ≤ Real.exp (-c * n) :=
  radiusTail_exponential_decay_of_lt_critical_via_susceptibility d hd p hp

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
