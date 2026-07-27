import Percolation.Extensions.LongRangeMassTransport

/-!
# The supercritical half of the Newman--Schulman power-law theorem
-/

namespace Percolation

open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators Topology unitInterval

/-- Root-cluster size tails decrease to the percolation probability. -/
theorem tendsto_longRangeMeasure_real_clusterAtLeast
    (p : LongRangeProfile) :
    Tendsto
      (fun m ↦ (longRangeMeasure p).real
        (longRangeClusterAtLeastEvent 0 m)) atTop
      (𝓝 (longRangeTheta p)) := by
  let μ := longRangeMeasure p
  have hμ : Tendsto
      (fun m : ℕ ↦ μ (longRangeClusterAtLeastEvent 0 m)) atTop
      (𝓝 (μ (⋂ m : ℕ, longRangeClusterAtLeastEvent 0 m))) :=
    tendsto_measure_iInter_atTop
      (fun m ↦ (measurableSet_longRangeClusterAtLeastEvent 0 m).nullMeasurableSet)
      (fun _m _n hmn ↦ longRangeClusterAtLeastEvent_mono hmn)
      ⟨0, measure_ne_top _ _⟩
  have hreal :=
    (ENNReal.tendsto_toReal (measure_ne_top μ
      (⋂ m : ℕ, longRangeClusterAtLeastEvent 0 m))).comp hμ
  rw [iInter_longRangeClusterAtLeastEvent_eq_percolationEvent] at hreal
  simpa [longRangeTheta, μ, Measure.real, Function.comp_def] using hreal

/-- Quadratic targets tend to infinity. -/
theorem pow_two_le_longRangeQuadraticTarget
    {base : ℕ} (hbase : 0 < base) : ∀ k : ℕ,
    2 ^ k ≤ longRangeQuadraticTarget base 4 k
  | 0 => by simpa using hbase
  | k + 1 => by
      rw [longRangeQuadraticTarget_succ, pow_succ]
      have ih := pow_two_le_longRangeQuadraticTarget hbase k
      have hquota : 2 ≤ longRangeQuadraticQuota 4 k := by
        have hsquare : 16 ≤ (4 + k) ^ 2 := by
          simpa [pow_two] using
            Nat.mul_self_le_mul_self (show 4 ≤ 4 + k by omega)
        simp only [longRangeQuadraticQuota, longRangeQuadraticArity]
        omega
      calc
        2 ^ k * 2 ≤ longRangeQuadraticTarget base 4 k * 2 :=
          Nat.mul_le_mul_right 2 ih
        _ ≤ longRangeQuadraticTarget base 4 k *
            longRangeQuadraticQuota 4 k := Nat.mul_le_mul_left _ hquota
        _ = longRangeQuadraticQuota 4 k *
            longRangeQuadraticTarget base 4 k := by ac_rfl

theorem tendsto_longRangeQuadraticTarget_atTop
    {base : ℕ} (hbase : 0 < base) :
    Tendsto (longRangeQuadraticTarget base 4) atTop atTop := by
  apply tendsto_atTop_mono' atTop
    (Filter.Eventually.of_forall (pow_two_le_longRangeQuadraticTarget hbase))
  exact tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℕ) < 2)

/-- For `1 < α < 2`, some strict nearest-neighbour parameter percolates.  This is the
Newman--Schulman upper-phase half of Grimmett's Theorem 12.8. -/
theorem LongRangePowerLawFamily.exists_strict_parameter_theta_pos
    {β α : ℝ} (F : LongRangePowerLawFamily β α)
    (hβ : 0 < β) (hα1 : 1 < α) (hα2 : α < 2) :
    ∃ q : I, (q : ℝ) < 1 ∧ 0 < F.theta q := by
  obtain ⟨base, q, hbase, hq1, htail, hAdm, hinit⟩ :=
    exists_initialized_quadraticScheme F hβ hα1 hα2
  let S := longRangeQuadraticScheme base 4 hbase (by norm_num)
  have hgood : Tendsto
      (fun k ↦ (longRangeMeasure (F q)).real (S.goodEvent k 0)) atTop (𝓝 1) :=
    S.tendsto_measureReal_goodEvent F q hβ (by linarith) htail
      (longRangeQuadraticError 4) hAdm hinit
      (tendsto_longRangeQuadraticError_zero 4) 0
  have htarget : Tendsto S.target atTop atTop := by
    exact tendsto_longRangeQuadraticTarget_atTop hbase
  have htailLimit : Tendsto
      (fun k ↦ (longRangeMeasure (F q)).real
        (longRangeClusterAtLeastEvent 0 (S.target k))) atTop
      (𝓝 (F.theta q)) := by
    exact (tendsto_longRangeMeasure_real_clusterAtLeast (F q)).comp htarget
  have hleftLimit : Tendsto
      (fun k ↦ (3 / 4 : ℝ) *
        (longRangeMeasure (F q)).real (S.goodEvent k 0)) atTop
      (𝓝 (3 / 4 : ℝ)) := by
    convert tendsto_const_nhds.mul hgood using 1 <;> norm_num
  have hpoint (k : ℕ) :
      (3 / 4 : ℝ) * (longRangeMeasure (F q)).real (S.goodEvent k 0) ≤
        (longRangeMeasure (F q)).real
          (longRangeClusterAtLeastEvent 0 (S.target k)) := by
    have hdensity : (3 / 4 : ℝ) ≤ (S.target k : ℝ) / S.length k := by
      change (3 / 4 : ℝ) ≤
        (longRangeQuadraticTarget base 4 k : ℝ) /
          longRangeQuadraticLength base 4 k
      exact quadratic_target_density_lower (base := base) (N := 4)
        hbase (by norm_num) k
    have hmass := target_density_mul_goodProbability_le_clusterAtLeast
      (F q) (L := S.length k) (m := S.target k) (S.length_pos k) 0
    exact (mul_le_mul_of_nonneg_right hdensity measureReal_nonneg).trans hmass
  have hlower : (3 / 4 : ℝ) ≤ F.theta q :=
    le_of_tendsto_of_tendsto hleftLimit htailLimit
      (Filter.Eventually.of_forall hpoint)
  exact ⟨q, hq1, lt_of_lt_of_le (by norm_num) hlower⟩

/-- Consequently the nearest-neighbour critical parameter is strictly below one. -/
theorem LongRangePowerLawFamily.criticalProbability_lt_one
    {β α : ℝ} (F : LongRangePowerLawFamily β α)
    (hβ : 0 < β) (hα1 : 1 < α) (hα2 : α < 2) :
    F.criticalProbability < 1 := by
  obtain ⟨q, hq1, hq⟩ := F.exists_strict_parameter_theta_pos hβ hα1 hα2
  exact F.criticalProbability_lt_one_of_theta_pos hq1 hq

/-- **Grimmett 12.8, with the suppressed family hypothesis made explicit.**

The book specifies only `p(1)` and the tail asymptotic, which do not determine a probability
measure and do not force a zero phase at a positive nearest-neighbour parameter.  For a complete
monotone family, a positive zero-phase witness together with the Newman--Schulman upper-phase
argument yields the advertised non-trivial critical value and phase separation. -/
theorem longRangePowerLaw_exists_critical
    {β α : ℝ} (F : LongRangePowerLawFamily β α)
    (hβ : 0 < β) (hα1 : 1 < α) (hα2 : α < 2)
    (hlow : ∃ q₀ : I, 0 < (q₀ : ℝ) ∧ F.theta q₀ = 0) :
    0 < F.criticalProbability ∧ F.criticalProbability < 1 ∧
      (∀ q : I, (q : ℝ) < F.criticalProbability → F.theta q = 0) ∧
      (∀ q : I, F.criticalProbability < (q : ℝ) → 0 < F.theta q) := by
  obtain ⟨q₀, hq₀, hq₀zero⟩ := hlow
  have hzero : F.theta 0 = 0 := by
    apply le_antisymm
    · exact (F.theta_mono (show (0 : I) ≤ q₀ by exact q₀.2.1)).trans_eq hq₀zero
    · exact F.theta_nonneg 0
  have hpcLower : (q₀ : ℝ) ≤ F.criticalProbability :=
    F.le_criticalProbability_of_theta_eq_zero hq₀zero
  exact ⟨hq₀.trans_le hpcLower, F.criticalProbability_lt_one hβ hα1 hα2,
    fun q hq ↦ F.theta_eq_zero_of_lt_criticalProbability hzero hq,
    fun q hq ↦ F.theta_pos_of_criticalProbability_lt hq⟩

/-- Criterion 12.2 supplies the explicit low-phase witness needed by the repaired 12.8
interface whenever a positive parameter has mean degree at most one. -/
theorem longRangePowerLaw_exists_critical_of_meanDegree_le_one
    {β α : ℝ} (F : LongRangePowerLawFamily β α)
    (hβ : 0 < β) (hα1 : 1 < α) (hα2 : α < 2)
    {q₀ : I} (hq₀ : 0 < (q₀ : ℝ))
    (hmean : longRangeMeanDegreeENNReal (F q₀) ≤ 1) :
    0 < F.criticalProbability ∧ F.criticalProbability < 1 ∧
      (∀ q : I, (q : ℝ) < F.criticalProbability → F.theta q = 0) ∧
      (∀ q : I, F.criticalProbability < (q : ℝ) → 0 < F.theta q) := by
  apply longRangePowerLaw_exists_critical F hβ hα1 hα2
  refine ⟨q₀, hq₀, ?_⟩
  have hmeasure := longRangeMeasure_percolationEvent_eq_zero_of_meanDegree_le_one
    (F q₀) hmean 0
  simpa [LongRangePowerLawFamily.theta, longRangeTheta, Measure.real,
    hmeasure] using congrArg ENNReal.toReal hmeasure

end Percolation
