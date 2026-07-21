import Percolation.Extensions.LongRangeQuadraticControl

/-!
# Initializing the long-range multiscale recursion near density one
-/

namespace Percolation

open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators Topology unitInterval

/-- A concrete sequence of unit-interval parameters increasing to one. -/
noncomputable def unitIntervalApproachOne (n : ℕ) : I :=
  ⟨(n : ℝ) / (n + 1), by
    constructor
    · positivity
    · exact (div_le_one (by positivity)).mpr (by norm_num)⟩

@[simp]
theorem coe_unitIntervalApproachOne (n : ℕ) :
    (unitIntervalApproachOne n : ℝ) = (n : ℝ) / (n + 1) := rfl

theorem unitIntervalApproachOne_lt_one (n : ℕ) :
    (unitIntervalApproachOne n : ℝ) < 1 := by
  rw [coe_unitIntervalApproachOne]
  exact (div_lt_one (by positivity)).mpr (by norm_num)

theorem tendsto_unitIntervalApproachOne :
    Tendsto unitIntervalApproachOne atTop (𝓝 (1 : I)) := by
  rw [tendsto_subtype_rng]
  simpa using (tendsto_natCast_div_add_atTop (1 : ℝ))

/-- A power-law family admits a strict parameter close enough to one to meet both the
tail lower bound and any prescribed finite seed-error budget. -/
theorem exists_parameter_seed_error_le
    {β α : ℝ} (hβ : 0 < β) {base : ℕ} {ε : ℝ} (hε : 0 < ε) :
    ∃ q : I, (q : ℝ) < 1 ∧
      longRangePowerLawTailProbability β α 1 ≤ q ∧
      1 - (q : ℝ) ^ base ≤ ε := by
  have hcoe : Tendsto (fun n ↦ (unitIntervalApproachOne n : ℝ)) atTop (𝓝 1) := by
    exact tendsto_subtype_rng.mp tendsto_unitIntervalApproachOne
  have htail :
      (longRangePowerLawTailProbability β α 1 : ℝ) < 1 :=
    longRangePowerLawTailProbability_lt_one (by norm_num)
  have heTail : ∀ᶠ n in atTop,
      (longRangePowerLawTailProbability β α 1 : ℝ) <
        (unitIntervalApproachOne n : ℝ) :=
    hcoe.eventually (Ioi_mem_nhds htail)
  have hpow : Tendsto
      (fun n ↦ (unitIntervalApproachOne n : ℝ) ^ base) atTop (𝓝 1) := by
    simpa using hcoe.pow base
  have hePow : ∀ᶠ n in atTop,
      1 - ε < (unitIntervalApproachOne n : ℝ) ^ base :=
    hpow.eventually (Ioi_mem_nhds (sub_lt_self 1 hε))
  obtain ⟨n, hnTail, hnPow⟩ := (heTail.and hePow).exists
  refine ⟨unitIntervalApproachOne n, unitIntervalApproachOne_lt_one n, ?_, by linarith⟩
  exact_mod_cast hnTail.le

/-- A finite block contains no more internal nearest-neighbour bonds than vertices. -/
theorem card_longRangeBlockNearestEdges_le_length
    (L : ℕ) (z : ℤ) :
    (longRangeBlockNearestEdges L 1 0 z).card ≤ L := by
  classical
  calc
    (longRangeBlockNearestEdges L 1 0 z).card ≤
        ((longRangeBlockVertices L 1 0 z).filter fun x ↦
          x + 1 ∈ longRangeBlockVertices L 1 0 z).card :=
      Finset.card_image_le
    _ ≤ (longRangeBlockVertices L 1 0 z).card := Finset.card_filter_le _ _
    _ = L := by simp [longRangeBlockVertices_card, longRangeBlockLength]

/-- The explicit nearest-neighbour seed bound initializes every translated base block. -/
theorem measureReal_intervalLargeComponent_compl_le_of_seed
    {β α : ℝ} (F : LongRangePowerLawFamily β α) (q : I)
    {base : ℕ} (hbase : 0 < base) {ε : ℝ}
    (hseed : 1 - (q : ℝ) ^ base ≤ ε) (z : ℤ) :
    (longRangeMeasure (F q)).real
        (longRangeIntervalLargeComponentEvent base base z)ᶜ ≤ ε := by
  let seed : Set LongRangeConfiguration :=
    {ω | (longRangeBlockNearestEdges base 1 0 z : Set (Sym2 ℤ)) ⊆ ω}
  have hseedSub : seed ⊆ longRangeIntervalLargeComponentEvent base base z :=
    nearestOpen_subset_longRangeIntervalLargeComponentEvent hbase le_rfl z
  have hprobSeed : (longRangeMeasure (F q)).real seed =
      (q : ℝ) ^ (longRangeBlockNearestEdges base 1 0 z).card :=
    longRangeMeasure_real_blockNearestOpen F q base 1 0 z
  have hpow : (q : ℝ) ^ base ≤
      (q : ℝ) ^ (longRangeBlockNearestEdges base 1 0 z).card :=
    pow_le_pow_of_le_one q.2.1 q.2.2
      (card_longRangeBlockNearestEdges_le_length base z)
  have hgood : (q : ℝ) ^ base ≤
      (longRangeMeasure (F q)).real
        (longRangeIntervalLargeComponentEvent base base z) := by
    calc
      (q : ℝ) ^ base ≤ (longRangeMeasure (F q)).real seed := by
        rw [hprobSeed]
        exact hpow
      _ ≤ _ := measureReal_mono hseedSub
  have hcompl := measureReal_compl (μ := longRangeMeasure (F q))
    (measurableSet_longRangeIntervalLargeComponentEvent base base z)
  rw [measureReal_univ_eq_one] at hcompl
  linarith

/-- Fully initialized quadratic scheme for some strict nearest-neighbour parameter. -/
theorem exists_initialized_quadraticScheme
    {β α : ℝ} (F : LongRangePowerLawFamily β α)
    (hβ : 0 < β) (hα1 : 1 < α) (hα2 : α < 2) :
    ∃ (base : ℕ) (q : I), ∃ hbase : 0 < base, (q : ℝ) < 1 ∧
      longRangePowerLawTailProbability β α 1 ≤ q ∧
      let S := longRangeQuadraticScheme base 4 hbase (by norm_num)
      S.ErrorAdmissible (β := β) (α := α) (longRangeQuadraticError 4) ∧
      ∀ z : ℤ, (longRangeMeasure (F q)).real (S.goodEvent 0 z)ᶜ ≤
        longRangeQuadraticError 4 0 := by
  obtain ⟨base, hbase, hcross⟩ :=
    exists_base_quadraticCrossControlled hβ hα1 hα2
  obtain ⟨q, hq1, htail, hseed⟩ :=
    exists_parameter_seed_error_le hβ
      (base := base) (ε := longRangeQuadraticError 4 0)
      (longRangeQuadraticError_pos 4 0)
  refine ⟨base, q, hbase, hq1, htail, ?_, ?_⟩
  · exact quadratic_errorAdmissible hbase (by norm_num) hcross
  · intro z
    change (longRangeMeasure (F q)).real
      (longRangeIntervalLargeComponentEvent base base z)ᶜ ≤
        longRangeQuadraticError 4 0
    exact measureReal_intervalLargeComponent_compl_le_of_seed
      F q hbase hseed z

end Percolation
