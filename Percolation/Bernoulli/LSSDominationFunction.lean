import Percolation.Bernoulli.LSSCountable

/-!
# A single source-facing LSS domination function

The fixed-target LSS theorem supplies, for every iid density below one, a sufficiently high
marginal threshold.  Grimmett's Theorem 7.65 has the opposite quantifier order: it asserts one
nondecreasing function `π(δ)`, tending to one as `δ → 1`, which works simultaneously at every
marginal density `δ`.  This file constructs such a function explicitly and treats the endpoint
`δ = 1` without totalized conditionals.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory Filter Topology
open scoped unitInterval

/-- Explicit real-valued LSS output density.  It inverts the slack in the concrete marginal
threshold used by the dilution proof, and is truncated at zero for small input densities. -/
noncomputable def lssDominationDensityReal (B : ℕ) (delta : ℝ) : ℝ :=
  max 0 (1 - 2 * (2 * (1 - delta)) ^ (((B + 1 : ℕ) : ℝ)⁻¹))

theorem lssDominationDensityReal_nonneg (B : ℕ) (delta : ℝ) :
    0 ≤ lssDominationDensityReal B delta :=
  le_max_left _ _

theorem lssDominationDensityReal_le_one (B : ℕ) {delta : ℝ}
    (hdelta : delta ≤ 1) :
    lssDominationDensityReal B delta ≤ 1 := by
  rw [lssDominationDensityReal, max_le_iff]
  refine ⟨zero_le_one, ?_⟩
  have hroot : 0 ≤ (2 * (1 - delta)) ^ (((B + 1 : ℕ) : ℝ)⁻¹) :=
    Real.rpow_nonneg (by positivity) _
  linarith

/-- Unit-interval packaging of the source-facing LSS domination density. -/
noncomputable def lssDominationDensityUnit (B : ℕ) (delta : I) : I :=
  ⟨lssDominationDensityReal B delta,
    lssDominationDensityReal_nonneg B delta,
    lssDominationDensityReal_le_one B delta.2.2⟩

@[simp]
theorem lssDominationDensityUnit_coe (B : ℕ) (delta : I) :
    (lssDominationDensityUnit B delta : ℝ) = lssDominationDensityReal B delta :=
  rfl

@[simp]
theorem lssDominationDensityReal_one (B : ℕ) :
    lssDominationDensityReal B 1 = 1 := by
  have hexponent : ((B : ℝ) + 1)⁻¹ ≠ 0 := by positivity
  rw [lssDominationDensityReal]
  simp [Real.zero_rpow hexponent]

@[simp]
theorem lssDominationDensityReal_zero (B : ℕ) :
    lssDominationDensityReal B 0 = 0 := by
  rw [lssDominationDensityReal, max_eq_left]
  have hroot : 1 ≤ (2 : ℝ) ^ (((B + 1 : ℕ) : ℝ)⁻¹) :=
    Real.one_le_rpow (by norm_num) (by positivity)
  have hroot' : 1 ≤ (2 : ℝ) ^ (((B : ℝ) + 1)⁻¹) := by
    simpa [Nat.cast_add] using hroot
  norm_num
  linarith

@[simp]
theorem lssDominationDensityUnit_zero (B : ℕ) :
    lssDominationDensityUnit B (0 : I) = 0 := by
  ext
  exact lssDominationDensityReal_zero B

theorem lssDominationDensityReal_lt_one_of_lt_one
    (B : ℕ) {delta : ℝ} (hdelta : delta < 1) :
    lssDominationDensityReal B delta < 1 := by
  rw [lssDominationDensityReal, max_lt_iff]
  refine ⟨zero_lt_one, ?_⟩
  have hbase : 0 < 2 * (1 - delta) := by positivity
  have hroot : 0 < (2 * (1 - delta)) ^ (((B + 1 : ℕ) : ℝ)⁻¹) :=
    Real.rpow_pos_of_pos hbase _
  linarith

theorem continuous_lssDominationDensityReal (B : ℕ) :
    Continuous (lssDominationDensityReal B) := by
  unfold lssDominationDensityReal
  have hexponent : 0 ≤ (((B + 1 : ℕ) : ℝ)⁻¹) := by positivity
  exact continuous_const.max <| continuous_const.sub <| continuous_const.mul <|
    (Real.continuous_rpow_const hexponent).comp (by fun_prop)

theorem continuous_lssDominationDensityUnit (B : ℕ) :
    Continuous (lssDominationDensityUnit B) := by
  apply Continuous.subtype_mk
  exact (continuous_lssDominationDensityReal B).comp continuous_subtype_val

/-- The single LSS output function converges to iid density one as the input marginals tend to
one. -/
theorem lssDominationDensityUnit_tendsto_one (B : ℕ) :
    Tendsto (lssDominationDensityUnit B) (𝓝 (1 : I)) (𝓝 (1 : I)) := by
  have h : ContinuousAt (lssDominationDensityUnit B) (1 : I) :=
    (continuous_lssDominationDensityUnit B).continuousAt
  change Tendsto (lssDominationDensityUnit B) (𝓝 (1 : I))
    (𝓝 (lssDominationDensityUnit B (1 : I))) at h
  have hvalue : lssDominationDensityUnit B (1 : I) = 1 := by
    ext
    exact lssDominationDensityReal_one B
  have hout : 𝓝 (lssDominationDensityUnit B (1 : I)) = 𝓝 (1 : I) :=
    congrArg nhds hvalue
  exact hout ▸ h

theorem monotone_lssDominationDensityReal_on_unit (B : ℕ) :
    MonotoneOn (lssDominationDensityReal B) (Set.Icc 0 1) := by
  intro delta hdelta epsilon hepsilon hde
  unfold lssDominationDensityReal
  apply max_le_max_left
  have hbase : 2 * (1 - epsilon) ≤ 2 * (1 - delta) := by linarith
  have hbaseEpsilon : 0 ≤ 2 * (1 - epsilon) := by linarith [hepsilon.2]
  have hpow := Real.rpow_le_rpow hbaseEpsilon hbase
    (by positivity : 0 ≤ (((B + 1 : ℕ) : ℝ)⁻¹))
  linarith

/-- Monotonicity required in the literal statement of Theorem 7.65. -/
theorem monotone_lssDominationDensityUnit (B : ℕ) :
    Monotone (lssDominationDensityUnit B) := by
  intro delta epsilon hde
  exact monotone_lssDominationDensityReal_on_unit B delta.2 epsilon.2 hde

theorem lssParameterSlack_eq_one_sub_aux_pow_succ
    (B : ℕ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    lssParameterSlack B q = (1 - lssAuxiliaryDensity q) ^ (B + 1) := by
  have hsub0 : 0 ≤ 1 - lssAuxiliaryDensity q := by
    unfold lssAuxiliaryDensity
    linarith
  have haux : 1 - lssAuxiliaryDensity q ≤ lssAuxiliaryDensity q := by
    unfold lssAuxiliaryDensity
    linarith
  unfold lssParameterSlack
  rw [min_eq_left]
  · rw [pow_succ']
  · apply mul_le_mul_of_nonneg_left
    exact pow_le_pow_left₀ hsub0 haux B
    exact hsub0

/-- For a positive output density, the old fixed-target LSS threshold lies below the input
marginal density.  This is the inverse calculation linking the two quantifier orders. -/
theorem lssMarginalThreshold_lssDominationDensityReal_le
    (B : ℕ) {delta : ℝ} (hdelta1 : delta ≤ 1)
    (hpos : 0 < lssDominationDensityReal B delta) :
    lssMarginalThreshold B (lssDominationDensityReal B delta) ≤ delta := by
  let exponent : ℝ := (((B + 1 : ℕ) : ℝ)⁻¹)
  let root : ℝ := (2 * (1 - delta)) ^ exponent
  let q : ℝ := lssDominationDensityReal B delta
  have hbase0 : 0 ≤ 2 * (1 - delta) := by linarith
  have hroot0 : 0 ≤ root := Real.rpow_nonneg hbase0 exponent
  have hexpressionPos : 0 < 1 - 2 * root := by
    dsimp [q, lssDominationDensityReal, root, exponent] at hpos
    dsimp [root, exponent]
    simpa [Nat.cast_add] using hpos
  have hqeq : q = 1 - 2 * root := by
    dsimp [q, lssDominationDensityReal]
    rw [max_eq_right hexpressionPos.le]
  have hq0 : 0 ≤ q := hpos.le
  have hq1 : q ≤ 1 := by rw [hqeq]; linarith
  have haux : 1 - lssAuxiliaryDensity q = root := by
    rw [hqeq]
    unfold lssAuxiliaryDensity
    ring
  have hrootPow : root ^ (B + 1) = 2 * (1 - delta) := by
    dsimp [root, exponent]
    exact Real.rpow_inv_natCast_pow hbase0 (by omega)
  rw [lssMarginalThreshold,
    lssParameterSlack_eq_one_sub_aux_pow_succ B hq0 hq1, haux, hrootPow]
  linarith

/-- Every probability law dominates the all-closed iid site law. -/
theorem stochasticallyDominates_setBernoulli_zero
    {V : Type*} [Countable V]
    (mu : Measure (Set V)) [IsProbabilityMeasure mu] :
    StochasticallyDominates mu setBer((Set.univ : Set V), (0 : I)) := by
  rw [setBernoulli_zero]
  intro f hf hinc hbdd
  rw [integral_dirac f ∅]
  obtain ⟨C, hC⟩ := hbdd
  have hfInt : Integrable f mu := integrable_of_bounded_measurable hf hC
  have hconstInt : Integrable (fun _ : Set V ↦ f ∅) mu := integrable_const _
  have hle : ∀ᵐ eta ∂mu, f ∅ ≤ f eta :=
    ae_of_all _ fun eta ↦ hinc (Set.empty_subset eta)
  simpa using integral_mono_ae hconstInt hfInt hle

/-- On a countable site set, unit one-site marginals force the law to be concentrated on the
all-open configuration, so it dominates iid density one. -/
theorem stochasticallyDominates_setBernoulli_one_of_marginals
    {V : Type*} [Countable V] [DecidableEq V]
    (e : ℕ ≃ V) (mu : Measure (Set V)) [IsProbabilityMeasure mu]
    (hmarginal : ∀ v : V, 1 ≤ mu.real {eta : Set V | v ∈ eta}) :
    StochasticallyDominates mu setBer((Set.univ : Set V), (1 : I)) := by
  have hmemAE (v : V) : ∀ᵐ eta ∂mu, v ∈ eta := by
    let E : Set (Set V) := {eta | v ∈ eta}
    have hEm : MeasurableSet E := measurableSet_mem v
    have hreal : mu.real E = mu.real Set.univ := by
      apply le_antisymm
      · exact measureReal_mono (Set.subset_univ E)
      · rw [probReal_univ]
        exact hmarginal v
    exact (ae_mem_iff_measure_eq hEm.nullMeasurableSet).2
      ((measureReal_eq_measureReal_iff).mp hreal)
  have hall : ∀ᵐ eta ∂mu, eta = Set.univ := by
    filter_upwards [ae_all_iff.2 fun n ↦ hmemAE (e n)] with eta heta
    apply Set.eq_univ_of_forall
    intro v
    simpa using heta (e.symm v)
  rw [setBernoulli_one]
  intro f _hf _hinc _hbdd
  rw [integral_dirac f Set.univ]
  have heq : (∫ eta, f eta ∂mu) = ∫ _eta, f Set.univ ∂mu :=
    integral_congr_ae (hall.mono fun eta heta ↦ congrArg f heta)
  exact le_of_eq <| calc
    f Set.univ = ∫ _eta, f Set.univ ∂mu := by simp
    _ = ∫ eta, f eta ∂mu := heq.symm

/-- The explicit function works simultaneously for every input marginal density, including
the two endpoints. -/
theorem lssDominationDensity_stochasticallyDominates
    {V : Type*} [Countable V] [DecidableEq V]
    (G : SimpleGraph V) (k B : ℕ) (e : ℕ ≃ V)
    (hneighbor : ∀ n (current : Fin n),
      (Finset.univ.filter fun x ↦
        (enumerationPrefixDependencyGraph G k e n).edist current x ≤ 1).card ≤ B)
    (delta : I) (mu : Measure (Set V)) [IsProbabilityMeasure mu]
    (hmu : KDependent G k mu)
    (hmarginal : ∀ current : V,
      (delta : ℝ) ≤ mu.real {original : Set V | current ∈ original}) :
    StochasticallyDominates mu
      setBer((Set.univ : Set V), lssDominationDensityUnit B delta) := by
  by_cases hdeltaOne : (delta : ℝ) = 1
  · have hdelta : delta = 1 := Subtype.ext hdeltaOne
    subst delta
    have hpi : lssDominationDensityUnit B (1 : I) = 1 := by
      ext
      exact lssDominationDensityReal_one B
    rw [hpi]
    exact stochasticallyDominates_setBernoulli_one_of_marginals e mu hmarginal
  let q : I := lssDominationDensityUnit B delta
  by_cases hqZero : (q : ℝ) = 0
  · have hq : q = 0 := Subtype.ext hqZero
    rw [show lssDominationDensityUnit B delta = q from rfl, hq]
    exact stochasticallyDominates_setBernoulli_zero mu
  have hdeltaLt : (delta : ℝ) < 1 := lt_of_le_of_ne delta.2.2 hdeltaOne
  have hqNonneg : 0 ≤ (q : ℝ) := q.2.1
  have hqPos : 0 < (q : ℝ) := lt_of_le_of_ne hqNonneg (Ne.symm hqZero)
  have hqLt : (q : ℝ) < 1 := by
    exact lssDominationDensityReal_lt_one_of_lt_one B hdeltaLt
  have hthreshold : lssMarginalThreshold B (q : ℝ) ≤ (delta : ℝ) := by
    exact lssMarginalThreshold_lssDominationDensityReal_le B delta.2.2 hqPos
  apply lss_stochasticallyDominates G k B e hneighbor q hqLt mu hmu
  intro current
  exact hthreshold.trans (hmarginal current)

/-- **Theorem 7.65 (Liggett--Schonmann--Stacey), literal source quantifier order.**  There is
one nondecreasing output-density function, tending to one at input density one, such that every
`k`-dependent law with one-site marginals at least `δ` dominates iid density `π(δ)`. -/
theorem exists_lssDominationDensity
    {V : Type*} [Countable V] [DecidableEq V]
    (G : SimpleGraph V) (k B : ℕ) (e : ℕ ≃ V)
    (hneighbor : ∀ n (current : Fin n),
      (Finset.univ.filter fun x ↦
        (enumerationPrefixDependencyGraph G k e n).edist current x ≤ 1).card ≤ B) :
    ∃ pi : I → I,
      Monotone pi ∧ Tendsto pi (𝓝 (1 : I)) (𝓝 (1 : I)) ∧
      ∀ (delta : I) (mu : Measure (Set V)), IsProbabilityMeasure mu →
        KDependent G k mu →
        (∀ current : V,
          (delta : ℝ) ≤ mu.real {original : Set V | current ∈ original}) →
        StochasticallyDominates mu setBer((Set.univ : Set V), pi delta) := by
  refine ⟨lssDominationDensityUnit B, monotone_lssDominationDensityUnit B,
    lssDominationDensityUnit_tendsto_one B, ?_⟩
  intro delta mu hprob hmu hmarginal
  letI : IsProbabilityMeasure mu := hprob
  exact lssDominationDensity_stochasticallyDominates
    G k B e hneighbor delta mu hmu hmarginal

end Percolation
