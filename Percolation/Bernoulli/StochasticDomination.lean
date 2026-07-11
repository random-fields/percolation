import Percolation.Bernoulli.Coupling
import Percolation.Bernoulli.FKGInfinite
import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.MeasureTheory.Integral.Layercake

/-!
# Stochastic domination and finite-range dependence

The primary definition follows Grimmett (7.63): comparison of expectations of every bounded,
increasing, measurable real function on site configurations.  An event-level consequence is
provided for the block constructions.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval

/-- A real function is bounded uniformly on its entire domain. -/
def IsBoundedRealFunction {X : Type*} (f : X → ℝ) : Prop :=
  ∃ C : ℝ, ∀ x, |f x| ≤ C

/-- Stochastic domination in the exact expectation formulation of Grimmett (7.63). -/
def StochasticallyDominates {ι : Type*}
    (μ ν : Measure (Set ι)) : Prop :=
  ∀ f : Set ι → ℝ, Measurable f → IsIncreasingRandomVariable f →
    IsBoundedRealFunction f → ∫ ω, f ω ∂ν ≤ ∫ ω, f ω ∂μ

theorem StochasticallyDominates.refl {ι : Type*} (μ : Measure (Set ι)) :
    StochasticallyDominates μ μ := by
  intro f _hf _hinc _hbdd
  exact le_rfl

theorem StochasticallyDominates.trans {ι : Type*} {μ ν ξ : Measure (Set ι)}
    (hμν : StochasticallyDominates μ ν) (hνξ : StochasticallyDominates ν ξ) :
    StochasticallyDominates μ ξ := by
  intro f hf hinc hbdd
  exact (hνξ f hf hinc hbdd).trans (hμν f hf hinc hbdd)

/-- The monotone uniform coupling gives the basic iid stochastic ordering.  Besides being useful
in block comparisons, this theorem is an executable sanity check that the orientation of
`StochasticallyDominates` agrees with Grimmett's convention. -/
theorem setBernoulli_stochasticallyDominates {ι : Type*} [Countable ι]
    {p q : I} (hpq : p ≤ q) :
    StochasticallyDominates setBer((Set.univ : Set ι), q)
      setBer((Set.univ : Set ι), p) := by
  intro f hf hinc hbdd
  obtain ⟨C, hC⟩ := hbdd
  exact hinc.setBernoulli_integral_mono hf hpq
    (integrable_of_bounded_measurable hf hC)
    (integrable_of_bounded_measurable hf hC)

/-- Stochastic domination compares every increasing measurable event. -/
theorem StochasticallyDominates.measureReal_le {ι : Type*}
    {μ ν : Measure (Set ι)} (h : StochasticallyDominates μ ν)
    {A : Set (Set ι)} (hAm : MeasurableSet A) (hA : IsIncreasingEvent A) :
    ν.real A ≤ μ.real A := by
  let f : Set ι → ℝ := A.indicator fun _ ↦ 1
  have hfm : Measurable f := measurable_const.indicator hAm
  have hfi : IsIncreasingRandomVariable f := hA.indicator_isIncreasingRandomVariable
  have hfb : IsBoundedRealFunction f := by
    refine ⟨1, ?_⟩
    intro ω
    by_cases hω : ω ∈ A <;> simp [f, hω]
  have hle := h f hfm hfi hfb
  dsimp [f] at hle
  rw [integral_indicator_const (1 : ℝ) hAm, integral_indicator_const (1 : ℝ) hAm,
    smul_eq_mul, smul_eq_mul, mul_one, mul_one] at hle
  exact hle

/-- For probability laws, comparison of all measurable increasing events implies Grimmett's
expectation formulation of stochastic domination.  The proof uses the layer-cake formula on a
bounded increasing observable. -/
theorem stochasticallyDominates_of_measureReal_le {ι : Type*}
    (μ ν : Measure (Set ι)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : ∀ A : Set (Set ι), MeasurableSet A → IsIncreasingEvent A →
      ν.real A ≤ μ.real A) :
    StochasticallyDominates μ ν := by
  intro f hf hinc hbdd
  obtain ⟨C, hC⟩ := hbdd
  have hC0 : 0 ≤ C := (abs_nonneg (f ∅)).trans (hC ∅)
  let g : Set ι → ℝ := fun ω ↦ f ω + C
  have hg0 : ∀ ω, 0 ≤ g ω := by
    intro ω
    have hfLower := (abs_le.mp (hC ω)).1
    dsimp [g]
    linarith
  have hgUpper : ∀ ω, g ω ≤ 2 * C := by
    intro ω
    have hfUpper := (abs_le.mp (hC ω)).2
    dsimp [g]
    linarith
  have hgm : Measurable g := hf.add_const C
  have hgb : ∀ ω, |g ω| ≤ 2 * C := by
    intro ω
    rw [abs_of_nonneg (hg0 ω)]
    exact hgUpper ω
  have hfIntμ : Integrable f μ := integrable_of_bounded_measurable hf hC
  have hfIntν : Integrable f ν := integrable_of_bounded_measurable hf hC
  have hgIntμ : Integrable g μ := integrable_of_bounded_measurable hgm hgb
  have hgIntν : Integrable g ν := integrable_of_bounded_measurable hgm hgb
  let tailμ : ℝ → ℝ := fun t ↦ μ.real {ω : Set ι | t < g ω}
  let tailν : ℝ → ℝ := fun t ↦ ν.real {ω : Set ι | t < g ω}
  have htailμ_antitone : Antitone tailμ := by
    intro s t hst
    apply measureReal_mono _ (measure_ne_top μ _)
    intro ω hω
    exact lt_of_le_of_lt hst hω
  have htailν_antitone : Antitone tailν := by
    intro s t hst
    apply measureReal_mono _ (measure_ne_top ν _)
    intro ω hω
    exact lt_of_le_of_lt hst hω
  have htailμ_meas : Measurable tailμ := htailμ_antitone.measurable
  have htailν_meas : Measurable tailν := htailν_antitone.measurable
  have htailμ_int : Integrable tailμ (volume.restrict (Set.Ioi 0)) := by
    let b : ℝ → ℝ := Set.Ioc 0 (2 * C) |>.indicator fun _ ↦ 1
    have hbInt : Integrable b volume := by
      change Integrable ((Set.Ioc 0 (2 * C)).indicator (fun _ ↦ (1 : ℝ))) volume
      exact (integrableOn_const (μ := volume) (s := Set.Ioc 0 (2 * C))
        (C := (1 : ℝ)) measure_Ioc_lt_top.ne).integrable_indicator measurableSet_Ioc
    apply Integrable.mono' (hbInt.mono_measure Measure.restrict_le_self)
      htailμ_meas.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := ht
    by_cases htC : t ≤ 2 * C
    · have htail_le : tailμ t ≤ 1 := by
        exact (measureReal_mono (Set.subset_univ _)).trans_eq probReal_univ
      rw [show b t = 1 by simp [b, ht0, htC], Real.norm_eq_abs,
        abs_of_nonneg measureReal_nonneg]
      exact htail_le
    · have hempty : {ω : Set ι | t < g ω} = ∅ := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        exact fun hω ↦ (not_le_of_gt hω) (hgUpper ω |>.trans (le_of_not_ge htC))
      simp [tailμ, hempty, b, ht0, htC]
  have htailν_int : Integrable tailν (volume.restrict (Set.Ioi 0)) := by
    let b : ℝ → ℝ := Set.Ioc 0 (2 * C) |>.indicator fun _ ↦ 1
    have hbInt : Integrable b volume := by
      change Integrable ((Set.Ioc 0 (2 * C)).indicator (fun _ ↦ (1 : ℝ))) volume
      exact (integrableOn_const (μ := volume) (s := Set.Ioc 0 (2 * C))
        (C := (1 : ℝ)) measure_Ioc_lt_top.ne).integrable_indicator measurableSet_Ioc
    apply Integrable.mono' (hbInt.mono_measure Measure.restrict_le_self)
      htailν_meas.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := ht
    by_cases htC : t ≤ 2 * C
    · have htail_le : tailν t ≤ 1 := by
        exact (measureReal_mono (Set.subset_univ _)).trans_eq probReal_univ
      rw [show b t = 1 by simp [b, ht0, htC], Real.norm_eq_abs,
        abs_of_nonneg measureReal_nonneg]
      exact htail_le
    · have hempty : {ω : Set ι | t < g ω} = ∅ := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        exact fun hω ↦ (not_le_of_gt hω) (hgUpper ω |>.trans (le_of_not_ge htC))
      simp [tailν, hempty, b, ht0, htC]
  have htail : ∀ t, tailν t ≤ tailμ t := by
    intro t
    apply h
    · change MeasurableSet (g ⁻¹' Set.Ioi t)
      exact hgm measurableSet_Ioi
    · intro A B hAB hA
      change t < g A at hA
      change t < g B
      dsimp [g] at hA ⊢
      exact hA.trans_le (by simpa [add_comm] using add_le_add_right (hinc hAB) C)
  have hg_le : ∫ ω, g ω ∂ν ≤ ∫ ω, g ω ∂μ := by
    rw [hgIntν.integral_eq_integral_meas_lt (Filter.Eventually.of_forall hg0),
      hgIntμ.integral_eq_integral_meas_lt (Filter.Eventually.of_forall hg0)]
    exact integral_mono htailν_int htailμ_int htail
  rw [show (∫ ω, g ω ∂ν) = (∫ ω, f ω ∂ν) + C by
      simp only [g, integral_add hfIntν (integrable_const C), integral_const,
        probReal_univ, one_smul],
    show (∫ ω, g ω ∂μ) = (∫ ω, f ω ∂μ) + C by
      simp only [g, integral_add hfIntμ (integrable_const C), integral_const,
        probReal_univ, one_smul]] at hg_le
  linarith

theorem stochasticallyDominates_iff_measureReal_le {ι : Type*}
    (μ ν : Measure (Set ι)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    StochasticallyDominates μ ν ↔
      ∀ A : Set (Set ι), MeasurableSet A → IsIncreasingEvent A →
        ν.real A ≤ μ.real A := by
  constructor
  · intro h A hAm hAi
    exact h.measureReal_le hAm hAi
  · exact stochasticallyDominates_of_measureReal_le μ ν

/-- The sigma-algebra generated by site coordinates in `S`. -/
@[reducible] def siteCoordinateMeasurableSpace
    (ι : Type*) (S : Set ι) : MeasurableSpace (Set ι) :=
  MeasurableSpace.generateFrom {{ω : Set ι | x ∈ ω} | x ∈ S}

theorem siteCoordinateMeasurableSpace_le (ι : Type*) (S : Set ι) :
    siteCoordinateMeasurableSpace ι S ≤ (inferInstance : MeasurableSpace (Set ι)) := by
  rw [siteCoordinateMeasurableSpace]
  apply MeasurableSpace.generateFrom_le
  intro A hA
  rcases hA with ⟨x, _hx, rfl⟩
  exact measurableSet_mem x

/-- A site law is `k`-dependent when coordinate sigma-algebras at mutual graph distance greater
than `k` are independent. -/
def KDependent {ι : Type*} (G : SimpleGraph ι) (k : ℕ) (μ : Measure (Set ι)) : Prop :=
  ∀ A B : Set ι,
    (∀ x ∈ A, ∀ y ∈ B, (k : ℕ∞) < G.edist x y) →
      Indep (siteCoordinateMeasurableSpace ι A) (siteCoordinateMeasurableSpace ι B) μ

theorem KDependent.mono {ι : Type*} {G : SimpleGraph ι} {μ : Measure (Set ι)}
    {k l : ℕ} (h : KDependent G k μ) (hkl : k ≤ l) : KDependent G l μ := by
  intro A B hsep
  apply h A B
  intro x hx y hy
  exact lt_of_le_of_lt (by exact_mod_cast hkl) (hsep x hx y hy)

/-- Every iid site field is `k`-dependent for every `k`. -/
theorem setBernoulli_kDependent {ι : Type*} [Countable ι] [DecidableEq ι]
    (G : SimpleGraph ι) (k : ℕ) (p : I) :
    KDependent G k setBer((Set.univ : Set ι), p) := by
  intro A B hsep
  have hdisj : Disjoint A B := Set.disjoint_left.2 fun x hxA hxB ↦ by
    have h := hsep x hxA x hxB
    simp at h
  have hsm : ∀ x : ι, MeasurableSet {s : Set ι | x ∈ s} := fun x ↦ measurableSet_mem x
  simpa [siteCoordinateMeasurableSpace] using
    (ProbabilityTheory.iIndepSet.indep_generateFrom_of_disjoint
      (μ := setBer((Set.univ : Set ι), p))
      (s := fun x : ι ↦ {η : Set ι | x ∈ η}) hsm
      (setBernoulli_iIndepSet_mem_univ p) A B hdisj)

/-- Independence of two sub-σ-algebras is transported through a measurable pushforward. -/
theorem Indep.map_measure {Ω β : Type*} [MeasurableSpace Ω] [mβ : MeasurableSpace β]
    {μ : Measure Ω} [IsZeroOrProbabilityMeasure μ] {f : Ω → β} (hf : Measurable f)
    {m₁ m₂ : MeasurableSpace β}
    (hm₁ : m₁ ≤ mβ)
    (hm₂ : m₂ ≤ mβ)
    (h : Indep (MeasurableSpace.comap f m₁) (MeasurableSpace.comap f m₂) μ) :
    @Indep β m₁ m₂ mβ
      (@Measure.map Ω β _ mβ f μ) := by
  let ν : @Measure β mβ :=
    @Measure.map Ω β _ mβ f μ
  change @Indep β m₁ m₂ mβ ν
  rw [@indep_iff_forall_indepSet β m₁ m₂
    mβ ν]
  intro s t hs ht
  have hsGlobal : @MeasurableSet β mβ s := by
    exact hm₁ s hs
  have htGlobal : @MeasurableSet β mβ t := by
    exact hm₂ t ht
  have hsComap : MeasurableSet[MeasurableSpace.comap f m₁] (f ⁻¹' s) :=
    ⟨s, hs, rfl⟩
  have htComap : MeasurableSet[MeasurableSpace.comap f m₂] (f ⁻¹' t) :=
    ⟨t, ht, rfl⟩
  have hind := h.indepSet_of_measurableSet hsComap htComap
  have hmapInter : ν (s ∩ t) = μ (f ⁻¹' (s ∩ t)) := by
    dsimp [ν]
    exact @Measure.map_apply Ω β _ mβ μ f hf (s ∩ t) (hsGlobal.inter htGlobal)
  have hmapS : ν s = μ (f ⁻¹' s) := by
    dsimp [ν]
    exact @Measure.map_apply Ω β _ mβ μ f hf s hsGlobal
  have hmapT : ν t = μ (f ⁻¹' t) := by
    dsimp [ν]
    exact @Measure.map_apply Ω β _ mβ μ f hf t htGlobal
  apply (indepSet_iff_indepSets_singleton hsGlobal htGlobal ν).mpr
  apply indepSets_singleton_iff.mpr
  calc
    ν (s ∩ t) = μ (f ⁻¹' (s ∩ t)) := hmapInter
    _ = μ (f ⁻¹' s) * μ (f ⁻¹' t) := by
      simpa [Set.preimage_inter] using hind.measure_inter_eq_mul
    _ = ν s * ν t := by
      rw [hmapS, hmapT]

end Percolation
