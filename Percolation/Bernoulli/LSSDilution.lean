import Percolation.Bernoulli.LSSParameters

/-!
# Independent dilution of a site field

In the proof of Grimmett Theorem 7.65, an arbitrary site field `Y` is multiplied
coordinatewise by an independent iid Bernoulli field `Z`.  This file constructs the resulting
law as a measurable pushforward and proves the source's immediate stochastic comparison
`Y ⩾st ZY` by a literal monotone coupling.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval

/-- Coordinatewise product of two set-valued site configurations. -/
def siteDilutionMap {ι : Type*} (z : Set ι × Set ι) : Set ι :=
  z.1 ∩ z.2

theorem measurable_siteDilutionMap {ι : Type*} :
    Measurable (siteDilutionMap : Set ι × Set ι → Set ι) := by
  change Measurable fun z : Set ι × Set ι => {i | i ∈ z.1 ∧ i ∈ z.2}
  fun_prop

/-- Law obtained by retaining every occupied site of `μ` independently with probability `p`. -/
noncomputable def siteDilutionLaw {ι : Type*}
    (μ : Measure (Set ι)) (p : I) : Measure (Set ι) :=
  (μ.prod setBer((Set.univ : Set ι), p)).map siteDilutionMap

instance siteDilutionLaw_isProbabilityMeasure {ι : Type*}
    (μ : Measure (Set ι)) [IsProbabilityMeasure μ] (p : I) :
    IsProbabilityMeasure (siteDilutionLaw μ p) := by
  unfold siteDilutionLaw
  exact Measure.isProbabilityMeasure_map measurable_siteDilutionMap.aemeasurable

/-- One-site marginal of the diluted law is the original marginal times the retention
probability. -/
theorem siteDilutionLaw_real_mem {ι : Type*} [Countable ι] [DecidableEq ι]
    (μ : Measure (Set ι)) [IsProbabilityMeasure μ] (p : I) (x : ι) :
    (siteDilutionLaw μ p).real {η : Set ι | x ∈ η} =
      μ.real {η : Set ι | x ∈ η} * (p : ℝ) := by
  rw [siteDilutionLaw, map_measureReal_apply measurable_siteDilutionMap
    (measurableSet_mem x)]
  have hpre : siteDilutionMap ⁻¹' {η : Set ι | x ∈ η} =
      {η : Set ι | x ∈ η} ×ˢ {η : Set ι | x ∈ η} := by
    ext z
    simp [siteDilutionMap]
  rw [hpre, measureReal_prod_prod]
  have hsingle := setBernoulli_real_superset_finset_univ ({x} : Finset ι) p
  simpa [Set.singleton_subset_iff] using congrArg
    (fun r : ℝ => μ.real {η : Set ι | x ∈ η} * r) hsingle

/-- Coupling map pairing the original field with its independently thinned subfield. -/
def siteDilutionCouplingMap {ι : Type*}
    (z : Set ι × Set ι) : Set ι × Set ι :=
  (z.1, siteDilutionMap z)

theorem measurable_siteDilutionCouplingMap {ι : Type*} :
    Measurable (siteDilutionCouplingMap : Set ι × Set ι → Set ι × Set ι) := by
  exact Measurable.prod measurable_fst measurable_siteDilutionMap

/-- The original field contains its diluted copy in the canonical product coupling. -/
theorem hasMonotoneCoupling_siteDilutionLaw {ι : Type*} [Countable ι]
    (μ : Measure (Set ι)) [IsProbabilityMeasure μ] (p : I) :
    HasMonotoneCoupling μ (siteDilutionLaw μ p) := by
  let ν := setBer((Set.univ : Set ι), p)
  let κ := (μ.prod ν).map siteDilutionCouplingMap
  have hQ : Measurable (siteDilutionCouplingMap :
      Set ι × Set ι → Set ι × Set ι) := measurable_siteDilutionCouplingMap
  haveI : IsProbabilityMeasure (μ.prod ν) := inferInstance
  haveI : IsProbabilityMeasure κ := by
    dsimp only [κ]
    exact Measure.isProbabilityMeasure_map hQ.aemeasurable
  refine ⟨κ, inferInstance, ?_, ?_, ?_⟩
  · calc
      κ.map Prod.fst = (μ.prod ν).map (Prod.fst ∘ siteDilutionCouplingMap) := by
        dsimp only [κ]
        rw [Measure.map_map measurable_fst hQ]
      _ = (μ.prod ν).map Prod.fst := by
        congr 1
      _ = μ := by simp [ν]
  · calc
      κ.map Prod.snd = (μ.prod ν).map (Prod.snd ∘ siteDilutionCouplingMap) := by
        dsimp only [κ]
        rw [Measure.map_map measurable_snd hQ]
      _ = (μ.prod ν).map siteDilutionMap := by
        congr 1
      _ = siteDilutionLaw μ p := rfl
  · have hmeas : MeasurableSet {z : Set ι × Set ι | z.2 ⊆ z.1} := by
      change MeasurableSet {z : Set ι × Set ι | ∀ i, i ∈ z.2 → i ∈ z.1}
      measurability
    dsimp only [κ]
    rw [ae_map_iff hQ.aemeasurable hmeas]
    filter_upwards with z
    exact Set.inter_subset_left

/-- The easy comparison in the proof of (7.116): independent dilution can only close sites. -/
theorem stochasticallyDominates_siteDilutionLaw {ι : Type*} [Countable ι]
    (μ : Measure (Set ι)) [IsProbabilityMeasure μ] (p : I) :
    StochasticallyDominates μ (siteDilutionLaw μ p) :=
  (hasMonotoneCoupling_siteDilutionLaw μ p).stochasticallyDominates

end Percolation
