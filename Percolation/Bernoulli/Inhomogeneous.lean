import Percolation.Bernoulli.FKGInfinite
import Percolation.Bernoulli.Coupling
import Mathlib.Probability.Independence.InfinitePi

/-!
# Countable inhomogeneous Bernoulli product measures

This file extracts the coordinate-dependent product law needed by Grimmett,
*Percolation* (2nd ed.), §§12.1 and 12.3, from the planar Chapter 11 module.  It is deliberately
independent of planar critical-surface inputs: long-range, mixed, oriented, and discretized
continuum models all need this probability layer without importing any external theorem.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped Finset unitInterval

/-- The Bernoulli law on one Boolean coordinate with parameter `p`. -/
noncomputable def bernoulliPropMeasure (p : I) : Measure Prop :=
  unitInterval.toNNReal p • Measure.dirac True +
    unitInterval.toNNReal (σ p) • Measure.dirac False

noncomputable instance bernoulliPropMeasure.isProbabilityMeasure (p : I) :
    IsProbabilityMeasure (bernoulliPropMeasure p) := by
  rw [bernoulliPropMeasure]
  infer_instance

/-- Independent Bernoulli coordinates with a coordinate-dependent density profile. -/
noncomputable def inhomogeneousSetBernoulli {ι : Type*} (q : ι → I) : Measure (Set ι) :=
  Measure.comap (fun s i ↦ i ∈ s) <|
    Measure.infinitePi fun i ↦ bernoulliPropMeasure (q i)

noncomputable instance inhomogeneousSetBernoulli.isProbabilityMeasure {ι : Type*}
    (q : ι → I) : IsProbabilityMeasure (inhomogeneousSetBernoulli q) := by
  rw [inhomogeneousSetBernoulli]
  exact MeasurableEquiv.setOf.symm.measurableEmbedding.isProbabilityMeasure_comap <|
    .of_forall fun P ↦ ⟨{i | P i}, rfl⟩

theorem inhomogeneousSetBernoulli_eq_map {ι : Type*} (q : ι → I) :
    inhomogeneousSetBernoulli q =
      (Measure.infinitePi fun i ↦ bernoulliPropMeasure (q i)).map
        (fun b : ι → Prop ↦ {i | b i}) := by
  exact MeasurableEquiv.setOf.comap_symm

theorem inhomogeneousSetBernoulli_apply' {ι : Type*} (q : ι → I)
    (S : Set (Set ι)) :
    inhomogeneousSetBernoulli q S =
      (Measure.infinitePi fun i ↦ bernoulliPropMeasure (q i))
        ((fun b : ι → Prop ↦ {i | b i}) ⁻¹' S) := by
  exact MeasurableEquiv.setOf.symm.comap_apply _ _

/-- A constant density profile recovers Mathlib's homogeneous Bernoulli random set on all
coordinates. -/
theorem inhomogeneousSetBernoulli_const {ι : Type*} (p : I) :
    inhomogeneousSetBernoulli (fun _ : ι ↦ p) =
      setBer((Set.univ : Set ι), p) := by
  rw [inhomogeneousSetBernoulli_eq_map, setBernoulli_eq_map]
  congr 2

/-- Negating one Boolean Bernoulli coordinate replaces its density by the complementary
density. -/
theorem bernoulliPropMeasure_map_not (p : I) :
    (bernoulliPropMeasure p).map Not = bernoulliPropMeasure (σ p) := by
  rw [Measure.ext_iff_singleton]
  intro b
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton b)]
  by_cases hb : b
  · have hb' : b = True := propext (iff_true_intro hb)
    subst b
    simp [bernoulliPropMeasure]
  · have hb' : b = False := propext (iff_false_intro hb)
    subst b
    simp [bernoulliPropMeasure]

/-- Complementing every coordinate of an inhomogeneous Bernoulli set complements every
coordinate density. -/
theorem inhomogeneousSetBernoulli_map_compl {ι : Type*} (q : ι → I) :
    (inhomogeneousSetBernoulli q).map (fun s : Set ι ↦ sᶜ) =
      inhomogeneousSetBernoulli (fun i ↦ σ (q i)) := by
  rw [inhomogeneousSetBernoulli_eq_map, inhomogeneousSetBernoulli_eq_map,
    Measure.map_map measurable_compl
      (by fun_prop : Measurable (fun b : ι → Prop ↦ {i | b i}))]
  have hpi := Measure.infinitePi_map_pi
    (μ := fun i : ι ↦ bernoulliPropMeasure (q i))
    (f := fun _ : ι ↦ Not) (fun _ ↦ by fun_prop)
  simp_rw [bernoulliPropMeasure_map_not] at hpi
  rw [← hpi, Measure.map_map
    (by fun_prop : Measurable (fun b : ι → Prop ↦ {i | b i}))
    (by fun_prop : Measurable (fun b : ι → Prop ↦ fun i ↦ ¬b i))]
  congr 1

/-- Homogeneous specialization of `inhomogeneousSetBernoulli_map_compl`. -/
theorem setBernoulli_map_compl_univ {ι : Type*} (p : I) :
    (setBer((Set.univ : Set ι), p)).map (fun s : Set ι ↦ sᶜ) =
      setBer((Set.univ : Set ι), σ p) := by
  rw [← inhomogeneousSetBernoulli_const p,
    inhomogeneousSetBernoulli_map_compl]
  simpa using (inhomogeneousSetBernoulli_const (ι := ι) (σ p))

/-! ### Monotone common-uniform coupling -/

/-- Coordinate-dependent thresholding of a common family of iid uniform random variables. -/
def inhomogeneousThresholdConfiguration {ι : Type*} (q : ι → I)
    (X : ι → ℝ) : Set ι :=
  {i | X i < q i}

theorem measurable_inhomogeneousThresholdConfiguration {ι : Type*} (q : ι → I) :
    Measurable (inhomogeneousThresholdConfiguration q : (ι → ℝ) → Set ι) := by
  change Measurable
    ((fun P : ι → Prop ↦ {i | P i}) ∘
      fun (X : ι → ℝ) (i : ι) ↦ (X i < (q i : ℝ) : Prop))
  refine Measurable.comp (by fun_prop) ?_
  exact measurable_pi_lambda _ fun i ↦
    (measurable_lt_prop _).comp (measurable_pi_apply i)

theorem inhomogeneousThresholdConfiguration_mono {ι : Type*} {q r : ι → I}
    (hqr : ∀ i, q i ≤ r i) (X : ι → ℝ) :
    inhomogeneousThresholdConfiguration q X ⊆
      inhomogeneousThresholdConfiguration r X := by
  intro i hi
  change X i < (q i : ℝ) at hi
  change X i < (r i : ℝ)
  exact lt_of_lt_of_le hi (Subtype.coe_le_coe.mpr (hqr i))

/-- The common-uniform coupling has precisely the requested inhomogeneous product marginal. -/
theorem couplingMeasure_map_inhomogeneousThresholdConfiguration {ι : Type*} (q : ι → I) :
    (couplingMeasure ι).map (inhomogeneousThresholdConfiguration q) =
      inhomogeneousSetBernoulli q := by
  rw [inhomogeneousSetBernoulli_eq_map]
  have hcoord : Measurable fun (X : ι → ℝ) (i : ι) ↦ (X i < (q i : ℝ) : Prop) :=
    measurable_pi_lambda _ fun i ↦
      (measurable_lt_prop _).comp (measurable_pi_apply i)
  have hcomp : (inhomogeneousThresholdConfiguration q : (ι → ℝ) → Set ι) =
      (fun P : ι → Prop ↦ {i | P i}) ∘
        (fun X (i : ι) ↦ (X i < (q i : ℝ) : Prop)) := rfl
  rw [hcomp, ← Measure.map_map (by fun_prop) hcoord, couplingMeasure,
    Measure.infinitePi_map_pi _ fun _ ↦ measurable_lt_prop _]
  congrm Measure.map _ (Measure.infinitePi fun i ↦ ?_)
  rw [volume_restrict_map_lt_prop]
  change bernoulliPropMeasure (q i) = _
  rw [bernoulliPropMeasure]

/-- Increasing events are monotone under coordinatewise enlargement of an inhomogeneous
Bernoulli density profile. -/
theorem IsIncreasingEvent.inhomogeneousSetBernoulli_real_mono {ι : Type*}
    {A : Set (Set ι)} (hA : IsIncreasingEvent A) (hAm : MeasurableSet A)
    {q r : ι → I} (hqr : ∀ i, q i ≤ r i) :
    (inhomogeneousSetBernoulli q).real A ≤
      (inhomogeneousSetBernoulli r).real A := by
  rw [← couplingMeasure_map_inhomogeneousThresholdConfiguration q,
    ← couplingMeasure_map_inhomogeneousThresholdConfiguration r,
    measureReal_def, measureReal_def,
    Measure.map_apply (measurable_inhomogeneousThresholdConfiguration q) hAm,
    Measure.map_apply (measurable_inhomogeneousThresholdConfiguration r) hAm]
  refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono fun X hX ↦ ?_)
  exact hA (inhomogeneousThresholdConfiguration_mono hqr X) hX

/-- The coordinate restriction of an inhomogeneous product is again an inhomogeneous product,
with the pulled-back density profile.  The map is stated for an embedding because later
long-range restrictions include half-lines and finite-coordinate subtypes as well as
equivalences. -/
theorem inhomogeneousSetBernoulli_map_preimage_embedding {α β : Type*}
    (f : α ↪ β) (q : β → I) :
    (inhomogeneousSetBernoulli q).map (fun s : Set β ↦ f ⁻¹' s) =
      inhomogeneousSetBernoulli (q ∘ f) := by
  classical
  rw [inhomogeneousSetBernoulli_eq_map, inhomogeneousSetBernoulli_eq_map]
  rw [Measure.map_map (measurable_preimage_embedding f)
    (by fun_prop : Measurable (fun b : β → Prop ↦ {i | b i}))]
  have hprod :
      (Measure.infinitePi fun i : β ↦ bernoulliPropMeasure (q i)).map
          (fun b : β → Prop ↦ fun a : α ↦ b (f a)) =
        Measure.infinitePi fun a : α ↦ bernoulliPropMeasure ((q ∘ f) a) := by
    simpa only [Function.comp_apply] using
      infinitePi_map_precomp_embedding f (fun i : β ↦ bernoulliPropMeasure (q i))
  rw [← hprod]
  rw [Measure.map_map
    (by fun_prop : Measurable (fun b : α → Prop ↦ {i | b i}))
    (by fun_prop : Measurable (fun b : β → Prop ↦ fun a : α ↦ b (f a)))]
  congr 1

/-- A finite assignment cylinder under a countable inhomogeneous product has the expected
coordinatewise product probability. -/
theorem inhomogeneousSetBernoulli_real_eqOn_finset {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (v : ι → Prop) [DecidablePred v] (q : ι → I) :
    (inhomogeneousSetBernoulli q).real
        {t : Set ι | ∀ i, i ∈ s → ((i ∈ t) = v i)} =
      ∏ i : s, if v i then (q i : ℝ) else (1 - (q i : ℝ)) := by
  classical
  rw [measureReal_def, inhomogeneousSetBernoulli_apply']
  have hpre :
      ((fun b : ι → Prop ↦ {i | b i}) ⁻¹'
          {t : Set ι | ∀ i, i ∈ s → ((i ∈ t) = v i)}) =
        MeasureTheory.cylinder s {b : ∀ i : s, Prop | ∀ i : s, b i = v i} := by
    ext b
    simp [MeasureTheory.cylinder, Finset.restrict]
  rw [hpre, MeasureTheory.Measure.infinitePi_cylinder]
  · have hset : ({b : ∀ i : s, Prop | ∀ i : s, b i = v i} :
        Set (∀ i : s, Prop)) =
        Set.pi Set.univ (fun i : s ↦ ({v i} : Set Prop)) := by
      ext b
      simp
    rw [hset, Measure.pi_pi, ENNReal.toReal_prod]
    apply Finset.prod_congr rfl
    intro i _hi
    by_cases hvi : v i <;> simp [bernoulliPropMeasure, hvi]
  · rw [show ({b : ∀ i : s, Prop | ∀ i : s, b i = v i} :
        Set (∀ i : s, Prop)) =
        Set.pi Set.univ (fun i : s ↦ ({v i} : Set Prop)) by
      ext b
      simp]
    exact MeasurableSet.univ_pi fun i ↦ measurableSet_singleton (v i)

/-- One coordinate is open with its prescribed density. -/
@[simp]
theorem inhomogeneousSetBernoulli_real_mem {ι : Type*} (q : ι → I) (i : ι) :
    (inhomogeneousSetBernoulli q).real {s : Set ι | i ∈ s} = q i := by
  classical
  have h := inhomogeneousSetBernoulli_real_eqOn_finset
    ({i} : Finset ι) (fun _ ↦ True) q
  simpa using h

/-- One coordinate is closed with the complementary density. -/
@[simp]
theorem inhomogeneousSetBernoulli_real_notMem {ι : Type*} (q : ι → I) (i : ι) :
    (inhomogeneousSetBernoulli q).real {s : Set ι | i ∉ s} = 1 - q i := by
  classical
  have h := inhomogeneousSetBernoulli_real_eqOn_finset
    ({i} : Finset ι) (fun _ ↦ False) q
  simpa using h

/-- Probability that every coordinate in a finite set is present. -/
theorem inhomogeneousSetBernoulli_real_superset_finset {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (q : ι → I) :
    (inhomogeneousSetBernoulli q).real {t : Set ι | (s : Set ι) ⊆ t} =
      ∏ i ∈ s, (q i : ℝ) := by
  classical
  have h := inhomogeneousSetBernoulli_real_eqOn_finset s (fun _ ↦ True) q
  change (inhomogeneousSetBernoulli q).real {t : Set ι | ∀ i ∈ s, i ∈ t} = _
  rw [← Finset.prod_attach]
  simpa using h

/-- Probability that every coordinate in a finite set is absent. -/
theorem inhomogeneousSetBernoulli_real_disjoint_finset {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (q : ι → I) :
    (inhomogeneousSetBernoulli q).real {t : Set ι | Disjoint (s : Set ι) t} =
      ∏ i ∈ s, (1 - (q i : ℝ)) := by
  classical
  have h := inhomogeneousSetBernoulli_real_eqOn_finset s (fun _ ↦ False) q
  rw [show ({t : Set ι | Disjoint (s : Set ι) t} : Set (Set ι)) =
      {t : Set ι | ∀ i ∈ s, i ∉ t} by
    ext t
    simp [Set.disjoint_left]]
  change (inhomogeneousSetBernoulli q).real {t : Set ι | ∀ i ∈ s, i ∉ t} = _
  rw [← Finset.prod_attach]
  simpa using h

/-- Joint probability of disjoint finite open and closed prescriptions. -/
theorem inhomogeneousSetBernoulli_real_superset_inter_disjoint_finset
    {ι : Type*} [DecidableEq ι] (s t : Finset ι)
    (hst : Disjoint s t) (q : ι → I) :
    (inhomogeneousSetBernoulli q).real
        ({u : Set ι | (s : Set ι) ⊆ u} ∩ {u : Set ι | Disjoint (t : Set ι) u}) =
      (∏ i ∈ s, (q i : ℝ)) * ∏ i ∈ t, (1 - (q i : ℝ)) := by
  classical
  let v : ι → Prop := fun i ↦ i ∈ s
  have h := inhomogeneousSetBernoulli_real_eqOn_finset (s ∪ t) v q
  have hevent :
      ({u : Set ι | ∀ i, i ∈ s ∪ t → ((i ∈ u) = v i)} : Set (Set ι)) =
        {u : Set ι | (s : Set ι) ⊆ u} ∩ {u : Set ι | Disjoint (t : Set ι) u} := by
    ext u
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, v]
    constructor
    · intro hu
      constructor
      · intro i hi
        exact (hu i (Finset.mem_union_left t hi)).mpr hi
      · rw [Set.disjoint_left]
        intro i hi hiu
        have hiv := hu i (Finset.mem_union_right s hi)
        exact (Finset.disjoint_left.mp hst (hiv.mp hiu) hi)
    · rintro ⟨hus, hut⟩ i hi
      by_cases his : i ∈ s
      · simp [his, hus his]
      · have hit : i ∈ t := (Finset.mem_union.mp hi).resolve_left his
        have hiu : i ∉ u := by
          intro hiu
          exact Set.disjoint_left.mp hut hit hiu
        simp [his, hiu]
  rw [hevent] at h
  rw [Finset.prod_coe_sort (s := s ∪ t)
    (f := fun i ↦ if v i then (q i : ℝ) else (1 - (q i : ℝ)))] at h
  calc
    (inhomogeneousSetBernoulli q).real
        ({u : Set ι | (s : Set ι) ⊆ u} ∩ {u : Set ι | Disjoint (t : Set ι) u}) =
        ∏ i ∈ s ∪ t, if i ∈ s then (q i : ℝ) else (1 - (q i : ℝ)) := by
          simpa [v] using h
    _ = (∏ i ∈ s, (q i : ℝ)) *
        ∏ i ∈ t, (1 - (q i : ℝ)) := by
      rw [Finset.prod_union hst]
      congr 1
      · apply Finset.prod_congr rfl
        intro i hi
        simp [hi]
      · apply Finset.prod_congr rfl
        intro i hi
        have his : i ∉ s := fun his ↦ Finset.disjoint_left.mp hst his hi
        simp [his]

/-! ### Coordinate independence -/

/-- The membership coordinates of an inhomogeneous Bernoulli random set are mutually
independent. -/
theorem inhomogeneousSetBernoulli_iIndepFun_mem {ι : Type*} (q : ι → I) :
    iIndepFun (fun i (s : Set ι) ↦ i ∈ s) (inhomogeneousSetBernoulli q) := by
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map (by fun_prop)]
  rw [inhomogeneousSetBernoulli_eq_map]
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  have hcomp : ((fun ω : Set ι ↦ fun i ↦ i ∈ ω) ∘
      (fun b : ι → Prop ↦ {i | b i})) = id := by
    funext b i
    rfl
  rw [hcomp, Measure.map_id]
  congrm Measure.infinitePi fun i ↦ ?_
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  change bernoulliPropMeasure (q i) =
    (Measure.infinitePi fun i ↦ bernoulliPropMeasure (q i)).map (fun b ↦ b i)
  exact (Measure.infinitePi_map_eval (fun i ↦ bernoulliPropMeasure (q i)) i).symm

/-- The elementary coordinate events are mutually independent under an inhomogeneous product
law. -/
theorem inhomogeneousSetBernoulli_iIndepSet_coordinateEvent {ι : Type*} (q : ι → I) :
    iIndepSet (fun i ↦ {s : Set ι | i ∈ s}) (inhomogeneousSetBernoulli q) := by
  apply iIndep_comap_mem_iff.mp
  simpa only [Set.mem_setOf_eq] using
    (inhomogeneousSetBernoulli_iIndepFun_mem q).iIndep

/-- Sigma algebras generated by disjoint coordinate blocks are independent for an
inhomogeneous product law. -/
theorem indep_generateFrom_coordinateEvents_inhomogeneous {ι : Type*}
    (q : ι → I) {S T : Set ι} (hST : Disjoint S T) :
    Indep (MeasurableSpace.generateFrom (coordinateEvents S))
      (MeasurableSpace.generateFrom (coordinateEvents T))
      (inhomogeneousSetBernoulli q) := by
  exact iIndepSet.indep_generateFrom_of_disjoint
    measurableSet_coordinateEvent
    (inhomogeneousSetBernoulli_iIndepSet_coordinateEvent q) S T hST

/-- Events supported on disjoint finite coordinate sets are independent under an
inhomogeneous Bernoulli product. -/
theorem inhomogeneousSetBernoulli_indepSet_of_dependsOn
    {ι : Type*} (q : ι → I) {E F : Finset ι} (hEF : Disjoint E F)
    {A B : Set (Set ι)} (hA : DependsOn E A) (hB : DependsOn F B) :
    IndepSet A B (inhomogeneousSetBernoulli q) := by
  apply (indep_generateFrom_coordinateEvents_inhomogeneous q
    (show Disjoint (E : Set ι) (F : Set ι) by simpa using hEF)).indepSet_of_measurableSet
  · exact hA.measurableSet_generateFrom_coordinateEvents Set.Subset.rfl
  · exact hB.measurableSet_generateFrom_coordinateEvents Set.Subset.rfl

/-- Events supported on pairwise-disjoint finite coordinate blocks are mutually independent
under an inhomogeneous Bernoulli product. -/
theorem inhomogeneousSetBernoulli_iIndepSet_of_pairwiseDisjoint_dependsOn
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (q : ι → I) (support : κ → Finset ι) (A : κ → Set (Set ι))
    (hdep : ∀ k, DependsOn (support k) (A k))
    (hpair : Set.PairwiseDisjoint (Set.univ : Set κ) support) :
    iIndepSet A (inhomogeneousSetBernoulli q) := by
  classical
  apply (iIndepSet_iff_meas_biInter fun k ↦ (hdep k).measurableSet).2
  intro J
  induction J using Finset.induction_on with
  | empty => simp
  | @insert a J ha ih =>
      have hdisj : Disjoint (support a : Set ι)
          (J.biUnion support : Set ι) := by
        rw [Set.disjoint_left]
        intro e hea heJ
        rw [Finset.coe_biUnion] at heJ
        obtain ⟨b, hbJ, heb⟩ := Set.mem_iUnion₂.mp heJ
        exact Finset.disjoint_left.mp
          (hpair (Set.mem_univ a) (Set.mem_univ b)
            (fun hab ↦ ha (hab ▸ hbJ))) hea heb
      have hind := indep_generateFrom_coordinateEvents_inhomogeneous q hdisj
      have hAa : MeasurableSet[
          MeasurableSpace.generateFrom (coordinateEvents (support a : Set ι))]
          (A a) :=
        (hdep a).measurableSet_generateFrom_coordinateEvents Set.Subset.rfl
      have hAJ : MeasurableSet[
          MeasurableSpace.generateFrom
            (coordinateEvents (J.biUnion support : Set ι))]
          (⋂ k ∈ J, A k) := by
        apply J.measurableSet_biInter
        intro k hk
        apply (hdep k).measurableSet_generateFrom_coordinateEvents
        intro e he
        rw [Finset.coe_biUnion]
        exact Set.mem_iUnion₂.mpr ⟨k, hk, he⟩
      have hprod :
          inhomogeneousSetBernoulli q (A a ∩ ⋂ k ∈ J, A k) =
            inhomogeneousSetBernoulli q (A a) *
              inhomogeneousSetBernoulli q (⋂ k ∈ J, A k) :=
        (ProbabilityTheory.indepSet_iff_measure_inter_eq_mul
          (hdep a).measurableSet
          (J.measurableSet_biInter fun k _hk ↦ (hdep k).measurableSet)
          (inhomogeneousSetBernoulli q)).mp
            (hind.indepSet_of_measurableSet hAa hAJ)
      simpa [ha, ih] using hprod

end Percolation
