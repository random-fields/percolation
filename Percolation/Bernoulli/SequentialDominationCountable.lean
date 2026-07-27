import Percolation.Bernoulli.SequentialDomination

/-!
# Countable sequential domination: finite-cylinder transfer

The finite theorem in `SequentialDomination` is transported along an enumeration of a countable
site set.  This module proves the part of Grimmett (7.64) needed by every finite block event:
if every enumerated finite marginal satisfies the ratio-free prefix inequalities, then every
increasing finite-cylinder event has at least its iid Bernoulli probability.

The extension from finite cylinders to all bounded increasing measurable functions is kept as a
separate topological/measure-theoretic step.  In particular, this file does not silently identify
finite-dimensional domination with the full countable theorem.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval

/-- The first `n` vertices of an enumeration, as an embedding. -/
def enumerationPrefixEmbedding {V : Type*} (e : ℕ ≃ V) (n : ℕ) : Fin n ↪ V :=
  Fin.valEmbedding.trans e.toEmbedding

/-- Restrict a site configuration to the first `n` enumerated vertices. -/
def enumerationPrefixRestriction {V : Type*} (e : ℕ ≃ V) (n : ℕ)
    (η : Set V) : Set (Fin n) :=
  (enumerationPrefixEmbedding e n) ⁻¹' η

theorem measurable_enumerationPrefixRestriction {V : Type*} (e : ℕ ≃ V) (n : ℕ) :
    Measurable (enumerationPrefixRestriction e n : Set V → Set (Fin n)) := by
  change Measurable
    ((fun P : Fin n → Prop ↦ {i | P i}) ∘
      fun (η : Set V) (i : Fin n) ↦ ((enumerationPrefixEmbedding e n i ∈ η) : Prop))
  refine Measurable.comp (by fun_prop) ?_
  exact measurable_pi_lambda _ fun i ↦
    (measurableSet_mem (enumerationPrefixEmbedding e n i)).mem

/-- Pushforward law of the first `n` enumerated coordinates. -/
noncomputable def enumerationPrefixLaw {V : Type*} (e : ℕ ≃ V) (n : ℕ)
    (μ : Measure (Set V)) : Measure (Set (Fin n)) :=
  μ.map (enumerationPrefixRestriction e n)

instance enumerationPrefixLaw_isProbabilityMeasure {V : Type*} (e : ℕ ≃ V) (n : ℕ)
    (μ : Measure (Set V)) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (enumerationPrefixLaw e n μ) := by
  rw [enumerationPrefixLaw]
  exact Measure.isProbabilityMeasure_map
    (measurable_enumerationPrefixRestriction e n).aemeasurable

/-- Reconstruct a configuration on `V` by declaring only the supplied prefix coordinates open. -/
def enumerationPrefixLift {V : Type*} (e : ℕ ≃ V) (n : ℕ)
    (ξ : Set (Fin n)) : Set V :=
  enumerationPrefixEmbedding e n '' ξ

theorem enumerationPrefixLift_mono {V : Type*} (e : ℕ ≃ V) (n : ℕ)
    {ξ ζ : Set (Fin n)} (hξζ : ξ ⊆ ζ) :
    enumerationPrefixLift e n ξ ⊆ enumerationPrefixLift e n ζ :=
  Set.image_mono hξζ

@[simp]
theorem enumerationPrefixRestriction_lift {V : Type*} (e : ℕ ≃ V) (n : ℕ)
    (ξ : Set (Fin n)) :
    enumerationPrefixRestriction e n (enumerationPrefixLift e n ξ) = ξ := by
  ext i
  constructor
  · rintro ⟨j, hj, hji⟩
    exact (enumerationPrefixEmbedding e n).injective hji ▸ hj
  · intro hi
    exact ⟨i, hi, rfl⟩

/-- A prefix long enough to contain a prescribed finite support. -/
def enumerationSupportLength {V : Type*} [DecidableEq V] (e : ℕ ≃ V)
    (R : Finset V) : ℕ :=
  R.sup (fun v ↦ e.symm v) + 1

theorem support_subset_range_enumerationPrefixEmbedding {V : Type*} [DecidableEq V]
    (e : ℕ ≃ V) (R : Finset V) :
    (R : Set V) ⊆ Set.range (enumerationPrefixEmbedding e (enumerationSupportLength e R)) := by
  intro v hv
  have hle : e.symm v ≤ R.sup (fun z ↦ e.symm z) := Finset.le_sup hv
  let i : Fin (enumerationSupportLength e R) :=
    ⟨e.symm v, by rw [enumerationSupportLength]; omega⟩
  refine ⟨i, ?_⟩
  exact e.apply_symm_apply v

/-- Pull a site event back along the finite prefix lift. -/
def enumerationPrefixEvent {V : Type*} (e : ℕ ≃ V) (n : ℕ)
    (A : Set (Set V)) : Set (Set (Fin n)) :=
  enumerationPrefixLift e n ⁻¹' A

theorem IsIncreasingEvent.enumerationPrefixEvent {V : Type*} {A : Set (Set V)}
    (hA : IsIncreasingEvent A) (e : ℕ ≃ V) (n : ℕ) :
    IsIncreasingEvent (enumerationPrefixEvent e n A) := by
  intro ξ ζ hξζ hξ
  exact hA (enumerationPrefixLift_mono e n hξζ) hξ

theorem DependsOn.preimage_enumerationPrefixEvent_eq {V : Type*} [DecidableEq V]
    {R : Finset V} {A : Set (Set V)} (hA : DependsOn R A) (e : ℕ ≃ V) :
    enumerationPrefixRestriction e (enumerationSupportLength e R) ⁻¹'
        enumerationPrefixEvent e (enumerationSupportLength e R) A = A := by
  ext η
  change enumerationPrefixLift e (enumerationSupportLength e R)
      (enumerationPrefixRestriction e (enumerationSupportLength e R) η) ∈ A ↔ η ∈ A
  apply hA
  intro v hv
  obtain ⟨i, hi⟩ := support_subset_range_enumerationPrefixEmbedding e R hv
  constructor
  · rintro ⟨j, hj, hjv⟩
    have hji : j = i := (enumerationPrefixEmbedding e _).injective (hjv.trans hi.symm)
    subst j
    change enumerationPrefixEmbedding e (enumerationSupportLength e R) i ∈ η at hj
    simpa [hi] using hj
  · intro hvη
    exact ⟨i, by simpa [enumerationPrefixRestriction, hi] using hvη, hi⟩

/-- Iid Bernoulli sites restrict to iid Bernoulli sites on an enumerated prefix. -/
theorem setBernoulli_map_enumerationPrefixRestriction {V : Type*} (e : ℕ ≃ V)
    (n : ℕ) (p : I) :
    enumerationPrefixLaw e n setBer((Set.univ : Set V), p) =
      setBer((Set.univ : Set (Fin n)), p) := by
  exact setBernoulli_map_preimage_univ (enumerationPrefixEmbedding e n) p

/-- **Countable sequential criterion (7.64), finite-cylinder event form.**  The full source
criterion will extend this comparison from finite-cylinder events to all bounded increasing
measurable observables. -/
theorem finiteCylinder_measureReal_le_of_prefixSequential {V : Type*} [DecidableEq V]
    (e : ℕ ≃ V) (μ : Measure (Set V)) [IsProbabilityMeasure μ] (p : I)
    (hseq : ∀ n, HasFiniteSequentialLowerBound (enumerationPrefixLaw e n μ) (p : ℝ))
    {R : Finset V} {A : Set (Set V)} (hdep : DependsOn R A)
    (hinc : IsIncreasingEvent A) :
    setBer((Set.univ : Set V), p).real A ≤ μ.real A := by
  let n := enumerationSupportLength e R
  let B := enumerationPrefixEvent e n A
  have hBm : MeasurableSet B := B.toFinite.measurableSet
  have hfin := finiteSequentialLowerBound_measureReal_le
    (enumerationPrefixLaw e n μ) p (hseq n) (hinc.enumerationPrefixEvent e n)
  have hpre : enumerationPrefixRestriction e n ⁻¹' B = A := by
    exact hdep.preimage_enumerationPrefixEvent_eq e
  have hμ : (enumerationPrefixLaw e n μ).real B = μ.real A := by
    rw [enumerationPrefixLaw, map_measureReal_apply
      (measurable_enumerationPrefixRestriction e n) hBm, hpre]
  have hpmap := setBernoulli_map_enumerationPrefixRestriction e n p
  have hp : setBer((Set.univ : Set (Fin n)), p).real B =
      setBer((Set.univ : Set V), p).real A := by
    rw [← hpmap, enumerationPrefixLaw, map_measureReal_apply
      (measurable_enumerationPrefixRestriction e n) hBm, hpre]
  rw [hp, hμ] at hfin
  exact hfin

/-! ### Infinite output from positive-density prefix domination -/

/-- A site configuration contains at least `k` distinct sites.  This injection formulation has
the correct behavior on infinite sets, unlike `Set.ncard`, whose junk value on infinite sets is
zero. -/
def HasAtLeastSites {V : Type*} (k : ℕ) (η : Set V) : Prop :=
  ∃ f : Fin k → V, Function.Injective f ∧ ∀ i, f i ∈ η

theorem isIncreasingEvent_hasAtLeastSites {V : Type*} (k : ℕ) :
    IsIncreasingEvent {η : Set V | HasAtLeastSites k η} := by
  intro η ξ hηξ
  rintro ⟨f, hf, hmem⟩
  exact ⟨f, hf, fun i ↦ hηξ (hmem i)⟩

theorem measurableSet_hasAtLeastSites {V : Type*} [Countable V] (k : ℕ) :
    MeasurableSet {η : Set V | HasAtLeastSites k η} := by
  have hrepr : {η : Set V | HasAtLeastSites k η} =
      ⋃ f : {f : Fin k → V // Function.Injective f},
        ⋂ i : Fin k, {η : Set V | f.1 i ∈ η} := by
    ext η
    simp only [Set.mem_setOf_eq, HasAtLeastSites, Set.mem_iUnion, Set.mem_iInter]
    constructor
    · rintro ⟨f, hf, hmem⟩
      exact ⟨⟨f, hf⟩, hmem⟩
    · rintro ⟨f, hmem⟩
      exact ⟨f.1, f.2, hmem⟩
  rw [hrepr]
  apply MeasurableSet.iUnion
  intro f
  exact MeasurableSet.iInter fun i ↦ measurableSet_mem (f.1 i)

theorem hasAtLeastSites_all_imp_infinite {V : Type*} {η : Set V}
    (h : ∀ k, HasAtLeastSites k η) : η.Infinite := by
  intro hfin
  obtain ⟨f, hf, hmem⟩ := h (hfin.toFinset.card + 1)
  let g : Fin (hfin.toFinset.card + 1) → {v // v ∈ hfin.toFinset} := fun i ↦
    ⟨f i, by simpa using hmem i⟩
  have hg : Function.Injective g := fun _ _ hij ↦ hf (Subtype.ext_iff.mp hij)
  have := Fintype.card_le_of_injective g hg
  simp at this

/-- The coordinate with block label `j` and within-block label `i`. -/
def finiteBlockEmbedding {k m : ℕ} (j : Fin k) : Fin m ↪ Fin (k * m) where
  toFun i := finProdFinEquiv (j, i)
  inj' := fun _ _ h ↦ congrArg Prod.snd (finProdFinEquiv.injective h)

/-- The `j`-th block of `m` coordinates in a Boolean string of length `k*m`. -/
def finiteCoordinateBlock {k m : ℕ} (j : Fin k) : Finset (Fin (k * m)) :=
  Finset.univ.map (finiteBlockEmbedding j)

@[simp]
theorem card_finiteCoordinateBlock {k m : ℕ} (j : Fin k) :
    (finiteCoordinateBlock (m := m) j).card = m := by
  simp [finiteCoordinateBlock]

theorem finiteCoordinateBlock_pairwiseDisjoint {k m : ℕ} :
    Pairwise fun i j : Fin k ↦
      Disjoint (finiteCoordinateBlock (m := m) i) (finiteCoordinateBlock (m := m) j) := by
  intro i j hij
  rw [Finset.disjoint_left]
  intro x hxi hxj
  rw [finiteCoordinateBlock, Finset.mem_map] at hxi hxj
  obtain ⟨a, _ha, hax⟩ := hxi
  obtain ⟨b, _hb, hbx⟩ := hxj
  have hp : (i, a) = (j, b) := finProdFinEquiv.injective (hax.trans hbx.symm)
  exact hij (congrArg Prod.fst hp)

/-- One specified coordinate block is entirely closed. -/
def finiteBlockEmptyEvent {k m : ℕ} (j : Fin k) : Set (Set (Fin (k * m))) :=
  {ξ | Disjoint ((finiteCoordinateBlock (m := m) j : Finset _) : Set _) ξ}

theorem measurableSet_finiteBlockEmptyEvent {k m : ℕ} (j : Fin k) :
    MeasurableSet (finiteBlockEmptyEvent (m := m) j) :=
  measurableSet_disjoint_finset (finiteCoordinateBlock (m := m) j)

theorem setBernoulli_real_finiteBlockEmptyEvent {k m : ℕ} (j : Fin k) (p : I) :
    setBer((Set.univ : Set (Fin (k * m))), p).real
        (finiteBlockEmptyEvent (m := m) j) = (1 - (p : ℝ)) ^ m := by
  simpa [finiteBlockEmptyEvent] using
    setBernoulli_real_open_closed_on_finset_univ (∅ : Finset (Fin (k * m)))
      (finiteCoordinateBlock (m := m) j) p (by simp)

/-- Every one of `k` disjoint coordinate blocks contains an open site. -/
def allFiniteBlocksHit (k m : ℕ) : Set (Set (Fin (k * m))) :=
  {ξ | ∀ j : Fin k, ∃ i : Fin m, finiteBlockEmbedding j i ∈ ξ}

theorem isIncreasingEvent_allFiniteBlocksHit (k m : ℕ) :
    IsIncreasingEvent (allFiniteBlocksHit k m) := by
  intro ξ ζ hξζ hξ j
  obtain ⟨i, hi⟩ := hξ j
  exact ⟨i, hξζ hi⟩

theorem measurableSet_allFiniteBlocksHit (k m : ℕ) :
    MeasurableSet (allFiniteBlocksHit k m) := by
  have hrepr : allFiniteBlocksHit k m =
      ⋂ j : Fin k, ⋃ i : Fin m,
        {ξ : Set (Fin (k * m)) | finiteBlockEmbedding j i ∈ ξ} := by
    ext ξ
    simp [allFiniteBlocksHit]
  rw [hrepr]
  exact MeasurableSet.iInter fun j ↦ MeasurableSet.iUnion fun i ↦
    measurableSet_mem (finiteBlockEmbedding j i)

theorem allFiniteBlocksHit_compl_subset {k m : ℕ} :
    (allFiniteBlocksHit k m)ᶜ ⊆ ⋃ j : Fin k, finiteBlockEmptyEvent (m := m) j := by
  intro ξ hξ
  simp only [Set.mem_compl_iff, allFiniteBlocksHit, Set.mem_setOf_eq, not_forall] at hξ
  obtain ⟨j, hj⟩ := hξ
  simp only [not_exists] at hj
  refine Set.mem_iUnion.mpr ⟨j, ?_⟩
  rw [finiteBlockEmptyEvent, Set.mem_setOf_eq, Set.disjoint_left]
  intro x hx hξx
  change x ∈ finiteCoordinateBlock (m := m) j at hx
  rw [finiteCoordinateBlock, Finset.mem_map] at hx
  obtain ⟨i, _hi, rfl⟩ := hx
  exact hj i hξx

theorem allFiniteBlocksHit_hasAtLeastSites {k m : ℕ} {ξ : Set (Fin (k * m))}
    (hξ : ξ ∈ allFiniteBlocksHit k m) : HasAtLeastSites k ξ := by
  classical
  let chooseIndex : Fin k → Fin m := fun j ↦ Classical.choose (hξ j)
  have hchoose (j : Fin k) : finiteBlockEmbedding j (chooseIndex j) ∈ ξ :=
    Classical.choose_spec (hξ j)
  let f : Fin k → Fin (k * m) := fun j ↦ finiteBlockEmbedding j (chooseIndex j)
  refine ⟨f, ?_, hchoose⟩
  intro i j hij
  have hp : (i, chooseIndex i) = (j, chooseIndex j) :=
    finProdFinEquiv.injective hij
  exact Fin.ext (congrArg (fun z ↦ z.1.val) hp)

theorem one_sub_nat_mul_pow_le_setBernoulli_allFiniteBlocksHit
    (k m : ℕ) (p : I) :
    1 - k * (1 - (p : ℝ)) ^ m ≤
      setBer((Set.univ : Set (Fin (k * m))), p).real (allFiniteBlocksHit k m) := by
  let μ := setBer((Set.univ : Set (Fin (k * m))), p)
  have hcomp : μ.real (allFiniteBlocksHit k m)ᶜ ≤ k * (1 - (p : ℝ)) ^ m := by
    calc
      μ.real (allFiniteBlocksHit k m)ᶜ ≤
          μ.real (⋃ j : Fin k, finiteBlockEmptyEvent (m := m) j) :=
        measureReal_mono allFiniteBlocksHit_compl_subset
      _ ≤ ∑ j : Fin k, μ.real (finiteBlockEmptyEvent (m := m) j) :=
        measureReal_iUnion_fintype_le _
      _ = k * (1 - (p : ℝ)) ^ m := by
        simp [μ, setBernoulli_real_finiteBlockEmptyEvent]
  have hcomplEq : μ.real (allFiniteBlocksHit k m)ᶜ =
      1 - μ.real (allFiniteBlocksHit k m) := by
    rw [measureReal_compl (measurableSet_allFiniteBlocksHit k m), probReal_univ]
  rw [hcomplEq] at hcomp
  linarith

theorem prefix_allFiniteBlocksHit_subset_hasAtLeastSites {V : Type*}
    (e : ℕ ≃ V) (k m : ℕ) :
    enumerationPrefixRestriction e (k * m) ⁻¹' allFiniteBlocksHit k m ⊆
      {η : Set V | HasAtLeastSites k η} := by
  intro η hη
  obtain ⟨f, hf, hmem⟩ := allFiniteBlocksHit_hasAtLeastSites hη
  let g : Fin k → V := fun i ↦ enumerationPrefixEmbedding e (k * m) (f i)
  refine ⟨g, (enumerationPrefixEmbedding e (k * m)).injective.comp hf, ?_⟩
  intro i
  exact hmem i

/-- Positive-density prefix domination forces every finite lower-cardinality event to have
probability one. -/
theorem hasAtLeastSites_probability_eq_one_of_prefixSequential {V : Type*}
    [Countable V] [DecidableEq V] (e : ℕ ≃ V)
    (μ : Measure (Set V)) [IsProbabilityMeasure μ] (p : I) (hp : 0 < (p : ℝ))
    (hseq : ∀ n, HasFiniteSequentialLowerBound (enumerationPrefixLaw e n μ) (p : ℝ))
    (k : ℕ) :
    μ.real {η : Set V | HasAtLeastSites k η} = 1 := by
  apply le_antisymm
    ((measureReal_mono (Set.subset_univ _)).trans_eq probReal_univ)
  by_cases hk : k = 0
  · subst k
    have hEvent : {η : Set V | HasAtLeastSites 0 η} = Set.univ := by
      ext η
      constructor
      · intro _
        trivial
      · intro _
        exact ⟨Fin.elim0, fun i ↦ Fin.elim0 i, fun i ↦ Fin.elim0 i⟩
    rw [hEvent, probReal_univ]
  · apply le_of_forall_pos_le_add
    intro ε hε
    have hkpos : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
    have hq0 : 0 ≤ 1 - (p : ℝ) := sub_nonneg.mpr p.2.2
    have hq1 : 1 - (p : ℝ) < 1 := by linarith
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (div_pos hε hkpos) hq1
    have hkm : (k : ℝ) * (1 - (p : ℝ)) ^ m < ε := by
      calc
        (k : ℝ) * (1 - (p : ℝ)) ^ m < (k : ℝ) * (ε / k) :=
          mul_lt_mul_of_pos_left hm hkpos
        _ = ε := by field_simp
    let B := allFiniteBlocksHit k m
    have hBm : MeasurableSet B := measurableSet_allFiniteBlocksHit k m
    have hfin := finiteSequentialLowerBound_measureReal_le
      (enumerationPrefixLaw e (k * m) μ) p (hseq (k * m))
      (isIncreasingEvent_allFiniteBlocksHit k m)
    have hmap : (enumerationPrefixLaw e (k * m) μ).real B =
        μ.real (enumerationPrefixRestriction e (k * m) ⁻¹' B) := by
      rw [enumerationPrefixLaw, map_measureReal_apply
        (measurable_enumerationPrefixRestriction e (k * m)) hBm]
    have hsub : enumerationPrefixRestriction e (k * m) ⁻¹' B ⊆
        {η : Set V | HasAtLeastSites k η} :=
      prefix_allFiniteBlocksHit_subset_hasAtLeastSites e k m
    have hlower : 1 - (k : ℝ) * (1 - (p : ℝ)) ^ m ≤
        μ.real {η : Set V | HasAtLeastSites k η} := by
      calc
        1 - (k : ℝ) * (1 - (p : ℝ)) ^ m ≤
            setBer((Set.univ : Set (Fin (k * m))), p).real B := by
          exact one_sub_nat_mul_pow_le_setBernoulli_allFiniteBlocksHit k m p
        _ ≤ (enumerationPrefixLaw e (k * m) μ).real B := hfin
        _ = μ.real (enumerationPrefixRestriction e (k * m) ⁻¹' B) := hmap
        _ ≤ μ.real {η : Set V | HasAtLeastSites k η} := measureReal_mono hsub
    linarith

/-- **Exploration consequence of the sequential criterion.** A probability law whose every
enumerated finite marginal satisfies the positive-density prefix bound is concentrated on
infinite site sets.  This is the measure-theoretic conclusion needed in Lemma 7.24. -/
theorem infinite_siteSet_probability_eq_one_of_prefixSequential {V : Type*}
    [Countable V] [DecidableEq V] (e : ℕ ≃ V)
    (μ : Measure (Set V)) [IsProbabilityMeasure μ] (p : I) (hp : 0 < (p : ℝ))
    (hseq : ∀ n, HasFiniteSequentialLowerBound (enumerationPrefixLaw e n μ) (p : ℝ)) :
    μ.real {η : Set V | η.Infinite} = 1 := by
  let A : ℕ → Set (Set V) := fun k ↦ {η | HasAtLeastSites k η}
  have hAm (k : ℕ) : MeasurableSet (A k) := measurableSet_hasAtLeastSites k
  have hAone (k : ℕ) : μ.real (A k) = 1 :=
    hasAtLeastSites_probability_eq_one_of_prefixSequential e μ p hp hseq k
  have hAcNull (k : ℕ) : μ (A k)ᶜ = 0 := by
    apply (measureReal_eq_zero_iff (μ := μ)).mp
    rw [measureReal_compl (hAm k), probReal_univ, hAone k]
    norm_num
  let E : Set (Set V) := ⋂ k, A k
  have hEm : MeasurableSet E := MeasurableSet.iInter hAm
  have hEcNull : μ Eᶜ = 0 := by
    change μ ((⋂ k, A k)ᶜ) = 0
    rw [Set.compl_iInter]
    exact measure_iUnion_null hAcNull
  have hEone : μ.real E = 1 := by
    have hEcReal : μ.real Eᶜ = 0 := (measureReal_eq_zero_iff (μ := μ)).mpr hEcNull
    rw [measureReal_compl hEm, probReal_univ] at hEcReal
    linarith
  have hEsub : E ⊆ {η : Set V | η.Infinite} := by
    intro η hη
    exact hasAtLeastSites_all_imp_infinite fun k ↦ Set.mem_iInter.mp hη k
  apply le_antisymm
    ((measureReal_mono (Set.subset_univ _)).trans_eq probReal_univ)
  exact hEone ▸ measureReal_mono hEsub

end Percolation
