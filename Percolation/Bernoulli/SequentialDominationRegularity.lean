import Percolation.Bernoulli.SequentialDominationCountable
import Mathlib.MeasureTheory.Measure.Regular

/-!
# Regularity lift for countable stochastic domination

Finite-dimensional stochastic domination controls finite-cylinder events.  This file proves
the missing regularity step in Grimmett's sequential criterion (7.64): on a countable site
space, domination of every increasing finite-cylinder event implies domination of every
bounded increasing measurable observable.

The proof transports configurations to the compact Boolean product space.  Inner and outer
regularity reduce a hypothetical failure to a compact set inside an open set.  Compactness
then inserts a finite union of positive cylinders between them, contradicting the assumed
finite-cylinder comparison.  The final event-to-expectation step is the existing layer-cake
theorem `stochasticallyDominates_of_measureReal_le`.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval

variable {V : Type*}

/-- The measurable equivalence between subsets and Boolean coordinate vectors. -/
noncomputable def setBoolMeasurableEquiv : Set V ≃ᵐ (V → Bool) where
  toEquiv :=
    { toFun := fun eta i => @decide (i ∈ eta) (Classical.propDecidable _)
      invFun := fun x => {i | x i = true}
      left_inv := fun eta => by ext i; simp
      right_inv := fun x => by
        funext i
        generalize hi : x i = b
        cases b <;> simp [hi] }
  measurable_toFun := by
    apply measurable_pi_lambda
    intro i
    apply measurable_to_bool
    convert measurableSet_mem i using 1
    ext eta
    simp
  measurable_invFun := by
    apply measurable_pi_lambda
    intro i
    exact ((measurableSet_singleton true).preimage (measurable_pi_apply i)).mem

@[simp]
theorem setBoolMeasurableEquiv_apply_eq_true (eta : Set V) (i : V) :
    setBoolMeasurableEquiv eta i = true ↔ i ∈ eta := by
  simp [setBoolMeasurableEquiv]

@[simp]
theorem mem_setBoolMeasurableEquiv_symm (x : V → Bool) (i : V) :
    i ∈ setBoolMeasurableEquiv.symm x ↔ x i = true := Iff.rfl

/-- Coordinatewise inclusion on Boolean configuration vectors. -/
def BoolConfigurationLE (x y : V → Bool) : Prop :=
  ∀ i, x i = true → y i = true

/-- An increasing event in the Boolean product encoding. -/
def IsIncreasingBoolConfigurationEvent (A : Set (V → Bool)) : Prop :=
  ∀ ⦃x y⦄, BoolConfigurationLE x y → x ∈ A → y ∈ A

/-- The positive cylinder requiring every site in `R` to be open. -/
def boolPositiveCylinder (R : Finset V) : Set (V → Bool) :=
  {x | ∀ i ∈ R, x i = true}

theorem isOpen_boolPositiveCylinder (R : Finset V) :
    IsOpen (boolPositiveCylinder R) := by
  rw [show boolPositiveCylinder R =
      ⋂ i ∈ R, (fun x : V → Bool => x i) ⁻¹' {true} by
    ext x
    simp [boolPositiveCylinder]]
  exact isOpen_biInter_finset fun i _hi =>
    (isOpen_discrete ({true} : Set Bool)).preimage (continuous_apply i)

theorem isIncreasingBoolConfigurationEvent_boolPositiveCylinder (R : Finset V) :
    IsIncreasingBoolConfigurationEvent (boolPositiveCylinder R) := by
  intro x y hxy hx i hi
  exact hxy i (hx i hi)

/-- Every point of an increasing event has a positive finite-cylinder neighborhood inside
any prescribed open superset of that event. -/
theorem exists_boolPositiveCylinder_subset_open_of_increasing [DecidableEq V]
    {A U : Set (V → Bool)} (hA : IsIncreasingBoolConfigurationEvent A)
    (hAU : A ⊆ U) (hU : IsOpen U) {x : V → Bool} (hx : x ∈ A) :
    ∃ R : Finset V, (∀ i ∈ R, x i = true) ∧ boolPositiveCylinder R ⊆ U := by
  let W : {i // x i = true} → Set (V → Bool) :=
    fun i => (fun y : V → Bool => y i.1) ⁻¹' {false}
  have hWopen : ∀ i, IsOpen (W i) := fun i =>
    (isOpen_discrete ({false} : Set Bool)).preimage (continuous_apply i.1)
  have hcover : Uᶜ ⊆ ⋃ i, W i := by
    intro y hy
    by_contra hall
    have hxy : BoolConfigurationLE x y := by
      intro i hi
      by_cases hyi : y i = true
      · exact hyi
      · have hyfalse : y i = false := Bool.eq_false_of_not_eq_true hyi
        exact (hall (Set.mem_iUnion.mpr ⟨⟨i, hi⟩, hyfalse⟩)).elim
    exact hy (hAU (hA hxy hx))
  obtain ⟨t, ht⟩ := hU.isClosed_compl.isCompact.elim_finite_subcover W hWopen hcover
  let R : Finset V := t.image Subtype.val
  refine ⟨R, ?_, ?_⟩
  · intro i hi
    simp only [R, Finset.mem_image] at hi
    obtain ⟨j, _hj, rfl⟩ := hi
    exact j.2
  · intro y hy
    by_contra hyU
    have hcovered := ht hyU
    simp only [Set.mem_iUnion, W, Set.mem_preimage, Set.mem_singleton_iff] at hcovered
    obtain ⟨j, hjt, hjfalse⟩ := hcovered
    have hjtrue : y j.1 = true := hy j.1 (Finset.mem_image.mpr ⟨j, hjt, rfl⟩)
    simp [hjtrue] at hjfalse

/-- A compact subset of an increasing Boolean event and an open superset admit an intermediate
increasing finite-cylinder event. -/
theorem exists_finiteIncreasingCylinder_between_compact_open [DecidableEq V]
    {K A U : Set (V → Bool)} (hK : IsCompact K) (hKA : K ⊆ A)
    (hA : IsIncreasingBoolConfigurationEvent A) (hAU : A ⊆ U) (hU : IsOpen U) :
    ∃ (R : Finset V) (D : Set (V → Bool)),
      K ⊆ D ∧ D ⊆ U ∧ IsOpen D ∧
        IsIncreasingBoolConfigurationEvent D ∧
          DependsOn R (setBoolMeasurableEquiv ⁻¹' D) := by
  have hex : ∀ x : K, ∃ R : Finset V,
      (∀ i ∈ R, x.1 i = true) ∧ boolPositiveCylinder R ⊆ U := by
    intro x
    exact exists_boolPositiveCylinder_subset_open_of_increasing
      hA hAU hU (hKA x.2)
  let support : K → Finset V := fun x => (hex x).choose
  let C : K → Set (V → Bool) := fun x => boolPositiveCylinder (support x)
  have hxC : ∀ x : K, x.1 ∈ C x := fun x => (hex x).choose_spec.1
  have hCU : ∀ x : K, C x ⊆ U := fun x => (hex x).choose_spec.2
  have hopen : ∀ x : K, IsOpen (C x) := fun x =>
    isOpen_boolPositiveCylinder (support x)
  have hcover : K ⊆ ⋃ x : K, C x := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hxC ⟨x, hx⟩⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover C hopen hcover
  let R : Finset V := t.biUnion support
  let D : Set (V → Bool) := ⋃ x, ⋃ (_hx : x ∈ t), C x
  refine ⟨R, D, ht, ?_, ?_, ?_, ?_⟩
  · intro y hy
    simp only [D, Set.mem_iUnion] at hy
    obtain ⟨x, _hxt, hyC⟩ := hy
    exact hCU x hyC
  · exact isOpen_iUnion fun x => isOpen_iUnion fun _hx => hopen x
  · intro x y hxy hx
    simp only [D, Set.mem_iUnion] at hx ⊢
    obtain ⟨z, hzt, hxCz⟩ := hx
    exact ⟨z, hzt,
      isIncreasingBoolConfigurationEvent_boolPositiveCylinder (support z) hxy hxCz⟩
  · intro eta xi heq
    simp only [Set.mem_preimage, D, Set.mem_iUnion]
    constructor
    · rintro ⟨x, hxt, heta⟩
      refine ⟨x, hxt, ?_⟩
      change ∀ i ∈ support x, setBoolMeasurableEquiv xi i = true
      change ∀ i ∈ support x, setBoolMeasurableEquiv eta i = true at heta
      intro i hi
      apply (setBoolMeasurableEquiv_apply_eq_true xi i).mpr
      apply (heq i (Finset.mem_biUnion.mpr ⟨x, hxt, hi⟩)).mp
      exact (setBoolMeasurableEquiv_apply_eq_true eta i).mp (heta i hi)
    · rintro ⟨x, hxt, hxi⟩
      refine ⟨x, hxt, ?_⟩
      change ∀ i ∈ support x, setBoolMeasurableEquiv eta i = true
      change ∀ i ∈ support x, setBoolMeasurableEquiv xi i = true at hxi
      intro i hi
      apply (setBoolMeasurableEquiv_apply_eq_true eta i).mpr
      apply (heq i (Finset.mem_biUnion.mpr ⟨x, hxt, hi⟩)).mpr
      exact (setBoolMeasurableEquiv_apply_eq_true xi i).mp (hxi i hi)

/-- On a countable site set, increasing finite-cylinder event comparison implies stochastic
domination in Grimmett's full expectation formulation. -/
theorem stochasticallyDominates_of_finiteCylinder_measureReal_le
    [Countable V] [DecidableEq V]
    (mu nu : Measure (Set V)) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (hfinite : ∀ (R : Finset V) (A : Set (Set V)),
      DependsOn R A → IsIncreasingEvent A → nu.real A ≤ mu.real A) :
    StochasticallyDominates mu nu := by
  apply stochasticallyDominates_of_measureReal_le mu nu
  intro A hAm hA
  let e : Set V ≃ᵐ (V → Bool) := setBoolMeasurableEquiv
  let muB : Measure (V → Bool) := mu.map e
  let nuB : Measure (V → Bool) := nu.map e
  let B : Set (V → Bool) := e.symm ⁻¹' A
  have hBm : MeasurableSet B := hAm.preimage e.symm.measurable
  have hBinc : IsIncreasingBoolConfigurationEvent B := by
    intro x y hxy hx
    apply hA _ hx
    intro i hi
    change x i = true at hi
    change y i = true
    exact hxy i hi
  have hmuB : muB B = mu A := by
    change (mu.map e) B = mu A
    rw [MeasurableEquiv.map_apply]
    apply congrArg mu
    ext eta
    change e.symm (e eta) ∈ A ↔ eta ∈ A
    rw [e.symm_apply_apply]
  have hnuB : nuB B = nu A := by
    change (nu.map e) B = nu A
    rw [MeasurableEquiv.map_apply]
    apply congrArg nu
    ext eta
    change e.symm (e eta) ∈ A ↔ eta ∈ A
    rw [e.symm_apply_apply]
  have hmeasure : nu A ≤ mu A := by
    rw [← hnuB, ← hmuB]
    by_contra hnot
    have hlt : muB B < nuB B := lt_of_not_ge hnot
    letI : IsProbabilityMeasure muB :=
      Measure.isProbabilityMeasure_map e.measurable.aemeasurable
    letI : IsProbabilityMeasure nuB :=
      Measure.isProbabilityMeasure_map e.measurable.aemeasurable
    obtain ⟨K, hKB, hKcompact, hmuK⟩ :=
      hBm.exists_lt_isCompact_of_ne_top (measure_ne_top nuB B) hlt
    obtain ⟨U, hBU, hUopen, hUK⟩ :=
      B.exists_isOpen_lt_of_lt (μ := muB) (nuB K) hmuK
    obtain ⟨R, D, hKD, hDU, _hDopen, hDinc, hDdep⟩ :=
      exists_finiteIncreasingCylinder_between_compact_open
        hKcompact hKB hBinc hBU hUopen
    let E : Set (Set V) := e ⁻¹' D
    have hEinc : IsIncreasingEvent E := by
      intro eta xi hetaxi heta
      apply hDinc _ heta
      intro i hi
      rw [show e eta i = true ↔ i ∈ eta by
        exact setBoolMeasurableEquiv_apply_eq_true eta i] at hi
      rw [show e xi i = true ↔ i ∈ xi by
        exact setBoolMeasurableEquiv_apply_eq_true xi i]
      exact hetaxi hi
    have hreal := hfinite R E hDdep hEinc
    have hmeasureE : nu E ≤ mu E := by
      calc
        nu E = ENNReal.ofReal (nu.real E) :=
          (ofReal_measureReal (μ := nu) (s := E)).symm
        _ ≤ ENNReal.ofReal (mu.real E) := ENNReal.ofReal_le_ofReal hreal
        _ = mu E := ofReal_measureReal (μ := mu) (s := E)
    have hnuDmuD : nuB D ≤ muB D := by
      change (nu.map e) D ≤ (mu.map e) D
      rw [MeasurableEquiv.map_apply, MeasurableEquiv.map_apply]
      exact hmeasureE
    have hchain : nuB K ≤ muB U :=
      (measure_mono hKD).trans (hnuDmuD.trans (measure_mono hDU))
    exact (not_le_of_gt hUK) hchain
  exact ENNReal.toReal_mono (measure_ne_top mu A) hmeasure

/-- **Countable sequential criterion (7.64).**  Ratio-free one-step lower bounds on every
enumerated finite marginal imply full stochastic domination of iid Bernoulli sites. -/
theorem sequentialLowerBound_stochasticallyDominates
    [Countable V] [DecidableEq V]
    (e : ℕ ≃ V) (mu : Measure (Set V)) [IsProbabilityMeasure mu] (p : I)
    (hseq : ∀ n, HasFiniteSequentialLowerBound (enumerationPrefixLaw e n mu) (p : ℝ)) :
    StochasticallyDominates mu setBer((Set.univ : Set V), p) := by
  apply stochasticallyDominates_of_finiteCylinder_measureReal_le
  intro R A hdep hinc
  exact finiteCylinder_measureReal_le_of_prefixSequential
    e mu p hseq hdep hinc

end Percolation
