import Percolation.Bernoulli.Basic
import Mathlib.Combinatorics.SetFamily.HarrisKleitman
import Mathlib.MeasureTheory.Constructions.UnitInterval

/-!
# Increasing events for Bernoulli percolation

This file starts the Chapter 2 infrastructure from Grimmett's *Percolation*: events on
edge-configuration spaces that are preserved when more edges are opened.  The definitions are
kept for arbitrary coordinate types, and the final section specializes them to the cubic-lattice
events already developed in `Percolation.Bernoulli.Basic`.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped ENNReal Finset unitInterval BigOperators

/-- An event on configurations `Set ι` is increasing if opening additional coordinates preserves
membership. This is the production version of Grimmett's Chapter 2 increasing events. -/
def IsIncreasingEvent {ι : Type*} (A : Set (Set ι)) : Prop :=
  ∀ ⦃ω η : Set ι⦄, ω ⊆ η → ω ∈ A → η ∈ A

/-- An event is decreasing if its complement is increasing. Equivalently, membership is preserved
when open coordinates are removed. -/
def IsDecreasingEvent {ι : Type*} (A : Set (Set ι)) : Prop :=
  IsIncreasingEvent Aᶜ

theorem IsIncreasingEvent.mono {ι : Type*} {A : Set (Set ι)}
    (hA : IsIncreasingEvent A) {ω η : Set ι} (hωη : ω ⊆ η) (hω : ω ∈ A) :
    η ∈ A :=
  hA hωη hω

theorem isIncreasingEvent_empty {ι : Type*} :
    IsIncreasingEvent (∅ : Set (Set ι)) := by
  intro ω η hωη hω
  exact hω.elim

theorem isIncreasingEvent_univ {ι : Type*} :
    IsIncreasingEvent (Set.univ : Set (Set ι)) := by
  intro ω η hωη hω
  exact Set.mem_univ η

theorem IsIncreasingEvent.inter {ι : Type*} {A B : Set (Set ι)}
    (hA : IsIncreasingEvent A) (hB : IsIncreasingEvent B) :
    IsIncreasingEvent (A ∩ B) := by
  intro ω η hωη hω
  exact ⟨hA hωη hω.1, hB hωη hω.2⟩

theorem IsIncreasingEvent.union {ι : Type*} {A B : Set (Set ι)}
    (hA : IsIncreasingEvent A) (hB : IsIncreasingEvent B) :
    IsIncreasingEvent (A ∪ B) := by
  intro ω η hωη hω
  rcases hω with hω | hω
  · exact Or.inl (hA hωη hω)
  · exact Or.inr (hB hωη hω)

theorem isIncreasingEvent_iInter {ι κ : Type*} {A : κ → Set (Set ι)}
    (hA : ∀ k, IsIncreasingEvent (A k)) :
    IsIncreasingEvent (⋂ k, A k) := by
  intro ω η hωη hω
  rw [Set.mem_iInter] at hω ⊢
  intro k
  exact hA k hωη (hω k)

theorem isIncreasingEvent_iUnion {ι κ : Type*} {A : κ → Set (Set ι)}
    (hA : ∀ k, IsIncreasingEvent (A k)) :
    IsIncreasingEvent (⋃ k, A k) := by
  intro ω η hωη hω
  rw [Set.mem_iUnion] at hω ⊢
  rcases hω with ⟨k, hk⟩
  exact ⟨k, hA k hωη hk⟩

theorem isDecreasingEvent_iff {ι : Type*} {A : Set (Set ι)} :
    IsDecreasingEvent A ↔
      ∀ ⦃ω η : Set ι⦄, ω ⊆ η → η ∈ A → ω ∈ A := by
  constructor
  · intro hA ω η hωη hη
    by_contra hω
    exact hA hωη hω hη
  · intro hA ω η hωη hω hη
    exact hω (hA hωη hη)

theorem IsDecreasingEvent.antitone {ι : Type*} {A : Set (Set ι)}
    (hA : IsDecreasingEvent A) {ω η : Set ι} (hωη : ω ⊆ η) (hη : η ∈ A) :
    ω ∈ A :=
  isDecreasingEvent_iff.mp hA hωη hη

theorem IsDecreasingEvent.inter {ι : Type*} {A B : Set (Set ι)}
    (hA : IsDecreasingEvent A) (hB : IsDecreasingEvent B) :
    IsDecreasingEvent (A ∩ B) := by
  rw [isDecreasingEvent_iff]
  intro ω η hωη hη
  exact ⟨hA.antitone hωη hη.1, hB.antitone hωη hη.2⟩

theorem IsDecreasingEvent.union {ι : Type*} {A B : Set (Set ι)}
    (hA : IsDecreasingEvent A) (hB : IsDecreasingEvent B) :
    IsDecreasingEvent (A ∪ B) := by
  rw [isDecreasingEvent_iff]
  intro ω η hωη hη
  rcases hη with hη | hη
  · exact Or.inl (hA.antitone hωη hη)
  · exact Or.inr (hB.antitone hωη hη)

/-- A random variable on configurations is increasing if opening more coordinates can only
increase its value. This is Grimmett's Chapter 2 order notion for random variables, separated
from measurability/integrability hypotheses. -/
def IsIncreasingRandomVariable {ι α : Type*} [Preorder α] (N : Set ι → α) : Prop :=
  ∀ ⦃ω η : Set ι⦄, ω ⊆ η → N ω ≤ N η

theorem IsIncreasingRandomVariable.mono {ι α : Type*} [Preorder α] {N : Set ι → α}
    (hN : IsIncreasingRandomVariable N) {ω η : Set ι} (hωη : ω ⊆ η) :
    N ω ≤ N η :=
  hN hωη

/-- Grimmett's uniform-threshold configuration: the coordinate `e` is open at parameter `p`
when the coupled uniform variable `X e` is below `p`. -/
def thresholdConfiguration {ι : Type*} (p : I) (X : ι → ℝ) : Set ι :=
  {e | X e < (p : ℝ)}

@[simp]
theorem mem_thresholdConfiguration_iff {ι : Type*} (p : I) (X : ι → ℝ) (e : ι) :
    e ∈ thresholdConfiguration p X ↔ X e < (p : ℝ) :=
  Iff.rfl

/-- The core deterministic step in Grimmett's proof of Theorem (2.1): using the same threshold
variables for both parameters gives an ordered pair of configurations. -/
theorem thresholdConfiguration_subset_of_le {ι : Type*} {p q : I}
    (hpq : (p : ℝ) ≤ q) (X : ι → ℝ) :
    thresholdConfiguration p X ⊆ thresholdConfiguration q X := by
  intro e he
  exact lt_of_lt_of_le he hpq

theorem IsIncreasingRandomVariable.thresholdConfiguration_mono {ι α : Type*} [Preorder α]
    {N : Set ι → α} (hN : IsIncreasingRandomVariable N) {p q : I}
    (hpq : (p : ℝ) ≤ q) (X : ι → ℝ) :
    N (thresholdConfiguration p X) ≤ N (thresholdConfiguration q X) :=
  hN (thresholdConfiguration_subset_of_le hpq X)

theorem IsIncreasingEvent.thresholdConfiguration_mem_mono {ι : Type*} {A : Set (Set ι)}
    (hA : IsIncreasingEvent A) {p q : I} (hpq : (p : ℝ) ≤ q) (X : ι → ℝ)
    (hmem : thresholdConfiguration p X ∈ A) :
    thresholdConfiguration q X ∈ A :=
  hA (thresholdConfiguration_subset_of_le hpq X) hmem

/-- Indicator functions of increasing events are increasing random variables, exactly as in
Grimmett's proof of the event part of Theorem (2.1). -/
theorem IsIncreasingEvent.indicator_isIncreasingRandomVariable {ι : Type*}
    {A : Set (Set ι)} (hA : IsIncreasingEvent A) :
    IsIncreasingRandomVariable (fun ω : Set ι ↦ A.indicator (fun _ ↦ (1 : ℝ)) ω) := by
  intro ω η hωη
  change A.indicator (fun _ ↦ (1 : ℝ)) ω ≤ A.indicator (fun _ ↦ (1 : ℝ)) η
  by_cases hω : ω ∈ A
  · have hη : η ∈ A := hA hωη hω
    rw [Set.indicator_of_mem hω, Set.indicator_of_mem hη]
  · rw [Set.indicator_of_notMem hω]
    by_cases hη : η ∈ A
    · rw [Set.indicator_of_mem hη]
      norm_num
    · rw [Set.indicator_of_notMem hη]

/-- The expectation step in Grimmett's proof of Theorem (2.1), isolated from the later fact that
thresholding iid uniforms has Bernoulli law. The hypotheses `hp` and `hq` are the formal version
of "so long as these mean values exist". -/
theorem IsIncreasingRandomVariable.integral_thresholdConfiguration_mono {ι Ω : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ι → ℝ} {N : Set ι → ℝ}
    (hN : IsIncreasingRandomVariable N) {p q : I} (hpq : (p : ℝ) ≤ q)
    (hp : Integrable (fun ω ↦ N (thresholdConfiguration p (X ω))) μ)
    (hq : Integrable (fun ω ↦ N (thresholdConfiguration q (X ω))) μ) :
    (∫ ω, N (thresholdConfiguration p (X ω)) ∂μ) ≤
      ∫ ω, N (thresholdConfiguration q (X ω)) ∂μ := by
  exact integral_mono hp hq fun ω ↦ hN.thresholdConfiguration_mono hpq (X ω)

theorem IsIncreasingEvent.thresholdConfiguration_event_subset {ι Ω : Type*}
    {A : Set (Set ι)} (hA : IsIncreasingEvent A) {p q : I} (hpq : (p : ℝ) ≤ q)
    (X : Ω → ι → ℝ) :
    {ω : Ω | thresholdConfiguration p (X ω) ∈ A} ⊆
      {ω : Ω | thresholdConfiguration q (X ω) ∈ A} := by
  intro ω hω
  exact hA.thresholdConfiguration_mem_mono hpq (X ω) hω

theorem IsIncreasingEvent.measure_thresholdConfiguration_event_mono {ι Ω : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω} {A : Set (Set ι)} (hA : IsIncreasingEvent A)
    {p q : I} (hpq : (p : ℝ) ≤ q) (X : Ω → ι → ℝ) :
    μ {ω : Ω | thresholdConfiguration p (X ω) ∈ A} ≤
      μ {ω : Ω | thresholdConfiguration q (X ω) ∈ A} :=
  measure_mono (hA.thresholdConfiguration_event_subset hpq X)

theorem IsIncreasingEvent.measureReal_thresholdConfiguration_event_mono {ι Ω : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ] {A : Set (Set ι)}
    (hA : IsIncreasingEvent A) {p q : I} (hpq : (p : ℝ) ≤ q) (X : Ω → ι → ℝ) :
    μ.real {ω : Ω | thresholdConfiguration p (X ω) ∈ A} ≤
      μ.real {ω : Ω | thresholdConfiguration q (X ω) ∈ A} :=
  measureReal_mono (hA.thresholdConfiguration_event_subset hpq X)

theorem IsIncreasingEvent.integral_indicator_thresholdConfiguration_mono {ι Ω : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ι → ℝ} {A : Set (Set ι)}
    (hA : IsIncreasingEvent A) {p q : I} (hpq : (p : ℝ) ≤ q)
    (hp : Integrable
      (fun ω ↦ A.indicator (fun _ ↦ (1 : ℝ)) (thresholdConfiguration p (X ω))) μ)
    (hq : Integrable
      (fun ω ↦ A.indicator (fun _ ↦ (1 : ℝ)) (thresholdConfiguration q (X ω))) μ) :
    (∫ ω, A.indicator (fun _ ↦ (1 : ℝ)) (thresholdConfiguration p (X ω)) ∂μ) ≤
      ∫ ω, A.indicator (fun _ ↦ (1 : ℝ)) (thresholdConfiguration q (X ω)) ∂μ :=
  hA.indicator_isIncreasingRandomVariable.integral_thresholdConfiguration_mono hpq hp hq

/-- A single uniform variable thresholded at `p` has Bernoulli law with parameter `p`. -/
theorem unitInterval_volume_map_lt (p : I) :
    Measure.map (fun x : I ↦ (x : ℝ) < (p : ℝ)) volume =
      unitInterval.toNNReal p • Measure.dirac True +
        unitInterval.toNNReal (σ p) • Measure.dirac False := by
  ext s hs
  rw [Measure.map_apply]
  · by_cases htrue : True ∈ s <;> by_cases hfalse : False ∈ s
    · have hs_univ : s = Set.univ := by
        ext b
        by_cases hb : b <;> simp [hb, htrue, hfalse]
      simp [hs_univ]
    · have hs_true : s = ({True} : Set Prop) := by
        ext b
        by_cases hb : b <;> simp [hb, htrue, hfalse]
      rw [hs_true]
      simp [unitInterval.toNNReal]
      calc
        volume (Set.Iio p) = ENNReal.ofReal (p : ℝ) := unitInterval.volume_Iio p
        _ = (unitInterval.toNNReal p : ℝ≥0∞) := by
          rw [ENNReal.coe_nnreal_eq, unitInterval.coe_toNNReal]
    · have hs_false : s = ({False} : Set Prop) := by
        ext b
        by_cases hb : b <;> simp [hb, htrue, hfalse]
      rw [hs_false]
      simp [unitInterval.toNNReal]
      calc
        volume (Set.Ici p) = ENNReal.ofReal (1 - (p : ℝ)) := unitInterval.volume_Ici p
        _ = (unitInterval.toNNReal (σ p) : ℝ≥0∞) := by
          rw [ENNReal.coe_nnreal_eq, unitInterval.coe_toNNReal]
          rfl
    · have hs_empty : s = ∅ := by
        ext b
        by_cases hb : b <;> simp [hb, htrue, hfalse]
      simp [hs_empty]
  · fun_prop
  · exact hs

/-- Iid unit-interval thresholds give the product Bernoulli law on Boolean coordinate functions. -/
theorem infinitePi_volume_map_lt {ι : Type*} (p : I) :
    Measure.map (fun X : ι → I ↦ fun i ↦ (X i : ℝ) < (p : ℝ))
        (Measure.infinitePi fun _ : ι ↦ (volume : Measure I)) =
      Measure.infinitePi fun _ : ι ↦
        unitInterval.toNNReal p • Measure.dirac True +
          unitInterval.toNNReal (σ p) • Measure.dirac False := by
  let μB : ι → Measure Prop := fun _ ↦
    unitInterval.toNNReal p • Measure.dirac True +
      unitInterval.toNNReal (σ p) • Measure.dirac False
  change Measure.map (fun X : ι → I ↦ fun i ↦ (X i : ℝ) < (p : ℝ))
        (Measure.infinitePi fun _ : ι ↦ (volume : Measure I)) = Measure.infinitePi μB
  refine Measure.eq_infinitePi μB ?_
  intro s t ht
  rw [Measure.map_apply]
  · have hpre :
        (fun X : ι → I ↦ fun i ↦ (X i : ℝ) < (p : ℝ)) ⁻¹'
            Set.pi ((s : Finset ι) : Set ι) t =
          Set.pi ((s : Finset ι) : Set ι)
            (fun i ↦ {x : I | ((x : ℝ) < (p : ℝ)) ∈ t i}) := by
      ext X
      simp [Set.mem_pi]
    rw [hpre, Measure.infinitePi_pi]
    · apply Finset.prod_congr rfl
      intro i hi
      have hcoord := congrArg (fun μ : Measure Prop ↦ μ (t i)) (unitInterval_volume_map_lt p)
      change (Measure.map (fun x : I ↦ (x : ℝ) < (p : ℝ)) volume) (t i) =
        μB i (t i) at hcoord
      rw [Measure.map_apply] at hcoord
      · exact hcoord
      · fun_prop
      · exact ht i
    · intro i hi
      exact (ht i).preimage (by fun_prop : Measurable fun x : I ↦ (x : ℝ) < (p : ℝ))
  · fun_prop
  · exact MeasurableSet.pi (Finset.countable_toSet s) fun i hi ↦ ht i

/-- Grimmett's iid-uniform threshold construction has Bernoulli product marginal law. -/
theorem infinitePi_volume_map_thresholdConfiguration {ι : Type*} (p : I) :
    Measure.map (fun X : ι → I ↦ thresholdConfiguration p (fun i ↦ (X i : ℝ)))
        (Measure.infinitePi fun _ : ι ↦ (volume : Measure I)) =
      setBer((Set.univ : Set ι), p) := by
  rw [setBernoulli_eq_map]
  simp only [Set.mem_univ]
  rw [← infinitePi_volume_map_lt (ι := ι) p]
  change Measure.map (fun X : ι → I ↦ thresholdConfiguration p (fun i ↦ (X i : ℝ)))
      (Measure.infinitePi fun _ : ι ↦ (volume : Measure I)) =
    Measure.map (⇑(MeasurableEquiv.setOf : (ι → Prop) ≃ᵐ Set ι))
      (Measure.map (fun X : ι → I ↦ fun i ↦ (X i : ℝ) < (p : ℝ))
        (Measure.infinitePi fun _ : ι ↦ (volume : Measure I)))
  rw [Measure.map_map MeasurableEquiv.setOf.measurable]
  · rfl
  · fun_prop

/-- A monotone coupling of two configuration laws: both configurations are built on one sample
space, have the requested marginal laws, and are ordered pointwise. This is the theorem-facing
abstraction produced by Grimmett's iid-uniform threshold construction. -/
def IsMonotoneCoupling {ι Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) (μ₁ μ₂ : Measure (Set ι)) (η₁ η₂ : Ω → Set ι) : Prop :=
  Measurable η₁ ∧ Measurable η₂ ∧ Measure.map η₁ ν = μ₁ ∧ Measure.map η₂ ν = μ₂ ∧
    ∀ ω, η₁ ω ⊆ η₂ ω

theorem IsMonotoneCoupling.measurable_left {ι Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} {μ₁ μ₂ : Measure (Set ι)} {η₁ η₂ : Ω → Set ι}
    (h : IsMonotoneCoupling ν μ₁ μ₂ η₁ η₂) :
    Measurable η₁ :=
  h.1

theorem IsMonotoneCoupling.measurable_right {ι Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} {μ₁ μ₂ : Measure (Set ι)} {η₁ η₂ : Ω → Set ι}
    (h : IsMonotoneCoupling ν μ₁ μ₂ η₁ η₂) :
    Measurable η₂ :=
  h.2.1

theorem IsMonotoneCoupling.map_left {ι Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} {μ₁ μ₂ : Measure (Set ι)} {η₁ η₂ : Ω → Set ι}
    (h : IsMonotoneCoupling ν μ₁ μ₂ η₁ η₂) :
    Measure.map η₁ ν = μ₁ :=
  h.2.2.1

theorem IsMonotoneCoupling.map_right {ι Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} {μ₁ μ₂ : Measure (Set ι)} {η₁ η₂ : Ω → Set ι}
    (h : IsMonotoneCoupling ν μ₁ μ₂ η₁ η₂) :
    Measure.map η₂ ν = μ₂ :=
  h.2.2.2.1

theorem IsMonotoneCoupling.ordered {ι Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} {μ₁ μ₂ : Measure (Set ι)} {η₁ η₂ : Ω → Set ι}
    (h : IsMonotoneCoupling ν μ₁ μ₂ η₁ η₂) (ω : Ω) :
    η₁ ω ⊆ η₂ ω :=
  h.2.2.2.2 ω

/-- The event-probability conclusion of Grimmett's Theorem (2.1), abstracted from the
construction of the coupling. -/
theorem IsIncreasingEvent.measureReal_le_of_monotoneCoupling {ι Ω : Type*}
    [MeasurableSpace Ω] {ν : Measure Ω} [IsFiniteMeasure ν]
    {μ₁ μ₂ : Measure (Set ι)} {η₁ η₂ : Ω → Set ι}
    {A : Set (Set ι)} (hA : IsIncreasingEvent A) (hAmeas : MeasurableSet A)
    (hc : IsMonotoneCoupling ν μ₁ μ₂ η₁ η₂) :
    μ₁.real A ≤ μ₂.real A := by
  rw [← hc.map_left, ← hc.map_right]
  rw [map_measureReal_apply hc.measurable_left hAmeas,
    map_measureReal_apply hc.measurable_right hAmeas]
  exact measureReal_mono fun ω hω ↦ hA (hc.ordered ω) hω

theorem measurable_thresholdConfiguration_unitInterval {ι : Type*} (p : I) :
    Measurable (fun X : ι → I ↦ thresholdConfiguration p (fun i ↦ (X i : ℝ))) := by
  change Measurable
    ((MeasurableEquiv.setOf : (ι → Prop) ≃ᵐ Set ι) ∘
      (fun X : ι → I ↦ fun i ↦ (X i : ℝ) < (p : ℝ)))
  exact MeasurableEquiv.setOf.measurable.comp (by fun_prop)

/-- The monotone coupling in Grimmett's proof of Theorem (2.1), built from iid unit-interval
threshold variables. -/
theorem infinitePi_volume_thresholdConfiguration_isMonotoneCoupling {ι : Type*}
    {p q : I} (hpq : (p : ℝ) ≤ q) :
    IsMonotoneCoupling (Measure.infinitePi fun _ : ι ↦ (volume : Measure I))
      setBer((Set.univ : Set ι), p) setBer((Set.univ : Set ι), q)
      (fun X : ι → I ↦ thresholdConfiguration p (fun i ↦ (X i : ℝ)))
      (fun X : ι → I ↦ thresholdConfiguration q (fun i ↦ (X i : ℝ))) := by
  refine ⟨measurable_thresholdConfiguration_unitInterval p,
    measurable_thresholdConfiguration_unitInterval q,
    infinitePi_volume_map_thresholdConfiguration p,
    infinitePi_volume_map_thresholdConfiguration q, ?_⟩
  intro X
  exact thresholdConfiguration_subset_of_le hpq (fun i ↦ (X i : ℝ))

/-- Grimmett's Theorem (2.1), event part, for Bernoulli product measures on arbitrary coordinates:
probabilities of measurable increasing events are non-decreasing in `p`. -/
theorem IsIncreasingEvent.setBernoulli_real_mono {ι : Type*} {A : Set (Set ι)}
    (hA : IsIncreasingEvent A) (hAmeas : MeasurableSet A) {p q : I}
    (hpq : (p : ℝ) ≤ q) :
    setBer((Set.univ : Set ι), p).real A ≤ setBer((Set.univ : Set ι), q).real A :=
  hA.measureReal_le_of_monotoneCoupling hAmeas
    (infinitePi_volume_thresholdConfiguration_isMonotoneCoupling hpq)

/-- Grimmett's Theorem (2.1), random-variable part, for Bernoulli product measures on arbitrary
coordinates. The integrability hypotheses are the formal version of "so long as these mean values
exist". -/
theorem IsIncreasingRandomVariable.setBernoulli_integral_mono {ι : Type*}
    {N : Set ι → ℝ} (hN : IsIncreasingRandomVariable N) {p q : I} (hpq : (p : ℝ) ≤ q)
    (hp : Integrable N setBer((Set.univ : Set ι), p))
    (hq : Integrable N setBer((Set.univ : Set ι), q)) :
    (∫ ω, N ω ∂setBer((Set.univ : Set ι), p)) ≤
      ∫ ω, N ω ∂setBer((Set.univ : Set ι), q) := by
  let ν : Measure (ι → I) := Measure.infinitePi fun _ : ι ↦ (volume : Measure I)
  let ηp : (ι → I) → Set ι := fun X ↦ thresholdConfiguration p (fun i ↦ (X i : ℝ))
  let ηq : (ι → I) → Set ι := fun X ↦ thresholdConfiguration q (fun i ↦ (X i : ℝ))
  have hηp : Measurable ηp := measurable_thresholdConfiguration_unitInterval p
  have hηq : Measurable ηq := measurable_thresholdConfiguration_unitInterval q
  have hpmap : Measure.map ηp ν = setBer((Set.univ : Set ι), p) := by
    simpa [ν, ηp] using infinitePi_volume_map_thresholdConfiguration (ι := ι) p
  have hqmap : Measure.map ηq ν = setBer((Set.univ : Set ι), q) := by
    simpa [ν, ηq] using infinitePi_volume_map_thresholdConfiguration (ι := ι) q
  have hp_map_int : Integrable N (Measure.map ηp ν) := by
    rw [hpmap]
    exact hp
  have hq_map_int : Integrable N (Measure.map ηq ν) := by
    rw [hqmap]
    exact hq
  have hp_comp : Integrable (fun X ↦ N (ηp X)) ν := by
    simpa [Function.comp_def, ηp] using hp_map_int.comp_measurable hηp
  have hq_comp : Integrable (fun X ↦ N (ηq X)) ν := by
    simpa [Function.comp_def, ηq] using hq_map_int.comp_measurable hηq
  rw [← hpmap, ← hqmap]
  rw [integral_map hηp.aemeasurable hp_map_int.aestronglyMeasurable]
  rw [integral_map hηq.aemeasurable hq_map_int.aestronglyMeasurable]
  exact hN.integral_thresholdConfiguration_mono hpq hp_comp hq_comp

/-- Restrict an arbitrary configuration to a finite coordinate support. -/
noncomputable def restrictTo {ι : Type*} [DecidableEq ι]
    (E : Finset ι) (ω : Set ι) : Finset ι := by
  classical
  exact E.filter fun e ↦ e ∈ ω

@[simp]
theorem mem_restrictTo_iff {ι : Type*} [DecidableEq ι]
    (E : Finset ι) (ω : Set ι) (e : ι) :
    e ∈ restrictTo E ω ↔ e ∈ E ∧ e ∈ ω := by
  classical
  simp [restrictTo]

theorem restrictTo_subset {ι : Type*} [DecidableEq ι]
    (E : Finset ι) (ω : Set ι) :
    restrictTo E ω ⊆ E := by
  intro e he
  exact (mem_restrictTo_iff E ω e).mp he |>.1

theorem restrictTo_subset_configuration {ι : Type*} [DecidableEq ι]
    (E : Finset ι) (ω : Set ι) :
    ((restrictTo E ω : Finset ι) : Set ι) ⊆ ω := by
  intro e he
  exact (mem_restrictTo_iff E ω e).mp he |>.2

/-- A finite-support event only depends on the coordinates in `E`. -/
def DependsOn {ι : Type*} (E : Finset ι) (A : Set (Set ι)) : Prop :=
  ∀ ⦃ω η : Set ι⦄, (∀ e ∈ E, (e ∈ ω ↔ e ∈ η)) → (ω ∈ A ↔ η ∈ A)

/-- The finite trace of an event on a support `E`. Its elements are finite configurations contained
in `E` that make the event occur. -/
noncomputable def eventTrace {ι : Type*} [DecidableEq ι]
    (E : Finset ι) (A : Set (Set ι)) : Finset (Finset ι) := by
  classical
  exact E.powerset.filter fun s ↦ ((s : Finset ι) : Set ι) ∈ A

@[simp]
theorem mem_eventTrace_iff {ι : Type*} [DecidableEq ι]
    (E : Finset ι) (A : Set (Set ι)) (s : Finset ι) :
    s ∈ eventTrace E A ↔ s ⊆ E ∧ ((s : Finset ι) : Set ι) ∈ A := by
  classical
  simp [eventTrace]

/-- Rebuild an event from a finite trace by looking only at the coordinates in `E`. -/
noncomputable def eventOfTrace {ι : Type*} [DecidableEq ι]
    (E : Finset ι) (T : Set (Finset ι)) : Set (Set ι) :=
  {ω | restrictTo E ω ∈ T}

theorem dependsOn_eventOfTrace {ι : Type*} [DecidableEq ι]
    (E : Finset ι) (T : Set (Finset ι)) :
    DependsOn E (eventOfTrace E T) := by
  intro ω η hcoord
  have hrestrict : restrictTo E ω = restrictTo E η := by
    ext e
    by_cases he : e ∈ E
    · simp [restrictTo, he, hcoord e he]
    · simp [restrictTo, he]
  simp [eventOfTrace, hrestrict]

theorem restrictTo_mem_eventTrace_iff_of_dependsOn {ι : Type*} [DecidableEq ι]
    {E : Finset ι} {A : Set (Set ι)} (hA : DependsOn E A) (ω : Set ι) :
    restrictTo E ω ∈ eventTrace E A ↔ ω ∈ A := by
  classical
  rw [mem_eventTrace_iff]
  constructor
  · intro hω
    have hcoord :
        ∀ e ∈ E, (e ∈ ((restrictTo E ω : Finset ι) : Set ι) ↔ e ∈ ω) := by
      intro e he
      simp [restrictTo, he]
    exact (hA hcoord).mp hω.2
  · intro hω
    refine ⟨restrictTo_subset E ω, ?_⟩
    have hcoord :
        ∀ e ∈ E, (e ∈ ω ↔ e ∈ ((restrictTo E ω : Finset ι) : Set ι)) := by
      intro e he
      simp [restrictTo, he]
    exact (hA hcoord).mp hω

/-- A finite trace is increasing relative to its ambient support. -/
def IsIncreasingTrace {ι : Type*} (E : Finset ι) (T : Set (Finset ι)) : Prop :=
  ∀ ⦃s t : Finset ι⦄, s ⊆ t → t ⊆ E → s ∈ T → t ∈ T

theorem IsIncreasingEvent.eventTrace {ι : Type*} [DecidableEq ι]
    {E : Finset ι} {A : Set (Set ι)} (hA : IsIncreasingEvent A) :
    IsIncreasingTrace E (eventTrace E A) := by
  intro s t hst htE hs
  exact (mem_eventTrace_iff E A t).mpr
    ⟨htE, hA (by intro e he; exact hst he) ((mem_eventTrace_iff E A s).mp hs).2⟩

theorem IsIncreasingTrace.eventOfTrace {ι : Type*} [DecidableEq ι]
    {E : Finset ι} {T : Set (Finset ι)} (hT : IsIncreasingTrace E T) :
    IsIncreasingEvent (eventOfTrace E T) := by
  intro ω η hωη hω
  exact hT (by
    intro e he
    rw [mem_restrictTo_iff] at he ⊢
    exact ⟨he.1, hωη he.2⟩) (restrictTo_subset E η) hω

/-- The finite family of configurations of a finite coordinate type that realize an event. -/
noncomputable def finiteEventFamily {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Set (Set ι)) : Finset (Finset ι) := by
  classical
  exact Finset.univ.filter fun s ↦ ((s : Finset ι) : Set ι) ∈ A

@[simp]
theorem mem_finiteEventFamily_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Set (Set ι)) (s : Finset ι) :
    s ∈ finiteEventFamily A ↔ ((s : Finset ι) : Set ι) ∈ A := by
  classical
  simp [finiteEventFamily]

theorem IsIncreasingEvent.isUpperSet_finiteEventFamily {ι : Type*}
    [Fintype ι] [DecidableEq ι] {A : Set (Set ι)}
    (hA : IsIncreasingEvent A) :
    IsUpperSet (finiteEventFamily A : Set (Finset ι)) := by
  intro s t hst hs
  exact (mem_finiteEventFamily_iff A t).mpr
    (hA (by intro e he; exact hst he) ((mem_finiteEventFamily_iff A s).mp hs))

/-- The uniform-measure finite FKG/Harris cardinal inequality. This is the `p = 1/2` finite
product-space core of Grimmett's Theorem 2.4, delegated to Mathlib's Harris-Kleitman theorem. -/
theorem finiteUniform_fkg_card {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Set (Set ι)} (hA : IsIncreasingEvent A) (hB : IsIncreasingEvent B) :
    (finiteEventFamily A).card * (finiteEventFamily B).card ≤
      2 ^ Fintype.card ι * (finiteEventFamily (A ∩ B)).card := by
  classical
  have hHK :=
    (hA.isUpperSet_finiteEventFamily).le_card_inter_finset
      (hB.isUpperSet_finiteEventFamily)
  have hInter :
      finiteEventFamily (A ∩ B) = finiteEventFamily A ∩ finiteEventFamily B := by
    ext s
    simp [finiteEventFamily]
  simpa [hInter] using hHK

/-- Uniform probability of an event on a finite coordinate cube. This is the `p = 1/2` product
measure written as normalized counting measure on `Finset ι`. -/
noncomputable def finiteUniformEventProbability {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Set (Set ι)) : ℝ :=
  (finiteEventFamily A).card / (2 ^ Fintype.card ι : ℝ)

theorem finiteUniformEventProbability_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Set (Set ι)) :
    0 ≤ finiteUniformEventProbability A := by
  classical
  unfold finiteUniformEventProbability
  positivity

theorem finiteUniformEventProbability_le_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Set (Set ι)) :
    finiteUniformEventProbability A ≤ 1 := by
  classical
  unfold finiteUniformEventProbability
  have hcard : (finiteEventFamily A).card ≤ Fintype.card (Finset ι) :=
    Finset.card_le_univ _
  rw [Fintype.card_finset] at hcard
  have hden_pos : (0 : ℝ) < (2 ^ Fintype.card ι : ℝ) := by positivity
  have hcard_real :
      ((finiteEventFamily A).card : ℝ) ≤ (2 ^ Fintype.card ι : ℝ) := by
    exact_mod_cast hcard
  exact (div_le_one hden_pos).mpr hcard_real

/-- The uniform finite-product FKG/Harris inequality in probability form. -/
theorem finiteUniform_fkg_probability {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Set (Set ι)} (hA : IsIncreasingEvent A) (hB : IsIncreasingEvent B) :
    finiteUniformEventProbability A * finiteUniformEventProbability B ≤
      finiteUniformEventProbability (A ∩ B) := by
  classical
  let d : ℝ := (2 : ℝ) ^ Fintype.card ι
  have hd_pos : 0 < d := by
    dsimp [d]
    positivity
  have hcard := finiteUniform_fkg_card hA hB
  have hreal :
      ((finiteEventFamily A).card * (finiteEventFamily B).card : ℝ) ≤
        d * (finiteEventFamily (A ∩ B)).card := by
    dsimp [d]
    exact_mod_cast hcard
  unfold finiteUniformEventProbability
  change ((finiteEventFamily A).card : ℝ) / d *
      (((finiteEventFamily B).card : ℝ) / d) ≤
    ((finiteEventFamily (A ∩ B)).card : ℝ) / d
  field_simp [hd_pos.ne']
  nlinarith

section Cubic

theorem isIncreasingEvent_openEdgeSetEvent (d : ℕ) (s : Finset (CubicEdge d)) :
    IsIncreasingEvent (openEdgeSetEvent d s) := by
  intro ω η hωη hω
  exact Set.Subset.trans hω hωη

theorem isDecreasingEvent_closedEdgeSetEvent (d : ℕ) (s : Finset (CubicEdge d)) :
    IsDecreasingEvent (closedEdgeSetEvent d s) := by
  rw [isDecreasingEvent_iff]
  intro ω η hωη hη
  exact hη.mono_right hωη

theorem isIncreasingEvent_walkIsOpen {d : ℕ} {u v : Cubic d}
    (w : (cubicGraph d).Walk u v) :
    IsIncreasingEvent {ω : EdgeConfiguration d | walkIsOpen ω w} := by
  intro ω η hωη hω e he
  exact hωη (hω e he)

theorem isIncreasingEvent_selfAvoidingWalkIsOpen {d n : ℕ}
    (steps : SelfAvoidingWalk d n) :
    IsIncreasingEvent {ω : EdgeConfiguration d | selfAvoidingWalkIsOpen ω steps} := by
  simpa [selfAvoidingWalkIsOpen] using
    isIncreasingEvent_walkIsOpen (selfAvoidingWalkWalk steps)

theorem isIncreasingEvent_existsOpenSelfAvoidingWalk (d n : ℕ) :
    IsIncreasingEvent {ω : EdgeConfiguration d | existsOpenSelfAvoidingWalk d n ω} := by
  intro ω η hωη hω
  rcases hω with ⟨steps, hsteps⟩
  exact ⟨steps, isIncreasingEvent_selfAvoidingWalkIsOpen steps hωη hsteps⟩

theorem isIncreasingEvent_hasOpenPathOfLengthExactly (d n : ℕ) :
    IsIncreasingEvent {ω : EdgeConfiguration d | hasOpenPathOfLengthExactly d ω n} := by
  intro ω η hωη hω
  change hasOpenPathOfLengthExactly d ω n at hω
  change hasOpenPathOfLengthExactly d η n
  rw [hasOpenPathOfLengthExactly_iff_existsOpenSelfAvoidingWalk] at hω ⊢
  exact isIncreasingEvent_existsOpenSelfAvoidingWalk d n hωη hω

theorem isIncreasingEvent_hasOpenPathOfLengthAtLeast (d n : ℕ) :
    IsIncreasingEvent {ω : EdgeConfiguration d | hasOpenPathOfLengthAtLeast d ω n} := by
  intro ω η hωη hω
  change hasOpenPathOfLengthAtLeast d ω n at hω
  change hasOpenPathOfLengthAtLeast d η n
  rw [hasOpenPathOfLengthAtLeast_iff_hasOpenPathOfLengthExactly] at hω ⊢
  exact isIncreasingEvent_hasOpenPathOfLengthExactly d n hωη hω

theorem isIncreasingEvent_hasOpenPathOfLengthExactlyFrom (d : ℕ) (x : Cubic d) (n : ℕ) :
    IsIncreasingEvent {ω : EdgeConfiguration d | hasOpenPathOfLengthExactlyFrom d ω x n} := by
  intro ω η hωη hω
  rcases hω with ⟨v, w, hwpath, hwlen, hopen⟩
  exact ⟨v, w, hwpath, hwlen, isIncreasingEvent_walkIsOpen w hωη hopen⟩

theorem isIncreasingEvent_hasOpenPathOfLengthAtLeastFrom (d : ℕ) (x : Cubic d) (n : ℕ) :
    IsIncreasingEvent {ω : EdgeConfiguration d | hasOpenPathOfLengthAtLeastFrom d ω x n} := by
  intro ω η hωη hω
  change hasOpenPathOfLengthAtLeastFrom d ω x n at hω
  change hasOpenPathOfLengthAtLeastFrom d η x n
  rw [hasOpenPathOfLengthAtLeastFrom_iff_hasOpenPathOfLengthExactlyFrom] at hω ⊢
  exact isIncreasingEvent_hasOpenPathOfLengthExactlyFrom d x n hωη hω

theorem isIncreasingEvent_hasArbitrarilyLongOpenPaths (d : ℕ) :
    IsIncreasingEvent {ω : EdgeConfiguration d | hasArbitrarilyLongOpenPaths d ω} := by
  intro ω η hωη hω n
  exact isIncreasingEvent_hasOpenPathOfLengthAtLeast d n hωη (hω n)

theorem isIncreasingEvent_hasArbitrarilyLongOpenPathsFrom (d : ℕ) (x : Cubic d) :
    IsIncreasingEvent {ω : EdgeConfiguration d | hasArbitrarilyLongOpenPathsFrom d ω x} := by
  intro ω η hωη hω n
  exact isIncreasingEvent_hasOpenPathOfLengthAtLeastFrom d x n hωη (hω n)

theorem isIncreasingEvent_hasInfiniteOpenCluster (d : ℕ) :
    IsIncreasingEvent {ω : EdgeConfiguration d | hasInfiniteOpenCluster d ω} := by
  intro ω η hωη hω
  change hasInfiniteOpenCluster d ω at hω
  change hasInfiniteOpenCluster d η
  rw [hasInfiniteOpenCluster_iff_hasArbitrarilyLongOpenPaths] at hω ⊢
  exact isIncreasingEvent_hasArbitrarilyLongOpenPaths d hωη hω

theorem isIncreasingEvent_hasInfiniteOpenClusterFrom (d : ℕ) (x : Cubic d) :
    IsIncreasingEvent {ω : EdgeConfiguration d | hasInfiniteOpenClusterFrom d ω x} := by
  intro ω η hωη hω
  change hasInfiniteOpenClusterFrom d ω x at hω
  change hasInfiniteOpenClusterFrom d η x
  rw [hasInfiniteOpenClusterFrom_iff_hasArbitrarilyLongOpenPathsFrom] at hω ⊢
  exact isIncreasingEvent_hasArbitrarilyLongOpenPathsFrom d x hωη hω

/-- A finite indexed family of walks with common endpoints has an increasing open-path event. -/
def existsOpenWalkIn {d : ℕ} {u v : Cubic d} {β : Type*}
    (s : Finset β) (walk : β → (cubicGraph d).Walk u v)
    (ω : EdgeConfiguration d) : Prop :=
  ∃ b ∈ s, walkIsOpen ω (walk b)

theorem isIncreasingEvent_existsOpenWalkIn {d : ℕ} {u v : Cubic d}
    {β : Type*} (s : Finset β) (walk : β → (cubicGraph d).Walk u v) :
    IsIncreasingEvent {ω : EdgeConfiguration d | existsOpenWalkIn s walk ω} := by
  intro ω η hωη hω
  rcases hω with ⟨b, hb, hbopen⟩
  exact ⟨b, hb, isIncreasingEvent_walkIsOpen (walk b) hωη hbopen⟩

/-- Grimmett's Theorem (2.1) for any increasing cubic event once a monotone coupling with the
two Bernoulli bond marginals has been constructed. The remaining source-facing step is to supply
this coupling from iid uniform thresholds. -/
theorem IsIncreasingEvent.bernoulliBondMeasure_real_le_of_monotoneCoupling (d : ℕ)
    {p q : I} {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsFiniteMeasure ν]
    {ηp ηq : Ω → EdgeConfiguration d} {A : Set (EdgeConfiguration d)}
    (hA : IsIncreasingEvent A) (hAmeas : MeasurableSet A)
    (hc : IsMonotoneCoupling ν (bernoulliBondMeasure d p) (bernoulliBondMeasure d q) ηp ηq) :
    (bernoulliBondMeasure d p).real A ≤ (bernoulliBondMeasure d q).real A :=
  hA.measureReal_le_of_monotoneCoupling hAmeas hc

/-- Grimmett's Theorem (2.1), event part, for Bernoulli bond percolation on `ℤ^d`. -/
theorem IsIncreasingEvent.bernoulliBondMeasure_real_mono (d : ℕ)
    {A : Set (EdgeConfiguration d)} (hA : IsIncreasingEvent A) (hAmeas : MeasurableSet A)
    {p q : I} (hpq : (p : ℝ) ≤ q) :
    (bernoulliBondMeasure d p).real A ≤ (bernoulliBondMeasure d q).real A := by
  simpa [bernoulliBondMeasure] using hA.setBernoulli_real_mono hAmeas hpq

/-- Grimmett's Theorem (2.1), random-variable part, for Bernoulli bond percolation on `ℤ^d`. -/
theorem IsIncreasingRandomVariable.bernoulliBondMeasure_integral_mono (d : ℕ)
    {N : EdgeConfiguration d → ℝ} (hN : IsIncreasingRandomVariable N)
    {p q : I} (hpq : (p : ℝ) ≤ q)
    (hp : Integrable N (bernoulliBondMeasure d p))
    (hq : Integrable N (bernoulliBondMeasure d q)) :
    (∫ ω, N ω ∂bernoulliBondMeasure d p) ≤ ∫ ω, N ω ∂bernoulliBondMeasure d q := by
  simpa [bernoulliBondMeasure] using hN.setBernoulli_integral_mono hpq hp hq

/-- A finite all-open cylinder monotonicity corollary of Grimmett's Theorem (2.1). -/
theorem bernoulliBondMeasure_real_openEdgeSetEvent_mono (d : ℕ)
    (s : Finset (CubicEdge d)) {p q : I} (hpq : (p : ℝ) ≤ q) :
    (bernoulliBondMeasure d p).real (openEdgeSetEvent d s) ≤
      (bernoulliBondMeasure d q).real (openEdgeSetEvent d s) := by
  rw [bernoulliBondMeasure_real_openEdgeSetEvent,
    bernoulliBondMeasure_real_openEdgeSetEvent]
  exact pow_le_pow_left₀ p.2.1 hpq s.card

/-- Closed finite cylinders are antitone in the Bernoulli edge parameter. -/
theorem bernoulliBondMeasure_real_closedEdgeSetEvent_antitone (d : ℕ)
    (s : Finset (CubicEdge d)) {p q : I} (hpq : (p : ℝ) ≤ q) :
    (bernoulliBondMeasure d q).real (closedEdgeSetEvent d s) ≤
      (bernoulliBondMeasure d p).real (closedEdgeSetEvent d s) := by
  rw [bernoulliBondMeasure_real_closedEdgeSetEvent,
    bernoulliBondMeasure_real_closedEdgeSetEvent]
  exact pow_le_pow_left₀ (sub_nonneg.mpr q.2.2) (by linarith) s.card

end Cubic

end Percolation
