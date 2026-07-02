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

theorem DependsOn.mono {ι : Type*} {E F : Finset ι} {A : Set (Set ι)}
    (hA : DependsOn E A) (hEF : E ⊆ F) :
    DependsOn F A := by
  intro ω η hcoord
  exact hA fun e he ↦ hcoord e (hEF he)

theorem DependsOn.inter {ι : Type*} {E : Finset ι} {A B : Set (Set ι)}
    (hA : DependsOn E A) (hB : DependsOn E B) :
    DependsOn E (A ∩ B) := by
  intro ω η hcoord
  exact and_congr (hA hcoord) (hB hcoord)

theorem DependsOn.union {ι : Type*} {E : Finset ι} {A B : Set (Set ι)}
    (hA : DependsOn E A) (hB : DependsOn E B) :
    DependsOn E (A ∪ B) := by
  intro ω η hcoord
  exact or_congr (hA hcoord) (hB hcoord)

theorem DependsOn.compl {ι : Type*} {E : Finset ι} {A : Set (Set ι)}
    (hA : DependsOn E A) :
    DependsOn E Aᶜ := by
  intro ω η hcoord
  exact not_congr (hA hcoord)

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

theorem eventTrace_inter {ι : Type*} [DecidableEq ι]
    (E : Finset ι) (A B : Set (Set ι)) :
    eventTrace E (A ∩ B) = eventTrace E A ∩ eventTrace E B := by
  ext s
  simp [eventTrace, and_assoc, and_left_comm]

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

/-- A finite trace is decreasing relative to its ambient support. -/
def IsDecreasingTrace {ι : Type*} (E : Finset ι) (T : Set (Finset ι)) : Prop :=
  ∀ ⦃s t : Finset ι⦄, s ⊆ t → t ⊆ E → t ∈ T → s ∈ T

theorem IsIncreasingEvent.eventTrace {ι : Type*} [DecidableEq ι]
    {E : Finset ι} {A : Set (Set ι)} (hA : IsIncreasingEvent A) :
    IsIncreasingTrace E (eventTrace E A) := by
  intro s t hst htE hs
  exact (mem_eventTrace_iff E A t).mpr
    ⟨htE, hA (by intro e he; exact hst he) ((mem_eventTrace_iff E A s).mp hs).2⟩

theorem IsDecreasingEvent.eventTrace {ι : Type*} [DecidableEq ι]
    {E : Finset ι} {A : Set (Set ι)} (hA : IsDecreasingEvent A) :
    IsDecreasingTrace E (eventTrace E A) := by
  intro s t hst hsE ht
  exact (mem_eventTrace_iff E A s).mpr
    ⟨hst.trans hsE,
      hA.antitone (by intro e he; exact hst he) ((mem_eventTrace_iff E A t).mp ht).2⟩

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

/-- A real-valued observable on a finite cube is increasing when it is monotone under adding
coordinates inside the ambient support. This is the finite-coordinate random-variable predicate
used in Grimmett's induction proof of FKG. -/
def IsIncreasingFinsetFunction {ι : Type*} (E : Finset ι) (X : Finset ι → ℝ) : Prop :=
  ∀ ⦃s t : Finset ι⦄, s ⊆ t → t ⊆ E → X s ≤ X t

/-- A real-valued observable on a finite cube is decreasing when it is antitone under adding
coordinates inside the ambient support. -/
def IsDecreasingFinsetFunction {ι : Type*} (E : Finset ι) (X : Finset ι → ℝ) : Prop :=
  ∀ ⦃s t : Finset ι⦄, s ⊆ t → t ⊆ E → X t ≤ X s

theorem IsIncreasingFinsetFunction.mono {ι : Type*} {E : Finset ι} {X : Finset ι → ℝ}
    (hX : IsIncreasingFinsetFunction E X) {s t : Finset ι} (hst : s ⊆ t) (htE : t ⊆ E) :
    X s ≤ X t :=
  hX hst htE

theorem IsDecreasingFinsetFunction.antitone {ι : Type*} {E : Finset ι}
    {X : Finset ι → ℝ} (hX : IsDecreasingFinsetFunction E X) {s t : Finset ι}
    (hst : s ⊆ t) (htE : t ⊆ E) :
    X t ≤ X s :=
  hX hst htE

theorem IsIncreasingFinsetFunction.neg_isDecreasingFinsetFunction {ι : Type*}
    {E : Finset ι} {X : Finset ι → ℝ} (hX : IsIncreasingFinsetFunction E X) :
    IsDecreasingFinsetFunction E (fun s ↦ -X s) := by
  intro s t hst htE
  exact neg_le_neg (hX.mono hst htE)

theorem IsDecreasingFinsetFunction.neg_isIncreasingFinsetFunction {ι : Type*}
    {E : Finset ι} {X : Finset ι → ℝ} (hX : IsDecreasingFinsetFunction E X) :
    IsIncreasingFinsetFunction E (fun s ↦ -X s) := by
  intro s t hst htE
  exact neg_le_neg (hX.antitone hst htE)

theorem IsIncreasingFinsetFunction.empty_le_singleton {ι : Type*} {a : ι}
    {X : Finset ι → ℝ} (hX : IsIncreasingFinsetFunction ({a} : Finset ι) X) :
    X ∅ ≤ X {a} :=
  hX.mono (Finset.empty_subset _) (by intro e he; exact he)

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

/-- Weighted Bernoulli expectation for a real-valued observable on the finite cube of subsets of
`E`. This is the finite-coordinate product measure used in Grimmett's proof of FKG before the
martingale limiting step. -/
noncomputable def finiteBernoulliExpectation {ι : Type*} [DecidableEq ι]
    (E : Finset ι) (p : ℝ) (X : Finset ι → ℝ) : ℝ :=
  E.powerset.sum fun s ↦ p ^ s.card * (1 - p) ^ (E.card - s.card) * X s

@[simp]
theorem finiteBernoulliExpectation_empty {ι : Type*} [DecidableEq ι]
    (p : ℝ) (X : Finset ι → ℝ) :
    finiteBernoulliExpectation (∅ : Finset ι) p X = X ∅ := by
  simp [finiteBernoulliExpectation]

/-- Finite Bernoulli expectation preserves pointwise inequalities on the supporting cube when
`0 ≤ p ≤ 1`. -/
theorem finiteBernoulliExpectation_mono {ι : Type*} [DecidableEq ι]
    {E : Finset ι} {p : ℝ} {X Y : Finset ι → ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hXY : ∀ ⦃s : Finset ι⦄, s ⊆ E → X s ≤ Y s) :
    finiteBernoulliExpectation E p X ≤ finiteBernoulliExpectation E p Y := by
  unfold finiteBernoulliExpectation
  refine Finset.sum_le_sum ?_
  intro s hs
  have hsE : s ⊆ E := Finset.mem_powerset.mp hs
  have hq0 : 0 ≤ 1 - p := sub_nonneg.mpr hp1
  have hweight : 0 ≤ p ^ s.card * (1 - p) ^ (E.card - s.card) :=
    mul_nonneg (pow_nonneg hp0 _) (pow_nonneg hq0 _)
  exact mul_le_mul_of_nonneg_left (hXY hsE) hweight

/-- Finite Bernoulli expectation only depends on values on the supporting cube. -/
theorem finiteBernoulliExpectation_congr {ι : Type*} [DecidableEq ι]
    {E : Finset ι} {p : ℝ} {X Y : Finset ι → ℝ}
    (hXY : ∀ ⦃s : Finset ι⦄, s ⊆ E → X s = Y s) :
    finiteBernoulliExpectation E p X = finiteBernoulliExpectation E p Y := by
  unfold finiteBernoulliExpectation
  apply Finset.sum_congr rfl
  intro s hs
  rw [hXY (Finset.mem_powerset.mp hs)]

/-- Pull a scalar out of a finite Bernoulli expectation. -/
theorem finiteBernoulliExpectation_const_mul {ι : Type*} [DecidableEq ι]
    (E : Finset ι) (p c : ℝ) (X : Finset ι → ℝ) :
    finiteBernoulliExpectation E p (fun s ↦ c * X s) =
      c * finiteBernoulliExpectation E p X := by
  unfold finiteBernoulliExpectation
  calc
    E.powerset.sum (fun s ↦ p ^ s.card * (1 - p) ^ (E.card - s.card) * (c * X s)) =
        E.powerset.sum
          (fun s ↦ c * (p ^ s.card * (1 - p) ^ (E.card - s.card) * X s)) := by
      apply Finset.sum_congr rfl
      intro s _hs
      ring
    _ = c * E.powerset.sum
        (fun s ↦ p ^ s.card * (1 - p) ^ (E.card - s.card) * X s) := by
      rw [Finset.mul_sum]

/-- Negation commutes with finite Bernoulli expectation. -/
theorem finiteBernoulliExpectation_neg {ι : Type*} [DecidableEq ι]
    (E : Finset ι) (p : ℝ) (X : Finset ι → ℝ) :
    finiteBernoulliExpectation E p (fun s ↦ -X s) =
      -finiteBernoulliExpectation E p X := by
  rw [show (fun s ↦ -X s) = fun s ↦ (-1 : ℝ) * X s by
    funext s
    ring]
  rw [finiteBernoulliExpectation_const_mul]
  ring

/-- Additivity of finite Bernoulli expectation. -/
theorem finiteBernoulliExpectation_add {ι : Type*} [DecidableEq ι]
    (E : Finset ι) (p : ℝ) (X Y : Finset ι → ℝ) :
    finiteBernoulliExpectation E p (fun s ↦ X s + Y s) =
      finiteBernoulliExpectation E p X + finiteBernoulliExpectation E p Y := by
  unfold finiteBernoulliExpectation
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _hs
  ring

/-- Subtractivity of finite Bernoulli expectation. -/
theorem finiteBernoulliExpectation_sub {ι : Type*} [DecidableEq ι]
    (E : Finset ι) (p : ℝ) (X Y : Finset ι → ℝ) :
    finiteBernoulliExpectation E p (fun s ↦ X s - Y s) =
      finiteBernoulliExpectation E p X - finiteBernoulliExpectation E p Y := by
  unfold finiteBernoulliExpectation
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro s _hs
  ring

/-- Expectation of a random variable on one Bernoulli coordinate, with values `x0` at the closed
state and `x1` at the open state. This is the scalar base case used in Grimmett's proof of the
finite FKG inequality. -/
noncomputable def twoPointBernoulliExpectation (p x0 x1 : ℝ) : ℝ :=
  (1 - p) * x0 + p * x1

/-- Monotonicity of the one-coordinate Bernoulli expectation in both endpoint values. -/
theorem twoPointBernoulliExpectation_mono {p x0 x1 y0 y1 : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (h0 : x0 ≤ y0) (h1 : x1 ≤ y1) :
    twoPointBernoulliExpectation p x0 x1 ≤ twoPointBernoulliExpectation p y0 y1 := by
  unfold twoPointBernoulliExpectation
  have hq0 : 0 ≤ 1 - p := sub_nonneg.mpr hp1
  nlinarith [mul_le_mul_of_nonneg_left h0 hq0, mul_le_mul_of_nonneg_left h1 hp0]

/-- One-coordinate expectation when the closed value is zero. -/
theorem twoPointBernoulliExpectation_zero_left (p c : ℝ) :
    twoPointBernoulliExpectation p 0 c = p * c := by
  unfold twoPointBernoulliExpectation
  ring

/-- Split a finite Bernoulli expectation according to whether a fresh coordinate is closed or
open. This is the conditioning identity used in Grimmett's finite-coordinate FKG induction. -/
theorem finiteBernoulliExpectation_insert {ι : Type*} [DecidableEq ι]
    {E : Finset ι} {a : ι} (ha : a ∉ E) (p : ℝ) (X : Finset ι → ℝ) :
    finiteBernoulliExpectation (insert a E) p X =
      finiteBernoulliExpectation E p
        (fun s ↦ twoPointBernoulliExpectation p (X s) (X (insert a s))) := by
  unfold finiteBernoulliExpectation twoPointBernoulliExpectation
  rw [Finset.powerset_insert]
  have hdisj : Disjoint E.powerset (E.powerset.image (insert a)) := by
    rw [Finset.disjoint_left]
    intro s hs himg
    rcases Finset.mem_image.mp himg with ⟨t, _ht, hts⟩
    rw [← hts] at hs
    have ha_not_insert : a ∉ insert a t := Finset.notMem_of_mem_powerset_of_notMem hs ha
    exact ha_not_insert (Finset.mem_insert_self a t)
  rw [Finset.sum_union hdisj]
  have hinj : Set.InjOn (insert a) (↑E.powerset : Set (Finset ι)) := by
    intro s hs t ht hst
    have hsa : a ∉ s := Finset.notMem_of_mem_powerset_of_notMem hs ha
    have hta : a ∉ t := Finset.notMem_of_mem_powerset_of_notMem ht ha
    calc
      s = (insert a s).erase a := by simp [hsa]
      _ = (insert a t).erase a := by rw [hst]
      _ = t := by simp [hta]
  rw [Finset.sum_image hinj]
  have hcard_insert_E : #(insert a E) = #E + 1 := Finset.card_insert_of_notMem ha
  simp only [hcard_insert_E]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s hs
  have hsE : s ⊆ E := Finset.mem_powerset.mp hs
  have hsa : a ∉ s := Finset.notMem_mono hsE ha
  have hcard_insert_s : #(insert a s) = #s + 1 := Finset.card_insert_of_notMem hsa
  have hcard_le : #s ≤ #E := Finset.card_le_card hsE
  simp [hcard_insert_s]
  have hsucc_sub_closed : #E + 1 - #s = (#E - #s) + 1 := by omega
  rw [hsucc_sub_closed]
  rw [pow_succ, pow_succ]
  ring

/-- Split a finite Bernoulli expectation according to whether a fresh coordinate is closed or
open. -/
theorem finiteBernoulliExpectation_insert_split {ι : Type*} [DecidableEq ι]
    {E : Finset ι} {a : ι} (ha : a ∉ E) (p : ℝ) (X : Finset ι → ℝ) :
    finiteBernoulliExpectation (insert a E) p X =
      (1 - p) * finiteBernoulliExpectation E p X +
        p * finiteBernoulliExpectation E p (fun s ↦ X (insert a s)) := by
  rw [finiteBernoulliExpectation_insert ha]
  unfold twoPointBernoulliExpectation
  rw [show finiteBernoulliExpectation E p
        (fun s ↦ (1 - p) * X s + p * X (insert a s)) =
      finiteBernoulliExpectation E p (fun s ↦ (1 - p) * X s) +
        finiteBernoulliExpectation E p (fun s ↦ p * X (insert a s)) by
    exact finiteBernoulliExpectation_add E p _ _]
  rw [finiteBernoulliExpectation_const_mul, finiteBernoulliExpectation_const_mul]

/-- A constant observable has expectation equal to that constant under the one-coordinate
Bernoulli law. -/
theorem twoPointBernoulliExpectation_const (p c : ℝ) :
    twoPointBernoulliExpectation p c c = c := by
  unfold twoPointBernoulliExpectation
  ring

/-- Finite Bernoulli weights sum to one. -/
theorem finiteBernoulliExpectation_const {ι : Type*} [DecidableEq ι]
    (E : Finset ι) (p c : ℝ) :
    finiteBernoulliExpectation E p (fun _ ↦ c) = c := by
  induction E using Finset.induction with
  | empty =>
      simp [finiteBernoulliExpectation]
  | insert _a E ha ih =>
      rw [finiteBernoulliExpectation_insert ha]
      simpa [twoPointBernoulliExpectation_const] using ih

/-- Finite Bernoulli expectation of a nonnegative observable is nonnegative. -/
theorem finiteBernoulliExpectation_nonneg {ι : Type*} [DecidableEq ι]
    {E : Finset ι} {p : ℝ} {X : Finset ι → ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hX : ∀ ⦃s : Finset ι⦄, s ⊆ E → 0 ≤ X s) :
    0 ≤ finiteBernoulliExpectation E p X := by
  unfold finiteBernoulliExpectation
  refine Finset.sum_nonneg ?_
  intro s hs
  have hsE : s ⊆ E := Finset.mem_powerset.mp hs
  have hq0 : 0 ≤ 1 - p := sub_nonneg.mpr hp1
  have hweight : 0 ≤ p ^ s.card * (1 - p) ^ (E.card - s.card) :=
    mul_nonneg (pow_nonneg hp0 _) (pow_nonneg hq0 _)
  exact mul_nonneg hweight (hX hsE)

/-- The exact covariance identity behind the one-coordinate base case of Grimmett's FKG
induction. -/
theorem twoPointBernoulliExpectation_mul_sub (p x0 x1 y0 y1 : ℝ) :
    twoPointBernoulliExpectation p (x0 * y0) (x1 * y1) -
        twoPointBernoulliExpectation p x0 x1 * twoPointBernoulliExpectation p y0 y1 =
      p * (1 - p) * ((x1 - x0) * (y1 - y0)) := by
  unfold twoPointBernoulliExpectation
  ring

/-- Grimmett's one-coordinate FKG computation: if the two observables are increasing in the
single Bernoulli coordinate, their covariance is nonnegative. This is the `n = 1` base of the
finite-coordinate conditioning induction for Theorem (2.4). -/
theorem twoPointBernoulliExpectation_fkg {p x0 x1 y0 y1 : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hx : x0 ≤ x1) (hy : y0 ≤ y1) :
    twoPointBernoulliExpectation p x0 x1 *
        twoPointBernoulliExpectation p y0 y1 ≤
      twoPointBernoulliExpectation p (x0 * y0) (x1 * y1) := by
  have hp01 : 0 ≤ p * (1 - p) := mul_nonneg hp0 (sub_nonneg.mpr hp1)
  have hxy : 0 ≤ (x1 - x0) * (y1 - y0) :=
    mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hy)
  have hnonneg : 0 ≤ p * (1 - p) * ((x1 - x0) * (y1 - y0)) :=
    mul_nonneg hp01 hxy
  rw [← twoPointBernoulliExpectation_mul_sub p x0 x1 y0 y1] at hnonneg
  linarith

/-- On a singleton support, the finite Bernoulli expectation is exactly the two-point
expectation used in Grimmett's `n = 1` FKG computation. -/
theorem finiteBernoulliExpectation_singleton {ι : Type*} [DecidableEq ι]
    (a : ι) (p : ℝ) (X : Finset ι → ℝ) :
    finiteBernoulliExpectation ({a} : Finset ι) p X =
      twoPointBernoulliExpectation p (X ∅) (X {a}) := by
  have hpowerset : ({a} : Finset ι).powerset = ({∅, {a}} : Finset (Finset ι)) := by
    ext s
    simp [Finset.mem_powerset, Finset.subset_singleton_iff]
  simp [finiteBernoulliExpectation, twoPointBernoulliExpectation, hpowerset]

/-- The finite-cube singleton form of the weighted FKG base case. -/
theorem finiteBernoulliExpectation_singleton_fkg {ι : Type*} [DecidableEq ι]
    (a : ι) {p : ℝ} {X Y : Finset ι → ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hX : X ∅ ≤ X {a}) (hY : Y ∅ ≤ Y {a}) :
    finiteBernoulliExpectation ({a} : Finset ι) p X *
        finiteBernoulliExpectation ({a} : Finset ι) p Y ≤
      finiteBernoulliExpectation ({a} : Finset ι) p (fun s ↦ X s * Y s) := by
  rw [finiteBernoulliExpectation_singleton, finiteBernoulliExpectation_singleton,
    finiteBernoulliExpectation_singleton]
  exact twoPointBernoulliExpectation_fkg hp0 hp1 hX hY

/-- The one-coordinate finite FKG theorem stated with the finite-cube monotonicity predicate. -/
theorem finiteBernoulliExpectation_singleton_fkg_of_increasing {ι : Type*} [DecidableEq ι]
    (a : ι) {p : ℝ} {X Y : Finset ι → ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hX : IsIncreasingFinsetFunction ({a} : Finset ι) X)
    (hY : IsIncreasingFinsetFunction ({a} : Finset ι) Y) :
    finiteBernoulliExpectation ({a} : Finset ι) p X *
        finiteBernoulliExpectation ({a} : Finset ι) p Y ≤
      finiteBernoulliExpectation ({a} : Finset ι) p (fun s ↦ X s * Y s) :=
  finiteBernoulliExpectation_singleton_fkg a hp0 hp1 hX.empty_le_singleton
    hY.empty_le_singleton

/-- Finite-coordinate weighted FKG/Harris inequality. This is Grimmett's induction step before
the martingale limiting argument: condition on one coordinate, apply the one-coordinate FKG
inside each fiber, and use the induction hypothesis for the conditional expectations. -/
theorem finiteBernoulliExpectation_fkg {ι : Type*} [DecidableEq ι]
    {E : Finset ι} {p : ℝ} {X Y : Finset ι → ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hX : IsIncreasingFinsetFunction E X) (hY : IsIncreasingFinsetFunction E Y) :
    finiteBernoulliExpectation E p X * finiteBernoulliExpectation E p Y ≤
      finiteBernoulliExpectation E p (fun s ↦ X s * Y s) := by
  induction E using Finset.induction generalizing X Y with
  | empty =>
      simp [finiteBernoulliExpectation]
  | insert a E ha ih =>
      rw [finiteBernoulliExpectation_insert ha p X,
        finiteBernoulliExpectation_insert ha p Y,
        finiteBernoulliExpectation_insert ha p (fun s ↦ X s * Y s)]
      have hXbar : IsIncreasingFinsetFunction E
          (fun s ↦ twoPointBernoulliExpectation p (X s) (X (insert a s))) := by
        intro s t hst htE
        exact twoPointBernoulliExpectation_mono hp0 hp1
          (hX.mono hst (by intro e he; exact Finset.mem_insert.mpr (Or.inr (htE he))))
          (hX.mono (Finset.insert_subset_insert a hst) (Finset.insert_subset_insert a htE))
      have hYbar : IsIncreasingFinsetFunction E
          (fun s ↦ twoPointBernoulliExpectation p (Y s) (Y (insert a s))) := by
        intro s t hst htE
        exact twoPointBernoulliExpectation_mono hp0 hp1
          (hY.mono hst (by intro e he; exact Finset.mem_insert.mpr (Or.inr (htE he))))
          (hY.mono (Finset.insert_subset_insert a hst) (Finset.insert_subset_insert a htE))
      have hind := ih hXbar hYbar
      have hfiber : finiteBernoulliExpectation E p
            (fun s ↦ twoPointBernoulliExpectation p (X s) (X (insert a s)) *
              twoPointBernoulliExpectation p (Y s) (Y (insert a s))) ≤
          finiteBernoulliExpectation E p
            (fun s ↦ twoPointBernoulliExpectation p (X s * Y s)
              (X (insert a s) * Y (insert a s))) := by
        exact finiteBernoulliExpectation_mono hp0 hp1 (fun _s hsE ↦
          twoPointBernoulliExpectation_fkg hp0 hp1
            (hX.mono (by intro e he; exact Finset.mem_insert.mpr (Or.inr he))
              (Finset.insert_subset_insert a hsE))
            (hY.mono (by intro e he; exact Finset.mem_insert.mpr (Or.inr he))
              (Finset.insert_subset_insert a hsE)))
      exact le_trans hind hfiber

/-- Finite-coordinate weighted FKG for two decreasing observables. -/
theorem finiteBernoulliExpectation_fkg_of_decreasing {ι : Type*} [DecidableEq ι]
    {E : Finset ι} {p : ℝ} {X Y : Finset ι → ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hX : IsDecreasingFinsetFunction E X) (hY : IsDecreasingFinsetFunction E Y) :
    finiteBernoulliExpectation E p X * finiteBernoulliExpectation E p Y ≤
      finiteBernoulliExpectation E p (fun s ↦ X s * Y s) := by
  have h := finiteBernoulliExpectation_fkg hp0 hp1
    hX.neg_isIncreasingFinsetFunction hY.neg_isIncreasingFinsetFunction
  rw [finiteBernoulliExpectation_neg, finiteBernoulliExpectation_neg] at h
  have hprod :
      finiteBernoulliExpectation E p (fun s ↦ -X s * -Y s) =
        finiteBernoulliExpectation E p (fun s ↦ X s * Y s) := by
    apply finiteBernoulliExpectation_congr
    intro s _hsE
    ring
  rw [hprod] at h
  simpa using h

/-- Finite-coordinate weighted negative correlation for an increasing observable and a decreasing
observable. -/
theorem finiteBernoulliExpectation_le_mul_of_increasing_decreasing {ι : Type*}
    [DecidableEq ι] {E : Finset ι} {p : ℝ} {X Y : Finset ι → ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hX : IsIncreasingFinsetFunction E X) (hY : IsDecreasingFinsetFunction E Y) :
    finiteBernoulliExpectation E p (fun s ↦ X s * Y s) ≤
      finiteBernoulliExpectation E p X * finiteBernoulliExpectation E p Y := by
  have h := finiteBernoulliExpectation_fkg hp0 hp1 hX hY.neg_isIncreasingFinsetFunction
  rw [finiteBernoulliExpectation_neg] at h
  have hprod :
      finiteBernoulliExpectation E p (fun s ↦ X s * -Y s) =
        -finiteBernoulliExpectation E p (fun s ↦ X s * Y s) := by
    rw [show (fun s ↦ X s * -Y s) = fun s ↦ -(X s * Y s) by
      funext s
      ring]
    exact finiteBernoulliExpectation_neg E p (fun s ↦ X s * Y s)
  rw [hprod] at h
  nlinarith

/-- Weighted Bernoulli probability of a finite trace on the cube of subsets of `E`. -/
noncomputable def finiteBernoulliEventProbability {ι : Type*} [DecidableEq ι]
    (E : Finset ι) (p : ℝ) (T : Set (Finset ι)) : ℝ :=
  finiteBernoulliExpectation E p (fun s ↦ T.indicator (fun _ ↦ (1 : ℝ)) s)

/-- Finite Bernoulli event probabilities are nonnegative for `0 ≤ p ≤ 1`. -/
theorem finiteBernoulliEventProbability_nonneg {ι : Type*} [DecidableEq ι]
    (E : Finset ι) {p : ℝ} (T : Set (Finset ι)) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ finiteBernoulliEventProbability E p T := by
  unfold finiteBernoulliEventProbability
  exact finiteBernoulliExpectation_nonneg hp0 hp1 (fun s _hs ↦ by
    by_cases h : s ∈ T <;> simp [h])

@[simp]
theorem finiteBernoulliEventProbability_univ {ι : Type*} [DecidableEq ι]
    (E : Finset ι) (p : ℝ) :
    finiteBernoulliEventProbability E p (Set.univ : Set (Finset ι)) = 1 := by
  simp [finiteBernoulliEventProbability, finiteBernoulliExpectation_const]

/-- Finite Bernoulli event probability only depends on the trace inside the supporting cube. -/
theorem finiteBernoulliEventProbability_congr {ι : Type*} [DecidableEq ι]
    {E : Finset ι} {p : ℝ} {T U : Set (Finset ι)}
    (hTU : ∀ ⦃s : Finset ι⦄, s ⊆ E → (s ∈ T ↔ s ∈ U)) :
    finiteBernoulliEventProbability E p T = finiteBernoulliEventProbability E p U := by
  unfold finiteBernoulliEventProbability
  apply finiteBernoulliExpectation_congr
  intro s hsE
  by_cases hT : s ∈ T
  · have hU : s ∈ U := (hTU hsE).1 hT
    simp [hT, hU]
  · have hU : s ∉ U := by
      intro h
      exact hT ((hTU hsE).2 h)
    simp [hT, hU]

/-- The product-measure cylinder where the finite trace on `E` is exactly `s`. -/
noncomputable def finiteTraceCylinder {ι : Type*} [DecidableEq ι]
    (E s : Finset ι) : Set (Set ι) :=
  {ω | restrictTo E ω = s}

@[simp]
theorem mem_finiteTraceCylinder_iff {ι : Type*} [DecidableEq ι]
    (E s : Finset ι) (ω : Set ι) :
    ω ∈ finiteTraceCylinder E s ↔ restrictTo E ω = s :=
  Iff.rfl

theorem finiteTraceCylinder_eq_open_closed_of_subset {ι : Type*} [DecidableEq ι]
    {E s : Finset ι} (hsE : s ⊆ E) :
    finiteTraceCylinder E s =
      {ω : Set ι | (s : Set ι) ⊆ ω ∧ Disjoint ((E \ s : Finset ι) : Set ι) ω} := by
  ext ω
  constructor
  · intro hω
    constructor
    · intro e hes
      have he : e ∈ restrictTo E ω := by
        rw [hω]
        exact hes
      exact (mem_restrictTo_iff E ω e).mp he |>.2
    · rw [Set.disjoint_left]
      intro e heEs heω
      have heE : e ∈ E := (Finset.mem_sdiff.mp heEs).1
      have hes : e ∉ s := (Finset.mem_sdiff.mp heEs).2
      have he : e ∈ restrictTo E ω := (mem_restrictTo_iff E ω e).mpr ⟨heE, heω⟩
      rw [hω] at he
      exact hes he
  · rintro ⟨hsω, hclosed⟩
    ext e
    constructor
    · intro he
      have heEω := (mem_restrictTo_iff E ω e).mp he
      by_contra hes
      exact (Set.disjoint_left.mp hclosed) (Finset.mem_sdiff.mpr ⟨heEω.1, hes⟩) heEω.2
    · intro hes
      exact (mem_restrictTo_iff E ω e).mpr ⟨hsE hes, hsω hes⟩

/-- Exact finite traces are measurable product cylinders. -/
theorem measurableSet_finiteTraceCylinder {ι : Type*} [DecidableEq ι]
    (E s : Finset ι) :
    MeasurableSet (finiteTraceCylinder E s) := by
  classical
  by_cases hsE : s ⊆ E
  · rw [finiteTraceCylinder_eq_open_closed_of_subset hsE]
    exact (measurableSet_superset_finset s).inter (measurableSet_disjoint_finset (E \ s))
  · have hempty : finiteTraceCylinder E s = ∅ := by
      ext ω
      constructor
      · intro hω
        have hs : s ⊆ E := by
          intro e he
          rw [← hω] at he
          exact restrictTo_subset E ω he
        exact (hsE hs).elim
      · intro hω
        exact hω.elim
    rw [hempty]
    exact MeasurableSet.empty

/-- Product-measure probability of an exact finite trace. -/
theorem setBernoulli_real_finiteTraceCylinder {ι : Type*} [DecidableEq ι]
    (E s : Finset ι) (p : I) (hsE : s ⊆ E) :
    setBer((Set.univ : Set ι), p).real (finiteTraceCylinder E s) =
      (p : ℝ) ^ s.card * (1 - (p : ℝ)) ^ (E.card - s.card) := by
  rw [finiteTraceCylinder_eq_open_closed_of_subset hsE]
  have hdisj : Disjoint (s : Set ι) ((E \ s : Finset ι) : Set ι) := by
    rw [Set.disjoint_left]
    intro e hes heEs
    exact (Finset.mem_sdiff.mp heEs).2 hes
  rw [setBernoulli_real_open_closed_on_finset_univ s (E \ s) p hdisj]
  rw [Finset.card_sdiff_of_subset hsE]

theorem eventOfTrace_eq_iUnion_finiteTraceCylinder {ι : Type*} [DecidableEq ι]
    (E : Finset ι) (T : Set (Finset ι)) [DecidablePred fun s : Finset ι ↦ s ∈ T] :
    eventOfTrace E T =
      ⋃ s ∈ E.powerset.filter (fun s ↦ s ∈ T), finiteTraceCylinder E s := by
  classical
  ext ω
  constructor
  · intro hω
    refine Set.mem_iUnion.mpr ⟨restrictTo E ω, ?_⟩
    refine Set.mem_iUnion.mpr ⟨?_, ?_⟩
    · exact Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr (restrictTo_subset E ω), hω⟩
    · rfl
  · intro hω
    rcases Set.mem_iUnion.mp hω with ⟨s, hsω⟩
    rcases Set.mem_iUnion.mp hsω with ⟨hsT, hωs⟩
    have hT : s ∈ T := (Finset.mem_filter.mp hsT).2
    change restrictTo E ω ∈ T
    rw [hωs]
    exact hT

theorem pairwiseDisjoint_finiteTraceCylinder {ι : Type*} [DecidableEq ι]
    (E : Finset ι) (T : Set (Finset ι)) [DecidablePred fun s : Finset ι ↦ s ∈ T] :
    Set.PairwiseDisjoint (↑(E.powerset.filter (fun s ↦ s ∈ T)))
      (finiteTraceCylinder E) := by
  intro s _hs t _ht hst
  change Disjoint (finiteTraceCylinder E s) (finiteTraceCylinder E t)
  rw [Set.disjoint_left]
  intro ω hωs hωt
  exact hst (hωs.symm.trans hωt)

/-- The finite trace probability agrees with the actual Bernoulli product-measure probability
of the event reconstructed from that trace. -/
theorem setBernoulli_real_eventOfTrace {ι : Type*} [DecidableEq ι]
    (E : Finset ι) (T : Set (Finset ι)) (p : I) :
    setBer((Set.univ : Set ι), p).real (eventOfTrace E T) =
      finiteBernoulliEventProbability E (p : ℝ) T := by
  classical
  rw [eventOfTrace_eq_iUnion_finiteTraceCylinder]
  rw [measureReal_biUnion_finset
    (μ := setBer((Set.univ : Set ι), p))
    (s := E.powerset.filter (fun s ↦ s ∈ T))
    (f := finiteTraceCylinder E)
    (pairwiseDisjoint_finiteTraceCylinder E T)
    (fun s _hs ↦ measurableSet_finiteTraceCylinder E s)]
  unfold finiteBernoulliEventProbability finiteBernoulliExpectation
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro s hs
  have hsE : s ⊆ E := Finset.mem_powerset.mp hs
  rw [setBernoulli_real_finiteTraceCylinder E s p hsE]
  by_cases hT : s ∈ T <;> simp [hT]

/-- A finite-support event has the same Bernoulli product probability as its finite trace. -/
theorem DependsOn.setBernoulli_real_eq_finiteBernoulliEventProbability {ι : Type*}
    [DecidableEq ι] {E : Finset ι} {A : Set (Set ι)} (hA : DependsOn E A) (p : I) :
    setBer((Set.univ : Set ι), p).real A =
      finiteBernoulliEventProbability E (p : ℝ) (eventTrace E A) := by
  have hAeq : A = eventOfTrace E (eventTrace E A) := by
    ext ω
    exact (restrictTo_mem_eventTrace_iff_of_dependsOn hA ω).symm
  calc
    setBer((Set.univ : Set ι), p).real A =
        setBer((Set.univ : Set ι), p).real (eventOfTrace E (eventTrace E A)) := by
      exact congrArg (fun B : Set (Set ι) ↦ setBer((Set.univ : Set ι), p).real B) hAeq
    _ = finiteBernoulliEventProbability E (p : ℝ) (eventTrace E A) :=
      setBernoulli_real_eventOfTrace E (eventTrace E A) p

/-- Split a finite Bernoulli event probability according to whether a fresh coordinate is closed
or open. This is the finite conditioning identity used in the Russo induction. -/
theorem finiteBernoulliEventProbability_insert_split {ι : Type*} [DecidableEq ι]
    {E : Finset ι} {a : ι} (ha : a ∉ E) (p : ℝ) (T : Set (Finset ι)) :
    finiteBernoulliEventProbability (insert a E) p T =
      (1 - p) * finiteBernoulliEventProbability E p T +
        p * finiteBernoulliEventProbability E p {s : Finset ι | insert a s ∈ T} := by
  unfold finiteBernoulliEventProbability
  rw [finiteBernoulliExpectation_insert ha]
  unfold twoPointBernoulliExpectation
  rw [show finiteBernoulliExpectation E p
        (fun s ↦ (1 - p) * T.indicator (fun _ ↦ (1 : ℝ)) s +
          p * T.indicator (fun _ ↦ (1 : ℝ)) (insert a s)) =
      finiteBernoulliExpectation E p
        (fun s ↦ (1 - p) * T.indicator (fun _ ↦ (1 : ℝ)) s) +
        finiteBernoulliExpectation E p
          (fun s ↦ p *
            ({s : Finset ι | insert a s ∈ T}).indicator (fun _ ↦ (1 : ℝ)) s) by
    unfold finiteBernoulliExpectation
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro s _hs
    by_cases hs : insert a s ∈ T <;> simp [hs]
    ring]
  rw [finiteBernoulliExpectation_const_mul, finiteBernoulliExpectation_const_mul]

/-- Heterogeneous finite Bernoulli expectation on the finite cube of subsets of `E`, with
coordinate-dependent open probabilities `q`. This is the product measure used in Grimmett's
Russo proof before specializing all coordinates to the same parameter. -/
noncomputable def finiteBernoulliHeteroExpectation {ι : Type*} [DecidableEq ι]
    (E : Finset ι) (q : ι → ℝ) (X : Finset ι → ℝ) : ℝ :=
  E.powerset.sum fun s ↦ E.prod (fun e ↦ if e ∈ s then q e else 1 - q e) * X s

/-- Heterogeneous finite Bernoulli probability of a finite trace. -/
noncomputable def finiteBernoulliHeteroEventProbability {ι : Type*} [DecidableEq ι]
    (E : Finset ι) (q : ι → ℝ) (T : Set (Finset ι)) : ℝ :=
  finiteBernoulliHeteroExpectation E q (fun s ↦ T.indicator (fun _ ↦ (1 : ℝ)) s)

/-- Heterogeneous finite Bernoulli expectation only depends on coordinate probabilities on `E`
and observable values on the supporting cube. -/
theorem finiteBernoulliHeteroExpectation_congr {ι : Type*} [DecidableEq ι]
    {E : Finset ι} {q r : ι → ℝ} {X Y : Finset ι → ℝ}
    (hqr : ∀ e ∈ E, q e = r e)
    (hXY : ∀ ⦃s : Finset ι⦄, s ⊆ E → X s = Y s) :
    finiteBernoulliHeteroExpectation E q X = finiteBernoulliHeteroExpectation E r Y := by
  unfold finiteBernoulliHeteroExpectation
  apply Finset.sum_congr rfl
  intro s hs
  have hsE : s ⊆ E := Finset.mem_powerset.mp hs
  have hprod :
      E.prod (fun e ↦ if e ∈ s then q e else 1 - q e) =
        E.prod (fun e ↦ if e ∈ s then r e else 1 - r e) := by
    apply Finset.prod_congr rfl
    intro e he
    rw [hqr e he]
  rw [hprod, hXY hsE]

/-- Split a heterogeneous finite Bernoulli expectation according to a fresh coordinate. -/
theorem finiteBernoulliHeteroExpectation_insert {ι : Type*} [DecidableEq ι]
    {E : Finset ι} {a : ι} (ha : a ∉ E) (q : ι → ℝ) (X : Finset ι → ℝ) :
    finiteBernoulliHeteroExpectation (insert a E) q X =
      finiteBernoulliHeteroExpectation E q
        (fun s ↦ (1 - q a) * X s + q a * X (insert a s)) := by
  unfold finiteBernoulliHeteroExpectation
  rw [Finset.powerset_insert]
  have hdisj : Disjoint E.powerset (E.powerset.image (insert a)) := by
    rw [Finset.disjoint_left]
    intro s hs himg
    rcases Finset.mem_image.mp himg with ⟨t, _ht, hts⟩
    rw [← hts] at hs
    have ha_not_insert : a ∉ insert a t := Finset.notMem_of_mem_powerset_of_notMem hs ha
    exact ha_not_insert (Finset.mem_insert_self a t)
  rw [Finset.sum_union hdisj]
  have hinj : Set.InjOn (insert a) (↑E.powerset : Set (Finset ι)) := by
    intro s hs t ht hst
    have hsa : a ∉ s := Finset.notMem_of_mem_powerset_of_notMem hs ha
    have hta : a ∉ t := Finset.notMem_of_mem_powerset_of_notMem ht ha
    calc
      s = (insert a s).erase a := by simp [hsa]
      _ = (insert a t).erase a := by rw [hst]
      _ = t := by simp [hta]
  rw [Finset.sum_image hinj]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s hs
  have hsE : s ⊆ E := Finset.mem_powerset.mp hs
  have hsa : a ∉ s := Finset.notMem_mono hsE ha
  have hprod_closed :
      (insert a E).prod (fun e ↦ if e ∈ s then q e else 1 - q e) =
        (1 - q a) * E.prod (fun e ↦ if e ∈ s then q e else 1 - q e) := by
    rw [Finset.prod_insert ha]
    simp [hsa]
  have hprod_open :
      (insert a E).prod (fun e ↦ if e ∈ insert a s then q e else 1 - q e) =
        q a * E.prod (fun e ↦ if e ∈ s then q e else 1 - q e) := by
    rw [Finset.prod_insert ha]
    congr 1
    · simp
    · apply Finset.prod_congr rfl
      intro e heE
      have hne : e ≠ a := by
        intro h
        exact ha (by simpa [h] using heE)
      simp [Finset.mem_insert, hne]
  rw [hprod_closed, hprod_open]
  ring

/-- The heterogeneous finite Bernoulli expectation specializes to the homogeneous one when all
coordinate probabilities are the same. -/
theorem finiteBernoulliHeteroExpectation_const {ι : Type*} [DecidableEq ι]
    (E : Finset ι) (p : ℝ) (X : Finset ι → ℝ) :
    finiteBernoulliHeteroExpectation E (fun _ ↦ p) X = finiteBernoulliExpectation E p X := by
  induction E using Finset.induction generalizing X with
  | empty =>
      simp [finiteBernoulliHeteroExpectation, finiteBernoulliExpectation]
  | insert a E ha ih =>
      rw [finiteBernoulliHeteroExpectation_insert ha, finiteBernoulliExpectation_insert ha]
      rw [ih]
      apply finiteBernoulliExpectation_congr
      intro s _hsE
      unfold twoPointBernoulliExpectation
      ring

/-- The heterogeneous finite Bernoulli event probability specializes to the homogeneous one when
all coordinate probabilities are the same. -/
theorem finiteBernoulliHeteroEventProbability_const {ι : Type*} [DecidableEq ι]
    (E : Finset ι) (p : ℝ) (T : Set (Finset ι)) :
    finiteBernoulliHeteroEventProbability E (fun _ ↦ p) T =
      finiteBernoulliEventProbability E p T := by
  unfold finiteBernoulliHeteroEventProbability finiteBernoulliEventProbability
  rw [finiteBernoulliHeteroExpectation_const]

/-- If a finite trace is invariant under opening a fresh coordinate, then its heterogeneous
probability on the enlarged support agrees with its probability on the old support. -/
theorem finiteBernoulliHeteroEventProbability_insert_invariant {ι : Type*} [DecidableEq ι]
    {E : Finset ι} {e : ι} (he : e ∉ E) (q : ι → ℝ) (P : Set (Finset ι))
    (hP : ∀ ⦃s : Finset ι⦄, s ⊆ E → (insert e s ∈ P ↔ s ∈ P)) :
    finiteBernoulliHeteroEventProbability (insert e E) q P =
      finiteBernoulliHeteroEventProbability E q P := by
  unfold finiteBernoulliHeteroEventProbability
  rw [finiteBernoulliHeteroExpectation_insert he]
  apply finiteBernoulliHeteroExpectation_congr
  · intro f _hf
    rfl
  · intro s hsE
    by_cases hs : s ∈ P
    · have hsins : insert e s ∈ P := (hP hsE).2 hs
      simp [Set.indicator_of_mem hs, Set.indicator_of_mem hsins]
    · have hsins : insert e s ∉ P := by
        intro h
        exact hs ((hP hsE).1 h)
      simp [Set.indicator_of_notMem hs, Set.indicator_of_notMem hsins]

/-- Finite intersection of a family of finite traces. This is the finite-family event appearing
in Grimmett's iterated FKG inequality (2.7). -/
def finiteTraceInter {ι κ : Type*} (J : Finset κ) (T : κ → Set (Finset ι)) :
    Set (Finset ι) :=
  {s | ∀ i, i ∈ J → s ∈ T i}

@[simp]
theorem mem_finiteTraceInter_iff {ι κ : Type*} (J : Finset κ)
    (T : κ → Set (Finset ι)) (s : Finset ι) :
    s ∈ finiteTraceInter J T ↔ ∀ i, i ∈ J → s ∈ T i :=
  Iff.rfl

@[simp]
theorem finiteTraceInter_empty {ι κ : Type*} (T : κ → Set (Finset ι)) :
    finiteTraceInter (∅ : Finset κ) T = Set.univ := by
  ext s
  simp [finiteTraceInter]

theorem finiteTraceInter_insert {ι κ : Type*} [DecidableEq κ]
    (a : κ) (J : Finset κ) (T : κ → Set (Finset ι)) :
    finiteTraceInter (insert a J) T = T a ∩ finiteTraceInter J T := by
  ext s
  simp [finiteTraceInter]

/-- Finite intersection of a family of configuration events. This is the event-level version of
`finiteTraceInter`. -/
def finiteEventInter {ι κ : Type*} (J : Finset κ) (A : κ → Set (Set ι)) :
    Set (Set ι) :=
  {ω | ∀ i, i ∈ J → ω ∈ A i}

@[simp]
theorem mem_finiteEventInter_iff {ι κ : Type*} (J : Finset κ)
    (A : κ → Set (Set ι)) (ω : Set ι) :
    ω ∈ finiteEventInter J A ↔ ∀ i, i ∈ J → ω ∈ A i :=
  Iff.rfl

@[simp]
theorem finiteEventInter_empty {ι κ : Type*} (A : κ → Set (Set ι)) :
    finiteEventInter (∅ : Finset κ) A = Set.univ := by
  ext ω
  simp [finiteEventInter]

theorem finiteEventInter_insert {ι κ : Type*} [DecidableEq κ]
    (a : κ) (J : Finset κ) (A : κ → Set (Set ι)) :
    finiteEventInter (insert a J) A = A a ∩ finiteEventInter J A := by
  ext ω
  simp [finiteEventInter]

/-- A finite intersection of increasing configuration events is increasing. -/
theorem isIncreasingEvent_finiteEventInter {ι κ : Type*} {J : Finset κ}
    {A : κ → Set (Set ι)} (hA : ∀ i ∈ J, IsIncreasingEvent (A i)) :
    IsIncreasingEvent (finiteEventInter J A) := by
  intro ω η hωη hω i hi
  exact hA i hi hωη (hω i hi)

/-- A finite intersection of finite-support events still depends on the common finite support. -/
theorem dependsOn_finiteEventInter {ι κ : Type*} {E : Finset ι} {J : Finset κ}
    {A : κ → Set (Set ι)} (hA : ∀ i ∈ J, DependsOn E (A i)) :
    DependsOn E (finiteEventInter J A) := by
  intro ω η hcoord
  constructor
  · intro hω i hi
    exact (hA i hi hcoord).mp (hω i hi)
  · intro hη i hi
    exact (hA i hi hcoord).mpr (hη i hi)

/-- A finite intersection of increasing traces is increasing. -/
theorem isIncreasingTrace_finiteTraceInter {ι κ : Type*} {E : Finset ι}
    {J : Finset κ} {T : κ → Set (Finset ι)}
    (hT : ∀ i ∈ J, IsIncreasingTrace E (T i)) :
    IsIncreasingTrace E (finiteTraceInter J T) := by
  intro s t hst htE hs i hi
  exact hT i hi hst htE (hs i hi)

theorem mem_eventTrace_finiteEventInter_iff {ι κ : Type*} [DecidableEq ι]
    {E : Finset ι} {J : Finset κ} {A : κ → Set (Set ι)} {s : Finset ι}
    (hsE : s ⊆ E) :
    s ∈ eventTrace E (finiteEventInter J A) ↔
      s ∈ finiteTraceInter J (fun i ↦ eventTrace E (A i)) := by
  simp [mem_eventTrace_iff, finiteEventInter, finiteTraceInter, hsE]

/-- The indicator of an increasing finite trace is an increasing finite-cube observable. -/
theorem IsIncreasingTrace.indicator_isIncreasingFinsetFunction {ι : Type*}
    {E : Finset ι} {T : Set (Finset ι)} (hT : IsIncreasingTrace E T) :
    IsIncreasingFinsetFunction E (fun s ↦ T.indicator (fun _ ↦ (1 : ℝ)) s) := by
  intro s t hst htE
  change T.indicator (fun _ ↦ (1 : ℝ)) s ≤ T.indicator (fun _ ↦ (1 : ℝ)) t
  by_cases hs : s ∈ T
  · have ht : t ∈ T := hT hst htE hs
    rw [Set.indicator_of_mem hs, Set.indicator_of_mem ht]
  · rw [Set.indicator_of_notMem hs]
    by_cases ht : t ∈ T
    · rw [Set.indicator_of_mem ht]
      norm_num
    · rw [Set.indicator_of_notMem ht]

/-- The indicator of a decreasing finite trace is a decreasing finite-cube observable. -/
theorem IsDecreasingTrace.indicator_isDecreasingFinsetFunction {ι : Type*}
    {E : Finset ι} {T : Set (Finset ι)} (hT : IsDecreasingTrace E T) :
    IsDecreasingFinsetFunction E (fun s ↦ T.indicator (fun _ ↦ (1 : ℝ)) s) := by
  intro s t hst htE
  change T.indicator (fun _ ↦ (1 : ℝ)) t ≤ T.indicator (fun _ ↦ (1 : ℝ)) s
  by_cases ht : t ∈ T
  · have hs : s ∈ T := hT hst htE ht
    rw [Set.indicator_of_mem ht, Set.indicator_of_mem hs]
  · rw [Set.indicator_of_notMem ht]
    by_cases hs : s ∈ T
    · rw [Set.indicator_of_mem hs]
      norm_num
    · rw [Set.indicator_of_notMem hs]

theorem indicator_mul_indicator_inter {ι : Type*} (T U : Set (Finset ι)) (s : Finset ι) :
    T.indicator (fun _ ↦ (1 : ℝ)) s * U.indicator (fun _ ↦ (1 : ℝ)) s =
      (T ∩ U).indicator (fun _ ↦ (1 : ℝ)) s := by
  by_cases hT : s ∈ T <;> by_cases hU : s ∈ U <;> simp [hT, hU]

/-- Finite-trace weighted FKG/Harris inequality for increasing events. This is the event
specialization of Grimmett's finite-coordinate FKG induction. -/
theorem finiteBernoulliEventProbability_fkg {ι : Type*} [DecidableEq ι]
    {E : Finset ι} {p : ℝ} {T U : Set (Finset ι)}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hT : IsIncreasingTrace E T) (hU : IsIncreasingTrace E U) :
    finiteBernoulliEventProbability E p T * finiteBernoulliEventProbability E p U ≤
      finiteBernoulliEventProbability E p (T ∩ U) := by
  have hfgk := finiteBernoulliExpectation_fkg hp0 hp1
    hT.indicator_isIncreasingFinsetFunction hU.indicator_isIncreasingFinsetFunction
  unfold finiteBernoulliEventProbability at hfgk ⊢
  simpa [indicator_mul_indicator_inter] using hfgk

/-- Finite-trace weighted FKG/Harris inequality for decreasing events. -/
theorem finiteBernoulliEventProbability_fkg_of_decreasing {ι : Type*} [DecidableEq ι]
    {E : Finset ι} {p : ℝ} {T U : Set (Finset ι)}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hT : IsDecreasingTrace E T) (hU : IsDecreasingTrace E U) :
    finiteBernoulliEventProbability E p T * finiteBernoulliEventProbability E p U ≤
      finiteBernoulliEventProbability E p (T ∩ U) := by
  have hfkg := finiteBernoulliExpectation_fkg_of_decreasing hp0 hp1
    hT.indicator_isDecreasingFinsetFunction hU.indicator_isDecreasingFinsetFunction
  unfold finiteBernoulliEventProbability at hfkg ⊢
  simpa [indicator_mul_indicator_inter] using hfkg

/-- Finite-trace negative correlation for an increasing event and a decreasing event. -/
theorem finiteBernoulliEventProbability_le_mul_of_increasing_decreasing
    {ι : Type*} [DecidableEq ι] {E : Finset ι} {p : ℝ} {T U : Set (Finset ι)}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hT : IsIncreasingTrace E T) (hU : IsDecreasingTrace E U) :
    finiteBernoulliEventProbability E p (T ∩ U) ≤
      finiteBernoulliEventProbability E p T * finiteBernoulliEventProbability E p U := by
  have hcorr := finiteBernoulliExpectation_le_mul_of_increasing_decreasing hp0 hp1
    hT.indicator_isIncreasingFinsetFunction hU.indicator_isDecreasingFinsetFunction
  unfold finiteBernoulliEventProbability at hcorr ⊢
  simpa [indicator_mul_indicator_inter] using hcorr

/-- Grimmett's iterated FKG inequality (2.7), finite-trace form. For any finite family of
increasing traces, the probability of their simultaneous occurrence dominates the product of the
individual probabilities. -/
theorem finiteBernoulliEventProbability_iterated_fkg {ι κ : Type*}
    [DecidableEq ι] [DecidableEq κ]
    {E : Finset ι} {p : ℝ} {J : Finset κ} {T : κ → Set (Finset ι)}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hT : ∀ i ∈ J, IsIncreasingTrace E (T i)) :
    J.prod (fun i ↦ finiteBernoulliEventProbability E p (T i)) ≤
      finiteBernoulliEventProbability E p (finiteTraceInter J T) := by
  induction J using Finset.induction with
  | empty =>
      simp
  | insert a J ha ih =>
      have hJ : ∀ i ∈ J, IsIncreasingTrace E (T i) := by
        intro i hi
        exact hT i (Finset.mem_insert.mpr (Or.inr hi))
      have hInter : IsIncreasingTrace E (finiteTraceInter J T) :=
        isIncreasingTrace_finiteTraceInter hJ
      have hstep := finiteBernoulliEventProbability_fkg hp0 hp1
        (hT a (Finset.mem_insert_self a J)) hInter
      have hprod_le : finiteBernoulliEventProbability E p (T a) *
            J.prod (fun i ↦ finiteBernoulliEventProbability E p (T i)) ≤
          finiteBernoulliEventProbability E p (T a) *
            finiteBernoulliEventProbability E p (finiteTraceInter J T) :=
        mul_le_mul_of_nonneg_left (ih hJ)
          (finiteBernoulliEventProbability_nonneg E (T a) hp0 hp1)
      calc
        (insert a J).prod (fun i ↦ finiteBernoulliEventProbability E p (T i)) =
            finiteBernoulliEventProbability E p (T a) *
              J.prod (fun i ↦ finiteBernoulliEventProbability E p (T i)) := by
          rw [Finset.prod_insert ha]
        _ ≤ finiteBernoulliEventProbability E p (T a) *
            finiteBernoulliEventProbability E p (finiteTraceInter J T) := hprod_le
        _ ≤ finiteBernoulliEventProbability E p (T a ∩ finiteTraceInter J T) := hstep
        _ = finiteBernoulliEventProbability E p (finiteTraceInter (insert a J) T) := by
          rw [finiteTraceInter_insert]

/-- Finite-coordinate weighted FKG for traces of increasing configuration events. -/
theorem finiteBernoulliEventTrace_fkg {ι : Type*} [DecidableEq ι]
    {E : Finset ι} {p : ℝ} {A B : Set (Set ι)}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hA : IsIncreasingEvent A) (hB : IsIncreasingEvent B) :
    finiteBernoulliEventProbability E p (eventTrace E A) *
        finiteBernoulliEventProbability E p (eventTrace E B) ≤
      finiteBernoulliEventProbability E p (eventTrace E (A ∩ B)) := by
  have h := finiteBernoulliEventProbability_fkg (E := E)
    (T := (eventTrace E A : Set (Finset ι))) (U := (eventTrace E B : Set (Finset ι)))
    hp0 hp1 (hA.eventTrace (E := E)) (hB.eventTrace (E := E))
  simpa [eventTrace_inter] using h

/-- Finite-coordinate weighted FKG for traces of decreasing configuration events. -/
theorem finiteBernoulliEventTrace_fkg_of_decreasing {ι : Type*} [DecidableEq ι]
    {E : Finset ι} {p : ℝ} {A B : Set (Set ι)}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hA : IsDecreasingEvent A) (hB : IsDecreasingEvent B) :
    finiteBernoulliEventProbability E p (eventTrace E A) *
        finiteBernoulliEventProbability E p (eventTrace E B) ≤
      finiteBernoulliEventProbability E p (eventTrace E (A ∩ B)) := by
  have h := finiteBernoulliEventProbability_fkg_of_decreasing (E := E)
    (T := (eventTrace E A : Set (Finset ι))) (U := (eventTrace E B : Set (Finset ι)))
    hp0 hp1 (hA.eventTrace (E := E)) (hB.eventTrace (E := E))
  simpa [eventTrace_inter] using h

/-- Finite-coordinate negative correlation for an increasing and a decreasing configuration
event. -/
theorem finiteBernoulliEventTrace_le_mul_of_increasing_decreasing {ι : Type*}
    [DecidableEq ι] {E : Finset ι} {p : ℝ} {A B : Set (Set ι)}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hA : IsIncreasingEvent A) (hB : IsDecreasingEvent B) :
    finiteBernoulliEventProbability E p (eventTrace E (A ∩ B)) ≤
      finiteBernoulliEventProbability E p (eventTrace E A) *
        finiteBernoulliEventProbability E p (eventTrace E B) := by
  have h := finiteBernoulliEventProbability_le_mul_of_increasing_decreasing (E := E)
    (T := (eventTrace E A : Set (Finset ι))) (U := (eventTrace E B : Set (Finset ι)))
    hp0 hp1 (hA.eventTrace (E := E)) (hB.eventTrace (E := E))
  simpa [eventTrace_inter] using h

/-- Grimmett's iterated FKG inequality (2.7) for finite traces of increasing configuration
events. -/
theorem finiteBernoulliEventTrace_iterated_fkg {ι κ : Type*}
    [DecidableEq ι] [DecidableEq κ]
    {E : Finset ι} {p : ℝ} {J : Finset κ} {A : κ → Set (Set ι)}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hA : ∀ i ∈ J, IsIncreasingEvent (A i)) :
    J.prod (fun i ↦ finiteBernoulliEventProbability E p (eventTrace E (A i))) ≤
      finiteBernoulliEventProbability E p (finiteTraceInter J fun i ↦ eventTrace E (A i)) :=
  finiteBernoulliEventProbability_iterated_fkg hp0 hp1 fun i hi ↦ (hA i hi).eventTrace

/-- Grimmett's iterated FKG inequality (2.7), finite-trace form with an event-level
intersection on the right. -/
theorem finiteBernoulliEventTrace_iterated_fkg_eventInter {ι κ : Type*}
    [DecidableEq ι] [DecidableEq κ]
    {E : Finset ι} {p : ℝ} {J : Finset κ} {A : κ → Set (Set ι)}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hA : ∀ i ∈ J, IsIncreasingEvent (A i)) :
    J.prod (fun i ↦ finiteBernoulliEventProbability E p (eventTrace E (A i))) ≤
      finiteBernoulliEventProbability E p (eventTrace E (finiteEventInter J A)) := by
  have h := finiteBernoulliEventTrace_iterated_fkg (E := E) (p := p) (J := J) hp0 hp1 hA
  have hprob :
      finiteBernoulliEventProbability E p (finiteTraceInter J fun i ↦ eventTrace E (A i)) =
        finiteBernoulliEventProbability E p (eventTrace E (finiteEventInter J A)) := by
    apply finiteBernoulliEventProbability_congr
    intro s hsE
    exact (mem_eventTrace_finiteEventInter_iff (E := E) (J := J) (A := A) hsE).symm
  exact h.trans_eq hprob

/-- Finite-support FKG for increasing events stated directly in the Bernoulli product measure. -/
theorem setBernoulli_real_fkg_of_dependsOn {ι : Type*} [DecidableEq ι]
    {E F : Finset ι} {A B : Set (Set ι)} (p : I)
    (hAinc : IsIncreasingEvent A) (hBinc : IsIncreasingEvent B)
    (hAdep : DependsOn E A) (hBdep : DependsOn F B) :
    setBer((Set.univ : Set ι), p).real A *
        setBer((Set.univ : Set ι), p).real B ≤
      setBer((Set.univ : Set ι), p).real (A ∩ B) := by
  let G : Finset ι := E ∪ F
  have hAdepG : DependsOn G A := hAdep.mono (by intro e he; exact Finset.mem_union_left F he)
  have hBdepG : DependsOn G B := hBdep.mono (by intro e he; exact Finset.mem_union_right E he)
  have hABdepG : DependsOn G (A ∩ B) := hAdepG.inter hBdepG
  rw [hAdepG.setBernoulli_real_eq_finiteBernoulliEventProbability p,
    hBdepG.setBernoulli_real_eq_finiteBernoulliEventProbability p,
    hABdepG.setBernoulli_real_eq_finiteBernoulliEventProbability p]
  exact finiteBernoulliEventTrace_fkg (E := G) (p := (p : ℝ)) p.2.1 p.2.2 hAinc hBinc

/-- Finite-support FKG for decreasing events stated directly in the Bernoulli product measure. -/
theorem setBernoulli_real_fkg_of_decreasing_dependsOn {ι : Type*} [DecidableEq ι]
    {E F : Finset ι} {A B : Set (Set ι)} (p : I)
    (hAdec : IsDecreasingEvent A) (hBdec : IsDecreasingEvent B)
    (hAdep : DependsOn E A) (hBdep : DependsOn F B) :
    setBer((Set.univ : Set ι), p).real A *
        setBer((Set.univ : Set ι), p).real B ≤
      setBer((Set.univ : Set ι), p).real (A ∩ B) := by
  let G : Finset ι := E ∪ F
  have hAdepG : DependsOn G A := hAdep.mono (by intro e he; exact Finset.mem_union_left F he)
  have hBdepG : DependsOn G B := hBdep.mono (by intro e he; exact Finset.mem_union_right E he)
  have hABdepG : DependsOn G (A ∩ B) := hAdepG.inter hBdepG
  rw [hAdepG.setBernoulli_real_eq_finiteBernoulliEventProbability p,
    hBdepG.setBernoulli_real_eq_finiteBernoulliEventProbability p,
    hABdepG.setBernoulli_real_eq_finiteBernoulliEventProbability p]
  exact finiteBernoulliEventTrace_fkg_of_decreasing (E := G) (p := (p : ℝ))
    p.2.1 p.2.2 hAdec hBdec

/-- Finite-support negative correlation for an increasing event and a decreasing event under the
Bernoulli product measure. -/
theorem setBernoulli_real_le_mul_of_increasing_decreasing_dependsOn {ι : Type*}
    [DecidableEq ι] {E F : Finset ι} {A B : Set (Set ι)} (p : I)
    (hAinc : IsIncreasingEvent A) (hBdec : IsDecreasingEvent B)
    (hAdep : DependsOn E A) (hBdep : DependsOn F B) :
    setBer((Set.univ : Set ι), p).real (A ∩ B) ≤
      setBer((Set.univ : Set ι), p).real A *
        setBer((Set.univ : Set ι), p).real B := by
  let G : Finset ι := E ∪ F
  have hAdepG : DependsOn G A := hAdep.mono (by intro e he; exact Finset.mem_union_left F he)
  have hBdepG : DependsOn G B := hBdep.mono (by intro e he; exact Finset.mem_union_right E he)
  have hABdepG : DependsOn G (A ∩ B) := hAdepG.inter hBdepG
  rw [hAdepG.setBernoulli_real_eq_finiteBernoulliEventProbability p,
    hBdepG.setBernoulli_real_eq_finiteBernoulliEventProbability p,
    hABdepG.setBernoulli_real_eq_finiteBernoulliEventProbability p]
  exact finiteBernoulliEventTrace_le_mul_of_increasing_decreasing (E := G) (p := (p : ℝ))
    p.2.1 p.2.2 hAinc hBdec

/-- Finite-support iterated FKG for increasing events stated directly in the Bernoulli product
measure. -/
theorem setBernoulli_real_iterated_fkg_of_dependsOn {ι κ : Type*}
    [DecidableEq ι] [DecidableEq κ] {E : κ → Finset ι} {J : Finset κ}
    {A : κ → Set (Set ι)} (p : I)
    (hAinc : ∀ i ∈ J, IsIncreasingEvent (A i))
    (hAdep : ∀ i ∈ J, DependsOn (E i) (A i)) :
    J.prod (fun i ↦ setBer((Set.univ : Set ι), p).real (A i)) ≤
      setBer((Set.univ : Set ι), p).real (finiteEventInter J A) := by
  let G : Finset ι := J.biUnion E
  have hAdepG : ∀ i ∈ J, DependsOn G (A i) := by
    intro i hi
    exact (hAdep i hi).mono (Finset.subset_biUnion_of_mem E hi)
  have hInterDep : DependsOn G (finiteEventInter J A) :=
    dependsOn_finiteEventInter hAdepG
  calc
    J.prod (fun i ↦ setBer((Set.univ : Set ι), p).real (A i)) =
        J.prod (fun i ↦ finiteBernoulliEventProbability G (p : ℝ) (eventTrace G (A i))) := by
      apply Finset.prod_congr rfl
      intro i hi
      exact hAdepG i hi |>.setBernoulli_real_eq_finiteBernoulliEventProbability p
    _ ≤ finiteBernoulliEventProbability G (p : ℝ) (eventTrace G (finiteEventInter J A)) :=
      finiteBernoulliEventTrace_iterated_fkg_eventInter (E := G) (p := (p : ℝ)) (J := J)
        p.2.1 p.2.2 hAinc
    _ = setBer((Set.univ : Set ι), p).real (finiteEventInter J A) := by
      rw [hInterDep.setBernoulli_real_eq_finiteBernoulliEventProbability p]

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

/-- Finite-support FKG for increasing cubic bond events. -/
theorem bernoulliBondMeasure_real_fkg_of_dependsOn (d : ℕ)
    {E F : Finset (CubicEdge d)} {A B : Set (EdgeConfiguration d)} (p : I)
    (hAinc : IsIncreasingEvent A) (hBinc : IsIncreasingEvent B)
    (hAdep : DependsOn E A) (hBdep : DependsOn F B) :
    (bernoulliBondMeasure d p).real A * (bernoulliBondMeasure d p).real B ≤
      (bernoulliBondMeasure d p).real (A ∩ B) := by
  simpa [bernoulliBondMeasure] using
    setBernoulli_real_fkg_of_dependsOn (ι := CubicEdge d) p hAinc hBinc hAdep hBdep

/-- Finite-support FKG for decreasing cubic bond events. -/
theorem bernoulliBondMeasure_real_fkg_of_decreasing_dependsOn (d : ℕ)
    {E F : Finset (CubicEdge d)} {A B : Set (EdgeConfiguration d)} (p : I)
    (hAdec : IsDecreasingEvent A) (hBdec : IsDecreasingEvent B)
    (hAdep : DependsOn E A) (hBdep : DependsOn F B) :
    (bernoulliBondMeasure d p).real A * (bernoulliBondMeasure d p).real B ≤
      (bernoulliBondMeasure d p).real (A ∩ B) := by
  simpa [bernoulliBondMeasure] using
    setBernoulli_real_fkg_of_decreasing_dependsOn (ι := CubicEdge d) p hAdec hBdec
      hAdep hBdep

/-- Finite-support negative correlation for an increasing cubic event and a decreasing cubic
event. -/
theorem bernoulliBondMeasure_real_le_mul_of_increasing_decreasing_dependsOn (d : ℕ)
    {E F : Finset (CubicEdge d)} {A B : Set (EdgeConfiguration d)} (p : I)
    (hAinc : IsIncreasingEvent A) (hBdec : IsDecreasingEvent B)
    (hAdep : DependsOn E A) (hBdep : DependsOn F B) :
    (bernoulliBondMeasure d p).real (A ∩ B) ≤
      (bernoulliBondMeasure d p).real A * (bernoulliBondMeasure d p).real B := by
  simpa [bernoulliBondMeasure] using
    setBernoulli_real_le_mul_of_increasing_decreasing_dependsOn (ι := CubicEdge d) p
      hAinc hBdec hAdep hBdep

/-- Finite-support iterated FKG for increasing cubic bond events. -/
theorem bernoulliBondMeasure_real_iterated_fkg_of_dependsOn (d : ℕ)
    {κ : Type*} [DecidableEq κ] {E : κ → Finset (CubicEdge d)} {J : Finset κ}
    {A : κ → Set (EdgeConfiguration d)} (p : I)
    (hAinc : ∀ i ∈ J, IsIncreasingEvent (A i))
    (hAdep : ∀ i ∈ J, DependsOn (E i) (A i)) :
    J.prod (fun i ↦ (bernoulliBondMeasure d p).real (A i)) ≤
      (bernoulliBondMeasure d p).real (finiteEventInter J A) := by
  simpa [bernoulliBondMeasure] using
    setBernoulli_real_iterated_fkg_of_dependsOn (ι := CubicEdge d) p hAinc hAdep

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
