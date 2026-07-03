import Percolation.Bernoulli.Basic
import Mathlib.Combinatorics.SetFamily.HarrisKleitman
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.Probability.Martingale.Convergence

/-!
# Increasing events for Bernoulli percolation

This file starts the Chapter 2 infrastructure from Grimmett's *Percolation*: events on
edge-configuration spaces that are preserved when more edges are opened.  The definitions are
kept for arbitrary coordinate types, and the final section specializes them to the cubic-lattice
events already developed in `Percolation.Bernoulli.Basic`.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped ENNReal Finset unitInterval BigOperators symmDiff

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

theorem restrictTo_coe_finset_of_subset {ι : Type*} [DecidableEq ι]
    {E s : Finset ι} (hsE : s ⊆ E) :
    restrictTo E ((s : Finset ι) : Set ι) = s := by
  ext e
  constructor
  · intro he
    exact (mem_restrictTo_iff E ((s : Finset ι) : Set ι) e).mp he |>.2
  · intro hes
    exact (mem_restrictTo_iff E ((s : Finset ι) : Set ι) e).mpr ⟨hsE hes, hes⟩

/-- Force the finite trace `s` on the support `E`, leaving all coordinates outside `E` as in
the ambient configuration `ω`. This is the source-shaped finite conditioning operation in
Grimmett's martingale proof of FKG. -/
def forceFiniteTrace {ι : Type*} (E s : Finset ι) (ω : Set ι) : Set ι :=
  (s : Set ι) ∪ (ω \ (E : Set ι))

@[simp]
theorem mem_forceFiniteTrace_iff {ι : Type*}
    (E s : Finset ι) (ω : Set ι) (e : ι) :
    e ∈ forceFiniteTrace E s ω ↔ e ∈ s ∨ e ∈ ω ∧ e ∉ E := by
  simp [forceFiniteTrace]

/-- The forced configuration agrees with its finite trace on every coordinate in the conditioning
support. -/
theorem forceFiniteTrace_agree_on {ι : Type*} (E s : Finset ι) (ω : Set ι) :
    ∀ e ∈ E, (e ∈ forceFiniteTrace E s ω ↔ e ∈ ((s : Finset ι) : Set ι)) := by
  intro e heE
  rw [mem_forceFiniteTrace_iff]
  constructor
  · rintro (hes | hωE)
    · exact hes
    · exact (hωE.2 heE).elim
  · intro hes
    exact Or.inl hes

theorem forceFiniteTrace_subset_of_subset {ι : Type*}
    {E s t : Finset ι} {ω : Set ι} (hst : s ⊆ t) :
    forceFiniteTrace E s ω ⊆ forceFiniteTrace E t ω := by
  intro e he
  rw [mem_forceFiniteTrace_iff] at he ⊢
  exact he.imp (fun hes ↦ hst hes) id

theorem restrictTo_forceFiniteTrace_of_subset {ι : Type*} [DecidableEq ι]
    {E s : Finset ι} (hsE : s ⊆ E) (ω : Set ι) :
    restrictTo E (forceFiniteTrace E s ω) = s := by
  ext e
  rw [mem_restrictTo_iff, mem_forceFiniteTrace_iff]
  constructor
  · rintro ⟨heE, hes | hωE⟩
    · exact hes
    · exact (hωE.2 heE).elim
  · intro hes
    exact ⟨hsE hes, Or.inl hes⟩

/-- A finite-support event only depends on the coordinates in `E`. -/
def DependsOn {ι : Type*} (E : Finset ι) (A : Set (Set ι)) : Prop :=
  ∀ ⦃ω η : Set ι⦄, (∀ e ∈ E, (e ∈ ω ↔ e ∈ η)) → (ω ∈ A ↔ η ∈ A)

theorem DependsOn.forceFiniteTrace_mem_iff {ι : Type*}
    {E s : Finset ι} {A : Set (Set ι)} (hA : DependsOn E A) (ω : Set ι) :
    forceFiniteTrace E s ω ∈ A ↔ ((s : Finset ι) : Set ι) ∈ A :=
  hA (forceFiniteTrace_agree_on E s ω)

/-- Pulling an event back by a finite trace forcing map only depends on the original support
outside the forced coordinates. -/
theorem DependsOn.forceFiniteTrace_preimage {ι : Type*} [DecidableEq ι]
    {E F s : Finset ι} {A : Set (Set ι)} (hA : DependsOn F A) :
    DependsOn (F.filter fun e ↦ e ∉ E) {ω | forceFiniteTrace E s ω ∈ A} := by
  intro ω η hcoord
  exact hA fun e heF ↦ by
    by_cases heE : e ∈ E
    · rw [mem_forceFiniteTrace_iff, mem_forceFiniteTrace_iff]
      simp [heE]
    · have heFilter : e ∈ F.filter (fun e ↦ e ∉ E) := Finset.mem_filter.mpr ⟨heF, heE⟩
      rw [mem_forceFiniteTrace_iff, mem_forceFiniteTrace_iff]
      simp [heE, hcoord e heFilter]

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

/-- A real-valued observable only depends on the coordinates in `E`. -/
def DependsOnFunction {ι : Type*} (E : Finset ι) (X : Set ι → ℝ) : Prop :=
  ∀ ⦃ω η : Set ι⦄, (∀ e ∈ E, (e ∈ ω ↔ e ∈ η)) → X ω = X η

theorem DependsOnFunction.mono {ι : Type*} {E F : Finset ι} {X : Set ι → ℝ}
    (hX : DependsOnFunction E X) (hEF : E ⊆ F) :
    DependsOnFunction F X := by
  intro ω η hcoord
  exact hX fun e he ↦ hcoord e (hEF he)

theorem DependsOnFunction.mul {ι : Type*} {E : Finset ι} {X Y : Set ι → ℝ}
    (hX : DependsOnFunction E X) (hY : DependsOnFunction E Y) :
    DependsOnFunction E (fun ω ↦ X ω * Y ω) := by
  intro ω η hcoord
  change X ω * Y ω = X η * Y η
  rw [hX hcoord, hY hcoord]

theorem DependsOnFunction.eq_restrictTo {ι : Type*} [DecidableEq ι]
    {E : Finset ι} {X : Set ι → ℝ} (hX : DependsOnFunction E X) (ω : Set ι) :
    X ((restrictTo E ω : Finset ι) : Set ι) = X ω := by
  exact hX fun e he ↦ by simp [restrictTo, he]

/-- On a finite coordinate type, every event depends on the full coordinate set. -/
theorem dependsOn_univ {ι : Type*} [Fintype ι] {A : Set (Set ι)} :
    DependsOn (Finset.univ : Finset ι) A := by
  intro ω η hcoord
  have hωη : ω = η := by
    ext e
    exact hcoord e (by simp)
  rw [hωη]

/-- On a finite coordinate type, every observable depends on the full coordinate set. -/
theorem dependsOnFunction_univ {ι : Type*} [Fintype ι] {X : Set ι → ℝ} :
    DependsOnFunction (Finset.univ : Finset ι) X := by
  intro ω η hcoord
  have hωη : ω = η := by
    ext e
    exact hcoord e (by simp)
  rw [hωη]

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

/-- The finite trace of a real-valued observable on support `E`. -/
noncomputable def finiteObservableTrace {ι : Type*} (_E : Finset ι) (X : Set ι → ℝ) :
    Finset ι → ℝ :=
  fun s ↦ X ((s : Finset ι) : Set ι)

/-- Lift a finite-cube observable to the full configuration space by reading only the trace on
`E`. Conditional-probability martingale approximants in the infinite FKG proof have this shape. -/
noncomputable def observableOfFiniteTrace {ι : Type*} [DecidableEq ι]
    (E : Finset ι) (X : Finset ι → ℝ) : Set ι → ℝ :=
  fun ω ↦ X (restrictTo E ω)

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

theorem IsIncreasingRandomVariable.finiteObservableTrace {ι : Type*}
    {E : Finset ι} {X : Set ι → ℝ} (hX : IsIncreasingRandomVariable X) :
    IsIncreasingFinsetFunction E (finiteObservableTrace E X) := by
  intro s t hst htE
  exact hX.mono (by intro e he; exact hst he)

theorem finiteObservableTrace_isDecreasingFinsetFunction {ι : Type*}
    {E : Finset ι} {X : Set ι → ℝ}
    (hX : ∀ ⦃ω η : Set ι⦄, ω ⊆ η → X η ≤ X ω) :
    IsDecreasingFinsetFunction E (finiteObservableTrace E X) := by
  intro s t hst htE
  exact hX (by intro e he; exact hst he)

theorem dependsOnFunction_observableOfFiniteTrace {ι : Type*} [DecidableEq ι]
    (E : Finset ι) (X : Finset ι → ℝ) :
    DependsOnFunction E (observableOfFiniteTrace E X) := by
  intro ω η hcoord
  have hrestrict : restrictTo E ω = restrictTo E η := by
    ext e
    by_cases he : e ∈ E
    · simp [restrictTo, he, hcoord e he]
    · simp [restrictTo, he]
  simp [observableOfFiniteTrace, hrestrict]

theorem IsIncreasingFinsetFunction.observableOfFiniteTrace {ι : Type*} [DecidableEq ι]
    {E : Finset ι} {X : Finset ι → ℝ} (hX : IsIncreasingFinsetFunction E X) :
    IsIncreasingRandomVariable (observableOfFiniteTrace E X) := by
  intro ω η hωη
  exact hX.mono (by
    intro e he
    rw [mem_restrictTo_iff] at he ⊢
    exact ⟨he.1, hωη he.2⟩) (restrictTo_subset E η)

theorem IsDecreasingFinsetFunction.observableOfFiniteTrace {ι : Type*} [DecidableEq ι]
    {E : Finset ι} {X : Finset ι → ℝ} (hX : IsDecreasingFinsetFunction E X) :
    ∀ ⦃ω η : Set ι⦄, ω ⊆ η →
      observableOfFiniteTrace E X η ≤ observableOfFiniteTrace E X ω := by
  intro ω η hωη
  exact hX.antitone (by
    intro e he
    rw [mem_restrictTo_iff] at he ⊢
    exact ⟨he.1, hωη he.2⟩) (restrictTo_subset E η)

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

/-- Conditional probability of an event after forcing a finite trace and leaving the outside
coordinates random. In the infinite FKG proof this is the finite σ-algebra martingale
approximant, viewed as a real-valued observable on traces. -/
noncomputable def finiteTraceConditionalProbability {ι : Type*}
    (E : Finset ι) (p : I) (A : Set (Set ι)) (s : Finset ι) : ℝ :=
  setBer((Set.univ : Set ι), p).real {ω | forceFiniteTrace E s ω ∈ A}

theorem finiteTraceConditionalProbability_nonneg {ι : Type*}
    (E : Finset ι) (p : I) (A : Set (Set ι)) (s : Finset ι) :
    0 ≤ finiteTraceConditionalProbability E p A s := by
  unfold finiteTraceConditionalProbability
  exact measureReal_nonneg

theorem finiteTraceConditionalProbability_le_one {ι : Type*}
    (E : Finset ι) (p : I) (A : Set (Set ι)) (s : Finset ι) :
    finiteTraceConditionalProbability E p A s ≤ 1 := by
  unfold finiteTraceConditionalProbability
  exact measureReal_le_one

theorem observableOfFiniteTrace_finiteTraceConditionalProbability_nonneg
    {ι : Type*} [DecidableEq ι] (E : Finset ι) (p : I)
    (A : Set (Set ι)) (ω : Set ι) :
    0 ≤ observableOfFiniteTrace E (finiteTraceConditionalProbability E p A) ω :=
  finiteTraceConditionalProbability_nonneg E p A (restrictTo E ω)

theorem observableOfFiniteTrace_finiteTraceConditionalProbability_le_one
    {ι : Type*} [DecidableEq ι] (E : Finset ι) (p : I)
    (A : Set (Set ι)) (ω : Set ι) :
    observableOfFiniteTrace E (finiteTraceConditionalProbability E p A) ω ≤ 1 :=
  finiteTraceConditionalProbability_le_one E p A (restrictTo E ω)

/-- If `A` already depends on the finite conditioning support, then the conditional probability
after forcing trace `s` is exactly the indicator of `A` at that trace. This is the finite
tower-property fixed point for the conditional-probability approximants. -/
theorem finiteTraceConditionalProbability_eq_indicator_of_dependsOn {ι : Type*}
    {E s : Finset ι} {A : Set (Set ι)} (hA : DependsOn E A) (p : I) :
    finiteTraceConditionalProbability E p A s =
      A.indicator (fun _ ↦ (1 : ℝ)) ((s : Finset ι) : Set ι) := by
  unfold finiteTraceConditionalProbability
  by_cases hsA : ((s : Finset ι) : Set ι) ∈ A
  · have hset : {ω : Set ι | forceFiniteTrace E s ω ∈ A} = Set.univ := by
      ext ω
      simp [hA.forceFiniteTrace_mem_iff ω, hsA]
    rw [hset]
    simp [Set.indicator_of_mem hsA]
  · have hset : {ω : Set ι | forceFiniteTrace E s ω ∈ A} = ∅ := by
      ext ω
      simp [hA.forceFiniteTrace_mem_iff ω, hsA]
    rw [hset]
    simp [Set.indicator_of_notMem hsA]

/-- On traces contained in the conditioning support, the conditional probability of a
finite-support event is the indicator of its finite event trace. -/
theorem finiteTraceConditionalProbability_eq_eventTrace_indicator_of_dependsOn
    {ι : Type*} [DecidableEq ι] {E s : Finset ι} {A : Set (Set ι)}
    (hA : DependsOn E A) (p : I) (hsE : s ⊆ E) :
    finiteTraceConditionalProbability E p A s =
      (eventTrace E A : Set (Finset ι)).indicator (fun _ ↦ (1 : ℝ)) s := by
  rw [finiteTraceConditionalProbability_eq_indicator_of_dependsOn hA p]
  by_cases hsA : ((s : Finset ι) : Set ι) ∈ A
  · have hsT : s ∈ eventTrace E A := (mem_eventTrace_iff E A s).mpr ⟨hsE, hsA⟩
    simp [Set.indicator_of_mem hsA, Set.indicator_of_mem hsT]
  · have hsT : s ∉ eventTrace E A := by
      intro hs
      exact hsA ((mem_eventTrace_iff E A s).mp hs).2
    simp [Set.indicator_of_notMem hsA, Set.indicator_of_notMem hsT]

/-- A finite-support event is a fixed point of its own conditional-probability lift. -/
theorem observableOfFiniteTrace_finiteTraceConditionalProbability_eq_indicator_of_dependsOn
    {ι : Type*} [DecidableEq ι] {E : Finset ι} {A : Set (Set ι)}
    (hA : DependsOn E A) (p : I) :
    observableOfFiniteTrace E (finiteTraceConditionalProbability E p A) =
      fun ω ↦ A.indicator (fun _ ↦ (1 : ℝ)) ω := by
  funext ω
  rw [observableOfFiniteTrace]
  rw [finiteTraceConditionalProbability_eq_indicator_of_dependsOn hA p]
  have hiff : (((restrictTo E ω : Finset ι) : Set ι) ∈ A ↔ ω ∈ A) := by
    exact hA fun e he ↦ by simp [restrictTo, he]
  by_cases hω : ω ∈ A
  · have hres : ((restrictTo E ω : Finset ι) : Set ι) ∈ A := hiff.mpr hω
    simp [Set.indicator_of_mem hres, Set.indicator_of_mem hω]
  · have hres : ((restrictTo E ω : Finset ι) : Set ι) ∉ A := by
      intro h
      exact hω (hiff.mp h)
    simp [Set.indicator_of_notMem hres, Set.indicator_of_notMem hω]

theorem finiteTraceConditionalProbability_isIncreasingFinsetFunction {ι : Type*}
    {E : Finset ι} (p : I) {A : Set (Set ι)} (hA : IsIncreasingEvent A) :
    IsIncreasingFinsetFunction E (finiteTraceConditionalProbability E p A) := by
  intro s t hst _htE
  unfold finiteTraceConditionalProbability
  exact measureReal_mono fun ω hω ↦ hA (forceFiniteTrace_subset_of_subset hst) hω

theorem finiteTraceConditionalProbability_isDecreasingFinsetFunction {ι : Type*}
    {E : Finset ι} (p : I) {A : Set (Set ι)} (hA : IsDecreasingEvent A) :
    IsDecreasingFinsetFunction E (finiteTraceConditionalProbability E p A) := by
  intro s t hst _htE
  unfold finiteTraceConditionalProbability
  exact measureReal_mono fun ω hω ↦ hA.antitone (forceFiniteTrace_subset_of_subset hst) hω

/-- Threshold events of the conditional trace probability. These are increasing finite-cube
events whenever the original event is increasing. -/
noncomputable def finiteTraceConditionalEvent {ι : Type*}
    (E : Finset ι) (p : I) (A : Set (Set ι)) (r : ℝ) : Set (Finset ι) :=
  {s | r ≤ finiteTraceConditionalProbability E p A s}

theorem finiteTraceConditionalEvent_isIncreasingTrace {ι : Type*}
    {E : Finset ι} (p : I) {A : Set (Set ι)} (r : ℝ) (hA : IsIncreasingEvent A) :
    IsIncreasingTrace E (finiteTraceConditionalEvent E p A r) := by
  intro s t hst htE hs
  exact hs.trans
    ((finiteTraceConditionalProbability_isIncreasingFinsetFunction (E := E) p hA) hst htE)

theorem finiteTraceConditionalEvent_isDecreasingTrace {ι : Type*}
    {E : Finset ι} (p : I) {A : Set (Set ι)} (r : ℝ) (hA : IsDecreasingEvent A) :
    IsDecreasingTrace E (finiteTraceConditionalEvent E p A r) := by
  intro s t hst htE ht
  exact ht.trans
    ((finiteTraceConditionalProbability_isDecreasingFinsetFunction (E := E) p hA) hst htE)

theorem finiteTraceConditionalEvent_eventOfTrace_isIncreasingEvent {ι : Type*}
    [DecidableEq ι] {E : Finset ι} (p : I) {A : Set (Set ι)} (r : ℝ)
    (hA : IsIncreasingEvent A) :
    IsIncreasingEvent (eventOfTrace E (finiteTraceConditionalEvent E p A r)) :=
  (finiteTraceConditionalEvent_isIncreasingTrace (E := E) p r hA).eventOfTrace

theorem finiteTraceConditionalEvent_eventOfTrace_isDecreasingEvent {ι : Type*}
    [DecidableEq ι] {E : Finset ι} (p : I) {A : Set (Set ι)} (r : ℝ)
    (hA : IsDecreasingEvent A) :
    IsDecreasingEvent (eventOfTrace E (finiteTraceConditionalEvent E p A r)) := by
  rw [isDecreasingEvent_iff]
  intro ω η hωη hη
  exact finiteTraceConditionalEvent_isDecreasingTrace (E := E) p r hA (by
    intro e he
    rw [mem_restrictTo_iff] at he ⊢
    exact ⟨he.1, hωη he.2⟩) (restrictTo_subset E η) hη

theorem dependsOn_eventOfTrace_finiteTraceConditionalEvent {ι : Type*}
    [DecidableEq ι] (E : Finset ι) (p : I) (A : Set (Set ι)) (r : ℝ) :
    DependsOn E (eventOfTrace E (finiteTraceConditionalEvent E p A r)) :=
  dependsOn_eventOfTrace E (finiteTraceConditionalEvent E p A r)

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

/-- Finite-coordinate weighted FKG/Harris inequality for increasing observables, with the
support specialized to all coordinates of a finite coordinate type. -/
theorem finiteBernoulliExpectation_fkg_univ {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ℝ} {X Y : Finset ι → ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hX : IsIncreasingFinsetFunction (Finset.univ : Finset ι) X)
    (hY : IsIncreasingFinsetFunction (Finset.univ : Finset ι) Y) :
    finiteBernoulliExpectation (Finset.univ : Finset ι) p X *
        finiteBernoulliExpectation (Finset.univ : Finset ι) p Y ≤
      finiteBernoulliExpectation (Finset.univ : Finset ι) p (fun s ↦ X s * Y s) :=
  finiteBernoulliExpectation_fkg hp0 hp1 hX hY

/-- Finite-coordinate weighted FKG/Harris inequality for decreasing observables, with the
support specialized to all coordinates of a finite coordinate type. -/
theorem finiteBernoulliExpectation_fkg_of_decreasing_univ {ι : Type*}
    [Fintype ι] [DecidableEq ι] {p : ℝ} {X Y : Finset ι → ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hX : IsDecreasingFinsetFunction (Finset.univ : Finset ι) X)
    (hY : IsDecreasingFinsetFunction (Finset.univ : Finset ι) Y) :
    finiteBernoulliExpectation (Finset.univ : Finset ι) p X *
        finiteBernoulliExpectation (Finset.univ : Finset ι) p Y ≤
      finiteBernoulliExpectation (Finset.univ : Finset ι) p (fun s ↦ X s * Y s) :=
  finiteBernoulliExpectation_fkg_of_decreasing hp0 hp1 hX hY

/-- Finite-coordinate negative correlation for an increasing observable and a decreasing
observable, with the support specialized to all coordinates of a finite coordinate type. -/
theorem finiteBernoulliExpectation_le_mul_of_increasing_decreasing_univ {ι : Type*}
    [Fintype ι] [DecidableEq ι] {p : ℝ} {X Y : Finset ι → ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hX : IsIncreasingFinsetFunction (Finset.univ : Finset ι) X)
    (hY : IsDecreasingFinsetFunction (Finset.univ : Finset ι) Y) :
    finiteBernoulliExpectation (Finset.univ : Finset ι) p (fun s ↦ X s * Y s) ≤
      finiteBernoulliExpectation (Finset.univ : Finset ι) p X *
        finiteBernoulliExpectation (Finset.univ : Finset ι) p Y :=
  finiteBernoulliExpectation_le_mul_of_increasing_decreasing hp0 hp1 hX hY

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

/-- If a configuration already has finite trace `s` on `E`, forcing that trace does not change
the configuration. -/
theorem forceFiniteTrace_eq_of_mem_finiteTraceCylinder {ι : Type*} [DecidableEq ι]
    {E s : Finset ι} {ω : Set ι} (hω : ω ∈ finiteTraceCylinder E s) :
    forceFiniteTrace E s ω = ω := by
  ext e
  rw [mem_forceFiniteTrace_iff]
  by_cases heE : e ∈ E
  · have hmem : e ∈ restrictTo E ω ↔ e ∈ s := by
      rw [hω]
    rw [mem_restrictTo_iff] at hmem
    have hsiff : e ∈ s ↔ e ∈ ω := by
      constructor
      · intro hes
        exact (hmem.mpr hes).2
      · intro heω
        exact hmem.mp ⟨heE, heω⟩
    simp [heE, hsiff]
  · have hnot_s : e ∉ s := by
      intro hes
      have hmem : e ∈ restrictTo E ω ↔ e ∈ s := by
        rw [hω]
      exact heE (restrictTo_subset E ω (hmem.mpr hes))
    simp [heE, hnot_s]

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

/-- Events reconstructed from a finite trace are measurable cylinder events. -/
theorem measurableSet_eventOfTrace {ι : Type*} [DecidableEq ι]
    (E : Finset ι) (T : Set (Finset ι)) :
    MeasurableSet (eventOfTrace E T) := by
  classical
  rw [eventOfTrace_eq_iUnion_finiteTraceCylinder]
  exact Finset.measurableSet_biUnion (E.powerset.filter fun s ↦ s ∈ T) fun s _hs ↦
    measurableSet_finiteTraceCylinder E s

/-- The σ-algebra generated by reading only the finite trace on `E`. A set is measurable for
this σ-algebra exactly when it has the form `eventOfTrace E T`. -/
@[implicit_reducible]
noncomputable def finiteTraceMeasurableSpace {ι : Type*} [DecidableEq ι]
    (E : Finset ι) : MeasurableSpace (Set ι) :=
  MeasurableSpace.comap (restrictTo E) ⊤

theorem measurableSet_finiteTraceMeasurableSpace_iff {ι : Type*} [DecidableEq ι]
    (E : Finset ι) (A : Set (Set ι)) :
    MeasurableSet[finiteTraceMeasurableSpace E] A ↔
      ∃ T : Set (Finset ι), eventOfTrace E T = A := by
  rw [finiteTraceMeasurableSpace, MeasurableSpace.measurableSet_comap]
  constructor
  · rintro ⟨T, _hT, hTpre⟩
    exact ⟨T, by simpa [eventOfTrace] using hTpre⟩
  · rintro ⟨T, rfl⟩
    exact ⟨T, by trivial, by rfl⟩

theorem finiteTraceMeasurableSpace_le {ι : Type*} [DecidableEq ι] (E : Finset ι) :
    finiteTraceMeasurableSpace E ≤ (inferInstance : MeasurableSpace (Set ι)) := by
  intro A hA
  rcases (measurableSet_finiteTraceMeasurableSpace_iff E A).mp hA with ⟨T, hT⟩
  rw [← hT]
  exact measurableSet_eventOfTrace E T

theorem measurableSet_eventOfTrace_finiteTraceMeasurableSpace {ι : Type*} [DecidableEq ι]
    (E : Finset ι) (T : Set (Finset ι)) :
    MeasurableSet[finiteTraceMeasurableSpace E] (eventOfTrace E T) :=
  (measurableSet_finiteTraceMeasurableSpace_iff E (eventOfTrace E T)).mpr ⟨T, rfl⟩

theorem measurable_observableOfFiniteTrace_finiteTraceMeasurableSpace
    {ι : Type*} [DecidableEq ι] (E : Finset ι) (X : Finset ι → ℝ) :
    Measurable[finiteTraceMeasurableSpace E] (observableOfFiniteTrace E X) := by
  intro U _hU
  exact (measurableSet_finiteTraceMeasurableSpace_iff E
    ((observableOfFiniteTrace E X) ⁻¹' U)).mpr ⟨{s | X s ∈ U}, rfl⟩

theorem finiteTraceMeasurableSpace_mono {ι : Type*} [DecidableEq ι] {E F : Finset ι}
    (hEF : E ⊆ F) :
    finiteTraceMeasurableSpace E ≤ finiteTraceMeasurableSpace F := by
  intro A hA
  rcases (measurableSet_finiteTraceMeasurableSpace_iff E A).mp hA with ⟨T, hT⟩
  rw [← hT]
  have hdep : DependsOn F (eventOfTrace E T) := (dependsOn_eventOfTrace E T).mono hEF
  have heq :
      eventOfTrace E T = eventOfTrace F (eventTrace F (eventOfTrace E T)) := by
    ext ω
    exact (restrictTo_mem_eventTrace_iff_of_dependsOn hdep ω).symm
  rw [heq]
  exact measurableSet_eventOfTrace_finiteTraceMeasurableSpace F
    (eventTrace F (eventOfTrace E T))

/-- Coordinate-open events indexed by a chosen set of coordinates. -/
def coordinateEvents {ι : Type*} (S : Set ι) : Set (Set (Set ι)) :=
  {A | ∃ e ∈ S, {ω : Set ι | e ∈ ω} = A}

/-- The σ-algebra generated by coordinate-open events in `S`. -/
@[reducible]
def coordinateMeasurableSpace {ι : Type*} (S : Set ι) : MeasurableSpace (Set ι) :=
  MeasurableSpace.generateFrom (coordinateEvents S)

theorem measurableSet_coordinateEvent_of_mem {ι : Type*} (S : Set ι) {e : ι}
    (he : e ∈ S) :
    MeasurableSet[coordinateMeasurableSpace S] {ω : Set ι | e ∈ ω} :=
  MeasurableSpace.measurableSet_generateFrom (by exact ⟨e, he, rfl⟩)

theorem coordinateMeasurableSpace_le {ι : Type*} [DecidableEq ι] (S : Set ι) :
    coordinateMeasurableSpace S ≤ (inferInstance : MeasurableSpace (Set ι)) := by
  rw [coordinateMeasurableSpace]
  exact MeasurableSpace.generateFrom_le fun A hA ↦ by
    rcases hA with ⟨e, _he, rfl⟩
    simpa [Set.singleton_subset_iff] using measurableSet_superset_finset ({e} : Finset ι)

theorem measurableSet_finiteTraceCylinder_coordinateMeasurableSpace
    {ι : Type*} [DecidableEq ι] {S : Set ι} {E s : Finset ι}
    (hES : (E : Set ι) ⊆ S) :
    MeasurableSet[coordinateMeasurableSpace S] (finiteTraceCylinder E s) := by
  classical
  by_cases hsE : s ⊆ E
  · rw [finiteTraceCylinder_eq_open_closed_of_subset hsE]
    have hopen :
        MeasurableSet[coordinateMeasurableSpace S] {ω : Set ι | (s : Set ι) ⊆ ω} := by
      rw [show {ω : Set ι | (s : Set ι) ⊆ ω} =
          ⋂ e ∈ s, {ω : Set ι | e ∈ ω} by
        ext ω
        simp [Set.subset_def]]
      exact MeasurableSet.biInter (Finset.countable_toSet s) fun e he ↦
        measurableSet_coordinateEvent_of_mem S (hES (hsE he))
    have hclosed : MeasurableSet[coordinateMeasurableSpace S]
        {ω : Set ι | Disjoint (((E \ s : Finset ι) : Set ι)) ω} := by
      rw [show {ω : Set ι | Disjoint (((E \ s : Finset ι) : Set ι)) ω} =
          ⋂ e ∈ E \ s, ({ω : Set ι | e ∈ ω})ᶜ by
        ext ω
        simp [Set.disjoint_left]]
      exact MeasurableSet.biInter (Finset.countable_toSet (E \ s)) fun e he ↦
        (measurableSet_coordinateEvent_of_mem S (hES (Finset.mem_sdiff.mp he).1)).compl
    exact hopen.inter hclosed
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
    exact @MeasurableSet.empty (Set ι) (coordinateMeasurableSpace S)

theorem measurableSet_eventOfTrace_coordinateMeasurableSpace
    {ι : Type*} [DecidableEq ι] {S : Set ι} (E : Finset ι) (T : Set (Finset ι))
    (hES : (E : Set ι) ⊆ S) :
    MeasurableSet[coordinateMeasurableSpace S] (eventOfTrace E T) := by
  classical
  rw [eventOfTrace_eq_iUnion_finiteTraceCylinder]
  exact Finset.measurableSet_biUnion (E.powerset.filter fun s ↦ s ∈ T) fun s _hs ↦
    measurableSet_finiteTraceCylinder_coordinateMeasurableSpace hES

theorem DependsOn.measurableSet_coordinateMeasurableSpace {ι : Type*} [DecidableEq ι]
    {S : Set ι} {E : Finset ι} {A : Set (Set ι)}
    (hA : DependsOn E A) (hES : (E : Set ι) ⊆ S) :
    MeasurableSet[coordinateMeasurableSpace S] A := by
  have hAeq : A = eventOfTrace E (eventTrace E A) := by
    ext ω
    exact (restrictTo_mem_eventTrace_iff_of_dependsOn hA ω).symm
  rw [hAeq]
  exact measurableSet_eventOfTrace_coordinateMeasurableSpace E (eventTrace E A) hES

/-- Bernoulli coordinate σ-algebras generated by disjoint coordinate sets are independent. -/
theorem setBernoulli_indep_coordinateMeasurableSpace_of_disjoint
    {ι : Type*} [DecidableEq ι] (p : I) (S T : Set ι) (hdisj : Disjoint S T) :
    Indep (coordinateMeasurableSpace S) (coordinateMeasurableSpace T)
      setBer((Set.univ : Set ι), p) := by
  classical
  have hsm : ∀ e : ι, MeasurableSet {ω : Set ι | e ∈ ω} := by
    intro e
    simpa [Set.singleton_subset_iff] using measurableSet_superset_finset ({e} : Finset ι)
  simpa [coordinateMeasurableSpace, coordinateEvents] using
    (ProbabilityTheory.iIndepSet.indep_generateFrom_of_disjoint
      (μ := setBer((Set.univ : Set ι), p))
      (s := fun e : ι ↦ {ω : Set ι | e ∈ ω})
      hsm (setBernoulli_iIndepSet_mem_univ (ι := ι) p) S T hdisj)

/-- The filtration obtained by revealing a monotone sequence of finite traces. -/
noncomputable def finiteTraceFiltration {ι : Type*} [DecidableEq ι]
    (E : ℕ → Finset ι) (hE : Monotone E) :
    Filtration ℕ (inferInstance : MeasurableSpace (Set ι)) where
  seq n := finiteTraceMeasurableSpace (E n)
  mono' _ _ hnm := finiteTraceMeasurableSpace_mono (hE hnm)
  le' n := finiteTraceMeasurableSpace_le (E n)

/-- If every element of a finite set is eventually contained in a sequence of finite supports,
then the whole finite set is eventually contained in that sequence. -/
theorem eventually_finset_subset_of_eventually_mem {ι : Type*} {E : ℕ → Finset ι}
    (F : Finset ι) (hE : ∀ e ∈ F, ∀ᶠ n in Filter.atTop, e ∈ E n) :
    ∀ᶠ n in Filter.atTop, F ⊆ E n := by
  classical
  induction F using Finset.induction with
  | empty =>
      exact Filter.Eventually.of_forall fun n e he ↦ (Finset.notMem_empty e he).elim
  | insert a F ha ih =>
      have ha_eventually : ∀ᶠ n in Filter.atTop, a ∈ E n :=
        hE a (Finset.mem_insert_self a F)
      have hF_eventually : ∀ᶠ n in Filter.atTop, F ⊆ E n :=
        ih fun e he ↦ hE e (Finset.mem_insert.mpr (Or.inr he))
      exact (ha_eventually.and hF_eventually).mono fun n hn e he ↦ by
        rw [Finset.mem_insert] at he
        rcases he with rfl | he
        · exact hn.1
        · exact hn.2 he

/-- L¹ martingale convergence for event indicators along the finite-trace filtration. This is the
Mathlib convergence theorem in the notation used by the percolation FKG development. -/
theorem tendsto_eLpNorm_condExp_indicator_finiteTraceFiltration
    {ι : Type*} [DecidableEq ι] (p : I) {E : ℕ → Finset ι} (hE : Monotone E)
    {A : Set (Set ι)}
    (hA : MeasurableSet[⨆ n, (finiteTraceFiltration E hE) n] A) :
    Filter.Tendsto
      (fun n ↦
        eLpNorm
          (setBer((Set.univ : Set ι), p)[fun ω ↦ A.indicator (fun _ ↦ (1 : ℝ)) ω |
            (finiteTraceFiltration E hE) n] -
            fun ω ↦ A.indicator (fun _ ↦ (1 : ℝ)) ω)
          1 (setBer((Set.univ : Set ι), p)))
      Filter.atTop (nhds 0) := by
  let μ := setBer((Set.univ : Set ι), p)
  have hsup_le :
      (⨆ n, (finiteTraceFiltration E hE) n) ≤
        (inferInstance : MeasurableSpace (Set ι)) :=
    iSup_le fun n ↦ (finiteTraceFiltration E hE).le n
  have hAamb : MeasurableSet A := hsup_le A hA
  have hAint : Integrable (fun ω ↦ A.indicator (fun _ ↦ (1 : ℝ)) ω) μ :=
    (integrable_const (1 : ℝ)).indicator hAamb
  have hAsm :
      StronglyMeasurable[⨆ n, (finiteTraceFiltration E hE) n]
        (fun ω ↦ A.indicator (fun _ ↦ (1 : ℝ)) ω) :=
    (measurable_const.indicator hA).stronglyMeasurable
  simpa [μ] using
    (hAint.tendsto_eLpNorm_condExp (ℱ := finiteTraceFiltration E hE) hAsm)

/-- L¹ martingale convergence for finite-trace filtrations whose supremum is the full
configuration σ-algebra. -/
theorem tendsto_eLpNorm_condExp_indicator_finiteTraceFiltration_of_iSup_eq
    {ι : Type*} [DecidableEq ι] (p : I) {E : ℕ → Finset ι} (hE : Monotone E)
    (hEsup :
      (⨆ n, (finiteTraceFiltration E hE) n) =
        (inferInstance : MeasurableSpace (Set ι)))
    {A : Set (Set ι)} (hA : MeasurableSet A) :
    Filter.Tendsto
      (fun n ↦
        eLpNorm
          (setBer((Set.univ : Set ι), p)[fun ω ↦ A.indicator (fun _ ↦ (1 : ℝ)) ω |
            (finiteTraceFiltration E hE) n] -
            fun ω ↦ A.indicator (fun _ ↦ (1 : ℝ)) ω)
          1 (setBer((Set.univ : Set ι), p)))
      Filter.atTop (nhds 0) := by
  refine tendsto_eLpNorm_condExp_indicator_finiteTraceFiltration (p := p) hE ?_
  rw [hEsup]
  exact hA

/-- Finite-support events are measurable cylinder events. -/
theorem DependsOn.measurableSet {ι : Type*} [DecidableEq ι]
    {E : Finset ι} {A : Set (Set ι)} (hA : DependsOn E A) :
    MeasurableSet A := by
  have hAeq : A = eventOfTrace E (eventTrace E A) := by
    ext ω
    exact (restrictTo_mem_eventTrace_iff_of_dependsOn hA ω).symm
  rw [hAeq]
  exact measurableSet_eventOfTrace E (eventTrace E A)

/-- The algebra of events depending on finitely many coordinates. This is the cylinder algebra
used by the finite FKG theorem before the martingale/measure-limit passage. -/
def finiteSupportEvents (ι : Type*) : Set (Set (Set ι)) :=
  {A | ∃ E : Finset ι, DependsOn E A}

theorem mem_finiteSupportEvents_iff {ι : Type*} (A : Set (Set ι)) :
    A ∈ finiteSupportEvents ι ↔ ∃ E : Finset ι, DependsOn E A :=
  Iff.rfl

/-- Finite-support events form an algebra of sets. -/
theorem isSetAlgebra_finiteSupportEvents {ι : Type*} [DecidableEq ι] :
    MeasureTheory.IsSetAlgebra (finiteSupportEvents ι) where
  empty_mem := by
    refine ⟨∅, ?_⟩
    intro ω η hcoord
    simp
  compl_mem := by
    rintro A ⟨E, hA⟩
    exact ⟨E, hA.compl⟩
  union_mem := by
    rintro A B ⟨E, hA⟩ ⟨F, hB⟩
    refine ⟨E ∪ F, ?_⟩
    exact (hA.mono (by intro e he; exact Finset.mem_union_left F he)).union
      (hB.mono (by intro e he; exact Finset.mem_union_right E he))

/-- Every finite-support event is measurable in the configuration σ-algebra. -/
theorem measurableSet_of_mem_finiteSupportEvents {ι : Type*} [DecidableEq ι]
    {A : Set (Set ι)} (hA : A ∈ finiteSupportEvents ι) :
    MeasurableSet A := by
  rcases hA with ⟨E, hE⟩
  exact hE.measurableSet

theorem coordinateOpen_mem_finiteSupportEvents {ι : Type*} [DecidableEq ι] (i : ι) :
    {ω : Set ι | i ∈ ω} ∈ finiteSupportEvents ι := by
  refine ⟨{i}, ?_⟩
  intro ω η hcoord
  exact hcoord i (by simp)

/-- The finite-support event algebra generates the full configuration σ-algebra. -/
theorem generateFrom_finiteSupportEvents_eq {ι : Type*} [DecidableEq ι] :
    MeasurableSpace.generateFrom (finiteSupportEvents ι) =
      (inferInstance : MeasurableSpace (Set ι)) := by
  have hset :
      MeasurableSpace.comap (⇑MeasurableEquiv.setOf.symm)
          (inferInstance : MeasurableSpace (ι → Prop)) =
        (inferInstance : MeasurableSpace (Set ι)) :=
    MeasurableEquiv.setOf.symm.measurableEmbedding.comap_eq
  have hset' :
      MeasurableSpace.comap (fun ω : Set ι ↦ fun i ↦ i ∈ ω)
          (inferInstance : MeasurableSpace (ι → Prop)) =
        (inferInstance : MeasurableSpace (Set ι)) := by
    simpa using hset
  let mFS : MeasurableSpace (Set ι) := MeasurableSpace.generateFrom (finiteSupportEvents ι)
  apply le_antisymm
  · exact MeasurableSpace.generateFrom_le
      (fun A hA ↦ measurableSet_of_mem_finiteSupportEvents hA)
  · have hmem :
        @Measurable (Set ι) (ι → Prop) mFS inferInstance (fun ω i ↦ i ∈ ω) := by
      rw [measurable_pi_iff]
      intro i
      refine measurable_to_countable' ?_
      intro b
      have hcoord : MeasurableSet[mFS] {ω : Set ι | i ∈ ω} :=
        MeasurableSpace.measurableSet_generateFrom (coordinateOpen_mem_finiteSupportEvents i)
      by_cases hb : b
      · simpa [mFS, hb] using hcoord
      · have hfiber :
            ((fun ω : Set ι ↦ i ∈ ω) ⁻¹' ({b} : Set Prop)) =
              ({ω : Set ι | i ∈ ω} : Set (Set ι))ᶜ := by
          ext ω
          simp [hb]
        rw [hfiber]
        exact hcoord.compl
    have hcomap :
        MeasurableSpace.comap (fun ω : Set ι ↦ fun i ↦ i ∈ ω)
            (inferInstance : MeasurableSpace (ι → Prop)) ≤ mFS :=
      hmem.comap_le
    simpa [mFS, hset'] using hcomap

/-- Forcing a finite trace is measurable from the outside-coordinate σ-algebra to the full
configuration σ-algebra. -/
theorem measurable_forceFiniteTrace_coordinateMeasurableSpace
    {ι : Type*} [DecidableEq ι] (E s : Finset ι) :
    @Measurable (Set ι) (Set ι)
      (coordinateMeasurableSpace ((E : Set ι)ᶜ)) (inferInstance)
      (forceFiniteTrace E s) := by
  rw [← generateFrom_finiteSupportEvents_eq (ι := ι)]
  refine @measurable_generateFrom (Set ι) (Set ι)
    (coordinateMeasurableSpace ((E : Set ι)ᶜ)) (finiteSupportEvents ι)
    (forceFiniteTrace E s) ?_
  intro A hA
  rcases hA with ⟨F, hF⟩
  have hdep : DependsOn (F.filter fun e ↦ e ∉ E)
      {ω | forceFiniteTrace E s ω ∈ A} :=
    hF.forceFiniteTrace_preimage
  exact hdep.measurableSet_coordinateMeasurableSpace (by
    intro e he
    exact (Finset.mem_filter.mp he).2)

/-- Product disintegration over a finite trace atom. Intersecting an arbitrary measurable event
with the exact trace atom is the atom probability times the probability of the event after forcing
that trace and resampling the outside coordinates. -/
theorem setBernoulli_real_inter_finiteTraceCylinder_eq_mul_finiteTraceConditionalProbability
    {ι : Type*} [DecidableEq ι] (E s : Finset ι) (p : I) {A : Set (Set ι)}
    (hAmeas : MeasurableSet A) :
    setBer((Set.univ : Set ι), p).real (A ∩ finiteTraceCylinder E s) =
      setBer((Set.univ : Set ι), p).real (finiteTraceCylinder E s) *
        finiteTraceConditionalProbability E p A s := by
  let μ := setBer((Set.univ : Set ι), p)
  let Tail : Set (Set ι) := {ω | forceFiniteTrace E s ω ∈ A}
  have hCsub : MeasurableSet[coordinateMeasurableSpace (E : Set ι)]
      (finiteTraceCylinder E s) :=
    measurableSet_finiteTraceCylinder_coordinateMeasurableSpace (S := (E : Set ι))
      (E := E) (s := s) (by intro e he; exact he)
  have hTailsub : MeasurableSet[coordinateMeasurableSpace ((E : Set ι)ᶜ)] Tail := by
    exact measurable_forceFiniteTrace_coordinateMeasurableSpace E s hAmeas
  have hCmeas : MeasurableSet (finiteTraceCylinder E s) :=
    (coordinateMeasurableSpace_le (E : Set ι)) (finiteTraceCylinder E s) hCsub
  have hTailmeas : MeasurableSet Tail :=
    (coordinateMeasurableSpace_le ((E : Set ι)ᶜ)) Tail hTailsub
  have hdisj : Disjoint (E : Set ι) ((E : Set ι)ᶜ) := by
    rw [Set.disjoint_left]
    intro e heE heEc
    exact heEc heE
  have hIndep :=
    setBernoulli_indep_coordinateMeasurableSpace_of_disjoint (ι := ι) p (E : Set ι)
      ((E : Set ι)ᶜ) hdisj
  have hIndepSet : IndepSet (finiteTraceCylinder E s) Tail μ := by
    rw [indepSet_iff_measure_inter_eq_mul (μ := μ) hCmeas hTailmeas]
    exact (Indep_iff _ _ μ).1 hIndep (finiteTraceCylinder E s) Tail hCsub hTailsub
  have hset : A ∩ finiteTraceCylinder E s = finiteTraceCylinder E s ∩ Tail := by
    ext ω
    constructor
    · intro hω
      refine ⟨hω.2, ?_⟩
      simpa [Tail, forceFiniteTrace_eq_of_mem_finiteTraceCylinder hω.2] using hω.1
    · intro hω
      refine ⟨?_, hω.1⟩
      simpa [Tail, forceFiniteTrace_eq_of_mem_finiteTraceCylinder hω.1] using hω.2
  calc
    setBer((Set.univ : Set ι), p).real (A ∩ finiteTraceCylinder E s) =
        μ.real (finiteTraceCylinder E s ∩ Tail) := by
      simp [μ, hset]
    _ = μ.real (finiteTraceCylinder E s) * μ.real Tail := by
      have h := hIndepSet.measure_inter_eq_mul
      unfold Measure.real
      rw [h, ENNReal.toReal_mul]
    _ = setBer((Set.univ : Set ι), p).real (finiteTraceCylinder E s) *
        finiteTraceConditionalProbability E p A s := by
      rfl

/-- If an increasing finite-support filtration eventually contains every coordinate, then its
supremum is the full configuration σ-algebra. -/
theorem iSup_finiteTraceFiltration_eq_of_eventually_mem {ι : Type*} [DecidableEq ι]
    {E : ℕ → Finset ι} (hE : Monotone E)
    (hcover : ∀ e : ι, ∀ᶠ n in Filter.atTop, e ∈ E n) :
    (⨆ n, (finiteTraceFiltration E hE) n) =
      (inferInstance : MeasurableSpace (Set ι)) := by
  apply le_antisymm
  · exact iSup_le fun n ↦ (finiteTraceFiltration E hE).le n
  · calc
      (inferInstance : MeasurableSpace (Set ι)) =
          MeasurableSpace.generateFrom (finiteSupportEvents ι) :=
        (generateFrom_finiteSupportEvents_eq (ι := ι)).symm
      _ ≤ ⨆ n, (finiteTraceFiltration E hE) n := by
        refine MeasurableSpace.generateFrom_le ?_
        intro A hA
        rcases hA with ⟨F, hFdep⟩
        have hFE_eventually : ∀ᶠ n in Filter.atTop, F ⊆ E n :=
          eventually_finset_subset_of_eventually_mem F fun e _he ↦ hcover e
        rcases hFE_eventually.exists with ⟨n, hFn⟩
        have hAdep : DependsOn (E n) A := hFdep.mono hFn
        have hAeq : A = eventOfTrace (E n) (eventTrace (E n) A) := by
          ext ω
          exact (restrictTo_mem_eventTrace_iff_of_dependsOn hAdep ω).symm
        rw [hAeq]
        exact (le_iSup (fun n ↦ (finiteTraceFiltration E hE) n) n)
          (eventOfTrace (E n) (eventTrace (E n) A))
          (measurableSet_eventOfTrace_finiteTraceMeasurableSpace (E n)
            (eventTrace (E n) A))

/-- L¹ martingale convergence along a finite-trace exhaustion that eventually contains every
coordinate. -/
theorem tendsto_eLpNorm_condExp_indicator_finiteTraceFiltration_of_eventually_mem
    {ι : Type*} [DecidableEq ι] (p : I) {E : ℕ → Finset ι} (hE : Monotone E)
    (hcover : ∀ e : ι, ∀ᶠ n in Filter.atTop, e ∈ E n)
    {A : Set (Set ι)} (hA : MeasurableSet A) :
    Filter.Tendsto
      (fun n ↦
        eLpNorm
          (setBer((Set.univ : Set ι), p)[fun ω ↦ A.indicator (fun _ ↦ (1 : ℝ)) ω |
            (finiteTraceFiltration E hE) n] -
            fun ω ↦ A.indicator (fun _ ↦ (1 : ℝ)) ω)
          1 (setBer((Set.univ : Set ι), p)))
      Filter.atTop (nhds 0) :=
  tendsto_eLpNorm_condExp_indicator_finiteTraceFiltration_of_iSup_eq
    (p := p) hE (iSup_finiteTraceFiltration_eq_of_eventually_mem hE hcover) hA

/-- Finite-support events are measure-dense in Bernoulli product measure. This is the
measure-approximation half of Grimmett's limiting passage after finite FKG. -/
theorem setBernoulli_measureDense_finiteSupportEvents {ι : Type*} [DecidableEq ι] (p : I) :
    (setBer((Set.univ : Set ι), p)).MeasureDense (finiteSupportEvents ι) := by
  refine MeasureTheory.Measure.MeasureDense.of_generateFrom_isSetAlgebra_finite
    (μ := setBer((Set.univ : Set ι), p)) isSetAlgebra_finiteSupportEvents ?_
  exact (generateFrom_finiteSupportEvents_eq (ι := ι)).symm

/-- Any measurable Bernoulli event can be approximated in measure by a finite-support event. -/
theorem exists_finiteSupportEvent_measure_symmDiff_lt {ι : Type*} [DecidableEq ι]
    (p : I) {A : Set (Set ι)} (hA : MeasurableSet A) {ε : ℝ} (hε : 0 < ε) :
    ∃ B, B ∈ finiteSupportEvents ι ∧
      setBer((Set.univ : Set ι), p) (A ∆ B) < ENNReal.ofReal ε := by
  exact (setBernoulli_measureDense_finiteSupportEvents (ι := ι) p).approx A hA
    (by finiteness) ε hε

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

/-- The conditional-probability lift of a finite-support event integrates back to the event
probability. This is the finite-support tower property for the Chapter 2 FKG martingale
approximants. -/
theorem integral_observableOfFiniteTrace_finiteTraceConditionalProbability_setBernoulli
    {ι : Type*} [DecidableEq ι] {E : Finset ι} {A : Set (Set ι)}
    (hA : DependsOn E A) (p : I) :
    (∫ ω, observableOfFiniteTrace E (finiteTraceConditionalProbability E p A) ω
        ∂setBer((Set.univ : Set ι), p)) =
      setBer((Set.univ : Set ι), p).real A := by
  rw [observableOfFiniteTrace_finiteTraceConditionalProbability_eq_indicator_of_dependsOn hA p]
  exact integral_indicator_one (μ := setBer((Set.univ : Set ι), p)) hA.measurableSet

/-- Products of conditional-probability lifts of finite-support events integrate back to the
probability of the intersection. -/
theorem integral_observableOfFiniteTrace_finiteTraceConditionalProbability_mul_setBernoulli
    {ι : Type*} [DecidableEq ι] {E : Finset ι} {A B : Set (Set ι)}
    (hA : DependsOn E A) (hB : DependsOn E B) (p : I) :
    (∫ ω,
        observableOfFiniteTrace E (finiteTraceConditionalProbability E p A) ω *
          observableOfFiniteTrace E (finiteTraceConditionalProbability E p B) ω
        ∂setBer((Set.univ : Set ι), p)) =
      setBer((Set.univ : Set ι), p).real (A ∩ B) := by
  rw [observableOfFiniteTrace_finiteTraceConditionalProbability_eq_indicator_of_dependsOn hA p,
    observableOfFiniteTrace_finiteTraceConditionalProbability_eq_indicator_of_dependsOn hB p]
  have hfun :
      (fun ω : Set ι ↦
          A.indicator (fun _ ↦ (1 : ℝ)) ω *
            B.indicator (fun _ ↦ (1 : ℝ)) ω) =
        fun ω ↦ (A ∩ B).indicator (fun _ ↦ (1 : ℝ)) ω := by
    funext ω
    by_cases hωA : ω ∈ A <;> by_cases hωB : ω ∈ B <;> simp [hωA, hωB]
  rw [hfun]
  exact integral_indicator_one (μ := setBer((Set.univ : Set ι), p))
    (hA.measurableSet.inter hB.measurableSet)

/-- If a growing sequence of conditioning supports eventually contains the support of a
finite-support event, then the conditional-probability integrals are eventually constant and hence
converge to the event probability. -/
theorem tendsto_integral_finiteTraceConditionalProbability_of_eventually_dependsOn
    {ι : Type*} [DecidableEq ι] {Eseq : ℕ → Finset ι} {F : Finset ι}
    {A : Set (Set ι)} (hA : DependsOn F A)
    (hFE : ∀ᶠ n in Filter.atTop, F ⊆ Eseq n) (p : I) :
    Filter.Tendsto
      (fun n ↦
        ∫ ω, observableOfFiniteTrace (Eseq n)
            (finiteTraceConditionalProbability (Eseq n) p A) ω
          ∂setBer((Set.univ : Set ι), p)) Filter.atTop
      (nhds (setBer((Set.univ : Set ι), p).real A)) := by
  refine tendsto_nhds_of_eventually_eq ?_
  exact hFE.mono fun _n hsub ↦
    integral_observableOfFiniteTrace_finiteTraceConditionalProbability_setBernoulli
      (hA.mono hsub) p

/-- Product version of
`tendsto_integral_finiteTraceConditionalProbability_of_eventually_dependsOn`. -/
theorem tendsto_integral_finiteTraceConditionalProbability_mul_of_eventually_dependsOn
    {ι : Type*} [DecidableEq ι] {Eseq : ℕ → Finset ι} {FA FB : Finset ι}
    {A B : Set (Set ι)} (hA : DependsOn FA A) (hB : DependsOn FB B)
    (hFAE : ∀ᶠ n in Filter.atTop, FA ⊆ Eseq n)
    (hFBE : ∀ᶠ n in Filter.atTop, FB ⊆ Eseq n) (p : I) :
    Filter.Tendsto
      (fun n ↦
        ∫ ω,
          observableOfFiniteTrace (Eseq n)
              (finiteTraceConditionalProbability (Eseq n) p A) ω *
            observableOfFiniteTrace (Eseq n)
              (finiteTraceConditionalProbability (Eseq n) p B) ω
          ∂setBer((Set.univ : Set ι), p)) Filter.atTop
      (nhds (setBer((Set.univ : Set ι), p).real (A ∩ B))) := by
  refine tendsto_nhds_of_eventually_eq ?_
  exact (hFAE.and hFBE).mono fun _n hsub ↦
    integral_observableOfFiniteTrace_finiteTraceConditionalProbability_mul_setBernoulli
      (hA.mono hsub.1) (hB.mono hsub.2) p

/-- A finite-support observable is the finite sum of its values on exact trace cylinders. -/
theorem finiteObservableTrace_expansion_apply {ι : Type*} [DecidableEq ι]
    (E : Finset ι) (X : Set ι → ℝ) (ω : Set ι) :
    E.powerset.sum (fun s ↦
        X ((s : Finset ι) : Set ι) *
          (finiteTraceCylinder E s).indicator (fun _ : Set ι ↦ (1 : ℝ)) ω) =
      X ((restrictTo E ω : Finset ι) : Set ι) := by
  classical
  rw [Finset.sum_eq_single (restrictTo E ω)]
  · simp [finiteTraceCylinder]
  · intro s hs hne
    have hnot : ω ∉ finiteTraceCylinder E s := by
      intro hω
      exact hne hω.symm
    simp [Set.indicator_of_notMem hnot]
  · intro hnot
    exact (hnot (Finset.mem_powerset.mpr (restrictTo_subset E ω))).elim

/-- A finite-support observable is integrable under Bernoulli product measure. -/
theorem DependsOnFunction.integrable_setBernoulli {ι : Type*} [DecidableEq ι]
    {E : Finset ι} {X : Set ι → ℝ} (hX : DependsOnFunction E X) (p : I) :
    Integrable X (setBer((Set.univ : Set ι), p)) := by
  classical
  let μ := setBer((Set.univ : Set ι), p)
  let F : Set ι → ℝ := fun ω ↦
    E.powerset.sum fun s ↦
      X ((s : Finset ι) : Set ι) *
        (finiteTraceCylinder E s).indicator (fun _ : Set ι ↦ (1 : ℝ)) ω
  have hFint : Integrable F μ := by
    refine integrable_finsetSum E.powerset ?_
    intro s hs
    have hfun :
        (fun ω : Set ι ↦
            X ((s : Finset ι) : Set ι) *
              (finiteTraceCylinder E s).indicator (fun _ : Set ι ↦ (1 : ℝ)) ω) =
          (finiteTraceCylinder E s).indicator
            (fun _ : Set ι ↦ X ((s : Finset ι) : Set ι)) := by
      funext ω
      by_cases hω : ω ∈ finiteTraceCylinder E s
      · simp [Set.indicator_of_mem hω]
      · simp [Set.indicator_of_notMem hω]
    rw [hfun]
    exact (integrable_const (X ((s : Finset ι) : Set ι))).indicator
      (measurableSet_finiteTraceCylinder E s)
  refine hFint.congr ?_
  filter_upwards with ω
  dsimp [F]
  rw [finiteObservableTrace_expansion_apply E X ω, hX.eq_restrictTo]

/-- Product-measure expectation of a finite-support observable equals its finite-cube
expectation over the trace. -/
theorem DependsOnFunction.integral_setBernoulli_eq_finiteBernoulliExpectation
    {ι : Type*} [DecidableEq ι] {E : Finset ι} {X : Set ι → ℝ}
    (hX : DependsOnFunction E X) (p : I) :
    (∫ ω, X ω ∂setBer((Set.univ : Set ι), p)) =
      finiteBernoulliExpectation E (p : ℝ) (finiteObservableTrace E X) := by
  classical
  let μ := setBer((Set.univ : Set ι), p)
  let F : Set ι → ℝ := fun ω ↦
    E.powerset.sum fun s ↦
      X ((s : Finset ι) : Set ι) *
        (finiteTraceCylinder E s).indicator (fun _ : Set ι ↦ (1 : ℝ)) ω
  have hXF : X =ᵐ[μ] F := by
    filter_upwards with ω
    dsimp [F]
    rw [finiteObservableTrace_expansion_apply E X ω, hX.eq_restrictTo]
  calc
    (∫ ω, X ω ∂setBer((Set.univ : Set ι), p)) = ∫ ω, F ω ∂μ := by
      simpa [μ] using integral_congr_ae hXF
    _ = E.powerset.sum (fun s ↦
        ∫ ω, X ((s : Finset ι) : Set ι) *
          (finiteTraceCylinder E s).indicator (fun _ : Set ι ↦ (1 : ℝ)) ω ∂μ) := by
      rw [integral_finsetSum]
      intro s hs
      have hfun :
          (fun ω : Set ι ↦
              X ((s : Finset ι) : Set ι) *
                (finiteTraceCylinder E s).indicator (fun _ : Set ι ↦ (1 : ℝ)) ω) =
            (finiteTraceCylinder E s).indicator
              (fun _ : Set ι ↦ X ((s : Finset ι) : Set ι)) := by
        funext ω
        by_cases hω : ω ∈ finiteTraceCylinder E s
        · simp [Set.indicator_of_mem hω]
        · simp [Set.indicator_of_notMem hω]
      rw [hfun]
      exact (integrable_const (X ((s : Finset ι) : Set ι))).indicator
        (measurableSet_finiteTraceCylinder E s)
    _ = finiteBernoulliExpectation E (p : ℝ) (finiteObservableTrace E X) := by
      unfold finiteBernoulliExpectation finiteObservableTrace
      apply Finset.sum_congr rfl
      intro s hs
      have hsE : s ⊆ E := Finset.mem_powerset.mp hs
      have hfun :
          (fun ω : Set ι ↦
              X ((s : Finset ι) : Set ι) *
                (finiteTraceCylinder E s).indicator (fun _ : Set ι ↦ (1 : ℝ)) ω) =
            (finiteTraceCylinder E s).indicator
              (fun _ : Set ι ↦ X ((s : Finset ι) : Set ι)) := by
        funext ω
        by_cases hω : ω ∈ finiteTraceCylinder E s
        · simp [Set.indicator_of_mem hω]
        · simp [Set.indicator_of_notMem hω]
      rw [hfun]
      rw [integral_indicator_const
        (μ := μ) (e := X ((s : Finset ι) : Set ι))
        (s_meas := measurableSet_finiteTraceCylinder E s)]
      simp only [smul_eq_mul]
      change μ.real (finiteTraceCylinder E s) *
          X ((s : Finset ι) : Set ι) =
        (p : ℝ) ^ s.card * (1 - (p : ℝ)) ^ (E.card - s.card) *
          X ((s : Finset ι) : Set ι)
      rw [show μ.real (finiteTraceCylinder E s) =
          (p : ℝ) ^ s.card * (1 - (p : ℝ)) ^ (E.card - s.card) by
        dsimp [μ]
        exact setBernoulli_real_finiteTraceCylinder E s p hsE]

/-- The product-measure expectation of a lifted finite-cube observable is exactly its finite
Bernoulli expectation. -/
theorem integral_observableOfFiniteTrace_setBernoulli_eq_finiteBernoulliExpectation
    {ι : Type*} [DecidableEq ι] (E : Finset ι) (X : Finset ι → ℝ) (p : I) :
    (∫ ω, observableOfFiniteTrace E X ω ∂setBer((Set.univ : Set ι), p)) =
      finiteBernoulliExpectation E (p : ℝ) X := by
  rw [(dependsOnFunction_observableOfFiniteTrace E X).integral_setBernoulli_eq_finiteBernoulliExpectation p]
  unfold finiteBernoulliExpectation finiteObservableTrace observableOfFiniteTrace
  apply Finset.sum_congr rfl
  intro s hs
  rw [restrictTo_coe_finset_of_subset (Finset.mem_powerset.mp hs)]

/-- The explicit finite-trace conditional-probability observable has the defining integral
property of conditional expectation on every finite-trace event. -/
theorem setIntegral_eventOfTrace_finiteTraceConditionalProbability_setBernoulli
    {ι : Type*} [DecidableEq ι] (E : Finset ι) (T : Set (Finset ι)) (p : I)
    {A : Set (Set ι)} (hAmeas : MeasurableSet A) :
    (∫ ω in eventOfTrace E T,
        observableOfFiniteTrace E (finiteTraceConditionalProbability E p A) ω
        ∂setBer((Set.univ : Set ι), p)) =
      setBer((Set.univ : Set ι), p).real (A ∩ eventOfTrace E T) := by
  classical
  let μ := setBer((Set.univ : Set ι), p)
  have hfun :
      (eventOfTrace E T).indicator
          (fun ω : Set ι ↦
            observableOfFiniteTrace E (finiteTraceConditionalProbability E p A) ω) =
        observableOfFiniteTrace E
          (fun s ↦ T.indicator (fun _ ↦ (1 : ℝ)) s *
            finiteTraceConditionalProbability E p A s) := by
    funext ω
    by_cases hω : restrictTo E ω ∈ T
    · have hωevent : ω ∈ eventOfTrace E T := hω
      simp [observableOfFiniteTrace, hω, Set.indicator_of_mem hωevent]
    · have hωevent : ω ∉ eventOfTrace E T := hω
      simp [observableOfFiniteTrace, hω, Set.indicator_of_notMem hωevent]
  have hAevent :
      A ∩ eventOfTrace E T =
        ⋃ s ∈ E.powerset.filter (fun s ↦ s ∈ T), A ∩ finiteTraceCylinder E s := by
    rw [eventOfTrace_eq_iUnion_finiteTraceCylinder]
    ext ω
    constructor
    · intro hω
      rcases Set.mem_iUnion.mp hω.2 with ⟨s, hsω⟩
      rcases Set.mem_iUnion.mp hsω with ⟨hsfilter, hωs⟩
      exact Set.mem_iUnion.mpr ⟨s, Set.mem_iUnion.mpr ⟨hsfilter, ⟨hω.1, hωs⟩⟩⟩
    · intro hω
      rcases Set.mem_iUnion.mp hω with ⟨s, hsω⟩
      rcases Set.mem_iUnion.mp hsω with ⟨hsfilter, hAs⟩
      exact ⟨hAs.1, Set.mem_iUnion.mpr ⟨s, Set.mem_iUnion.mpr ⟨hsfilter, hAs.2⟩⟩⟩
  have hpair :
      Set.PairwiseDisjoint (↑(E.powerset.filter (fun s ↦ s ∈ T)))
        (fun s ↦ A ∩ finiteTraceCylinder E s) := by
    intro s _hs t _ht hst
    change Disjoint (A ∩ finiteTraceCylinder E s) (A ∩ finiteTraceCylinder E t)
    rw [Set.disjoint_left]
    intro ω hωs hωt
    exact hst (hωs.2.symm.trans hωt.2)
  have hmeasure :
      μ.real (A ∩ eventOfTrace E T) =
        (E.powerset.filter (fun s ↦ s ∈ T)).sum
          (fun s ↦ μ.real (A ∩ finiteTraceCylinder E s)) := by
    rw [hAevent]
    rw [measureReal_biUnion_finset (μ := μ)
      (s := E.powerset.filter (fun s ↦ s ∈ T))
      (f := fun s ↦ A ∩ finiteTraceCylinder E s) hpair
      (fun s _hs ↦ hAmeas.inter (measurableSet_finiteTraceCylinder E s))]
  have hprob :
      μ.real (A ∩ eventOfTrace E T) =
        finiteBernoulliExpectation E (p : ℝ)
          (fun s ↦ T.indicator (fun _ ↦ (1 : ℝ)) s *
            finiteTraceConditionalProbability E p A s) := by
    rw [hmeasure]
    unfold finiteBernoulliExpectation
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro s hs
    have hsE : s ⊆ E := Finset.mem_powerset.mp hs
    by_cases hT : s ∈ T
    · simp [hT]
      rw [setBernoulli_real_inter_finiteTraceCylinder_eq_mul_finiteTraceConditionalProbability
        E s p hAmeas]
      rw [setBernoulli_real_finiteTraceCylinder E s p hsE]
    · simp [hT]
  rw [← integral_indicator (μ := μ)
    (f := fun ω : Set ι ↦
      observableOfFiniteTrace E (finiteTraceConditionalProbability E p A) ω)
    (s := eventOfTrace E T) (measurableSet_eventOfTrace E T)]
  rw [hfun]
  rw [integral_observableOfFiniteTrace_setBernoulli_eq_finiteBernoulliExpectation]
  simpa [μ] using hprob.symm

/-- The explicit finite-trace conditional-probability observable is a version of the conditional
expectation of the event indicator with respect to the finite-trace σ-algebra. -/
theorem finiteTraceConditionalProbability_ae_eq_condExp
    {ι : Type*} [DecidableEq ι] (E : Finset ι) (p : I)
    {A : Set (Set ι)} (hAmeas : MeasurableSet A) :
    (fun ω : Set ι ↦
        observableOfFiniteTrace E (finiteTraceConditionalProbability E p A) ω) =ᵐ[
      setBer((Set.univ : Set ι), p)]
      setBer((Set.univ : Set ι), p)[fun ω ↦ A.indicator (fun _ ↦ (1 : ℝ)) ω |
        finiteTraceMeasurableSpace E] := by
  let μ := setBer((Set.univ : Set ι), p)
  have hm :
      finiteTraceMeasurableSpace E ≤ (inferInstance : MeasurableSpace (Set ι)) :=
    finiteTraceMeasurableSpace_le E
  haveI : SigmaFinite (μ.trim hm) := by infer_instance
  have hf : Integrable (fun ω : Set ι ↦ A.indicator (fun _ ↦ (1 : ℝ)) ω) μ :=
    (integrable_const (1 : ℝ)).indicator hAmeas
  have hgint : Integrable
      (fun ω : Set ι ↦
        observableOfFiniteTrace E (finiteTraceConditionalProbability E p A) ω) μ := by
    simpa [μ] using
      (dependsOnFunction_observableOfFiniteTrace E
        (finiteTraceConditionalProbability E p A)).integrable_setBernoulli p
  refine ae_eq_condExp_of_forall_setIntegral_eq
    (μ := μ) (m := finiteTraceMeasurableSpace E) hm hf ?_ ?_ ?_
  · intro S _hS _hμS
    exact hgint.integrableOn
  · intro S hS _hμS
    rcases (measurableSet_finiteTraceMeasurableSpace_iff E S).mp hS with ⟨T, hT⟩
    subst S
    have hright :
        (∫ ω in eventOfTrace E T, A.indicator (fun _ ↦ (1 : ℝ)) ω ∂μ) =
          μ.real (A ∩ eventOfTrace E T) := by
      rw [← integral_indicator (μ := μ)
        (f := fun ω : Set ι ↦ A.indicator (fun _ ↦ (1 : ℝ)) ω)
        (s := eventOfTrace E T) (measurableSet_eventOfTrace E T)]
      have hfun :
          (eventOfTrace E T).indicator
              (fun ω : Set ι ↦ A.indicator (fun _ ↦ (1 : ℝ)) ω) =
            fun ω ↦ (A ∩ eventOfTrace E T).indicator (fun _ ↦ (1 : ℝ)) ω := by
        funext ω
        by_cases hωA : ω ∈ A <;>
          by_cases hωT : ω ∈ eventOfTrace E T <;> simp [hωA, hωT]
      rw [hfun]
      exact integral_indicator_one (μ := μ) (hAmeas.inter (measurableSet_eventOfTrace E T))
    rw [setIntegral_eventOfTrace_finiteTraceConditionalProbability_setBernoulli E T p hAmeas]
    exact hright.symm
  · exact (measurable_observableOfFiniteTrace_finiteTraceMeasurableSpace E
      (finiteTraceConditionalProbability E p A)).aestronglyMeasurable

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

/-- A finite intersection of measurable configuration events is measurable. -/
theorem measurableSet_finiteEventInter {ι κ : Type*} [DecidableEq κ] [MeasurableSpace (Set ι)]
    {J : Finset κ} {A : κ → Set (Set ι)}
    (hA : ∀ i ∈ J, MeasurableSet (A i)) :
    MeasurableSet (finiteEventInter J A) := by
  induction J using Finset.induction with
  | empty =>
      simp
  | insert a J ha ih =>
      rw [finiteEventInter_insert]
      refine (hA a (Finset.mem_insert_self a J)).inter (ih ?_)
      intro i hi
      exact hA i (Finset.mem_insert.mpr (Or.inr hi))

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

/-- Lifting the indicator of a finite trace gives exactly the indicator of the corresponding
cylinder event. This is the bookkeeping bridge between event FKG and the observable form used by
conditional-expectation approximants. -/
theorem observableOfFiniteTrace_indicator {ι : Type*} [DecidableEq ι]
    (E : Finset ι) (T : Set (Finset ι)) :
    observableOfFiniteTrace E (fun s ↦ T.indicator (fun _ ↦ (1 : ℝ)) s) =
      fun ω ↦ (eventOfTrace E T).indicator (fun _ ↦ (1 : ℝ)) ω := by
  funext ω
  by_cases hω : restrictTo E ω ∈ T
  · have hω' : ω ∈ eventOfTrace E T := hω
    simp [observableOfFiniteTrace, hω, Set.indicator_of_mem hω']
  · have hω' : ω ∉ eventOfTrace E T := hω
    simp [observableOfFiniteTrace, hω, Set.indicator_of_notMem hω']

/-- Intersections of lifted finite-trace events are lifted intersections. -/
theorem eventOfTrace_inter_trace {ι : Type*} [DecidableEq ι]
    (E : Finset ι) (T U : Set (Finset ι)) :
    eventOfTrace E (T ∩ U) = eventOfTrace E T ∩ eventOfTrace E U := by
  ext ω
  simp [eventOfTrace]

theorem indicator_mul_indicator_inter {ι : Type*} (T U : Set (Finset ι)) (s : Finset ι) :
    T.indicator (fun _ ↦ (1 : ℝ)) s * U.indicator (fun _ ↦ (1 : ℝ)) s =
      (T ∩ U).indicator (fun _ ↦ (1 : ℝ)) s := by
  by_cases hT : s ∈ T <;> by_cases hU : s ∈ U <;> simp [hT, hU]

/-- The integral of a lifted finite-trace indicator is the probability of the corresponding
cylinder event. -/
theorem integral_observableOfFiniteTrace_indicator_setBernoulli {ι : Type*} [DecidableEq ι]
    (E : Finset ι) (T : Set (Finset ι)) (p : I) :
    (∫ ω, observableOfFiniteTrace E (fun s ↦ T.indicator (fun _ ↦ (1 : ℝ)) s) ω
        ∂setBer((Set.univ : Set ι), p)) =
      setBer((Set.univ : Set ι), p).real (eventOfTrace E T) := by
  rw [observableOfFiniteTrace_indicator]
  exact integral_indicator_one (μ := setBer((Set.univ : Set ι), p))
    (measurableSet_eventOfTrace E T)

/-- Products of lifted finite-trace indicators integrate to the probability of the intersection
of the corresponding cylinder events. -/
theorem integral_observableOfFiniteTrace_indicator_mul_setBernoulli {ι : Type*}
    [DecidableEq ι] (E : Finset ι) (T U : Set (Finset ι)) (p : I) :
    (∫ ω,
        observableOfFiniteTrace E (fun s ↦ T.indicator (fun _ ↦ (1 : ℝ)) s) ω *
          observableOfFiniteTrace E (fun s ↦ U.indicator (fun _ ↦ (1 : ℝ)) s) ω
        ∂setBer((Set.univ : Set ι), p)) =
      setBer((Set.univ : Set ι), p).real (eventOfTrace E T ∩ eventOfTrace E U) := by
  have hfun :
      (fun ω : Set ι ↦
          observableOfFiniteTrace E (fun s ↦ T.indicator (fun _ ↦ (1 : ℝ)) s) ω *
            observableOfFiniteTrace E (fun s ↦ U.indicator (fun _ ↦ (1 : ℝ)) s) ω) =
        observableOfFiniteTrace E (fun s ↦ (T ∩ U).indicator (fun _ ↦ (1 : ℝ)) s) := by
    funext ω
    simp [observableOfFiniteTrace, indicator_mul_indicator_inter]
  rw [hfun, integral_observableOfFiniteTrace_indicator_setBernoulli]
  rw [eventOfTrace_inter_trace]

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

/-- Finite-support FKG/Harris inequality for increasing real-valued observables under the
Bernoulli product measure. This is the product-measure random-variable face of Grimmett's
Theorem (2.4) before the martingale limiting passage. -/
theorem setBernoulli_integral_fkg_of_dependsOnFunction {ι : Type*} [DecidableEq ι]
    {E F : Finset ι} {X Y : Set ι → ℝ} (p : I)
    (hXinc : IsIncreasingRandomVariable X) (hYinc : IsIncreasingRandomVariable Y)
    (hXdep : DependsOnFunction E X) (hYdep : DependsOnFunction F Y) :
    (∫ ω, X ω ∂setBer((Set.univ : Set ι), p)) *
        (∫ ω, Y ω ∂setBer((Set.univ : Set ι), p)) ≤
      ∫ ω, X ω * Y ω ∂setBer((Set.univ : Set ι), p) := by
  let G : Finset ι := E ∪ F
  have hXdepG : DependsOnFunction G X :=
    hXdep.mono (by intro e he; exact Finset.mem_union_left F he)
  have hYdepG : DependsOnFunction G Y :=
    hYdep.mono (by intro e he; exact Finset.mem_union_right E he)
  have hXYdepG : DependsOnFunction G (fun ω ↦ X ω * Y ω) := hXdepG.mul hYdepG
  rw [hXdepG.integral_setBernoulli_eq_finiteBernoulliExpectation p,
    hYdepG.integral_setBernoulli_eq_finiteBernoulliExpectation p,
    hXYdepG.integral_setBernoulli_eq_finiteBernoulliExpectation p]
  simpa [finiteObservableTrace] using
    finiteBernoulliExpectation_fkg (E := G) (p := (p : ℝ)) p.2.1 p.2.2
      hXinc.finiteObservableTrace hYinc.finiteObservableTrace

/-- Finite-support FKG/Harris inequality for decreasing real-valued observables under the
Bernoulli product measure. -/
theorem setBernoulli_integral_fkg_of_decreasing_dependsOnFunction {ι : Type*}
    [DecidableEq ι] {E F : Finset ι} {X Y : Set ι → ℝ} (p : I)
    (hXdec : ∀ ⦃ω η : Set ι⦄, ω ⊆ η → X η ≤ X ω)
    (hYdec : ∀ ⦃ω η : Set ι⦄, ω ⊆ η → Y η ≤ Y ω)
    (hXdep : DependsOnFunction E X) (hYdep : DependsOnFunction F Y) :
    (∫ ω, X ω ∂setBer((Set.univ : Set ι), p)) *
        (∫ ω, Y ω ∂setBer((Set.univ : Set ι), p)) ≤
      ∫ ω, X ω * Y ω ∂setBer((Set.univ : Set ι), p) := by
  let G : Finset ι := E ∪ F
  have hXdepG : DependsOnFunction G X :=
    hXdep.mono (by intro e he; exact Finset.mem_union_left F he)
  have hYdepG : DependsOnFunction G Y :=
    hYdep.mono (by intro e he; exact Finset.mem_union_right E he)
  have hXYdepG : DependsOnFunction G (fun ω ↦ X ω * Y ω) := hXdepG.mul hYdepG
  rw [hXdepG.integral_setBernoulli_eq_finiteBernoulliExpectation p,
    hYdepG.integral_setBernoulli_eq_finiteBernoulliExpectation p,
    hXYdepG.integral_setBernoulli_eq_finiteBernoulliExpectation p]
  simpa [finiteObservableTrace] using
    finiteBernoulliExpectation_fkg_of_decreasing (E := G) (p := (p : ℝ)) p.2.1 p.2.2
      (finiteObservableTrace_isDecreasingFinsetFunction hXdec)
      (finiteObservableTrace_isDecreasingFinsetFunction hYdec)

/-- Finite-support negative correlation for an increasing and a decreasing observable under the
Bernoulli product measure. -/
theorem setBernoulli_integral_le_mul_of_increasing_decreasing_dependsOnFunction
    {ι : Type*} [DecidableEq ι] {E F : Finset ι} {X Y : Set ι → ℝ} (p : I)
    (hXinc : IsIncreasingRandomVariable X)
    (hYdec : ∀ ⦃ω η : Set ι⦄, ω ⊆ η → Y η ≤ Y ω)
    (hXdep : DependsOnFunction E X) (hYdep : DependsOnFunction F Y) :
    (∫ ω, X ω * Y ω ∂setBer((Set.univ : Set ι), p)) ≤
      (∫ ω, X ω ∂setBer((Set.univ : Set ι), p)) *
        (∫ ω, Y ω ∂setBer((Set.univ : Set ι), p)) := by
  let G : Finset ι := E ∪ F
  have hXdepG : DependsOnFunction G X :=
    hXdep.mono (by intro e he; exact Finset.mem_union_left F he)
  have hYdepG : DependsOnFunction G Y :=
    hYdep.mono (by intro e he; exact Finset.mem_union_right E he)
  have hXYdepG : DependsOnFunction G (fun ω ↦ X ω * Y ω) := hXdepG.mul hYdepG
  rw [hXdepG.integral_setBernoulli_eq_finiteBernoulliExpectation p,
    hYdepG.integral_setBernoulli_eq_finiteBernoulliExpectation p,
    hXYdepG.integral_setBernoulli_eq_finiteBernoulliExpectation p]
  simpa [finiteObservableTrace] using
    finiteBernoulliExpectation_le_mul_of_increasing_decreasing (E := G) (p := (p : ℝ))
      p.2.1 p.2.2 hXinc.finiteObservableTrace
      (finiteObservableTrace_isDecreasingFinsetFunction hYdec)

/-- FKG for lifted finite-cube increasing observables under the Bernoulli product measure. This is
the finite-coordinate observable form that conditional-probability approximants will use. -/
theorem setBernoulli_integral_fkg_observableOfFiniteTrace {ι : Type*} [DecidableEq ι]
    {E : Finset ι} {X Y : Finset ι → ℝ} (p : I)
    (hXinc : IsIncreasingFinsetFunction E X) (hYinc : IsIncreasingFinsetFunction E Y) :
    (∫ ω, observableOfFiniteTrace E X ω ∂setBer((Set.univ : Set ι), p)) *
        (∫ ω, observableOfFiniteTrace E Y ω ∂setBer((Set.univ : Set ι), p)) ≤
      ∫ ω, observableOfFiniteTrace E X ω * observableOfFiniteTrace E Y ω
        ∂setBer((Set.univ : Set ι), p) := by
  exact setBernoulli_integral_fkg_of_dependsOnFunction p
    hXinc.observableOfFiniteTrace hYinc.observableOfFiniteTrace
    (dependsOnFunction_observableOfFiniteTrace E X)
    (dependsOnFunction_observableOfFiniteTrace E Y)

/-- FKG for lifted finite-cube decreasing observables under the Bernoulli product measure. -/
theorem setBernoulli_integral_fkg_of_decreasing_observableOfFiniteTrace
    {ι : Type*} [DecidableEq ι] {E : Finset ι} {X Y : Finset ι → ℝ} (p : I)
    (hXdec : IsDecreasingFinsetFunction E X) (hYdec : IsDecreasingFinsetFunction E Y) :
    (∫ ω, observableOfFiniteTrace E X ω ∂setBer((Set.univ : Set ι), p)) *
        (∫ ω, observableOfFiniteTrace E Y ω ∂setBer((Set.univ : Set ι), p)) ≤
      ∫ ω, observableOfFiniteTrace E X ω * observableOfFiniteTrace E Y ω
        ∂setBer((Set.univ : Set ι), p) := by
  exact setBernoulli_integral_fkg_of_decreasing_dependsOnFunction p
    hXdec.observableOfFiniteTrace hYdec.observableOfFiniteTrace
    (dependsOnFunction_observableOfFiniteTrace E X)
    (dependsOnFunction_observableOfFiniteTrace E Y)

/-- Negative association for a lifted increasing finite-cube observable and a lifted decreasing
finite-cube observable. -/
theorem setBernoulli_integral_le_mul_of_increasing_decreasing_observableOfFiniteTrace
    {ι : Type*} [DecidableEq ι] {E : Finset ι} {X Y : Finset ι → ℝ} (p : I)
    (hXinc : IsIncreasingFinsetFunction E X) (hYdec : IsDecreasingFinsetFunction E Y) :
    (∫ ω, observableOfFiniteTrace E X ω * observableOfFiniteTrace E Y ω
        ∂setBer((Set.univ : Set ι), p)) ≤
      (∫ ω, observableOfFiniteTrace E X ω ∂setBer((Set.univ : Set ι), p)) *
        (∫ ω, observableOfFiniteTrace E Y ω ∂setBer((Set.univ : Set ι), p)) := by
  exact setBernoulli_integral_le_mul_of_increasing_decreasing_dependsOnFunction p
    hXinc.observableOfFiniteTrace hYdec.observableOfFiniteTrace
    (dependsOnFunction_observableOfFiniteTrace E X)
    (dependsOnFunction_observableOfFiniteTrace E Y)

/-- The finite conditional-probability step in Grimmett's martingale proof of FKG. After
conditioning on the finite trace `E`, the conditional probabilities of two increasing events are
increasing finite-cube observables, so finite FKG applies. -/
theorem finiteTraceConditionalProbability_fkg {ι : Type*} [DecidableEq ι]
    {E : Finset ι} (p : I) {A B : Set (Set ι)}
    (hAinc : IsIncreasingEvent A) (hBinc : IsIncreasingEvent B) :
    finiteBernoulliExpectation E (p : ℝ) (finiteTraceConditionalProbability E p A) *
        finiteBernoulliExpectation E (p : ℝ) (finiteTraceConditionalProbability E p B) ≤
      finiteBernoulliExpectation E (p : ℝ)
        (fun s ↦
          finiteTraceConditionalProbability E p A s *
            finiteTraceConditionalProbability E p B s) := by
  exact finiteBernoulliExpectation_fkg (E := E) (p := (p : ℝ)) p.2.1 p.2.2
    (finiteTraceConditionalProbability_isIncreasingFinsetFunction (E := E) p hAinc)
    (finiteTraceConditionalProbability_isIncreasingFinsetFunction (E := E) p hBinc)

/-- The lifted finite conditional-probability FKG step under the Bernoulli product measure. -/
theorem setBernoulli_integral_fkg_finiteTraceConditionalProbability
    {ι : Type*} [DecidableEq ι] {E : Finset ι} (p : I) {A B : Set (Set ι)}
    (hAinc : IsIncreasingEvent A) (hBinc : IsIncreasingEvent B) :
    (∫ ω,
        observableOfFiniteTrace E (finiteTraceConditionalProbability E p A) ω
        ∂setBer((Set.univ : Set ι), p)) *
        (∫ ω,
          observableOfFiniteTrace E (finiteTraceConditionalProbability E p B) ω
          ∂setBer((Set.univ : Set ι), p)) ≤
      ∫ ω,
        observableOfFiniteTrace E (finiteTraceConditionalProbability E p A) ω *
          observableOfFiniteTrace E (finiteTraceConditionalProbability E p B) ω
        ∂setBer((Set.univ : Set ι), p) := by
  exact setBernoulli_integral_fkg_observableOfFiniteTrace (E := E) (p := p)
    (finiteTraceConditionalProbability_isIncreasingFinsetFunction (E := E) p hAinc)
    (finiteTraceConditionalProbability_isIncreasingFinsetFunction (E := E) p hBinc)

/-- Decreasing-event version of the finite conditional-probability FKG step. -/
theorem finiteTraceConditionalProbability_fkg_of_decreasing
    {ι : Type*} [DecidableEq ι] {E : Finset ι} (p : I) {A B : Set (Set ι)}
    (hAdec : IsDecreasingEvent A) (hBdec : IsDecreasingEvent B) :
    finiteBernoulliExpectation E (p : ℝ) (finiteTraceConditionalProbability E p A) *
        finiteBernoulliExpectation E (p : ℝ) (finiteTraceConditionalProbability E p B) ≤
      finiteBernoulliExpectation E (p : ℝ)
        (fun s ↦
          finiteTraceConditionalProbability E p A s *
            finiteTraceConditionalProbability E p B s) := by
  exact finiteBernoulliExpectation_fkg_of_decreasing (E := E) (p := (p : ℝ)) p.2.1 p.2.2
    (finiteTraceConditionalProbability_isDecreasingFinsetFunction (E := E) p hAdec)
    (finiteTraceConditionalProbability_isDecreasingFinsetFunction (E := E) p hBdec)

/-- Negative-association version of the finite conditional-probability step. -/
theorem finiteTraceConditionalProbability_le_mul_of_increasing_decreasing
    {ι : Type*} [DecidableEq ι] {E : Finset ι} (p : I) {A B : Set (Set ι)}
    (hAinc : IsIncreasingEvent A) (hBdec : IsDecreasingEvent B) :
    finiteBernoulliExpectation E (p : ℝ)
        (fun s ↦
          finiteTraceConditionalProbability E p A s *
            finiteTraceConditionalProbability E p B s) ≤
      finiteBernoulliExpectation E (p : ℝ) (finiteTraceConditionalProbability E p A) *
        finiteBernoulliExpectation E (p : ℝ) (finiteTraceConditionalProbability E p B) := by
  exact finiteBernoulliExpectation_le_mul_of_increasing_decreasing (E := E) (p := (p : ℝ))
    p.2.1 p.2.2
    (finiteTraceConditionalProbability_isIncreasingFinsetFunction (E := E) p hAinc)
    (finiteTraceConditionalProbability_isDecreasingFinsetFunction (E := E) p hBdec)

/-- FKG/Harris inequality for finite-trace cylinder events, derived through the lifted-observable
form. This is the exact finite-coordinate face used by conditional-probability approximants in the
full measurable-event proof. -/
theorem setBernoulli_real_fkg_eventOfTrace {ι : Type*} [DecidableEq ι]
    {E : Finset ι} {T U : Set (Finset ι)} (p : I)
    (hT : IsIncreasingTrace E T) (hU : IsIncreasingTrace E U) :
    setBer((Set.univ : Set ι), p).real (eventOfTrace E T) *
        setBer((Set.univ : Set ι), p).real (eventOfTrace E U) ≤
      setBer((Set.univ : Set ι), p).real (eventOfTrace E T ∩ eventOfTrace E U) := by
  rw [← integral_observableOfFiniteTrace_indicator_setBernoulli E T p,
    ← integral_observableOfFiniteTrace_indicator_setBernoulli E U p,
    ← integral_observableOfFiniteTrace_indicator_mul_setBernoulli E T U p]
  exact setBernoulli_integral_fkg_observableOfFiniteTrace (E := E) (p := p)
    hT.indicator_isIncreasingFinsetFunction hU.indicator_isIncreasingFinsetFunction

/-- FKG/Harris inequality for decreasing finite-trace cylinder events, derived through the
lifted-observable form. -/
theorem setBernoulli_real_fkg_eventOfTrace_of_decreasing {ι : Type*}
    [DecidableEq ι] {E : Finset ι} {T U : Set (Finset ι)} (p : I)
    (hT : IsDecreasingTrace E T) (hU : IsDecreasingTrace E U) :
    setBer((Set.univ : Set ι), p).real (eventOfTrace E T) *
        setBer((Set.univ : Set ι), p).real (eventOfTrace E U) ≤
      setBer((Set.univ : Set ι), p).real (eventOfTrace E T ∩ eventOfTrace E U) := by
  rw [← integral_observableOfFiniteTrace_indicator_setBernoulli E T p,
    ← integral_observableOfFiniteTrace_indicator_setBernoulli E U p,
    ← integral_observableOfFiniteTrace_indicator_mul_setBernoulli E T U p]
  exact setBernoulli_integral_fkg_of_decreasing_observableOfFiniteTrace (E := E) (p := p)
    hT.indicator_isDecreasingFinsetFunction hU.indicator_isDecreasingFinsetFunction

/-- Negative correlation for an increasing and a decreasing finite-trace cylinder event, derived
through the lifted-observable form. -/
theorem setBernoulli_real_le_mul_eventOfTrace_of_increasing_decreasing
    {ι : Type*} [DecidableEq ι] {E : Finset ι} {T U : Set (Finset ι)} (p : I)
    (hT : IsIncreasingTrace E T) (hU : IsDecreasingTrace E U) :
    setBer((Set.univ : Set ι), p).real (eventOfTrace E T ∩ eventOfTrace E U) ≤
      setBer((Set.univ : Set ι), p).real (eventOfTrace E T) *
        setBer((Set.univ : Set ι), p).real (eventOfTrace E U) := by
  rw [← integral_observableOfFiniteTrace_indicator_setBernoulli E T p,
    ← integral_observableOfFiniteTrace_indicator_setBernoulli E U p,
    ← integral_observableOfFiniteTrace_indicator_mul_setBernoulli E T U p]
  exact setBernoulli_integral_le_mul_of_increasing_decreasing_observableOfFiniteTrace
    (E := E) (p := p) hT.indicator_isIncreasingFinsetFunction
    hU.indicator_isDecreasingFinsetFunction

/-- FKG/Harris inequality on a finite Bernoulli product space, stated without explicit
finite-support hypotheses because every event depends on the full finite coordinate set. -/
theorem setBernoulli_real_fkg_finite {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Set (Set ι)} (p : I)
    (hAinc : IsIncreasingEvent A) (hBinc : IsIncreasingEvent B) :
    setBer((Set.univ : Set ι), p).real A *
        setBer((Set.univ : Set ι), p).real B ≤
      setBer((Set.univ : Set ι), p).real (A ∩ B) :=
  setBernoulli_real_fkg_of_dependsOn p hAinc hBinc dependsOn_univ dependsOn_univ

/-- FKG/Harris inequality for two decreasing events on a finite Bernoulli product space. -/
theorem setBernoulli_real_fkg_of_decreasing_finite {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Set (Set ι)} (p : I)
    (hAdec : IsDecreasingEvent A) (hBdec : IsDecreasingEvent B) :
    setBer((Set.univ : Set ι), p).real A *
        setBer((Set.univ : Set ι), p).real B ≤
      setBer((Set.univ : Set ι), p).real (A ∩ B) :=
  setBernoulli_real_fkg_of_decreasing_dependsOn p hAdec hBdec dependsOn_univ dependsOn_univ

/-- Negative correlation between an increasing and a decreasing event on a finite Bernoulli
product space. -/
theorem setBernoulli_real_le_mul_of_increasing_decreasing_finite {ι : Type*}
    [Fintype ι] [DecidableEq ι] {A B : Set (Set ι)} (p : I)
    (hAinc : IsIncreasingEvent A) (hBdec : IsDecreasingEvent B) :
    setBer((Set.univ : Set ι), p).real (A ∩ B) ≤
      setBer((Set.univ : Set ι), p).real A *
        setBer((Set.univ : Set ι), p).real B :=
  setBernoulli_real_le_mul_of_increasing_decreasing_dependsOn p hAinc hBdec
    dependsOn_univ dependsOn_univ

/-- FKG/Harris inequality for increasing observables on a finite Bernoulli product space. -/
theorem setBernoulli_integral_fkg_finite {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X Y : Set ι → ℝ} (p : I)
    (hXinc : IsIncreasingRandomVariable X) (hYinc : IsIncreasingRandomVariable Y) :
    (∫ ω, X ω ∂setBer((Set.univ : Set ι), p)) *
        (∫ ω, Y ω ∂setBer((Set.univ : Set ι), p)) ≤
      ∫ ω, X ω * Y ω ∂setBer((Set.univ : Set ι), p) :=
  setBernoulli_integral_fkg_of_dependsOnFunction p hXinc hYinc
    dependsOnFunction_univ dependsOnFunction_univ

/-- FKG/Harris inequality for decreasing observables on a finite Bernoulli product space. -/
theorem setBernoulli_integral_fkg_of_decreasing_finite {ι : Type*}
    [Fintype ι] [DecidableEq ι] {X Y : Set ι → ℝ} (p : I)
    (hXdec : ∀ ⦃ω η : Set ι⦄, ω ⊆ η → X η ≤ X ω)
    (hYdec : ∀ ⦃ω η : Set ι⦄, ω ⊆ η → Y η ≤ Y ω) :
    (∫ ω, X ω ∂setBer((Set.univ : Set ι), p)) *
        (∫ ω, Y ω ∂setBer((Set.univ : Set ι), p)) ≤
      ∫ ω, X ω * Y ω ∂setBer((Set.univ : Set ι), p) :=
  setBernoulli_integral_fkg_of_decreasing_dependsOnFunction p hXdec hYdec
    dependsOnFunction_univ dependsOnFunction_univ

/-- Negative correlation for an increasing and a decreasing observable on a finite Bernoulli
product space. -/
theorem setBernoulli_integral_le_mul_of_increasing_decreasing_finite {ι : Type*}
    [Fintype ι] [DecidableEq ι] {X Y : Set ι → ℝ} (p : I)
    (hXinc : IsIncreasingRandomVariable X)
    (hYdec : ∀ ⦃ω η : Set ι⦄, ω ⊆ η → Y η ≤ Y ω) :
    (∫ ω, X ω * Y ω ∂setBer((Set.univ : Set ι), p)) ≤
      (∫ ω, X ω ∂setBer((Set.univ : Set ι), p)) *
        (∫ ω, Y ω ∂setBer((Set.univ : Set ι), p)) :=
  setBernoulli_integral_le_mul_of_increasing_decreasing_dependsOnFunction p hXinc hYdec
    dependsOnFunction_univ dependsOnFunction_univ

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

/-- Iterated FKG on a finite Bernoulli product space, stated without explicit finite-support
hypotheses. -/
theorem setBernoulli_real_iterated_fkg_finite {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [DecidableEq κ] {J : Finset κ}
    {A : κ → Set (Set ι)} (p : I)
    (hAinc : ∀ i ∈ J, IsIncreasingEvent (A i)) :
    J.prod (fun i ↦ setBer((Set.univ : Set ι), p).real (A i)) ≤
      setBer((Set.univ : Set ι), p).real (finiteEventInter J A) :=
  setBernoulli_real_iterated_fkg_of_dependsOn
    (E := fun _ : κ ↦ (Finset.univ : Finset ι)) p hAinc fun _ _ ↦ dependsOn_univ

/-- Pass a product inequality through limits of real sequences. This is the analytic skeleton of
Grimmett's martingale/limit step after the finite-coordinate FKG proof. -/
theorem mul_le_of_tendsto_atTop_of_forall_le {x y z : ℕ → ℝ} {a b c : ℝ}
    (hx : Filter.Tendsto x Filter.atTop (nhds a))
    (hy : Filter.Tendsto y Filter.atTop (nhds b))
    (hz : Filter.Tendsto z Filter.atTop (nhds c))
    (hxyz : ∀ n, x n * y n ≤ z n) :
    a * b ≤ c :=
  le_of_tendsto_of_tendsto' (hx.mul hy) hz hxyz

/-- Pass a reverse product inequality through limits of real sequences. This is the analytic
version used for increasing/decreasing negative association. -/
theorem le_mul_of_tendsto_atTop_of_forall_le {x y z : ℕ → ℝ} {a b c : ℝ}
    (hx : Filter.Tendsto x Filter.atTop (nhds a))
    (hy : Filter.Tendsto y Filter.atTop (nhds b))
    (hz : Filter.Tendsto z Filter.atTop (nhds c))
    (hxyz : ∀ n, z n ≤ x n * y n) :
    c ≤ a * b :=
  le_of_tendsto_of_tendsto' hz (hx.mul hy) hxyz

/-- FKG passes from finite-support increasing approximations to their probability limits. This is
the theorem-facing limit bridge for Grimmett's full FKG theorem: the remaining source-specific
work is to construct approximants and prove the three convergence hypotheses. -/
theorem setBernoulli_real_fkg_of_finiteSupport_tendsto {ι : Type*} [DecidableEq ι]
    (p : I) {A B : Set (Set ι)}
    {Aapprox Bapprox : ℕ → Set (Set ι)}
    {EA EB : ℕ → Finset ι}
    (hAinc : ∀ n, IsIncreasingEvent (Aapprox n))
    (hBinc : ∀ n, IsIncreasingEvent (Bapprox n))
    (hAdep : ∀ n, DependsOn (EA n) (Aapprox n))
    (hBdep : ∀ n, DependsOn (EB n) (Bapprox n))
    (hAtend : Filter.Tendsto
      (fun n ↦ setBer((Set.univ : Set ι), p).real (Aapprox n)) Filter.atTop
      (nhds (setBer((Set.univ : Set ι), p).real A)))
    (hBtend : Filter.Tendsto
      (fun n ↦ setBer((Set.univ : Set ι), p).real (Bapprox n)) Filter.atTop
      (nhds (setBer((Set.univ : Set ι), p).real B)))
    (hABtend : Filter.Tendsto
      (fun n ↦ setBer((Set.univ : Set ι), p).real (Aapprox n ∩ Bapprox n)) Filter.atTop
      (nhds (setBer((Set.univ : Set ι), p).real (A ∩ B)))) :
    setBer((Set.univ : Set ι), p).real A *
        setBer((Set.univ : Set ι), p).real B ≤
      setBer((Set.univ : Set ι), p).real (A ∩ B) := by
  exact mul_le_of_tendsto_atTop_of_forall_le hAtend hBtend hABtend fun n ↦
    setBernoulli_real_fkg_of_dependsOn p (hAinc n) (hBinc n) (hAdep n) (hBdep n)

/-- Decreasing-event FKG passes from finite-support decreasing approximations to their probability
limits. -/
theorem setBernoulli_real_fkg_of_decreasing_finiteSupport_tendsto {ι : Type*}
    [DecidableEq ι] (p : I) {A B : Set (Set ι)}
    {Aapprox Bapprox : ℕ → Set (Set ι)}
    {EA EB : ℕ → Finset ι}
    (hAdec : ∀ n, IsDecreasingEvent (Aapprox n))
    (hBdec : ∀ n, IsDecreasingEvent (Bapprox n))
    (hAdep : ∀ n, DependsOn (EA n) (Aapprox n))
    (hBdep : ∀ n, DependsOn (EB n) (Bapprox n))
    (hAtend : Filter.Tendsto
      (fun n ↦ setBer((Set.univ : Set ι), p).real (Aapprox n)) Filter.atTop
      (nhds (setBer((Set.univ : Set ι), p).real A)))
    (hBtend : Filter.Tendsto
      (fun n ↦ setBer((Set.univ : Set ι), p).real (Bapprox n)) Filter.atTop
      (nhds (setBer((Set.univ : Set ι), p).real B)))
    (hABtend : Filter.Tendsto
      (fun n ↦ setBer((Set.univ : Set ι), p).real (Aapprox n ∩ Bapprox n)) Filter.atTop
      (nhds (setBer((Set.univ : Set ι), p).real (A ∩ B)))) :
    setBer((Set.univ : Set ι), p).real A *
        setBer((Set.univ : Set ι), p).real B ≤
      setBer((Set.univ : Set ι), p).real (A ∩ B) := by
  exact mul_le_of_tendsto_atTop_of_forall_le hAtend hBtend hABtend fun n ↦
    setBernoulli_real_fkg_of_decreasing_dependsOn p
      (hAdec n) (hBdec n) (hAdep n) (hBdep n)

/-- Negative association for an increasing event and a decreasing event passes from finite-support
approximations to their probability limits. -/
theorem setBernoulli_real_le_mul_of_increasing_decreasing_finiteSupport_tendsto
    {ι : Type*} [DecidableEq ι] (p : I) {A B : Set (Set ι)}
    {Aapprox Bapprox : ℕ → Set (Set ι)}
    {EA EB : ℕ → Finset ι}
    (hAinc : ∀ n, IsIncreasingEvent (Aapprox n))
    (hBdec : ∀ n, IsDecreasingEvent (Bapprox n))
    (hAdep : ∀ n, DependsOn (EA n) (Aapprox n))
    (hBdep : ∀ n, DependsOn (EB n) (Bapprox n))
    (hAtend : Filter.Tendsto
      (fun n ↦ setBer((Set.univ : Set ι), p).real (Aapprox n)) Filter.atTop
      (nhds (setBer((Set.univ : Set ι), p).real A)))
    (hBtend : Filter.Tendsto
      (fun n ↦ setBer((Set.univ : Set ι), p).real (Bapprox n)) Filter.atTop
      (nhds (setBer((Set.univ : Set ι), p).real B)))
    (hABtend : Filter.Tendsto
      (fun n ↦ setBer((Set.univ : Set ι), p).real (Aapprox n ∩ Bapprox n)) Filter.atTop
      (nhds (setBer((Set.univ : Set ι), p).real (A ∩ B)))) :
    setBer((Set.univ : Set ι), p).real (A ∩ B) ≤
      setBer((Set.univ : Set ι), p).real A *
        setBer((Set.univ : Set ι), p).real B := by
  exact le_mul_of_tendsto_atTop_of_forall_le hAtend hBtend hABtend fun n ↦
    setBernoulli_real_le_mul_of_increasing_decreasing_dependsOn p
      (hAinc n) (hBdec n) (hAdep n) (hBdep n)

/-- FKG passes from finite-support increasing observable approximations to their integral
limits. This is the observable-facing limit bridge for Grimmett's martingale step: the remaining
source-specific work is to construct finite-coordinate approximants and prove the three
convergence hypotheses. -/
theorem setBernoulli_integral_fkg_of_finiteSupport_tendsto {ι : Type*} [DecidableEq ι]
    (p : I) {X Y : Set ι → ℝ}
    {Xapprox Yapprox : ℕ → Set ι → ℝ}
    {EX EY : ℕ → Finset ι}
    (hXinc : ∀ n, IsIncreasingRandomVariable (Xapprox n))
    (hYinc : ∀ n, IsIncreasingRandomVariable (Yapprox n))
    (hXdep : ∀ n, DependsOnFunction (EX n) (Xapprox n))
    (hYdep : ∀ n, DependsOnFunction (EY n) (Yapprox n))
    (hXtend : Filter.Tendsto
      (fun n ↦ ∫ ω, Xapprox n ω ∂setBer((Set.univ : Set ι), p)) Filter.atTop
      (nhds (∫ ω, X ω ∂setBer((Set.univ : Set ι), p))))
    (hYtend : Filter.Tendsto
      (fun n ↦ ∫ ω, Yapprox n ω ∂setBer((Set.univ : Set ι), p)) Filter.atTop
      (nhds (∫ ω, Y ω ∂setBer((Set.univ : Set ι), p))))
    (hXYtend : Filter.Tendsto
      (fun n ↦ ∫ ω, Xapprox n ω * Yapprox n ω ∂setBer((Set.univ : Set ι), p))
        Filter.atTop
      (nhds (∫ ω, X ω * Y ω ∂setBer((Set.univ : Set ι), p)))) :
    (∫ ω, X ω ∂setBer((Set.univ : Set ι), p)) *
        (∫ ω, Y ω ∂setBer((Set.univ : Set ι), p)) ≤
      ∫ ω, X ω * Y ω ∂setBer((Set.univ : Set ι), p) := by
  exact mul_le_of_tendsto_atTop_of_forall_le hXtend hYtend hXYtend fun n ↦
    setBernoulli_integral_fkg_of_dependsOnFunction p
      (hXinc n) (hYinc n) (hXdep n) (hYdep n)

/-- Decreasing-observable FKG passes from finite-support decreasing approximations to their
integral limits. -/
theorem setBernoulli_integral_fkg_of_decreasing_finiteSupport_tendsto {ι : Type*}
    [DecidableEq ι] (p : I) {X Y : Set ι → ℝ}
    {Xapprox Yapprox : ℕ → Set ι → ℝ}
    {EX EY : ℕ → Finset ι}
    (hXdec : ∀ n, ∀ ⦃ω η : Set ι⦄, ω ⊆ η → Xapprox n η ≤ Xapprox n ω)
    (hYdec : ∀ n, ∀ ⦃ω η : Set ι⦄, ω ⊆ η → Yapprox n η ≤ Yapprox n ω)
    (hXdep : ∀ n, DependsOnFunction (EX n) (Xapprox n))
    (hYdep : ∀ n, DependsOnFunction (EY n) (Yapprox n))
    (hXtend : Filter.Tendsto
      (fun n ↦ ∫ ω, Xapprox n ω ∂setBer((Set.univ : Set ι), p)) Filter.atTop
      (nhds (∫ ω, X ω ∂setBer((Set.univ : Set ι), p))))
    (hYtend : Filter.Tendsto
      (fun n ↦ ∫ ω, Yapprox n ω ∂setBer((Set.univ : Set ι), p)) Filter.atTop
      (nhds (∫ ω, Y ω ∂setBer((Set.univ : Set ι), p))))
    (hXYtend : Filter.Tendsto
      (fun n ↦ ∫ ω, Xapprox n ω * Yapprox n ω ∂setBer((Set.univ : Set ι), p))
        Filter.atTop
      (nhds (∫ ω, X ω * Y ω ∂setBer((Set.univ : Set ι), p)))) :
    (∫ ω, X ω ∂setBer((Set.univ : Set ι), p)) *
        (∫ ω, Y ω ∂setBer((Set.univ : Set ι), p)) ≤
      ∫ ω, X ω * Y ω ∂setBer((Set.univ : Set ι), p) := by
  exact mul_le_of_tendsto_atTop_of_forall_le hXtend hYtend hXYtend fun n ↦
    setBernoulli_integral_fkg_of_decreasing_dependsOnFunction p
      (hXdec n) (hYdec n) (hXdep n) (hYdep n)

/-- Negative association for an increasing observable and a decreasing observable passes from
finite-support approximations to their integral limits. -/
theorem setBernoulli_integral_le_mul_of_increasing_decreasing_finiteSupport_tendsto
    {ι : Type*} [DecidableEq ι] (p : I) {X Y : Set ι → ℝ}
    {Xapprox Yapprox : ℕ → Set ι → ℝ}
    {EX EY : ℕ → Finset ι}
    (hXinc : ∀ n, IsIncreasingRandomVariable (Xapprox n))
    (hYdec : ∀ n, ∀ ⦃ω η : Set ι⦄, ω ⊆ η → Yapprox n η ≤ Yapprox n ω)
    (hXdep : ∀ n, DependsOnFunction (EX n) (Xapprox n))
    (hYdep : ∀ n, DependsOnFunction (EY n) (Yapprox n))
    (hXtend : Filter.Tendsto
      (fun n ↦ ∫ ω, Xapprox n ω ∂setBer((Set.univ : Set ι), p)) Filter.atTop
      (nhds (∫ ω, X ω ∂setBer((Set.univ : Set ι), p))))
    (hYtend : Filter.Tendsto
      (fun n ↦ ∫ ω, Yapprox n ω ∂setBer((Set.univ : Set ι), p)) Filter.atTop
      (nhds (∫ ω, Y ω ∂setBer((Set.univ : Set ι), p))))
    (hXYtend : Filter.Tendsto
      (fun n ↦ ∫ ω, Xapprox n ω * Yapprox n ω ∂setBer((Set.univ : Set ι), p))
        Filter.atTop
      (nhds (∫ ω, X ω * Y ω ∂setBer((Set.univ : Set ι), p)))) :
    (∫ ω, X ω * Y ω ∂setBer((Set.univ : Set ι), p)) ≤
      (∫ ω, X ω ∂setBer((Set.univ : Set ι), p)) *
        (∫ ω, Y ω ∂setBer((Set.univ : Set ι), p)) := by
  exact le_mul_of_tendsto_atTop_of_forall_le hXtend hYtend hXYtend fun n ↦
    setBernoulli_integral_le_mul_of_increasing_decreasing_dependsOnFunction p
      (hXinc n) (hYdec n) (hXdep n) (hYdep n)

/-- FKG for events from lifted finite-coordinate observable approximants. This is the
martingale-facing bridge for the full measurable-event theorem: conditional expectations of
event indicators should supply the monotone finite-cube functions and the three convergence
hypotheses. -/
theorem setBernoulli_real_fkg_of_observableOfFiniteTrace_tendsto
    {ι : Type*} [DecidableEq ι] (p : I) {A B : Set (Set ι)}
    {EX EY : ℕ → Finset ι} {X Y : ℕ → Finset ι → ℝ}
    (hXinc : ∀ n, IsIncreasingFinsetFunction (EX n) (X n))
    (hYinc : ∀ n, IsIncreasingFinsetFunction (EY n) (Y n))
    (hXtend : Filter.Tendsto
      (fun n ↦
        ∫ ω, observableOfFiniteTrace (EX n) (X n) ω
          ∂setBer((Set.univ : Set ι), p)) Filter.atTop
      (nhds (setBer((Set.univ : Set ι), p).real A)))
    (hYtend : Filter.Tendsto
      (fun n ↦
        ∫ ω, observableOfFiniteTrace (EY n) (Y n) ω
          ∂setBer((Set.univ : Set ι), p)) Filter.atTop
      (nhds (setBer((Set.univ : Set ι), p).real B)))
    (hXYtend : Filter.Tendsto
      (fun n ↦
        ∫ ω,
          observableOfFiniteTrace (EX n) (X n) ω *
            observableOfFiniteTrace (EY n) (Y n) ω
          ∂setBer((Set.univ : Set ι), p)) Filter.atTop
      (nhds (setBer((Set.univ : Set ι), p).real (A ∩ B)))) :
    setBer((Set.univ : Set ι), p).real A *
        setBer((Set.univ : Set ι), p).real B ≤
      setBer((Set.univ : Set ι), p).real (A ∩ B) := by
  exact mul_le_of_tendsto_atTop_of_forall_le hXtend hYtend hXYtend fun n ↦
    setBernoulli_integral_fkg_of_dependsOnFunction p
      (hXinc n).observableOfFiniteTrace (hYinc n).observableOfFiniteTrace
      (dependsOnFunction_observableOfFiniteTrace (EX n) (X n))
      (dependsOnFunction_observableOfFiniteTrace (EY n) (Y n))

/-- Conditional-probability martingale form of the measurable-event FKG bridge. Once the
conditional probabilities along an exhausting finite trace have the standard three convergence
properties, the full FKG inequality follows from the finite conditional-probability step. -/
theorem setBernoulli_real_fkg_of_finiteTraceConditionalProbability_tendsto
    {ι : Type*} [DecidableEq ι] (p : I) {A B : Set (Set ι)}
    {E : ℕ → Finset ι}
    (hAinc : IsIncreasingEvent A) (hBinc : IsIncreasingEvent B)
    (hAtend : Filter.Tendsto
      (fun n ↦
        ∫ ω,
          observableOfFiniteTrace (E n) (finiteTraceConditionalProbability (E n) p A) ω
          ∂setBer((Set.univ : Set ι), p)) Filter.atTop
      (nhds (setBer((Set.univ : Set ι), p).real A)))
    (hBtend : Filter.Tendsto
      (fun n ↦
        ∫ ω,
          observableOfFiniteTrace (E n) (finiteTraceConditionalProbability (E n) p B) ω
          ∂setBer((Set.univ : Set ι), p)) Filter.atTop
      (nhds (setBer((Set.univ : Set ι), p).real B)))
    (hABtend : Filter.Tendsto
      (fun n ↦
        ∫ ω,
          observableOfFiniteTrace (E n) (finiteTraceConditionalProbability (E n) p A) ω *
            observableOfFiniteTrace (E n) (finiteTraceConditionalProbability (E n) p B) ω
          ∂setBer((Set.univ : Set ι), p)) Filter.atTop
      (nhds (setBer((Set.univ : Set ι), p).real (A ∩ B)))) :
    setBer((Set.univ : Set ι), p).real A *
        setBer((Set.univ : Set ι), p).real B ≤
      setBer((Set.univ : Set ι), p).real (A ∩ B) := by
  exact setBernoulli_real_fkg_of_observableOfFiniteTrace_tendsto
    (p := p) (A := A) (B := B) (EX := E) (EY := E)
    (X := fun n ↦ finiteTraceConditionalProbability (E n) p A)
    (Y := fun n ↦ finiteTraceConditionalProbability (E n) p B)
    (fun n ↦ finiteTraceConditionalProbability_isIncreasingFinsetFunction (E := E n) p hAinc)
    (fun n ↦ finiteTraceConditionalProbability_isIncreasingFinsetFunction (E := E n) p hBinc)
    hAtend hBtend hABtend

/-- L¹ convergence of real-valued approximants to an event indicator implies convergence of
their integrals to the event probability. This is the analytic form used to turn martingale
convergence into the probability convergence hypotheses in the FKG bridge. -/
theorem tendsto_integral_indicator_of_eLpNorm_tendsto {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {A : Set Ω} (hA : MeasurableSet A)
    {F : ℕ → Ω → ℝ}
    (hFint : ∀ᶠ n in Filter.atTop, Integrable (F n) μ)
    (hFL1 : Filter.Tendsto
      (fun n ↦ eLpNorm (F n - fun ω ↦ A.indicator (fun _ ↦ (1 : ℝ)) ω) 1 μ)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n ↦ ∫ ω, F n ω ∂μ) Filter.atTop
      (nhds (μ.real A)) := by
  have hAesm : AEStronglyMeasurable (fun ω ↦ A.indicator (fun _ ↦ (1 : ℝ)) ω) μ :=
    (measurable_const.indicator hA).aestronglyMeasurable
  have h := tendsto_integral_of_L1'
    (f := fun ω ↦ A.indicator (fun _ ↦ (1 : ℝ)) ω)
    hAesm hFint hFL1
  have hlim :
      (∫ ω, A.indicator (fun _ ↦ (1 : ℝ)) ω ∂μ) = μ.real A := by
    simpa using (integral_indicator_one (μ := μ) hA)
  simpa [hlim] using h

/-- Bounded L¹ convergence is stable under multiplying two event-indicator approximants. If
`Fₙ → 1_A` and `Gₙ → 1_B` in L¹ and `0 ≤ Fₙ ≤ 1`, then `FₙGₙ → 1_{A∩B}` in L¹. This is the
analytic product estimate needed in Grimmett's martingale proof of FKG. -/
theorem tendsto_eLpNorm_mul_indicator_inter_of_bounded
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {A B : Set Ω} (hAmeas : MeasurableSet A) (hBmeas : MeasurableSet B)
    {F G : ℕ → Ω → ℝ}
    (hFint : ∀ n, Integrable (F n) μ) (hGint : ∀ n, Integrable (G n) μ)
    (hF0 : ∀ n ω, 0 ≤ F n ω) (hF1 : ∀ n ω, F n ω ≤ 1)
    (hFL1 : Filter.Tendsto
      (fun n ↦ eLpNorm (F n - fun ω ↦ A.indicator (fun _ ↦ (1 : ℝ)) ω) 1 μ)
      Filter.atTop (nhds 0))
    (hGL1 : Filter.Tendsto
      (fun n ↦ eLpNorm (G n - fun ω ↦ B.indicator (fun _ ↦ (1 : ℝ)) ω) 1 μ)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun n ↦
        eLpNorm
          ((fun ω ↦ F n ω * G n ω) -
            fun ω ↦ (A ∩ B).indicator (fun _ ↦ (1 : ℝ)) ω)
          1 μ)
      Filter.atTop (nhds 0) := by
  have hAint : Integrable (fun ω ↦ A.indicator (fun _ ↦ (1 : ℝ)) ω) μ :=
    (integrable_const (1 : ℝ)).indicator hAmeas
  have hBint : Integrable (fun ω ↦ B.indicator (fun _ ↦ (1 : ℝ)) ω) μ :=
    (integrable_const (1 : ℝ)).indicator hBmeas
  have hprod_le : ∀ n,
      eLpNorm
          ((fun ω ↦ F n ω * G n ω) -
            fun ω ↦ (A ∩ B).indicator (fun _ ↦ (1 : ℝ)) ω)
          1 μ ≤
        eLpNorm (F n - fun ω ↦ A.indicator (fun _ ↦ (1 : ℝ)) ω) 1 μ +
          eLpNorm (G n - fun ω ↦ B.indicator (fun _ ↦ (1 : ℝ)) ω) 1 μ := by
    intro n
    let X : Ω → ℝ := F n - fun ω ↦ A.indicator (fun _ ↦ (1 : ℝ)) ω
    let Y : Ω → ℝ := G n - fun ω ↦ B.indicator (fun _ ↦ (1 : ℝ)) ω
    have hmono :
        eLpNorm
            ((fun ω ↦ F n ω * G n ω) -
              fun ω ↦ (A ∩ B).indicator (fun _ ↦ (1 : ℝ)) ω)
            1 μ ≤
          eLpNorm (fun ω ↦ ‖X ω‖ + ‖Y ω‖) 1 μ := by
      refine eLpNorm_mono_ae_real (ae_of_all μ fun ω ↦ ?_)
      dsimp [X, Y]
      let a : ℝ := A.indicator (fun _ ↦ (1 : ℝ)) ω
      let b : ℝ := B.indicator (fun _ ↦ (1 : ℝ)) ω
      have hInter : (A ∩ B).indicator (fun _ ↦ (1 : ℝ)) ω = a * b := by
        by_cases hωA : ω ∈ A <;> by_cases hωB : ω ∈ B <;>
          simp [a, b, hωA, hωB]
      have hFnorm : ‖F n ω‖ ≤ 1 := by
        rw [Real.norm_eq_abs, abs_of_nonneg (hF0 n ω)]
        exact hF1 n ω
      have hbnorm : ‖b‖ ≤ 1 := by
        by_cases hωB : ω ∈ B
        · simp [b, hωB]
        · simp [b, hωB]
      calc
        ‖F n ω * G n ω - (A ∩ B).indicator (fun _ ↦ (1 : ℝ)) ω‖ =
            ‖F n ω * (G n ω - b) + b * (F n ω - a)‖ := by
          rw [hInter]
          ring_nf
        _ ≤ ‖F n ω * (G n ω - b)‖ + ‖b * (F n ω - a)‖ := norm_add_le _ _
        _ = ‖F n ω‖ * ‖G n ω - b‖ + ‖b‖ * ‖F n ω - a‖ := by
          rw [norm_mul, norm_mul]
        _ ≤ 1 * ‖G n ω - b‖ + 1 * ‖F n ω - a‖ := by
          have h1 := mul_le_mul_of_nonneg_right hFnorm (norm_nonneg (G n ω - b))
          have h2 := mul_le_mul_of_nonneg_right hbnorm (norm_nonneg (F n ω - a))
          nlinarith
        _ = ‖F n ω - a‖ + ‖G n ω - b‖ := by
          ring
    have hsum :
        eLpNorm (fun ω ↦ ‖X ω‖ + ‖Y ω‖) 1 μ ≤
          eLpNorm (F n - fun ω ↦ A.indicator (fun _ ↦ (1 : ℝ)) ω) 1 μ +
            eLpNorm (G n - fun ω ↦ B.indicator (fun _ ↦ (1 : ℝ)) ω) 1 μ := by
      have hXesm : AEStronglyMeasurable X μ :=
        (hFint n).aestronglyMeasurable.sub hAint.aestronglyMeasurable
      have hYesm : AEStronglyMeasurable Y μ :=
        (hGint n).aestronglyMeasurable.sub hBint.aestronglyMeasurable
      have h := eLpNorm_add_le (μ := μ) (p := (1 : ℝ≥0∞)) hXesm.norm hYesm.norm le_rfl
      rw [← eLpNorm_norm (F n - fun ω ↦ A.indicator (fun _ ↦ (1 : ℝ)) ω),
        ← eLpNorm_norm (G n - fun ω ↦ B.indicator (fun _ ↦ (1 : ℝ)) ω)]
      change eLpNorm ((fun ω ↦ ‖X ω‖) + fun ω ↦ ‖Y ω‖) 1 μ ≤
        eLpNorm (fun ω ↦ ‖X ω‖) 1 μ + eLpNorm (fun ω ↦ ‖Y ω‖) 1 μ
      simpa using h
    exact hmono.trans hsum
  have hsum_tend : Filter.Tendsto
      (fun n ↦ eLpNorm (F n - fun ω ↦ A.indicator (fun _ ↦ (1 : ℝ)) ω) 1 μ +
        eLpNorm (G n - fun ω ↦ B.indicator (fun _ ↦ (1 : ℝ)) ω) 1 μ)
      Filter.atTop (nhds (0 + 0)) := hFL1.add hGL1
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ ?_ hprod_le
  · simpa using hsum_tend
  · intro n
    exact zero_le

/-- Conditional-probability martingale form of FKG with L¹ convergence hypotheses. The
finite-trace conditional probabilities are the monotone finite-cube observables; if they converge
in L¹ to the two indicators and their products converge in L¹ to the intersection indicator, then
the full event FKG inequality follows. -/
theorem setBernoulli_real_fkg_of_finiteTraceConditionalProbability_eLpNorm_tendsto
    {ι : Type*} [DecidableEq ι] (p : I) {A B : Set (Set ι)}
    {E : ℕ → Finset ι}
    (hAmeas : MeasurableSet A) (hBmeas : MeasurableSet B)
    (hAinc : IsIncreasingEvent A) (hBinc : IsIncreasingEvent B)
    (hAL1 : Filter.Tendsto
      (fun n ↦
        eLpNorm
          ((fun ω : Set ι ↦
              observableOfFiniteTrace (E n) (finiteTraceConditionalProbability (E n) p A) ω) -
            fun ω ↦ A.indicator (fun _ ↦ (1 : ℝ)) ω)
          1 (setBer((Set.univ : Set ι), p)))
      Filter.atTop (nhds 0))
    (hBL1 : Filter.Tendsto
      (fun n ↦
        eLpNorm
          ((fun ω : Set ι ↦
              observableOfFiniteTrace (E n) (finiteTraceConditionalProbability (E n) p B) ω) -
            fun ω ↦ B.indicator (fun _ ↦ (1 : ℝ)) ω)
          1 (setBer((Set.univ : Set ι), p)))
      Filter.atTop (nhds 0))
    (hABL1 : Filter.Tendsto
      (fun n ↦
        eLpNorm
          ((fun ω : Set ι ↦
              observableOfFiniteTrace (E n) (finiteTraceConditionalProbability (E n) p A) ω *
                observableOfFiniteTrace (E n) (finiteTraceConditionalProbability (E n) p B) ω) -
            fun ω ↦ (A ∩ B).indicator (fun _ ↦ (1 : ℝ)) ω)
          1 (setBer((Set.univ : Set ι), p)))
      Filter.atTop (nhds 0)) :
    setBer((Set.univ : Set ι), p).real A *
        setBer((Set.univ : Set ι), p).real B ≤
      setBer((Set.univ : Set ι), p).real (A ∩ B) := by
  let μ := setBer((Set.univ : Set ι), p)
  have hAint : Filter.Tendsto
      (fun n ↦
        ∫ ω,
          observableOfFiniteTrace (E n) (finiteTraceConditionalProbability (E n) p A) ω ∂μ)
      Filter.atTop (nhds (μ.real A)) := by
    refine tendsto_integral_indicator_of_eLpNorm_tendsto (μ := μ) hAmeas ?_ ?_
    · exact Filter.Eventually.of_forall fun n ↦
        (dependsOnFunction_observableOfFiniteTrace (E n)
          (finiteTraceConditionalProbability (E n) p A)).integrable_setBernoulli p
    · simpa [μ] using hAL1
  have hBint : Filter.Tendsto
      (fun n ↦
        ∫ ω,
          observableOfFiniteTrace (E n) (finiteTraceConditionalProbability (E n) p B) ω ∂μ)
      Filter.atTop (nhds (μ.real B)) := by
    refine tendsto_integral_indicator_of_eLpNorm_tendsto (μ := μ) hBmeas ?_ ?_
    · exact Filter.Eventually.of_forall fun n ↦
        (dependsOnFunction_observableOfFiniteTrace (E n)
          (finiteTraceConditionalProbability (E n) p B)).integrable_setBernoulli p
    · simpa [μ] using hBL1
  have hABint : Filter.Tendsto
      (fun n ↦
        ∫ ω,
          observableOfFiniteTrace (E n) (finiteTraceConditionalProbability (E n) p A) ω *
            observableOfFiniteTrace (E n) (finiteTraceConditionalProbability (E n) p B) ω ∂μ)
      Filter.atTop (nhds (μ.real (A ∩ B))) := by
    refine tendsto_integral_indicator_of_eLpNorm_tendsto (μ := μ) (hAmeas.inter hBmeas) ?_ ?_
    · exact Filter.Eventually.of_forall fun n ↦
        ((dependsOnFunction_observableOfFiniteTrace (E n)
          (finiteTraceConditionalProbability (E n) p A)).mul
          (dependsOnFunction_observableOfFiniteTrace (E n)
            (finiteTraceConditionalProbability (E n) p B))).integrable_setBernoulli p
    · simpa [μ] using hABL1
  exact setBernoulli_real_fkg_of_finiteTraceConditionalProbability_tendsto
    (p := p) (A := A) (B := B) (E := E) hAinc hBinc
    (by simpa [μ] using hAint)
    (by simpa [μ] using hBint)
    (by simpa [μ] using hABint)

/-- Conditional-expectation version of the finite-trace FKG bridge. Once the finite-trace
conditional probabilities are identified as versions of the conditional expectations along an
exhausting finite-trace filtration, Mathlib's L¹ martingale convergence theorem supplies the
single-event convergence hypotheses automatically. The product L¹ convergence is kept explicit;
it is the remaining analytic estimate needed to turn the conditional-expectation bridge into a
fully closed arbitrary-event FKG theorem. -/
theorem setBernoulli_real_fkg_of_finiteTraceConditionalProbability_condExp
    {ι : Type*} [DecidableEq ι] (p : I) {A B : Set (Set ι)}
    {E : ℕ → Finset ι} (hE : Monotone E)
    (hcover : ∀ e : ι, ∀ᶠ n in Filter.atTop, e ∈ E n)
    (hAmeas : MeasurableSet A) (hBmeas : MeasurableSet B)
    (hAinc : IsIncreasingEvent A) (hBinc : IsIncreasingEvent B)
    (hAcond : ∀ n,
      (fun ω : Set ι ↦
        observableOfFiniteTrace (E n) (finiteTraceConditionalProbability (E n) p A) ω) =ᵐ[
          setBer((Set.univ : Set ι), p)]
        setBer((Set.univ : Set ι), p)[fun ω ↦ A.indicator (fun _ ↦ (1 : ℝ)) ω |
          (finiteTraceFiltration E hE) n])
    (hBcond : ∀ n,
      (fun ω : Set ι ↦
        observableOfFiniteTrace (E n) (finiteTraceConditionalProbability (E n) p B) ω) =ᵐ[
          setBer((Set.univ : Set ι), p)]
        setBer((Set.univ : Set ι), p)[fun ω ↦ B.indicator (fun _ ↦ (1 : ℝ)) ω |
          (finiteTraceFiltration E hE) n])
    (hABL1 : Filter.Tendsto
      (fun n ↦
        eLpNorm
          ((fun ω : Set ι ↦
              observableOfFiniteTrace (E n) (finiteTraceConditionalProbability (E n) p A) ω *
                observableOfFiniteTrace (E n) (finiteTraceConditionalProbability (E n) p B) ω) -
            fun ω ↦ (A ∩ B).indicator (fun _ ↦ (1 : ℝ)) ω)
          1 (setBer((Set.univ : Set ι), p)))
      Filter.atTop (nhds 0)) :
    setBer((Set.univ : Set ι), p).real A *
        setBer((Set.univ : Set ι), p).real B ≤
      setBer((Set.univ : Set ι), p).real (A ∩ B) := by
  let μ := setBer((Set.univ : Set ι), p)
  have hAcondL1 := tendsto_eLpNorm_condExp_indicator_finiteTraceFiltration_of_eventually_mem
    (p := p) hE hcover hAmeas
  have hBcondL1 := tendsto_eLpNorm_condExp_indicator_finiteTraceFiltration_of_eventually_mem
    (p := p) hE hcover hBmeas
  have hAL1 : Filter.Tendsto
      (fun n ↦
        eLpNorm
          ((fun ω : Set ι ↦
              observableOfFiniteTrace (E n) (finiteTraceConditionalProbability (E n) p A) ω) -
            fun ω ↦ A.indicator (fun _ ↦ (1 : ℝ)) ω)
          1 μ)
      Filter.atTop (nhds 0) := by
    refine hAcondL1.congr' ?_
    exact Filter.Eventually.of_forall fun n ↦ eLpNorm_congr_ae (by
      filter_upwards [hAcond n] with ω hω
      simp only [Pi.sub_apply]
      rw [← hω])
  have hBL1 : Filter.Tendsto
      (fun n ↦
        eLpNorm
          ((fun ω : Set ι ↦
              observableOfFiniteTrace (E n) (finiteTraceConditionalProbability (E n) p B) ω) -
            fun ω ↦ B.indicator (fun _ ↦ (1 : ℝ)) ω)
          1 μ)
      Filter.atTop (nhds 0) := by
    refine hBcondL1.congr' ?_
    exact Filter.Eventually.of_forall fun n ↦ eLpNorm_congr_ae (by
      filter_upwards [hBcond n] with ω hω
      simp only [Pi.sub_apply]
      rw [← hω])
  exact setBernoulli_real_fkg_of_finiteTraceConditionalProbability_eLpNorm_tendsto
    (p := p) (A := A) (B := B) (E := E) hAmeas hBmeas hAinc hBinc
    (by simpa [μ] using hAL1) (by simpa [μ] using hBL1) (by simpa [μ] using hABL1)

/-- Closed conditional-expectation version of the finite-trace FKG bridge. Once the
finite-trace conditional probabilities are identified as versions of the conditional expectations
along an exhausting finite-trace filtration, Mathlib's L¹ martingale convergence theorem supplies
the two single-event convergence hypotheses, and bounded product convergence supplies the
intersection convergence hypothesis. -/
theorem setBernoulli_real_fkg_of_finiteTraceConditionalProbability_condExp_of_eventually_mem
    {ι : Type*} [DecidableEq ι] (p : I) {A B : Set (Set ι)}
    {E : ℕ → Finset ι} (hE : Monotone E)
    (hcover : ∀ e : ι, ∀ᶠ n in Filter.atTop, e ∈ E n)
    (hAmeas : MeasurableSet A) (hBmeas : MeasurableSet B)
    (hAinc : IsIncreasingEvent A) (hBinc : IsIncreasingEvent B)
    (hAcond : ∀ n,
      (fun ω : Set ι ↦
        observableOfFiniteTrace (E n) (finiteTraceConditionalProbability (E n) p A) ω) =ᵐ[
          setBer((Set.univ : Set ι), p)]
        setBer((Set.univ : Set ι), p)[fun ω ↦ A.indicator (fun _ ↦ (1 : ℝ)) ω |
          (finiteTraceFiltration E hE) n])
    (hBcond : ∀ n,
      (fun ω : Set ι ↦
        observableOfFiniteTrace (E n) (finiteTraceConditionalProbability (E n) p B) ω) =ᵐ[
          setBer((Set.univ : Set ι), p)]
        setBer((Set.univ : Set ι), p)[fun ω ↦ B.indicator (fun _ ↦ (1 : ℝ)) ω |
          (finiteTraceFiltration E hE) n]) :
    setBer((Set.univ : Set ι), p).real A *
        setBer((Set.univ : Set ι), p).real B ≤
      setBer((Set.univ : Set ι), p).real (A ∩ B) := by
  let μ := setBer((Set.univ : Set ι), p)
  have hAcondL1 := tendsto_eLpNorm_condExp_indicator_finiteTraceFiltration_of_eventually_mem
    (p := p) hE hcover hAmeas
  have hBcondL1 := tendsto_eLpNorm_condExp_indicator_finiteTraceFiltration_of_eventually_mem
    (p := p) hE hcover hBmeas
  have hAL1 : Filter.Tendsto
      (fun n ↦
        eLpNorm
          ((fun ω : Set ι ↦
              observableOfFiniteTrace (E n) (finiteTraceConditionalProbability (E n) p A) ω) -
            fun ω ↦ A.indicator (fun _ ↦ (1 : ℝ)) ω)
          1 μ)
      Filter.atTop (nhds 0) := by
    refine hAcondL1.congr' ?_
    exact Filter.Eventually.of_forall fun n ↦ eLpNorm_congr_ae (by
      filter_upwards [hAcond n] with ω hω
      simp only [Pi.sub_apply]
      rw [← hω])
  have hBL1 : Filter.Tendsto
      (fun n ↦
        eLpNorm
          ((fun ω : Set ι ↦
              observableOfFiniteTrace (E n) (finiteTraceConditionalProbability (E n) p B) ω) -
            fun ω ↦ B.indicator (fun _ ↦ (1 : ℝ)) ω)
          1 μ)
      Filter.atTop (nhds 0) := by
    refine hBcondL1.congr' ?_
    exact Filter.Eventually.of_forall fun n ↦ eLpNorm_congr_ae (by
      filter_upwards [hBcond n] with ω hω
      simp only [Pi.sub_apply]
      rw [← hω])
  have hFint : ∀ n, Integrable
      (fun ω : Set ι ↦
        observableOfFiniteTrace (E n) (finiteTraceConditionalProbability (E n) p A) ω) μ := by
    intro n
    simpa [μ] using
      (dependsOnFunction_observableOfFiniteTrace (E n)
        (finiteTraceConditionalProbability (E n) p A)).integrable_setBernoulli p
  have hGint : ∀ n, Integrable
      (fun ω : Set ι ↦
        observableOfFiniteTrace (E n) (finiteTraceConditionalProbability (E n) p B) ω) μ := by
    intro n
    simpa [μ] using
      (dependsOnFunction_observableOfFiniteTrace (E n)
        (finiteTraceConditionalProbability (E n) p B)).integrable_setBernoulli p
  have hF0 : ∀ n (ω : Set ι),
      0 ≤ observableOfFiniteTrace (E n) (finiteTraceConditionalProbability (E n) p A) ω := by
    intro n ω
    exact observableOfFiniteTrace_finiteTraceConditionalProbability_nonneg (E n) p A ω
  have hF1 : ∀ n (ω : Set ι),
      observableOfFiniteTrace (E n) (finiteTraceConditionalProbability (E n) p A) ω ≤ 1 := by
    intro n ω
    exact observableOfFiniteTrace_finiteTraceConditionalProbability_le_one (E n) p A ω
  have hABL1 : Filter.Tendsto
      (fun n ↦
        eLpNorm
          ((fun ω : Set ι ↦
              observableOfFiniteTrace (E n) (finiteTraceConditionalProbability (E n) p A) ω *
                observableOfFiniteTrace (E n) (finiteTraceConditionalProbability (E n) p B) ω) -
            fun ω ↦ (A ∩ B).indicator (fun _ ↦ (1 : ℝ)) ω)
          1 μ)
      Filter.atTop (nhds 0) := by
    exact tendsto_eLpNorm_mul_indicator_inter_of_bounded
      (μ := μ) (A := A) (B := B)
      (F := fun n (ω : Set ι) ↦
        observableOfFiniteTrace (E n) (finiteTraceConditionalProbability (E n) p A) ω)
      (G := fun n (ω : Set ι) ↦
        observableOfFiniteTrace (E n) (finiteTraceConditionalProbability (E n) p B) ω)
      hAmeas hBmeas hFint hGint hF0 hF1 hAL1 hBL1
  exact setBernoulli_real_fkg_of_finiteTraceConditionalProbability_condExp
    (p := p) (A := A) (B := B) (E := E) hE hcover hAmeas hBmeas hAinc hBinc
    hAcond hBcond (by simpa [μ] using hABL1)

/-- Full measurable-event FKG/Harris inequality along an exhausting finite-coordinate
filtration. This closes Grimmett's martingale limiting step for any coordinate space equipped with
a monotone finite exhaustion. -/
theorem setBernoulli_real_fkg_of_finiteTraceFiltration
    {ι : Type*} [DecidableEq ι] (p : I) {A B : Set (Set ι)}
    {E : ℕ → Finset ι} (hE : Monotone E)
    (hcover : ∀ e : ι, ∀ᶠ n in Filter.atTop, e ∈ E n)
    (hAmeas : MeasurableSet A) (hBmeas : MeasurableSet B)
    (hAinc : IsIncreasingEvent A) (hBinc : IsIncreasingEvent B) :
    setBer((Set.univ : Set ι), p).real A *
        setBer((Set.univ : Set ι), p).real B ≤
      setBer((Set.univ : Set ι), p).real (A ∩ B) := by
  refine setBernoulli_real_fkg_of_finiteTraceConditionalProbability_condExp_of_eventually_mem
    (p := p) (A := A) (B := B) (E := E) hE hcover hAmeas hBmeas hAinc hBinc ?_ ?_
  · intro n
    simpa [finiteTraceFiltration] using
      finiteTraceConditionalProbability_ae_eq_condExp (E n) p hAmeas
  · intro n
    simpa [finiteTraceFiltration] using
      finiteTraceConditionalProbability_ae_eq_condExp (E n) p hBmeas

/-- Full measurable-event FKG/Harris inequality for two decreasing events along an exhausting
finite-coordinate filtration. This is the decreasing/decreasing companion to
`setBernoulli_real_fkg_of_finiteTraceFiltration`. -/
theorem setBernoulli_real_fkg_of_decreasing_finiteTraceFiltration
    {ι : Type*} [DecidableEq ι] (p : I) {A B : Set (Set ι)}
    {E : ℕ → Finset ι} (hE : Monotone E)
    (hcover : ∀ e : ι, ∀ᶠ n in Filter.atTop, e ∈ E n)
    (hAmeas : MeasurableSet A) (hBmeas : MeasurableSet B)
    (hAdec : IsDecreasingEvent A) (hBdec : IsDecreasingEvent B) :
    setBer((Set.univ : Set ι), p).real A *
        setBer((Set.univ : Set ι), p).real B ≤
      setBer((Set.univ : Set ι), p).real (A ∩ B) := by
  let μ := setBer((Set.univ : Set ι), p)
  have hcomp := setBernoulli_real_fkg_of_finiteTraceFiltration
    (p := p) (A := Aᶜ) (B := Bᶜ) (E := E) hE hcover hAmeas.compl hBmeas.compl
    hAdec hBdec
  have hAcomp : μ.real Aᶜ = 1 - μ.real A := by
    rw [measureReal_compl (μ := μ) hAmeas]
    simp [μ]
  have hBcomp : μ.real Bᶜ = 1 - μ.real B := by
    rw [measureReal_compl (μ := μ) hBmeas]
    simp [μ]
  have hABcomp : μ.real (Aᶜ ∩ Bᶜ) = 1 - μ.real (A ∪ B) := by
    have hset : Aᶜ ∩ Bᶜ = (A ∪ B)ᶜ := by
      ext ω
      simp
    rw [hset, measureReal_compl (μ := μ) (hAmeas.union hBmeas)]
    simp [μ]
  have hunion : μ.real (A ∪ B) + μ.real (A ∩ B) = μ.real A + μ.real B :=
    measureReal_union_add_inter (μ := μ) (s := A) (t := B) hBmeas
  have hcomp' : (1 - μ.real A) * (1 - μ.real B) ≤ 1 - μ.real (A ∪ B) := by
    simpa [μ, hAcomp, hBcomp, hABcomp] using hcomp
  nlinarith

/-- Full measurable-event negative association for an increasing event and a decreasing event
along an exhausting finite-coordinate filtration. -/
theorem setBernoulli_real_le_mul_of_increasing_decreasing_finiteTraceFiltration
    {ι : Type*} [DecidableEq ι] (p : I) {A B : Set (Set ι)}
    {E : ℕ → Finset ι} (hE : Monotone E)
    (hcover : ∀ e : ι, ∀ᶠ n in Filter.atTop, e ∈ E n)
    (hAmeas : MeasurableSet A) (hBmeas : MeasurableSet B)
    (hAinc : IsIncreasingEvent A) (hBdec : IsDecreasingEvent B) :
    setBer((Set.univ : Set ι), p).real (A ∩ B) ≤
      setBer((Set.univ : Set ι), p).real A *
        setBer((Set.univ : Set ι), p).real B := by
  let μ := setBer((Set.univ : Set ι), p)
  have hcomp := setBernoulli_real_fkg_of_finiteTraceFiltration
    (p := p) (A := A) (B := Bᶜ) (E := E) hE hcover hAmeas hBmeas.compl hAinc hBdec
  have hBcomp : μ.real Bᶜ = 1 - μ.real B := by
    rw [measureReal_compl (μ := μ) hBmeas]
    simp [μ]
  have hdisj : Disjoint (A ∩ Bᶜ) (A ∩ B) := by
    rw [Set.disjoint_left]
    intro ω hωc hω
    exact hωc.2 hω.2
  have hunion : (A ∩ Bᶜ) ∪ (A ∩ B) = A := by
    ext ω
    by_cases hωA : ω ∈ A <;> by_cases hωB : ω ∈ B <;> simp [hωA, hωB]
  have hsum : μ.real (A ∩ Bᶜ) + μ.real (A ∩ B) = μ.real A := by
    have h := measureReal_union (μ := μ) (s₁ := A ∩ Bᶜ) (s₂ := A ∩ B) hdisj
      (hAmeas.inter hBmeas)
    rw [hunion] at h
    exact h.symm
  have hcomp' : μ.real A * (1 - μ.real B) ≤ μ.real (A ∩ Bᶜ) := by
    simpa [μ, hBcomp] using hcomp
  nlinarith

/-- Grimmett's iterated FKG inequality (2.7) for a finite family of arbitrary measurable
increasing events along an exhausting finite-coordinate filtration. -/
theorem setBernoulli_real_iterated_fkg_of_finiteTraceFiltration
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] (p : I) {J : Finset κ}
    {A : κ → Set (Set ι)}
    {E : ℕ → Finset ι} (hE : Monotone E)
    (hcover : ∀ e : ι, ∀ᶠ n in Filter.atTop, e ∈ E n)
    (hAmeas : ∀ i ∈ J, MeasurableSet (A i))
    (hAinc : ∀ i ∈ J, IsIncreasingEvent (A i)) :
    J.prod (fun i ↦ setBer((Set.univ : Set ι), p).real (A i)) ≤
      setBer((Set.univ : Set ι), p).real (finiteEventInter J A) := by
  let μ : Measure (Set ι) := setBer((Set.univ : Set ι), p)
  revert hAmeas hAinc
  refine Finset.induction_on J ?_ ?_
  · intro hAmeas hAinc
    simp [finiteEventInter]
  · intro a J ha ih hAmeas hAinc
    have hAameas : MeasurableSet (A a) :=
      hAmeas a (Finset.mem_insert_self a J)
    have hAainc : IsIncreasingEvent (A a) :=
      hAinc a (Finset.mem_insert_self a J)
    have hJmeas : ∀ i ∈ J, MeasurableSet (A i) := by
      intro i hi
      exact hAmeas i (Finset.mem_insert.mpr (Or.inr hi))
    have hJinc : ∀ i ∈ J, IsIncreasingEvent (A i) := by
      intro i hi
      exact hAinc i (Finset.mem_insert.mpr (Or.inr hi))
    have hind :
        J.prod (fun i ↦ μ.real (A i)) ≤ μ.real (finiteEventInter J A) := by
      simpa [μ] using ih hJmeas hJinc
    have hInterMeas : MeasurableSet (finiteEventInter J A) :=
      measurableSet_finiteEventInter hJmeas
    have hInterInc : IsIncreasingEvent (finiteEventInter J A) :=
      isIncreasingEvent_finiteEventInter hJinc
    have hstep :
        μ.real (A a) * μ.real (finiteEventInter J A) ≤
          μ.real (A a ∩ finiteEventInter J A) := by
      simpa [μ] using
        setBernoulli_real_fkg_of_finiteTraceFiltration
          (p := p) (A := A a) (B := finiteEventInter J A) (E := E)
          hE hcover hAameas hInterMeas hAainc hInterInc
    have hprod :
        μ.real (A a) * J.prod (fun i ↦ μ.real (A i)) ≤
          μ.real (A a) * μ.real (finiteEventInter J A) :=
      mul_le_mul_of_nonneg_left hind measureReal_nonneg
    calc
      (insert a J).prod (fun i ↦ μ.real (A i)) =
          μ.real (A a) * J.prod (fun i ↦ μ.real (A i)) := by
        rw [Finset.prod_insert ha]
      _ ≤ μ.real (A a) * μ.real (finiteEventInter J A) := hprod
      _ ≤ μ.real (A a ∩ finiteEventInter J A) := hstep
      _ = μ.real (finiteEventInter (insert a J) A) := by
        rw [finiteEventInter_insert]

/-- Decreasing-event conditional-probability form of the measurable-event FKG bridge. -/
theorem setBernoulli_real_fkg_of_decreasing_finiteTraceConditionalProbability_tendsto
    {ι : Type*} [DecidableEq ι] (p : I) {A B : Set (Set ι)}
    {E : ℕ → Finset ι}
    (hAdec : IsDecreasingEvent A) (hBdec : IsDecreasingEvent B)
    (hAtend : Filter.Tendsto
      (fun n ↦
        ∫ ω,
          observableOfFiniteTrace (E n) (finiteTraceConditionalProbability (E n) p A) ω
          ∂setBer((Set.univ : Set ι), p)) Filter.atTop
      (nhds (setBer((Set.univ : Set ι), p).real A)))
    (hBtend : Filter.Tendsto
      (fun n ↦
        ∫ ω,
          observableOfFiniteTrace (E n) (finiteTraceConditionalProbability (E n) p B) ω
          ∂setBer((Set.univ : Set ι), p)) Filter.atTop
      (nhds (setBer((Set.univ : Set ι), p).real B)))
    (hABtend : Filter.Tendsto
      (fun n ↦
        ∫ ω,
          observableOfFiniteTrace (E n) (finiteTraceConditionalProbability (E n) p A) ω *
            observableOfFiniteTrace (E n) (finiteTraceConditionalProbability (E n) p B) ω
          ∂setBer((Set.univ : Set ι), p)) Filter.atTop
      (nhds (setBer((Set.univ : Set ι), p).real (A ∩ B)))) :
    setBer((Set.univ : Set ι), p).real A *
        setBer((Set.univ : Set ι), p).real B ≤
      setBer((Set.univ : Set ι), p).real (A ∩ B) := by
  exact mul_le_of_tendsto_atTop_of_forall_le hAtend hBtend hABtend fun n ↦
    setBernoulli_integral_fkg_of_decreasing_observableOfFiniteTrace (E := E n) (p := p)
      (finiteTraceConditionalProbability_isDecreasingFinsetFunction (E := E n) p hAdec)
      (finiteTraceConditionalProbability_isDecreasingFinsetFunction (E := E n) p hBdec)

/-- Increasing/decreasing conditional-probability form of the negative-association bridge. -/
theorem setBernoulli_real_le_mul_of_finiteTraceConditionalProbability_tendsto
    {ι : Type*} [DecidableEq ι] (p : I) {A B : Set (Set ι)}
    {E : ℕ → Finset ι}
    (hAinc : IsIncreasingEvent A) (hBdec : IsDecreasingEvent B)
    (hAtend : Filter.Tendsto
      (fun n ↦
        ∫ ω,
          observableOfFiniteTrace (E n) (finiteTraceConditionalProbability (E n) p A) ω
          ∂setBer((Set.univ : Set ι), p)) Filter.atTop
      (nhds (setBer((Set.univ : Set ι), p).real A)))
    (hBtend : Filter.Tendsto
      (fun n ↦
        ∫ ω,
          observableOfFiniteTrace (E n) (finiteTraceConditionalProbability (E n) p B) ω
          ∂setBer((Set.univ : Set ι), p)) Filter.atTop
      (nhds (setBer((Set.univ : Set ι), p).real B)))
    (hABtend : Filter.Tendsto
      (fun n ↦
        ∫ ω,
          observableOfFiniteTrace (E n) (finiteTraceConditionalProbability (E n) p A) ω *
            observableOfFiniteTrace (E n) (finiteTraceConditionalProbability (E n) p B) ω
          ∂setBer((Set.univ : Set ι), p)) Filter.atTop
      (nhds (setBer((Set.univ : Set ι), p).real (A ∩ B)))) :
    setBer((Set.univ : Set ι), p).real (A ∩ B) ≤
      setBer((Set.univ : Set ι), p).real A *
        setBer((Set.univ : Set ι), p).real B := by
  exact le_mul_of_tendsto_atTop_of_forall_le hAtend hBtend hABtend fun n ↦
    setBernoulli_integral_le_mul_of_increasing_decreasing_observableOfFiniteTrace
      (E := E n) (p := p)
      (finiteTraceConditionalProbability_isIncreasingFinsetFunction (E := E n) p hAinc)
      (finiteTraceConditionalProbability_isDecreasingFinsetFunction (E := E n) p hBdec)

/-- Finite-support FKG recovered through the conditional-probability martingale bridge whenever
the conditioning supports eventually contain the two finite event supports. This theorem is
redundant with `setBernoulli_real_fkg_of_dependsOn`, but records the source-facing route used in
the full measurable-event proof. -/
theorem setBernoulli_real_fkg_of_finiteTraceConditionalProbability_eventually_dependsOn
    {ι : Type*} [DecidableEq ι] (p : I) {A B : Set (Set ι)}
    {Eseq : ℕ → Finset ι} {FA FB : Finset ι}
    (hAinc : IsIncreasingEvent A) (hBinc : IsIncreasingEvent B)
    (hAdep : DependsOn FA A) (hBdep : DependsOn FB B)
    (hFAE : ∀ᶠ n in Filter.atTop, FA ⊆ Eseq n)
    (hFBE : ∀ᶠ n in Filter.atTop, FB ⊆ Eseq n) :
    setBer((Set.univ : Set ι), p).real A *
        setBer((Set.univ : Set ι), p).real B ≤
      setBer((Set.univ : Set ι), p).real (A ∩ B) := by
  exact setBernoulli_real_fkg_of_finiteTraceConditionalProbability_tendsto
    (p := p) (A := A) (B := B) (E := Eseq) hAinc hBinc
    (tendsto_integral_finiteTraceConditionalProbability_of_eventually_dependsOn hAdep hFAE p)
    (tendsto_integral_finiteTraceConditionalProbability_of_eventually_dependsOn hBdep hFBE p)
    (tendsto_integral_finiteTraceConditionalProbability_mul_of_eventually_dependsOn
      hAdep hBdep hFAE hFBE p)

/-- Decreasing-event finite-support FKG through the conditional-probability bridge. -/
theorem setBernoulli_real_fkg_of_decreasing_finiteTraceConditionalProbability_eventually_dependsOn
    {ι : Type*} [DecidableEq ι] (p : I) {A B : Set (Set ι)}
    {Eseq : ℕ → Finset ι} {FA FB : Finset ι}
    (hAdec : IsDecreasingEvent A) (hBdec : IsDecreasingEvent B)
    (hAdep : DependsOn FA A) (hBdep : DependsOn FB B)
    (hFAE : ∀ᶠ n in Filter.atTop, FA ⊆ Eseq n)
    (hFBE : ∀ᶠ n in Filter.atTop, FB ⊆ Eseq n) :
    setBer((Set.univ : Set ι), p).real A *
        setBer((Set.univ : Set ι), p).real B ≤
      setBer((Set.univ : Set ι), p).real (A ∩ B) := by
  exact setBernoulli_real_fkg_of_decreasing_finiteTraceConditionalProbability_tendsto
    (p := p) (A := A) (B := B) (E := Eseq) hAdec hBdec
    (tendsto_integral_finiteTraceConditionalProbability_of_eventually_dependsOn hAdep hFAE p)
    (tendsto_integral_finiteTraceConditionalProbability_of_eventually_dependsOn hBdep hFBE p)
    (tendsto_integral_finiteTraceConditionalProbability_mul_of_eventually_dependsOn
      hAdep hBdep hFAE hFBE p)

/-- Increasing/decreasing finite-support negative association through the
conditional-probability bridge. -/
theorem setBernoulli_real_le_mul_of_finiteTraceConditionalProbability_eventually_dependsOn
    {ι : Type*} [DecidableEq ι] (p : I) {A B : Set (Set ι)}
    {Eseq : ℕ → Finset ι} {FA FB : Finset ι}
    (hAinc : IsIncreasingEvent A) (hBdec : IsDecreasingEvent B)
    (hAdep : DependsOn FA A) (hBdep : DependsOn FB B)
    (hFAE : ∀ᶠ n in Filter.atTop, FA ⊆ Eseq n)
    (hFBE : ∀ᶠ n in Filter.atTop, FB ⊆ Eseq n) :
    setBer((Set.univ : Set ι), p).real (A ∩ B) ≤
      setBer((Set.univ : Set ι), p).real A *
        setBer((Set.univ : Set ι), p).real B := by
  exact setBernoulli_real_le_mul_of_finiteTraceConditionalProbability_tendsto
    (p := p) (A := A) (B := B) (E := Eseq) hAinc hBdec
    (tendsto_integral_finiteTraceConditionalProbability_of_eventually_dependsOn hAdep hFAE p)
    (tendsto_integral_finiteTraceConditionalProbability_of_eventually_dependsOn hBdep hFBE p)
    (tendsto_integral_finiteTraceConditionalProbability_mul_of_eventually_dependsOn
      hAdep hBdep hFAE hFBE p)

/-- Under a Dirac probability measure, event FKG is automatic for measurable events. This is the
endpoint input for the Bernoulli parameters `p = 0` and `p = 1`. -/
theorem dirac_real_fkg {Ω : Type*} [MeasurableSpace Ω] (ω : Ω)
    {A B : Set Ω} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    (Measure.dirac ω).real A * (Measure.dirac ω).real B ≤
      (Measure.dirac ω).real (A ∩ B) := by
  rw [Measure.real, Measure.real, Measure.real]
  rw [Measure.dirac_apply' ω hA, Measure.dirac_apply' ω hB,
    Measure.dirac_apply' ω (hA.inter hB)]
  by_cases hωA : ω ∈ A <;> by_cases hωB : ω ∈ B <;> simp [hωA, hωB]

/-- FKG at Bernoulli parameter `p = 0`, where the product measure is a Dirac mass at the empty
configuration. -/
theorem setBernoulli_real_fkg_zero {ι : Type*} {A B : Set (Set ι)}
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    setBer((Set.univ : Set ι), (0 : I)).real A *
        setBer((Set.univ : Set ι), (0 : I)).real B ≤
      setBer((Set.univ : Set ι), (0 : I)).real (A ∩ B) := by
  rw [setBernoulli_zero]
  exact dirac_real_fkg ∅ hA hB

/-- FKG at Bernoulli parameter `p = 1`, where the product measure is a Dirac mass at the full
configuration. -/
theorem setBernoulli_real_fkg_one {ι : Type*} {A B : Set (Set ι)}
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    setBer((Set.univ : Set ι), (1 : I)).real A *
        setBer((Set.univ : Set ι), (1 : I)).real B ≤
      setBer((Set.univ : Set ι), (1 : I)).real (A ∩ B) := by
  rw [setBernoulli_one]
  exact dirac_real_fkg Set.univ hA hB

/-- If finite-measure events converge in symmetric-difference measure, their real probabilities
converge. This is the measure-continuity input used to turn finite-support approximations into
the probability convergence hypotheses of the FKG limit bridge. -/
theorem tendsto_measureReal_of_tendsto_measureReal_symmDiff {Ω : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {A : Set Ω} {Aapprox : ℕ → Set Ω}
    (hA : NullMeasurableSet A μ) (hAapprox : ∀ n, NullMeasurableSet (Aapprox n) μ)
    (hΔ : Filter.Tendsto (fun n ↦ μ.real (Aapprox n ∆ A)) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n ↦ μ.real (Aapprox n)) Filter.atTop (nhds (μ.real A)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Filter.Eventually.of_forall fun n ↦ norm_nonneg _) ?_ hΔ
  exact Filter.Eventually.of_forall fun n ↦ by
    simpa [Real.norm_eq_abs] using
      abs_measureReal_sub_le_measureReal_symmDiff (μ := μ) (s := Aapprox n) (t := A)
        (hAapprox n) hA

/-- Symmetric difference of intersections is controlled by the union of the two component
symmetric differences. -/
theorem symmDiff_inter_subset_union_symmDiff {Ω : Type*}
    (A A' B B' : Set Ω) :
    (A ∩ B) ∆ (A' ∩ B') ⊆ (A ∆ A') ∪ (B ∆ B') := by
  intro ω hω
  simp [Set.symmDiff_def] at hω ⊢
  tauto

/-- Real measure form of `symmDiff_inter_subset_union_symmDiff`. -/
theorem measureReal_symmDiff_inter_le_add {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (A A' B B' : Set Ω) :
    μ.real ((A ∩ B) ∆ (A' ∩ B')) ≤ μ.real (A ∆ A') + μ.real (B ∆ B') := by
  exact (measureReal_mono (symmDiff_inter_subset_union_symmDiff A A' B B'))
    |>.trans (measureReal_union_le (A ∆ A') (B ∆ B'))

/-- If two event approximations converge in symmetric-difference measure, then their
intersections converge in symmetric-difference measure. -/
theorem tendsto_measureReal_symmDiff_inter {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {A B : Set Ω}
    {Aapprox Bapprox : ℕ → Set Ω}
    (hAΔ : Filter.Tendsto (fun n ↦ μ.real (Aapprox n ∆ A)) Filter.atTop (nhds 0))
    (hBΔ : Filter.Tendsto (fun n ↦ μ.real (Bapprox n ∆ B)) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n ↦ μ.real ((Aapprox n ∩ Bapprox n) ∆ (A ∩ B)))
      Filter.atTop (nhds 0) := by
  have hsum : Filter.Tendsto
      (fun n ↦ μ.real (Aapprox n ∆ A) + μ.real (Bapprox n ∆ B))
      Filter.atTop (nhds 0) := by
    simpa using hAΔ.add hBΔ
  refine squeeze_zero' (Filter.Eventually.of_forall fun _n ↦ measureReal_nonneg) ?_ hsum
  exact Filter.Eventually.of_forall fun n ↦
    measureReal_symmDiff_inter_le_add μ (Aapprox n) A (Bapprox n) B

/-- FKG for increasing events obtained from finite-support increasing approximations converging in
symmetric-difference measure. This packages the three probability-convergence hypotheses of
`setBernoulli_real_fkg_of_finiteSupport_tendsto` into the standard approximation topology on
events. -/
theorem setBernoulli_real_fkg_of_finiteSupport_symmDiff_tendsto {ι : Type*} [DecidableEq ι]
    (p : I) {A B : Set (Set ι)}
    {Aapprox Bapprox : ℕ → Set (Set ι)}
    {EA EB : ℕ → Finset ι}
    (hAmeas : MeasurableSet A) (hBmeas : MeasurableSet B)
    (hAinc : ∀ n, IsIncreasingEvent (Aapprox n))
    (hBinc : ∀ n, IsIncreasingEvent (Bapprox n))
    (hAdep : ∀ n, DependsOn (EA n) (Aapprox n))
    (hBdep : ∀ n, DependsOn (EB n) (Bapprox n))
    (hAΔ : Filter.Tendsto
      (fun n ↦ setBer((Set.univ : Set ι), p).real (Aapprox n ∆ A)) Filter.atTop
      (nhds 0))
    (hBΔ : Filter.Tendsto
      (fun n ↦ setBer((Set.univ : Set ι), p).real (Bapprox n ∆ B)) Filter.atTop
      (nhds 0))
    (hABΔ : Filter.Tendsto
      (fun n ↦ setBer((Set.univ : Set ι), p).real ((Aapprox n ∩ Bapprox n) ∆ (A ∩ B)))
        Filter.atTop (nhds 0)) :
    setBer((Set.univ : Set ι), p).real A *
        setBer((Set.univ : Set ι), p).real B ≤
      setBer((Set.univ : Set ι), p).real (A ∩ B) := by
  let μ : Measure (Set ι) := setBer((Set.univ : Set ι), p)
  refine setBernoulli_real_fkg_of_finiteSupport_tendsto (p := p)
    (hAinc := hAinc) (hBinc := hBinc) (hAdep := hAdep) (hBdep := hBdep) ?_ ?_ ?_
  · exact tendsto_measureReal_of_tendsto_measureReal_symmDiff
      (μ := μ) hAmeas.nullMeasurableSet
      (fun n ↦ (hAdep n).measurableSet.nullMeasurableSet) hAΔ
  · exact tendsto_measureReal_of_tendsto_measureReal_symmDiff
      (μ := μ) hBmeas.nullMeasurableSet
      (fun n ↦ (hBdep n).measurableSet.nullMeasurableSet) hBΔ
  · exact tendsto_measureReal_of_tendsto_measureReal_symmDiff
      (μ := μ) (hAmeas.inter hBmeas).nullMeasurableSet
      (fun n ↦
        (((hAdep n).mono (Finset.subset_union_left (s₁ := EA n) (s₂ := EB n))).inter
          ((hBdep n).mono (Finset.subset_union_right (s₁ := EA n) (s₂ := EB n))))
          |>.measurableSet.nullMeasurableSet)
      hABΔ

/-- FKG for increasing events from finite-support increasing approximations, with the intersection
convergence derived from the two individual symmetric-difference convergence hypotheses. -/
theorem setBernoulli_real_fkg_of_finiteSupport_symmDiff_tendsto_pair
    {ι : Type*} [DecidableEq ι] (p : I) {A B : Set (Set ι)}
    {Aapprox Bapprox : ℕ → Set (Set ι)}
    {EA EB : ℕ → Finset ι}
    (hAmeas : MeasurableSet A) (hBmeas : MeasurableSet B)
    (hAinc : ∀ n, IsIncreasingEvent (Aapprox n))
    (hBinc : ∀ n, IsIncreasingEvent (Bapprox n))
    (hAdep : ∀ n, DependsOn (EA n) (Aapprox n))
    (hBdep : ∀ n, DependsOn (EB n) (Bapprox n))
    (hAΔ : Filter.Tendsto
      (fun n ↦ setBer((Set.univ : Set ι), p).real (Aapprox n ∆ A)) Filter.atTop
      (nhds 0))
    (hBΔ : Filter.Tendsto
      (fun n ↦ setBer((Set.univ : Set ι), p).real (Bapprox n ∆ B)) Filter.atTop
      (nhds 0)) :
    setBer((Set.univ : Set ι), p).real A *
        setBer((Set.univ : Set ι), p).real B ≤
      setBer((Set.univ : Set ι), p).real (A ∩ B) := by
  exact setBernoulli_real_fkg_of_finiteSupport_symmDiff_tendsto (p := p)
    hAmeas hBmeas hAinc hBinc hAdep hBdep hAΔ hBΔ
    (tendsto_measureReal_symmDiff_inter (μ := setBer((Set.univ : Set ι), p)) hAΔ hBΔ)

/-- Decreasing-event FKG obtained from finite-support decreasing approximations converging in
symmetric-difference measure. -/
theorem setBernoulli_real_fkg_of_decreasing_finiteSupport_symmDiff_tendsto
    {ι : Type*} [DecidableEq ι] (p : I) {A B : Set (Set ι)}
    {Aapprox Bapprox : ℕ → Set (Set ι)}
    {EA EB : ℕ → Finset ι}
    (hAmeas : MeasurableSet A) (hBmeas : MeasurableSet B)
    (hAdec : ∀ n, IsDecreasingEvent (Aapprox n))
    (hBdec : ∀ n, IsDecreasingEvent (Bapprox n))
    (hAdep : ∀ n, DependsOn (EA n) (Aapprox n))
    (hBdep : ∀ n, DependsOn (EB n) (Bapprox n))
    (hAΔ : Filter.Tendsto
      (fun n ↦ setBer((Set.univ : Set ι), p).real (Aapprox n ∆ A)) Filter.atTop
      (nhds 0))
    (hBΔ : Filter.Tendsto
      (fun n ↦ setBer((Set.univ : Set ι), p).real (Bapprox n ∆ B)) Filter.atTop
      (nhds 0))
    (hABΔ : Filter.Tendsto
      (fun n ↦ setBer((Set.univ : Set ι), p).real ((Aapprox n ∩ Bapprox n) ∆ (A ∩ B)))
        Filter.atTop (nhds 0)) :
    setBer((Set.univ : Set ι), p).real A *
        setBer((Set.univ : Set ι), p).real B ≤
      setBer((Set.univ : Set ι), p).real (A ∩ B) := by
  let μ : Measure (Set ι) := setBer((Set.univ : Set ι), p)
  refine setBernoulli_real_fkg_of_decreasing_finiteSupport_tendsto (p := p)
    (hAdec := hAdec) (hBdec := hBdec) (hAdep := hAdep) (hBdep := hBdep) ?_ ?_ ?_
  · exact tendsto_measureReal_of_tendsto_measureReal_symmDiff
      (μ := μ) hAmeas.nullMeasurableSet
      (fun n ↦ (hAdep n).measurableSet.nullMeasurableSet) hAΔ
  · exact tendsto_measureReal_of_tendsto_measureReal_symmDiff
      (μ := μ) hBmeas.nullMeasurableSet
      (fun n ↦ (hBdep n).measurableSet.nullMeasurableSet) hBΔ
  · exact tendsto_measureReal_of_tendsto_measureReal_symmDiff
      (μ := μ) (hAmeas.inter hBmeas).nullMeasurableSet
      (fun n ↦
        (((hAdep n).mono (Finset.subset_union_left (s₁ := EA n) (s₂ := EB n))).inter
          ((hBdep n).mono (Finset.subset_union_right (s₁ := EA n) (s₂ := EB n))))
          |>.measurableSet.nullMeasurableSet)
      hABΔ

/-- Decreasing-event FKG from finite-support decreasing approximations, with intersection
convergence derived from the two individual symmetric-difference convergence hypotheses. -/
theorem setBernoulli_real_fkg_of_decreasing_finiteSupport_symmDiff_tendsto_pair
    {ι : Type*} [DecidableEq ι] (p : I) {A B : Set (Set ι)}
    {Aapprox Bapprox : ℕ → Set (Set ι)}
    {EA EB : ℕ → Finset ι}
    (hAmeas : MeasurableSet A) (hBmeas : MeasurableSet B)
    (hAdec : ∀ n, IsDecreasingEvent (Aapprox n))
    (hBdec : ∀ n, IsDecreasingEvent (Bapprox n))
    (hAdep : ∀ n, DependsOn (EA n) (Aapprox n))
    (hBdep : ∀ n, DependsOn (EB n) (Bapprox n))
    (hAΔ : Filter.Tendsto
      (fun n ↦ setBer((Set.univ : Set ι), p).real (Aapprox n ∆ A)) Filter.atTop
      (nhds 0))
    (hBΔ : Filter.Tendsto
      (fun n ↦ setBer((Set.univ : Set ι), p).real (Bapprox n ∆ B)) Filter.atTop
      (nhds 0)) :
    setBer((Set.univ : Set ι), p).real A *
        setBer((Set.univ : Set ι), p).real B ≤
      setBer((Set.univ : Set ι), p).real (A ∩ B) := by
  exact setBernoulli_real_fkg_of_decreasing_finiteSupport_symmDiff_tendsto (p := p)
    hAmeas hBmeas hAdec hBdec hAdep hBdep hAΔ hBΔ
    (tendsto_measureReal_symmDiff_inter (μ := setBer((Set.univ : Set ι), p)) hAΔ hBΔ)

/-- Negative association for increasing/decreasing events obtained from finite-support
approximations converging in symmetric-difference measure. -/
theorem setBernoulli_real_le_mul_of_increasing_decreasing_finiteSupport_symmDiff_tendsto
    {ι : Type*} [DecidableEq ι] (p : I) {A B : Set (Set ι)}
    {Aapprox Bapprox : ℕ → Set (Set ι)}
    {EA EB : ℕ → Finset ι}
    (hAmeas : MeasurableSet A) (hBmeas : MeasurableSet B)
    (hAinc : ∀ n, IsIncreasingEvent (Aapprox n))
    (hBdec : ∀ n, IsDecreasingEvent (Bapprox n))
    (hAdep : ∀ n, DependsOn (EA n) (Aapprox n))
    (hBdep : ∀ n, DependsOn (EB n) (Bapprox n))
    (hAΔ : Filter.Tendsto
      (fun n ↦ setBer((Set.univ : Set ι), p).real (Aapprox n ∆ A)) Filter.atTop
      (nhds 0))
    (hBΔ : Filter.Tendsto
      (fun n ↦ setBer((Set.univ : Set ι), p).real (Bapprox n ∆ B)) Filter.atTop
      (nhds 0))
    (hABΔ : Filter.Tendsto
      (fun n ↦ setBer((Set.univ : Set ι), p).real ((Aapprox n ∩ Bapprox n) ∆ (A ∩ B)))
        Filter.atTop (nhds 0)) :
    setBer((Set.univ : Set ι), p).real (A ∩ B) ≤
      setBer((Set.univ : Set ι), p).real A *
        setBer((Set.univ : Set ι), p).real B := by
  let μ : Measure (Set ι) := setBer((Set.univ : Set ι), p)
  refine setBernoulli_real_le_mul_of_increasing_decreasing_finiteSupport_tendsto (p := p)
    (hAinc := hAinc) (hBdec := hBdec) (hAdep := hAdep) (hBdep := hBdep) ?_ ?_ ?_
  · exact tendsto_measureReal_of_tendsto_measureReal_symmDiff
      (μ := μ) hAmeas.nullMeasurableSet
      (fun n ↦ (hAdep n).measurableSet.nullMeasurableSet) hAΔ
  · exact tendsto_measureReal_of_tendsto_measureReal_symmDiff
      (μ := μ) hBmeas.nullMeasurableSet
      (fun n ↦ (hBdep n).measurableSet.nullMeasurableSet) hBΔ
  · exact tendsto_measureReal_of_tendsto_measureReal_symmDiff
      (μ := μ) (hAmeas.inter hBmeas).nullMeasurableSet
      (fun n ↦
        (((hAdep n).mono (Finset.subset_union_left (s₁ := EA n) (s₂ := EB n))).inter
          ((hBdep n).mono (Finset.subset_union_right (s₁ := EA n) (s₂ := EB n))))
          |>.measurableSet.nullMeasurableSet)
      hABΔ

/-- Negative association for increasing/decreasing finite-support approximations, with intersection
convergence derived from the two individual symmetric-difference convergence hypotheses. -/
theorem setBernoulli_real_le_mul_of_increasing_decreasing_finiteSupport_symmDiff_tendsto_pair
    {ι : Type*} [DecidableEq ι] (p : I) {A B : Set (Set ι)}
    {Aapprox Bapprox : ℕ → Set (Set ι)}
    {EA EB : ℕ → Finset ι}
    (hAmeas : MeasurableSet A) (hBmeas : MeasurableSet B)
    (hAinc : ∀ n, IsIncreasingEvent (Aapprox n))
    (hBdec : ∀ n, IsDecreasingEvent (Bapprox n))
    (hAdep : ∀ n, DependsOn (EA n) (Aapprox n))
    (hBdep : ∀ n, DependsOn (EB n) (Bapprox n))
    (hAΔ : Filter.Tendsto
      (fun n ↦ setBer((Set.univ : Set ι), p).real (Aapprox n ∆ A)) Filter.atTop
      (nhds 0))
    (hBΔ : Filter.Tendsto
      (fun n ↦ setBer((Set.univ : Set ι), p).real (Bapprox n ∆ B)) Filter.atTop
      (nhds 0)) :
    setBer((Set.univ : Set ι), p).real (A ∩ B) ≤
      setBer((Set.univ : Set ι), p).real A *
        setBer((Set.univ : Set ι), p).real B := by
  exact setBernoulli_real_le_mul_of_increasing_decreasing_finiteSupport_symmDiff_tendsto
    (p := p) hAmeas hBmeas hAinc hBdec hAdep hBdep hAΔ hBΔ
    (tendsto_measureReal_symmDiff_inter (μ := setBer((Set.univ : Set ι), p)) hAΔ hBΔ)

/-- Continuity from below for real-valued finite measures. This is the `Measure.real` version of
`tendsto_measure_iUnion_atTop`, used to pass finite FKG inequalities to increasing limits. -/
theorem tendsto_measureReal_iUnion_atTop {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {A : ℕ → Set Ω} (hAmono : Monotone A) :
    Filter.Tendsto (fun n ↦ μ.real (A n)) Filter.atTop
      (nhds (μ.real (⋃ n, A n))) := by
  have h := tendsto_measure_iUnion_atTop (μ := μ) hAmono
  have hne : μ (⋃ n, A n) ≠ ∞ := by finiteness
  simpa [Measure.real, Function.comp_def] using (ENNReal.tendsto_toReal hne).comp h

/-- Continuity from above for real-valued finite measures. This is the `Measure.real` version of
`tendsto_measure_iInter_atTop`, used to pass finite FKG inequalities to decreasing limits. -/
theorem tendsto_measureReal_iInter_atTop {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {A : ℕ → Set Ω}
    (hAmeas : ∀ n, MeasurableSet (A n)) (hAanti : Antitone A) :
    Filter.Tendsto (fun n ↦ μ.real (A n)) Filter.atTop
      (nhds (μ.real (⋂ n, A n))) := by
  have h := tendsto_measure_iInter_atTop (μ := μ)
    (fun n ↦ (hAmeas n).nullMeasurableSet) hAanti ⟨0, by finiteness⟩
  have hne : μ (⋂ n, A n) ≠ ∞ := by finiteness
  simpa [Measure.real, Function.comp_def] using (ENNReal.tendsto_toReal hne).comp h

/-- FKG for increasing limits of finite-support increasing events. This is the common
continuity-from-below form of Grimmett's limiting step: each finite stage is a cylinder event,
and the target events are their increasing countable unions. -/
theorem setBernoulli_real_fkg_iUnion_finiteSupport {ι : Type*} [DecidableEq ι]
    (p : I) {A B : ℕ → Set (Set ι)} {EA EB : ℕ → Finset ι}
    (hAmono : Monotone A) (hBmono : Monotone B)
    (hAinc : ∀ n, IsIncreasingEvent (A n))
    (hBinc : ∀ n, IsIncreasingEvent (B n))
    (hAdep : ∀ n, DependsOn (EA n) (A n))
    (hBdep : ∀ n, DependsOn (EB n) (B n)) :
    setBer((Set.univ : Set ι), p).real (⋃ n, A n) *
        setBer((Set.univ : Set ι), p).real (⋃ n, B n) ≤
      setBer((Set.univ : Set ι), p).real ((⋃ n, A n) ∩ (⋃ n, B n)) := by
  let μ : Measure (Set ι) := setBer((Set.univ : Set ι), p)
  have hABmono : Monotone fun n ↦ A n ∩ B n := by
    intro n m hnm ω hω
    exact ⟨hAmono hnm hω.1, hBmono hnm hω.2⟩
  have hABUnion : (⋃ n, A n ∩ B n) = (⋃ n, A n) ∩ (⋃ n, B n) := by
    ext ω
    constructor
    · intro hω
      rcases Set.mem_iUnion.mp hω with ⟨n, hn⟩
      exact ⟨Set.mem_iUnion.mpr ⟨n, hn.1⟩, Set.mem_iUnion.mpr ⟨n, hn.2⟩⟩
    · intro hω
      rcases Set.mem_iUnion.mp hω.1 with ⟨n, hn⟩
      rcases Set.mem_iUnion.mp hω.2 with ⟨m, hm⟩
      refine Set.mem_iUnion.mpr ⟨max n m, ?_⟩
      exact ⟨hAmono (Nat.le_max_left n m) hn, hBmono (Nat.le_max_right n m) hm⟩
  refine setBernoulli_real_fkg_of_finiteSupport_tendsto (p := p)
    (A := ⋃ n, A n) (B := ⋃ n, B n) (Aapprox := A) (Bapprox := B)
    (EA := EA) (EB := EB) hAinc hBinc hAdep hBdep ?_ ?_ ?_
  · exact tendsto_measureReal_iUnion_atTop (μ := μ) hAmono
  · exact tendsto_measureReal_iUnion_atTop (μ := μ) hBmono
  · simpa [μ, hABUnion] using tendsto_measureReal_iUnion_atTop (μ := μ) hABmono

/-- FKG for decreasing limits of finite-support increasing events. This covers events such as
countable intersections of increasing cylinder events, for example "arbitrarily long open paths"
after each finite-length event has been localized. -/
theorem setBernoulli_real_fkg_iInter_finiteSupport {ι : Type*} [DecidableEq ι]
    (p : I) {A B : ℕ → Set (Set ι)} {EA EB : ℕ → Finset ι}
    (hAanti : Antitone A) (hBanti : Antitone B)
    (hAmeas : ∀ n, MeasurableSet (A n))
    (hBmeas : ∀ n, MeasurableSet (B n))
    (hAinc : ∀ n, IsIncreasingEvent (A n))
    (hBinc : ∀ n, IsIncreasingEvent (B n))
    (hAdep : ∀ n, DependsOn (EA n) (A n))
    (hBdep : ∀ n, DependsOn (EB n) (B n)) :
    setBer((Set.univ : Set ι), p).real (⋂ n, A n) *
        setBer((Set.univ : Set ι), p).real (⋂ n, B n) ≤
      setBer((Set.univ : Set ι), p).real ((⋂ n, A n) ∩ (⋂ n, B n)) := by
  let μ : Measure (Set ι) := setBer((Set.univ : Set ι), p)
  have hABanti : Antitone fun n ↦ A n ∩ B n := by
    intro n m hnm ω hω
    exact ⟨hAanti hnm hω.1, hBanti hnm hω.2⟩
  have hABmeas : ∀ n, MeasurableSet (A n ∩ B n) := fun n ↦ (hAmeas n).inter (hBmeas n)
  have hABInter : (⋂ n, A n ∩ B n) = (⋂ n, A n) ∩ (⋂ n, B n) := by
    ext ω
    simp [forall_and]
  refine setBernoulli_real_fkg_of_finiteSupport_tendsto (p := p)
    (A := ⋂ n, A n) (B := ⋂ n, B n) (Aapprox := A) (Bapprox := B)
    (EA := EA) (EB := EB) hAinc hBinc hAdep hBdep ?_ ?_ ?_
  · exact tendsto_measureReal_iInter_atTop (μ := μ) hAmeas hAanti
  · exact tendsto_measureReal_iInter_atTop (μ := μ) hBmeas hBanti
  · simpa [μ, hABInter] using tendsto_measureReal_iInter_atTop (μ := μ) hABmeas hABanti

section Cubic

theorem isIncreasingEvent_openEdgeSetEvent (d : ℕ) (s : Finset (CubicEdge d)) :
    IsIncreasingEvent (openEdgeSetEvent d s) := by
  intro ω η hωη hω
  exact Set.Subset.trans hω hωη

theorem dependsOn_openEdgeSetEvent (d : ℕ) (s : Finset (CubicEdge d)) :
    DependsOn s (openEdgeSetEvent d s) := by
  intro ω η hcoord
  constructor
  · intro hω e he
    exact (hcoord e he).mp (hω he)
  · intro hη e he
    exact (hcoord e he).mpr (hη he)

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

theorem dependsOn_walkIsOpen {d : ℕ} {u v : Cubic d}
    (w : (cubicGraph d).Walk u v) :
    DependsOn (walkEdgeFinset w) {ω : EdgeConfiguration d | walkIsOpen ω w} := by
  simpa [openEdgeSetEvent, walkIsOpen_event_eq_openOn_walkEdgeFinset w] using
    dependsOn_openEdgeSetEvent d (walkEdgeFinset w)

/-- The walk represented by a counted self-avoiding direction word, started at an arbitrary
vertex. This is the rooted finite-path family used to localize infinite-cluster events. -/
def selfAvoidingWalkWalkFrom {d n : ℕ} (x : Cubic d) (steps : SelfAvoidingWalk d n) :
    (cubicGraph d).Walk x (cubicEndpointFrom x steps.1.toList) :=
  cubicWalkFrom x steps.1.toList

@[simp]
theorem selfAvoidingWalkWalkFrom_length {d n : ℕ} (x : Cubic d)
    (steps : SelfAvoidingWalk d n) :
    (selfAvoidingWalkWalkFrom x steps).length = n := by
  simp [selfAvoidingWalkWalkFrom]

/-- The rooted graph walk represented by a counted self-avoiding direction word is a path. -/
theorem selfAvoidingWalkWalkFrom_isPath {d n : ℕ} (x : Cubic d)
    (steps : SelfAvoidingWalk d n) :
    (selfAvoidingWalkWalkFrom x steps).IsPath := by
  refine cubicWalkFrom_isPath ?_
  have htranslate :
      cubicVerticesFrom x steps.1.toList =
        (cubicVerticesFrom (cubicOrigin : Cubic d) steps.1.toList).map
          (cubicTranslate (cubicOrigin : Cubic d) x) :=
    cubicVerticesFrom_eq_map_translate (cubicOrigin : Cubic d) x steps.1.toList
  rw [htranslate]
  exact steps.2.map (cubicTranslate_injective (cubicOrigin : Cubic d) x)

/-- A counted self-avoiding direction word from a root is open in a bond configuration. -/
def selfAvoidingWalkIsOpenFrom {d n : ℕ} (x : Cubic d) (ω : EdgeConfiguration d)
    (steps : SelfAvoidingWalk d n) : Prop :=
  walkIsOpen ω (selfAvoidingWalkWalkFrom x steps)

/-- There is at least one open counted self-avoiding direction word of length `n` from `x`. -/
def existsOpenSelfAvoidingWalkFrom (d n : ℕ) (x : Cubic d)
    (ω : EdgeConfiguration d) : Prop :=
  ∃ steps : SelfAvoidingWalk d n, selfAvoidingWalkIsOpenFrom x ω steps

/-- The finite coordinate support used by all counted self-avoiding paths of length `n`
started at `x`. -/
noncomputable def selfAvoidingWalkFromSupport (d n : ℕ) (x : Cubic d) :
    Finset (CubicEdge d) :=
  Finset.univ.biUnion fun steps : SelfAvoidingWalk d n ↦
    walkEdgeFinset (selfAvoidingWalkWalkFrom x steps)

theorem walkEdgeFinset_selfAvoidingWalkWalkFrom_subset_support {d n : ℕ}
    (x : Cubic d) (steps : SelfAvoidingWalk d n) :
    walkEdgeFinset (selfAvoidingWalkWalkFrom x steps) ⊆
      selfAvoidingWalkFromSupport d n x := by
  intro e he
  classical
  exact Finset.mem_biUnion.mpr ⟨steps, Finset.mem_univ steps, he⟩

theorem isIncreasingEvent_selfAvoidingWalkIsOpenFrom {d n : ℕ}
    (x : Cubic d) (steps : SelfAvoidingWalk d n) :
    IsIncreasingEvent {ω : EdgeConfiguration d | selfAvoidingWalkIsOpenFrom x ω steps} := by
  simpa [selfAvoidingWalkIsOpenFrom] using
    isIncreasingEvent_walkIsOpen (selfAvoidingWalkWalkFrom x steps)

theorem dependsOn_selfAvoidingWalkIsOpenFrom {d n : ℕ}
    (x : Cubic d) (steps : SelfAvoidingWalk d n) :
    DependsOn (walkEdgeFinset (selfAvoidingWalkWalkFrom x steps))
      {ω : EdgeConfiguration d | selfAvoidingWalkIsOpenFrom x ω steps} := by
  simpa [selfAvoidingWalkIsOpenFrom] using
    dependsOn_walkIsOpen (selfAvoidingWalkWalkFrom x steps)

theorem isIncreasingEvent_existsOpenSelfAvoidingWalkFrom (d n : ℕ) (x : Cubic d) :
    IsIncreasingEvent {ω : EdgeConfiguration d | existsOpenSelfAvoidingWalkFrom d n x ω} := by
  intro ω η hωη hω
  rcases hω with ⟨steps, hsteps⟩
  exact ⟨steps, isIncreasingEvent_selfAvoidingWalkIsOpenFrom x steps hωη hsteps⟩

theorem dependsOn_existsOpenSelfAvoidingWalkFrom (d n : ℕ) (x : Cubic d) :
    DependsOn (selfAvoidingWalkFromSupport d n x)
      {ω : EdgeConfiguration d | existsOpenSelfAvoidingWalkFrom d n x ω} := by
  intro ω η hcoord
  constructor
  · rintro ⟨steps, hsteps⟩
    refine ⟨steps, ?_⟩
    have hdep := (dependsOn_selfAvoidingWalkIsOpenFrom x steps).mono
      (walkEdgeFinset_selfAvoidingWalkWalkFrom_subset_support x steps)
    exact (hdep hcoord).mp hsteps
  · rintro ⟨steps, hsteps⟩
    refine ⟨steps, ?_⟩
    have hdep := (dependsOn_selfAvoidingWalkIsOpenFrom x steps).mono
      (walkEdgeFinset_selfAvoidingWalkWalkFrom_subset_support x steps)
    exact (hdep hcoord).mpr hsteps

theorem hasOpenPathOfLengthExactlyFrom_imp_existsOpenSelfAvoidingWalkFrom {d n : ℕ}
    {ω : EdgeConfiguration d} {x : Cubic d} :
    hasOpenPathOfLengthExactlyFrom d ω x n → existsOpenSelfAvoidingWalkFrom d n x ω := by
  rintro ⟨v, w, hwpath, hwlen, hopen⟩
  rcases exists_cubicWalkFrom_copy_eq w with ⟨steps, hend, heq, hlen⟩
  let vec : List.Vector (CubicDirection d) n := ⟨steps, by rw [hlen, hwlen]⟩
  have hnodup : cubicVectorSelfAvoiding vec := by
    unfold cubicVectorSelfAvoiding cubicVectorVertices
    have hcopy_nodup : ((cubicWalkFrom x steps).copy rfl hend).support.Nodup := by
      rw [heq]
      exact hwpath.support_nodup
    have hxnodup : (cubicVerticesFrom x steps).Nodup := by
      simpa [SimpleGraph.Walk.support_copy, cubicWalkFrom_support] using hcopy_nodup
    have htranslate :
        cubicVerticesFrom x steps =
          (cubicVerticesFrom (cubicOrigin : Cubic d) steps).map
            (cubicTranslate (cubicOrigin : Cubic d) x) :=
      cubicVerticesFrom_eq_map_translate (cubicOrigin : Cubic d) x steps
    rw [htranslate] at hxnodup
    simpa [vec] using List.Nodup.of_map (cubicTranslate (cubicOrigin : Cubic d) x) hxnodup
  refine ⟨⟨vec, hnodup⟩, ?_⟩
  unfold selfAvoidingWalkIsOpenFrom selfAvoidingWalkWalkFrom
  intro e he
  have hcopyopen : walkIsOpen ω ((cubicWalkFrom x steps).copy rfl hend) := by
    rw [heq]
    exact hopen
  have hecopy : e ∈ ((cubicWalkFrom x steps).copy rfl hend).edges := by
    simpa [SimpleGraph.Walk.edges_copy] using he
  exact hcopyopen e hecopy

theorem existsOpenSelfAvoidingWalkFrom_imp_hasOpenPathOfLengthExactlyFrom {d n : ℕ}
    {ω : EdgeConfiguration d} {x : Cubic d} :
    existsOpenSelfAvoidingWalkFrom d n x ω → hasOpenPathOfLengthExactlyFrom d ω x n := by
  rintro ⟨steps, hopen⟩
  exact ⟨cubicEndpointFrom x steps.1.toList, selfAvoidingWalkWalkFrom x steps,
    selfAvoidingWalkWalkFrom_isPath x steps, selfAvoidingWalkWalkFrom_length x steps, hopen⟩

theorem hasOpenPathOfLengthExactlyFrom_iff_existsOpenSelfAvoidingWalkFrom {d n : ℕ}
    {ω : EdgeConfiguration d} {x : Cubic d} :
    hasOpenPathOfLengthExactlyFrom d ω x n ↔ existsOpenSelfAvoidingWalkFrom d n x ω :=
  ⟨hasOpenPathOfLengthExactlyFrom_imp_existsOpenSelfAvoidingWalkFrom,
    existsOpenSelfAvoidingWalkFrom_imp_hasOpenPathOfLengthExactlyFrom⟩

theorem dependsOn_hasOpenPathOfLengthExactlyFrom (d : ℕ) (x : Cubic d) (n : ℕ) :
    DependsOn (selfAvoidingWalkFromSupport d n x)
      {ω : EdgeConfiguration d | hasOpenPathOfLengthExactlyFrom d ω x n} := by
  simpa [hasOpenPathOfLengthExactlyFrom_iff_existsOpenSelfAvoidingWalkFrom] using
    dependsOn_existsOpenSelfAvoidingWalkFrom d n x

theorem dependsOn_hasOpenPathOfLengthAtLeastFrom (d : ℕ) (x : Cubic d) (n : ℕ) :
    DependsOn (selfAvoidingWalkFromSupport d n x)
      {ω : EdgeConfiguration d | hasOpenPathOfLengthAtLeastFrom d ω x n} := by
  simpa [hasOpenPathOfLengthAtLeastFrom_iff_hasOpenPathOfLengthExactlyFrom] using
    dependsOn_hasOpenPathOfLengthExactlyFrom d x n

theorem measurableSet_hasOpenPathOfLengthExactlyFrom (d : ℕ) (x : Cubic d) (n : ℕ) :
    MeasurableSet {ω : EdgeConfiguration d | hasOpenPathOfLengthExactlyFrom d ω x n} :=
  (dependsOn_hasOpenPathOfLengthExactlyFrom d x n).measurableSet

theorem measurableSet_hasOpenPathOfLengthAtLeastFrom (d : ℕ) (x : Cubic d) (n : ℕ) :
    MeasurableSet {ω : EdgeConfiguration d | hasOpenPathOfLengthAtLeastFrom d ω x n} :=
  (dependsOn_hasOpenPathOfLengthAtLeastFrom d x n).measurableSet

theorem hasOpenPathOfLengthAtLeastFrom_mono_of_le {d n m : ℕ}
    {ω : EdgeConfiguration d} {x : Cubic d} (hnm : n ≤ m) :
    hasOpenPathOfLengthAtLeastFrom d ω x m →
      hasOpenPathOfLengthAtLeastFrom d ω x n := by
  rintro ⟨v, w, hwpath, hlen, hopen⟩
  refine ⟨w.getVert n, w.take n, hwpath.take n, ?_, walkIsOpen_take w hopen n⟩
  simp [Nat.min_eq_left (hnm.trans hlen)]

theorem antitone_hasOpenPathOfLengthAtLeastFrom (d : ℕ) (x : Cubic d) :
    Antitone fun n : ℕ ↦
      {ω : EdgeConfiguration d | hasOpenPathOfLengthAtLeastFrom d ω x n} := by
  intro n m hnm ω hω
  exact hasOpenPathOfLengthAtLeastFrom_mono_of_le hnm hω

theorem hasInfiniteOpenClusterFrom_event_eq_iInter (d : ℕ) (x : Cubic d) :
    {ω : EdgeConfiguration d | hasInfiniteOpenClusterFrom d ω x} =
      ⋂ n : ℕ, {ω : EdgeConfiguration d | hasOpenPathOfLengthAtLeastFrom d ω x n} := by
  ext ω
  simp [hasInfiniteOpenClusterFrom_iff_hasArbitrarilyLongOpenPathsFrom,
    hasArbitrarilyLongOpenPathsFrom]

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

/-- Finite-support FKG for increasing cubic bond observables. -/
theorem bernoulliBondMeasure_integral_fkg_of_dependsOnFunction (d : ℕ)
    {E F : Finset (CubicEdge d)} {X Y : EdgeConfiguration d → ℝ} (p : I)
    (hXinc : IsIncreasingRandomVariable X) (hYinc : IsIncreasingRandomVariable Y)
    (hXdep : DependsOnFunction E X) (hYdep : DependsOnFunction F Y) :
    (∫ ω, X ω ∂bernoulliBondMeasure d p) *
        (∫ ω, Y ω ∂bernoulliBondMeasure d p) ≤
      ∫ ω, X ω * Y ω ∂bernoulliBondMeasure d p := by
  simpa [bernoulliBondMeasure] using
    setBernoulli_integral_fkg_of_dependsOnFunction (ι := CubicEdge d) p
      hXinc hYinc hXdep hYdep

/-- Finite-support FKG for decreasing cubic bond observables. -/
theorem bernoulliBondMeasure_integral_fkg_of_decreasing_dependsOnFunction (d : ℕ)
    {E F : Finset (CubicEdge d)} {X Y : EdgeConfiguration d → ℝ} (p : I)
    (hXdec : ∀ ⦃ω η : EdgeConfiguration d⦄, ω ⊆ η → X η ≤ X ω)
    (hYdec : ∀ ⦃ω η : EdgeConfiguration d⦄, ω ⊆ η → Y η ≤ Y ω)
    (hXdep : DependsOnFunction E X) (hYdep : DependsOnFunction F Y) :
    (∫ ω, X ω ∂bernoulliBondMeasure d p) *
        (∫ ω, Y ω ∂bernoulliBondMeasure d p) ≤
      ∫ ω, X ω * Y ω ∂bernoulliBondMeasure d p := by
  simpa [bernoulliBondMeasure] using
    setBernoulli_integral_fkg_of_decreasing_dependsOnFunction (ι := CubicEdge d) p
      hXdec hYdec hXdep hYdep

/-- Finite-support negative correlation for increasing/decreasing cubic bond observables. -/
theorem bernoulliBondMeasure_integral_le_mul_of_increasing_decreasing_dependsOnFunction
    (d : ℕ) {E F : Finset (CubicEdge d)} {X Y : EdgeConfiguration d → ℝ} (p : I)
    (hXinc : IsIncreasingRandomVariable X)
    (hYdec : ∀ ⦃ω η : EdgeConfiguration d⦄, ω ⊆ η → Y η ≤ Y ω)
    (hXdep : DependsOnFunction E X) (hYdep : DependsOnFunction F Y) :
    (∫ ω, X ω * Y ω ∂bernoulliBondMeasure d p) ≤
      (∫ ω, X ω ∂bernoulliBondMeasure d p) *
        (∫ ω, Y ω ∂bernoulliBondMeasure d p) := by
  simpa [bernoulliBondMeasure] using
    setBernoulli_integral_le_mul_of_increasing_decreasing_dependsOnFunction
      (ι := CubicEdge d) p hXinc hYdec hXdep hYdep

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

/-- FKG passes from finite-support increasing approximations to their probability limits for
Bernoulli bond percolation. -/
theorem bernoulliBondMeasure_real_fkg_of_finiteSupport_tendsto (d : ℕ) (p : I)
    {A B : Set (EdgeConfiguration d)}
    {Aapprox Bapprox : ℕ → Set (EdgeConfiguration d)}
    {EA EB : ℕ → Finset (CubicEdge d)}
    (hAinc : ∀ n, IsIncreasingEvent (Aapprox n))
    (hBinc : ∀ n, IsIncreasingEvent (Bapprox n))
    (hAdep : ∀ n, DependsOn (EA n) (Aapprox n))
    (hBdep : ∀ n, DependsOn (EB n) (Bapprox n))
    (hAtend : Filter.Tendsto
      (fun n ↦ (bernoulliBondMeasure d p).real (Aapprox n)) Filter.atTop
      (nhds ((bernoulliBondMeasure d p).real A)))
    (hBtend : Filter.Tendsto
      (fun n ↦ (bernoulliBondMeasure d p).real (Bapprox n)) Filter.atTop
      (nhds ((bernoulliBondMeasure d p).real B)))
    (hABtend : Filter.Tendsto
      (fun n ↦ (bernoulliBondMeasure d p).real (Aapprox n ∩ Bapprox n)) Filter.atTop
      (nhds ((bernoulliBondMeasure d p).real (A ∩ B)))) :
    (bernoulliBondMeasure d p).real A * (bernoulliBondMeasure d p).real B ≤
      (bernoulliBondMeasure d p).real (A ∩ B) := by
  simpa [bernoulliBondMeasure] using
    setBernoulli_real_fkg_of_finiteSupport_tendsto (ι := CubicEdge d) p
      hAinc hBinc hAdep hBdep hAtend hBtend hABtend

/-- Decreasing-event FKG passes from finite-support decreasing approximations to their probability
limits for Bernoulli bond percolation. -/
theorem bernoulliBondMeasure_real_fkg_of_decreasing_finiteSupport_tendsto (d : ℕ) (p : I)
    {A B : Set (EdgeConfiguration d)}
    {Aapprox Bapprox : ℕ → Set (EdgeConfiguration d)}
    {EA EB : ℕ → Finset (CubicEdge d)}
    (hAdec : ∀ n, IsDecreasingEvent (Aapprox n))
    (hBdec : ∀ n, IsDecreasingEvent (Bapprox n))
    (hAdep : ∀ n, DependsOn (EA n) (Aapprox n))
    (hBdep : ∀ n, DependsOn (EB n) (Bapprox n))
    (hAtend : Filter.Tendsto
      (fun n ↦ (bernoulliBondMeasure d p).real (Aapprox n)) Filter.atTop
      (nhds ((bernoulliBondMeasure d p).real A)))
    (hBtend : Filter.Tendsto
      (fun n ↦ (bernoulliBondMeasure d p).real (Bapprox n)) Filter.atTop
      (nhds ((bernoulliBondMeasure d p).real B)))
    (hABtend : Filter.Tendsto
      (fun n ↦ (bernoulliBondMeasure d p).real (Aapprox n ∩ Bapprox n)) Filter.atTop
      (nhds ((bernoulliBondMeasure d p).real (A ∩ B)))) :
    (bernoulliBondMeasure d p).real A * (bernoulliBondMeasure d p).real B ≤
      (bernoulliBondMeasure d p).real (A ∩ B) := by
  simpa [bernoulliBondMeasure] using
    setBernoulli_real_fkg_of_decreasing_finiteSupport_tendsto (ι := CubicEdge d) p
      hAdec hBdec hAdep hBdep hAtend hBtend hABtend

/-- Negative association for increasing/decreasing event approximations passes to probability
limits for Bernoulli bond percolation. -/
theorem bernoulliBondMeasure_real_le_mul_of_increasing_decreasing_finiteSupport_tendsto
    (d : ℕ) (p : I) {A B : Set (EdgeConfiguration d)}
    {Aapprox Bapprox : ℕ → Set (EdgeConfiguration d)}
    {EA EB : ℕ → Finset (CubicEdge d)}
    (hAinc : ∀ n, IsIncreasingEvent (Aapprox n))
    (hBdec : ∀ n, IsDecreasingEvent (Bapprox n))
    (hAdep : ∀ n, DependsOn (EA n) (Aapprox n))
    (hBdep : ∀ n, DependsOn (EB n) (Bapprox n))
    (hAtend : Filter.Tendsto
      (fun n ↦ (bernoulliBondMeasure d p).real (Aapprox n)) Filter.atTop
      (nhds ((bernoulliBondMeasure d p).real A)))
    (hBtend : Filter.Tendsto
      (fun n ↦ (bernoulliBondMeasure d p).real (Bapprox n)) Filter.atTop
      (nhds ((bernoulliBondMeasure d p).real B)))
    (hABtend : Filter.Tendsto
      (fun n ↦ (bernoulliBondMeasure d p).real (Aapprox n ∩ Bapprox n)) Filter.atTop
      (nhds ((bernoulliBondMeasure d p).real (A ∩ B)))) :
    (bernoulliBondMeasure d p).real (A ∩ B) ≤
      (bernoulliBondMeasure d p).real A * (bernoulliBondMeasure d p).real B := by
  simpa [bernoulliBondMeasure] using
    setBernoulli_real_le_mul_of_increasing_decreasing_finiteSupport_tendsto
      (ι := CubicEdge d) p hAinc hBdec hAdep hBdep hAtend hBtend hABtend

/-- FKG passes from finite-support increasing approximations converging in symmetric-difference
measure to their target events for Bernoulli bond percolation. -/
theorem bernoulliBondMeasure_real_fkg_of_finiteSupport_symmDiff_tendsto (d : ℕ) (p : I)
    {A B : Set (EdgeConfiguration d)}
    {Aapprox Bapprox : ℕ → Set (EdgeConfiguration d)}
    {EA EB : ℕ → Finset (CubicEdge d)}
    (hAmeas : MeasurableSet A) (hBmeas : MeasurableSet B)
    (hAinc : ∀ n, IsIncreasingEvent (Aapprox n))
    (hBinc : ∀ n, IsIncreasingEvent (Bapprox n))
    (hAdep : ∀ n, DependsOn (EA n) (Aapprox n))
    (hBdep : ∀ n, DependsOn (EB n) (Bapprox n))
    (hAΔ : Filter.Tendsto
      (fun n ↦ (bernoulliBondMeasure d p).real (Aapprox n ∆ A)) Filter.atTop
      (nhds 0))
    (hBΔ : Filter.Tendsto
      (fun n ↦ (bernoulliBondMeasure d p).real (Bapprox n ∆ B)) Filter.atTop
      (nhds 0))
    (hABΔ : Filter.Tendsto
      (fun n ↦ (bernoulliBondMeasure d p).real ((Aapprox n ∩ Bapprox n) ∆ (A ∩ B)))
        Filter.atTop (nhds 0)) :
    (bernoulliBondMeasure d p).real A * (bernoulliBondMeasure d p).real B ≤
      (bernoulliBondMeasure d p).real (A ∩ B) := by
  simpa [bernoulliBondMeasure] using
    setBernoulli_real_fkg_of_finiteSupport_symmDiff_tendsto (ι := CubicEdge d) p
      hAmeas hBmeas hAinc hBinc hAdep hBdep hAΔ hBΔ hABΔ

/-- FKG from finite-support increasing approximations converging in symmetric-difference measure
for Bernoulli bond percolation; the intersection convergence is derived automatically. -/
theorem bernoulliBondMeasure_real_fkg_of_finiteSupport_symmDiff_tendsto_pair
    (d : ℕ) (p : I) {A B : Set (EdgeConfiguration d)}
    {Aapprox Bapprox : ℕ → Set (EdgeConfiguration d)}
    {EA EB : ℕ → Finset (CubicEdge d)}
    (hAmeas : MeasurableSet A) (hBmeas : MeasurableSet B)
    (hAinc : ∀ n, IsIncreasingEvent (Aapprox n))
    (hBinc : ∀ n, IsIncreasingEvent (Bapprox n))
    (hAdep : ∀ n, DependsOn (EA n) (Aapprox n))
    (hBdep : ∀ n, DependsOn (EB n) (Bapprox n))
    (hAΔ : Filter.Tendsto
      (fun n ↦ (bernoulliBondMeasure d p).real (Aapprox n ∆ A)) Filter.atTop
      (nhds 0))
    (hBΔ : Filter.Tendsto
      (fun n ↦ (bernoulliBondMeasure d p).real (Bapprox n ∆ B)) Filter.atTop
      (nhds 0)) :
    (bernoulliBondMeasure d p).real A * (bernoulliBondMeasure d p).real B ≤
      (bernoulliBondMeasure d p).real (A ∩ B) := by
  simpa [bernoulliBondMeasure] using
    setBernoulli_real_fkg_of_finiteSupport_symmDiff_tendsto_pair
      (ι := CubicEdge d) p hAmeas hBmeas hAinc hBinc hAdep hBdep hAΔ hBΔ

/-- Decreasing-event FKG passes from finite-support decreasing approximations converging in
symmetric-difference measure for Bernoulli bond percolation. -/
theorem bernoulliBondMeasure_real_fkg_of_decreasing_finiteSupport_symmDiff_tendsto
    (d : ℕ) (p : I) {A B : Set (EdgeConfiguration d)}
    {Aapprox Bapprox : ℕ → Set (EdgeConfiguration d)}
    {EA EB : ℕ → Finset (CubicEdge d)}
    (hAmeas : MeasurableSet A) (hBmeas : MeasurableSet B)
    (hAdec : ∀ n, IsDecreasingEvent (Aapprox n))
    (hBdec : ∀ n, IsDecreasingEvent (Bapprox n))
    (hAdep : ∀ n, DependsOn (EA n) (Aapprox n))
    (hBdep : ∀ n, DependsOn (EB n) (Bapprox n))
    (hAΔ : Filter.Tendsto
      (fun n ↦ (bernoulliBondMeasure d p).real (Aapprox n ∆ A)) Filter.atTop
      (nhds 0))
    (hBΔ : Filter.Tendsto
      (fun n ↦ (bernoulliBondMeasure d p).real (Bapprox n ∆ B)) Filter.atTop
      (nhds 0))
    (hABΔ : Filter.Tendsto
      (fun n ↦ (bernoulliBondMeasure d p).real ((Aapprox n ∩ Bapprox n) ∆ (A ∩ B)))
        Filter.atTop (nhds 0)) :
    (bernoulliBondMeasure d p).real A * (bernoulliBondMeasure d p).real B ≤
      (bernoulliBondMeasure d p).real (A ∩ B) := by
  simpa [bernoulliBondMeasure] using
    setBernoulli_real_fkg_of_decreasing_finiteSupport_symmDiff_tendsto
      (ι := CubicEdge d) p hAmeas hBmeas hAdec hBdec hAdep hBdep hAΔ hBΔ hABΔ

/-- Decreasing-event FKG from finite-support decreasing approximations converging in
symmetric-difference measure for Bernoulli bond percolation; the intersection convergence is
derived automatically. -/
theorem bernoulliBondMeasure_real_fkg_of_decreasing_finiteSupport_symmDiff_tendsto_pair
    (d : ℕ) (p : I) {A B : Set (EdgeConfiguration d)}
    {Aapprox Bapprox : ℕ → Set (EdgeConfiguration d)}
    {EA EB : ℕ → Finset (CubicEdge d)}
    (hAmeas : MeasurableSet A) (hBmeas : MeasurableSet B)
    (hAdec : ∀ n, IsDecreasingEvent (Aapprox n))
    (hBdec : ∀ n, IsDecreasingEvent (Bapprox n))
    (hAdep : ∀ n, DependsOn (EA n) (Aapprox n))
    (hBdep : ∀ n, DependsOn (EB n) (Bapprox n))
    (hAΔ : Filter.Tendsto
      (fun n ↦ (bernoulliBondMeasure d p).real (Aapprox n ∆ A)) Filter.atTop
      (nhds 0))
    (hBΔ : Filter.Tendsto
      (fun n ↦ (bernoulliBondMeasure d p).real (Bapprox n ∆ B)) Filter.atTop
      (nhds 0)) :
    (bernoulliBondMeasure d p).real A * (bernoulliBondMeasure d p).real B ≤
      (bernoulliBondMeasure d p).real (A ∩ B) := by
  simpa [bernoulliBondMeasure] using
    setBernoulli_real_fkg_of_decreasing_finiteSupport_symmDiff_tendsto_pair
      (ι := CubicEdge d) p hAmeas hBmeas hAdec hBdec hAdep hBdep hAΔ hBΔ

/-- Negative association for increasing/decreasing approximations converging in
symmetric-difference measure for Bernoulli bond percolation. -/
theorem bernoulliBondMeasure_real_le_mul_of_increasing_decreasing_finiteSupport_symmDiff_tendsto
    (d : ℕ) (p : I) {A B : Set (EdgeConfiguration d)}
    {Aapprox Bapprox : ℕ → Set (EdgeConfiguration d)}
    {EA EB : ℕ → Finset (CubicEdge d)}
    (hAmeas : MeasurableSet A) (hBmeas : MeasurableSet B)
    (hAinc : ∀ n, IsIncreasingEvent (Aapprox n))
    (hBdec : ∀ n, IsDecreasingEvent (Bapprox n))
    (hAdep : ∀ n, DependsOn (EA n) (Aapprox n))
    (hBdep : ∀ n, DependsOn (EB n) (Bapprox n))
    (hAΔ : Filter.Tendsto
      (fun n ↦ (bernoulliBondMeasure d p).real (Aapprox n ∆ A)) Filter.atTop
      (nhds 0))
    (hBΔ : Filter.Tendsto
      (fun n ↦ (bernoulliBondMeasure d p).real (Bapprox n ∆ B)) Filter.atTop
      (nhds 0))
    (hABΔ : Filter.Tendsto
      (fun n ↦ (bernoulliBondMeasure d p).real ((Aapprox n ∩ Bapprox n) ∆ (A ∩ B)))
        Filter.atTop (nhds 0)) :
    (bernoulliBondMeasure d p).real (A ∩ B) ≤
      (bernoulliBondMeasure d p).real A * (bernoulliBondMeasure d p).real B := by
  simpa [bernoulliBondMeasure] using
    setBernoulli_real_le_mul_of_increasing_decreasing_finiteSupport_symmDiff_tendsto
      (ι := CubicEdge d) p hAmeas hBmeas hAinc hBdec hAdep hBdep hAΔ hBΔ hABΔ

/-- Negative association for increasing/decreasing approximations converging in
symmetric-difference measure for Bernoulli bond percolation; the intersection convergence is
derived automatically. -/
theorem bernoulliBondMeasure_real_le_mul_of_increasing_decreasing_finiteSupport_symmDiff_tendsto_pair
    (d : ℕ) (p : I) {A B : Set (EdgeConfiguration d)}
    {Aapprox Bapprox : ℕ → Set (EdgeConfiguration d)}
    {EA EB : ℕ → Finset (CubicEdge d)}
    (hAmeas : MeasurableSet A) (hBmeas : MeasurableSet B)
    (hAinc : ∀ n, IsIncreasingEvent (Aapprox n))
    (hBdec : ∀ n, IsDecreasingEvent (Bapprox n))
    (hAdep : ∀ n, DependsOn (EA n) (Aapprox n))
    (hBdep : ∀ n, DependsOn (EB n) (Bapprox n))
    (hAΔ : Filter.Tendsto
      (fun n ↦ (bernoulliBondMeasure d p).real (Aapprox n ∆ A)) Filter.atTop
      (nhds 0))
    (hBΔ : Filter.Tendsto
      (fun n ↦ (bernoulliBondMeasure d p).real (Bapprox n ∆ B)) Filter.atTop
      (nhds 0)) :
    (bernoulliBondMeasure d p).real (A ∩ B) ≤
      (bernoulliBondMeasure d p).real A * (bernoulliBondMeasure d p).real B := by
  simpa [bernoulliBondMeasure] using
    setBernoulli_real_le_mul_of_increasing_decreasing_finiteSupport_symmDiff_tendsto_pair
      (ι := CubicEdge d) p hAmeas hBmeas hAinc hBdec hAdep hBdep hAΔ hBΔ

/-- FKG passes from finite-support increasing observable approximations to their integral limits
for Bernoulli bond percolation. -/
theorem bernoulliBondMeasure_integral_fkg_of_finiteSupport_tendsto (d : ℕ) (p : I)
    {X Y : EdgeConfiguration d → ℝ}
    {Xapprox Yapprox : ℕ → EdgeConfiguration d → ℝ}
    {EX EY : ℕ → Finset (CubicEdge d)}
    (hXinc : ∀ n, IsIncreasingRandomVariable (Xapprox n))
    (hYinc : ∀ n, IsIncreasingRandomVariable (Yapprox n))
    (hXdep : ∀ n, DependsOnFunction (EX n) (Xapprox n))
    (hYdep : ∀ n, DependsOnFunction (EY n) (Yapprox n))
    (hXtend : Filter.Tendsto
      (fun n ↦ ∫ ω, Xapprox n ω ∂bernoulliBondMeasure d p) Filter.atTop
      (nhds (∫ ω, X ω ∂bernoulliBondMeasure d p)))
    (hYtend : Filter.Tendsto
      (fun n ↦ ∫ ω, Yapprox n ω ∂bernoulliBondMeasure d p) Filter.atTop
      (nhds (∫ ω, Y ω ∂bernoulliBondMeasure d p)))
    (hXYtend : Filter.Tendsto
      (fun n ↦ ∫ ω, Xapprox n ω * Yapprox n ω ∂bernoulliBondMeasure d p)
        Filter.atTop
      (nhds (∫ ω, X ω * Y ω ∂bernoulliBondMeasure d p))) :
    (∫ ω, X ω ∂bernoulliBondMeasure d p) *
        (∫ ω, Y ω ∂bernoulliBondMeasure d p) ≤
      ∫ ω, X ω * Y ω ∂bernoulliBondMeasure d p := by
  simpa [bernoulliBondMeasure] using
    setBernoulli_integral_fkg_of_finiteSupport_tendsto (ι := CubicEdge d) p
      hXinc hYinc hXdep hYdep hXtend hYtend hXYtend

/-- Decreasing-observable FKG passes from finite-support decreasing approximations to their
integral limits for Bernoulli bond percolation. -/
theorem bernoulliBondMeasure_integral_fkg_of_decreasing_finiteSupport_tendsto
    (d : ℕ) (p : I) {X Y : EdgeConfiguration d → ℝ}
    {Xapprox Yapprox : ℕ → EdgeConfiguration d → ℝ}
    {EX EY : ℕ → Finset (CubicEdge d)}
    (hXdec : ∀ n, ∀ ⦃ω η : EdgeConfiguration d⦄, ω ⊆ η → Xapprox n η ≤ Xapprox n ω)
    (hYdec : ∀ n, ∀ ⦃ω η : EdgeConfiguration d⦄, ω ⊆ η → Yapprox n η ≤ Yapprox n ω)
    (hXdep : ∀ n, DependsOnFunction (EX n) (Xapprox n))
    (hYdep : ∀ n, DependsOnFunction (EY n) (Yapprox n))
    (hXtend : Filter.Tendsto
      (fun n ↦ ∫ ω, Xapprox n ω ∂bernoulliBondMeasure d p) Filter.atTop
      (nhds (∫ ω, X ω ∂bernoulliBondMeasure d p)))
    (hYtend : Filter.Tendsto
      (fun n ↦ ∫ ω, Yapprox n ω ∂bernoulliBondMeasure d p) Filter.atTop
      (nhds (∫ ω, Y ω ∂bernoulliBondMeasure d p)))
    (hXYtend : Filter.Tendsto
      (fun n ↦ ∫ ω, Xapprox n ω * Yapprox n ω ∂bernoulliBondMeasure d p)
        Filter.atTop
      (nhds (∫ ω, X ω * Y ω ∂bernoulliBondMeasure d p))) :
    (∫ ω, X ω ∂bernoulliBondMeasure d p) *
        (∫ ω, Y ω ∂bernoulliBondMeasure d p) ≤
      ∫ ω, X ω * Y ω ∂bernoulliBondMeasure d p := by
  simpa [bernoulliBondMeasure] using
    setBernoulli_integral_fkg_of_decreasing_finiteSupport_tendsto
      (ι := CubicEdge d) p hXdec hYdec hXdep hYdep hXtend hYtend hXYtend

/-- Negative association for increasing/decreasing observable approximations passes to integral
limits for Bernoulli bond percolation. -/
theorem bernoulliBondMeasure_integral_le_mul_of_increasing_decreasing_finiteSupport_tendsto
    (d : ℕ) (p : I) {X Y : EdgeConfiguration d → ℝ}
    {Xapprox Yapprox : ℕ → EdgeConfiguration d → ℝ}
    {EX EY : ℕ → Finset (CubicEdge d)}
    (hXinc : ∀ n, IsIncreasingRandomVariable (Xapprox n))
    (hYdec : ∀ n, ∀ ⦃ω η : EdgeConfiguration d⦄, ω ⊆ η → Yapprox n η ≤ Yapprox n ω)
    (hXdep : ∀ n, DependsOnFunction (EX n) (Xapprox n))
    (hYdep : ∀ n, DependsOnFunction (EY n) (Yapprox n))
    (hXtend : Filter.Tendsto
      (fun n ↦ ∫ ω, Xapprox n ω ∂bernoulliBondMeasure d p) Filter.atTop
      (nhds (∫ ω, X ω ∂bernoulliBondMeasure d p)))
    (hYtend : Filter.Tendsto
      (fun n ↦ ∫ ω, Yapprox n ω ∂bernoulliBondMeasure d p) Filter.atTop
      (nhds (∫ ω, Y ω ∂bernoulliBondMeasure d p)))
    (hXYtend : Filter.Tendsto
      (fun n ↦ ∫ ω, Xapprox n ω * Yapprox n ω ∂bernoulliBondMeasure d p)
        Filter.atTop
      (nhds (∫ ω, X ω * Y ω ∂bernoulliBondMeasure d p))) :
    (∫ ω, X ω * Y ω ∂bernoulliBondMeasure d p) ≤
      (∫ ω, X ω ∂bernoulliBondMeasure d p) *
        (∫ ω, Y ω ∂bernoulliBondMeasure d p) := by
  simpa [bernoulliBondMeasure] using
    setBernoulli_integral_le_mul_of_increasing_decreasing_finiteSupport_tendsto
      (ι := CubicEdge d) p hXinc hYdec hXdep hYdep hXtend hYtend hXYtend

/-- FKG for increasing limits of finite-support increasing cubic bond events. -/
theorem bernoulliBondMeasure_real_fkg_iUnion_finiteSupport (d : ℕ) (p : I)
    {A B : ℕ → Set (EdgeConfiguration d)} {EA EB : ℕ → Finset (CubicEdge d)}
    (hAmono : Monotone A) (hBmono : Monotone B)
    (hAinc : ∀ n, IsIncreasingEvent (A n))
    (hBinc : ∀ n, IsIncreasingEvent (B n))
    (hAdep : ∀ n, DependsOn (EA n) (A n))
    (hBdep : ∀ n, DependsOn (EB n) (B n)) :
    (bernoulliBondMeasure d p).real (⋃ n, A n) *
        (bernoulliBondMeasure d p).real (⋃ n, B n) ≤
      (bernoulliBondMeasure d p).real ((⋃ n, A n) ∩ (⋃ n, B n)) := by
  simpa [bernoulliBondMeasure] using
    setBernoulli_real_fkg_iUnion_finiteSupport (ι := CubicEdge d) p
      hAmono hBmono hAinc hBinc hAdep hBdep

/-- FKG for decreasing limits of finite-support increasing cubic bond events. -/
theorem bernoulliBondMeasure_real_fkg_iInter_finiteSupport (d : ℕ) (p : I)
    {A B : ℕ → Set (EdgeConfiguration d)} {EA EB : ℕ → Finset (CubicEdge d)}
    (hAanti : Antitone A) (hBanti : Antitone B)
    (hAmeas : ∀ n, MeasurableSet (A n))
    (hBmeas : ∀ n, MeasurableSet (B n))
    (hAinc : ∀ n, IsIncreasingEvent (A n))
    (hBinc : ∀ n, IsIncreasingEvent (B n))
    (hAdep : ∀ n, DependsOn (EA n) (A n))
    (hBdep : ∀ n, DependsOn (EB n) (B n)) :
    (bernoulliBondMeasure d p).real (⋂ n, A n) *
        (bernoulliBondMeasure d p).real (⋂ n, B n) ≤
      (bernoulliBondMeasure d p).real ((⋂ n, A n) ∩ (⋂ n, B n)) := by
  simpa [bernoulliBondMeasure] using
    setBernoulli_real_fkg_iInter_finiteSupport (ι := CubicEdge d) p
      hAanti hBanti hAmeas hBmeas hAinc hBinc hAdep hBdep

/-- FKG between a finite-support increasing bond event and the rooted infinite-cluster event.
This is the concrete measurable-event instance needed in Grimmett's root-independence proof:
the infinite event is a decreasing intersection of finite-support increasing path events. -/
theorem bernoulliBondMeasure_real_fkg_of_dependsOn_hasInfiniteOpenClusterFrom
    (d : ℕ) {E : Finset (CubicEdge d)} {A : Set (EdgeConfiguration d)} (p : I)
    (x : Cubic d) (hAinc : IsIncreasingEvent A) (hAdep : DependsOn E A) :
    (bernoulliBondMeasure d p).real A * thetaFrom d x p ≤
      (bernoulliBondMeasure d p).real
        (A ∩ {ω : EdgeConfiguration d | hasInfiniteOpenClusterFrom d ω x}) := by
  let B : ℕ → Set (EdgeConfiguration d) :=
    fun n ↦ {ω : EdgeConfiguration d | hasOpenPathOfLengthAtLeastFrom d ω x n}
  have h := bernoulliBondMeasure_real_fkg_iInter_finiteSupport (d := d) (p := p)
    (A := fun _ : ℕ ↦ A) (B := B) (EA := fun _ : ℕ ↦ E)
    (EB := fun n ↦ selfAvoidingWalkFromSupport d n x)
    (fun _ _ _ _ hω ↦ hω)
    (by simpa [B] using antitone_hasOpenPathOfLengthAtLeastFrom d x)
    (fun _ ↦ hAdep.measurableSet)
    (fun n ↦ by simpa [B] using measurableSet_hasOpenPathOfLengthAtLeastFrom d x n)
    (fun _ ↦ hAinc)
    (fun n ↦ by simpa [B] using isIncreasingEvent_hasOpenPathOfLengthAtLeastFrom d x n)
    (fun _ ↦ hAdep)
    (fun n ↦ by simpa [B] using dependsOn_hasOpenPathOfLengthAtLeastFrom d x n)
  have hconst : (⋂ _ : ℕ, A) = A := by
    ext ω
    simp
  simpa [thetaFrom, B, hasInfiniteOpenClusterFrom_event_eq_iInter d x, hconst] using h

/-- FKG between two rooted infinite-cluster events. Both events are represented as decreasing
intersections of finite-support increasing path events. -/
theorem bernoulliBondMeasure_real_fkg_hasInfiniteOpenClusterFrom
    (d : ℕ) (p : I) (x y : Cubic d) :
    thetaFrom d x p * thetaFrom d y p ≤
      (bernoulliBondMeasure d p).real
        ({ω : EdgeConfiguration d | hasInfiniteOpenClusterFrom d ω x} ∩
          {ω : EdgeConfiguration d | hasInfiniteOpenClusterFrom d ω y}) := by
  let A : ℕ → Set (EdgeConfiguration d) :=
    fun n ↦ {ω : EdgeConfiguration d | hasOpenPathOfLengthAtLeastFrom d ω x n}
  let B : ℕ → Set (EdgeConfiguration d) :=
    fun n ↦ {ω : EdgeConfiguration d | hasOpenPathOfLengthAtLeastFrom d ω y n}
  have h := bernoulliBondMeasure_real_fkg_iInter_finiteSupport (d := d) (p := p)
    (A := A) (B := B)
    (EA := fun n ↦ selfAvoidingWalkFromSupport d n x)
    (EB := fun n ↦ selfAvoidingWalkFromSupport d n y)
    (by simpa [A] using antitone_hasOpenPathOfLengthAtLeastFrom d x)
    (by simpa [B] using antitone_hasOpenPathOfLengthAtLeastFrom d y)
    (fun n ↦ by simpa [A] using measurableSet_hasOpenPathOfLengthAtLeastFrom d x n)
    (fun n ↦ by simpa [B] using measurableSet_hasOpenPathOfLengthAtLeastFrom d y n)
    (fun n ↦ by simpa [A] using isIncreasingEvent_hasOpenPathOfLengthAtLeastFrom d x n)
    (fun n ↦ by simpa [B] using isIncreasingEvent_hasOpenPathOfLengthAtLeastFrom d y n)
    (fun n ↦ by simpa [A] using dependsOn_hasOpenPathOfLengthAtLeastFrom d x n)
    (fun n ↦ by simpa [B] using dependsOn_hasOpenPathOfLengthAtLeastFrom d y n)
  simpa [thetaFrom, A, B, hasInfiniteOpenClusterFrom_event_eq_iInter d x,
    hasInfiniteOpenClusterFrom_event_eq_iInter d y] using h

/-- Deterministic event inclusion behind Grimmett's origin-independence theorem: if a fixed walk
from `x` to `y` is open and `y` has an infinite open cluster, then `x` has one too. -/
theorem walkIsOpen_inter_hasInfiniteOpenClusterFrom_subset {d : ℕ} {x y : Cubic d}
    (w : (cubicGraph d).Walk x y) :
    {ω : EdgeConfiguration d | walkIsOpen ω w} ∩
        {ω : EdgeConfiguration d | hasInfiniteOpenClusterFrom d ω y} ⊆
      {ω : EdgeConfiguration d | hasInfiniteOpenClusterFrom d ω x} := by
  intro ω hω
  exact hasInfiniteOpenClusterFrom_of_walkIsOpen w hω.1 hω.2

/-- Source-shaped FKG step for Grimmett's Theorem (2.8): once FKG supplies the lower bound for
the fixed connector event and the infinite-cluster event at `y`, the percolation probability at
`x` dominates their product. -/
theorem bernoulliBondMeasure_real_walkIsOpen_mul_thetaFrom_le_thetaFrom_of_fkg
    {d : ℕ} {x y : Cubic d} (p : I) (w : (cubicGraph d).Walk x y)
    (hFKG :
      (bernoulliBondMeasure d p).real {ω : EdgeConfiguration d | walkIsOpen ω w} *
          thetaFrom d y p ≤
        (bernoulliBondMeasure d p).real
          ({ω : EdgeConfiguration d | walkIsOpen ω w} ∩
            {ω : EdgeConfiguration d | hasInfiniteOpenClusterFrom d ω y})) :
    (bernoulliBondMeasure d p).real {ω : EdgeConfiguration d | walkIsOpen ω w} *
        thetaFrom d y p ≤
      thetaFrom d x p := by
  have hmono :
      (bernoulliBondMeasure d p).real
          ({ω : EdgeConfiguration d | walkIsOpen ω w} ∩
            {ω : EdgeConfiguration d | hasInfiniteOpenClusterFrom d ω y}) ≤
        (bernoulliBondMeasure d p).real
          {ω : EdgeConfiguration d | hasInfiniteOpenClusterFrom d ω x} :=
    measureReal_mono (walkIsOpen_inter_hasInfiniteOpenClusterFrom_subset w) (by
      change setBer((Set.univ : Set (CubicEdge d)), p)
          {ω : EdgeConfiguration d | hasInfiniteOpenClusterFrom d ω x} ≠ ∞
      refine ne_of_lt ((measure_mono (Set.subset_univ _)).trans_lt ?_)
      rw [MeasureTheory.IsProbabilityMeasure.measure_univ]
      exact ENNReal.one_lt_top)
  exact hFKG.trans (by simpa [thetaFrom] using hmono)

/-- Source-shaped FKG step for Grimmett's Theorem (2.8), now discharged for the actual rooted
infinite-cluster event by the decreasing finite-path approximation above. -/
theorem bernoulliBondMeasure_real_walkIsOpen_mul_thetaFrom_le_thetaFrom
    {d : ℕ} {x y : Cubic d} (p : I) (w : (cubicGraph d).Walk x y) :
    (bernoulliBondMeasure d p).real {ω : EdgeConfiguration d | walkIsOpen ω w} *
        thetaFrom d y p ≤
      thetaFrom d x p := by
  have hFKG :
      (bernoulliBondMeasure d p).real {ω : EdgeConfiguration d | walkIsOpen ω w} *
          thetaFrom d y p ≤
        (bernoulliBondMeasure d p).real
          ({ω : EdgeConfiguration d | walkIsOpen ω w} ∩
            {ω : EdgeConfiguration d | hasInfiniteOpenClusterFrom d ω y}) :=
    bernoulliBondMeasure_real_fkg_of_dependsOn_hasInfiniteOpenClusterFrom
      d p y (isIncreasingEvent_walkIsOpen w) (dependsOn_walkIsOpen w)
  exact bernoulliBondMeasure_real_walkIsOpen_mul_thetaFrom_le_thetaFrom_of_fkg p w hFKG

/-- If a fixed open trail from `x` to `y` has positive probability and the FKG lower bound for
the connector event is available, then vanishing of the rooted percolation probability at `x`
forces vanishing at `y`. This is the zero-transfer half of Grimmett's Theorem (2.8). -/
theorem thetaFrom_eq_zero_of_open_trail_fkg {d : ℕ} {x y : Cubic d} {p : I}
    (w : (cubicGraph d).Walk x y) (htrail : w.IsTrail) (hp : 0 < (p : ℝ))
    (hFKG :
      (bernoulliBondMeasure d p).real {ω : EdgeConfiguration d | walkIsOpen ω w} *
          thetaFrom d y p ≤
        (bernoulliBondMeasure d p).real
          ({ω : EdgeConfiguration d | walkIsOpen ω w} ∩
            {ω : EdgeConfiguration d | hasInfiniteOpenClusterFrom d ω y}))
    (hx : thetaFrom d x p = 0) :
    thetaFrom d y p = 0 := by
  have hle :=
    bernoulliBondMeasure_real_walkIsOpen_mul_thetaFrom_le_thetaFrom_of_fkg p w hFKG
  have hwalk_pos :
      0 < (bernoulliBondMeasure d p).real {ω : EdgeConfiguration d | walkIsOpen ω w} :=
    bernoulliBondMeasure_real_walkIsOpen_pos p w htrail hp
  have hy_nonneg : 0 ≤ thetaFrom d y p := measureReal_nonneg
  apply le_antisymm ?_ hy_nonneg
  have hprod :
      (bernoulliBondMeasure d p).real {ω : EdgeConfiguration d | walkIsOpen ω w} *
          thetaFrom d y p ≤ 0 := by
    simpa [hx] using hle
  nlinarith

/-- Two-sided zero-set transfer along a fixed trail, stated with the two FKG instances that will
come from the full measurable-event FKG theorem. -/
theorem thetaFrom_eq_zero_iff_of_open_trail_fkg {d : ℕ} {x y : Cubic d} {p : I}
    (w : (cubicGraph d).Walk x y) (htrail : w.IsTrail) (hp : 0 < (p : ℝ))
    (hFKGxy :
      (bernoulliBondMeasure d p).real {ω : EdgeConfiguration d | walkIsOpen ω w} *
          thetaFrom d y p ≤
        (bernoulliBondMeasure d p).real
          ({ω : EdgeConfiguration d | walkIsOpen ω w} ∩
            {ω : EdgeConfiguration d | hasInfiniteOpenClusterFrom d ω y}))
    (hFKGyx :
      (bernoulliBondMeasure d p).real {ω : EdgeConfiguration d | walkIsOpen ω w.reverse} *
          thetaFrom d x p ≤
        (bernoulliBondMeasure d p).real
          ({ω : EdgeConfiguration d | walkIsOpen ω w.reverse} ∩
            {ω : EdgeConfiguration d | hasInfiniteOpenClusterFrom d ω x})) :
    thetaFrom d x p = 0 ↔ thetaFrom d y p = 0 := by
  constructor
  · exact thetaFrom_eq_zero_of_open_trail_fkg w htrail hp hFKGxy
  · exact thetaFrom_eq_zero_of_open_trail_fkg w.reverse (htrail.reverse w) hp hFKGyx

/-- Vanishing of the rooted percolation probability transfers along any fixed open trail with
positive edge parameter. This is the FKG-powered zero-transfer half of Grimmett's Theorem (2.8)
without an external FKG hypothesis. -/
theorem thetaFrom_eq_zero_of_open_trail {d : ℕ} {x y : Cubic d} {p : I}
    (w : (cubicGraph d).Walk x y) (htrail : w.IsTrail) (hp : 0 < (p : ℝ))
    (hx : thetaFrom d x p = 0) :
    thetaFrom d y p = 0 := by
  have hle := bernoulliBondMeasure_real_walkIsOpen_mul_thetaFrom_le_thetaFrom p w
  have hwalk_pos :
      0 < (bernoulliBondMeasure d p).real {ω : EdgeConfiguration d | walkIsOpen ω w} :=
    bernoulliBondMeasure_real_walkIsOpen_pos p w htrail hp
  have hy_nonneg : 0 ≤ thetaFrom d y p := measureReal_nonneg
  apply le_antisymm ?_ hy_nonneg
  have hprod :
      (bernoulliBondMeasure d p).real {ω : EdgeConfiguration d | walkIsOpen ω w} *
          thetaFrom d y p ≤ 0 := by
    simpa [hx] using hle
  nlinarith

/-- Two-sided zero-set transfer along a fixed trail, with the rooted infinite-cluster FKG
instance supplied internally. -/
theorem thetaFrom_eq_zero_iff_of_open_trail {d : ℕ} {x y : Cubic d} {p : I}
    (w : (cubicGraph d).Walk x y) (htrail : w.IsTrail) (hp : 0 < (p : ℝ)) :
    thetaFrom d x p = 0 ↔ thetaFrom d y p = 0 := by
  constructor
  · exact thetaFrom_eq_zero_of_open_trail w htrail hp
  · exact thetaFrom_eq_zero_of_open_trail w.reverse (htrail.reverse w) hp

/-- Two-sided zero-set transfer along any fixed finite walk. The walk is first reduced to its
path representative, whose edge list is a trail, so the fixed connector has positive Bernoulli
probability when `p > 0`. -/
theorem thetaFrom_eq_zero_iff_of_walk {d : ℕ} {x y : Cubic d} {p : I}
    (w : (cubicGraph d).Walk x y) (hp : 0 < (p : ℝ)) :
    thetaFrom d x p = 0 ↔ thetaFrom d y p = 0 := by
  exact thetaFrom_eq_zero_iff_of_open_trail (w.toPath : (cubicGraph d).Walk x y)
    w.toPath.property.isTrail hp

/-- Two-sided zero-set transfer for any two reachable cubic-lattice vertices. This is the graph
connectivity-facing form of Grimmett's Theorem (2.8). -/
theorem thetaFrom_eq_zero_iff_of_reachable {d : ℕ} {x y : Cubic d} {p : I}
    (hxy : (cubicGraph d).Reachable x y) (hp : 0 < (p : ℝ)) :
    thetaFrom d x p = 0 ↔ thetaFrom d y p = 0 := by
  rcases hxy with ⟨w⟩
  exact thetaFrom_eq_zero_iff_of_walk w hp

/-- Origin-rooted version of Grimmett's zero-set transfer: for any vertex reachable from the
origin, the event probabilities `θ(p)` and `θ_x(p)` vanish for exactly the same `p > 0`. -/
theorem theta_eq_zero_iff_thetaFrom_of_reachable_origin {d : ℕ} {x : Cubic d} {p : I}
    (hx : (cubicGraph d).Reachable (cubicOrigin : Cubic d) x) (hp : 0 < (p : ℝ)) :
    theta d p = 0 ↔ thetaFrom d x p = 0 := by
  simpa [thetaFrom_origin] using thetaFrom_eq_zero_iff_of_reachable hx hp

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
