import Percolation.Bernoulli.Sprinkling

/-!
# Independence for arbitrary coordinate blocks

Finite-cylinder independence is not enough for the strip exploration in Grimmett's proof of
Theorem 8.21: one history uses all bonds strictly to the left of an entrance hyperplane, while
the fresh event uses every bond internal to the next infinite strip.  This file packages the
corresponding product-measure fact through the common-uniform coupling.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval

variable {ι : Type*}

/-- Event membership is determined by the coordinates in the possibly infinite set `S`. -/
def DependsOnCoordinates (S : Set ι) (A : Set (Set ι)) : Prop :=
  ∀ ⦃ω η : Set ι⦄, (∀ e ∈ S, (e ∈ ω ↔ e ∈ η)) → (ω ∈ A ↔ η ∈ A)

theorem DependsOnCoordinates.mono {S T : Set ι} {A : Set (Set ι)}
    (hA : DependsOnCoordinates S A) (hST : S ⊆ T) :
    DependsOnCoordinates T A :=
  fun _ _ h ↦ hA fun e he ↦ h e (hST he)

theorem DependsOnCoordinates.inter {S : Set ι} {A B : Set (Set ι)}
    (hA : DependsOnCoordinates S A) (hB : DependsOnCoordinates S B) :
    DependsOnCoordinates S (A ∩ B) :=
  fun _ _ h ↦ and_congr (hA h) (hB h)

theorem DependsOnCoordinates.union {S : Set ι} {A B : Set (Set ι)}
    (hA : DependsOnCoordinates S A) (hB : DependsOnCoordinates S B) :
    DependsOnCoordinates S (A ∪ B) :=
  fun _ _ h ↦ or_congr (hA h) (hB h)

theorem DependsOnCoordinates.compl {S : Set ι} {A : Set (Set ι)}
    (hA : DependsOnCoordinates S A) : DependsOnCoordinates S Aᶜ :=
  fun _ _ h ↦ not_congr (hA h)

theorem DependsOnCoordinates.iUnion {κ : Sort*} {S : Set ι}
    {A : κ → Set (Set ι)} (hA : ∀ k, DependsOnCoordinates S (A k)) :
    DependsOnCoordinates S (⋃ k, A k) := by
  intro ω η h
  simp only [Set.mem_iUnion]
  exact exists_congr fun k ↦ hA k h

theorem DependsOnCoordinates.iInter {κ : Sort*} {S : Set ι}
    {A : κ → Set (Set ι)} (hA : ∀ k, DependsOnCoordinates S (A k)) :
    DependsOnCoordinates S (⋂ k, A k) := by
  intro ω η h
  simp only [Set.mem_iInter]
  exact forall_congr' fun k ↦ hA k h

theorem dependsOnCoordinates_coordinateEvent {S : Set ι} {e : ι} (he : e ∈ S) :
    DependsOnCoordinates S {ω : Set ι | e ∈ ω} :=
  fun _ _ h ↦ h e he

theorem DependsOn.dependsOnCoordinates {E : Finset ι} {A : Set (Set ι)}
    (hA : DependsOn E A) : DependsOnCoordinates (E : Set ι) A :=
  hA

/-- Pulling a coordinate-local event back through the threshold map gives an event in the
corresponding real-coordinate sigma algebra. -/
theorem DependsOnCoordinates.measurableSet_thresholdConfiguration_preimage
    {S : Set ι} {A : Set (Set ι)} (hA : DependsOnCoordinates S A)
    (hAm : MeasurableSet A) (p : I) :
    MeasurableSet[coordSigma ι S] (thresholdConfiguration p ⁻¹' A) := by
  apply measurableSet_coordSigma_of_eqOn
    (hAm.preimage (measurable_thresholdConfiguration p))
  intro X Y hXY
  exact hA fun e he ↦ by
    change (X e < (p : ℝ)) ↔ (Y e < (p : ℝ))
    rw [hXY e he]

/-- Events determined by disjoint, possibly infinite coordinate blocks are independent under
Bernoulli product measure. -/
theorem setBernoulli_indepSet_of_dependsOnCoordinates
    (p : I) {S T : Set ι} (hST : Disjoint S T)
    {A B : Set (Set ι)} (hA : DependsOnCoordinates S A)
    (hB : DependsOnCoordinates T B) (hAm : MeasurableSet A)
    (hBm : MeasurableSet B) :
    IndepSet A B setBer((Set.univ : Set ι), p) := by
  let f : (ι → ℝ) → Set ι := thresholdConfiguration p
  have hpreA : MeasurableSet[coordSigma ι S] (f ⁻¹' A) :=
    hA.measurableSet_thresholdConfiguration_preimage hAm p
  have hpreB : MeasurableSet[coordSigma ι T] (f ⁻¹' B) :=
    hB.measurableSet_thresholdConfiguration_preimage hBm p
  have hindep : IndepSet (f ⁻¹' A) (f ⁻¹' B) (couplingMeasure ι) :=
    indepSet_of_measurableSet_coordSigma_of_disjoint hST hpreA hpreB
  have hmap := couplingMeasure_map_thresholdConfiguration (ι := ι) p
  rw [indepSet_iff_measure_inter_eq_mul
      (μ := setBer((Set.univ : Set ι), p)) hAm hBm,
    ← hmap,
    Measure.map_apply (measurable_thresholdConfiguration p) (hAm.inter hBm),
    Measure.map_apply (measurable_thresholdConfiguration p) hAm,
    Measure.map_apply (measurable_thresholdConfiguration p) hBm]
  simpa only [Set.preimage_inter] using hindep.measure_inter_eq_mul

/-- Real-probability factorization form of arbitrary-block Bernoulli independence. -/
theorem setBernoulli_real_inter_eq_mul_of_dependsOnCoordinates
    (p : I) {S T : Set ι} (hST : Disjoint S T)
    {A B : Set (Set ι)} (hA : DependsOnCoordinates S A)
    (hB : DependsOnCoordinates T B) (hAm : MeasurableSet A)
    (hBm : MeasurableSet B) :
    setBer((Set.univ : Set ι), p).real (A ∩ B) =
      setBer((Set.univ : Set ι), p).real A *
        setBer((Set.univ : Set ι), p).real B := by
  have hindep := setBernoulli_indepSet_of_dependsOnCoordinates
    p hST hA hB hAm hBm
  have h := hindep.measure_inter_eq_mul
  rw [Measure.real, h, ENNReal.toReal_mul, ← Measure.real, ← Measure.real]

end Percolation
