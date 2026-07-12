import Percolation.Critical.ExplorationHistory

/-!
# Reindexing symmetry of the common uniform coupling

Dynamic steering repeatedly translates, permutes, and reflects the lattice.  The common i.i.d.
uniform labels are invariant under the corresponding edge permutation; this file derives that
fact from the generic infinite-product projection theorem.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval

/-- Precompose a coordinate field by an equivalence of index types. -/
def couplingReindex {alpha beta : Type*} (e : alpha ≃ beta)
    (X : beta → ℝ) : alpha → ℝ :=
  fun a ↦ X (e a)

theorem measurable_couplingReindex {alpha beta : Type*} (e : alpha ≃ beta) :
    Measurable (couplingReindex e : (beta → ℝ) → alpha → ℝ) := by
  unfold couplingReindex
  fun_prop

/-- I.i.d. uniform product labels are invariant under arbitrary coordinate equivalences. -/
theorem couplingMeasure_map_reindex {alpha beta : Type*} (e : alpha ≃ beta) :
    (couplingMeasure beta).map (couplingReindex e) = couplingMeasure alpha := by
  unfold couplingMeasure couplingReindex
  simpa using infinitePi_map_precomp_embedding e.toEmbedding
    (fun _ : beta ↦ volume.restrict (Set.Icc (0 : ℝ) 1))

theorem couplingMeasure_real_preimage_reindex
    {alpha : Type*} (e : alpha ≃ alpha) {A : Set (alpha → ℝ)}
    (hA : MeasurableSet A) :
    (couplingMeasure alpha).real (couplingReindex e ⁻¹' A) =
      (couplingMeasure alpha).real A := by
  calc
    (couplingMeasure alpha).real (couplingReindex e ⁻¹' A) =
        ((couplingMeasure alpha).map (couplingReindex e)).real A := by
      simp only [measureReal_def]
      rw [Measure.map_apply (measurable_couplingReindex e) hA]
    _ = (couplingMeasure alpha).real A := by
      rw [couplingMeasure_map_reindex e]

theorem thresholdConfiguration_couplingReindex_mem_iff
    {alpha beta : Type*} (e : alpha ≃ beta) (p : I)
    (X : beta → ℝ) (a : alpha) :
    a ∈ thresholdConfiguration p (couplingReindex e X) ↔
      e a ∈ thresholdConfiguration p X :=
  Iff.rfl

/-- Reindex uniform edge labels along a cubic graph automorphism. -/
def cubicGraphIsoCouplingReindex {d : ℕ}
    (phi : cubicGraph d ≃g cubicGraph d)
    (X : CubicEdge d → ℝ) : CubicEdge d → ℝ :=
  couplingReindex phi.mapEdgeSet X

/-- Thresholding reindexed common-uniform labels is exactly configuration pullback along the
same graph automorphism. -/
theorem thresholdConfiguration_cubicGraphIsoCouplingReindex
    {d : ℕ} (phi : cubicGraph d ≃g cubicGraph d) (p : I)
    (X : CubicEdge d → ℝ) :
    thresholdConfiguration p (cubicGraphIsoCouplingReindex phi X) =
      cubicGraphIsoConfigurationPullback phi (thresholdConfiguration p X) := by
  ext e
  rfl

theorem measurable_cubicGraphIsoCouplingReindex {d : ℕ}
    (phi : cubicGraph d ≃g cubicGraph d) :
    Measurable (cubicGraphIsoCouplingReindex phi) :=
  measurable_couplingReindex phi.mapEdgeSet

theorem couplingMeasure_real_preimage_cubicGraphIsoReindex
    {d : ℕ} (phi : cubicGraph d ≃g cubicGraph d)
    {A : Set (CubicEdge d → ℝ)} (hA : MeasurableSet A) :
    (couplingMeasure (CubicEdge d)).real
        (cubicGraphIsoCouplingReindex phi ⁻¹' A) =
      (couplingMeasure (CubicEdge d)).real A :=
  couplingMeasure_real_preimage_reindex phi.mapEdgeSet hA

/-- Transport an event on uniform labels through a cubic graph automorphism. -/
def cubicGraphIsoCouplingTransportEvent {d : ℕ}
    (phi : cubicGraph d ≃g cubicGraph d)
    (A : Set (CubicEdge d → ℝ)) : Set (CubicEdge d → ℝ) :=
  cubicGraphIsoCouplingReindex phi ⁻¹' A

theorem measurableSet_cubicGraphIsoCouplingTransportEvent
    {d : ℕ} (phi : cubicGraph d ≃g cubicGraph d)
    {A : Set (CubicEdge d → ℝ)} (hA : MeasurableSet A) :
    MeasurableSet (cubicGraphIsoCouplingTransportEvent phi A) :=
  hA.preimage (measurable_cubicGraphIsoCouplingReindex phi)

theorem cubicGraphIsoCouplingTransportEvent_inter
    {d : ℕ} (phi : cubicGraph d ≃g cubicGraph d)
    (A H : Set (CubicEdge d → ℝ)) :
    cubicGraphIsoCouplingTransportEvent phi (A ∩ H) =
      cubicGraphIsoCouplingTransportEvent phi A ∩
        cubicGraphIsoCouplingTransportEvent phi H :=
  Set.preimage_inter

theorem couplingMeasure_real_cubicGraphIsoTransportEvent
    {d : ℕ} (phi : cubicGraph d ≃g cubicGraph d)
    {A : Set (CubicEdge d → ℝ)} (hA : MeasurableSet A) :
    (couplingMeasure (CubicEdge d)).real
        (cubicGraphIsoCouplingTransportEvent phi A) =
      (couplingMeasure (CubicEdge d)).real A :=
  couplingMeasure_real_preimage_cubicGraphIsoReindex phi hA

/-- Ratio-free conditional success bounds are invariant under every cubic graph automorphism. -/
theorem historySuccessLowerBound_cubicGraphIsoTransport
    {d : ℕ} (phi : cubicGraph d ≃g cubicGraph d)
    {success history : Set (CubicEdge d → ℝ)}
    (hsuccess : MeasurableSet success) (hhistory : MeasurableSet history)
    {gamma : ℝ}
    (h : HistorySuccessLowerBound (couplingMeasure (CubicEdge d))
      success history gamma) :
    HistorySuccessLowerBound (couplingMeasure (CubicEdge d))
      (cubicGraphIsoCouplingTransportEvent phi success)
      (cubicGraphIsoCouplingTransportEvent phi history) gamma := by
  unfold HistorySuccessLowerBound at h ⊢
  rw [← cubicGraphIsoCouplingTransportEvent_inter]
  rw [couplingMeasure_real_cubicGraphIsoTransportEvent phi hhistory,
    couplingMeasure_real_cubicGraphIsoTransportEvent phi (hsuccess.inter hhistory)]
  exact h

end Percolation
