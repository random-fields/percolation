import Percolation.Critical.DynamicLaterSiteState

/-!
# History stability of the literal non-root schedule

The mixed witness selected at a non-root restart is part of the explored certificate.  Hence
the complete dependent witness profile is constant on the accumulated finite-history cell
produced by the source recursion.  This is the semantic invariant needed for the exact finite
partitions in the adaptive coarse-site program.
-/

namespace Percolation

open scoped unitInterval

namespace LaterSiteMixedSeedProfile

/-- Under a monotone threshold policy, the final accumulated-history cell refines the incoming
history cell. -/
theorem runExtensions_historyProfile_event_subset
    {d m n : ℕ} {hd : 0 < d} {incoming : CubicDirection d}
    (W : LaterSiteMixedSeedProfile d m n hd incoming)
    (inletCenter : Cubic d) (firstFlip secondFlip : Fin d → Bool)
    (p : I) (incremented : RootExtensionThresholdPolicy d)
    (hmono : ∀ S a e, S.lower e ≤ incremented S a e)
    (X : CubicEdge d → ℝ) (S : SourceFiniteEdgeRevealState d)
    (slots : List (LaterSiteSlot d)) :
    (W.runExtensions inletCenter firstFlip secondFlip p incremented X S slots
      ).historyProfile.event ⊆ S.historyProfile.event := by
  induction slots generalizing S with
  | nil => exact Set.Subset.rfl
  | cons k rest ih =>
      let a := laterSiteSlotDirection hd incoming k
      let center := W.slotCenter inletCenter firstFlip secondFlip k
      let flip := W.slotTransverseFlip firstFlip secondFlip k
      let Q := S.framedQuery center a flip
      let S' := S.next (Q.restartSupport m n) p (incremented S a) X
      exact (ih (S := S')).trans
        (S.next_historyProfile_event_subset_historyProfile_event
          (Q.restartSupport m n) p (incremented S a) X (hmono S a))

/-- A realization remains in the accumulated-history cell produced by its own literal
non-root recursion on the probability-one common-uniform support. -/
theorem mem_runExtensions_historyProfile
    {d m n : ℕ} {hd : 0 < d} {incoming : CubicDirection d}
    (W : LaterSiteMixedSeedProfile d m n hd incoming)
    (inletCenter : Cubic d) (firstFlip secondFlip : Fin d → Bool)
    (p : I) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) (S : SourceFiniteEdgeRevealState d)
    (slots : List (LaterSiteSlot d))
    (hnonneg : X ∈ SourceFiniteEdgeRevealState.nonnegativeCouplingEvent)
    (hcurrent : X ∈ S.historyProfile.event) :
    X ∈ (W.runExtensions inletCenter firstFlip secondFlip
      p incremented X S slots).historyProfile.event := by
  induction slots generalizing S with
  | nil => exact hcurrent
  | cons k rest ih =>
      let a := laterSiteSlotDirection hd incoming k
      let center := W.slotCenter inletCenter firstFlip secondFlip k
      let flip := W.slotTransverseFlip firstFlip secondFlip k
      let Q := S.framedQuery center a flip
      exact ih
        (S := S.next (Q.restartSupport m n) p (incremented S a) X)
        (S.mem_next_historyProfile (Q.restartSupport m n) p
          (incremented S a) X hcurrent hnonneg)

/-- For fixed geometric and witness data, a finite non-root schedule has finite state range
whenever its incoming source state does. -/
theorem finite_range_runExtensions
    {d m n : ℕ} {hd : 0 < d} {incoming : CubicDirection d}
    (W : LaterSiteMixedSeedProfile d m n hd incoming)
    (inletCenter : Cubic d) (firstFlip secondFlip : Fin d → Bool)
    (p : I) (incremented : RootExtensionThresholdPolicy d)
    (state : (CubicEdge d → ℝ) → SourceFiniteEdgeRevealState d)
    (slots : List (LaterSiteSlot d))
    (hstate : (Set.range state).Finite) :
    (Set.range fun X ↦ W.runExtensions inletCenter firstFlip secondFlip
      p incremented X (state X) slots).Finite := by
  induction slots generalizing state with
  | nil => simpa using hstate
  | cons k rest ih =>
      let a := laterSiteSlotDirection hd incoming k
      let center := W.slotCenter inletCenter firstFlip secondFlip k
      let flip := W.slotTransverseFlip firstFlip secondFlip k
      let nextState : (CubicEdge d → ℝ) → SourceFiniteEdgeRevealState d := fun X ↦
        let S := state X
        let Q := S.framedQuery center a flip
        S.next (Q.restartSupport m n) p (incremented S a) X
      have hnext : (Set.range nextState).Finite := by
        apply SourceFiniteEdgeRevealState.finite_range_next_of_finite_range
          state (fun S ↦ (S.framedQuery center a flip).restartSupport m n)
          p (fun S ↦ incremented S a) hstate
      simpa [runExtensions, nextState, a, center, flip] using ih nextState hnext

/-- Every named mixed witness in a successful prefix remains valid throughout its terminal
accumulated-history cell. -/
theorem runMixedWitnesses_of_mem_historyProfile
    {d m n : ℕ} {hd : 0 < d} {incoming : CubicDirection d}
    (W : LaterSiteMixedSeedProfile d m n hd incoming)
    (inletCenter : Cubic d) (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (hmono : ∀ S a e, S.lower e ≤ incremented S a e)
    (X Y : CubicEdge d → ℝ) (S : SourceFiniteEdgeRevealState d)
    (slots : List (LaterSiteSlot d))
    (hadds : ∀ j (hj : j < slots.length) e,
      let state := W.runExtensions inletCenter firstFlip secondFlip
        p incremented X S (slots.take j)
      let k := slots[j]
      let a := laterSiteSlotDirection hd incoming k
      (incremented state a e : ℝ) = (state.lower e : ℝ) + delta)
    (hfresh : ∀ j (hj : j < slots.length),
      let state := W.runExtensions inletCenter firstFlip secondFlip
        p incremented X S (slots.take j)
      let k := slots[j]
      let a := laterSiteSlotDirection hd incoming k
      let center := W.slotCenter inletCenter firstFlip secondFlip k
      let flip := W.slotTransverseFlip firstFlip secondFlip k
      let F := cubicRestartFrameIso center a flip
      Disjoint (cubicEdgeEndpointVertices (state.referenceExploredEdges F))
        (cubicEdgeEndpointVertices (seededBoundaryTargetSupport d a.1 m n)))
    (hsuccess : W.runMixedWitnesses inletCenter firstFlip secondFlip
      p delta incremented X S slots)
    (hY : Y ∈ (W.runExtensions inletCenter firstFlip secondFlip
      p incremented X S slots).historyProfile.event) :
    W.runMixedWitnesses inletCenter firstFlip secondFlip
      p delta incremented Y S slots := by
  induction slots generalizing S with
  | nil => trivial
  | cons k rest ih =>
      let a := laterSiteSlotDirection hd incoming k
      let center := W.slotCenter inletCenter firstFlip secondFlip k
      let flip := W.slotTransverseFlip firstFlip secondFlip k
      let Q := S.framedQuery center a flip
      let SX := S.next (Q.restartSupport m n) p (incremented S a) X
      let SY := S.next (Q.restartSupport m n) p (incremented S a) Y
      have hYnext : Y ∈ SX.historyProfile.event := by
        exact W.runExtensions_historyProfile_event_subset inletCenter firstFlip secondFlip
          p incremented hmono X SX rest hY
      have hfreshFirst :
          let F := cubicRestartFrameIso center a flip
          Disjoint (cubicEdgeEndpointVertices (S.referenceExploredEdges F))
            (cubicEdgeEndpointVertices (seededBoundaryTargetSupport d a.1 m n)) := by
        simpa [a, center, flip] using hfresh 0 (by simp)
      have hfirstY : (W.witness k).IsMixedRestartWitness
          Q.region p Q.beta delta
          (cubicGraphIsoCouplingReindex
            (cubicRestartFrameIso center a flip) Y) := by
        apply S.mixedWitness_of_mem_nextHistoryProfile
          center a flip p delta (incremented S a) X Y (W.witness k)
          hfreshFirst
        · intro e _he
          rw [S.framedQuery_physicalBoundaryThreshold]
          simpa [a, center, flip] using hadds 0 (by simp) e
        · exact hsuccess.1
        · exact hYnext
      have hstate : SY = SX := by
        exact S.next_eq_of_mem_next_historyProfile
          (Q.restartSupport m n) p (incremented S a) X Y hYnext
      refine ⟨hfirstY, ?_⟩
      change W.runMixedWitnesses inletCenter firstFlip secondFlip
        p delta incremented Y SY rest
      rw [hstate]
      apply ih (S := SX)
      · intro j hj e
        have hs := hadds (j + 1) (by simp; omega) e
        simpa [a, center, flip, Q, SX, List.take_succ_cons,
          runExtensions] using hs
      · intro j hj
        have hs := hfresh (j + 1) (by simp; omega)
        simpa [a, center, flip, Q, SX, List.take_succ_cons,
          runExtensions] using hs
      · exact hsuccess.2
      · exact hY

end LaterSiteMixedSeedProfile

end Percolation
