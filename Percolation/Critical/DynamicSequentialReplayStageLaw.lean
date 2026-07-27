import Percolation.Critical.DynamicReplayStageLaw

/-!
# Sequentially correct one-slot law for the dynamic replay

The pre-query replay state does not determine future restart successes.  Consequently the outer
cell for a stage is `A ∩ sourceHistory`, and only the *runtime prefix* through the preceding
slots is required to have a terminal history cell contained in that outer cell.  This file
packages that corrected two-level finite partition and proves the null-history-safe one-slot
lower estimate used by Lemma 7.24.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval

namespace DynamicBlockHistoryReplay

variable {d m n : ℕ} {F : Set (Cubic d)} [LinearOrder F]

/-- Correct certificate for one padded slot.  Exact replay freezes the incoming global state;
the existing `LaterSitePrefixCertificate` then partitions the actual semantic past inside that
state by the accumulated history after the first `j` runtime slots. -/
structure SequentialReplayStageCertificate
    (hd : 0 < d) (hmn : 2 * m ≤ n)
    (W : RootRadialSeedProfile d m n) (root : F)
    (p radialIncremented : I) (delta epsilon : ℝ)
    (incremented : RootExtensionThresholdPolicy d)
    (history : List (F × Bool)) (v : F)
    (A : Set (CubicEdge d → ℝ)) (j : ℕ) where
  outer_measurable : MeasurableSet A
  replay_exact : ∀ X ∈ A, ∀ Y,
    Y ∈ (replay hd hmn W root p radialIncremented delta incremented X history
      ).source.historyProfile.event →
    replay hd hmn W root p radialIncremented delta incremented Y history =
      replay hd hmn W root p radialIncremented delta incremented X history
  replay_self : ∀ X ∈ A,
    X ∈ (replay hd hmn W root p radialIncremented delta incremented X history
      ).source.historyProfile.event
  epsilon_nonneg : 0 ≤ epsilon
  active : ∀ c : RepresentedReplayStateIndex hd hmn W root p radialIncremented delta
      incremented history A,
    let fullHistory := [(root, true)] ++ canonicalSuffix (d := d) (F := F) root history
    let S := c.1.1
    let queried := canonicalQueryFromFullHistory root fullHistory
    let seed := inletSeed hd root fullHistory queried S
    let incoming := incomingDirection hd root fullHistory queried
    let first := firstFlip hd root fullHistory queried S
    let directions := siteDirectionOrder hd root fullHistory queried
    ∀ _hj : j < directions.length,
      AdaptiveSiteExploration.LaterSitePrefixCertificate hmn S.source
        seed.physicalCenter (grimmettMarstrandSiteCenter (m + n + 1) queried.1)
        incoming first unusedSecondFlip p delta epsilon incremented directions j
        (representedReplayCell c)

namespace SequentialReplayStageCertificate

variable {p radialIncremented : I} {delta epsilon : ℝ}
  {incremented : RootExtensionThresholdPolicy d}
  {W : RootRadialSeedProfile d m n} {root : F}
  {history : List (F × Bool)} {v : F}
  {A : Set (CubicEdge d → ℝ)} {j : ℕ}
  {hd : 0 < d} {hmn : 2 * m ≤ n}

/-- The represented outer cell is measurable because it is the explicit intersection of the
semantic past and one finite accumulated-history cylinder. -/
theorem measurableSet_representedReplayCell
    (C : SequentialReplayStageCertificate hd hmn W root p radialIncremented delta epsilon
      incremented history v A j)
    (c : RepresentedReplayStateIndex hd hmn W root p radialIncremented delta
      incremented history A) :
    MeasurableSet (representedReplayCell c) := by
  exact C.outer_measurable.inter c.1.1.source.historyProfile.measurableSet_event

end SequentialReplayStageCertificate

/-- Slice of one represented incoming replay cell by the fixed-state padded slot event. -/
noncomputable def sequentialReplayStageSlice
    (hd : 0 < d) (hmn : 2 * m ≤ n)
    (W : RootRadialSeedProfile d m n) (root : F)
    (p radialIncremented : I) (delta : ℝ)
    (incremented : RootExtensionThresholdPolicy d)
    (history : List (F × Bool)) (v : F)
    (A : Set (CubicEdge d → ℝ))
    (c : RepresentedReplayStateIndex hd hmn W root p radialIncremented delta
      incremented history A) (j : ℕ) : Set (CubicEdge d → ℝ) :=
  representedReplayCell c ∩
    statePaddedStageSuccess hd hmn root p delta incremented
      ([(root, true)] ++ canonicalSuffix (d := d) (F := F) root history) v c.1.1 j

/-- Summing the represented slices gives exactly the semantic next-slot event. -/
theorem iUnion_sequentialReplayStageSlice_eq
    (hd : 0 < d) (hmn : 2 * m ≤ n)
    (W : RootRadialSeedProfile d m n) (root : F)
    (p radialIncremented : I) (delta : ℝ)
    (incremented : RootExtensionThresholdPolicy d)
    (history : List (F × Bool)) (v : F)
    (A : Set (CubicEdge d → ℝ)) (j : ℕ)
    (hreplay : ∀ X ∈ A, ∀ Y,
      Y ∈ (replay hd hmn W root p radialIncremented delta incremented X history
        ).source.historyProfile.event →
      replay hd hmn W root p radialIncremented delta incremented Y history =
        replay hd hmn W root p radialIncremented delta incremented X history)
    (hself : ∀ X ∈ A,
      X ∈ (replay hd hmn W root p radialIncremented delta incremented X history
        ).source.historyProfile.event) :
    (⋃ c : RepresentedReplayStateIndex hd hmn W root p radialIncremented delta
        incremented history A,
      sequentialReplayStageSlice hd hmn W root p radialIncremented delta incremented
        history v A c j) =
      A ∩ paddedStageSuccess hd hmn W root p radialIncremented delta incremented
        history v j := by
  ext X
  constructor
  · intro hX
    rw [Set.mem_iUnion] at hX
    obtain ⟨c, hX⟩ := hX
    change X ∈ representedReplayCell c ∩
      statePaddedStageSuccess hd hmn root p delta incremented
        ([(root, true)] ++ canonicalSuffix (d := d) (F := F) root history) v c.1.1 j at hX
    obtain ⟨⟨hXA, hXsource⟩, hXsuccess⟩ := hX
    obtain ⟨Y, hYA, hYstate⟩ := c.2
    have hXstate :
        replay hd hmn W root p radialIncremented delta incremented X history = c.1.1 := by
      rw [← hYstate]
      exact hreplay Y hYA X (by simpa [hYstate] using hXsource)
    refine ⟨hXA, ?_⟩
    simpa [sequentialReplayStageSlice, statePaddedStageSuccess, paddedStageSuccess,
      hXstate] using hXsuccess
  · rintro ⟨hXA, hXsuccess⟩
    let S := replay hd hmn W root p radialIncremented delta incremented X history
    have hSmem : S ∈ replayStateFinset hd hmn W root p radialIncremented delta
        incremented history := by
      rw [mem_replayStateFinset_iff]
      exact ⟨X, rfl⟩
    let c : RepresentedReplayStateIndex hd hmn W root p radialIncremented delta
        incremented history A := ⟨⟨S, hSmem⟩, X, hXA, rfl⟩
    rw [Set.mem_iUnion]
    refine ⟨c, ?_⟩
    change X ∈ representedReplayCell c ∩
      statePaddedStageSuccess hd hmn root p delta incremented
        ([(root, true)] ++ canonicalSuffix (d := d) (F := F) root history) v c.1.1 j
    refine ⟨⟨hXA, by simpa [S] using hself X hXA⟩, ?_⟩
    simpa [statePaddedStageSuccess, paddedStageSuccess, S, c] using hXsuccess

variable {p radialIncremented : I} {delta epsilon : ℝ}
  {incremented : RootExtensionThresholdPolicy d}
  {W : RootRadialSeedProfile d m n} {root : F}
  {history : List (F × Bool)} {v : F}
  {A : Set (CubicEdge d → ℝ)} {j : ℕ}
  {hd : 0 < d} {hmn : 2 * m ≤ n}

private theorem mem_statePaddedStageSuccess_iff_runtimeQuery_of_lt
    (c : RepresentedReplayStateIndex hd hmn W root p radialIncremented delta
      incremented history A) (j : ℕ)
    (hj : j < (siteDirectionOrder hd root
      ([(root, true)] ++ canonicalSuffix (d := d) (F := F) root history)
      (canonicalQueryFromFullHistory root
        ([(root, true)] ++ canonicalSuffix (d := d) (F := F) root history))).length)
    (X : CubicEdge d → ℝ) :
    X ∈ statePaddedStageSuccess hd hmn root p delta incremented
        ([(root, true)] ++ canonicalSuffix (d := d) (F := F) root history) v c.1.1 j ↔
      let fullHistory :=
        [(root, true)] ++ canonicalSuffix (d := d) (F := F) root history
      let S := c.1.1
      let queried := canonicalQueryFromFullHistory root fullHistory
      let seed := inletSeed hd root fullHistory queried S
      let incoming := incomingDirection hd root fullHistory queried
      let first := firstFlip hd root fullHistory queried S
      let directions := siteDirectionOrder hd root fullHistory queried
      let Rj := LaterSiteRuntime.runFrom hmn seed.physicalCenter incoming first
        unusedSecondFlip p delta incremented X
          (siteInitialRuntime (m + n + 1) queried S seed) 0 (directions.take j)
      X ∈ (Rj.restartQuery seed.physicalCenter incoming first unusedSecondFlip
        directions[j] j).successEvent m n p delta := by
  unfold statePaddedStageSuccess
  change (if _h : j < (siteDirectionOrder hd root
    ([(root, true)] ++ canonicalSuffix (d := d) (F := F) root history)
    (canonicalQueryFromFullHistory root
      ([(root, true)] ++ canonicalSuffix (d := d) (F := F) root history))).length then _ else True) ↔ _
  rw [dif_pos hj]

private theorem sequentialReplayStageSlice_eq_prefixSemanticSuccess_of_lt
    (c : RepresentedReplayStateIndex hd hmn W root p radialIncremented delta
      incremented history A)
    (j : ℕ)
    (hj : j < (siteDirectionOrder hd root
      ([(root, true)] ++ canonicalSuffix (d := d) (F := F) root history)
      (canonicalQueryFromFullHistory root
        ([(root, true)] ++ canonicalSuffix (d := d) (F := F) root history))).length) :
    sequentialReplayStageSlice hd hmn W root p radialIncremented delta incremented
        history v A c j =
      let fullHistory := [(root, true)] ++ canonicalSuffix (d := d) (F := F) root history
      let S := c.1.1
      let queried := canonicalQueryFromFullHistory root fullHistory
      let seed := inletSeed hd root fullHistory queried S
      let incoming := incomingDirection hd root fullHistory queried
      let first := firstFlip hd root fullHistory queried S
      let directions := siteDirectionOrder hd root fullHistory queried
      {X | X ∈ representedReplayCell (hd := hd) (hmn := hmn) (W := W) (root := root)
          (p := p) (radialIncremented := radialIncremented) (delta := delta)
          (incremented := incremented) (history := history) (A := A) c ∧
        X ∈ ((LaterSiteRuntime.prefixRuntime hmn S.source seed.physicalCenter
          (grimmettMarstrandSiteCenter (m + n + 1) queried.1) incoming first
          unusedSecondFlip p delta incremented directions j X).restartQuery
            seed.physicalCenter incoming first unusedSecondFlip directions[j] j).successEvent
              m n p delta} := by
  ext X
  unfold sequentialReplayStageSlice
  rw [Set.mem_inter_iff]
  constructor
  · rintro ⟨hXcell, hXsuccess⟩
    refine ⟨hXcell, ?_⟩
    rw [mem_statePaddedStageSuccess_iff_runtimeQuery_of_lt c j hj] at hXsuccess
    simpa only [LaterSiteRuntime.prefixRuntime] using hXsuccess
  · rintro ⟨hXcell, hXsuccess⟩
    refine ⟨hXcell, ?_⟩
    rw [mem_statePaddedStageSuccess_iff_runtimeQuery_of_lt c j hj]
    simpa only [LaterSiteRuntime.prefixRuntime] using hXsuccess

namespace SequentialReplayStageCertificate

variable {p radialIncremented : I} {delta epsilon : ℝ}
  {incremented : RootExtensionThresholdPolicy d}
  {W : RootRadialSeedProfile d m n} {root : F}
  {history : List (F × Bool)} {v : F}
  {A : Set (CubicEdge d → ℝ)} {j : ℕ}
  {hd : 0 < d} {hmn : 2 * m ≤ n}

private theorem stageSlice_measurable_and_lower_of_lt
    (C : SequentialReplayStageCertificate hd hmn W root p radialIncremented delta epsilon
      incremented history v A j)
    (c : RepresentedReplayStateIndex hd hmn W root p radialIncremented delta
      incremented history A)
    (hj : j < (siteDirectionOrder hd root
      ([(root, true)] ++ canonicalSuffix (d := d) (F := F) root history)
      (canonicalQueryFromFullHistory root
        ([(root, true)] ++ canonicalSuffix (d := d) (F := F) root history))).length) :
    MeasurableSet (sequentialReplayStageSlice hd hmn W root p radialIncremented delta
        incremented history v A c j) ∧
      (1 - epsilon) * (couplingMeasure (CubicEdge d)).real
          (representedReplayCell (hd := hd) (hmn := hmn) (W := W) (root := root)
            (p := p) (radialIncremented := radialIncremented) (delta := delta)
            (incremented := incremented) (history := history) (A := A) c) ≤
        (couplingMeasure (CubicEdge d)).real
          (sequentialReplayStageSlice hd hmn W root p radialIncremented delta
            incremented history v A c j) := by
  rw [sequentialReplayStageSlice_eq_prefixSemanticSuccess_of_lt c j hj]
  let fullHistory := [(root, true)] ++ canonicalSuffix (d := d) (F := F) root history
  let S := c.1.1
  let queried := canonicalQueryFromFullHistory root fullHistory
  let seed := inletSeed hd root fullHistory queried S
  let incoming := incomingDirection hd root fullHistory queried
  let first := firstFlip hd root fullHistory queried S
  let directions := siteDirectionOrder hd root fullHistory queried
  let Acell := representedReplayCell (hd := hd) (hmn := hmn) (W := W) (root := root)
    (p := p) (radialIncremented := radialIncremented) (delta := delta)
    (incremented := incremented) (history := history) (A := A) c
  let D := C.active c hj
  have h := AdaptiveSiteExploration.laterSitePrefixSemantic_measurable_and_lower
    hmn S.source seed.physicalCenter
      (grimmettMarstrandSiteCenter (m + n + 1) queried.1) incoming first
      unusedSecondFlip p delta epsilon incremented
      D.hmono directions j D.hj Acell D.hnonempty D.hAcurrent D.hAnonnegative D.hstable
        D.hadds D.hfreshPrefix D.hTargetFresh D.hrestart
  simpa only [fullHistory, S, queried, seed, incoming, first, directions, Acell] using h

/-- Each represented slice is measurable and satisfies the local `(1-ε)` lower bound. -/
theorem stageSlice_measurable_and_lower
    (C : SequentialReplayStageCertificate hd hmn W root p radialIncremented delta epsilon
      incremented history v A j)
    (c : RepresentedReplayStateIndex hd hmn W root p radialIncremented delta
      incremented history A) :
    MeasurableSet (sequentialReplayStageSlice hd hmn W root p radialIncremented delta
        incremented history v A c j) ∧
      (1 - epsilon) * (couplingMeasure (CubicEdge d)).real
          (representedReplayCell c) ≤
        (couplingMeasure (CubicEdge d)).real
          (sequentialReplayStageSlice hd hmn W root p radialIncremented delta
            incremented history v A c j) := by
  let directions := siteDirectionOrder hd root
    ([(root, true)] ++ canonicalSuffix (d := d) (F := F) root history)
    (canonicalQueryFromFullHistory root
      ([(root, true)] ++ canonicalSuffix (d := d) (F := F) root history))
  by_cases hj : j < directions.length
  · exact C.stageSlice_measurable_and_lower_of_lt c (by simpa [directions] using hj)
  · have hslice : sequentialReplayStageSlice hd hmn W root p radialIncremented delta
        incremented history v A c j = representedReplayCell c := by
      ext X
      unfold sequentialReplayStageSlice statePaddedStageSuccess
      change (_ ∧ (if _h : j < directions.length then _ else True)) ↔ _
      rw [dif_neg hj]
      simp
    rw [hslice]
    constructor
    · exact C.measurableSet_representedReplayCell c
    · calc
        (1 - epsilon) * (couplingMeasure (CubicEdge d)).real
            (representedReplayCell c) ≤
          1 * (couplingMeasure (CubicEdge d)).real
            (representedReplayCell c) :=
              mul_le_mul_of_nonneg_right (by linarith [C.epsilon_nonneg]) measureReal_nonneg
        _ = (couplingMeasure (CubicEdge d)).real
            (representedReplayCell c) := one_mul _

set_option maxHeartbeats 800000 in
/-- Correct global one-slot law, with the semantic past retained inside every incoming replay
cell and refined by the literal runtime-prefix history. -/
theorem inter_paddedStageSuccess_measurable_and_lower
    (C : SequentialReplayStageCertificate hd hmn W root p radialIncremented delta epsilon
      incremented history v A j) :
    MeasurableSet
        (A ∩ paddedStageSuccess hd hmn W root p radialIncremented delta incremented
          history v j) ∧
      (1 - epsilon) * (couplingMeasure (CubicEdge d)).real A ≤
        (couplingMeasure (CubicEdge d)).real
          (A ∩ paddedStageSuccess hd hmn W root p radialIncremented delta incremented
            history v j) := by
  let success := fun c : RepresentedReplayStateIndex hd hmn W root p radialIncremented delta
      incremented history A ↦
    sequentialReplayStageSlice hd hmn W root p radialIncremented delta incremented
      history v A c j
  have hunion : finiteSuccessSliceUnion success =
      A ∩ paddedStageSuccess hd hmn W root p radialIncremented delta incremented
        history v j := by
    exact iUnion_sequentialReplayStageSlice_eq hd hmn W root p radialIncremented delta
      incremented history v A j C.replay_exact C.replay_self
  constructor
  · rw [← hunion]
    exact measurableSet_finiteSuccessSliceUnion fun c ↦
      (C.stageSlice_measurable_and_lower c).1
  · rw [← hunion]
    apply mul_measureReal_representedReplayCells_le_successUnion hd hmn W root p
      radialIncremented delta incremented history A (1 - epsilon) C.replay_exact
        C.replay_self success
    · exact C.measurableSet_representedReplayCell
    · intro c
      exact (C.stageSlice_measurable_and_lower c).1
    · intro c
      exact Set.inter_subset_left
    · intro c
      exact (C.stageSlice_measurable_and_lower c).2

end SequentialReplayStageCertificate

end DynamicBlockHistoryReplay

end Percolation
