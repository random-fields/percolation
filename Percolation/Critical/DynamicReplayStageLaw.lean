import Percolation.Critical.DynamicPartitionSigma

/-!
# One-slot probability law for the concrete dynamic replay

The executable Chapter 7 oracle chooses its restart geometry from the complete replay state.
That state is random, so a single source restart slot is not itself one fixed cylinder event.
This file partitions an outer history into its finitely many stable replay states and identifies
the resulting cellwise union with the literal `paddedStageSuccess` event.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval

namespace DynamicBlockHistoryReplay

variable {d m n : ℕ} {F : Set (Cubic d)} [LinearOrder F]

/-- The semantic restart query selected by one fixed global replay state. -/
noncomputable def stateRuntimeQuerySuccess
    (hd : 0 < d) (hmn : 2 * m ≤ n) (root : F) (p : I) (delta : ℝ)
    (incremented : RootExtensionThresholdPolicy d)
    (fullHistory : List (F × Bool)) (v : F)
    (S : DynamicBlockHistoryState d F) (j : ℕ) (a : CubicDirection d) :
    Set (CubicEdge d → ℝ) :=
  let queried := canonicalQueryFromFullHistory root fullHistory
  let seed := inletSeed hd root fullHistory queried S
  let incoming := incomingDirection hd root fullHistory queried
  let first := firstFlip hd root fullHistory queried S
  LaterSiteRuntime.prefixQuerySuccessEvent hmn S.source seed.physicalCenter
    (grimmettMarstrandSiteCenter (m + n + 1) queried.1) incoming first
    unusedSecondFlip p delta incremented (siteDirectionOrder hd root fullHistory queried) j a

/-- The `j`-th padded restart event when the incoming global replay state is fixed. -/
noncomputable def statePaddedStageSuccess
    (hd : 0 < d) (hmn : 2 * m ≤ n) (root : F)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (fullHistory : List (F × Bool)) (v : F)
    (S : DynamicBlockHistoryState d F) (j : ℕ) :
    Set (CubicEdge d → ℝ) :=
  {X |
    let queried := canonicalQueryFromFullHistory root fullHistory
    let seed := inletSeed hd root fullHistory queried S
    let incoming := incomingDirection hd root fullHistory queried
    let first := firstFlip hd root fullHistory queried S
    let directions := siteDirectionOrder hd root fullHistory queried
    if hj : j < directions.length then
      let Rj := LaterSiteRuntime.runFrom hmn seed.physicalCenter incoming first
        unusedSecondFlip p delta incremented X
          (siteInitialRuntime (m + n + 1) queried S seed) 0 (directions.take j)
      X ∈ (Rj.restartQuery seed.physicalCenter incoming first unusedSecondFlip
        directions[j] j).successEvent m n p delta
    else True}

/-- The active query selected by a fixed replay state and a concrete restart direction. -/
noncomputable def stateActiveQuerySuccess
    (hd : 0 < d) (hmn : 2 * m ≤ n) (root : F) (p : I) (delta : ℝ)
    (incremented : RootExtensionThresholdPolicy d)
    (fullHistory : List (F × Bool)) (v : F)
    (S : DynamicBlockHistoryState d F) (j : ℕ) (a : CubicDirection d) :
    Set (CubicEdge d → ℝ) :=
  stateRuntimeQuerySuccess hd hmn root p delta incremented fullHistory v S j a

/-- The non-padded semantic event for one fixed replay state and one concrete restart
direction.  Naming this event keeps the finite-partition proof opaque at replay call sites. -/
noncomputable def stateActiveStageSuccess
    (hd : 0 < d) (hmn : 2 * m ≤ n) (root : F) (p : I) (delta : ℝ)
    (incremented : RootExtensionThresholdPolicy d)
    (fullHistory : List (F × Bool)) (v : F)
    (S : DynamicBlockHistoryState d F) (j : ℕ) (a : CubicDirection d) :
    Set (CubicEdge d → ℝ) :=
  let queried := canonicalQueryFromFullHistory root fullHistory
  let seed := inletSeed hd root fullHistory queried S
  let incoming := incomingDirection hd root fullHistory queried
  let first := firstFlip hd root fullHistory queried S
  LaterSiteRuntime.prefixSemanticSuccessEvent hmn S.source seed.physicalCenter
    (grimmettMarstrandSiteCenter (m + n + 1) queried.1) incoming first
    unusedSecondFlip p delta incremented (siteDirectionOrder hd root fullHistory queried) j a
      S.source.historyProfile.event

/-- A stable global replay cell sliced by its fixed-state semantic restart event. -/
noncomputable def stableReplayStageSlice
    (hd : 0 < d) (hmn : 2 * m ≤ n)
    (W : RootRadialSeedProfile d m n) (root : F)
    (p radialIncremented : I) (delta : ℝ)
    (incremented : RootExtensionThresholdPolicy d)
    (history : List (F × Bool)) (v : F)
    (A : Set (CubicEdge d → ℝ))
    (c : StableReplayStateIndex hd hmn W root p radialIncremented delta
      incremented history A) (j : ℕ) : Set (CubicEdge d → ℝ) :=
  c.1.1.source.historyProfile.event ∩
    statePaddedStageSuccess hd hmn root p delta incremented
      ([(root, true)] ++ canonicalSuffix root history) v c.1.1 j

/-- Exact semantic identification after summing over all stable global replay cells. -/
theorem stableReplaySuccessUnion_stageSlice_eq
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
        ).source.historyProfile.event)
    (hstable : ∀ X ∈ A,
      (replay hd hmn W root p radialIncremented delta incremented X history
        ).source.historyProfile.event ⊆ A) :
    stableReplaySuccessUnion
        (fun c ↦ stableReplayStageSlice hd hmn W root p radialIncremented delta
          incremented history v A c j) =
      A ∩ paddedStageSuccess hd hmn W root p radialIncremented delta incremented
        history v j := by
  ext X
  constructor
  · intro hX
    rw [stableReplaySuccessUnion, finiteSuccessSliceUnion, Set.mem_iUnion] at hX
    obtain ⟨c, hXcell, hXsuccess⟩ := hX
    have hXA : X ∈ A := c.2.1 hXcell
    obtain ⟨Y, hYA, hYstate⟩ := c.2.2
    have hXstate :
        replay hd hmn W root p radialIncremented delta incremented X history = c.1.1 := by
      rw [← hYstate]
      exact hreplay Y hYA X (by simpa [hYstate] using hXcell)
    refine ⟨hXA, ?_⟩
    simpa [stableReplayStageSlice, statePaddedStageSuccess, paddedStageSuccess,
      hXstate] using hXsuccess
  · rintro ⟨hXA, hXsuccess⟩
    let S := replay hd hmn W root p radialIncremented delta incremented X history
    have hSmem : S ∈ replayStateFinset hd hmn W root p radialIncremented delta
        incremented history := by
      rw [mem_replayStateFinset_iff]
      exact ⟨X, rfl⟩
    let c : StableReplayStateIndex hd hmn W root p radialIncremented delta
        incremented history A :=
      ⟨⟨S, hSmem⟩, hstable X hXA, X, hXA, rfl⟩
    rw [stableReplaySuccessUnion, finiteSuccessSliceUnion, Set.mem_iUnion]
    refine ⟨c, hself X hXA, ?_⟩
    simpa [stableReplayStageSlice, statePaddedStageSuccess, paddedStageSuccess, S, c]
      using hXsuccess

/-- Reachable-state obligations needed to turn every semantic replay slot into the finite
partition supplied by Lemma 7.17.  This is an internal geometry/budget certificate; no
source-facing theorem is allowed to retain it as a hypothesis. -/
structure StableReplayStageCertificate
    (hd : 0 < d) (hmn : 2 * m ≤ n)
    (W : RootRadialSeedProfile d m n) (root : F)
    (p radialIncremented : I) (delta epsilon : ℝ)
    (incremented : RootExtensionThresholdPolicy d)
    (history : List (F × Bool)) (v : F)
    (A : Set (CubicEdge d → ℝ)) where
  replay_exact : ∀ X ∈ A, ∀ Y,
    Y ∈ (replay hd hmn W root p radialIncremented delta incremented X history
      ).source.historyProfile.event →
    replay hd hmn W root p radialIncremented delta incremented Y history =
      replay hd hmn W root p radialIncremented delta incremented X history
  replay_self : ∀ X ∈ A,
    X ∈ (replay hd hmn W root p radialIncremented delta incremented X history
      ).source.historyProfile.event
  replay_stable : ∀ X ∈ A,
    (replay hd hmn W root p radialIncremented delta incremented X history
      ).source.historyProfile.event ⊆ A
  nonnegative : A ⊆ SourceFiniteEdgeRevealState.nonnegativeCouplingEvent
  epsilon_nonneg : 0 ≤ epsilon
  policy_mono : ∀ S a e, S.lower e ≤ incremented S a e
  policy_adds : ∀
    (c : StableReplayStateIndex hd hmn W root p radialIncremented delta
      incremented history A)
    (X : CubicEdge d → ℝ), X ∈ c.1.1.source.historyProfile.event →
    let fullHistory := [(root, true)] ++ canonicalSuffix root history
    let queried := canonicalQueryFromFullHistory root fullHistory
    let seed := inletSeed hd root fullHistory queried c.1.1
    let incoming := incomingDirection hd root fullHistory queried
    let first := firstFlip hd root fullHistory queried c.1.1
    let directions := siteDirectionOrder hd root fullHistory queried
    ∀ l (hl : l < directions.length) e,
      let Rl := LaterSiteRuntime.runFrom hmn seed.physicalCenter incoming first
        unusedSecondFlip p delta incremented X
          (siteInitialRuntime (m + n + 1) queried c.1.1 seed) 0
          (directions.take l)
      let a := directions[l]
      (incremented Rl.source a e : ℝ) = (Rl.source.lower e : ℝ) + delta
  target_fresh : ∀
    (c : StableReplayStateIndex hd hmn W root p radialIncremented delta
      incremented history A)
    (X : CubicEdge d → ℝ), X ∈ c.1.1.source.historyProfile.event →
    let fullHistory := [(root, true)] ++ canonicalSuffix root history
    let queried := canonicalQueryFromFullHistory root fullHistory
    let seed := inletSeed hd root fullHistory queried c.1.1
    let incoming := incomingDirection hd root fullHistory queried
    let first := firstFlip hd root fullHistory queried c.1.1
    let directions := siteDirectionOrder hd root fullHistory queried
    ∀ l (hl : l < directions.length),
      let Rl := LaterSiteRuntime.runFrom hmn seed.physicalCenter incoming first
        unusedSecondFlip p delta incremented X
          (siteInitialRuntime (m + n + 1) queried c.1.1 seed) 0
          (directions.take l)
      let a := directions[l]
      let center := Rl.slotCenterFor seed.physicalCenter a l
      let flip := Rl.slotTransverseFlip incoming first unusedSecondFlip a l
      let frame := cubicRestartFrameIso center a flip
      Disjoint (cubicEdgeEndpointVertices (Rl.source.referenceExploredEdges frame))
        (cubicEdgeEndpointVertices (seededBoundaryTargetSupport d a.1 m n))
  restart_gt : ∀
    (c : StableReplayStateIndex hd hmn W root p radialIncremented delta
      incremented history A)
    (X : CubicEdge d → ℝ), X ∈ c.1.1.source.historyProfile.event →
    let fullHistory := [(root, true)] ++ canonicalSuffix root history
    let queried := canonicalQueryFromFullHistory root fullHistory
    let seed := inletSeed hd root fullHistory queried c.1.1
    let incoming := incomingDirection hd root fullHistory queried
    let first := firstFlip hd root fullHistory queried c.1.1
    let directions := siteDirectionOrder hd root fullHistory queried
    ∀ l (hl : l < directions.length),
      let Rl := LaterSiteRuntime.runFrom hmn seed.physicalCenter incoming first
        unusedSecondFlip p delta incremented X
          (siteInitialRuntime (m + n + 1) queried c.1.1 seed) 0
          (directions.take l)
      let a := directions[l]
      let Q := Rl.restartQuery seed.physicalCenter incoming first unusedSecondFlip a l
      (1 - epsilon) * (couplingMeasure (CubicEdge d)).real
          (Q.boundaryHistoryEvent n) <
        (couplingMeasure (CubicEdge d)).real
          (Q.successEvent m n p delta ∩ Q.boundaryHistoryEvent n)

namespace StableReplayStageCertificate

variable {p radialIncremented : I} {delta epsilon : ℝ}
  {incremented : RootExtensionThresholdPolicy d}
  {W : RootRadialSeedProfile d m n} {root : F}
  {history : List (F × Bool)} {v : F}
  {A : Set (CubicEdge d → ℝ)}
  {hd : 0 < d} {hmn : 2 * m ≤ n}

private theorem stablePrefix_event_subset
    (C : StableReplayStageCertificate hd hmn W root p radialIncremented delta epsilon
      incremented history v A)
    (c : StableReplayStateIndex hd hmn W root p radialIncremented delta
      incremented history A) (j : ℕ) :
    let fullHistory := [(root, true)] ++ canonicalSuffix root history
    let S := c.1.1
    let queried := canonicalQueryFromFullHistory root fullHistory
    let seed := inletSeed hd root fullHistory queried S
    let incoming := incomingDirection hd root fullHistory queried
    let first := firstFlip hd root fullHistory queried S
    let directions := siteDirectionOrder hd root fullHistory queried
    ∀ X ∈ S.source.historyProfile.event,
      (LaterSiteRuntime.prefixRuntime hmn S.source seed.physicalCenter
        (grimmettMarstrandSiteCenter (m + n + 1) queried.1) incoming first
        unusedSecondFlip p delta incremented directions j X).source.historyProfile.event ⊆
          S.source.historyProfile.event := by
  dsimp only
  intro X _hX
  let fullHistory := [(root, true)] ++ canonicalSuffix root history
  let queried := canonicalQueryFromFullHistory root fullHistory
  exact LaterSiteRuntime.runFrom_historyProfile_event_subset hmn
    (inletSeed hd root fullHistory queried c.1.1).physicalCenter
    (incomingDirection hd root fullHistory queried)
    (firstFlip hd root fullHistory queried c.1.1)
    unusedSecondFlip p delta incremented C.policy_mono X
    (siteInitialRuntime (m + n + 1) queried c.1.1
      (inletSeed hd root fullHistory queried c.1.1)) 0
    ((siteDirectionOrder hd root fullHistory queried).take j)

private theorem policy_adds_on_taken_prefix
    (C : StableReplayStageCertificate hd hmn W root p radialIncremented delta epsilon
      incremented history v A)
    (c : StableReplayStateIndex hd hmn W root p radialIncremented delta
      incremented history A) (j : ℕ) :
    let fullHistory := [(root, true)] ++ canonicalSuffix root history
    let S := c.1.1
    let queried := canonicalQueryFromFullHistory root fullHistory
    let seed := inletSeed hd root fullHistory queried S
    let incoming := incomingDirection hd root fullHistory queried
    let first := firstFlip hd root fullHistory queried S
    let directions := siteDirectionOrder hd root fullHistory queried
    ∀ X ∈ S.source.historyProfile.event, ∀ l
      (hl : l < (directions.take j).length) e,
      let Rl := LaterSiteRuntime.runFrom hmn seed.physicalCenter incoming first
        unusedSecondFlip p delta incremented X
          (siteInitialRuntime (m + n + 1) queried S seed) 0
          ((directions.take j).take l)
      let a := (directions.take j)[l]
      (incremented Rl.source a e : ℝ) = (Rl.source.lower e : ℝ) + delta := by
  dsimp only
  intro X hX l hl e
  have hlTake := hl
  rw [List.length_take] at hlTake
  have hlFull : l <
      (siteDirectionOrder hd root ([(root, true)] ++ canonicalSuffix root history)
        (canonicalQueryFromFullHistory root
          ([(root, true)] ++ canonicalSuffix root history))).length := by
    omega
  have hlj : l ≤ j := by omega
  have h := C.policy_adds c X hX l hlFull e
  simpa [List.take_take, Nat.min_eq_left hlj] using h

private theorem target_fresh_on_taken_prefix
    (C : StableReplayStageCertificate hd hmn W root p radialIncremented delta epsilon
      incremented history v A)
    (c : StableReplayStateIndex hd hmn W root p radialIncremented delta
      incremented history A) (j : ℕ) :
    let fullHistory := [(root, true)] ++ canonicalSuffix root history
    let S := c.1.1
    let queried := canonicalQueryFromFullHistory root fullHistory
    let seed := inletSeed hd root fullHistory queried S
    let incoming := incomingDirection hd root fullHistory queried
    let first := firstFlip hd root fullHistory queried S
    let directions := siteDirectionOrder hd root fullHistory queried
    ∀ X ∈ S.source.historyProfile.event, ∀ l
      (hl : l < (directions.take j).length),
      let Rl := LaterSiteRuntime.runFrom hmn seed.physicalCenter incoming first
        unusedSecondFlip p delta incremented X
          (siteInitialRuntime (m + n + 1) queried S seed) 0
          ((directions.take j).take l)
      let a := (directions.take j)[l]
      let center := Rl.slotCenterFor seed.physicalCenter a l
      let flip := Rl.slotTransverseFlip incoming first unusedSecondFlip a l
      let frame := cubicRestartFrameIso center a flip
      Disjoint (cubicEdgeEndpointVertices (Rl.source.referenceExploredEdges frame))
        (cubicEdgeEndpointVertices (seededBoundaryTargetSupport d a.1 m n)) := by
  dsimp only
  intro X hX l hl
  have hlTake := hl
  rw [List.length_take] at hlTake
  have hlFull : l <
      (siteDirectionOrder hd root ([(root, true)] ++ canonicalSuffix root history)
        (canonicalQueryFromFullHistory root
          ([(root, true)] ++ canonicalSuffix root history))).length := by
    omega
  have hlj : l ≤ j := by omega
  have h := C.target_fresh c X hX l hlFull
  simpa [List.take_take, Nat.min_eq_left hlj] using h

private theorem target_fresh_on_runtime_cell
    (C : StableReplayStageCertificate hd hmn W root p radialIncremented delta epsilon
      incremented history v A)
    (c : StableReplayStateIndex hd hmn W root p radialIncremented delta
      incremented history A) (j : ℕ)
    (hj : j < (siteDirectionOrder hd root
      ([(root, true)] ++ canonicalSuffix root history)
      (canonicalQueryFromFullHistory root
        ([(root, true)] ++ canonicalSuffix root history))).length) :
    let fullHistory := [(root, true)] ++ canonicalSuffix root history
    let S := c.1.1
    let queried := canonicalQueryFromFullHistory root fullHistory
    let seed := inletSeed hd root fullHistory queried S
    let incoming := incomingDirection hd root fullHistory queried
    let first := firstFlip hd root fullHistory queried S
    let directions := siteDirectionOrder hd root fullHistory queried
    ∀ r : LaterSiteRuntime.StablePrefixRuntimeIndex hmn S.source
        seed.physicalCenter (grimmettMarstrandSiteCenter (m + n + 1) queried.1)
          incoming first unusedSecondFlip p delta incremented directions j
          S.source.historyProfile.event,
      let R := r.1.1
      let a := directions[j]
      let center := R.slotCenterFor seed.physicalCenter a j
      let flip := R.slotTransverseFlip incoming first unusedSecondFlip a j
      let frame := cubicRestartFrameIso center a flip
      Disjoint (cubicEdgeEndpointVertices (R.source.referenceExploredEdges frame))
        (cubicEdgeEndpointVertices (seededBoundaryTargetSupport d a.1 m n)) := by
  dsimp only
  intro r
  obtain ⟨X, hXcell, hXruntime⟩ := r.2.2
  have h := C.target_fresh c X hXcell j hj
  rw [← hXruntime]
  simpa [LaterSiteRuntime.prefixRuntime] using h

private theorem restart_gt_on_runtime_cell
    (C : StableReplayStageCertificate hd hmn W root p radialIncremented delta epsilon
      incremented history v A)
    (c : StableReplayStateIndex hd hmn W root p radialIncremented delta
      incremented history A) (j : ℕ)
    (hj : j < (siteDirectionOrder hd root
      ([(root, true)] ++ canonicalSuffix root history)
      (canonicalQueryFromFullHistory root
        ([(root, true)] ++ canonicalSuffix root history))).length) :
    let fullHistory := [(root, true)] ++ canonicalSuffix root history
    let S := c.1.1
    let queried := canonicalQueryFromFullHistory root fullHistory
    let seed := inletSeed hd root fullHistory queried S
    let incoming := incomingDirection hd root fullHistory queried
    let first := firstFlip hd root fullHistory queried S
    let directions := siteDirectionOrder hd root fullHistory queried
    ∀ r : LaterSiteRuntime.StablePrefixRuntimeIndex hmn S.source
        seed.physicalCenter (grimmettMarstrandSiteCenter (m + n + 1) queried.1)
          incoming first unusedSecondFlip p delta incremented directions j
          S.source.historyProfile.event,
      let R := r.1.1
      let a := directions[j]
      let Q := R.restartQuery seed.physicalCenter incoming first unusedSecondFlip a j
      (1 - epsilon) * (couplingMeasure (CubicEdge d)).real
          (Q.boundaryHistoryEvent n) <
        (couplingMeasure (CubicEdge d)).real
          (Q.successEvent m n p delta ∩ Q.boundaryHistoryEvent n) := by
  dsimp only
  intro r
  obtain ⟨X, hXcell, hXruntime⟩ := r.2.2
  have h := C.restart_gt c X hXcell j hj
  rw [← hXruntime]
  simpa [LaterSiteRuntime.prefixRuntime] using h

private theorem activePrefixCertificate
    (C : StableReplayStageCertificate hd hmn W root p radialIncremented delta epsilon
      incremented history v A)
    (c : StableReplayStateIndex hd hmn W root p radialIncremented delta
      incremented history A) (j : ℕ)
    (hj : j < (siteDirectionOrder hd root
      ([(root, true)] ++ canonicalSuffix root history)
      (canonicalQueryFromFullHistory root
        ([(root, true)] ++ canonicalSuffix root history))).length) :
    AdaptiveSiteExploration.LaterSitePrefixCertificate hmn c.1.1.source
      (inletSeed hd root ([(root, true)] ++ canonicalSuffix root history)
        (canonicalQueryFromFullHistory root
          ([(root, true)] ++ canonicalSuffix root history)) c.1.1).physicalCenter
      (grimmettMarstrandSiteCenter (m + n + 1)
        (canonicalQueryFromFullHistory root
          ([(root, true)] ++ canonicalSuffix root history)).1)
      (incomingDirection hd root ([(root, true)] ++ canonicalSuffix root history)
        (canonicalQueryFromFullHistory root
          ([(root, true)] ++ canonicalSuffix root history)))
      (firstFlip hd root ([(root, true)] ++ canonicalSuffix root history)
        (canonicalQueryFromFullHistory root
          ([(root, true)] ++ canonicalSuffix root history)) c.1.1)
      unusedSecondFlip p delta epsilon incremented
      (siteDirectionOrder hd root ([(root, true)] ++ canonicalSuffix root history)
        (canonicalQueryFromFullHistory root
          ([(root, true)] ++ canonicalSuffix root history))) j
      c.1.1.source.historyProfile.event := by
  let fullHistory := [(root, true)] ++ canonicalSuffix root history
  let S := c.1.1
  let queried := canonicalQueryFromFullHistory root fullHistory
  let seed := inletSeed hd root fullHistory queried S
  let incoming := incomingDirection hd root fullHistory queried
  let first := firstFlip hd root fullHistory queried S
  let directions := siteDirectionOrder hd root fullHistory queried
  let Acell := S.source.historyProfile.event
  have hAcurrent : Acell ⊆ S.source.historyProfile.event := Set.Subset.rfl
  have hAnonnegative : Acell ⊆ SourceFiniteEdgeRevealState.nonnegativeCouplingEvent := by
    intro X hX
    exact C.nonnegative (c.2.1 hX)
  have hstablePrefix : ∀ X ∈ Acell,
      (LaterSiteRuntime.prefixRuntime hmn S.source seed.physicalCenter
        (grimmettMarstrandSiteCenter (m + n + 1) queried.1) incoming first
        unusedSecondFlip p delta incremented directions j X).source.historyProfile.event ⊆
          Acell := by
    exact stablePrefix_event_subset C c j
  obtain ⟨X0, hX0A, hX0state⟩ := c.2.2
  have hX0cell : X0 ∈ Acell := by
    have hs := C.replay_self X0 hX0A
    have hsource :
        (replay hd hmn W root p radialIncremented delta incremented X0 history).source =
          S.source := congrArg DynamicBlockHistoryState.source hX0state
    change X0 ∈ S.source.historyProfile.event
    rw [← hsource]
    exact hs
  have hnonempty : Nonempty
      (LaterSiteRuntime.StablePrefixRuntimeIndex hmn S.source seed.physicalCenter
        (grimmettMarstrandSiteCenter (m + n + 1) queried.1) incoming
        first unusedSecondFlip p delta incremented directions j Acell) :=
    LaterSiteRuntime.nonempty_stablePrefixRuntimeIndex hmn S.source seed.physicalCenter
      (grimmettMarstrandSiteCenter (m + n + 1) queried.1) incoming first unusedSecondFlip
        p delta incremented directions j Acell X0 hX0cell
        (hstablePrefix X0 hX0cell)
  have hadds : ∀ X ∈ Acell, ∀ l
      (hl : l < (directions.take j).length) e,
      let Rl := LaterSiteRuntime.runFrom hmn seed.physicalCenter incoming first
        unusedSecondFlip p delta incremented X
          (siteInitialRuntime (m + n + 1) queried S seed) 0
          ((directions.take j).take l)
      let a := (directions.take j)[l]
      (incremented Rl.source a e : ℝ) = (Rl.source.lower e : ℝ) + delta := by
    exact policy_adds_on_taken_prefix C c j
  have hfreshPrefix : ∀ X ∈ Acell, ∀ l
      (hl : l < (directions.take j).length),
      let Rl := LaterSiteRuntime.runFrom hmn seed.physicalCenter incoming first
        unusedSecondFlip p delta incremented X
          (siteInitialRuntime (m + n + 1) queried S seed) 0
          ((directions.take j).take l)
      let a := (directions.take j)[l]
      let center := Rl.slotCenterFor seed.physicalCenter a l
      let flip := Rl.slotTransverseFlip incoming first unusedSecondFlip a l
      let frame := cubicRestartFrameIso center a flip
      Disjoint (cubicEdgeEndpointVertices (Rl.source.referenceExploredEdges frame))
        (cubicEdgeEndpointVertices (seededBoundaryTargetSupport d a.1 m n)) := by
    exact target_fresh_on_taken_prefix C c j
  have hTargetFresh : ∀ r : LaterSiteRuntime.StablePrefixRuntimeIndex hmn S.source
      seed.physicalCenter (grimmettMarstrandSiteCenter (m + n + 1) queried.1)
        incoming first unusedSecondFlip p delta incremented directions j
        Acell,
      let R := r.1.1
      let a := directions[j]
      let center := R.slotCenterFor seed.physicalCenter a j
      let flip := R.slotTransverseFlip incoming first unusedSecondFlip a j
      let frame := cubicRestartFrameIso center a flip
      Disjoint (cubicEdgeEndpointVertices (R.source.referenceExploredEdges frame))
        (cubicEdgeEndpointVertices (seededBoundaryTargetSupport d a.1 m n)) := by
    exact target_fresh_on_runtime_cell C c j hj
  have hrestart : ∀ r : LaterSiteRuntime.StablePrefixRuntimeIndex hmn S.source
      seed.physicalCenter (grimmettMarstrandSiteCenter (m + n + 1) queried.1)
        incoming first unusedSecondFlip p delta incremented directions j
        Acell,
      let R := r.1.1
      let a := directions[j]
      let Q := R.restartQuery seed.physicalCenter incoming first unusedSecondFlip a j
      (1 - epsilon) * (couplingMeasure (CubicEdge d)).real
          (Q.boundaryHistoryEvent n) <
      (couplingMeasure (CubicEdge d)).real
          (Q.successEvent m n p delta ∩ Q.boundaryHistoryEvent n) := by
    exact restart_gt_on_runtime_cell C c j hj
  exact
    { hj := hj
      hmono := C.policy_mono
      hnonempty := hnonempty
      hAcurrent := hAcurrent
      hAnonnegative := hAnonnegative
      hstable := hstablePrefix
      hadds := hadds
      hfreshPrefix := hfreshPrefix
      hTargetFresh := hTargetFresh
      hrestart := hrestart }

/-- The geometric and threshold parts of a stable-cell certificate hold for the literal
runtime obtained by replaying any point of the certified outer event.  This is the deterministic
bridge used later to install the successful site's published seed boxes; unlike the probability
estimate, it needs no conditioning or division by the history mass. -/
theorem runtime_ready_of_mem
    (C : StableReplayStageCertificate hd hmn W root p radialIncremented delta epsilon
      incremented history v A)
    {X : CubicEdge d → ℝ} (hXA : X ∈ A) :
    let fullHistory := [(root, true)] ++ canonicalSuffix root history
    let S := replay hd hmn W root p radialIncremented delta incremented X history
    let queried := canonicalQueryFromFullHistory root fullHistory
    let seed := inletSeed hd root fullHistory queried S
    let incoming := incomingDirection hd root fullHistory queried
    let first := firstFlip hd root fullHistory queried S
    let directions := siteDirectionOrder hd root fullHistory queried
    ∀ j (hj : j < directions.length),
      let Rj := LaterSiteRuntime.runFrom hmn seed.physicalCenter incoming first
        unusedSecondFlip p delta incremented X
          (siteInitialRuntime (m + n + 1) queried S seed) 0 (directions.take j)
      let a := directions[j]
      Disjoint
          (cubicEdgeEndpointVertices (Rj.source.referenceExploredEdges
            (cubicRestartFrameIso (Rj.slotCenterFor seed.physicalCenter a j) a
              (Rj.slotTransverseFlip incoming first unusedSecondFlip a j))))
          (cubicEdgeEndpointVertices (seededBoundaryTargetSupport d a.1 m n)) ∧
        ∀ e ∈ (Rj.restartQuery seed.physicalCenter incoming first unusedSecondFlip a j
          ).boundarySupport n,
          ((Rj.restartQuery seed.physicalCenter incoming first unusedSecondFlip a j
            ).physicalBoundaryThreshold e : ℝ) + delta ≤
            (incremented Rj.source a e : ℝ) := by
  let S := replay hd hmn W root p radialIncremented delta incremented X history
  have hSmem : S ∈ replayStateFinset hd hmn W root p radialIncremented delta
      incremented history := by
    rw [mem_replayStateFinset_iff]
    exact ⟨X, rfl⟩
  let c : StableReplayStateIndex hd hmn W root p radialIncremented delta
      incremented history A :=
    ⟨⟨S, hSmem⟩, C.replay_stable X hXA, X, hXA, rfl⟩
  have hXcell : X ∈ S.source.historyProfile.event := by
    simpa [S] using C.replay_self X hXA
  dsimp only
  intro j hj
  constructor
  · simpa [c, S] using C.target_fresh c X (by simpa [c, S] using hXcell) j hj
  · intro e _he
    have hadd := C.policy_adds c X (by simpa [c, S] using hXcell) j hj e
    have hadd' :
        (incremented
          (LaterSiteRuntime.runFrom hmn
            (inletSeed hd root ([(root, true)] ++ canonicalSuffix root history)
              (canonicalQueryFromFullHistory root
                ([(root, true)] ++ canonicalSuffix root history)) S).physicalCenter
            (incomingDirection hd root ([(root, true)] ++ canonicalSuffix root history)
              (canonicalQueryFromFullHistory root
                ([(root, true)] ++ canonicalSuffix root history)))
            (firstFlip hd root ([(root, true)] ++ canonicalSuffix root history)
              (canonicalQueryFromFullHistory root
                ([(root, true)] ++ canonicalSuffix root history)) S)
            unusedSecondFlip p delta incremented X
            (siteInitialRuntime (m + n + 1)
              (canonicalQueryFromFullHistory root
                ([(root, true)] ++ canonicalSuffix root history)) S
              (inletSeed hd root ([(root, true)] ++ canonicalSuffix root history)
                (canonicalQueryFromFullHistory root
                  ([(root, true)] ++ canonicalSuffix root history)) S))
            0
            ((siteDirectionOrder hd root
              ([(root, true)] ++ canonicalSuffix root history)
              (canonicalQueryFromFullHistory root
                ([(root, true)] ++ canonicalSuffix root history))).take j)).source
          (siteDirectionOrder hd root ([(root, true)] ++ canonicalSuffix root history)
            (canonicalQueryFromFullHistory root
              ([(root, true)] ++ canonicalSuffix root history)))[j] e : ℝ) =
          ((LaterSiteRuntime.runFrom hmn
            (inletSeed hd root ([(root, true)] ++ canonicalSuffix root history)
              (canonicalQueryFromFullHistory root
                ([(root, true)] ++ canonicalSuffix root history)) S).physicalCenter
            (incomingDirection hd root ([(root, true)] ++ canonicalSuffix root history)
              (canonicalQueryFromFullHistory root
                ([(root, true)] ++ canonicalSuffix root history)))
            (firstFlip hd root ([(root, true)] ++ canonicalSuffix root history)
              (canonicalQueryFromFullHistory root
                ([(root, true)] ++ canonicalSuffix root history)) S)
            unusedSecondFlip p delta incremented X
            (siteInitialRuntime (m + n + 1)
              (canonicalQueryFromFullHistory root
                ([(root, true)] ++ canonicalSuffix root history)) S
              (inletSeed hd root ([(root, true)] ++ canonicalSuffix root history)
                (canonicalQueryFromFullHistory root
                  ([(root, true)] ++ canonicalSuffix root history)) S))
            0
            ((siteDirectionOrder hd root
              ([(root, true)] ++ canonicalSuffix root history)
              (canonicalQueryFromFullHistory root
                ([(root, true)] ++ canonicalSuffix root history))).take j)).source.lower e : ℝ) +
            delta := by
      simpa [c, S] using hadd
    rw [LaterSiteRuntime.restartQuery,
      SourceFiniteEdgeRevealState.framedQuery_physicalBoundaryThreshold]
    exact hadd'.ge

private theorem mem_statePaddedStageSuccess_iff_runtimeQuery_of_lt
    (c : StableReplayStateIndex hd hmn W root p radialIncremented delta
      incremented history A) (j : ℕ)
    (hj : j < (siteDirectionOrder hd root
      ([(root, true)] ++ canonicalSuffix root history)
      (canonicalQueryFromFullHistory root
        ([(root, true)] ++ canonicalSuffix root history))).length)
    (X : CubicEdge d → ℝ) :
    X ∈ statePaddedStageSuccess hd hmn root p delta incremented
        ([(root, true)] ++ canonicalSuffix root history) v c.1.1 j ↔
      let fullHistory := [(root, true)] ++ canonicalSuffix root history
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
    ([(root, true)] ++ canonicalSuffix root history)
    (canonicalQueryFromFullHistory root
      ([(root, true)] ++ canonicalSuffix root history))).length then _ else True) ↔ _
  rw [dif_pos hj]

private theorem stageSlice_eq_prefixSemanticSuccess_of_lt
    (c : StableReplayStateIndex hd hmn W root p radialIncremented delta
      incremented history A) (j : ℕ)
    (hj : j < (siteDirectionOrder hd root
      ([(root, true)] ++ canonicalSuffix root history)
      (canonicalQueryFromFullHistory root
        ([(root, true)] ++ canonicalSuffix root history))).length) :
    stableReplayStageSlice hd hmn W root p radialIncremented delta incremented
        history v A c j =
      let fullHistory := [(root, true)] ++ canonicalSuffix root history
      let S := c.1.1
      let queried := canonicalQueryFromFullHistory root fullHistory
      let seed := inletSeed hd root fullHistory queried S
      let incoming := incomingDirection hd root fullHistory queried
      let first := firstFlip hd root fullHistory queried S
      let directions := siteDirectionOrder hd root fullHistory queried
      {X | X ∈ S.source.historyProfile.event ∧
        X ∈ ((LaterSiteRuntime.prefixRuntime hmn S.source seed.physicalCenter
          (grimmettMarstrandSiteCenter (m + n + 1) queried.1) incoming first
          unusedSecondFlip p delta incremented directions j X).restartQuery
            seed.physicalCenter incoming first unusedSecondFlip directions[j] j).successEvent
              m n p delta} := by
  ext X
  unfold stableReplayStageSlice
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

private theorem stageSlice_measurable_and_lower_of_lt
    (C : StableReplayStageCertificate hd hmn W root p radialIncremented delta epsilon
      incremented history v A)
    (c : StableReplayStateIndex hd hmn W root p radialIncremented delta
      incremented history A) (j : ℕ)
    (hj : j < (siteDirectionOrder hd root
      ([(root, true)] ++ canonicalSuffix root history)
      (canonicalQueryFromFullHistory root
        ([(root, true)] ++ canonicalSuffix root history))).length) :
    MeasurableSet (stableReplayStageSlice hd hmn W root p radialIncremented delta
        incremented history v A c j) ∧
      (1 - epsilon) * (couplingMeasure (CubicEdge d)).real
          c.1.1.source.historyProfile.event ≤
        (couplingMeasure (CubicEdge d)).real
          (stableReplayStageSlice hd hmn W root p radialIncremented delta
            incremented history v A c j) := by
  rw [stageSlice_eq_prefixSemanticSuccess_of_lt c j hj]
  let fullHistory := [(root, true)] ++ canonicalSuffix root history
  let S := c.1.1
  let queried := canonicalQueryFromFullHistory root fullHistory
  let seed := inletSeed hd root fullHistory queried S
  let incoming := incomingDirection hd root fullHistory queried
  let first := firstFlip hd root fullHistory queried S
  let directions := siteDirectionOrder hd root fullHistory queried
  let Acell := S.source.historyProfile.event
  let D := activePrefixCertificate C c j hj
  have h := AdaptiveSiteExploration.laterSitePrefixSemantic_measurable_and_lower
    hmn S.source seed.physicalCenter
      (grimmettMarstrandSiteCenter (m + n + 1) queried.1) incoming first
      unusedSecondFlip p delta epsilon incremented
      D.hmono directions j D.hj Acell D.hnonempty D.hAcurrent D.hAnonnegative D.hstable
        D.hadds D.hfreshPrefix D.hTargetFresh D.hrestart
  simpa only [fullHistory, S, queried, seed, incoming, first, directions, Acell] using h

set_option maxHeartbeats 800000 in
/-- On each stable global replay cell, one padded slot is measurable and retains the
cellwise Lemma 7.17 factor. -/
theorem stageSlice_measurable_and_lower
    (C : StableReplayStageCertificate hd hmn W root p radialIncremented delta epsilon
      incremented history v A)
    (c : StableReplayStateIndex hd hmn W root p radialIncremented delta
      incremented history A) (j : ℕ) :
    MeasurableSet (stableReplayStageSlice hd hmn W root p radialIncremented delta
        incremented history v A c j) ∧
      (1 - epsilon) * (couplingMeasure (CubicEdge d)).real
          c.1.1.source.historyProfile.event ≤
        (couplingMeasure (CubicEdge d)).real
          (stableReplayStageSlice hd hmn W root p radialIncremented delta
            incremented history v A c j) := by
  let fullHistory := [(root, true)] ++ canonicalSuffix root history
  let S := c.1.1
  let queried := canonicalQueryFromFullHistory root fullHistory
  let directions := siteDirectionOrder hd root fullHistory queried
  by_cases hj : j < directions.length
  · exact stageSlice_measurable_and_lower_of_lt C c j (by simpa [directions] using hj)
  · have hslice : stableReplayStageSlice hd hmn W root p radialIncremented delta
        incremented history v A c j = c.1.1.source.historyProfile.event := by
      have hstateSuccess :
          statePaddedStageSuccess hd hmn root p delta incremented fullHistory v S j =
            Set.univ := by
        ext X
        unfold statePaddedStageSuccess
        change (if _h : j < directions.length then _ else True) ↔ X ∈ Set.univ
        rw [dif_neg hj]
        simp
      unfold stableReplayStageSlice
      rw [hstateSuccess]
      simp
    rw [hslice]
    constructor
    · exact c.1.1.source.historyProfile.measurableSet_event
    · calc
        (1 - epsilon) * (couplingMeasure (CubicEdge d)).real
            c.1.1.source.historyProfile.event ≤
          1 * (couplingMeasure (CubicEdge d)).real
            c.1.1.source.historyProfile.event :=
              mul_le_mul_of_nonneg_right (by linarith [C.epsilon_nonneg]) (measureReal_nonneg)
        _ = (couplingMeasure (CubicEdge d)).real
            c.1.1.source.historyProfile.event := one_mul _

/-- A certified literal replay slot is measurable on the outer history and satisfies the
global ratio-free `(1-ε)` lower bound after summing the stable replay cells. -/
theorem inter_paddedStageSuccess_measurable_and_lower
    (C : StableReplayStageCertificate hd hmn W root p radialIncremented delta epsilon
      incremented history v A)
    (j : ℕ) :
    MeasurableSet
        (A ∩ paddedStageSuccess hd hmn W root p radialIncremented delta incremented
          history v j) ∧
      (1 - epsilon) * (couplingMeasure (CubicEdge d)).real A ≤
        (couplingMeasure (CubicEdge d)).real
          (A ∩ paddedStageSuccess hd hmn W root p radialIncremented delta incremented
            history v j) := by
  let success := fun c : StableReplayStateIndex hd hmn W root p radialIncremented delta
      incremented history A ↦
    stableReplayStageSlice hd hmn W root p radialIncremented delta incremented
      history v A c j
  have hunion : stableReplaySuccessUnion success =
      A ∩ paddedStageSuccess hd hmn W root p radialIncremented delta incremented
        history v j := by
    exact stableReplaySuccessUnion_stageSlice_eq hd hmn W root p radialIncremented delta
      incremented history v A j C.replay_exact C.replay_self C.replay_stable
  constructor
  · rw [← hunion]
    apply measurableSet_finiteSuccessSliceUnion
    intro c
    exact (C.stageSlice_measurable_and_lower c j).1
  · rw [← hunion]
    apply mul_measureReal_stableReplayHistory_le_successUnion hd hmn W root p
      radialIncremented delta incremented history A (1 - epsilon)
        C.replay_exact C.replay_self C.replay_stable success
    · intro c
      exact (C.stageSlice_measurable_and_lower c j).1
    · intro c
      exact Set.inter_subset_left
    · intro c
      exact (C.stageSlice_measurable_and_lower c j).2

end StableReplayStageCertificate

/-- Per-slot certificates for the literal `4d` runtime on every admitted coarse query and
every preceding semantic success prefix. -/
structure ReplayProgramStageCertificates
    (hd : 0 < d) (hmn : 2 * m ≤ n)
    (W : RootRadialSeedProfile d m n) (root : F)
    (p radialIncremented : I) (delta epsilon : ℝ)
    (incremented : RootExtensionThresholdPolicy d)
    (initialEvent : Set (CubicEdge d → ℝ)) where
  /-- The initialized outer event is a genuine completed-root event, not merely an unrelated
  positive cylinder. -/
  initial_subset_root_completion : initialEvent ⊆
    W.mixedExtensionPrefixSuccessEvent p radialIncremented delta incremented
      (rootExtensionDirectionOrder d).length
  /-- The same literal increment policy used by later replay was already valid at every root
  extension prefix. -/
  root_policy_adds : W.PolicyAddsOnPrefixes p radialIncremented delta incremented
  slot : ∀ (history : List (F × Bool)) (v : F), AdmissibleQuery root history v →
    ∀ j, j < 4 * d →
      StableReplayStageCertificate hd hmn W root p radialIncremented delta epsilon
        incremented history v
        (initialEvent ∩
          (AdaptiveSiteExploration.finiteAdaptiveSuccessPrefix
              (paddedStageSuccess hd hmn W root p radialIncremented delta incremented)
              history v j ∩
            AdaptiveSiteExploration.adaptiveAnswerHistoryEvent
              (AdaptiveSiteExploration.finiteAdaptiveSuccessAnswer
                (paddedStageSuccess hd hmn W root p radialIncremented delta incremented)
                (4 * d)) history))

namespace ReplayProgramStageCertificates

variable {p radialIncremented : I} {delta epsilon : ℝ}
  {incremented : RootExtensionThresholdPolicy d}
  {W : RootRadialSeedProfile d m n} {root : F}
  {initialEvent : Set (CubicEdge d → ℝ)}
  {hd : 0 < d} {hmn : 2 * m ≤ n}

/-- The completed root event initializes the installed-seed invariant used by every later
coarse query. -/
theorem seededBoxesInstalled_rooted
    [NeZero d]
    (C : ReplayProgramStageCertificates hd hmn W root p radialIncremented delta epsilon
      incremented initialEvent)
    (hm : 1 ≤ m) (hmnStrict : m + 1 < n)
    {X : CubicEdge d → ℝ} (hX : X ∈ initialEvent) :
    (DynamicBlockHistoryState.rooted W root p radialIncremented delta incremented X
      ).SeedBoxesInstalled (m := m) := by
  exact DynamicBlockHistoryState.seededBoxesInstalled_rooted hm hmnStrict W root p
    radialIncremented delta incremented X C.root_policy_adds
      (C.initial_subset_root_completion hX)

/-- Every currently active replay runtime inherits the slotwise freshness and literal threshold
increment facts from the stage certificate at slot zero.  Slot zero is used only to choose the
stable outer replay cell; its certificate already quantifies over the complete active schedule. -/
theorem runtime_ready
    (C : ReplayProgramStageCertificates hd hmn W root p radialIncremented delta epsilon
      incremented initialEvent)
    (history : List (F × Bool)) (v : F) (hadmissible : AdmissibleQuery root history v)
    {X : CubicEdge d → ℝ} (hinitial : X ∈ initialEvent)
    (hhistory : X ∈ AdaptiveSiteExploration.adaptiveAnswerHistoryEvent
      (AdaptiveSiteExploration.finiteAdaptiveSuccessAnswer
        (paddedStageSuccess hd hmn W root p radialIncremented delta incremented)
        (4 * d)) history) :
    let fullHistory := [(root, true)] ++ canonicalSuffix root history
    let S := replay hd hmn W root p radialIncremented delta incremented X history
    let queried := canonicalQueryFromFullHistory root fullHistory
    let seed := inletSeed hd root fullHistory queried S
    let incoming := incomingDirection hd root fullHistory queried
    let first := firstFlip hd root fullHistory queried S
    let directions := siteDirectionOrder hd root fullHistory queried
    ∀ j (hj : j < directions.length),
      let Rj := LaterSiteRuntime.runFrom hmn seed.physicalCenter incoming first
        unusedSecondFlip p delta incremented X
          (siteInitialRuntime (m + n + 1) queried S seed) 0 (directions.take j)
      let a := directions[j]
      Disjoint
          (cubicEdgeEndpointVertices (Rj.source.referenceExploredEdges
            (cubicRestartFrameIso (Rj.slotCenterFor seed.physicalCenter a j) a
              (Rj.slotTransverseFlip incoming first unusedSecondFlip a j))))
          (cubicEdgeEndpointVertices (seededBoundaryTargetSupport d a.1 m n)) ∧
        ∀ e ∈ (Rj.restartQuery seed.physicalCenter incoming first unusedSecondFlip a j
          ).boundarySupport n,
          ((Rj.restartQuery seed.physicalCenter incoming first unusedSecondFlip a j
            ).physicalBoundaryThreshold e : ℝ) + delta ≤
            (incremented Rj.source a e : ℝ) := by
  have hj0 : 0 < 4 * d := by omega
  let C0 := C.slot history v hadmissible 0 hj0
  have hmem : X ∈ initialEvent ∩
      (AdaptiveSiteExploration.finiteAdaptiveSuccessPrefix
          (paddedStageSuccess hd hmn W root p radialIncremented delta incremented)
          history v 0 ∩
        AdaptiveSiteExploration.adaptiveAnswerHistoryEvent
          (AdaptiveSiteExploration.finiteAdaptiveSuccessAnswer
            (paddedStageSuccess hd hmn W root p radialIncremented delta incremented)
            (4 * d)) history) := by
    exact ⟨hinitial, by simpa using hhistory⟩
  exact C0.runtime_ready_of_mem hmem

/-- One accepted canonical replay query preserves the global installed-seed invariant.  The
proof combines the history-dependent parent table, the semantic `4d` answer, and the deterministic
slot readiness extracted above; no geometric premise remains on the call site. -/
theorem seededBoxesInstalled_step_true
    [NeZero d]
    (C : ReplayProgramStageCertificates hd hmn W root p radialIncremented delta epsilon
      incremented initialEvent)
    (history : List (F × Bool)) (v : F) (hadmissible : AdmissibleQuery root history v)
    {X : CubicEdge d → ℝ} (hinitial : X ∈ initialEvent)
    (hhistory : X ∈ AdaptiveSiteExploration.adaptiveAnswerHistoryEvent
      (AdaptiveSiteExploration.finiteAdaptiveSuccessAnswer
        (paddedStageSuccess hd hmn W root p radialIncremented delta incremented)
        (4 * d)) history)
    (hinstalled :
      (replay hd hmn W root p radialIncremented delta incremented X history
        ).SeedBoxesInstalled (m := m))
    (haccepted : AdaptiveSiteExploration.finiteAdaptiveSuccessAnswer
      (paddedStageSuccess hd hmn W root p radialIncremented delta incremented)
      (4 * d) X history v = true) :
    let fullHistory := [(root, true)] ++ canonicalSuffix root history
    let S := replay hd hmn W root p radialIncremented delta incremented X history
    let queried := canonicalQueryFromFullHistory root fullHistory
    (step hd hmn root fullHistory queried true p delta incremented X S
      ).SeedBoxesInstalled (m := m) := by
  let fullHistory := [(root, true)] ++ canonicalSuffix root history
  let S := replay hd hmn W root p radialIncremented delta incremented X history
  let queried := canonicalQueryFromFullHistory root fullHistory
  have hcompletion := C.initial_subset_root_completion hinitial
  have hcover : OutgoingCoversUndecidedNeighbors fullHistory S := by
    simpa [fullHistory, S] using outgoingCoversUndecidedNeighbors_replay
      hd hmn W root p radialIncremented delta incremented X history hcompletion
  have hquery : queried = v := by
    simpa [queried, fullHistory] using
      canonicalQueryFromFullHistory_eq_of_admissibleQuery root history v hadmissible
  have hinlet : cubicBoxEdges d
      (inletSeed hd root fullHistory queried S).physicalCenter m ⊆ S.source.explored := by
    have h := inletSeed_seedBox_subset_of_admissibleQuery (m := m)
      hd root history v S hadmissible hcover hinstalled
    simpa [fullHistory, queried, hquery] using h
  have hanswer : answer hd hmn W root p radialIncremented delta incremented X history v = true := by
    rw [answer_eq_finiteAdaptiveSuccessAnswer]
    exact haccepted
  have hsuccess :
      let seed := inletSeed hd root fullHistory queried S
      let incoming := incomingDirection hd root fullHistory queried
      let first := firstFlip hd root fullHistory queried S
      let directions := siteDirectionOrder hd root fullHistory queried
      LaterSiteRuntime.succeedsFrom hmn seed.physicalCenter incoming first
        unusedSecondFlip p delta incremented X
          (siteInitialRuntime (m + n + 1) queried S seed) 0 directions := by
    simpa only [answer, decide_eq_true_eq, S, fullHistory, queried] using hanswer
  have hready := C.runtime_ready history v hadmissible hinitial hhistory
  exact seededBoxesInstalled_step_true_of_success hd hmn root fullHistory queried p delta
    incremented X S hinstalled hinlet hsuccess hready

/-- Along any genuine finite adaptive history, every published parent seed remains physically
installed in the accumulated bond exploration.  The decomposition hypothesis merely says that
each recorded vertex was the actual query at the time it was recorded; it is discharged by the
site-exploration history in the final connection theorem. -/
theorem seededBoxesInstalled_replay
    [NeZero d]
    (C : ReplayProgramStageCertificates hd hmn W root p radialIncremented delta epsilon
      incremented initialEvent)
    (hm : 1 ≤ m) (hmnStrict : m + 1 < n)
    (history : List (F × Bool)) {X : CubicEdge d → ℝ}
    (hinitial : X ∈ initialEvent)
    (hhistory : X ∈ AdaptiveSiteExploration.adaptiveAnswerHistoryEvent
      (AdaptiveSiteExploration.finiteAdaptiveSuccessAnswer
        (paddedStageSuccess hd hmn W root p radialIncremented delta incremented)
        (4 * d)) history)
    (hadmissible : ∀ (prior : List (F × Bool)) (v : F) (accepted : Bool)
      (tail : List (F × Bool)),
      history = prior ++ (v, accepted) :: tail → AdmissibleQuery root prior v) :
    (replay hd hmn W root p radialIncremented delta incremented X history
      ).SeedBoxesInstalled (m := m) := by
  let finiteAnswer := AdaptiveSiteExploration.finiteAdaptiveSuccessAnswer
    (paddedStageSuccess hd hmn W root p radialIncremented delta incremented) (4 * d)
  induction history using List.reverseRecOn with
  | nil =>
      simpa [replay, canonicalSuffix, SiteExploration.replayState,
        cubicRegionSiteExploration, rootedSiteExploration] using
        C.seededBoxesInstalled_rooted hm hmnStrict hinitial
  | append_singleton prior entry ih =>
      rcases entry with ⟨v, accepted⟩
      have hadmissibleLast : AdmissibleQuery root prior v :=
        hadmissible prior v accepted [] (by simp)
      have hadmissiblePrior : ∀ (pref : List (F × Bool)) (u : F) (b : Bool)
          (tail : List (F × Bool)),
          prior = pref ++ (u, b) :: tail → AdmissibleQuery root pref u := by
        intro pref u b tail hprior
        apply hadmissible pref u b (tail ++ [(v, accepted)])
        rw [hprior]
        simp [List.append_assoc]
      have hhistorySplit :
          X ∈ AdaptiveSiteExploration.adaptiveAnswerHistoryEvent finiteAnswer prior ∩
            {Y | finiteAnswer Y prior v = accepted} := by
        rw [← AdaptiveSiteExploration.adaptiveAnswerHistoryEvent_append_singleton]
        simpa [finiteAnswer] using hhistory
      have hinstalledPrior :
          (replay hd hmn W root p radialIncremented delta incremented X prior
            ).SeedBoxesInstalled (m := m) := by
        exact ih (by simpa [finiteAnswer] using hhistorySplit.1) hadmissiblePrior
      rw [replay_append_singleton_of_admissibleQuery hd hmn W root p radialIncremented
        delta incremented X prior v accepted hadmissibleLast]
      cases accepted
      · exact seededBoxesInstalled_step_false hd hmn root
          ([(root, true)] ++ canonicalSuffix root prior) v p delta incremented X
          (replay hd hmn W root p radialIncremented delta incremented X prior)
          hinstalledPrior
      · have hstep := C.seededBoxesInstalled_step_true prior v hadmissibleLast hinitial
          (by simpa [finiteAnswer] using hhistorySplit.1) hinstalledPrior
          (by simpa [finiteAnswer] using hhistorySplit.2)
        have hquery : canonicalQueryFromFullHistory root
            ([(root, true)] ++ canonicalSuffix root prior) = v :=
          canonicalQueryFromFullHistory_eq_of_admissibleQuery root prior v hadmissibleLast
        dsimp only at hstep
        rw [hquery] at hstep
        exact hstep

/-- The source-faithful `4d` restart schedule satisfies the adaptive lower law once every
literal semantic prefix has its stable replay certificate. -/
theorem hasAdaptiveAnswerLowerBoundWithin
    (C : ReplayProgramStageCertificates hd hmn W root p radialIncremented delta epsilon
      incremented initialEvent)
    (hepsilon : epsilon ≤ 1) :
    AdaptiveSiteExploration.HasAdaptiveAnswerLowerBoundWithin
      (couplingMeasure (CubicEdge d)) initialEvent
      (answer hd hmn W root p radialIncremented delta incremented)
      (AdmissibleQuery root) ((1 - epsilon) ^ (4 * d)) := by
  let stage := paddedStageSuccess hd hmn W root p radialIncremented delta incremented
  let finiteAnswer := AdaptiveSiteExploration.finiteAdaptiveSuccessAnswer stage (4 * d)
  have hfinite :
      AdaptiveSiteExploration.HasAdaptiveAnswerLowerBoundWithin
        (couplingMeasure (CubicEdge d)) initialEvent finiteAnswer
        (AdmissibleQuery root) ((1 - epsilon) ^ (4 * d)) := by
    apply AdaptiveSiteExploration.hasAdaptiveAnswerLowerBoundWithin_finiteAdaptiveSuccessAnswer
      initialEvent stage (4 * d) (AdmissibleQuery root) (1 - epsilon)
        (sub_nonneg.mpr hepsilon)
    intro history v hadmissible j hj
    let A := initialEvent ∩
      (AdaptiveSiteExploration.finiteAdaptiveSuccessPrefix stage history v j ∩
        AdaptiveSiteExploration.adaptiveAnswerHistoryEvent finiteAnswer history)
    have hslot := (C.slot history v hadmissible j hj
      ).inter_paddedStageSuccess_measurable_and_lower j |>.2
    have hnext : A ∩ stage history v j =
        initialEvent ∩
          (AdaptiveSiteExploration.finiteAdaptiveSuccessPrefix stage history v (j + 1) ∩
            AdaptiveSiteExploration.adaptiveAnswerHistoryEvent finiteAnswer history) := by
      rw [AdaptiveSiteExploration.finiteAdaptiveSuccessPrefix_succ]
      ext X
      simp only [Set.mem_inter_iff]
      constructor
      · rintro ⟨⟨hi, hp, hh⟩, hs⟩
        exact ⟨hi, ⟨hs, hp⟩, hh⟩
      · rintro ⟨hi, ⟨hs, hp⟩, hh⟩
        exact ⟨⟨hi, hp, hh⟩, hs⟩
    rw [← hnext]
    simpa [A, stage, finiteAnswer] using hslot
  have hanswer :
      answer hd hmn W root p radialIncremented delta incremented = finiteAnswer := by
    simpa [stage, finiteAnswer] using
      answer_eq_finiteAdaptiveSuccessAnswer hd hmn W root p radialIncremented delta
        incremented
  simpa [hanswer] using hfinite

end ReplayProgramStageCertificates

end DynamicBlockHistoryReplay

end Percolation
