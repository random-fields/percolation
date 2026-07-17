import Percolation.Critical.DynamicHistoryReplay

/-!
# Exact explored-support envelope for dynamic replay prefixes

Target freshness is a geometric statement about the literal edges read before a restart.  The
coarse query-influence boxes used for threshold counting are intentionally oversized and overlap
across neighbouring queries, so they cannot prove freshness.  This file instead records the exact
finite union of the completed replay supports and the current runtime-prefix supports, then
reduces reference-coordinate freshness to disjointness from those transported physical pieces.
-/

namespace Percolation

open scoped unitInterval

namespace DynamicBlockHistoryReplay

variable {d m n : ℕ} {F : Set (Cubic d)} [LinearOrder F]

/-- Exact union of the framed supports used by a suffix of the post-radial root schedule. -/
noncomputable def rootExtensionRestartSupportUnionFrom
    (W : RootRadialSeedProfile d m n) (p : I)
    (incremented : RootExtensionThresholdPolicy d) (X : CubicEdge d → ℝ) :
    SourceFiniteEdgeRevealState d → List (CubicDirection d) → Finset (CubicEdge d)
  | _, [] => ∅
  | S, b :: rest =>
      let Q := S.framedQuery (W.physicalCenter b) b
        (oppositeTransverseRestartFlip b)
      Q.restartSupport m n ∪
        rootExtensionRestartSupportUnionFrom W p incremented X
          (S.next (Q.restartSupport m n) p (incremented S b) X) rest

/-- Exact support accounting for the literal post-radial root recursion. -/
theorem runPostRadialExtensions_explored_subset_initial_union_restartSupportUnionFrom
    (W : RootRadialSeedProfile d m n) (p : I)
    (incremented : RootExtensionThresholdPolicy d) (X : CubicEdge d → ℝ)
    (S : SourceFiniteEdgeRevealState d) (directions : List (CubicDirection d)) :
    (W.runPostRadialExtensions p incremented X S directions).explored ⊆
      S.explored ∪
        rootExtensionRestartSupportUnionFrom W p incremented X S directions := by
  induction directions generalizing S with
  | nil =>
      intro e he
      simpa [RootRadialSeedProfile.runPostRadialExtensions,
        rootExtensionRestartSupportUnionFrom] using he
  | cons b rest ih =>
      let Q := S.framedQuery (W.physicalCenter b) b
        (oppositeTransverseRestartFlip b)
      let Snext := S.next (Q.restartSupport m n) p (incremented S b) X
      have hnext : Snext.explored ⊆ S.explored ∪ Q.restartSupport m n := by
        simpa [Snext] using S.nextExplored_subset_explored_union_stageRegion
          (Q.restartSupport m n) p (incremented S b) X
      have hrest := ih Snext
      intro e he
      have he' : e ∈ Snext.explored ∪
          rootExtensionRestartSupportUnionFrom W p incremented X Snext rest := by
        exact hrest (by simpa [RootRadialSeedProfile.runPostRadialExtensions, Snext] using he)
      rcases Finset.mem_union.mp he' with heNext | heRest
      · rcases Finset.mem_union.mp (hnext heNext) with heOld | heLocal
        · exact Finset.mem_union_left _ heOld
        · exact Finset.mem_union_right _ <| Finset.mem_union_left _ heLocal
      · exact Finset.mem_union_right _ <| Finset.mem_union_right _ heRest

/-- Literal finite support envelope of the special radial step followed by every root
extension. -/
noncomputable def completedRootExploredSupportUnion
    (W : RootRadialSeedProfile d m n) (p radialIncremented : I)
    (incremented : RootExtensionThresholdPolicy d) (X : CubicEdge d → ℝ) :
    Finset (CubicEdge d) :=
  let Srad := rootPostRadialSourceEdgeState d m n p radialIncremented X
  rootInitialExploredEdges d m ∪ rootRadialEdgeSupport d m n ∪
    rootExtensionRestartSupportUnionFrom W p incremented X Srad
      (rootExtensionDirectionOrder d)

/-- Every edge explored by the completed root belongs to the initial seed, the radial support,
or one of the literal framed extension supports. -/
theorem completedRootExtensionState_explored_subset_supportUnion
    (W : RootRadialSeedProfile d m n) (p radialIncremented : I)
    (incremented : RootExtensionThresholdPolicy d) (X : CubicEdge d → ℝ) :
    (W.completedRootExtensionState p radialIncremented incremented X).explored ⊆
      completedRootExploredSupportUnion W p radialIncremented incremented X := by
  let S0 := rootInitialSourceEdgeState d m p
  let Srad := rootPostRadialSourceEdgeState d m n p radialIncremented X
  have hrad : Srad.explored ⊆ S0.explored ∪ rootRadialEdgeSupport d m n := by
    simpa [S0, Srad, rootPostRadialSourceEdgeState] using
      S0.nextExplored_subset_explored_union_stageRegion
        (rootRadialEdgeSupport d m n) p (fun _ ↦ radialIncremented) X
  have hext :=
    runPostRadialExtensions_explored_subset_initial_union_restartSupportUnionFrom
      W p incremented X Srad (rootExtensionDirectionOrder d)
  intro e he
  have he' := hext (by
    simpa [RootRadialSeedProfile.completedRootExtensionState, Srad] using he)
  rcases Finset.mem_union.mp he' with heRadial | heExtension
  · rcases Finset.mem_union.mp (hrad heRadial) with heInitial | heRadialSupport
    · simpa [completedRootExploredSupportUnion, S0, Srad,
        rootInitialSourceEdgeState] using
        (Finset.mem_union_left
          (rootExtensionRestartSupportUnionFrom W p incremented X Srad
            (rootExtensionDirectionOrder d))
          (Finset.mem_union_left (rootRadialEdgeSupport d m n) heInitial))
    · simpa [completedRootExploredSupportUnion, Srad] using
        (Finset.mem_union_left
          (rootExtensionRestartSupportUnionFrom W p incremented X Srad
            (rootExtensionDirectionOrder d))
          (Finset.mem_union_right (rootInitialExploredEdges d m) heRadialSupport))
  · simpa [completedRootExploredSupportUnion, Srad] using
      (Finset.mem_union_right
        (rootInitialExploredEdges d m ∪ rootRadialEdgeSupport d m n) heExtension)

/-- Endpoint-set form of the completed-root exact support envelope. -/
theorem endpointVertices_completedRootExtensionState_subset_supportUnion
    (W : RootRadialSeedProfile d m n) (p radialIncremented : I)
    (incremented : RootExtensionThresholdPolicy d) (X : CubicEdge d → ℝ) :
    cubicEdgeEndpointVertices
        (W.completedRootExtensionState p radialIncremented incremented X).explored ⊆
      cubicEdgeEndpointVertices
        (completedRootExploredSupportUnion W p radialIncremented incremented X) := by
  intro z hz
  obtain ⟨e, he, hze⟩ := mem_cubicEdgeEndpointVertices_iff.mp hz
  exact mem_cubicEdgeEndpointVertices_iff.mpr
    ⟨e, completedRootExtensionState_explored_subset_supportUnion
      W p radialIncremented incremented X he, hze⟩

omit [LinearOrder F] in
/-- The completed-root component of replay freshness can be reduced to disjointness from one
explicit finite support union. -/
theorem rooted_target_disjoint_of_supportUnion_disjoint
    (W : RootRadialSeedProfile d m n) (root : F)
    (p radialIncremented : I) (delta : ℝ)
    (incremented : RootExtensionThresholdPolicy d) (X : CubicEdge d → ℝ)
    (T : Finset (Cubic d))
    (hT : Disjoint
      (cubicEdgeEndpointVertices
        (completedRootExploredSupportUnion W p radialIncremented incremented X)) T) :
    Disjoint
      (cubicEdgeEndpointVertices
        (DynamicBlockHistoryState.rooted W root p radialIncremented delta incremented X
          ).source.explored) T := by
  rw [Finset.disjoint_left]
  intro z hz hzT
  apply Finset.disjoint_left.mp hT
  · apply endpointVertices_completedRootExtensionState_subset_supportUnion
      W p radialIncremented incremented X
    change z ∈ cubicEdgeEndpointVertices
      (W.rootExtensionPrefixState p radialIncremented incremented id
        (rootExtensionDirectionOrder d).length X).explored at hz
    rw [RootRadialSeedProfile.rootExtensionPrefixState, List.take_length] at hz
    simpa [RootRadialSeedProfile.completedRootExtensionState] using hz
  · exact hzT

/-- Exact union of all earlier replay supports and the first `j` supports of the next canonical
non-root runtime. -/
noncomputable def replayRuntimePrefixRestartSupportUnion
    (hd : 0 < d) (hmn : 2 * m ≤ n)
    (W : RootRadialSeedProfile d m n) (root : F)
    (p radialIncremented : I) (delta : ℝ)
    (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) (history : List (F × Bool)) (j : ℕ) :
    Finset (CubicEdge d) :=
  let fullHistory := [(root, true)] ++ canonicalSuffix root history
  let S := replay hd hmn W root p radialIncremented delta incremented X history
  let queried := canonicalQueryFromFullHistory root fullHistory
  let seed := inletSeed hd root fullHistory queried S
  let incoming := incomingDirection hd root fullHistory queried
  let first := firstFlip hd root fullHistory queried S
  let directions := siteDirectionOrder hd root fullHistory queried
  replayRestartSupportUnion hd hmn W root p radialIncremented delta incremented X history ∪
    LaterSiteRuntime.restartSupportUnionFrom hmn seed.physicalCenter incoming first
      unusedSecondFlip p delta incremented X
        (siteInitialRuntime (m + n + 1) queried S seed) 0 (directions.take j)

/-- The source of the next runtime prefix is covered by the completed-root explored set and
the exact finite support union accumulated before slot `j`. -/
theorem endpointVertices_replayRuntimePrefix_subset_rooted_union_restartSupportUnion
    (hd : 0 < d) (hmn : 2 * m ≤ n)
    (W : RootRadialSeedProfile d m n) (root : F)
    (p radialIncremented : I) (delta : ℝ)
    (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) (history : List (F × Bool)) (j : ℕ) :
    let fullHistory := [(root, true)] ++ canonicalSuffix root history
    let S := replay hd hmn W root p radialIncremented delta incremented X history
    let queried := canonicalQueryFromFullHistory root fullHistory
    let seed := inletSeed hd root fullHistory queried S
    let incoming := incomingDirection hd root fullHistory queried
    let first := firstFlip hd root fullHistory queried S
    let directions := siteDirectionOrder hd root fullHistory queried
    let Rj := LaterSiteRuntime.runFrom hmn seed.physicalCenter incoming first
      unusedSecondFlip p delta incremented X
        (siteInitialRuntime (m + n + 1) queried S seed) 0 (directions.take j)
    cubicEdgeEndpointVertices Rj.source.explored ⊆
      cubicEdgeEndpointVertices
          (DynamicBlockHistoryState.rooted W root p radialIncremented delta incremented X
            ).source.explored ∪
        cubicEdgeEndpointVertices
          (replayRuntimePrefixRestartSupportUnion hd hmn W root p radialIncremented delta
            incremented X history j) := by
  dsimp only
  let fullHistory := [(root, true)] ++ canonicalSuffix root history
  let S := replay hd hmn W root p radialIncremented delta incremented X history
  let queried := canonicalQueryFromFullHistory root fullHistory
  let seed := inletSeed hd root fullHistory queried S
  let incoming := incomingDirection hd root fullHistory queried
  let first := firstFlip hd root fullHistory queried S
  let directions := siteDirectionOrder hd root fullHistory queried
  let R0 := siteInitialRuntime (m + n + 1) queried S seed
  let localSupport := LaterSiteRuntime.restartSupportUnionFrom hmn seed.physicalCenter incoming
    first unusedSecondFlip p delta incremented X R0 0 (directions.take j)
  have hlocal :=
    LaterSiteRuntime.endpointVertices_runFrom_subset_initial_union_restartSupportUnionFrom
      hmn seed.physicalCenter incoming first unusedSecondFlip p delta incremented X R0 0
        (directions.take j)
  have hreplay := endpointVertices_replay_subset_rooted_union_restartSupportUnion hd hmn W
    root p radialIncremented delta incremented X history
  intro z hz
  have hzLocal : z ∈ cubicEdgeEndpointVertices S.source.explored ∪
      cubicEdgeEndpointVertices localSupport := by
    simpa [R0, localSupport] using hlocal hz
  rcases Finset.mem_union.mp hzLocal with hzPrior | hzCurrent
  · have hzReplay : z ∈ cubicEdgeEndpointVertices
          (DynamicBlockHistoryState.rooted W root p radialIncremented delta incremented X
            ).source.explored ∪
        cubicEdgeEndpointVertices
          (replayRestartSupportUnion hd hmn W root p radialIncremented delta incremented X
            history) := by
      simpa [S] using hreplay hzPrior
    rcases Finset.mem_union.mp hzReplay with hzRoot | hzEarlier
    · exact Finset.mem_union_left _ hzRoot
    · exact Finset.mem_union_right _ <|
        mem_cubicEdgeEndpointVertices_iff.mpr <| by
          obtain ⟨e, he, hze⟩ := mem_cubicEdgeEndpointVertices_iff.mp hzEarlier
          exact ⟨e, Finset.mem_union_left _ he, hze⟩
  · exact Finset.mem_union_right _ <|
      mem_cubicEdgeEndpointVertices_iff.mpr <| by
        obtain ⟨e, he, hze⟩ := mem_cubicEdgeEndpointVertices_iff.mp hzCurrent
        exact ⟨e, Finset.mem_union_right _ he, hze⟩

/-- Reference-coordinate target freshness follows from two concrete physical separation
checks: one for the completed-root explored set and one for the exact finite union of all later
restart supports preceding the slot. -/
theorem replayRuntimePrefix_targetFresh_of_disjoint_rooted_and_restartSupportUnion
    (hd : 0 < d) (hmn : 2 * m ≤ n)
    (W : RootRadialSeedProfile d m n) (root : F)
    (p radialIncremented : I) (delta : ℝ)
    (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) (history : List (F × Bool))
    (j : ℕ)
    (hj : j < (siteDirectionOrder hd root
      ([(root, true)] ++ canonicalSuffix root history)
      (canonicalQueryFromFullHistory root
        ([(root, true)] ++ canonicalSuffix root history))).length)
    (hroot :
      let fullHistory := [(root, true)] ++ canonicalSuffix root history
      let S := replay hd hmn W root p radialIncremented delta incremented X history
      let queried := canonicalQueryFromFullHistory root fullHistory
      let seed := inletSeed hd root fullHistory queried S
      let incoming := incomingDirection hd root fullHistory queried
      let first := firstFlip hd root fullHistory queried S
      let directions := siteDirectionOrder hd root fullHistory queried
      let Rj := LaterSiteRuntime.runFrom hmn seed.physicalCenter incoming first
        unusedSecondFlip p delta incremented X
          (siteInitialRuntime (m + n + 1) queried S seed) 0 (directions.take j)
      let a := directions[j]
      let frame := cubicRestartFrameIso (Rj.slotCenterFor seed.physicalCenter a j) a
        (Rj.slotTransverseFlip incoming first unusedSecondFlip a j)
      Disjoint
        (cubicEdgeEndpointVertices
          (DynamicBlockHistoryState.rooted W root p radialIncremented delta incremented X
            ).source.explored)
        ((cubicEdgeEndpointVertices (seededBoundaryTargetSupport d a.1 m n)).image frame))
    (hsupport :
      let fullHistory := [(root, true)] ++ canonicalSuffix root history
      let S := replay hd hmn W root p radialIncremented delta incremented X history
      let queried := canonicalQueryFromFullHistory root fullHistory
      let seed := inletSeed hd root fullHistory queried S
      let incoming := incomingDirection hd root fullHistory queried
      let first := firstFlip hd root fullHistory queried S
      let directions := siteDirectionOrder hd root fullHistory queried
      let Rj := LaterSiteRuntime.runFrom hmn seed.physicalCenter incoming first
        unusedSecondFlip p delta incremented X
          (siteInitialRuntime (m + n + 1) queried S seed) 0 (directions.take j)
      let a := directions[j]
      let frame := cubicRestartFrameIso (Rj.slotCenterFor seed.physicalCenter a j) a
        (Rj.slotTransverseFlip incoming first unusedSecondFlip a j)
      Disjoint
        (cubicEdgeEndpointVertices
          (replayRuntimePrefixRestartSupportUnion hd hmn W root p radialIncremented delta
            incremented X history j))
        ((cubicEdgeEndpointVertices (seededBoundaryTargetSupport d a.1 m n)).image frame)) :
    let fullHistory := [(root, true)] ++ canonicalSuffix root history
    let S := replay hd hmn W root p radialIncremented delta incremented X history
    let queried := canonicalQueryFromFullHistory root fullHistory
    let seed := inletSeed hd root fullHistory queried S
    let incoming := incomingDirection hd root fullHistory queried
    let first := firstFlip hd root fullHistory queried S
    let directions := siteDirectionOrder hd root fullHistory queried
    let Rj := LaterSiteRuntime.runFrom hmn seed.physicalCenter incoming first
      unusedSecondFlip p delta incremented X
        (siteInitialRuntime (m + n + 1) queried S seed) 0 (directions.take j)
    let a := directions[j]
    let frame := cubicRestartFrameIso (Rj.slotCenterFor seed.physicalCenter a j) a
      (Rj.slotTransverseFlip incoming first unusedSecondFlip a j)
    Disjoint (cubicEdgeEndpointVertices (Rj.source.referenceExploredEdges frame))
      (cubicEdgeEndpointVertices (seededBoundaryTargetSupport d a.1 m n)) := by
  dsimp only at hroot hsupport ⊢
  let fullHistory := [(root, true)] ++ canonicalSuffix root history
  let S := replay hd hmn W root p radialIncremented delta incremented X history
  let queried := canonicalQueryFromFullHistory root fullHistory
  let seed := inletSeed hd root fullHistory queried S
  let incoming := incomingDirection hd root fullHistory queried
  let first := firstFlip hd root fullHistory queried S
  let directions := siteDirectionOrder hd root fullHistory queried
  let Rj := LaterSiteRuntime.runFrom hmn seed.physicalCenter incoming first
    unusedSecondFlip p delta incremented X
      (siteInitialRuntime (m + n + 1) queried S seed) 0 (directions.take j)
  let a := directions[j]
  let frame := cubicRestartFrameIso (Rj.slotCenterFor seed.physicalCenter a j) a
    (Rj.slotTransverseFlip incoming first unusedSecondFlip a j)
  have henvelope :=
    endpointVertices_replayRuntimePrefix_subset_rooted_union_restartSupportUnion hd hmn W
      root p radialIncremented delta incremented X history j
  have hphysical : Disjoint (cubicEdgeEndpointVertices Rj.source.explored)
      ((cubicEdgeEndpointVertices (seededBoundaryTargetSupport d a.1 m n)).image frame) := by
    rw [Finset.disjoint_left]
    intro z hzExplored hzTarget
    have hzEnvelope := henvelope hzExplored
    rcases Finset.mem_union.mp hzEnvelope with hzRoot | hzSupport
    · exact Finset.disjoint_left.mp hroot hzRoot hzTarget
    · exact Finset.disjoint_left.mp hsupport hzSupport hzTarget
  exact Rj.source.targetEndpointFresh_of_disjoint_physicalTarget frame
    (seededBoundaryTargetSupport d a.1 m n) hphysical

/-- Exact-support form of replay-prefix freshness.  The two hypotheses now mention only literal
finite unions of restart supports: the special root union and the chronological non-root union.
No coarse influence box or future semantic success appears in the interface. -/
theorem replayRuntimePrefix_targetFresh_of_disjoint_supportUnions
    (hd : 0 < d) (hmn : 2 * m ≤ n)
    (W : RootRadialSeedProfile d m n) (root : F)
    (p radialIncremented : I) (delta : ℝ)
    (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) (history : List (F × Bool))
    (j : ℕ)
    (hj : j < (siteDirectionOrder hd root
      ([(root, true)] ++ canonicalSuffix root history)
      (canonicalQueryFromFullHistory root
        ([(root, true)] ++ canonicalSuffix root history))).length)
    (hrootSupport :
      let fullHistory := [(root, true)] ++ canonicalSuffix root history
      let S := replay hd hmn W root p radialIncremented delta incremented X history
      let queried := canonicalQueryFromFullHistory root fullHistory
      let seed := inletSeed hd root fullHistory queried S
      let incoming := incomingDirection hd root fullHistory queried
      let first := firstFlip hd root fullHistory queried S
      let directions := siteDirectionOrder hd root fullHistory queried
      let Rj := LaterSiteRuntime.runFrom hmn seed.physicalCenter incoming first
        unusedSecondFlip p delta incremented X
          (siteInitialRuntime (m + n + 1) queried S seed) 0 (directions.take j)
      let a := directions[j]
      let frame := cubicRestartFrameIso (Rj.slotCenterFor seed.physicalCenter a j) a
        (Rj.slotTransverseFlip incoming first unusedSecondFlip a j)
      Disjoint
        (cubicEdgeEndpointVertices
          (completedRootExploredSupportUnion W p radialIncremented incremented X))
        ((cubicEdgeEndpointVertices (seededBoundaryTargetSupport d a.1 m n)).image frame))
    (hlaterSupport :
      let fullHistory := [(root, true)] ++ canonicalSuffix root history
      let S := replay hd hmn W root p radialIncremented delta incremented X history
      let queried := canonicalQueryFromFullHistory root fullHistory
      let seed := inletSeed hd root fullHistory queried S
      let incoming := incomingDirection hd root fullHistory queried
      let first := firstFlip hd root fullHistory queried S
      let directions := siteDirectionOrder hd root fullHistory queried
      let Rj := LaterSiteRuntime.runFrom hmn seed.physicalCenter incoming first
        unusedSecondFlip p delta incremented X
          (siteInitialRuntime (m + n + 1) queried S seed) 0 (directions.take j)
      let a := directions[j]
      let frame := cubicRestartFrameIso (Rj.slotCenterFor seed.physicalCenter a j) a
        (Rj.slotTransverseFlip incoming first unusedSecondFlip a j)
      Disjoint
        (cubicEdgeEndpointVertices
          (replayRuntimePrefixRestartSupportUnion hd hmn W root p radialIncremented delta
            incremented X history j))
        ((cubicEdgeEndpointVertices (seededBoundaryTargetSupport d a.1 m n)).image frame)) :
    let fullHistory := [(root, true)] ++ canonicalSuffix root history
    let S := replay hd hmn W root p radialIncremented delta incremented X history
    let queried := canonicalQueryFromFullHistory root fullHistory
    let seed := inletSeed hd root fullHistory queried S
    let incoming := incomingDirection hd root fullHistory queried
    let first := firstFlip hd root fullHistory queried S
    let directions := siteDirectionOrder hd root fullHistory queried
    let Rj := LaterSiteRuntime.runFrom hmn seed.physicalCenter incoming first
      unusedSecondFlip p delta incremented X
        (siteInitialRuntime (m + n + 1) queried S seed) 0 (directions.take j)
    let a := directions[j]
    let frame := cubicRestartFrameIso (Rj.slotCenterFor seed.physicalCenter a j) a
      (Rj.slotTransverseFlip incoming first unusedSecondFlip a j)
    Disjoint (cubicEdgeEndpointVertices (Rj.source.referenceExploredEdges frame))
      (cubicEdgeEndpointVertices (seededBoundaryTargetSupport d a.1 m n)) := by
  apply replayRuntimePrefix_targetFresh_of_disjoint_rooted_and_restartSupportUnion
    hd hmn W root p radialIncremented delta incremented X history j hj
  · dsimp only at hrootSupport ⊢
    exact rooted_target_disjoint_of_supportUnion_disjoint W root p radialIncremented delta
      incremented X _ hrootSupport
  · exact hlaterSupport

end DynamicBlockHistoryReplay

end Percolation
