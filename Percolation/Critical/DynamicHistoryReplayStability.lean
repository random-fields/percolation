import Percolation.Critical.DynamicHistoryReplayFinite

/-!
# Exact-cell stability of dynamic-block history replay

Finite range is useful only when each accumulated reveal-history cell reproduces the same
coarse replay state.  This file begins that semantic layer with the completed root: its source
state and its full outgoing seed table are both constant on the terminal source-history cell.
-/

namespace Percolation

open scoped unitInterval

namespace DynamicBlockHistoryReplay

/-- A later root-prefix accumulated-history cell refines every earlier prefix cell. -/
theorem rootExtensionPrefixState_historyProfile_event_subset_of_le
    {d m n : ℕ} (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (incremented : RootExtensionThresholdPolicy d)
    (hmono : ∀ S a e, S.lower e ≤ incremented S a e)
    (X : CubicEdge d → ℝ) {k l : ℕ} (hkl : k ≤ l) :
    (W.rootExtensionPrefixState p radialIncremented incremented id l X
      ).historyProfile.event ⊆
      (W.rootExtensionPrefixState p radialIncremented incremented id k X
        ).historyProfile.event := by
  let initial := rootPostRadialSourceEdgeState d m n p radialIncremented X
  let directions := (rootExtensionDirectionOrder d).take l
  have htake : directions.take k = (rootExtensionDirectionOrder d).take k := by
    simp only [directions, List.take_take]
    congr 1
    omega
  have hsplit : directions = directions.take k ++ directions.drop k :=
    (List.take_append_drop k directions).symm
  rw [RootRadialSeedProfile.rootExtensionPrefixState,
    RootRadialSeedProfile.rootExtensionPrefixState]
  change (W.runPostRadialExtensions p incremented X initial directions
      ).historyProfile.event ⊆
    (W.runPostRadialExtensions p incremented X initial
      ((rootExtensionDirectionOrder d).take k)).historyProfile.event
  rw [hsplit, W.runPostRadialExtensions_append, htake]
  exact W.runPostRadialExtensions_historyProfile_event_subset p incremented hmono X
    (W.runPostRadialExtensions p incremented X initial
      ((rootExtensionDirectionOrder d).take k)) (directions.drop k)

/-- A realization in the radial event and the common nonnegative support belongs to every
root-prefix cell generated from itself. -/
theorem mem_rootExtensionPrefixState_historyProfile
    {d m n : ℕ} [NeZero d]
    (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (delta : ℝ)
    (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) (hroot : X ∈ rootRadialEvent d m n p delta)
    (hnonnegative : X ∈ SourceFiniteEdgeRevealState.nonnegativeCouplingEvent)
    (k : ℕ) :
    X ∈ (W.rootExtensionPrefixState p radialIncremented incremented id k X
      ).historyProfile.event := by
  apply W.mem_runPostRadialExtensions_historyProfile p incremented X
  · exact hnonnegative
  · exact rootRadialEvent_mem_postRadialSourceHistoryProfile
      p radialIncremented delta X hroot hnonnegative

/-- The selected outgoing witness at one completed-root direction is constant throughout the
terminal root source-history cell. -/
theorem rootOutgoingWitness_eq_of_mem_terminalHistoryProfile
    {d m n : ℕ} [NeZero d] (hm : 1 ≤ m) (hmn : m + 1 < n)
    (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (delta : ℝ)
    (incremented : RootExtensionThresholdPolicy d)
    (hmono : ∀ S a e, S.lower e ≤ incremented S a e)
    (hadds : W.PolicyAddsOnPrefixes p radialIncremented delta incremented)
    (hgeom : ∀ a : CubicDirection d,
      SeedBoxWithinBoundaryLayer d a.1 m n (W a).seedCenter.1)
    (X Y : CubicEdge d → ℝ)
    (hroot : X ∈ rootRadialEvent d m n p delta)
    (hnonnegative : X ∈ SourceFiniteEdgeRevealState.nonnegativeCouplingEvent)
    (hY : Y ∈
      (W.rootExtensionPrefixState p radialIncremented incremented id
        (rootExtensionDirectionOrder d).length X).historyProfile.event)
    (a : CubicDirection d) :
    W.rootOutgoingWitness p radialIncremented delta incremented Y a =
      W.rootOutgoingWitness p radialIncremented delta incremented X a := by
  let k := rootExtensionDirectionIndex a
  have hk : k < (rootExtensionDirectionOrder d).length :=
    rootExtensionDirectionIndex_lt a
  let SX := W.rootExtensionPrefixState p radialIncremented incremented id k X
  have hYprefix : Y ∈ SX.historyProfile.event := by
    exact rootExtensionPrefixState_historyProfile_event_subset_of_le W p radialIncremented
      incremented hmono X hk.le hY
  have hstate :
      W.rootExtensionPrefixState p radialIncremented incremented id k Y = SX := by
    exact W.rootExtensionPrefixState_eq_of_mem_historyProfile p radialIncremented
      incremented hmono k X Y hYprefix
  have hYnext : Y ∈
      (SX.next
        ((SX.framedQuery (W.physicalCenter a) a
          (oppositeTransverseRestartFlip a)).restartSupport m n)
        p (incremented SX a) X).historyProfile.event := by
    have hsubset := rootExtensionPrefixState_historyProfile_event_subset_of_le W
      p radialIncremented incremented hmono X (Nat.succ_le_iff.mpr hk) hY
    simpa [SX, k, W.rootExtensionPrefixState_succ p radialIncremented incremented id hk,
      rootExtensionDirectionOrder_get_directionIndex] using hsubset
  have hcurrent : X ∈ SX.historyProfile.event := by
    exact mem_rootExtensionPrefixState_historyProfile W p radialIncremented delta
      incremented X hroot hnonnegative k
  have hfresh :
      let F := cubicRestartFrameIso (W.physicalCenter a) a
        (oppositeTransverseRestartFlip a)
      Disjoint (cubicEdgeEndpointVertices (SX.referenceExploredEdges F))
        (cubicEdgeEndpointVertices (seededBoundaryTargetSupport d a.1 m n)) := by
    simpa [SX, k, RootRadialSeedProfile.postRadialFrame,
      rootExtensionDirectionOrder_get_directionIndex] using
      (rootPostRadialExtensions_prefix_targetEndpointFresh_of_geometry
        hm hmn W p radialIncremented incremented X hgeom hk)
  have hselected :
      SX.selectedMixedWitness (m := m) (n := n)
          (W.physicalCenter a) a (oppositeTransverseRestartFlip a) p delta Y =
        SX.selectedMixedWitness (m := m) (n := n)
          (W.physicalCenter a) a (oppositeTransverseRestartFlip a) p delta X := by
    unfold SourceFiniteEdgeRevealState.selectedMixedWitness
    apply SX.selectedMixedRestartSeedWitness_eq_of_mem_nextHistoryProfile
      (W.physicalCenter a) a (oppositeTransverseRestartFlip a) p delta
        (incremented SX a) X Y hfresh
    · intro e _he
      rw [SX.framedQuery_physicalBoundaryThreshold]
      simpa [SX, k, rootExtensionDirectionOrder_get_directionIndex] using
        hadds X k hk e
    · exact hcurrent
    · exact hnonnegative
    · exact hYnext
  unfold RootRadialSeedProfile.rootOutgoingWitness
    RootRadialSeedProfile.rootOutgoingPrefixState
  change (W.rootExtensionPrefixState p radialIncremented incremented id k Y
      ).selectedMixedWitness (W.physicalCenter a) a
        (oppositeTransverseRestartFlip a) p delta Y =
    (W.rootExtensionPrefixState p radialIncremented incremented id k X
      ).selectedMixedWitness (W.physicalCenter a) a
        (oppositeTransverseRestartFlip a) p delta X
  rw [hstate]
  exact hselected

/-- The entire completed-root global replay state is constant on its terminal accumulated
source-history cell. -/
theorem rooted_eq_of_mem_terminalHistoryProfile
    {d m n : ℕ} {F : Set (Cubic d)} [LinearOrder F] [NeZero d]
    (hm : 1 ≤ m) (hmn : m + 1 < n)
    (W : RootRadialSeedProfile d m n) (root : F)
    (p radialIncremented : I) (delta : ℝ)
    (incremented : RootExtensionThresholdPolicy d)
    (hmono : ∀ S a e, S.lower e ≤ incremented S a e)
    (hadds : W.PolicyAddsOnPrefixes p radialIncremented delta incremented)
    (hgeom : ∀ a : CubicDirection d,
      SeedBoxWithinBoundaryLayer d a.1 m n (W a).seedCenter.1)
    (X Y : CubicEdge d → ℝ)
    (hroot : X ∈ rootRadialEvent d m n p delta)
    (hnonnegative : X ∈ SourceFiniteEdgeRevealState.nonnegativeCouplingEvent)
    (hY : Y ∈
      (DynamicBlockHistoryState.rooted W root p radialIncremented delta incremented X
        ).source.historyProfile.event) :
    DynamicBlockHistoryState.rooted W root p radialIncremented delta incremented Y =
      DynamicBlockHistoryState.rooted W root p radialIncremented delta incremented X := by
  have hsource := W.rootExtensionPrefixState_eq_of_mem_historyProfile p radialIncremented
    incremented hmono (rootExtensionDirectionOrder d).length X Y hY
  let SY := DynamicBlockHistoryState.rooted W root p radialIncremented delta incremented Y
  let SX := DynamicBlockHistoryState.rooted W root p radialIncremented delta incremented X
  have hs : SY.source = SX.source := by
    simpa [SY, SX, DynamicBlockHistoryState.rooted] using hsource
  have ho : SY.outgoing = SX.outgoing := by
    funext v a
    by_cases hvr : v = root
    · subst v
      simp only [SY, SX, DynamicBlockHistoryState.rooted, if_pos]
      unfold RootRadialSeedProfile.rootOutgoingSeed
      rw [rootOutgoingWitness_eq_of_mem_terminalHistoryProfile hm hmn W p
        radialIncremented delta incremented hmono hadds hgeom X Y hroot
        hnonnegative hY a]
    · simp [SY, SX, DynamicBlockHistoryState.rooted, hvr]
  change SY = SX
  exact DynamicBlockHistoryState.ext hs ho

/-- A complete later-site step refines the incoming accumulated source-history cell. -/
theorem step_historyProfile_event_subset
    {d m n : ℕ} {F : Set (Cubic d)} [LinearOrder F]
    (hd : 0 < d) (hmn : 2 * m ≤ n) (root : F)
    (history : List (F × Bool)) (v : F) (accepted : Bool)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (hmono : ∀ S a e, S.lower e ≤ incremented S a e)
    (X : CubicEdge d → ℝ) (S : DynamicBlockHistoryState d F) :
    (step hd hmn root history v accepted p delta incremented X S
      ).source.historyProfile.event ⊆ S.source.historyProfile.event := by
  let seed := inletSeed hd root history v S
  let incoming := incomingDirection hd root history v
  let first := firstFlip hd root history v S
  let directions := siteDirectionOrder hd root history v
  simpa [step, siteRuntime, seed, incoming, first, directions] using
    LaterSiteRuntime.runFrom_historyProfile_event_subset hmn seed.physicalCenter incoming
      first unusedSecondFlip p delta incremented hmono X
      (LaterSiteRuntime.initial S.source seed.physicalCenter) 0
      directions

/-- On the common nonnegative support, a realization belongs to the terminal source-history
cell generated by its own complete later-site step. -/
theorem mem_step_historyProfile
    {d m n : ℕ} {F : Set (Cubic d)} [LinearOrder F]
    (hd : 0 < d) (hmn : 2 * m ≤ n) (root : F)
    (history : List (F × Bool)) (v : F) (accepted : Bool)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) (S : DynamicBlockHistoryState d F)
    (hcurrent : X ∈ S.source.historyProfile.event)
    (hnonnegative : X ∈ SourceFiniteEdgeRevealState.nonnegativeCouplingEvent) :
    X ∈ (step hd hmn root history v accepted p delta incremented X S
      ).source.historyProfile.event := by
  let seed := inletSeed hd root history v S
  let incoming := incomingDirection hd root history v
  let first := firstFlip hd root history v S
  let directions := siteDirectionOrder hd root history v
  simpa [step, siteRuntime, seed, incoming, first, directions] using
    LaterSiteRuntime.mem_runFrom_historyProfile hmn seed.physicalCenter incoming
      first unusedSecondFlip p delta incremented X
      (LaterSiteRuntime.initial S.source seed.physicalCenter) 0
      directions hnonnegative (by simpa using hcurrent)

/-- Exact-cell stability of one complete later-site decision.  The two hypotheses are precisely
the reachable threshold-budget and endpoint-freshness obligations for its at most `4d` slots. -/
theorem step_eq_of_mem_terminalHistoryProfile
    {d m n : ℕ} {F : Set (Cubic d)} [LinearOrder F]
    (hd : 0 < d) (hmn : 2 * m ≤ n) (root : F)
    (history : List (F × Bool)) (v : F) (accepted : Bool)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (hmono : ∀ S a e, S.lower e ≤ incremented S a e)
    (X Y : CubicEdge d → ℝ) (S : DynamicBlockHistoryState d F)
    (hcurrent : X ∈ S.source.historyProfile.event)
    (hnonnegative : X ∈ SourceFiniteEdgeRevealState.nonnegativeCouplingEvent)
    (hadds :
      let seed := inletSeed hd root history v S
      let incoming := incomingDirection hd root history v
      let first := firstFlip hd root history v S
      let directions := siteDirectionOrder hd root history v
      ∀ j (hj : j < directions.length) e,
        let Rj := LaterSiteRuntime.runFrom hmn seed.physicalCenter incoming
          first unusedSecondFlip p delta incremented X
          (LaterSiteRuntime.initial S.source seed.physicalCenter) 0
          (directions.take j)
        let a := directions[j]
        (incremented Rj.source a e : ℝ) = (Rj.source.lower e : ℝ) + delta)
    (hfresh :
      let seed := inletSeed hd root history v S
      let incoming := incomingDirection hd root history v
      let first := firstFlip hd root history v S
      let directions := siteDirectionOrder hd root history v
      ∀ j (hj : j < directions.length),
        let Rj := LaterSiteRuntime.runFrom hmn seed.physicalCenter incoming
          first unusedSecondFlip p delta incremented X
          (LaterSiteRuntime.initial S.source seed.physicalCenter) 0
          (directions.take j)
        let a := directions[j]
        let center := Rj.slotCenterFor seed.physicalCenter a j
        let flip := Rj.slotTransverseFlip incoming first unusedSecondFlip a j
        let frame := cubicRestartFrameIso center a flip
        Disjoint (cubicEdgeEndpointVertices (Rj.source.referenceExploredEdges frame))
          (cubicEdgeEndpointVertices (seededBoundaryTargetSupport d a.1 m n)))
    (hY : Y ∈ (step hd hmn root history v accepted p delta incremented X S
      ).source.historyProfile.event) :
    step hd hmn root history v accepted p delta incremented Y S =
      step hd hmn root history v accepted p delta incremented X S := by
  let seed := inletSeed hd root history v S
  let incoming := incomingDirection hd root history v
  let first := firstFlip hd root history v S
  let directions := siteDirectionOrder hd root history v
  have hrun :
      LaterSiteRuntime.runFrom hmn seed.physicalCenter incoming first unusedSecondFlip
          p delta incremented Y (LaterSiteRuntime.initial S.source seed.physicalCenter) 0
            directions =
        LaterSiteRuntime.runFrom hmn seed.physicalCenter incoming first unusedSecondFlip
          p delta incremented X (LaterSiteRuntime.initial S.source seed.physicalCenter) 0
            directions := by
    apply LaterSiteRuntime.runFrom_eq_of_mem_historyProfile hmn seed.physicalCenter incoming
      first unusedSecondFlip p delta incremented hmono X Y
      (LaterSiteRuntime.initial S.source seed.physicalCenter) 0
      directions
    · simpa [seed, incoming, first, directions] using hadds
    · simpa [seed, incoming, first, directions] using hfresh
    · simpa using hcurrent
    · exact hnonnegative
    · simpa [step, siteRuntime, seed, incoming, first, directions] using hY
  unfold step siteRuntime
  simp only
  rw [hrun]

/-- Replaying a fixed suffix from a fixed state refines that state's source-history cell. -/
theorem replayFrom_historyProfile_event_subset
    {d m n : ℕ} {F : Set (Cubic d)} [LinearOrder F]
    (hd : 0 < d) (hmn : 2 * m ≤ n) (root : F)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (hmono : ∀ S a e, S.lower e ≤ incremented S a e)
    (X : CubicEdge d → ℝ) (prior suffix : List (F × Bool))
    (S : DynamicBlockHistoryState d F) :
    (replayFrom hd hmn root p delta incremented X prior S suffix
      ).source.historyProfile.event ⊆ S.source.historyProfile.event := by
  induction suffix generalizing prior S with
  | nil => exact Set.Subset.rfl
  | cons head rest ih =>
      rcases head with ⟨v, accepted⟩
      exact (ih (prior ++ [(v, accepted)])
        (step hd hmn root prior v accepted p delta incremented X S)).trans
          (step_historyProfile_event_subset hd hmn root prior v accepted p delta
            incremented hmono X S)

/-- On the common nonnegative support, a realization belongs to the terminal source-history
cell produced by replaying any fixed suffix from a cell containing it. -/
theorem mem_replayFrom_historyProfile
    {d m n : ℕ} {F : Set (Cubic d)} [LinearOrder F]
    (hd : 0 < d) (hmn : 2 * m ≤ n) (root : F)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) (prior suffix : List (F × Bool))
    (S : DynamicBlockHistoryState d F)
    (hcurrent : X ∈ S.source.historyProfile.event)
    (hnonnegative : X ∈ SourceFiniteEdgeRevealState.nonnegativeCouplingEvent) :
    X ∈ (replayFrom hd hmn root p delta incremented X prior S suffix
      ).source.historyProfile.event := by
  induction suffix generalizing prior S with
  | nil => exact hcurrent
  | cons head rest ih =>
      rcases head with ⟨v, accepted⟩
      exact ih (prior ++ [(v, accepted)])
        (step hd hmn root prior v accepted p delta incremented X S)
        (mem_step_historyProfile hd hmn root prior v accepted p delta incremented X S
          hcurrent hnonnegative)

/-- Exact replay stability from a fixed incoming global state, assuming the one-step
exact-cell lemma at each state encountered by the fixed source realization. -/
theorem replayFrom_eq_of_mem_terminalHistoryProfile
    {d m n : ℕ} {F : Set (Cubic d)} [LinearOrder F]
    (hd : 0 < d) (hmn : 2 * m ≤ n) (root : F)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (hmono : ∀ S a e, S.lower e ≤ incremented S a e)
    (X Y : CubicEdge d → ℝ) (prior suffix : List (F × Bool))
    (S : DynamicBlockHistoryState d F)
    (hcurrent : X ∈ S.source.historyProfile.event)
    (hnonnegative : X ∈ SourceFiniteEdgeRevealState.nonnegativeCouplingEvent)
    (hstepStable : ∀ (prior' : List (F × Bool)) (v : F) (accepted : Bool)
      (T : DynamicBlockHistoryState d F),
      X ∈ T.source.historyProfile.event →
      Y ∈ (step hd hmn root prior' v accepted p delta incremented X T
        ).source.historyProfile.event →
      step hd hmn root prior' v accepted p delta incremented Y T =
        step hd hmn root prior' v accepted p delta incremented X T)
    (hY : Y ∈ (replayFrom hd hmn root p delta incremented X prior S suffix
      ).source.historyProfile.event) :
    replayFrom hd hmn root p delta incremented Y prior S suffix =
      replayFrom hd hmn root p delta incremented X prior S suffix := by
  induction suffix generalizing prior S with
  | nil => rfl
  | cons head rest ih =>
      rcases head with ⟨v, accepted⟩
      let T := step hd hmn root prior v accepted p delta incremented X S
      have hYstep : Y ∈ T.source.historyProfile.event := by
        exact replayFrom_historyProfile_event_subset hd hmn root p delta incremented
          hmono X (prior ++ [(v, accepted)]) rest T hY
      have hstep :
          step hd hmn root prior v accepted p delta incremented Y S = T :=
        hstepStable prior v accepted S hcurrent hYstep
      have hcurrentT : X ∈ T.source.historyProfile.event :=
        mem_step_historyProfile hd hmn root prior v accepted p delta incremented X S
          hcurrent hnonnegative
      change replayFrom hd hmn root p delta incremented Y (prior ++ [(v, accepted)])
          (step hd hmn root prior v accepted p delta incremented Y S) rest =
        replayFrom hd hmn root p delta incremented X (prior ++ [(v, accepted)]) T rest
      rw [hstep]
      exact ih (prior ++ [(v, accepted)]) T hcurrentT hY

/-- The full concrete dynamic-block replay is constant on its terminal source-history cell.
The only remaining inputs are the reachable one-step budget/freshness facts, packaged here as
the local stability premise. -/
theorem replay_eq_of_mem_terminalHistoryProfile
    {d m n : ℕ} {F : Set (Cubic d)} [LinearOrder F] [NeZero d]
    (hm : 1 ≤ m) (hmn : 2 * m ≤ n) (hmnStrict : m + 1 < n) (hd : 0 < d)
    (W : RootRadialSeedProfile d m n) (root : F)
    (p radialIncremented : I) (delta : ℝ)
    (incremented : RootExtensionThresholdPolicy d)
    (hmono : ∀ S a e, S.lower e ≤ incremented S a e)
    (haddsRoot : W.PolicyAddsOnPrefixes p radialIncremented delta incremented)
    (hgeomRoot : ∀ a : CubicDirection d,
      SeedBoxWithinBoundaryLayer d a.1 m n (W a).seedCenter.1)
    (X Y : CubicEdge d → ℝ) (history : List (F × Bool))
    (hroot : X ∈ rootRadialEvent d m n p delta)
    (hnonnegative : X ∈ SourceFiniteEdgeRevealState.nonnegativeCouplingEvent)
    (hstepStable : ∀ (prior' : List (F × Bool)) (v : F) (accepted : Bool)
      (T : DynamicBlockHistoryState d F),
      X ∈ T.source.historyProfile.event →
      Y ∈ (step hd hmn root prior' v accepted p delta incremented X T
        ).source.historyProfile.event →
      step hd hmn root prior' v accepted p delta incremented Y T =
        step hd hmn root prior' v accepted p delta incremented X T)
    (hY : Y ∈ (replay hd hmn W root p radialIncremented delta incremented X
      history).source.historyProfile.event) :
    replay hd hmn W root p radialIncremented delta incremented Y history =
      replay hd hmn W root p radialIncremented delta incremented X history := by
  let SX := DynamicBlockHistoryState.rooted W root p radialIncremented delta incremented X
  let SY := DynamicBlockHistoryState.rooted W root p radialIncremented delta incremented Y
  let suffix := canonicalSuffix root history
  have hYroot : Y ∈ SX.source.historyProfile.event := by
    exact replayFrom_historyProfile_event_subset hd hmn root p delta incremented
      hmono X [(root, true)] suffix SX (by simpa [replay, SX, suffix] using hY)
  have hrooted : SY = SX := by
    exact rooted_eq_of_mem_terminalHistoryProfile hm hmnStrict W root p radialIncremented
      delta incremented hmono haddsRoot hgeomRoot X Y hroot hnonnegative hYroot
  have hcurrent : X ∈ SX.source.historyProfile.event := by
    exact mem_rootExtensionPrefixState_historyProfile W p radialIncremented delta
      incremented X hroot hnonnegative (rootExtensionDirectionOrder d).length
  change replayFrom hd hmn root p delta incremented Y [(root, true)] SY suffix =
    replayFrom hd hmn root p delta incremented X [(root, true)] SX suffix
  rw [hrooted]
  exact replayFrom_eq_of_mem_terminalHistoryProfile hd hmn root p delta
    incremented hmono X Y [(root, true)] suffix SX hcurrent hnonnegative
      hstepStable (by simpa [replay, SX, suffix] using hY)

end DynamicBlockHistoryReplay

end Percolation
