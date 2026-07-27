import Percolation.Critical.DynamicRootMixedCompletion
import Percolation.Critical.DynamicMixedWitnessState

/-!
# Literal outgoing seeds of a completed root block

After the simultaneous radial phase, the root performs one source-state restart in every
signed direction.  This file names the actual mixed-threshold seed selected at each of those
slots.  These are the inlet anchors for later coarse sites.
-/

namespace Percolation

open scoped unitInterval

/-- An outgoing seed retains both its physical anchor and the target center in the local
reference frame.  The latter determines the compensating transverse mask at the child site. -/
structure LaterSiteOutgoingSeed (d : ℕ) where
  physicalCenter : Cubic d
  referenceCenter : Cubic d
  deriving DecidableEq

/-- Success along a finite source schedule implies success at each named slot, with the state
obtained from the literal preceding prefix. -/
theorem RootRadialSeedProfile.runPostRadialExtensionSuccesses_getElem
    {d m n : ℕ} (W : RootRadialSeedProfile d m n) (p : I) (delta : ℝ)
    (incremented : RootExtensionThresholdPolicy d) (X : CubicEdge d → ℝ)
    (S : SourceFiniteEdgeRevealState d) (directions : List (CubicDirection d))
    (hsuccess : W.runPostRadialExtensionSuccesses
      p delta incremented X S directions)
    (k : ℕ) (hk : k < directions.length) :
    let b := directions[k]
    let Sk := W.runPostRadialExtensions p incremented X S (directions.take k)
    let Q := Sk.framedQuery (W.physicalCenter b) b
      (oppositeTransverseRestartFlip b)
    X ∈ Q.successEvent m n p delta := by
  have hsplit : directions = directions.take k ++ directions.drop k :=
    (List.take_append_drop k directions).symm
  rw [hsplit, W.runPostRadialExtensionSuccesses_append] at hsuccess
  have htail := hsuccess.2
  rw [List.drop_eq_getElem_cons hk] at htail
  exact htail.1

/-- Every signed direction occurs in the fixed root-extension order. -/
theorem mem_rootExtensionDirectionOrder {d : ℕ} (a : CubicDirection d) :
    a ∈ rootExtensionDirectionOrder d := by
  simp [rootExtensionDirectionOrder]

/-- Slot occupied by a signed direction in the root schedule. -/
noncomputable def rootExtensionDirectionIndex {d : ℕ} (a : CubicDirection d) : ℕ :=
  (rootExtensionDirectionOrder d).idxOf a

theorem rootExtensionDirectionIndex_lt {d : ℕ} (a : CubicDirection d) :
    rootExtensionDirectionIndex a < (rootExtensionDirectionOrder d).length := by
  exact List.idxOf_lt_length_of_mem (mem_rootExtensionDirectionOrder a)

@[simp]
theorem rootExtensionDirectionOrder_get_directionIndex
    {d : ℕ} (a : CubicDirection d) :
    (rootExtensionDirectionOrder d)[rootExtensionDirectionIndex a]'
      (rootExtensionDirectionIndex_lt a) = a := by
  exact List.getElem_idxOf (rootExtensionDirectionIndex_lt a)

/-- Source state immediately before the root extension in direction `a`. -/
noncomputable def RootRadialSeedProfile.rootOutgoingPrefixState
    {d m n : ℕ} (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) (a : CubicDirection d) : SourceFiniteEdgeRevealState d :=
  W.rootExtensionPrefixState p radialIncremented incremented id
    (rootExtensionDirectionIndex a) X

/-- Canonical query whose selected target is the root's outgoing seed in direction `a`. -/
noncomputable def RootRadialSeedProfile.rootOutgoingQuery
    {d m n : ℕ} (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) (a : CubicDirection d) : FramedRestartQuery d :=
  (W.rootOutgoingPrefixState p radialIncremented incremented X a).framedQuery
    (W.physicalCenter a) a (oppositeTransverseRestartFlip a)

/-- The actual mixed-threshold target witness selected by that root extension. -/
noncomputable def RootRadialSeedProfile.rootOutgoingWitness
    {d m n : ℕ} (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (delta : ℝ)
    (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) (a : CubicDirection d) :
    Option (RestartSeedWitnessIndex d a.1 m n) :=
  (W.rootOutgoingPrefixState p radialIncremented incremented X a).selectedMixedWitness
    (W.physicalCenter a) a (oppositeTransverseRestartFlip a) p delta X

/-- Physical inlet anchor offered to a neighboring coarse site. -/
noncomputable def RootRadialSeedProfile.rootOutgoingSeedCenter
    {d m n : ℕ} (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (delta : ℝ)
    (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) (a : CubicDirection d) : Option (Cubic d) :=
  (W.rootOutgoingPrefixState p radialIncremented incremented X a
      ).selectedMixedPhysicalSeedCenter (m := m) (n := n)
    (W.physicalCenter a) a (oppositeTransverseRestartFlip a) p delta X

/-- Full outgoing record offered to the neighboring coarse site.  Besides its physical anchor,
it retains the physical displacement from the root coarse-site center needed by the child's
compensating turn. -/
noncomputable def RootRadialSeedProfile.rootOutgoingSeed
    {d m n : ℕ} (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (delta : ℝ)
    (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) (a : CubicDirection d) :
    Option (LaterSiteOutgoingSeed d) :=
  (W.rootOutgoingWitness p radialIncremented delta incremented X a).map fun U ↦
    let target := cubicRestartFrameIso (W.physicalCenter a) a
      (oppositeTransverseRestartFlip a) U.seedCenter.1
    ⟨target, cubicRelativePosition cubicOrigin target⟩

/-- Completion of all root slots implies success of the query in every signed direction. -/
theorem RootRadialSeedProfile.mem_rootOutgoingQuery_successEvent_of_completion
    {d m n : ℕ} (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (delta : ℝ)
    (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ)
    (hX : X ∈ W.mixedExtensionPrefixSuccessEvent p radialIncremented delta
      incremented (rootExtensionDirectionOrder d).length)
    (a : CubicDirection d) :
    X ∈ (W.rootOutgoingQuery p radialIncremented incremented X a).successEvent
      m n p delta := by
  have hfull : W.runPostRadialExtensionSuccesses p delta incremented X
      (rootPostRadialSourceEdgeState d m n p radialIncremented X)
      (rootExtensionDirectionOrder d) := by
    change X ∈ W.mixedRadialEvent p delta ∧
      W.runPostRadialExtensionSuccesses p delta incremented X
        (rootPostRadialSourceEdgeState d m n p radialIncremented X)
        ((rootExtensionDirectionOrder d).take
          (rootExtensionDirectionOrder d).length) at hX
    simpa only [List.take_length] using hX.2
  have hslot := W.runPostRadialExtensionSuccesses_getElem p delta incremented X
    (rootPostRadialSourceEdgeState d m n p radialIncremented X)
    (rootExtensionDirectionOrder d) hfull
    (rootExtensionDirectionIndex a) (rootExtensionDirectionIndex_lt a)
  simpa [RootRadialSeedProfile.rootOutgoingQuery,
    RootRadialSeedProfile.rootOutgoingPrefixState] using hslot

/-- Hence every completed root block exposes one literal outgoing seed in every direction. -/
theorem RootRadialSeedProfile.exists_rootOutgoingSeed_of_completion
    {d m n : ℕ} (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (delta : ℝ)
    (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ)
    (hX : X ∈ W.mixedExtensionPrefixSuccessEvent p radialIncremented delta
      incremented (rootExtensionDirectionOrder d).length)
    (a : CubicDirection d) :
    ∃ U : RestartSeedWitnessIndex d a.1 m n,
      W.rootOutgoingSeedCenter p radialIncremented delta incremented X a =
        some (cubicRestartFrameIso (W.physicalCenter a) a
          (oppositeTransverseRestartFlip a) U.seedCenter.1) ∧
      U.IsMixedRestartWitness
        (W.rootOutgoingQuery p radialIncremented incremented X a).region p
        (W.rootOutgoingQuery p radialIncremented incremented X a).beta delta
        (cubicGraphIsoCouplingReindex
          (cubicRestartFrameIso (W.physicalCenter a) a
            (oppositeTransverseRestartFlip a)) X) := by
  let S := W.rootOutgoingPrefixState p radialIncremented incremented X a
  have hsuccess := W.mem_rootOutgoingQuery_successEvent_of_completion
    p radialIncremented delta incremented X hX a
  simpa [RootRadialSeedProfile.rootOutgoingSeedCenter,
    RootRadialSeedProfile.rootOutgoingQuery, S] using
      S.exists_selectedMixedPhysicalSeedCenter_of_success
        (W.physicalCenter a) a (oppositeTransverseRestartFlip a) p delta X hsuccess

/-- Completed-root form of `rootOutgoingSeed`: the full child-steering record is present and
its reference center is the selected physical displacement from the root coarse-site center. -/
theorem RootRadialSeedProfile.exists_rootOutgoingSeedData_of_completion
    {d m n : ℕ} (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (delta : ℝ)
    (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ)
    (hX : X ∈ W.mixedExtensionPrefixSuccessEvent p radialIncremented delta
      incremented (rootExtensionDirectionOrder d).length)
    (a : CubicDirection d) :
    ∃ U : RestartSeedWitnessIndex d a.1 m n,
      W.rootOutgoingSeed p radialIncremented delta incremented X a =
        (let target := cubicRestartFrameIso (W.physicalCenter a) a
            (oppositeTransverseRestartFlip a) U.seedCenter.1;
          some ⟨target, cubicRelativePosition cubicOrigin target⟩) ∧
      U.IsMixedRestartWitness
        (W.rootOutgoingQuery p radialIncremented incremented X a).region p
        (W.rootOutgoingQuery p radialIncremented incremented X a).beta delta
        (cubicGraphIsoCouplingReindex
          (cubicRestartFrameIso (W.physicalCenter a) a
            (oppositeTransverseRestartFlip a)) X) := by
  let S := W.rootOutgoingPrefixState p radialIncremented incremented X a
  have hsuccess := W.mem_rootOutgoingQuery_successEvent_of_completion
    p radialIncremented delta incremented X hX a
  obtain ⟨U, hselected, hU⟩ := S.exists_selectedMixedWitness_of_success
    (W.physicalCenter a) a (oppositeTransverseRestartFlip a) p delta X hsuccess
  refine ⟨U, ?_, ?_⟩
  · simpa [RootRadialSeedProfile.rootOutgoingSeed,
      RootRadialSeedProfile.rootOutgoingWitness, S, hselected]
  · simpa [RootRadialSeedProfile.rootOutgoingQuery, S] using hU

/-- Every root-published inlet anchor lies in the literal half-way box joining the root coarse
site to the advertised signed neighbor.  This keeps the sharper bond-box location needed by
the two inlet restarts; the coarser radius-`2N` endpoint-box bound loses that information. -/
theorem RootRadialSeedProfile.rootOutgoingSeed_physicalCenter_mem_halfwayBox_of_completion
    {d m n : ℕ} (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (delta : ℝ)
    (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ)
    (hX : X ∈ W.mixedExtensionPrefixSuccessEvent p radialIncremented delta
      incremented (rootExtensionDirectionOrder d).length)
    (a : CubicDirection d) (U : LaterSiteOutgoingSeed d)
    (hU : W.rootOutgoingSeed p radialIncremented delta incremented X a = some U) :
    U.physicalCenter ∈
      grimmettMarstrandHalfwayBox d (m + n + 1) cubicOrigin a := by
  obtain ⟨V, hVSeed, hV⟩ := W.exists_rootOutgoingSeedData_of_completion
    p radialIncremented delta incremented X hX a
  have hUeq : U.physicalCenter = W.postRadialFrame a V.seedCenter.1 := by
    have hrecord := Option.some.inj (hU.symm.trans hVSeed)
    simpa [RootRadialSeedProfile.postRadialFrame] using
      congrArg LaterSiteOutgoingSeed.physicalCenter hrecord
  have hc : SeedBoxWithinBoundaryLayer d a.1 m n (W a).seedCenter.1 :=
    (hX.1.2 a).1.2.2.1
  have hq : SeedBoxWithinBoundaryLayer d a.1 m n V.seedCenter.1 :=
    hV.1.2.2.1
  let qref := cubicTranslate cubicOrigin (W a).seedCenter.1
    (cubicRestartFrameIso cubicOrigin (a.1, true)
      (oppositeTransverseRestartFlip (a.1, true)) V.seedCenter.1)
  have hqref : qref ∈
      grimmettMarstrandHalfwayBox d (m + n + 1) cubicOrigin (a.1, true) := by
    exact translated_compensating_seedCenter_mem_referenceHalfwayBox
      a.1 hc hq
  have himage : W.postRadialFrame a V.seedCenter.1 ∈
      cubicGraphIsoRegion
        (cubicRestartFrameIso cubicOrigin a (rootRadialTransverseFlip a))
        (grimmettMarstrandHalfwayBox d (m + n + 1) cubicOrigin (a.1, true)) := by
    refine ⟨qref, hqref, ?_⟩
    exact (W.postRadialFrame_apply a V.seedCenter.1).symm
  rw [hUeq]
  exact cubicRestartFrameIso_referenceHalfwayBox_subset_halfwayBox
    cubicOrigin a (rootRadialTransverseFlip a) himage

/-- Every outgoing seed advertised by a completed root block has already been absorbed into
the completed source exploration.  This is the root-to-later-site inlet invariant: the first
restart at a child is therefore based on an actually revealed open seed, rather than merely
on the center selected by the successful root query. -/
theorem RootRadialSeedProfile.rootOutgoingSeed_seedBox_subset_completedExplored
    {d m n : ℕ} [NeZero d] (hm : 1 ≤ m) (hmn : m + 1 < n)
    (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (delta : ℝ)
    (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ)
    (hadds : W.PolicyAddsOnPrefixes p radialIncremented delta incremented)
    (hX : X ∈ W.mixedExtensionPrefixSuccessEvent p radialIncremented delta
      incremented (rootExtensionDirectionOrder d).length)
    (a : CubicDirection d) (U : LaterSiteOutgoingSeed d)
    (hU : W.rootOutgoingSeed p radialIncremented delta incremented X a = some U) :
    cubicBoxEdges d U.physicalCenter m ⊆
      (W.completedRootExtensionState p radialIncremented incremented X).explored := by
  classical
  let k := rootExtensionDirectionIndex a
  have hk : k < (rootExtensionDirectionOrder d).length :=
    rootExtensionDirectionIndex_lt a
  let S := W.rootOutgoingPrefixState p radialIncremented incremented X a
  obtain ⟨V, hVSeed, hV⟩ := W.exists_rootOutgoingSeedData_of_completion
    p radialIncremented delta incremented X hX a
  have hUeq : U =
      (let target := cubicRestartFrameIso (W.physicalCenter a) a
          (oppositeTransverseRestartFlip a) V.seedCenter.1;
        ⟨target, cubicRelativePosition cubicOrigin target⟩) := by
    exact Option.some.inj (hU.symm.trans hVSeed)
  subst U
  have hgeom : ∀ b : CubicDirection d,
      SeedBoxWithinBoundaryLayer d b.1 m n (W b).seedCenter.1 := fun b ↦
    (hX.1.2 b).1.2.2.1
  have hfresh :
      let F := cubicRestartFrameIso (W.physicalCenter a) a
        (oppositeTransverseRestartFlip a)
      Disjoint (cubicEdgeEndpointVertices (S.referenceExploredEdges F))
        (cubicEdgeEndpointVertices (seededBoundaryTargetSupport d a.1 m n)) := by
    simpa [S, k, RootRadialSeedProfile.rootOutgoingPrefixState,
      RootRadialSeedProfile.postRadialFrame] using
      (rootPostRadialExtensions_prefix_targetEndpointFresh_of_geometry
        hm hmn W p radialIncremented incremented X hgeom hk)
  have hincremented : ∀ e ∈ (S.framedQuery (W.physicalCenter a) a
      (oppositeTransverseRestartFlip a)).boundarySupport n,
      (incremented S a e : ℝ) =
        ((S.framedQuery (W.physicalCenter a) a
          (oppositeTransverseRestartFlip a)).physicalBoundaryThreshold e : ℝ) + delta := by
    intro e _he
    rw [S.framedQuery_physicalBoundaryThreshold]
    simpa [S, k, RootRadialSeedProfile.rootOutgoingPrefixState] using
      hadds X k hk e
  have hseedNext := S.mixedWitness_seedBox_subset_nextExplored_of_eq
    (W.physicalCenter a) a (oppositeTransverseRestartFlip a)
    p delta (incremented S a) X hfresh hincremented V
    (by simpa [RootRadialSeedProfile.rootOutgoingQuery, S] using hV)
  have hseedPrefix :
      cubicBoxEdges d
          (cubicRestartFrameIso (W.physicalCenter a) a
            (oppositeTransverseRestartFlip a) V.seedCenter.1) m ⊆
        (W.rootExtensionPrefixState p radialIncremented incremented id (k + 1) X).explored := by
    rw [W.rootExtensionPrefixState_succ p radialIncremented incremented id hk X]
    simpa [S, k, RootRadialSeedProfile.rootOutgoingPrefixState] using hseedNext
  have hprefixFull := W.explored_subset_runPostRadialExtensions p incremented X
    (W.rootExtensionPrefixState p radialIncremented incremented id (k + 1) X)
    ((rootExtensionDirectionOrder d).drop (k + 1))
  apply hseedPrefix.trans
  simpa [RootRadialSeedProfile.rootExtensionPrefixState,
    RootRadialSeedProfile.completedRootExtensionState,
    ← W.runPostRadialExtensions_append, List.take_append_drop] using hprefixFull

end Percolation
