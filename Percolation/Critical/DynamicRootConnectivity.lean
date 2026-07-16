import Percolation.Critical.DynamicRootOutgoingSeeds
import Percolation.Critical.DynamicSourceConnectivity

/-!
# Pathwise connectivity of the completed root block

The special root construction starts from a fully open central seed, performs the simultaneous
radial reveal, and then performs one source restart in every signed direction.  This module
proves that the resulting accumulated source state is one open component at any final density
dominating all thresholds used by those updates.
-/

namespace Percolation

open scoped unitInterval

/-- Every vertex in a coordinate box is joined to its center by a walk whose edges remain in
the box. -/
theorem exists_cubicWalk_center_supported_in_box
    {d m : ℕ} (center x : Cubic d) (hx : x ∈ cubicMetricBox d center m) :
    ∃ w : (cubicGraph d).Walk center x,
      walkEdgeFinset w ⊆ cubicBoxEdges d center m := by
  obtain ⟨w, hwBetween⟩ := exists_cubicWalk_support_between d center x
  refine ⟨w, walkEdgeFinset_subset_cubicBoxEdges_of_support w ?_⟩
  intro z hz
  have hzBetween := hwBetween z hz
  have hcenter : center ∈ cubicMetricBox d center m := by
    rw [mem_cubicMetricBox]
    intro i
    omega
  rw [mem_cubicMetricBox] at hcenter hx ⊢
  intro i
  rcases hzBetween i with hzi | hzi
  · exact ⟨(hcenter i).1.trans hzi.1, hzi.2.trans (hx i).2⟩
  · exact ⟨(hx i).1.trans hzi.1, hzi.2.trans (hcenter i).2⟩

/-- The fully open central seed initializes the root-connected source invariant. -/
theorem rootInitialSourceEdgeState_rootedOpen
    {d m : ℕ} (p pFinal : I) (X : CubicEdge d → ℝ)
    (hseed : X ∈ rootSeedLabelEvent d m p)
    (hpFinal : (p : ℝ) ≤ (pFinal : ℝ)) :
    (rootInitialSourceEdgeState d m p).RootedOpen
      (thresholdConfiguration pFinal X) cubicOrigin := by
  have hopen : (rootInitialExploredEdges d m : Set (CubicEdge d)) ⊆
      thresholdConfiguration pFinal X := by
    intro e he
    exact (hseed he).trans_le hpFinal
  refine ⟨hopen, ?_⟩
  intro e he x hx
  have hxBox : x ∈ cubicMetricBox d cubicOrigin m :=
    endpoint_mem_cubicMetricBox_of_edge_mem_cubicBoxEdges he hx
  obtain ⟨w, hwBox⟩ :=
    exists_cubicWalk_center_supported_in_box cubicOrigin x hxBox
  refine ⟨w, ?_⟩
  intro f hf
  let e : CubicEdge d := ⟨f, w.edges_subset_edgeSet hf⟩
  exact hopen (hwBox ((mem_walkEdgeFinset_iff w e).mpr hf))

/-- The simultaneous radial update preserves origin connectivity.  Success of the radial
targets is not needed for this closure fact; it is used separately to ensure that all required
outgoing seeds exist. -/
theorem rootPostRadialSourceEdgeState_rootedOpen
    {d m n : ℕ} (p radialIncremented pFinal : I)
    (X : CubicEdge d → ℝ)
    (hseed : X ∈ rootSeedLabelEvent d m p)
    (hpFinal : (p : ℝ) ≤ (pFinal : ℝ))
    (hradialFinal : (radialIncremented : ℝ) ≤ (pFinal : ℝ)) :
    (rootPostRadialSourceEdgeState d m n p radialIncremented X).RootedOpen
      (thresholdConfiguration pFinal X) cubicOrigin := by
  exact (rootInitialSourceEdgeState d m p).rootedOpen_next
    (rootRadialEdgeSupport d m n) p pFinal (fun _ ↦ radialIncremented) X
      (rootInitialSourceEdgeState_rootedOpen p pFinal X hseed hpFinal)
      hpFinal (fun _ ↦ hradialFinal)

/-- Origin connectivity propagates through any list of post-radial root extensions. -/
theorem RootRadialSeedProfile.runPostRadialExtensions_rootedOpen
    {d m n : ℕ} (W : RootRadialSeedProfile d m n)
    (p pFinal : I) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) (S : SourceFiniteEdgeRevealState d)
    (directions : List (CubicDirection d))
    (hrooted : S.RootedOpen (thresholdConfiguration pFinal X) cubicOrigin)
    (hpFinal : (p : ℝ) ≤ (pFinal : ℝ))
    (hincrementedFinal : ∀ S a e,
      (incremented S a e : ℝ) ≤ (pFinal : ℝ)) :
    (W.runPostRadialExtensions p incremented X S directions).RootedOpen
      (thresholdConfiguration pFinal X) cubicOrigin := by
  induction directions generalizing S with
  | nil => exact hrooted
  | cons a rest ih =>
      let Q := S.framedQuery (W.physicalCenter a) a
        (oppositeTransverseRestartFlip a)
      apply ih
      exact S.rootedOpen_next (Q.restartSupport m n) p pFinal
        (incremented S a) X hrooted hpFinal (hincrementedFinal S a)

/-- The literal completed root state used to initialize history replay is one open component
rooted at the physical origin. -/
theorem RootRadialSeedProfile.completedRootExtensionState_rootedOpen
    {d m n : ℕ} (W : RootRadialSeedProfile d m n)
    (p radialIncremented pFinal : I) (delta : ℝ)
    (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ)
    (hcompletion : X ∈ W.mixedExtensionPrefixSuccessEvent p radialIncremented
      delta incremented (rootExtensionDirectionOrder d).length)
    (hpFinal : (p : ℝ) ≤ (pFinal : ℝ))
    (hradialFinal : (radialIncremented : ℝ) ≤ (pFinal : ℝ))
    (hincrementedFinal : ∀ S a e,
      (incremented S a e : ℝ) ≤ (pFinal : ℝ)) :
    (W.completedRootExtensionState p radialIncremented incremented X).RootedOpen
      (thresholdConfiguration pFinal X) cubicOrigin := by
  have hseed : X ∈ rootSeedLabelEvent d m p := hcompletion.1.1
  have hpost := rootPostRadialSourceEdgeState_rootedOpen (n := n)
    p radialIncremented pFinal X hseed hpFinal hradialFinal
  simpa [RootRadialSeedProfile.completedRootExtensionState] using
    W.runPostRadialExtensions_rootedOpen p pFinal incremented X
      (rootPostRadialSourceEdgeState d m n p radialIncremented X)
      (rootExtensionDirectionOrder d) hpost hpFinal hincrementedFinal

end Percolation
