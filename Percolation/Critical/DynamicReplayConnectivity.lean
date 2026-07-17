import Percolation.Critical.DynamicLaterSiteConnectivity
import Percolation.Critical.DynamicRootConnectivity
import Percolation.Critical.DynamicReachableConnectivity
import Percolation.Critical.DynamicReplayStageLaw

/-!
# Connectivity invariant for the complete history replay

The accumulated edge state is shared by accepted and rejected coarse queries.  Once the
completed root state is connected to the physical origin, every total runtime step preserves
that fact.  Consequently every edge and every installed seed retained by an arbitrary replay
belongs to the same final-density open component.
-/

namespace Percolation

open scoped unitInterval

namespace DynamicBlockHistoryState

/-- In positive dimension, the center of a nontrivial coordinate box is incident to one of its
internal edges. -/
theorem center_mem_cubicEdgeEndpointVertices_cubicBoxEdges
    {d m : ℕ} [NeZero d] (hm : 1 ≤ m) (center : Cubic d) :
    center ∈ cubicEdgeEndpointVertices (cubicBoxEdges d center m) := by
  classical
  let i : Fin d := 0
  let a : CubicDirection d := (i, true)
  have hcenter : center ∈ cubicMetricBox d center m := by
    rw [mem_cubicMetricBox]
    intro j
    omega
  have hstep : cubicStepFrom center a ∈ cubicMetricBox d center m := by
    rw [mem_cubicMetricBox]
    intro j
    by_cases hji : j = i
    · subst j
      simp [a, cubicStepFrom, cubicDirectionIncrement]
      omega
    · simp [a, cubicStepFrom, cubicDirectionIncrement, hji]
  apply mem_cubicEdgeEndpointVertices_iff.mpr
  refine ⟨cubicStepEdge center a,
    cubicStepEdge_mem_cubicBoxEdges hcenter hstep, ?_⟩
  simp [cubicStepEdge]

/-- An installed nontrivial seed box in a root-connected source state has its center connected
to the source anchor. -/
theorem connection_seedCenter_of_box_subset
    {d m : ℕ} [NeZero d] (hm : 1 ≤ m)
    {S : SourceFiniteEdgeRevealState d} {omega : EdgeConfiguration d}
    {anchor center : Cubic d}
    (hrooted : S.RootedOpen omega anchor)
    (hseed : cubicBoxEdges d center m ⊆ S.explored) :
    omega ∈ connectionEvent d anchor center := by
  obtain ⟨e, heBox, hcenter⟩ := mem_cubicEdgeEndpointVertices_iff.mp
    (center_mem_cubicEdgeEndpointVertices_cubicBoxEdges hm center)
  exact hrooted.2 e (hseed heBox) center hcenter

/-- Region-confined version of `connection_seedCenter_of_box_subset`. -/
theorem connection_seedCenterWithin_of_box_subset
    {d m : ℕ} [NeZero d] (hm : 1 ≤ m)
    {S : SourceFiniteEdgeRevealState d} {omega : EdgeConfiguration d}
    {A : Set (Cubic d)} {anchor center : Cubic d}
    (hrooted : S.RootedOpenWithin omega A anchor)
    (hseed : cubicBoxEdges d center m ⊆ S.explored) :
    omega ∈ connectionEventWithinVertices d A anchor center := by
  obtain ⟨e, heBox, hcenter⟩ := mem_cubicEdgeEndpointVertices_iff.mp
    (center_mem_cubicEdgeEndpointVertices_cubicBoxEdges hm center)
  exact hrooted.2 e (hseed heBox) center hcenter

/-- Every seed record published by a globally installed, root-connected history state names a
center in the same open component as the root anchor. -/
theorem outgoing_physicalCenter_connected
    {d m : ℕ} [NeZero d] (hm : 1 ≤ m)
    {V : Type*} {S : DynamicBlockHistoryState d V}
    {omega : EdgeConfiguration d} {anchor : Cubic d}
    (hrooted : S.source.RootedOpen omega anchor)
    (hinstalled : S.SeedBoxesInstalled (m := m))
    {v : V} {a : CubicDirection d} {U : LaterSiteOutgoingSeed d}
    (hU : S.outgoing v a = some U) :
    omega ∈ connectionEvent d anchor U.physicalCenter := by
  exact connection_seedCenter_of_box_subset hm hrooted (hinstalled v a U hU)

/-- Every installed seed center is connected to the root by a witness supported in `A` when
the accumulated source state carries the confined invariant. -/
theorem outgoing_physicalCenter_connectedWithin
    {d m : ℕ} [NeZero d] (hm : 1 ≤ m)
    {V : Type*} {S : DynamicBlockHistoryState d V}
    {omega : EdgeConfiguration d} {A : Set (Cubic d)} {anchor : Cubic d}
    (hrooted : S.source.RootedOpenWithin omega A anchor)
    (hinstalled : S.SeedBoxesInstalled (m := m))
    {v : V} {a : CubicDirection d} {U : LaterSiteOutgoingSeed d}
    (hU : S.outgoing v a = some U) :
    omega ∈ connectionEventWithinVertices d A anchor U.physicalCenter := by
  exact connection_seedCenterWithin_of_box_subset hm hrooted (hinstalled v a U hU)

/-- The source field of the initialized global history state is exactly the connected completed
root source state. -/
theorem rooted_source_rootedOpen
    {d m n : ℕ} {V : Type*} [DecidableEq V]
    (W : RootRadialSeedProfile d m n) (root : V)
    (p radialIncremented pFinal : I) (delta : ℝ)
    (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ)
    (hcompletion : X ∈ W.mixedExtensionPrefixSuccessEvent p radialIncremented
      delta incremented (rootExtensionDirectionOrder d).length)
    (hpFinal : (p : ℝ) ≤ (pFinal : ℝ))
    (hradialFinal : (radialIncremented : ℝ) ≤ (pFinal : ℝ))
    (hincrementedFinal : ∀ S a e,
      (incremented S a e : ℝ) ≤ (pFinal : ℝ)) :
    (rooted W root p radialIncremented delta incremented X).source.RootedOpen
      (thresholdConfiguration pFinal X) cubicOrigin := by
  change (W.runPostRadialExtensions p incremented X
      (rootPostRadialSourceEdgeState d m n p radialIncremented X)
      ((rootExtensionDirectionOrder d).take
        (rootExtensionDirectionOrder d).length)).RootedOpen
    (thresholdConfiguration pFinal X) cubicOrigin
  rw [List.take_length]
  exact W.completedRootExtensionState_rootedOpen p radialIncremented pFinal delta
    incremented X hcompletion hpFinal hradialFinal hincrementedFinal

/-- Reachable-prefix version of the initialized-history connectivity theorem. -/
theorem rooted_source_rootedOpen_of_prefixBounds
    {d m n : ℕ} {V : Type*} [DecidableEq V]
    (W : RootRadialSeedProfile d m n) (root : V)
    (p radialIncremented pFinal : I) (delta : ℝ)
    (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ)
    (hcompletion : X ∈ W.mixedExtensionPrefixSuccessEvent p radialIncremented
      delta incremented (rootExtensionDirectionOrder d).length)
    (hpFinal : (p : ℝ) ≤ (pFinal : ℝ))
    (hradialFinal : (radialIncremented : ℝ) ≤ (pFinal : ℝ))
    (hbounded : W.FinalThresholdBoundedOnPrefixes p pFinal incremented X
      (rootPostRadialSourceEdgeState d m n p radialIncremented X)
      (rootExtensionDirectionOrder d)) :
    (rooted W root p radialIncremented delta incremented X).source.RootedOpen
      (thresholdConfiguration pFinal X) cubicOrigin := by
  change (W.runPostRadialExtensions p incremented X
      (rootPostRadialSourceEdgeState d m n p radialIncremented X)
      ((rootExtensionDirectionOrder d).take
        (rootExtensionDirectionOrder d).length)).RootedOpen
    (thresholdConfiguration pFinal X) cubicOrigin
  rw [List.take_length]
  exact W.completedRootExtensionState_rootedOpen_of_prefixBounds p radialIncremented
      pFinal delta incremented X hcompletion hpFinal hradialFinal hbounded

/-- Initialized-history connectivity whose retained witness walks all stay in `A`. -/
theorem rooted_source_rootedOpenWithin_of_prefixBounds
    {d m n : ℕ} {V : Type*} [DecidableEq V] {A : Set (Cubic d)}
    (W : RootRadialSeedProfile d m n) (root : V)
    (p radialIncremented pFinal : I) (delta : ℝ)
    (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ)
    (hcompletion : X ∈ W.mixedExtensionPrefixSuccessEvent p radialIncremented
      delta incremented (rootExtensionDirectionOrder d).length)
    (hpFinal : (p : ℝ) ≤ (pFinal : ℝ))
    (hradialFinal : (radialIncremented : ℝ) ≤ (pFinal : ℝ))
    (hboxA : (cubicMetricBox d cubicOrigin m : Set (Cubic d)) ⊆ A)
    (hradialA : (cubicEdgeEndpointVertices (rootRadialEdgeSupport d m n) :
      Set (Cubic d)) ⊆ A)
    (hbounded : W.FinalThresholdBoundedOnPrefixes p pFinal incremented X
      (rootPostRadialSourceEdgeState d m n p radialIncremented X)
      (rootExtensionDirectionOrder d))
    (hstageA : ∀ j (hj : j < (rootExtensionDirectionOrder d).length),
      let S := W.runPostRadialExtensions p incremented X
        (rootPostRadialSourceEdgeState d m n p radialIncremented X)
        ((rootExtensionDirectionOrder d).take j)
      let a := (rootExtensionDirectionOrder d)[j]
      let Q := S.framedQuery (W.physicalCenter a) a
        (oppositeTransverseRestartFlip a)
      (cubicEdgeEndpointVertices (Q.restartSupport m n) : Set (Cubic d)) ⊆ A) :
    (rooted W root p radialIncremented delta incremented X).source.RootedOpenWithin
      (thresholdConfiguration pFinal X) A cubicOrigin := by
  change (W.runPostRadialExtensions p incremented X
      (rootPostRadialSourceEdgeState d m n p radialIncremented X)
      ((rootExtensionDirectionOrder d).take
        (rootExtensionDirectionOrder d).length)).RootedOpenWithin
    (thresholdConfiguration pFinal X) A cubicOrigin
  rw [List.take_length]
  exact W.completedRootExtensionState_rootedOpenWithin_of_prefixBounds p radialIncremented
    pFinal delta incremented X hcompletion hpFinal hradialFinal hboxA hradialA hbounded
      hstageA

/-- The root phase is automatically confined to the literal Grimmett--Marstrand thickening
when the coarse region contains the origin and all of its signed nearest neighbours.  This is
the exact specialization used for the planar coarse region after adjoining finitely many root
neighbours; it avoids requiring the source-facing construction to explore a direction outside
its coarse region. -/
theorem rooted_source_rootedOpenWithin_thickening_of_neighbors
    {d m n : ℕ} {V : Type*} [DecidableEq V] {F : Set (Cubic d)}
    (W : RootRadialSeedProfile d m n) (root : V)
    (p radialIncremented pFinal : I) (delta : ℝ)
    (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ)
    (hcompletion : X ∈ W.mixedExtensionPrefixSuccessEvent p radialIncremented
      delta incremented (rootExtensionDirectionOrder d).length)
    (hpFinal : (p : ℝ) ≤ (pFinal : ℝ))
    (hradialFinal : (radialIncremented : ℝ) ≤ (pFinal : ℝ))
    (hrootF : cubicOrigin ∈ F)
    (hneighborsF : ∀ a : CubicDirection d, cubicStepFrom cubicOrigin a ∈ F)
    (hbounded : W.FinalThresholdBoundedOnPrefixes p pFinal incremented X
      (rootPostRadialSourceEdgeState d m n p radialIncremented X)
      (rootExtensionDirectionOrder d)) :
    (rooted W root p radialIncremented delta incremented X).source.RootedOpenWithin
      (thresholdConfiguration pFinal X)
      (grimmettMarstrandThickening d F (m + n + 1)) cubicOrigin := by
  apply rooted_source_rootedOpenWithin_of_prefixBounds W root p radialIncremented pFinal
    delta incremented X hcompletion hpFinal hradialFinal
  · apply grimmettMarstrandCenteredBox_subset_thickening
      (N := m + n + 1) (R := m) hrootF
    omega
  · exact rootRadialEdgeSupport_endpointVertices_subset_thickening hrootF
  · exact hbounded
  · intro j hj
    dsimp only
    let a := (rootExtensionDirectionOrder d)[j]
    let S := W.runPostRadialExtensions p incremented X
      (rootPostRadialSourceEdgeState d m n p radialIncremented X)
      ((rootExtensionDirectionOrder d).take j)
    have hgeom : SeedBoxWithinBoundaryLayer d a.1 m n (W a).seedCenter.1 :=
      (hcompletion.1.2 a).1.2.2.1
    intro z hz
    rcases W.endpointVertices_postRadialQuery_subset_endpointBoxes_of_geometry
        a S hgeom hz with hz | hz
    · exact grimmettMarstrandCenteredBox_subset_thickening hrootF le_rfl hz
    · exact grimmettMarstrandCenteredBox_subset_thickening (hneighborsF a) le_rfl hz

end DynamicBlockHistoryState

namespace DynamicBlockHistoryReplay

variable {d m n : ℕ} {F : Set (Cubic d)} [LinearOrder F]

/-- One total coarse-site replay step preserves the origin-connected source invariant,
regardless of whether the coarse site is accepted. -/
theorem step_source_rootedOpen
    (hd : 0 < d) (hmn : 2 * m ≤ n)
    (root : F) (history : List (F × Bool)) (v : F) (accepted : Bool)
    (p pFinal : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) (S : DynamicBlockHistoryState d F)
    (hrooted : S.source.RootedOpen (thresholdConfiguration pFinal X) cubicOrigin)
    (hpFinal : (p : ℝ) ≤ (pFinal : ℝ))
    (hincrementedFinal : ∀ T a e,
      (incremented T a e : ℝ) ≤ (pFinal : ℝ)) :
    (step hd hmn root history v accepted p delta incremented X S
      ).source.RootedOpen (thresholdConfiguration pFinal X) cubicOrigin := by
  let seed := inletSeed hd root history v S
  let incoming := incomingDirection hd root history v
  let first := firstFlip hd root history v S
  let directions := siteDirectionOrder hd root history v
  let R0 := LaterSiteRuntime.initial S.source seed.physicalCenter
  have hR0 : R0.source.RootedOpen (thresholdConfiguration pFinal X) cubicOrigin := by
    simpa [R0, LaterSiteRuntime.initial] using hrooted
  have hrun := LaterSiteRuntime.rootedOpen_runFrom hmn seed.physicalCenter incoming first
    unusedSecondFlip p pFinal delta incremented X cubicOrigin R0 0 directions
      hR0 hpFinal hincrementedFinal
  simpa [step, siteRuntime, seed, incoming, first, directions, R0] using hrun

/-- One replay step preserves root connectivity from threshold bounds on only its actual
runtime prefixes. -/
theorem step_source_rootedOpen_of_prefixBounds
    (hd : 0 < d) (hmn : 2 * m ≤ n)
    (root : F) (history : List (F × Bool)) (v : F) (accepted : Bool)
    (p pFinal : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) (S : DynamicBlockHistoryState d F)
    (hrooted : S.source.RootedOpen (thresholdConfiguration pFinal X) cubicOrigin)
    (hpFinal : (p : ℝ) ≤ (pFinal : ℝ))
    (hbounded :
      let seed := inletSeed hd root history v S
      let incoming := incomingDirection hd root history v
      let first := firstFlip hd root history v S
      let directions := siteDirectionOrder hd root history v
      LaterSiteRuntime.FinalThresholdBoundedOnPrefixes hmn seed.physicalCenter incoming
        first unusedSecondFlip p pFinal delta incremented X
        (LaterSiteRuntime.initial S.source seed.physicalCenter) 0 directions) :
    (step hd hmn root history v accepted p delta incremented X S
      ).source.RootedOpen (thresholdConfiguration pFinal X) cubicOrigin := by
  let seed := inletSeed hd root history v S
  let incoming := incomingDirection hd root history v
  let first := firstFlip hd root history v S
  let directions := siteDirectionOrder hd root history v
  let R0 := LaterSiteRuntime.initial S.source seed.physicalCenter
  have hR0 : R0.source.RootedOpen (thresholdConfiguration pFinal X) cubicOrigin := by
    simpa [R0, LaterSiteRuntime.initial] using hrooted
  have hrun := LaterSiteRuntime.rootedOpen_runFrom_of_prefixBounds hmn
    seed.physicalCenter incoming first unusedSecondFlip p pFinal delta incremented X
      cubicOrigin R0 0 directions hR0 hpFinal hbounded
  simpa [step, siteRuntime, seed, incoming, first, directions, R0] using hrun

/-- One replay step preserves region-confined connectivity when each literal runtime stage is
contained in `A`. -/
theorem step_source_rootedOpenWithin_of_prefixBounds
    (hd : 0 < d) (hmn : 2 * m ≤ n) {A : Set (Cubic d)}
    (root : F) (history : List (F × Bool)) (v : F) (accepted : Bool)
    (p pFinal : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) (S : DynamicBlockHistoryState d F)
    (hrooted : S.source.RootedOpenWithin
      (thresholdConfiguration pFinal X) A cubicOrigin)
    (hpFinal : (p : ℝ) ≤ (pFinal : ℝ))
    (hbounded :
      let seed := inletSeed hd root history v S
      let incoming := incomingDirection hd root history v
      let first := firstFlip hd root history v S
      let directions := siteDirectionOrder hd root history v
      LaterSiteRuntime.FinalThresholdBoundedOnPrefixes hmn seed.physicalCenter incoming
        first unusedSecondFlip p pFinal delta incremented X
        (LaterSiteRuntime.initial S.source seed.physicalCenter) 0 directions)
    (hstageA :
      let seed := inletSeed hd root history v S
      let incoming := incomingDirection hd root history v
      let first := firstFlip hd root history v S
      let directions := siteDirectionOrder hd root history v
      ∀ j (hj : j < directions.length),
        let Rj := LaterSiteRuntime.runFrom hmn seed.physicalCenter incoming first
          unusedSecondFlip p delta incremented X
          (LaterSiteRuntime.initial S.source seed.physicalCenter) 0 (directions.take j)
        let a := directions[j]
        let Q := Rj.restartQuery seed.physicalCenter incoming first unusedSecondFlip a j
        (cubicEdgeEndpointVertices (Q.restartSupport m n) : Set (Cubic d)) ⊆ A) :
    (step hd hmn root history v accepted p delta incremented X S
      ).source.RootedOpenWithin (thresholdConfiguration pFinal X) A cubicOrigin := by
  let seed := inletSeed hd root history v S
  let incoming := incomingDirection hd root history v
  let first := firstFlip hd root history v S
  let directions := siteDirectionOrder hd root history v
  let R0 := LaterSiteRuntime.initial S.source seed.physicalCenter
  have hR0 : R0.source.RootedOpenWithin
      (thresholdConfiguration pFinal X) A cubicOrigin := by
    simpa [R0, LaterSiteRuntime.initial] using hrooted
  have hrun := LaterSiteRuntime.rootedOpenWithin_runFrom_of_prefixBounds hmn
    seed.physicalCenter incoming first unusedSecondFlip p pFinal delta incremented X
      cubicOrigin R0 0 directions hR0 hpFinal hbounded (by simpa [R0] using hstageA)
  simpa [step, siteRuntime, seed, incoming, first, directions, R0] using hrun

/-- Origin connectivity propagates through an arbitrary literal replay suffix. -/
theorem replayFrom_source_rootedOpen
    (hd : 0 < d) (hmn : 2 * m ≤ n)
    (root : F) (p pFinal : I) (delta : ℝ)
    (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ)
    (prior : List (F × Bool)) (S : DynamicBlockHistoryState d F)
    (history : List (F × Bool))
    (hrooted : S.source.RootedOpen (thresholdConfiguration pFinal X) cubicOrigin)
    (hpFinal : (p : ℝ) ≤ (pFinal : ℝ))
    (hincrementedFinal : ∀ T a e,
      (incremented T a e : ℝ) ≤ (pFinal : ℝ)) :
    (replayFrom hd hmn root p delta incremented X prior S history
      ).source.RootedOpen (thresholdConfiguration pFinal X) cubicOrigin := by
  induction history generalizing prior S with
  | nil => exact hrooted
  | cons entry rest ih =>
      rcases entry with ⟨v, accepted⟩
      apply ih
      exact step_source_rootedOpen hd hmn root prior v accepted p pFinal delta
        incremented X S hrooted hpFinal hincrementedFinal

/-- Origin connectivity through a replay suffix under bounds on only the concrete runtime
prefixes selected at each recorded history entry. -/
theorem replayFrom_source_rootedOpen_of_prefixBounds
    (hd : 0 < d) (hmn : 2 * m ≤ n)
    (root : F) (p pFinal : I) (delta : ℝ)
    (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ)
    (prior : List (F × Bool)) (S : DynamicBlockHistoryState d F)
    (history : List (F × Bool))
    (hrooted : S.source.RootedOpen (thresholdConfiguration pFinal X) cubicOrigin)
    (hpFinal : (p : ℝ) ≤ (pFinal : ℝ))
    (hbounded : ∀ (pref : List (F × Bool)) (v : F) (accepted : Bool)
      (tail : List (F × Bool)),
      history = pref ++ (v, accepted) :: tail →
      let T := replayFrom hd hmn root p delta incremented X prior S pref
      let fullHistory := prior ++ pref
      let seed := inletSeed hd root fullHistory v T
      let incoming := incomingDirection hd root fullHistory v
      let first := firstFlip hd root fullHistory v T
      let directions := siteDirectionOrder hd root fullHistory v
      LaterSiteRuntime.FinalThresholdBoundedOnPrefixes hmn seed.physicalCenter incoming
        first unusedSecondFlip p pFinal delta incremented X
        (LaterSiteRuntime.initial T.source seed.physicalCenter) 0 directions) :
    (replayFrom hd hmn root p delta incremented X prior S history
      ).source.RootedOpen (thresholdConfiguration pFinal X) cubicOrigin := by
  induction history generalizing prior S with
  | nil => exact hrooted
  | cons entry rest ih =>
      rcases entry with ⟨v, accepted⟩
      have hfirst := hbounded [] v accepted rest (by simp)
      have hstep := step_source_rootedOpen_of_prefixBounds hd hmn root prior v accepted
        p pFinal delta incremented X S hrooted hpFinal
        (by simpa [replayFrom] using hfirst)
      apply ih (prior := prior ++ [(v, accepted)])
        (S := step hd hmn root prior v accepted p delta incremented X S) hstep
      intro pref u b tail heq
      have hall := hbounded ((v, accepted) :: pref) u b tail (by simpa using heq)
      simpa [replayFrom, List.append_assoc] using hall

/-- Region-confined connectivity through a replay suffix under threshold and containment
certificates on every concrete runtime prefix. -/
theorem replayFrom_source_rootedOpenWithin_of_prefixBounds
    (hd : 0 < d) (hmn : 2 * m ≤ n) {A : Set (Cubic d)}
    (root : F) (p pFinal : I) (delta : ℝ)
    (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ)
    (prior : List (F × Bool)) (S : DynamicBlockHistoryState d F)
    (history : List (F × Bool))
    (hrooted : S.source.RootedOpenWithin
      (thresholdConfiguration pFinal X) A cubicOrigin)
    (hpFinal : (p : ℝ) ≤ (pFinal : ℝ))
    (hbounded : ∀ (pref : List (F × Bool)) (v : F) (accepted : Bool)
      (tail : List (F × Bool)),
      history = pref ++ (v, accepted) :: tail →
      let T := replayFrom hd hmn root p delta incremented X prior S pref
      let fullHistory := prior ++ pref
      let seed := inletSeed hd root fullHistory v T
      let incoming := incomingDirection hd root fullHistory v
      let first := firstFlip hd root fullHistory v T
      let directions := siteDirectionOrder hd root fullHistory v
      LaterSiteRuntime.FinalThresholdBoundedOnPrefixes hmn seed.physicalCenter incoming
        first unusedSecondFlip p pFinal delta incremented X
        (LaterSiteRuntime.initial T.source seed.physicalCenter) 0 directions)
    (hstageA : ∀ (pref : List (F × Bool)) (v : F) (accepted : Bool)
      (tail : List (F × Bool)),
      history = pref ++ (v, accepted) :: tail →
      let T := replayFrom hd hmn root p delta incremented X prior S pref
      let fullHistory := prior ++ pref
      let seed := inletSeed hd root fullHistory v T
      let incoming := incomingDirection hd root fullHistory v
      let first := firstFlip hd root fullHistory v T
      let directions := siteDirectionOrder hd root fullHistory v
      ∀ j (hj : j < directions.length),
        let Rj := LaterSiteRuntime.runFrom hmn seed.physicalCenter incoming first
          unusedSecondFlip p delta incremented X
          (LaterSiteRuntime.initial T.source seed.physicalCenter) 0 (directions.take j)
        let a := directions[j]
        let Q := Rj.restartQuery seed.physicalCenter incoming first unusedSecondFlip a j
        (cubicEdgeEndpointVertices (Q.restartSupport m n) : Set (Cubic d)) ⊆ A) :
    (replayFrom hd hmn root p delta incremented X prior S history
      ).source.RootedOpenWithin (thresholdConfiguration pFinal X) A cubicOrigin := by
  induction history generalizing prior S with
  | nil => exact hrooted
  | cons entry rest ih =>
      rcases entry with ⟨v, accepted⟩
      have hfirst := hbounded [] v accepted rest (by simp)
      have hfirstA := hstageA [] v accepted rest (by simp)
      have hstep := step_source_rootedOpenWithin_of_prefixBounds hd hmn root prior v
        accepted p pFinal delta incremented X S hrooted hpFinal
        (by simpa [replayFrom] using hfirst) (by simpa [replayFrom] using hfirstA)
      apply ih (prior := prior ++ [(v, accepted)])
        (S := step hd hmn root prior v accepted p delta incremented X S) hstep
      · intro pref u b tail heq
        have hall := hbounded ((v, accepted) :: pref) u b tail (by simpa using heq)
        simpa [replayFrom, List.append_assoc] using hall
      · intro pref u b tail heq
        have hall := hstageA ((v, accepted) :: pref) u b tail (by simpa using heq)
        simpa [replayFrom, List.append_assoc] using hall

/-- Every accumulated source state produced by the canonical global replay is a single open
component rooted at the physical origin. -/
theorem replay_source_rootedOpen
    (hd : 0 < d) (hmn : 2 * m ≤ n)
    (W : RootRadialSeedProfile d m n) (root : F)
    (p radialIncremented pFinal : I) (delta : ℝ)
    (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) (history : List (F × Bool))
    (hcompletion : X ∈ W.mixedExtensionPrefixSuccessEvent p radialIncremented
      delta incremented (rootExtensionDirectionOrder d).length)
    (hpFinal : (p : ℝ) ≤ (pFinal : ℝ))
    (hradialFinal : (radialIncremented : ℝ) ≤ (pFinal : ℝ))
    (hincrementedFinal : ∀ T a e,
      (incremented T a e : ℝ) ≤ (pFinal : ℝ)) :
    (replay hd hmn W root p radialIncremented delta incremented X history
      ).source.RootedOpen (thresholdConfiguration pFinal X) cubicOrigin := by
  exact replayFrom_source_rootedOpen hd hmn root p pFinal delta incremented X
    [(root, true)]
    (DynamicBlockHistoryState.rooted W root p radialIncremented delta incremented X)
    (canonicalSuffix root history)
    (DynamicBlockHistoryState.rooted_source_rootedOpen W root p radialIncremented
      pFinal delta incremented X hcompletion hpFinal hradialFinal hincrementedFinal)
    hpFinal hincrementedFinal

/-- Canonical replay connectivity with no conditions on unreachable policy states.  The root
bound concerns the literal `2d` root schedule, while the suffix bound concerns each runtime
selected by an actual prefix of `canonicalSuffix root history`. -/
theorem replay_source_rootedOpen_of_prefixBounds
    (hd : 0 < d) (hmn : 2 * m ≤ n)
    (W : RootRadialSeedProfile d m n) (root : F)
    (p radialIncremented pFinal : I) (delta : ℝ)
    (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) (history : List (F × Bool))
    (hcompletion : X ∈ W.mixedExtensionPrefixSuccessEvent p radialIncremented
      delta incremented (rootExtensionDirectionOrder d).length)
    (hpFinal : (p : ℝ) ≤ (pFinal : ℝ))
    (hradialFinal : (radialIncremented : ℝ) ≤ (pFinal : ℝ))
    (hrootBounded : W.FinalThresholdBoundedOnPrefixes p pFinal incremented X
      (rootPostRadialSourceEdgeState d m n p radialIncremented X)
      (rootExtensionDirectionOrder d))
    (hsuffixBounded : ∀ (pref : List (F × Bool)) (v : F) (accepted : Bool)
      (tail : List (F × Bool)),
      canonicalSuffix root history = pref ++ (v, accepted) :: tail →
      let T := replayFrom hd hmn root p delta incremented X [(root, true)]
        (DynamicBlockHistoryState.rooted W root p radialIncremented delta incremented X) pref
      let fullHistory := [(root, true)] ++ pref
      let seed := inletSeed hd root fullHistory v T
      let incoming := incomingDirection hd root fullHistory v
      let first := firstFlip hd root fullHistory v T
      let directions := siteDirectionOrder hd root fullHistory v
      LaterSiteRuntime.FinalThresholdBoundedOnPrefixes hmn seed.physicalCenter incoming
        first unusedSecondFlip p pFinal delta incremented X
        (LaterSiteRuntime.initial T.source seed.physicalCenter) 0 directions) :
    (replay hd hmn W root p radialIncremented delta incremented X history
      ).source.RootedOpen (thresholdConfiguration pFinal X) cubicOrigin := by
  exact replayFrom_source_rootedOpen_of_prefixBounds hd hmn root p pFinal delta
    incremented X [(root, true)]
    (DynamicBlockHistoryState.rooted W root p radialIncremented delta incremented X)
    (canonicalSuffix root history)
    (DynamicBlockHistoryState.rooted_source_rootedOpen_of_prefixBounds W root p
      radialIncremented pFinal delta incremented X hcompletion hpFinal hradialFinal
      hrootBounded)
    hpFinal hsuffixBounded

/-- Canonical replay connectivity with all witness walks confined to `A`.  The obligations are
split into the completed-root geometry and the literal non-root runtime prefixes, matching the
two geometric parts of the Grimmett--Marstrand construction. -/
theorem replay_source_rootedOpenWithin_of_prefixBounds
    (hd : 0 < d) (hmn : 2 * m ≤ n) {A : Set (Cubic d)}
    (W : RootRadialSeedProfile d m n) (root : F)
    (p radialIncremented pFinal : I) (delta : ℝ)
    (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) (history : List (F × Bool))
    (hcompletion : X ∈ W.mixedExtensionPrefixSuccessEvent p radialIncremented
      delta incremented (rootExtensionDirectionOrder d).length)
    (hpFinal : (p : ℝ) ≤ (pFinal : ℝ))
    (hradialFinal : (radialIncremented : ℝ) ≤ (pFinal : ℝ))
    (hboxA : (cubicMetricBox d cubicOrigin m : Set (Cubic d)) ⊆ A)
    (hradialA : (cubicEdgeEndpointVertices (rootRadialEdgeSupport d m n) :
      Set (Cubic d)) ⊆ A)
    (hrootBounded : W.FinalThresholdBoundedOnPrefixes p pFinal incremented X
      (rootPostRadialSourceEdgeState d m n p radialIncremented X)
      (rootExtensionDirectionOrder d))
    (hrootStageA : ∀ j (hj : j < (rootExtensionDirectionOrder d).length),
      let S := W.runPostRadialExtensions p incremented X
        (rootPostRadialSourceEdgeState d m n p radialIncremented X)
        ((rootExtensionDirectionOrder d).take j)
      let a := (rootExtensionDirectionOrder d)[j]
      let Q := S.framedQuery (W.physicalCenter a) a
        (oppositeTransverseRestartFlip a)
      (cubicEdgeEndpointVertices (Q.restartSupport m n) : Set (Cubic d)) ⊆ A)
    (hsuffixBounded : ∀ (pref : List (F × Bool)) (v : F) (accepted : Bool)
      (tail : List (F × Bool)),
      canonicalSuffix root history = pref ++ (v, accepted) :: tail →
      let T := replayFrom hd hmn root p delta incremented X [(root, true)]
        (DynamicBlockHistoryState.rooted W root p radialIncremented delta incremented X) pref
      let fullHistory := [(root, true)] ++ pref
      let seed := inletSeed hd root fullHistory v T
      let incoming := incomingDirection hd root fullHistory v
      let first := firstFlip hd root fullHistory v T
      let directions := siteDirectionOrder hd root fullHistory v
      LaterSiteRuntime.FinalThresholdBoundedOnPrefixes hmn seed.physicalCenter incoming
        first unusedSecondFlip p pFinal delta incremented X
        (LaterSiteRuntime.initial T.source seed.physicalCenter) 0 directions)
    (hsuffixStageA : ∀ (pref : List (F × Bool)) (v : F) (accepted : Bool)
      (tail : List (F × Bool)),
      canonicalSuffix root history = pref ++ (v, accepted) :: tail →
      let T := replayFrom hd hmn root p delta incremented X [(root, true)]
        (DynamicBlockHistoryState.rooted W root p radialIncremented delta incremented X) pref
      let fullHistory := [(root, true)] ++ pref
      let seed := inletSeed hd root fullHistory v T
      let incoming := incomingDirection hd root fullHistory v
      let first := firstFlip hd root fullHistory v T
      let directions := siteDirectionOrder hd root fullHistory v
      ∀ j (hj : j < directions.length),
        let Rj := LaterSiteRuntime.runFrom hmn seed.physicalCenter incoming first
          unusedSecondFlip p delta incremented X
          (LaterSiteRuntime.initial T.source seed.physicalCenter) 0 (directions.take j)
        let a := directions[j]
        let Q := Rj.restartQuery seed.physicalCenter incoming first unusedSecondFlip a j
        (cubicEdgeEndpointVertices (Q.restartSupport m n) : Set (Cubic d)) ⊆ A) :
    (replay hd hmn W root p radialIncremented delta incremented X history
      ).source.RootedOpenWithin (thresholdConfiguration pFinal X) A cubicOrigin := by
  exact replayFrom_source_rootedOpenWithin_of_prefixBounds hd hmn root p pFinal delta
    incremented X [(root, true)]
    (DynamicBlockHistoryState.rooted W root p radialIncremented delta incremented X)
    (canonicalSuffix root history)
    (DynamicBlockHistoryState.rooted_source_rootedOpenWithin_of_prefixBounds W root p
      radialIncremented pFinal delta incremented X hcompletion hpFinal hradialFinal
      hboxA hradialA hrootBounded hrootStageA)
    hpFinal hsuffixBounded hsuffixStageA

namespace ReplayProgramStageCertificates

variable {p radialIncremented pFinal : I} {delta epsilon : ℝ}
  {incremented : RootExtensionThresholdPolicy d}
  {W : RootRadialSeedProfile d m n} {root : F}
  {initialEvent : Set (CubicEdge d → ℝ)}
  {hd : 0 < d} {hmn : 2 * m ≤ n}

/-- Under the concrete replay certificates, every seed record visible after a genuine finite
adaptive history is physically installed and connected to the root component at the final
bond density.  This packages the seed-installation and pathwise-connectivity inductions into
the form needed by the final infinite-cluster argument. -/
theorem outgoing_physicalCenter_connected_replay
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
      history = prior ++ (v, accepted) :: tail → AdmissibleQuery root prior v)
    (hpFinal : (p : ℝ) ≤ (pFinal : ℝ))
    (hradialFinal : (radialIncremented : ℝ) ≤ (pFinal : ℝ))
    (hincrementedFinal : ∀ T a e,
      (incremented T a e : ℝ) ≤ (pFinal : ℝ))
    {v : F} {a : CubicDirection d} {U : LaterSiteOutgoingSeed d}
    (hU : (replay hd hmn W root p radialIncremented delta incremented X history
      ).outgoing v a = some U) :
    thresholdConfiguration pFinal X ∈
      connectionEvent d cubicOrigin U.physicalCenter := by
  let S := replay hd hmn W root p radialIncremented delta incremented X history
  have hcompletion := C.initial_subset_root_completion hinitial
  have hrooted : S.source.RootedOpen
      (thresholdConfiguration pFinal X) cubicOrigin := by
    exact replay_source_rootedOpen hd hmn W root p radialIncremented pFinal delta
      incremented X history hcompletion hpFinal hradialFinal hincrementedFinal
  have hinstalled : S.SeedBoxesInstalled (m := m) := by
    exact C.seededBoxesInstalled_replay hm hmnStrict history hinitial hhistory hadmissible
  exact DynamicBlockHistoryState.outgoing_physicalCenter_connected hm hrooted hinstalled hU

end ReplayProgramStageCertificates

end DynamicBlockHistoryReplay

end Percolation
