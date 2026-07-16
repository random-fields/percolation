import Percolation.Critical.DynamicHistoryReplay

/-!
# Finite branching of dynamic-block history replay

For every fixed finite coarse history, the concrete replay has only finitely many possible
states as the common-uniform edge labels vary.  This is the outer finite partition needed
before applying the per-site accumulated-history partition.
-/

namespace Percolation

open scoped unitInterval

namespace DynamicBlockHistoryReplay

variable {d m n : ℕ} {F : Set (Cubic d)} [LinearOrder F]

/-- The finite dependent table of root witnesses, before converting each witness to its
physical/reference seed record. -/
noncomputable def rootWitnessTable
    (W : RootRadialSeedProfile d m n) (p radialIncremented : I) (delta : ℝ)
    (incremented : RootExtensionThresholdPolicy d) (X : CubicEdge d → ℝ) :
    ∀ a : CubicDirection d, Option (RestartSeedWitnessIndex d a.1 m n) :=
  fun a ↦ W.rootOutgoingWitness p radialIncremented delta incremented X a

/-- Convert a finite root-witness table to the outgoing-seed table stored by global replay. -/
noncomputable def outgoingOfRootWitnessTable
    (W : RootRadialSeedProfile d m n) (root : F)
    (T : ∀ a : CubicDirection d, Option (RestartSeedWitnessIndex d a.1 m n)) :
    F → CubicDirection d → Option (LaterSiteOutgoingSeed d) :=
  fun v a ↦ if v = root then
    (T a).map fun U ↦
      ⟨cubicRestartFrameIso (W.physicalCenter a) a
          (oppositeTransverseRestartFlip a) U.seedCenter.1,
        U.seedCenter.1⟩
  else none

/-- The completed-root replay state has finite range.  Although its outgoing table is a
function on the infinite coarse region, it differs from `none` only at the root and factors
through a finite dependent witness table. -/
theorem finite_range_rooted
    (W : RootRadialSeedProfile d m n) (root : F)
    (p radialIncremented : I) (delta : ℝ)
    (incremented : RootExtensionThresholdPolicy d) :
    (Set.range fun X : CubicEdge d → ℝ ↦
      DynamicBlockHistoryState.rooted W root p radialIncremented delta incremented X).Finite := by
  classical
  let source : (CubicEdge d → ℝ) → SourceFiniteEdgeRevealState d := fun X ↦
    W.rootExtensionPrefixState p radialIncremented incremented id
      (rootExtensionDirectionOrder d).length X
  let witnesses : (CubicEdge d → ℝ) →
      (∀ a : CubicDirection d, Option (RestartSeedWitnessIndex d a.1 m n)) :=
    rootWitnessTable W p radialIncremented delta incremented
  have hsource : (Set.range source).Finite := by
    simpa [source] using W.finite_range_rootExtensionPrefixState p radialIncremented
      incremented (rootExtensionDirectionOrder d).length
  have hwitnesses : (Set.range witnesses).Finite :=
    Set.finite_univ.subset (Set.subset_univ _)
  let data : (CubicEdge d → ℝ) →
      SourceFiniteEdgeRevealState d ×
        (∀ a : CubicDirection d, Option (RestartSeedWitnessIndex d a.1 m n)) :=
    fun X ↦ (source X, witnesses X)
  have hdata : (Set.range data).Finite :=
    (hsource.prod hwitnesses).subset (Set.range_pair_subset source witnesses)
  let assemble :
      SourceFiniteEdgeRevealState d ×
        (∀ a : CubicDirection d, Option (RestartSeedWitnessIndex d a.1 m n)) →
        DynamicBlockHistoryState d F :=
    fun t ↦
      { source := t.1
        outgoing := outgoingOfRootWitnessTable W root t.2 }
  apply (hdata.image assemble).subset
  rintro S ⟨X, rfl⟩
  refine ⟨data X, ⟨X, rfl⟩, ?_⟩
  rfl

/-- One fixed Boolean coarse decision preserves finite range of a varying replay state. -/
theorem finite_range_step_of_finite_range
    (hd : 0 < d) (hmn : 2 * m ≤ n) (root : F)
    (history : List (F × Bool)) (v : F) (accepted : Bool)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (state : (CubicEdge d → ℝ) → DynamicBlockHistoryState d F)
    (hstate : (Set.range state).Finite) :
    (Set.range fun X ↦ step hd hmn root history v accepted p delta incremented X
      (state X)).Finite := by
  classical
  let runtime : (CubicEdge d → ℝ) → LaterSiteRuntime d := fun X ↦
    siteRuntime hd hmn root history v p delta incremented X (state X)
  have hruntime : (Set.range runtime).Finite := by
    have hfixed : ∀ S ∈ Set.range state,
        (Set.range fun X : CubicEdge d → ℝ ↦
          siteRuntime hd hmn root history v p delta incremented X S).Finite := by
      intro S _hS
      let seed := inletSeed hd root history v S
      let incoming := incomingDirection hd root history v
      let first := firstFlip hd root history v S
      let initialRuntime : (CubicEdge d → ℝ) → LaterSiteRuntime d := fun _ ↦
        LaterSiteRuntime.initial S.source seed.physicalCenter
      have hinitial : (Set.range initialRuntime).Finite := by
        have hsubset : Set.range initialRuntime ⊆
            {LaterSiteRuntime.initial S.source seed.physicalCenter} := by
          rintro R ⟨X, rfl⟩
          simp [initialRuntime]
        exact (Set.finite_singleton _).subset hsubset
      simpa [siteRuntime, seed, incoming, first, unusedSecondFlip] using
        LaterSiteRuntime.finite_range_runFrom hmn seed.physicalCenter incoming
          first unusedSecondFlip p delta incremented initialRuntime 0
          (siteDirectionOrder hd root history v) hinitial
    apply (hstate.biUnion hfixed).subset
    rintro R ⟨X, rfl⟩
    simp only [Set.mem_iUnion]
    exact ⟨state X, ⟨⟨X, rfl⟩, ⟨X, rfl⟩⟩⟩
  let data : (CubicEdge d → ℝ) →
      DynamicBlockHistoryState d F × LaterSiteRuntime d :=
    fun X ↦ (state X, runtime X)
  have hdata : (Set.range data).Finite :=
    (hstate.prod hruntime).subset (Set.range_pair_subset state runtime)
  let assemble : DynamicBlockHistoryState d F × LaterSiteRuntime d →
      DynamicBlockHistoryState d F := fun t ↦
    { source := t.2.source
      outgoing := if accepted then Function.update t.1.outgoing v t.2.outgoing
        else t.1.outgoing }
  apply (hdata.image assemble).subset
  rintro S ⟨X, rfl⟩
  refine ⟨data X, ⟨X, rfl⟩, ?_⟩
  rfl

/-- Replaying a fixed suffix preserves finite range of an arbitrary finite-range incoming
global state. -/
theorem finite_range_replayFrom
    (hd : 0 < d) (hmn : 2 * m ≤ n) (root : F)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (prior suffix : List (F × Bool))
    (state : (CubicEdge d → ℝ) → DynamicBlockHistoryState d F)
    (hstate : (Set.range state).Finite) :
    (Set.range fun X ↦ replayFrom hd hmn root p delta incremented X prior
      (state X) suffix).Finite := by
  induction suffix generalizing prior state with
  | nil => simpa using hstate
  | cons head rest ih =>
      rcases head with ⟨v, accepted⟩
      let nextState : (CubicEdge d → ℝ) → DynamicBlockHistoryState d F := fun X ↦
        step hd hmn root prior v accepted p delta incremented X (state X)
      have hnext : (Set.range nextState).Finite :=
        finite_range_step_of_finite_range hd hmn root prior v accepted p delta incremented
          state hstate
      simpa [replayFrom, nextState] using
        ih (prior ++ [(v, accepted)]) nextState hnext

/-- For every fixed coarse history, the complete concrete replay has finite range. -/
theorem finite_range_replay
    (hd : 0 < d) (hmn : 2 * m ≤ n)
    (W : RootRadialSeedProfile d m n) (root : F)
    (p radialIncremented : I) (delta : ℝ)
    (incremented : RootExtensionThresholdPolicy d)
    (history : List (F × Bool)) :
    (Set.range fun X ↦ replay hd hmn W root p radialIncremented delta incremented X
      history).Finite := by
  let rootedState : (CubicEdge d → ℝ) → DynamicBlockHistoryState d F := fun X ↦
    DynamicBlockHistoryState.rooted W root p radialIncremented delta incremented X
  simpa [replay, rootedState] using
    finite_range_replayFrom hd hmn root p delta incremented [(root, true)]
      (canonicalSuffix root history) rootedState
      (finite_range_rooted W root p radialIncremented delta incremented)

end DynamicBlockHistoryReplay

end Percolation
