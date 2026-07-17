import Percolation.Critical.DynamicReplayStageLaw
import Percolation.Critical.DynamicReplayRevealBudget
import Percolation.Critical.DynamicReachableConnectivity

/-!
# Global threshold accounting for the concrete replay

This file combines the finite-query packing bound with the literal runtime support theorem.
The resulting estimate is pointwise in the physical edge: a replay schedule contributes to that
edge's threshold budget only when its coarse query belongs to the edge endpoint's finite influence
set.
-/

namespace Percolation

open scoped unitInterval

namespace DynamicBlockHistoryReplay

variable {d m n : ℕ} {F : Set (Cubic d)} [LinearOrder F]
variable {p radialIncremented : I} {delta epsilon : ℝ}
variable {incremented : RootExtensionThresholdPolicy d}
variable {W : RootRadialSeedProfile d m n} {root : F}
variable {initialEvent : Set (CubicEdge d → ℝ)}
variable {hd : 0 < d} {hmn : 2 * m ≤ n}

namespace ReplayProgramStageCertificates

/-- The local influence-region confinement theorem specialized to a genuine replay state. -/
theorem supportsWithin_queryInfluenceRegion_replay
    [NeZero d]
    (C : ReplayProgramStageCertificates hd hmn W root p radialIncremented delta epsilon
      incremented initialEvent)
    (hm : 1 ≤ m) (hmnStrict : m + 1 < n)
    (hroot : (root : Cubic d) = cubicOrigin)
    (history : List (F × Bool)) {X : CubicEdge d → ℝ}
    (hinitial : X ∈ initialEvent)
    (hhistory : X ∈ AdaptiveSiteExploration.adaptiveAnswerHistoryEvent
      (AdaptiveSiteExploration.finiteAdaptiveSuccessAnswer
        (paddedStageSuccess hd hmn W root p radialIncremented delta incremented)
        (4 * d)) history)
    (hadmissibleHistory : ∀ (prior : List (F × Bool)) (v : F) (accepted : Bool)
      (tail : List (F × Bool)),
      history = prior ++ (v, accepted) :: tail → AdmissibleQuery root prior v)
    (v : F) (hadmissible : AdmissibleQuery root history v) :
    let fullHistory := [(root, true)] ++ canonicalSuffix root history
    let S := replay hd hmn W root p radialIncremented delta incremented X history
    let seed := inletSeed hd root fullHistory v S
    let incoming := incomingDirection hd root fullHistory v
    let first := firstFlip hd root fullHistory v S
    let directions := siteDirectionOrder hd root fullHistory v
    LaterSiteRuntime.SupportsWithin hmn seed.physicalCenter incoming first
      unusedSecondFlip p delta incremented X
      (grimmettMarstrandQueryInfluenceRegion (m + n + 1) v.1)
      (siteInitialRuntime (m + n + 1) v S seed) 0 directions := by
  dsimp only
  let S := replay hd hmn W root p radialIncremented delta incremented X history
  have hcompletion := C.initial_subset_root_completion hinitial
  have hcover : OutgoingCoversUndecidedNeighbors
      ([(root, true)] ++ canonicalSuffix root history) S := by
    simpa [S] using outgoingCoversUndecidedNeighbors_replay hd hmn W root p
      radialIncremented delta incremented X history hcompletion
  have hinstalled : S.SeedBoxesInstalled (m := m) := by
    exact C.seededBoxesInstalled_replay hm hmnStrict history hinitial hhistory
      hadmissibleHistory
  have hrootCenter : grimmettMarstrandSiteCenter (m + n + 1) root.1 =
      cubicOrigin := by
    rw [hroot]
    ext j
    simp [grimmettMarstrandSiteCenter, cubicScale, cubicOrigin]
  have hnormalized : S.OutgoingReferenceCentersNormalized (N := m + n + 1) := by
    simpa [S] using outgoingReferenceCentersNormalized_replay hd hmn W root p
      radialIncremented delta incremented X history hrootCenter
  have hhalfway : S.OutgoingSeedsInHalfwayBoxes (N := m + n + 1) := by
    exact C.outgoingSeedsInHalfwayBoxes_replay hm hmnStrict hroot history hinitial
      hhistory hadmissibleHistory
  exact siteRuntime_supportsWithin_queryInfluenceRegion_of_admissibleQuery hd hmn root
    history v p delta incremented X S hadmissible hcover hinstalled hnormalized hhalfway

end ReplayProgramStageCertificates

namespace ReplayProgramStageCertificatesBefore

/-- The local influence-region confinement theorem at finite certificate depth.  Unlike the
unbounded wrapper above, this version is available at history length exactly `depth`, because
its installed-seed and half-way-box invariants consume only certificates for strict prefixes. -/
theorem supportsWithin_queryInfluenceRegion_replay
    [NeZero d]
    (C : ReplayProgramStageCertificatesBefore hd hmn W root p radialIncremented delta epsilon
      incremented initialEvent depth)
    (hm : 1 ≤ m) (hmnStrict : m + 1 < n)
    (hroot : (root : Cubic d) = cubicOrigin)
    (history : List (F × Bool)) (hdepth : history.length ≤ depth)
    {X : CubicEdge d → ℝ}
    (hinitial : X ∈ initialEvent)
    (hhistory : X ∈ AdaptiveSiteExploration.adaptiveAnswerHistoryEvent
      (AdaptiveSiteExploration.finiteAdaptiveSuccessAnswer
        (paddedStageSuccess hd hmn W root p radialIncremented delta incremented)
        (4 * d)) history)
    (hadmissibleHistory : ∀ (prior : List (F × Bool)) (v : F) (accepted : Bool)
      (tail : List (F × Bool)),
      history = prior ++ (v, accepted) :: tail → AdmissibleQuery root prior v)
    (v : F) (hadmissible : AdmissibleQuery root history v) :
    let fullHistory := [(root, true)] ++ canonicalSuffix root history
    let S := replay hd hmn W root p radialIncremented delta incremented X history
    let seed := inletSeed hd root fullHistory v S
    let incoming := incomingDirection hd root fullHistory v
    let first := firstFlip hd root fullHistory v S
    let directions := siteDirectionOrder hd root fullHistory v
    LaterSiteRuntime.SupportsWithin hmn seed.physicalCenter incoming first
      unusedSecondFlip p delta incremented X
      (grimmettMarstrandQueryInfluenceRegion (m + n + 1) v.1)
      (siteInitialRuntime (m + n + 1) v S seed) 0 directions := by
  dsimp only
  let S := replay hd hmn W root p radialIncremented delta incremented X history
  have hcompletion := C.initial_subset_root_completion hinitial
  have hcover : OutgoingCoversUndecidedNeighbors
      ([(root, true)] ++ canonicalSuffix root history) S := by
    simpa [S] using outgoingCoversUndecidedNeighbors_replay hd hmn W root p
      radialIncremented delta incremented X history hcompletion
  have hinstalled : S.SeedBoxesInstalled (m := m) := by
    exact C.seededBoxesInstalled_replay hm hmnStrict history hdepth hinitial hhistory
      hadmissibleHistory
  have hrootCenter : grimmettMarstrandSiteCenter (m + n + 1) root.1 =
      cubicOrigin := by
    rw [hroot]
    ext j
    simp [grimmettMarstrandSiteCenter, cubicScale, cubicOrigin]
  have hnormalized : S.OutgoingReferenceCentersNormalized (N := m + n + 1) := by
    simpa [S] using outgoingReferenceCentersNormalized_replay hd hmn W root p
      radialIncremented delta incremented X history hrootCenter
  have hhalfway : S.OutgoingSeedsInHalfwayBoxes (N := m + n + 1) := by
    exact C.outgoingSeedsInHalfwayBoxes_replay hm hmnStrict hroot history hdepth hinitial
      hhistory hadmissibleHistory
  exact siteRuntime_supportsWithin_queryInfluenceRegion_of_admissibleQuery hd hmn root
    history v p delta incremented X S hadmissible hcover hinstalled hnormalized hhalfway

end ReplayProgramStageCertificatesBefore

/-- Threshold budget already spent by the completed root schedule. -/
noncomputable def rootReplayLowerBudget (d : ℕ) (p radialIncremented : I)
    (delta : ℝ) : ℝ :=
  max (p : ℝ) (radialIncremented : ℝ) +
    ((rootExtensionDirectionOrder d).length : ℝ) * delta

/-- Pointwise replay budget: the completed root cost plus `4d` increments for every earlier
coarse query whose reveal region can contain the chosen physical endpoint. -/
noncomputable def replayEdgeLowerBudget
    (N : ℕ) (p radialIncremented : I) (delta : ℝ)
    (root : F) (history : List (F × Bool)) (z : Cubic d) : ℝ :=
  rootReplayLowerBudget d p radialIncremented delta +
    ((replayInfluenceSitesSeen N z root history).card : ℝ) *
      (4 * d : ℕ) * delta

/-- Scale-uniform upper bound for every replay prefix, including room for one prospective
threshold increment at the current runtime stage. -/
noncomputable def replayThresholdCap
    (d : ℕ) (p radialIncremented : I) (delta : ℝ) : ℝ :=
  rootReplayLowerBudget d p radialIncremented delta +
    (((2 ^ d) * (2 * d + 1) : ℕ) : ℝ) * (4 * d : ℕ) * delta + delta

/-- Finite-depth form of the pointwise replay budget.  The proof follows the literal history
chronology, so the support-confinement fact needed for the last query is read only from
certificates for the strict prefix. -/
theorem replay_source_lower_le_spatialBudget_before
    [NeZero d]
    (hdelta : 0 ≤ delta)
    (C : ReplayProgramStageCertificatesBefore hd hmn W root p radialIncremented delta epsilon
      (budgetedRootExtensionThresholdPolicy delta hdelta) initialEvent depth)
    (hm : 1 ≤ m) (hmnStrict : m + 1 < n)
    (hroot : (root : Cubic d) = cubicOrigin)
    (history : List (F × Bool)) (hdepth : history.length ≤ depth)
    {X : CubicEdge d → ℝ}
    (hinitial : X ∈ initialEvent)
    (hhistory : X ∈ AdaptiveSiteExploration.adaptiveAnswerHistoryEvent
      (AdaptiveSiteExploration.finiteAdaptiveSuccessAnswer
        (paddedStageSuccess hd hmn W root p radialIncremented delta
          (budgetedRootExtensionThresholdPolicy delta hdelta))
        (4 * d)) history)
    (hadmissible : ∀ (prior : List (F × Bool)) (v : F) (accepted : Bool)
      (tail : List (F × Bool)),
      history = prior ++ (v, accepted) :: tail → AdmissibleQuery root prior v)
    (e : CubicEdge d) :
    ((replay hd hmn W root p radialIncremented delta
      (budgetedRootExtensionThresholdPolicy delta hdelta) X history
      ).source.lower e : ℝ) ≤
      replayEdgeLowerBudget (m + n + 1) p radialIncremented delta root history
        e.1.out.1 := by
  let policy : RootExtensionThresholdPolicy d :=
    budgetedRootExtensionThresholdPolicy delta hdelta
  let finiteAnswer := AdaptiveSiteExploration.finiteAdaptiveSuccessAnswer
    (paddedStageSuccess hd hmn W root p radialIncremented delta policy) (4 * d)
  induction history using List.reverseRecOn with
  | nil =>
      have hrootBound := W.coe_rootExtensionPrefixState_budgeted_lower_le
        p radialIncremented delta hdelta id (rootExtensionDirectionOrder d).length X e
      simpa [policy, replay, canonicalSuffix, DynamicBlockHistoryState.rooted,
        replayEdgeLowerBudget, replayInfluenceSitesSeen, rootReplayLowerBudget] using hrootBound
  | append_singleton prior entry ih =>
      rcases entry with ⟨v, accepted⟩
      have hpriorDepth : prior.length < depth := by
        simp only [List.length_append, List.length_singleton] at hdepth
        omega
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
        simpa [finiteAnswer, policy] using hhistory
      have hprior := ih hpriorDepth.le
        (by simpa [finiteAnswer, policy] using hhistorySplit.1) hadmissiblePrior
      let S := replay hd hmn W root p radialIncremented delta policy X prior
      let fullHistory := [(root, true)] ++ canonicalSuffix root prior
      let seed := inletSeed hd root fullHistory v S
      let incoming := incomingDirection hd root fullHistory v
      let first := firstFlip hd root fullHistory v S
      let directions := siteDirectionOrder hd root fullHistory v
      have hlen : directions.length ≤ 4 * d := by
        simpa [directions, fullHistory] using
          siteDirectionOrder_length_le hd root fullHistory v
      rw [replay_append_singleton_of_admissibleQuery hd hmn W root p radialIncremented
        delta policy X prior v accepted hadmissibleLast]
      change
        ((siteRuntime hd hmn root fullHistory v p delta policy X S).source.lower e : ℝ) ≤
          replayEdgeLowerBudget (m + n + 1) p radialIncremented delta root
            (prior ++ [(v, accepted)]) e.1.out.1
      by_cases hvInfluence : v.1 ∈
          grimmettMarstrandInfluenceSites (m + n + 1) e.1.out.1
      · have hpBudget : (p : ℝ) ≤
            replayEdgeLowerBudget (m + n + 1) p radialIncremented delta root prior
              e.1.out.1 := by
          have hnonnegRoot : 0 ≤
              ((rootExtensionDirectionOrder d).length : ℝ) * delta :=
            mul_nonneg (Nat.cast_nonneg _) hdelta
          have hnonnegSeen : 0 ≤
              ((replayInfluenceSitesSeen (m + n + 1) e.1.out.1 root prior).card : ℝ) *
                (4 * d : ℕ) * delta := by positivity
          unfold replayEdgeLowerBudget rootReplayLowerBudget
          linarith [le_max_left (p : ℝ) (radialIncremented : ℝ)]
        have hruntime := LaterSiteRuntime.coe_runFrom_lower_le_add_length_at hmn
          seed.physicalCenter incoming first unusedSecondFlip p delta hdelta policy
          (fun T a f ↦ coe_budgetedRootExtensionThresholdPolicy_le_add
            delta hdelta T a f)
          X (siteInitialRuntime (m + n + 1) v S seed) 0 directions
          (replayEdgeLowerBudget (m + n + 1) p radialIncremented delta root prior
            e.1.out.1) e (by simpa [S, siteInitialRuntime, LaterSiteRuntime.initialAt] using hprior)
          hpBudget
        have hnotSeen := not_mem_replayInfluenceSitesSeen_of_admissibleQuery
          (m + n + 1) e.1.out.1 root prior v hadmissibleLast
        have hseen := replayInfluenceSitesSeen_append_singleton_of_mem
          (m + n + 1) e.1.out.1 root prior v accepted hadmissibleLast hvInfluence
        change
          ((LaterSiteRuntime.runFrom hmn seed.physicalCenter incoming first unusedSecondFlip
            p delta policy X (siteInitialRuntime (m + n + 1) v S seed) 0
            directions).source.lower e : ℝ) ≤ _ at hruntime ⊢
        calc
          ((LaterSiteRuntime.runFrom hmn seed.physicalCenter incoming first unusedSecondFlip
            p delta policy X (siteInitialRuntime (m + n + 1) v S seed) 0
            directions).source.lower e : ℝ) ≤
              replayEdgeLowerBudget (m + n + 1) p radialIncremented delta root prior
                e.1.out.1 + (directions.length : ℝ) * delta := hruntime
          _ ≤ replayEdgeLowerBudget (m + n + 1) p radialIncremented delta root prior
                e.1.out.1 + (4 * d : ℕ) * delta := by
            gcongr
          _ = replayEdgeLowerBudget (m + n + 1) p radialIncremented delta root
                (prior ++ [(v, accepted)]) e.1.out.1 := by
            simp only [replayEdgeLowerBudget]
            rw [hseen, Finset.card_insert_of_notMem hnotSeen]
            push_cast
            ring
      · have hwithin := C.supportsWithin_queryInfluenceRegion_replay hm hmnStrict hroot
          prior hpriorDepth.le hinitial
          (by simpa [finiteAnswer, policy] using hhistorySplit.1)
          hadmissiblePrior v hadmissibleLast
        have hout : e.1.out.1 ∉
            grimmettMarstrandQueryInfluenceRegion (m + n + 1) v.1 := by
          intro he
          exact hvInfluence
            (mem_grimmettMarstrandInfluenceSites_of_mem_queryInfluenceRegion he)
        have heq := LaterSiteRuntime.runFrom_lower_eq_of_supportsWithin_of_endpoint_not_mem
          hmn seed.physicalCenter incoming first unusedSecondFlip p delta policy X
          (grimmettMarstrandQueryInfluenceRegion (m + n + 1) v.1)
          (siteInitialRuntime (m + n + 1) v S seed) 0 directions hwithin e hout
        have hseen := replayInfluenceSitesSeen_append_singleton_of_not_mem
          (m + n + 1) e.1.out.1 root prior v accepted hadmissibleLast hvInfluence
        change
          ((LaterSiteRuntime.runFrom hmn seed.physicalCenter incoming first unusedSecondFlip
            p delta policy X (siteInitialRuntime (m + n + 1) v S seed) 0
            directions).source.lower e : ℝ) ≤ _
        simp only [replayEdgeLowerBudget]
        rw [hseen]
        rw [heq]
        change
          ((replay hd hmn W root p radialIncremented delta policy X prior
            ).source.lower e : ℝ) ≤
            replayEdgeLowerBudget (m + n + 1) p radialIncremented delta root prior
              e.1.out.1 at hprior
        simp only [replayEdgeLowerBudget] at hprior
        push_cast at hprior ⊢
        simpa [S, siteInitialRuntime, LaterSiteRuntime.initialAt] using hprior

/-- Every physical edge threshold in a genuine concrete replay is bounded by the number of
distinct earlier coarse queries which can spatially influence one canonical endpoint. -/
theorem replay_source_lower_le_spatialBudget
    [NeZero d]
    (hdelta : 0 ≤ delta)
    (C : ReplayProgramStageCertificates hd hmn W root p radialIncremented delta epsilon
      (budgetedRootExtensionThresholdPolicy delta hdelta) initialEvent)
    (hm : 1 ≤ m) (hmnStrict : m + 1 < n)
    (hroot : (root : Cubic d) = cubicOrigin)
    (history : List (F × Bool)) {X : CubicEdge d → ℝ}
    (hinitial : X ∈ initialEvent)
    (hhistory : X ∈ AdaptiveSiteExploration.adaptiveAnswerHistoryEvent
      (AdaptiveSiteExploration.finiteAdaptiveSuccessAnswer
        (paddedStageSuccess hd hmn W root p radialIncremented delta
          (budgetedRootExtensionThresholdPolicy delta hdelta))
        (4 * d)) history)
    (hadmissible : ∀ (prior : List (F × Bool)) (v : F) (accepted : Bool)
      (tail : List (F × Bool)),
      history = prior ++ (v, accepted) :: tail → AdmissibleQuery root prior v)
    (e : CubicEdge d) :
    ((replay hd hmn W root p radialIncremented delta
      (budgetedRootExtensionThresholdPolicy delta hdelta) X history
      ).source.lower e : ℝ) ≤
      replayEdgeLowerBudget (m + n + 1) p radialIncremented delta root history
        e.1.out.1 := by
  let policy : RootExtensionThresholdPolicy d :=
    budgetedRootExtensionThresholdPolicy delta hdelta
  let finiteAnswer := AdaptiveSiteExploration.finiteAdaptiveSuccessAnswer
    (paddedStageSuccess hd hmn W root p radialIncremented delta policy) (4 * d)
  induction history using List.reverseRecOn with
  | nil =>
      have hrootBound := W.coe_rootExtensionPrefixState_budgeted_lower_le
        p radialIncremented delta hdelta id (rootExtensionDirectionOrder d).length X e
      simpa [policy, replay, canonicalSuffix, DynamicBlockHistoryState.rooted,
        replayEdgeLowerBudget, replayInfluenceSitesSeen, rootReplayLowerBudget] using hrootBound
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
        simpa [finiteAnswer, policy] using hhistory
      have hprior := ih (by simpa [finiteAnswer, policy] using hhistorySplit.1)
        hadmissiblePrior
      let S := replay hd hmn W root p radialIncremented delta policy X prior
      let fullHistory := [(root, true)] ++ canonicalSuffix root prior
      let seed := inletSeed hd root fullHistory v S
      let incoming := incomingDirection hd root fullHistory v
      let first := firstFlip hd root fullHistory v S
      let directions := siteDirectionOrder hd root fullHistory v
      have hlen : directions.length ≤ 4 * d := by
        simpa [directions, fullHistory] using
          siteDirectionOrder_length_le hd root fullHistory v
      rw [replay_append_singleton_of_admissibleQuery hd hmn W root p radialIncremented
        delta policy X prior v accepted hadmissibleLast]
      change
        ((siteRuntime hd hmn root fullHistory v p delta policy X S).source.lower e : ℝ) ≤
          replayEdgeLowerBudget (m + n + 1) p radialIncremented delta root
            (prior ++ [(v, accepted)]) e.1.out.1
      by_cases hvInfluence : v.1 ∈
          grimmettMarstrandInfluenceSites (m + n + 1) e.1.out.1
      · have hpBudget : (p : ℝ) ≤
            replayEdgeLowerBudget (m + n + 1) p radialIncremented delta root prior
              e.1.out.1 := by
          have hnonnegRoot : 0 ≤
              ((rootExtensionDirectionOrder d).length : ℝ) * delta :=
            mul_nonneg (Nat.cast_nonneg _) hdelta
          have hnonnegSeen : 0 ≤
              ((replayInfluenceSitesSeen (m + n + 1) e.1.out.1 root prior).card : ℝ) *
                (4 * d : ℕ) * delta := by positivity
          unfold replayEdgeLowerBudget rootReplayLowerBudget
          linarith [le_max_left (p : ℝ) (radialIncremented : ℝ)]
        have hruntime := LaterSiteRuntime.coe_runFrom_lower_le_add_length_at hmn
          seed.physicalCenter incoming first unusedSecondFlip p delta hdelta policy
          (fun T a f ↦ coe_budgetedRootExtensionThresholdPolicy_le_add
            delta hdelta T a f)
          X (siteInitialRuntime (m + n + 1) v S seed) 0 directions
          (replayEdgeLowerBudget (m + n + 1) p radialIncremented delta root prior
            e.1.out.1) e (by simpa [S, siteInitialRuntime, LaterSiteRuntime.initialAt] using hprior)
          hpBudget
        have hnotSeen := not_mem_replayInfluenceSitesSeen_of_admissibleQuery
          (m + n + 1) e.1.out.1 root prior v hadmissibleLast
        have hseen := replayInfluenceSitesSeen_append_singleton_of_mem
          (m + n + 1) e.1.out.1 root prior v accepted hadmissibleLast hvInfluence
        change
          ((LaterSiteRuntime.runFrom hmn seed.physicalCenter incoming first unusedSecondFlip
            p delta policy X (siteInitialRuntime (m + n + 1) v S seed) 0
            directions).source.lower e : ℝ) ≤ _ at hruntime ⊢
        calc
          ((LaterSiteRuntime.runFrom hmn seed.physicalCenter incoming first unusedSecondFlip
            p delta policy X (siteInitialRuntime (m + n + 1) v S seed) 0
            directions).source.lower e : ℝ) ≤
              replayEdgeLowerBudget (m + n + 1) p radialIncremented delta root prior
                e.1.out.1 + (directions.length : ℝ) * delta := hruntime
          _ ≤ replayEdgeLowerBudget (m + n + 1) p radialIncremented delta root prior
                e.1.out.1 + (4 * d : ℕ) * delta := by
            gcongr
          _ = replayEdgeLowerBudget (m + n + 1) p radialIncremented delta root
                (prior ++ [(v, accepted)]) e.1.out.1 := by
            simp only [replayEdgeLowerBudget]
            rw [hseen, Finset.card_insert_of_notMem hnotSeen]
            push_cast
            ring
      · have hwithin := C.supportsWithin_queryInfluenceRegion_replay hm hmnStrict hroot
          prior hinitial (by simpa [finiteAnswer, policy] using hhistorySplit.1)
          hadmissiblePrior v hadmissibleLast
        have hout : e.1.out.1 ∉
            grimmettMarstrandQueryInfluenceRegion (m + n + 1) v.1 := by
          intro he
          exact hvInfluence
            (mem_grimmettMarstrandInfluenceSites_of_mem_queryInfluenceRegion he)
        have heq := LaterSiteRuntime.runFrom_lower_eq_of_supportsWithin_of_endpoint_not_mem
          hmn seed.physicalCenter incoming first unusedSecondFlip p delta policy X
          (grimmettMarstrandQueryInfluenceRegion (m + n + 1) v.1)
          (siteInitialRuntime (m + n + 1) v S seed) 0 directions hwithin e hout
        have hseen := replayInfluenceSitesSeen_append_singleton_of_not_mem
          (m + n + 1) e.1.out.1 root prior v accepted hadmissibleLast hvInfluence
        change
          ((LaterSiteRuntime.runFrom hmn seed.physicalCenter incoming first unusedSecondFlip
            p delta policy X (siteInitialRuntime (m + n + 1) v S seed) 0
            directions).source.lower e : ℝ) ≤ _
        simp only [replayEdgeLowerBudget]
        rw [hseen]
        rw [heq]
        change
          ((replay hd hmn W root p radialIncremented delta policy X prior
            ).source.lower e : ℝ) ≤
            replayEdgeLowerBudget (m + n + 1) p radialIncremented delta root prior
              e.1.out.1 at hprior
        simp only [replayEdgeLowerBudget] at hprior
        push_cast at hprior ⊢
        simpa [S, siteInitialRuntime, LaterSiteRuntime.initialAt] using hprior

/-- Finite-depth prefix budget for the next runtime after a history of length at most `depth`.
It is the successor-construction form of `runtimePrefix_lower_add_le_replayThresholdCap`. -/
theorem runtimePrefix_lower_add_le_replayThresholdCap_before
    [NeZero d]
    (hdelta : 0 ≤ delta)
    (C : ReplayProgramStageCertificatesBefore hd hmn W root p radialIncremented delta epsilon
      (budgetedRootExtensionThresholdPolicy delta hdelta) initialEvent depth)
    (hm : 1 ≤ m) (hmnStrict : m + 1 < n)
    (hroot : (root : Cubic d) = cubicOrigin)
    (history : List (F × Bool)) (hdepth : history.length ≤ depth)
    {X : CubicEdge d → ℝ}
    (hinitial : X ∈ initialEvent)
    (hhistory : X ∈ AdaptiveSiteExploration.adaptiveAnswerHistoryEvent
      (AdaptiveSiteExploration.finiteAdaptiveSuccessAnswer
        (paddedStageSuccess hd hmn W root p radialIncremented delta
          (budgetedRootExtensionThresholdPolicy delta hdelta))
        (4 * d)) history)
    (hadmissibleHistory : ∀ (prior : List (F × Bool)) (u : F) (accepted : Bool)
      (tail : List (F × Bool)),
      history = prior ++ (u, accepted) :: tail → AdmissibleQuery root prior u)
    (v : F) (hadmissible : AdmissibleQuery root history v) :
    let policy := budgetedRootExtensionThresholdPolicy delta hdelta
    let fullHistory := [(root, true)] ++ canonicalSuffix root history
    let S := replay hd hmn W root p radialIncremented delta policy X history
    let seed := inletSeed hd root fullHistory v S
    let incoming := incomingDirection hd root fullHistory v
    let first := firstFlip hd root fullHistory v S
    let directions := siteDirectionOrder hd root fullHistory v
    ∀ l (hl : l < directions.length) e,
      let Rl := LaterSiteRuntime.runFrom hmn seed.physicalCenter incoming first
        unusedSecondFlip p delta policy X
          (siteInitialRuntime (m + n + 1) v S seed) 0 (directions.take l)
      (Rl.source.lower e : ℝ) + delta ≤
        replayThresholdCap d p radialIncremented delta := by
  dsimp only
  intro l hl e
  let policy : RootExtensionThresholdPolicy d :=
    budgetedRootExtensionThresholdPolicy delta hdelta
  let fullHistory := [(root, true)] ++ canonicalSuffix root history
  let S := replay hd hmn W root p radialIncremented delta policy X history
  let seed := inletSeed hd root fullHistory v S
  let incoming := incomingDirection hd root fullHistory v
  let first := firstFlip hd root fullHistory v S
  let directions := siteDirectionOrder hd root fullHistory v
  change l < directions.length at hl
  have hlen : directions.length ≤ 4 * d := by
    simpa [directions, fullHistory] using siteDirectionOrder_length_le hd root fullHistory v
  have htake : (directions.take l).length = l := List.length_take_of_le (Nat.le_of_lt hl)
  have hN : 0 < m + n + 1 := by omega
  have hprior := replay_source_lower_le_spatialBudget_before hdelta C hm hmnStrict hroot
    history hdepth hinitial hhistory hadmissibleHistory e
  have hpBudget : (p : ℝ) ≤
      replayEdgeLowerBudget (m + n + 1) p radialIncremented delta root history
        e.1.out.1 := by
    have hnonnegRoot : 0 ≤
        ((rootExtensionDirectionOrder d).length : ℝ) * delta :=
      mul_nonneg (Nat.cast_nonneg _) hdelta
    have hnonnegSeen : 0 ≤
        ((replayInfluenceSitesSeen (m + n + 1) e.1.out.1 root history).card : ℝ) *
          (4 * d : ℕ) * delta := by positivity
    unfold replayEdgeLowerBudget rootReplayLowerBudget
    linarith [le_max_left (p : ℝ) (radialIncremented : ℝ)]
  by_cases hvInfluence : v.1 ∈
      grimmettMarstrandInfluenceSites (m + n + 1) e.1.out.1
  · have hruntime := LaterSiteRuntime.coe_runFrom_lower_le_add_length_at hmn
      seed.physicalCenter incoming first unusedSecondFlip p delta hdelta policy
      (fun T a f ↦ coe_budgetedRootExtensionThresholdPolicy_le_add delta hdelta T a f)
      X (siteInitialRuntime (m + n + 1) v S seed) 0 (directions.take l)
      (replayEdgeLowerBudget (m + n + 1) p radialIncremented delta root history
        e.1.out.1) e (by simpa [S, siteInitialRuntime, LaterSiteRuntime.initialAt] using hprior)
      hpBudget
    have hnotSeen := not_mem_replayInfluenceSitesSeen_of_admissibleQuery
      (m + n + 1) e.1.out.1 root history v hadmissible
    have hseen := replayInfluenceSitesSeen_append_singleton_of_mem
      (m + n + 1) e.1.out.1 root history v false hadmissible hvInfluence
    have hcardAll := card_replayInfluenceSitesSeen_le (m + n + 1) hN e.1.out.1 root
      (history ++ [(v, false)])
    rw [hseen, Finset.card_insert_of_notMem hnotSeen] at hcardAll
    have hlSucc : l + 1 ≤ 4 * d := by omega
    let seenCard := (replayInfluenceSitesSeen
      (m + n + 1) e.1.out.1 root history).card
    let capCard := (2 ^ d) * (2 * d + 1)
    have hnat : seenCard * (4 * d) + (l + 1) ≤ capCard * (4 * d) := by
      calc
        seenCard * (4 * d) + (l + 1) ≤ seenCard * (4 * d) + (4 * d) := by omega
        _ = (seenCard + 1) * (4 * d) := by simp [Nat.add_mul]
        _ ≤ capCard * (4 * d) := Nat.mul_le_mul_right (4 * d) hcardAll
    have hreal :
        (seenCard : ℝ) * (4 * d : ℕ) + (l + 1 : ℕ) ≤
          (capCard : ℝ) * (4 * d : ℕ) := by exact_mod_cast hnat
    have hmul := mul_le_mul_of_nonneg_right hreal hdelta
    rw [htake] at hruntime
    change
      ((LaterSiteRuntime.runFrom hmn seed.physicalCenter incoming first unusedSecondFlip
        p delta policy X (siteInitialRuntime (m + n + 1) v S seed) 0
        (directions.take l)).source.lower e : ℝ) + delta ≤ _
    unfold replayEdgeLowerBudget at hruntime
    unfold replayThresholdCap
    dsimp only [seenCard, capCard] at hmul
    push_cast at hruntime hmul ⊢
    nlinarith
  · have hwithin := C.supportsWithin_queryInfluenceRegion_replay hm hmnStrict hroot
      history hdepth hinitial hhistory hadmissibleHistory v hadmissible
    have hout : e.1.out.1 ∉
        grimmettMarstrandQueryInfluenceRegion (m + n + 1) v.1 := by
      intro he
      exact hvInfluence
        (mem_grimmettMarstrandInfluenceSites_of_mem_queryInfluenceRegion he)
    have heq := LaterSiteRuntime.runFrom_lower_eq_of_supportsWithin_of_endpoint_not_mem
      hmn seed.physicalCenter incoming first unusedSecondFlip p delta policy X
      (grimmettMarstrandQueryInfluenceRegion (m + n + 1) v.1)
      (siteInitialRuntime (m + n + 1) v S seed) 0 (directions.take l)
      (LaterSiteRuntime.supportsWithin_take hmn seed.physicalCenter incoming first
        unusedSecondFlip p delta policy X
        (grimmettMarstrandQueryInfluenceRegion (m + n + 1) v.1)
        (siteInitialRuntime (m + n + 1) v S seed) 0 directions hwithin l)
      e hout
    have hcard := card_replayInfluenceSitesSeen_le (m + n + 1) hN e.1.out.1 root history
    have hnat :
        (replayInfluenceSitesSeen (m + n + 1) e.1.out.1 root history).card * (4 * d) ≤
          ((2 ^ d) * (2 * d + 1)) * (4 * d) :=
      Nat.mul_le_mul_right (4 * d) hcard
    have hreal :
        ((replayInfluenceSitesSeen
          (m + n + 1) e.1.out.1 root history).card : ℝ) * (4 * d : ℕ) ≤
          (((2 ^ d) * (2 * d + 1) : ℕ) : ℝ) * (4 * d : ℕ) := by
      exact_mod_cast hnat
    have hmul := mul_le_mul_of_nonneg_right hreal hdelta
    change
      ((LaterSiteRuntime.runFrom hmn seed.physicalCenter incoming first unusedSecondFlip
        p delta policy X (siteInitialRuntime (m + n + 1) v S seed) 0
        (directions.take l)).source.lower e : ℝ) + delta ≤ _
    rw [heq]
    change ((S.source.lower e : ℝ) + delta ≤ _)
    change ((S.source.lower e : ℝ) ≤ _) at hprior
    unfold replayEdgeLowerBudget at hprior
    unfold replayThresholdCap
    push_cast at hprior hmul ⊢
    nlinarith

/-- Finite-depth exact-addition identity for the canonical total threshold policy. -/
theorem runtimePrefix_budgetedPolicy_eq_add_before
    [NeZero d]
    (hdelta : 0 ≤ delta)
    (C : ReplayProgramStageCertificatesBefore hd hmn W root p radialIncremented delta epsilon
      (budgetedRootExtensionThresholdPolicy delta hdelta) initialEvent depth)
    (hm : 1 ≤ m) (hmnStrict : m + 1 < n)
    (hroot : (root : Cubic d) = cubicOrigin)
    (hcap : replayThresholdCap d p radialIncremented delta ≤ 1)
    (history : List (F × Bool)) (hdepth : history.length ≤ depth)
    {X : CubicEdge d → ℝ}
    (hinitial : X ∈ initialEvent)
    (hhistory : X ∈ AdaptiveSiteExploration.adaptiveAnswerHistoryEvent
      (AdaptiveSiteExploration.finiteAdaptiveSuccessAnswer
        (paddedStageSuccess hd hmn W root p radialIncremented delta
          (budgetedRootExtensionThresholdPolicy delta hdelta))
        (4 * d)) history)
    (hadmissibleHistory : ∀ (prior : List (F × Bool)) (u : F) (accepted : Bool)
      (tail : List (F × Bool)),
      history = prior ++ (u, accepted) :: tail → AdmissibleQuery root prior u)
    (v : F) (hadmissible : AdmissibleQuery root history v) :
    let policy := budgetedRootExtensionThresholdPolicy delta hdelta
    let fullHistory := [(root, true)] ++ canonicalSuffix root history
    let S := replay hd hmn W root p radialIncremented delta policy X history
    let seed := inletSeed hd root fullHistory v S
    let incoming := incomingDirection hd root fullHistory v
    let first := firstFlip hd root fullHistory v S
    let directions := siteDirectionOrder hd root fullHistory v
    ∀ l (hl : l < directions.length) e,
      let Rl := LaterSiteRuntime.runFrom hmn seed.physicalCenter incoming first
        unusedSecondFlip p delta policy X
          (siteInitialRuntime (m + n + 1) v S seed) 0 (directions.take l)
      let a := directions[l]
      (policy Rl.source a e : ℝ) = (Rl.source.lower e : ℝ) + delta := by
  dsimp only
  intro l hl e
  let policy : RootExtensionThresholdPolicy d :=
    budgetedRootExtensionThresholdPolicy delta hdelta
  let fullHistory := [(root, true)] ++ canonicalSuffix root history
  let S := replay hd hmn W root p radialIncremented delta policy X history
  let seed := inletSeed hd root fullHistory v S
  let incoming := incomingDirection hd root fullHistory v
  let first := firstFlip hd root fullHistory v S
  let directions := siteDirectionOrder hd root fullHistory v
  let Rl := LaterSiteRuntime.runFrom hmn seed.physicalCenter incoming first
    unusedSecondFlip p delta policy X
      (siteInitialRuntime (m + n + 1) v S seed) 0 (directions.take l)
  have hbudget : Rl.source.HasIncrementBudget delta := by
    intro f
    exact (runtimePrefix_lower_add_le_replayThresholdCap_before hdelta C hm hmnStrict hroot
      history hdepth hinitial hhistory hadmissibleHistory v hadmissible l hl f).trans hcap
  exact coe_budgetedRootExtensionThresholdPolicy_of_hasIncrementBudget
    delta hdelta Rl.source directions[l] hbudget e

/-- At every literal runtime prefix reached by a genuine semantic history, the old threshold
plus the next sprinkling increment is bounded by the scale-uniform replay cap. -/
theorem runtimePrefix_lower_add_le_replayThresholdCap
    [NeZero d]
    (hdelta : 0 ≤ delta)
    (C : ReplayProgramStageCertificates hd hmn W root p radialIncremented delta epsilon
      (budgetedRootExtensionThresholdPolicy delta hdelta) initialEvent)
    (hm : 1 ≤ m) (hmnStrict : m + 1 < n)
    (hroot : (root : Cubic d) = cubicOrigin)
    (history : List (F × Bool)) {X : CubicEdge d → ℝ}
    (hinitial : X ∈ initialEvent)
    (hhistory : X ∈ AdaptiveSiteExploration.adaptiveAnswerHistoryEvent
      (AdaptiveSiteExploration.finiteAdaptiveSuccessAnswer
        (paddedStageSuccess hd hmn W root p radialIncremented delta
          (budgetedRootExtensionThresholdPolicy delta hdelta))
        (4 * d)) history)
    (hadmissibleHistory : ∀ (prior : List (F × Bool)) (u : F) (accepted : Bool)
      (tail : List (F × Bool)),
      history = prior ++ (u, accepted) :: tail → AdmissibleQuery root prior u)
    (v : F) (hadmissible : AdmissibleQuery root history v) :
    let policy := budgetedRootExtensionThresholdPolicy delta hdelta
    let fullHistory := [(root, true)] ++ canonicalSuffix root history
    let S := replay hd hmn W root p radialIncremented delta policy X history
    let seed := inletSeed hd root fullHistory v S
    let incoming := incomingDirection hd root fullHistory v
    let first := firstFlip hd root fullHistory v S
    let directions := siteDirectionOrder hd root fullHistory v
    ∀ l (hl : l < directions.length) e,
      let Rl := LaterSiteRuntime.runFrom hmn seed.physicalCenter incoming first
        unusedSecondFlip p delta policy X
          (siteInitialRuntime (m + n + 1) v S seed) 0 (directions.take l)
      (Rl.source.lower e : ℝ) + delta ≤
        replayThresholdCap d p radialIncremented delta := by
  dsimp only
  intro l hl e
  let policy : RootExtensionThresholdPolicy d :=
    budgetedRootExtensionThresholdPolicy delta hdelta
  let fullHistory := [(root, true)] ++ canonicalSuffix root history
  let S := replay hd hmn W root p radialIncremented delta policy X history
  let seed := inletSeed hd root fullHistory v S
  let incoming := incomingDirection hd root fullHistory v
  let first := firstFlip hd root fullHistory v S
  let directions := siteDirectionOrder hd root fullHistory v
  change l < directions.length at hl
  have hlen : directions.length ≤ 4 * d := by
    simpa [directions, fullHistory] using siteDirectionOrder_length_le hd root fullHistory v
  have htake : (directions.take l).length = l := List.length_take_of_le (Nat.le_of_lt hl)
  have hN : 0 < m + n + 1 := by omega
  have hprior := replay_source_lower_le_spatialBudget hdelta C hm hmnStrict hroot
    history hinitial hhistory hadmissibleHistory e
  have hpBudget : (p : ℝ) ≤
      replayEdgeLowerBudget (m + n + 1) p radialIncremented delta root history
        e.1.out.1 := by
    have hnonnegRoot : 0 ≤
        ((rootExtensionDirectionOrder d).length : ℝ) * delta :=
      mul_nonneg (Nat.cast_nonneg _) hdelta
    have hnonnegSeen : 0 ≤
        ((replayInfluenceSitesSeen (m + n + 1) e.1.out.1 root history).card : ℝ) *
          (4 * d : ℕ) * delta := by positivity
    unfold replayEdgeLowerBudget rootReplayLowerBudget
    linarith [le_max_left (p : ℝ) (radialIncremented : ℝ)]
  by_cases hvInfluence : v.1 ∈
      grimmettMarstrandInfluenceSites (m + n + 1) e.1.out.1
  · have hruntime := LaterSiteRuntime.coe_runFrom_lower_le_add_length_at hmn
      seed.physicalCenter incoming first unusedSecondFlip p delta hdelta policy
      (fun T a f ↦ coe_budgetedRootExtensionThresholdPolicy_le_add delta hdelta T a f)
      X (siteInitialRuntime (m + n + 1) v S seed) 0 (directions.take l)
      (replayEdgeLowerBudget (m + n + 1) p radialIncremented delta root history
        e.1.out.1) e (by simpa [S, siteInitialRuntime, LaterSiteRuntime.initialAt] using hprior)
      hpBudget
    have hnotSeen := not_mem_replayInfluenceSitesSeen_of_admissibleQuery
      (m + n + 1) e.1.out.1 root history v hadmissible
    have hseen := replayInfluenceSitesSeen_append_singleton_of_mem
      (m + n + 1) e.1.out.1 root history v false hadmissible hvInfluence
    have hcardAll := card_replayInfluenceSitesSeen_le (m + n + 1) hN e.1.out.1 root
      (history ++ [(v, false)])
    rw [hseen, Finset.card_insert_of_notMem hnotSeen] at hcardAll
    have hlSucc : l + 1 ≤ 4 * d := by omega
    let seenCard := (replayInfluenceSitesSeen
      (m + n + 1) e.1.out.1 root history).card
    let capCard := (2 ^ d) * (2 * d + 1)
    have hnat : seenCard * (4 * d) + (l + 1) ≤ capCard * (4 * d) := by
      calc
        seenCard * (4 * d) + (l + 1) ≤ seenCard * (4 * d) + (4 * d) := by omega
        _ = (seenCard + 1) * (4 * d) := by simp [Nat.add_mul]
        _ ≤ capCard * (4 * d) := Nat.mul_le_mul_right (4 * d) hcardAll
    have hreal :
        (seenCard : ℝ) * (4 * d : ℕ) + (l + 1 : ℕ) ≤
          (capCard : ℝ) * (4 * d : ℕ) := by exact_mod_cast hnat
    have hmul := mul_le_mul_of_nonneg_right hreal hdelta
    rw [htake] at hruntime
    change
      ((LaterSiteRuntime.runFrom hmn seed.physicalCenter incoming first unusedSecondFlip
        p delta policy X (siteInitialRuntime (m + n + 1) v S seed) 0
        (directions.take l)).source.lower e : ℝ) + delta ≤ _
    unfold replayEdgeLowerBudget at hruntime
    unfold replayThresholdCap
    dsimp only [seenCard, capCard] at hmul
    push_cast at hruntime hmul ⊢
    nlinarith
  · have hwithin := C.supportsWithin_queryInfluenceRegion_replay hm hmnStrict hroot
      history hinitial hhistory hadmissibleHistory v hadmissible
    have hout : e.1.out.1 ∉
        grimmettMarstrandQueryInfluenceRegion (m + n + 1) v.1 := by
      intro he
      exact hvInfluence
        (mem_grimmettMarstrandInfluenceSites_of_mem_queryInfluenceRegion he)
    have heq := LaterSiteRuntime.runFrom_lower_eq_of_supportsWithin_of_endpoint_not_mem
      hmn seed.physicalCenter incoming first unusedSecondFlip p delta policy X
      (grimmettMarstrandQueryInfluenceRegion (m + n + 1) v.1)
      (siteInitialRuntime (m + n + 1) v S seed) 0 (directions.take l)
      (LaterSiteRuntime.supportsWithin_take hmn seed.physicalCenter incoming first
        unusedSecondFlip p delta policy X
        (grimmettMarstrandQueryInfluenceRegion (m + n + 1) v.1)
        (siteInitialRuntime (m + n + 1) v S seed) 0 directions hwithin l)
      e hout
    have hcard := card_replayInfluenceSitesSeen_le (m + n + 1) hN e.1.out.1 root history
    have hnat :
        (replayInfluenceSitesSeen (m + n + 1) e.1.out.1 root history).card * (4 * d) ≤
          ((2 ^ d) * (2 * d + 1)) * (4 * d) :=
      Nat.mul_le_mul_right (4 * d) hcard
    have hreal :
        ((replayInfluenceSitesSeen
          (m + n + 1) e.1.out.1 root history).card : ℝ) * (4 * d : ℕ) ≤
          (((2 ^ d) * (2 * d + 1) : ℕ) : ℝ) * (4 * d : ℕ) := by
      exact_mod_cast hnat
    have hmul := mul_le_mul_of_nonneg_right hreal hdelta
    change
      ((LaterSiteRuntime.runFrom hmn seed.physicalCenter incoming first unusedSecondFlip
        p delta policy X (siteInitialRuntime (m + n + 1) v S seed) 0
        (directions.take l)).source.lower e : ℝ) + delta ≤ _
    rw [heq]
    change ((S.source.lower e : ℝ) + delta ≤ _)
    change ((S.source.lower e : ℝ) ≤ _) at hprior
    unfold replayEdgeLowerBudget at hprior
    unfold replayThresholdCap
    push_cast at hprior hmul ⊢
    nlinarith

/-- The canonical total policy is the literal `lower + delta` policy at every reached runtime
prefix whenever the global replay cap fits in the unit interval. -/
theorem runtimePrefix_budgetedPolicy_eq_add
    [NeZero d]
    (hdelta : 0 ≤ delta)
    (C : ReplayProgramStageCertificates hd hmn W root p radialIncremented delta epsilon
      (budgetedRootExtensionThresholdPolicy delta hdelta) initialEvent)
    (hm : 1 ≤ m) (hmnStrict : m + 1 < n)
    (hroot : (root : Cubic d) = cubicOrigin)
    (hcap : replayThresholdCap d p radialIncremented delta ≤ 1)
    (history : List (F × Bool)) {X : CubicEdge d → ℝ}
    (hinitial : X ∈ initialEvent)
    (hhistory : X ∈ AdaptiveSiteExploration.adaptiveAnswerHistoryEvent
      (AdaptiveSiteExploration.finiteAdaptiveSuccessAnswer
        (paddedStageSuccess hd hmn W root p radialIncremented delta
          (budgetedRootExtensionThresholdPolicy delta hdelta))
        (4 * d)) history)
    (hadmissibleHistory : ∀ (prior : List (F × Bool)) (u : F) (accepted : Bool)
      (tail : List (F × Bool)),
      history = prior ++ (u, accepted) :: tail → AdmissibleQuery root prior u)
    (v : F) (hadmissible : AdmissibleQuery root history v) :
    let policy := budgetedRootExtensionThresholdPolicy delta hdelta
    let fullHistory := [(root, true)] ++ canonicalSuffix root history
    let S := replay hd hmn W root p radialIncremented delta policy X history
    let seed := inletSeed hd root fullHistory v S
    let incoming := incomingDirection hd root fullHistory v
    let first := firstFlip hd root fullHistory v S
    let directions := siteDirectionOrder hd root fullHistory v
    ∀ l (hl : l < directions.length) e,
      let Rl := LaterSiteRuntime.runFrom hmn seed.physicalCenter incoming first
        unusedSecondFlip p delta policy X
          (siteInitialRuntime (m + n + 1) v S seed) 0 (directions.take l)
      let a := directions[l]
      (policy Rl.source a e : ℝ) = (Rl.source.lower e : ℝ) + delta := by
  dsimp only
  intro l hl e
  let policy : RootExtensionThresholdPolicy d :=
    budgetedRootExtensionThresholdPolicy delta hdelta
  let fullHistory := [(root, true)] ++ canonicalSuffix root history
  let S := replay hd hmn W root p radialIncremented delta policy X history
  let seed := inletSeed hd root fullHistory v S
  let incoming := incomingDirection hd root fullHistory v
  let first := firstFlip hd root fullHistory v S
  let directions := siteDirectionOrder hd root fullHistory v
  let Rl := LaterSiteRuntime.runFrom hmn seed.physicalCenter incoming first
    unusedSecondFlip p delta policy X
      (siteInitialRuntime (m + n + 1) v S seed) 0 (directions.take l)
  have hbudget : Rl.source.HasIncrementBudget delta := by
    intro f
    exact (runtimePrefix_lower_add_le_replayThresholdCap hdelta C hm hmnStrict hroot
      history hinitial hhistory hadmissibleHistory v hadmissible l hl f).trans hcap
  exact coe_budgetedRootExtensionThresholdPolicy_of_hasIncrementBudget
    delta hdelta Rl.source directions[l] hbudget e

/-- The actual later-site runtime satisfies the final-density prefix certificate whenever the
global replay cap is below `pFinal`. -/
theorem runtime_finalThresholdBoundedOnPrefixes_budgeted
    [NeZero d]
    (hdelta : 0 ≤ delta)
    (C : ReplayProgramStageCertificates hd hmn W root p radialIncremented delta epsilon
      (budgetedRootExtensionThresholdPolicy delta hdelta) initialEvent)
    (hm : 1 ≤ m) (hmnStrict : m + 1 < n)
    (hroot : (root : Cubic d) = cubicOrigin)
    (pFinal : I)
    (hcap : replayThresholdCap d p radialIncremented delta ≤ (pFinal : ℝ))
    (history : List (F × Bool)) {X : CubicEdge d → ℝ}
    (hinitial : X ∈ initialEvent)
    (hhistory : X ∈ AdaptiveSiteExploration.adaptiveAnswerHistoryEvent
      (AdaptiveSiteExploration.finiteAdaptiveSuccessAnswer
        (paddedStageSuccess hd hmn W root p radialIncremented delta
          (budgetedRootExtensionThresholdPolicy delta hdelta))
        (4 * d)) history)
    (hadmissibleHistory : ∀ (prior : List (F × Bool)) (u : F) (accepted : Bool)
      (tail : List (F × Bool)),
      history = prior ++ (u, accepted) :: tail → AdmissibleQuery root prior u)
    (v : F) (hadmissible : AdmissibleQuery root history v) :
    let policy := budgetedRootExtensionThresholdPolicy delta hdelta
    let fullHistory := [(root, true)] ++ canonicalSuffix root history
    let S := replay hd hmn W root p radialIncremented delta policy X history
    let seed := inletSeed hd root fullHistory v S
    let incoming := incomingDirection hd root fullHistory v
    let first := firstFlip hd root fullHistory v S
    let directions := siteDirectionOrder hd root fullHistory v
    LaterSiteRuntime.FinalThresholdBoundedOnPrefixes hmn seed.physicalCenter incoming
      first unusedSecondFlip p pFinal delta policy X
      (siteInitialRuntime (m + n + 1) v S seed) 0 directions := by
  dsimp only
  intro l hl e
  let policy : RootExtensionThresholdPolicy d :=
    budgetedRootExtensionThresholdPolicy delta hdelta
  let fullHistory := [(root, true)] ++ canonicalSuffix root history
  let S := replay hd hmn W root p radialIncremented delta policy X history
  let seed := inletSeed hd root fullHistory v S
  let incoming := incomingDirection hd root fullHistory v
  let first := firstFlip hd root fullHistory v S
  let directions := siteDirectionOrder hd root fullHistory v
  let Rl := LaterSiteRuntime.runFrom hmn seed.physicalCenter incoming first
    unusedSecondFlip p delta policy X
      (siteInitialRuntime (m + n + 1) v S seed) 0 (directions.take l)
  calc
    (policy Rl.source directions[l] e : ℝ) ≤
        (Rl.source.lower e : ℝ) + delta :=
      coe_budgetedRootExtensionThresholdPolicy_le_add delta hdelta Rl.source
        directions[l] e
    _ ≤ replayThresholdCap d p radialIncremented delta :=
      runtimePrefix_lower_add_le_replayThresholdCap hdelta C hm hmnStrict hroot
        history hinitial hhistory hadmissibleHistory v hadmissible l hl e
    _ ≤ (pFinal : ℝ) := hcap

end DynamicBlockHistoryReplay

end Percolation
