import Percolation.Critical.DynamicReplayConnectivity

/-!
# Final-density certificate for the concrete Chapter 7 replay

The probability certificate and the final-density certificate have different jobs.  The former
proves the `4d` conditional success law.  The latter records Grimmett's `2d+1` reveal-overlap
accounting on the root prefixes and on the runtime prefixes which are actually reached.  Keeping
them separate prevents the success-attempt count from being mistaken for the threshold budget.
-/

namespace Percolation

open scoped unitInterval

namespace DynamicBlockHistoryReplay

variable {d m n : ℕ} {F : Set (Cubic d)} [LinearOrder F]
variable {p radialIncremented pFinal : I} {delta epsilon : ℝ}
variable {incremented : RootExtensionThresholdPolicy d}
variable {W : RootRadialSeedProfile d m n} {root : F}
variable {initialEvent : Set (CubicEdge d → ℝ)}
variable {hd : 0 < d} {hmn : 2 * m ≤ n}

/-- Reachable-state final-density accounting accompanying a replay probability certificate.
No condition is imposed on arbitrary source states outside the root and adaptive replay
executions. -/
structure ReplayProgramFinalThresholdCertificate
    (C : ReplayProgramStageCertificates hd hmn W root p radialIncremented delta epsilon
      incremented initialEvent)
    (pFinal : I) where
  base_le : (p : ℝ) ≤ (pFinal : ℝ)
  radial_le : (radialIncremented : ℝ) ≤ (pFinal : ℝ)
  root_bounded : ∀ {X : CubicEdge d → ℝ}, X ∈ initialEvent →
    W.FinalThresholdBoundedOnPrefixes p pFinal incremented X
      (rootPostRadialSourceEdgeState d m n p radialIncremented X)
      (rootExtensionDirectionOrder d)
  runtime_bounded : ∀ (history : List (F × Bool)) (v : F),
    AdmissibleQuery root history v →
    ∀ {X : CubicEdge d → ℝ}, X ∈ initialEvent →
      X ∈ AdaptiveSiteExploration.adaptiveAnswerHistoryEvent
        (AdaptiveSiteExploration.finiteAdaptiveSuccessAnswer
          (paddedStageSuccess hd hmn W root p radialIncremented delta incremented)
          (4 * d)) history →
      let fullHistory := [(root, true)] ++ canonicalSuffix root history
      let S := replay hd hmn W root p radialIncremented delta incremented X history
      let queried := canonicalQueryFromFullHistory root fullHistory
      let seed := inletSeed hd root fullHistory queried S
      let incoming := incomingDirection hd root fullHistory queried
      let first := firstFlip hd root fullHistory queried S
      let directions := siteDirectionOrder hd root fullHistory queried
      LaterSiteRuntime.FinalThresholdBoundedOnPrefixes hmn seed.physicalCenter incoming
        first unusedSecondFlip p pFinal delta incremented X
        (LaterSiteRuntime.initial S.source seed.physicalCenter) 0 directions

namespace ReplayProgramFinalThresholdCertificate

/-- Every state produced by a genuine finite adaptive history is root-connected at the final
density, using only the certificate's reachable root and runtime bounds. -/
theorem replay_source_rootedOpen
    (C : ReplayProgramStageCertificates hd hmn W root p radialIncremented delta epsilon
      incremented initialEvent)
    (B : ReplayProgramFinalThresholdCertificate C pFinal)
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
      ).source.RootedOpen (thresholdConfiguration pFinal X) cubicOrigin := by
  let finiteAnswer := AdaptiveSiteExploration.finiteAdaptiveSuccessAnswer
    (paddedStageSuccess hd hmn W root p radialIncremented delta incremented) (4 * d)
  induction history using List.reverseRecOn with
  | nil =>
      simpa [replay, canonicalSuffix, SiteExploration.replayState,
        cubicRegionSiteExploration, rootedSiteExploration] using
        DynamicBlockHistoryState.rooted_source_rootedOpen_of_prefixBounds W root p
          radialIncremented pFinal delta incremented X
          (C.initial_subset_root_completion hinitial) B.base_le B.radial_le
          (B.root_bounded hinitial)
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
      have hrootedPrior := ih
        (by simpa [finiteAnswer] using hhistorySplit.1) hadmissiblePrior
      have hbounded := B.runtime_bounded prior v hadmissibleLast hinitial
        (by simpa [finiteAnswer] using hhistorySplit.1)
      rw [replay_append_singleton_of_admissibleQuery hd hmn W root p radialIncremented
        delta incremented X prior v accepted hadmissibleLast]
      have hquery : canonicalQueryFromFullHistory root
          ([(root, true)] ++ canonicalSuffix root prior) = v :=
        canonicalQueryFromFullHistory_eq_of_admissibleQuery root prior v hadmissibleLast
      dsimp only at hbounded
      rw [hquery] at hbounded
      apply step_source_rootedOpen_of_prefixBounds hd hmn root
        ([(root, true)] ++ canonicalSuffix root prior) v accepted p pFinal delta
        incremented X (replay hd hmn W root p radialIncremented delta incremented X prior)
        hrootedPrior B.base_le
      exact hbounded

/-- Every published seed after a genuine replay lies in the origin component at the final
density, with no hypothesis about unreachable threshold-policy states. -/
theorem outgoing_physicalCenter_connected_replay
    [NeZero d]
    (C : ReplayProgramStageCertificates hd hmn W root p radialIncremented delta epsilon
      incremented initialEvent)
    (B : ReplayProgramFinalThresholdCertificate C pFinal)
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
    {v : F} {a : CubicDirection d} {U : LaterSiteOutgoingSeed d}
    (hU : (replay hd hmn W root p radialIncremented delta incremented X history
      ).outgoing v a = some U) :
    thresholdConfiguration pFinal X ∈
      connectionEvent d cubicOrigin U.physicalCenter := by
  let S := replay hd hmn W root p radialIncremented delta incremented X history
  have hrooted : S.source.RootedOpen
      (thresholdConfiguration pFinal X) cubicOrigin :=
    B.replay_source_rootedOpen C history hinitial hhistory hadmissible
  have hinstalled : S.SeedBoxesInstalled (m := m) :=
    C.seededBoxesInstalled_replay hm hmnStrict history hinitial hhistory hadmissible
  exact DynamicBlockHistoryState.outgoing_physicalCenter_connected hm hrooted
    hinstalled hU

end ReplayProgramFinalThresholdCertificate

end DynamicBlockHistoryReplay

end Percolation
