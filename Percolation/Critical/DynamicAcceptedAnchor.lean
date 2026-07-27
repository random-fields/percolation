import Percolation.Critical.AdaptiveAcceptanceTime
import Percolation.Critical.AdaptiveStateReplay
import Percolation.Critical.DynamicBlockAssembly
import Percolation.Critical.DynamicReplayFinalThreshold

/-!
# Acceptance-time anchors for the dynamic block construction

A vertex in the limiting occupied coarse cluster was accepted at a finite chronological query.
This file packages that query, its exact answer-history cell, and its deterministic replay state.
It is the bridge from Lemma 7.24's limiting site cluster to a concrete selected bond seed.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval

namespace SiteExploration

variable {V Omega : Type*} [DecidableEq V] [LinearOrder V]

/-- Finite replay data witnessing that `v` received a true answer. -/
structure AcceptedReplayQuery (E : SiteExploration V)
    (answer : Omega → List (V × Bool) → V → Bool) (X : Omega) (v : V) where
  history : List (V × Bool)
  trace : E.IsReplayTrace history
  history_mem : X ∈ AdaptiveSiteExploration.adaptiveAnswerHistoryEvent answer history
  next_eq : SiteExploration.nextVertex (E.replayState history) = some v
  accepted : answer X history v = true

namespace AcceptedReplayQuery

/-- Every earlier entry in an accepted replay query is itself a genuine chronological query. -/
theorem prior_next_eq
    {E : SiteExploration V} {answer : Omega → List (V × Bool) → V → Bool}
    {X : Omega} {v : V} (Q : E.AcceptedReplayQuery answer X v)
    {prior tail : List (V × Bool)} {u : V} {accepted : Bool}
    (hdecomp : Q.history = prior ++ (u, accepted) :: tail) :
    SiteExploration.nextVertex (E.replayState prior) = some u :=
  Q.trace.nextVertex_of_eq_append_cons hdecomp

end AcceptedReplayQuery

/-- Every non-initial vertex in the occupied limit has an exact accepted replay query. -/
theorem exists_acceptedReplayQuery_of_mem_occupiedLimit
    (E : SiteExploration V)
    (answer : Omega → List (V × Bool) → V → Bool) (X : Omega) {v : V}
    (hv : v ∈ E.toAdaptive.occupiedLimit
      (SiteExploration.realizePrefixedAdaptiveAnswer E.initial.history answer X))
    (hvInitial : v ∉ E.initial.occupied) :
    Nonempty (E.AcceptedReplayQuery answer X v) := by
  let fullAnswer :=
    SiteExploration.realizePrefixedAdaptiveAnswer E.initial.history answer X
  obtain ⟨k, hnext, haccepted⟩ :=
    E.toAdaptive.exists_acceptance_step_of_mem_occupiedLimit fullAnswer hv hvInitial
  obtain ⟨history, hstate, hhistory, htrace⟩ :=
    E.exists_suffix_stateAfter_eq_replayState_isReplayTrace fullAnswer k
  have hhistoryMem :=
    E.toAdaptive.stateAfter_drop_initialHistory_mem_adaptiveAnswerHistoryEvent
      answer X k
  have hnext' : SiteExploration.nextVertex (E.replayState history) = some v := by
    rw [← hstate]
    exact hnext
  have haccepted' : answer X history v = true := by
    change answer X
      ((E.toAdaptive.stateAfter fullAnswer k).history.drop E.initial.history.length) v =
        true at haccepted
    rw [hhistory] at haccepted
    simpa using haccepted
  refine ⟨⟨history, htrace, ?_, hnext', haccepted'⟩⟩
  change X ∈ AdaptiveSiteExploration.adaptiveAnswerHistoryEvent answer
    ((E.toAdaptive.stateAfter fullAnswer k).history.drop E.initial.history.length) at hhistoryMem
  rw [hhistory] at hhistoryMem
  simpa using hhistoryMem

end SiteExploration

namespace DynamicBlockHistoryReplay

variable {d m n : ℕ} {F : Set (Cubic d)} [LinearOrder F]

/-- A chronological accepted query in the induced cubic exploration is an `AdmissibleQuery`
for the concrete dynamic replay, and so is every one of its prior entries. -/
theorem AcceptedReplayQuery.admissible
    {Omega : Type*} {root : F}
    {answer : Omega → List (F × Bool) → F → Bool} {X : Omega} {v : F}
    (Q : (cubicRegionSiteExploration d F root).AcceptedReplayQuery answer X v) :
    AdmissibleQuery root Q.history v := by
  constructor
  · exact ⟨v, SiteExploration.mem_frontier_of_nextVertex_eq_some Q.next_eq⟩
  · exact (cubicRegionSiteExploration d F root).replayQuery_eq_of_nextVertex_eq_some
      root Q.history Q.next_eq |>.symm

theorem AcceptedReplayQuery.allPriorAdmissible
    {Omega : Type*} {root : F}
    {answer : Omega → List (F × Bool) → F → Bool} {X : Omega} {v : F}
    (Q : (cubicRegionSiteExploration d F root).AcceptedReplayQuery answer X v) :
    ∀ (prior : List (F × Bool)) (u : F) (accepted : Bool)
      (tail : List (F × Bool)),
      Q.history = prior ++ (u, accepted) :: tail → AdmissibleQuery root prior u := by
  intro prior u accepted tail hdecomp
  have hnext := Q.prior_next_eq hdecomp
  constructor
  · exact ⟨u, SiteExploration.mem_frontier_of_nextVertex_eq_some hnext⟩
  · exact (cubicRegionSiteExploration d F root).replayQuery_eq_of_nextVertex_eq_some
      root prior hnext |>.symm

/-! ## A total local anchor selected at acceptance time -/

/-- Every coarse site admits a total physical anchor which is uniformly local.  On the root it
is the physical origin.  On an occupied non-root site it is the inlet seed present immediately
before that site's accepted query; otherwise it is the deterministic coarse-site center.

The conclusion is intentionally existential.  Its choice below is total on arbitrary labels
and arbitrary coarse sites, while the containment and connectivity fields are required only on
the occupied configurations used by the infinite-cluster argument. -/
theorem exists_localAcceptedAnchor
    [NeZero d]
    {p radialIncremented pFinal : I} {delta epsilon : ℝ}
    {incremented : RootExtensionThresholdPolicy d}
    {W : RootRadialSeedProfile d m n} {root : F}
    {initialEvent : Set (CubicEdge d → ℝ)}
    {hd : 0 < d} {hmn : 2 * m ≤ n}
    (C : ReplayProgramStageCertificates hd hmn W root p radialIncremented delta epsilon
      incremented initialEvent)
    (B : ReplayProgramFinalThresholdCertificate C pFinal)
    (hm : 1 ≤ m) (hmnStrict : m + 1 < n)
    (hroot : (root : Cubic d) = cubicOrigin)
    (hrootF : cubicOrigin ∈ F)
    (hneighborsF : ∀ a : CubicDirection d, cubicStepFrom cubicOrigin a ∈ F)
    (X : CubicEdge d → ℝ) (v : F) :
    ∃ z : Cubic d,
      z ∈ cubicMetricBox d
          (grimmettMarstrandSiteCenter (m + n + 1) v.1) (3 * (m + n + 1)) ∧
      (X ∈ initialEvent →
        v ∈ (cubicRegionSiteExploration d F root).toAdaptive.occupiedLimit
          (SiteExploration.realizePrefixedAdaptiveAnswer
            (cubicRegionSiteExploration d F root).initial.history
            (answer hd hmn W root p radialIncremented delta incremented) X) →
        z ∈ grimmettMarstrandThickening d F (m + n + 1)) ∧
      (X ∈ initialEvent →
        v ∈ (cubicRegionSiteExploration d F root).toAdaptive.occupiedLimit
          (SiteExploration.realizePrefixedAdaptiveAnswer
            (cubicRegionSiteExploration d F root).initial.history
            (answer hd hmn W root p radialIncremented delta incremented) X) →
        thresholdConfiguration pFinal X ∈
          connectionEventWithinVertices d
            (grimmettMarstrandThickening d F (m + n + 1)) cubicOrigin z) := by
  classical
  let E := cubicRegionSiteExploration d F root
  let concreteAnswer := answer hd hmn W root p radialIncremented delta incremented
  let fullAnswer := SiteExploration.realizePrefixedAdaptiveAnswer E.initial.history
    concreteAnswer X
  by_cases hX : X ∈ initialEvent
  · by_cases hvr : v = root
    · subst v
      have hcenter : grimmettMarstrandSiteCenter (m + n + 1) root.1 = cubicOrigin := by
        rw [hroot]
        ext i
        simp [grimmettMarstrandSiteCenter, cubicScale, cubicOrigin]
      refine ⟨cubicOrigin, ?_, ?_, ?_⟩
      · rw [hcenter, mem_cubicMetricBox]
        intro i
        omega
      · intro _hX _hv
        apply grimmettMarstrandCenteredBox_subset_thickening
          (N := m + n + 1) (R := 0) hrootF (by omega)
        change cubicOrigin ∈ cubicMetricBox d
          (grimmettMarstrandSiteCenter (m + n + 1) cubicOrigin) 0
        simp [grimmettMarstrandSiteCenter, cubicScale, cubicOrigin]
      · intro _hX _hv
        have horigin : cubicOrigin ∈
            grimmettMarstrandThickening d F (m + n + 1) := by
          apply grimmettMarstrandCenteredBox_subset_thickening
            (N := m + n + 1) (R := 0) hrootF (by omega)
          change cubicOrigin ∈ cubicMetricBox d
            (grimmettMarstrandSiteCenter (m + n + 1) cubicOrigin) 0
          simp [grimmettMarstrandSiteCenter, cubicScale, cubicOrigin]
        exact ⟨SimpleGraph.Walk.nil, by simp [walkIsOpen], by simpa using horigin⟩
    · by_cases hv : v ∈ E.toAdaptive.occupiedLimit fullAnswer
      · have hv' : v ∈ (cubicRegionSiteExploration d F root).toAdaptive.occupiedLimit
            (SiteExploration.realizePrefixedAdaptiveAnswer
              (cubicRegionSiteExploration d F root).initial.history concreteAnswer X) := by
          simpa [E, fullAnswer] using hv
        have hvInitial : v ∉ (cubicRegionSiteExploration d F root).initial.occupied := by
          simp [cubicRegionSiteExploration, rootedSiteExploration, hvr]
        let Q := Classical.choice
          (SiteExploration.exists_acceptedReplayQuery_of_mem_occupiedLimit
            (cubicRegionSiteExploration d F root) concreteAnswer X hv' hvInitial)
        have hQhistory : X ∈ AdaptiveSiteExploration.adaptiveAnswerHistoryEvent
            (AdaptiveSiteExploration.finiteAdaptiveSuccessAnswer
              (paddedStageSuccess hd hmn W root p radialIncremented delta incremented)
              (4 * d)) Q.history := by
          have hanswer := answer_eq_finiteAdaptiveSuccessAnswer hd hmn W root p
            radialIncremented delta incremented
          simpa [concreteAnswer, hanswer] using Q.history_mem
        have hQadmissible : AdmissibleQuery root Q.history v :=
          DynamicBlockHistoryReplay.AcceptedReplayQuery.admissible Q
        have hQprior :=
          DynamicBlockHistoryReplay.AcceptedReplayQuery.allPriorAdmissible Q
        let S := replay hd hmn W root p radialIncremented delta incremented X Q.history
        let fullHistory := [(root, true)] ++ canonicalSuffix root Q.history
        let parent := inletParent root fullHistory v
        let incoming := incomingDirection hd root fullHistory v
        let seed := inletSeed hd root fullHistory v S
        have hcompletion := C.initial_subset_root_completion hX
        have hcover : OutgoingCoversUndecidedNeighbors fullHistory S := by
          simpa [S, fullHistory] using outgoingCoversUndecidedNeighbors_replay hd hmn W root p
            radialIncremented delta incremented X Q.history hcompletion
        have hinstalled : S.SeedBoxesInstalled (m := m) := by
          exact C.seededBoxesInstalled_replay hm hmnStrict Q.history hX hQhistory hQprior
        have hU : S.outgoing parent incoming = some seed := by
          simpa [fullHistory, parent, incoming, seed] using
            inletSeed_parent_outgoing_of_admissibleQuery (m := m) hd root Q.history v S
              hQadmissible hcover hinstalled
        have hstep : cubicStepFrom (parent : Cubic d) incoming = (v : Cubic d) := by
          simpa [fullHistory, parent, incoming] using
            cubicStepFrom_inletParent_incomingDirection_of_admissibleQuery hd root Q.history v
              hQadmissible
        have hhalfwayState : S.OutgoingSeedsInHalfwayBoxes (N := m + n + 1) := by
          exact C.outgoingSeedsInHalfwayBoxes_replay hm hmnStrict hroot Q.history hX
            hQhistory hQprior
        have hseedHalfway : seed.physicalCenter ∈
            grimmettMarstrandHalfwayBox d (m + n + 1) parent.1 incoming :=
          hhalfwayState parent incoming seed hU
        refine ⟨seed.physicalCenter, ?_, ?_, ?_⟩
        · have hlocal := grimmettMarstrandHalfwayBox_subset_destinationBox parent.1 incoming
            hseedHalfway
          simpa [hstep] using hlocal
        · intro _hX _hv
          have hstepF : cubicStepFrom parent.1 incoming ∈ F := by
            rw [hstep]
            exact v.2
          exact grimmettMarstrandHalfwayBox_subset_thickening parent.2 hstepF hseedHalfway
        · intro _hX _hv
          exact B.outgoing_physicalCenter_connectedWithin_thickening_replay C hm hmnStrict
            hroot hrootF hneighborsF Q.history hX hQhistory hQprior hU
      · refine ⟨grimmettMarstrandSiteCenter (m + n + 1) v.1, ?_, ?_, ?_⟩
        · rw [mem_cubicMetricBox]
          intro i
          omega
        · intro _hX hv'
          exact False.elim (hv (by simpa [E, fullAnswer] using hv'))
        · intro _hX hv'
          exact False.elim (hv (by simpa [E, fullAnswer] using hv'))
  · refine ⟨grimmettMarstrandSiteCenter (m + n + 1) v.1, ?_, ?_, ?_⟩
    · rw [mem_cubicMetricBox]
      intro i
      omega
    · intro hX' _hv
      exact False.elim (hX hX')
    · intro hX' _hv
      exact False.elim (hX hX')

/-- A deterministic choice of the acceptance-time anchor supplied above.  The definition is
total, including outside the positive initialization event and away from the occupied limit. -/
noncomputable def localAcceptedAnchor
    [NeZero d]
    {p radialIncremented pFinal : I} {delta epsilon : ℝ}
    {incremented : RootExtensionThresholdPolicy d}
    {W : RootRadialSeedProfile d m n} {root : F}
    {initialEvent : Set (CubicEdge d → ℝ)}
    {hd : 0 < d} {hmn : 2 * m ≤ n}
    (C : ReplayProgramStageCertificates hd hmn W root p radialIncremented delta epsilon
      incremented initialEvent)
    (B : ReplayProgramFinalThresholdCertificate C pFinal)
    (hm : 1 ≤ m) (hmnStrict : m + 1 < n)
    (hroot : (root : Cubic d) = cubicOrigin)
    (hrootF : cubicOrigin ∈ F)
    (hneighborsF : ∀ a : CubicDirection d, cubicStepFrom cubicOrigin a ∈ F)
    (X : CubicEdge d → ℝ) (v : F) : Cubic d :=
  Classical.choose
    (exists_localAcceptedAnchor C B hm hmnStrict hroot hrootF hneighborsF X v)

/-- Uniform locality, occupied-site containment, and final-density confined connectivity for
the chosen acceptance-time anchor. -/
theorem localAcceptedAnchor_spec
    [NeZero d]
    {p radialIncremented pFinal : I} {delta epsilon : ℝ}
    {incremented : RootExtensionThresholdPolicy d}
    {W : RootRadialSeedProfile d m n} {root : F}
    {initialEvent : Set (CubicEdge d → ℝ)}
    {hd : 0 < d} {hmn : 2 * m ≤ n}
    (C : ReplayProgramStageCertificates hd hmn W root p radialIncremented delta epsilon
      incremented initialEvent)
    (B : ReplayProgramFinalThresholdCertificate C pFinal)
    (hm : 1 ≤ m) (hmnStrict : m + 1 < n)
    (hroot : (root : Cubic d) = cubicOrigin)
    (hrootF : cubicOrigin ∈ F)
    (hneighborsF : ∀ a : CubicDirection d, cubicStepFrom cubicOrigin a ∈ F)
    (X : CubicEdge d → ℝ) (v : F) :
    localAcceptedAnchor C B hm hmnStrict hroot hrootF hneighborsF X v ∈
        cubicMetricBox d
          (grimmettMarstrandSiteCenter (m + n + 1) v.1) (3 * (m + n + 1)) ∧
      (X ∈ initialEvent →
        v ∈ (cubicRegionSiteExploration d F root).toAdaptive.occupiedLimit
          (SiteExploration.realizePrefixedAdaptiveAnswer
            (cubicRegionSiteExploration d F root).initial.history
            (answer hd hmn W root p radialIncremented delta incremented) X) →
        localAcceptedAnchor C B hm hmnStrict hroot hrootF hneighborsF X v ∈
          grimmettMarstrandThickening d F (m + n + 1)) ∧
      (X ∈ initialEvent →
        v ∈ (cubicRegionSiteExploration d F root).toAdaptive.occupiedLimit
          (SiteExploration.realizePrefixedAdaptiveAnswer
            (cubicRegionSiteExploration d F root).initial.history
            (answer hd hmn W root p radialIncremented delta incremented) X) →
        thresholdConfiguration pFinal X ∈
          connectionEventWithinVertices d
            (grimmettMarstrandThickening d F (m + n + 1)) cubicOrigin
            (localAcceptedAnchor C B hm hmnStrict hroot hrootF hneighborsF X v)) := by
  exact Classical.choose_spec
    (exists_localAcceptedAnchor C B hm hmnStrict hroot hrootF hneighborsF X v)

/-- The certified replay percolates in the literal thickening.  This theorem closes the
deterministic/probabilistic bridge directly from the semantic replay certificates, without
repackaging them through a second abstract program structure. -/
theorem regionHasInfiniteClusterProbability_pos_of_replayCertificates
    [NeZero d]
    {p radialIncremented pFinal : I} {delta : ℝ}
    {incremented : RootExtensionThresholdPolicy d}
    {W : RootRadialSeedProfile d m n} {root : F}
    {initialEvent : Set (CubicEdge d → ℝ)}
    {hd : 0 < d} {hmn : 2 * m ≤ n}
    (hF : (cubicRegionGraph d F).Connected)
    (hsite1 : siteCriticalProbability (cubicRegionGraph d F) < 1)
    (C : ReplayProgramStageCertificates hd hmn W root p radialIncremented delta
      (dynamicBlockRestartError d (siteCriticalProbability (cubicRegionGraph d F)))
      incremented initialEvent)
    (B : ReplayProgramFinalThresholdCertificate C pFinal)
    (hm : 1 ≤ m) (hmnStrict : m + 1 < n)
    (hroot : (root : Cubic d) = cubicOrigin)
    (hrootF : cubicOrigin ∈ F)
    (hneighborsF : ∀ a : CubicDirection d, cubicStepFrom cubicOrigin a ∈ F)
    (hinitialMeasurable : MeasurableSet initialEvent)
    (hinitialPos : 0 < (couplingMeasure (CubicEdge d)).real initialEvent)
    (hanswer : AdaptiveSiteExploration.MeasurableAnswer
      (answer hd hmn W root p radialIncremented delta incremented)) :
    0 < regionHasInfiniteClusterProbability d
      (grimmettMarstrandThickening d F (m + n + 1)) pFinal := by
  let pcSite := siteCriticalProbability (cubicRegionGraph d F)
  let concreteAnswer := answer hd hmn W root p radialIncremented delta incremented
  let fullAnswer := SiteExploration.realizePrefixedAdaptiveAnswer
    (cubicRegionSiteExploration d F root).initial.history concreteAnswer
  let q := dynamicBlockSiteDensityUnit pcSite (siteCriticalProbability_nonneg _) hsite1
  have hlower : AdaptiveSiteExploration.HasAdaptiveAnswerLowerBoundWithin
      (couplingMeasure (CubicEdge d)) initialEvent concreteAnswer
      (AdmissibleQuery root) (dynamicBlockSiteDensity pcSite) := by
    apply (C.hasAdaptiveAnswerLowerBoundWithin
      ((dynamicBlockRestartError_le_one_eighth hd
        (siteCriticalProbability_nonneg _)).trans (by norm_num))).mono_density
    exact (dynamicBlock_restartPow_gt_siteDensity hd
      (siteCriticalProbability_nonneg _) hsite1).le
  have hinfinite :
      0 < (couplingMeasure (CubicEdge d)).real
        (initialEvent ∩ {X |
          ((cubicRegionSiteExploration d F root).toAdaptive.occupiedLimit
            (fullAnswer X)).Infinite}) := by
    apply SiteExploration.cubicRegionSiteExploration_infinite_inter_probability_pos_of_adaptiveLowerBoundWithin
      (answer := fullAnswer) (admissible := AdmissibleQuery root)
      d F root hF (couplingMeasure (CubicEdge d)) initialEvent hinitialMeasurable
        hinitialPos q
    · simpa [q, pcSite] using dynamicBlockSiteDensity_gt hsite1
    · exact SiteExploration.measurableAnswer_realizePrefixedAdaptiveAnswer hanswer _
    · simpa [fullAnswer, concreteAnswer] using hlower
    · intro history hfrontier
      exact admissibleQuery_replayQuery root history hfrontier
  let anchor : (CubicEdge d → ℝ) → F → Cubic d := fun X v ↦
    localAcceptedAnchor C B hm hmnStrict hroot hrootF hneighborsF X v
  have hrootOccupied : ∀ X, root ∈
      (cubicRegionSiteExploration d F root).toAdaptive.occupiedLimit (fullAnswer X) := by
    intro X
    apply (cubicRegionSiteExploration d F root).toAdaptive.occupied_subset_occupiedLimit
      (fullAnswer X) 0
    exact (cubicRegionSiteExploration_initial_openRootedAt d F root).1
  have hsubset :
      initialEvent ∩ {X |
          ((cubicRegionSiteExploration d F root).toAdaptive.occupiedLimit
            (fullAnswer X)).Infinite} ⊆
        (thresholdConfiguration pFinal) ⁻¹'
          {omega | hasInfiniteOpenClusterInVertices d
            (grimmettMarstrandThickening d F (m + n + 1)) omega} := by
    intro X hX
    apply hasInfiniteOpenClusterInVertices_of_infinite_anchor_connections_finiteFibers
      hX.2 (anchor X)
    · intro z
      apply finite_preimage_of_anchor_mem_siteBox
        (N := m + n + 1) (R := 3 * (m + n + 1)) (by omega) (anchor X)
      intro v
      exact (localAcceptedAnchor_spec C B hm hmnStrict hroot hrootF hneighborsF X v).1
    · exact hrootOccupied X
    · intro v hv
      exact (localAcceptedAnchor_spec C B hm hmnStrict hroot hrootF hneighborsF X v
        ).2.1 hX.1 (by simpa [fullAnswer, concreteAnswer] using hv)
    · intro v hv
      have hrootConnection :=
        (localAcceptedAnchor_spec C B hm hmnStrict hroot hrootF hneighborsF X root
          ).2.2 hX.1 (by simpa [fullAnswer, concreteAnswer] using hrootOccupied X)
      have hvConnection :=
        (localAcceptedAnchor_spec C B hm hmnStrict hroot hrootF hneighborsF X v
          ).2.2 hX.1 (by simpa [fullAnswer, concreteAnswer] using hv)
      exact connectionEventWithinVertices_trans_mem_dynamic
        (connectionEventWithinVertices_symm_mem_dynamic hrootConnection) hvConnection
  rw [← couplingMeasure_real_hasInfiniteOpenClusterInVertices_thresholdConfiguration]
  exact hinfinite.trans_le (measureReal_mono hsubset)

/-- Target-density form of Theorem 7.2(a) for the concrete certified replay and its selected
finite-fibre anchors.  The target `q` is deliberately independent of the auxiliary coarse
region's critical probability; the source-facing specialization takes
`q = cubicCriticalProbability d + eta`. -/
theorem exists_regionCriticalProbability_thickening_le_of_replayCertificates
    [NeZero d]
    {p radialIncremented pFinal : I} {delta q : ℝ}
    {incremented : RootExtensionThresholdPolicy d}
    {W : RootRadialSeedProfile d m n} {root : F}
    {initialEvent : Set (CubicEdge d → ℝ)}
    {hd : 0 < d} {hmn : 2 * m ≤ n}
    (hF : (cubicRegionGraph d F).Connected) (hd2 : 2 ≤ d)
    (hcrit : regionCriticalProbability d F < 1)
    (C : ReplayProgramStageCertificates hd hmn W root p radialIncremented delta
      (dynamicBlockRestartError d (siteCriticalProbability (cubicRegionGraph d F)))
      incremented initialEvent)
    (B : ReplayProgramFinalThresholdCertificate C pFinal)
    (hm : 1 ≤ m) (hmnStrict : m + 1 < n)
    (hroot : (root : Cubic d) = cubicOrigin)
    (hrootF : cubicOrigin ∈ F)
    (hneighborsF : ∀ a : CubicDirection d, cubicStepFrom cubicOrigin a ∈ F)
    (hinitialMeasurable : MeasurableSet initialEvent)
    (hinitialPos : 0 < (couplingMeasure (CubicEdge d)).real initialEvent)
    (hanswer : AdaptiveSiteExploration.MeasurableAnswer
      (answer hd hmn W root p radialIncremented delta incremented))
    (hpFinal : (pFinal : ℝ) ≤ q) :
    ∃ k : ℕ,
      regionCriticalProbability d (cubicDilatedThickening d F k) ≤ q := by
  apply exists_regionCriticalProbability_thickening_le_of_dynamicPercolation hpFinal
  exact regionHasInfiniteClusterProbability_pos_of_replayCertificates hF
    (siteCriticalProbability_lt_one_of_regionCriticalProbability_lt_one root hd2 hF hcrit)
    C B hm hmnStrict hroot hrootF hneighborsF hinitialMeasurable hinitialPos hanswer

/-- Region-relative compatibility wrapper for callers of the earlier replay API. -/
theorem exists_regionCriticalProbability_thickening_le_add_of_replayCertificates
    [NeZero d]
    {p radialIncremented pFinal : I} {delta eta : ℝ}
    {incremented : RootExtensionThresholdPolicy d}
    {W : RootRadialSeedProfile d m n} {root : F}
    {initialEvent : Set (CubicEdge d → ℝ)}
    {hd : 0 < d} {hmn : 2 * m ≤ n}
    (hF : (cubicRegionGraph d F).Connected) (hd2 : 2 ≤ d)
    (hcrit : regionCriticalProbability d F < 1)
    (C : ReplayProgramStageCertificates hd hmn W root p radialIncremented delta
      (dynamicBlockRestartError d (siteCriticalProbability (cubicRegionGraph d F)))
      incremented initialEvent)
    (B : ReplayProgramFinalThresholdCertificate C pFinal)
    (hm : 1 ≤ m) (hmnStrict : m + 1 < n)
    (hroot : (root : Cubic d) = cubicOrigin)
    (hrootF : cubicOrigin ∈ F)
    (hneighborsF : ∀ a : CubicDirection d, cubicStepFrom cubicOrigin a ∈ F)
    (hinitialMeasurable : MeasurableSet initialEvent)
    (hinitialPos : 0 < (couplingMeasure (CubicEdge d)).real initialEvent)
    (hanswer : AdaptiveSiteExploration.MeasurableAnswer
      (answer hd hmn W root p radialIncremented delta incremented))
    (hpFinal : (pFinal : ℝ) ≤ regionCriticalProbability d F + eta) :
    ∃ k : ℕ,
      regionCriticalProbability d (cubicDilatedThickening d F k) ≤
        regionCriticalProbability d F + eta :=
  exists_regionCriticalProbability_thickening_le_of_replayCertificates hF hd2 hcrit C B hm
    hmnStrict hroot hrootF hneighborsF hinitialMeasurable hinitialPos hanswer hpFinal

end DynamicBlockHistoryReplay

end Percolation
