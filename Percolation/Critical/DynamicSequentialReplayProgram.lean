import Percolation.Critical.DynamicSequentialReplayStageLaw

/-!
# Sequential program law for the Grimmett--Marstrand replay

This is the program-level replacement for the earlier stable-replay interface.  At slot `j`,
the outer event records exactly the first `j` semantic successes and the already observed coarse
history.  The certificate then freezes only the incoming replay state and lets the literal
runtime-prefix partition classify the preceding restart outcomes.

The resulting theorem is the null-history-safe product lower bound required by the sequential
domination argument.  It does not assume that a pre-query source history determines future
restart successes.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval

namespace DynamicBlockHistoryReplay

variable {d m n : ℕ} {F : Set (Cubic d)} [LinearOrder F]

/-- Correct per-slot certificate family for the complete source-faithful `4d` program. -/
structure SequentialReplayProgramStageCertificates
    (hd : 0 < d) (hmn : 2 * m ≤ n)
    (W : RootRadialSeedProfile d m n) (root : F)
    (p radialIncremented : I) (delta epsilon : ℝ)
    (incremented : RootExtensionThresholdPolicy d)
    (initialEvent : Set (CubicEdge d → ℝ)) where
  initial_subset_root_completion : initialEvent ⊆
    W.mixedExtensionPrefixSuccessEvent p radialIncremented delta incremented
      (rootExtensionDirectionOrder d).length
  root_policy_adds : W.PolicyAddsOnPrefixes p radialIncremented delta incremented
  slot : ∀ (history : List (F × Bool)) (v : F), AdmissibleQuery root history v →
    ∀ j, j < 4 * d →
      SequentialReplayStageCertificate hd hmn W root p radialIncremented delta epsilon
        incremented history v
        (initialEvent ∩
          (AdaptiveSiteExploration.finiteAdaptiveSuccessPrefix
              (paddedStageSuccess hd hmn W root p radialIncremented delta incremented)
              history v j ∩
            AdaptiveSiteExploration.adaptiveAnswerHistoryEvent
              (AdaptiveSiteExploration.finiteAdaptiveSuccessAnswer
                (paddedStageSuccess hd hmn W root p radialIncremented delta incremented)
                (4 * d)) history)) j

/-- Finite-depth version used to construct the program by chronological induction. -/
structure SequentialReplayProgramStageCertificatesBefore
    (hd : 0 < d) (hmn : 2 * m ≤ n)
    (W : RootRadialSeedProfile d m n) (root : F)
    (p radialIncremented : I) (delta epsilon : ℝ)
    (incremented : RootExtensionThresholdPolicy d)
    (initialEvent : Set (CubicEdge d → ℝ)) (depth : ℕ) where
  initial_subset_root_completion : initialEvent ⊆
    W.mixedExtensionPrefixSuccessEvent p radialIncremented delta incremented
      (rootExtensionDirectionOrder d).length
  root_policy_adds : W.PolicyAddsOnPrefixes p radialIncremented delta incremented
  slot : ∀ (history : List (F × Bool)), history.length < depth →
    ∀ (v : F), AdmissibleQuery root history v →
      ∀ j, j < 4 * d →
        SequentialReplayStageCertificate hd hmn W root p radialIncremented delta epsilon
          incremented history v
          (initialEvent ∩
            (AdaptiveSiteExploration.finiteAdaptiveSuccessPrefix
                (paddedStageSuccess hd hmn W root p radialIncremented delta incremented)
                history v j ∩
              AdaptiveSiteExploration.adaptiveAnswerHistoryEvent
                (AdaptiveSiteExploration.finiteAdaptiveSuccessAnswer
                  (paddedStageSuccess hd hmn W root p radialIncremented delta incremented)
                  (4 * d)) history)) j

namespace SequentialReplayProgramStageCertificatesBefore

variable {p radialIncremented : I} {delta epsilon : ℝ}
  {incremented : RootExtensionThresholdPolicy d}
  {W : RootRadialSeedProfile d m n} {root : F}
  {initialEvent : Set (CubicEdge d → ℝ)}
  {hd : 0 < d} {hmn : 2 * m ≤ n} {depth depth' : ℕ}

/-- Forget certificates above a smaller finite depth. -/
def restrict
    (C : SequentialReplayProgramStageCertificatesBefore hd hmn W root p radialIncremented
      delta epsilon incremented initialEvent depth)
    (hle : depth' ≤ depth) :
    SequentialReplayProgramStageCertificatesBefore hd hmn W root p radialIncremented
      delta epsilon incremented initialEvent depth' where
  initial_subset_root_completion := C.initial_subset_root_completion
  root_policy_adds := C.root_policy_adds
  slot history hhistory v hadmissible j hj :=
    C.slot history (hhistory.trans_le hle) v hadmissible j hj

/-- A complete family restricts to each finite history depth. -/
def ofProgram
    (C : SequentialReplayProgramStageCertificates hd hmn W root p radialIncremented delta
      epsilon incremented initialEvent) (depth : ℕ) :
    SequentialReplayProgramStageCertificatesBefore hd hmn W root p radialIncremented delta
      epsilon incremented initialEvent depth where
  initial_subset_root_completion := C.initial_subset_root_completion
  root_policy_adds := C.root_policy_adds
  slot history _hhistory v hadmissible j hj := C.slot history v hadmissible j hj

/-- Read the certificate for a concrete history from depth `history.length + 1`. -/
def toProgram
    (C : ∀ depth : ℕ,
      SequentialReplayProgramStageCertificatesBefore hd hmn W root p radialIncremented delta
        epsilon incremented initialEvent depth) :
    SequentialReplayProgramStageCertificates hd hmn W root p radialIncremented delta epsilon
      incremented initialEvent where
  initial_subset_root_completion := (C 0).initial_subset_root_completion
  root_policy_adds := (C 0).root_policy_adds
  slot history v hadmissible j hj :=
    (C (history.length + 1)).slot history (by omega) v hadmissible j hj

end SequentialReplayProgramStageCertificatesBefore

namespace SequentialReplayProgramStageCertificates

variable {p radialIncremented : I} {delta epsilon : ℝ}
  {incremented : RootExtensionThresholdPolicy d}
  {W : RootRadialSeedProfile d m n} {root : F}
  {initialEvent : Set (CubicEdge d → ℝ)}
  {hd : 0 < d} {hmn : 2 * m ≤ n}

/-- The corrected finite program has the exact adaptive product lower bound. -/
theorem hasAdaptiveAnswerLowerBoundWithin
    (C : SequentialReplayProgramStageCertificates hd hmn W root p radialIncremented delta
      epsilon incremented initialEvent)
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
    have hslot :=
      (C.slot history v hadmissible j hj).inter_paddedStageSuccess_measurable_and_lower |>.2
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
      answer_eq_finiteAdaptiveSuccessAnswer hd hmn W root p radialIncremented delta incremented
  simpa [hanswer] using hfinite

end SequentialReplayProgramStageCertificates

end DynamicBlockHistoryReplay

end Percolation
