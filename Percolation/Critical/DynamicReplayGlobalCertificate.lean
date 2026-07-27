import Percolation.Critical.DynamicReplayGlobalThreshold
import Percolation.Critical.DynamicReplayFinalThreshold

/-!
# Concrete final-density certificate

The scale-uniform spatial cap supplies every field of the reachable-state final-threshold
certificate used by the Chapter 7 connectivity bridge.
-/

namespace Percolation

open scoped unitInterval

namespace DynamicBlockHistoryReplay

variable {d m n : ℕ} {F : Set (Cubic d)} [LinearOrder F]
variable {p radialIncremented pFinal : I} {delta epsilon : ℝ}
variable {W : RootRadialSeedProfile d m n} {root : F}
variable {initialEvent : Set (CubicEdge d → ℝ)}
variable {hd : 0 < d} {hmn : 2 * m ≤ n}

set_option maxHeartbeats 800000 in
/-- The canonical budgeted policy satisfies the complete reachable-state final-density
certificate once the explicit scale-uniform cap lies below `pFinal`. -/
noncomputable def replayProgramFinalThresholdCertificate_budgeted
    [NeZero d]
    (hdelta : 0 ≤ delta)
    (C : ReplayProgramStageCertificates hd hmn W root p radialIncremented delta epsilon
      (budgetedRootExtensionThresholdPolicy delta hdelta) initialEvent)
    (hm : 1 ≤ m) (hmnStrict : m + 1 < n)
    (hroot : (root : Cubic d) = cubicOrigin)
    (hcap : replayThresholdCap d p radialIncremented delta ≤ (pFinal : ℝ)) :
    ReplayProgramFinalThresholdCertificate C pFinal where
  base_le := by
    have hnonnegRoot : 0 ≤
        ((rootExtensionDirectionOrder d).length : ℝ) * delta :=
      mul_nonneg (Nat.cast_nonneg _) hdelta
    have hnonnegSpatial : 0 ≤
        (((2 ^ d) * (2 * d + 1) : ℕ) : ℝ) * (4 * d : ℕ) * delta := by
      positivity
    unfold replayThresholdCap rootReplayLowerBudget at hcap
    linarith [le_max_left (p : ℝ) (radialIncremented : ℝ)]
  radial_le := by
    have hnonnegRoot : 0 ≤
        ((rootExtensionDirectionOrder d).length : ℝ) * delta :=
      mul_nonneg (Nat.cast_nonneg _) hdelta
    have hnonnegSpatial : 0 ≤
        (((2 ^ d) * (2 * d + 1) : ℕ) : ℝ) * (4 * d : ℕ) * delta := by
      positivity
    unfold replayThresholdCap rootReplayLowerBudget at hcap
    linarith [le_max_right (p : ℝ) (radialIncremented : ℝ)]
  root_bounded := by
    intro X _hinitial
    apply W.finalThresholdBoundedOnPrefixes_budgeted p radialIncremented pFinal delta hdelta X
    have hnonnegSpatial : 0 ≤
        (((2 ^ d) * (2 * d + 1) : ℕ) : ℝ) * (4 * d : ℕ) * delta := by
      positivity
    unfold replayThresholdCap rootReplayLowerBudget at hcap
    linarith
  runtime_bounded := by
    intro history hadmissibleHistory v hadmissible X hinitial hhistory
    have hbounded := runtime_finalThresholdBoundedOnPrefixes_budgeted hdelta C hm hmnStrict hroot
      pFinal hcap history hinitial hhistory hadmissibleHistory v hadmissible
    have hquery : canonicalQueryFromFullHistory root
        ([(root, true)] ++ canonicalSuffix root history) = v :=
      canonicalQueryFromFullHistory_eq_of_admissibleQuery root history v hadmissible
    dsimp only at hbounded ⊢
    rw [hquery]
    exact hbounded

end DynamicBlockHistoryReplay

end Percolation
