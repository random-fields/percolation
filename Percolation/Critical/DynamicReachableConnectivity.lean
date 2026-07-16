import Percolation.Critical.DynamicLaterSiteConnectivity
import Percolation.Critical.DynamicRootConnectivity

/-!
# Final-density bounds along reachable dynamic prefixes

The total threshold policy is defined on every source state, including states which no
realization of the dynamic construction can reach.  Consequently the final-density argument
must not require a pointwise bound on that total function.  This file records the exact
reachable-prefix conditions and proves that they suffice for the pathwise connectivity
invariant.
-/

namespace Percolation

open scoped unitInterval

namespace RootRadialSeedProfile

/-- The increment policy is bounded by `pFinal` on precisely the root-extension prefix states
which occur in the supplied schedule. -/
def FinalThresholdBoundedOnPrefixes
    {d m n : ℕ} (W : RootRadialSeedProfile d m n)
    (p pFinal : I) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) (S : SourceFiniteEdgeRevealState d)
    (directions : List (CubicDirection d)) : Prop :=
  ∀ j (hj : j < directions.length) e,
    let Sj := W.runPostRadialExtensions p incremented X S (directions.take j)
    let a := directions[j]
    (incremented Sj a e : ℝ) ≤ (pFinal : ℝ)

/-- Origin connectivity through a root schedule needs threshold bounds only at its actual
prefix states. -/
theorem runPostRadialExtensions_rootedOpen_of_prefixBounds
    {d m n : ℕ} (W : RootRadialSeedProfile d m n)
    (p pFinal : I) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) (S : SourceFiniteEdgeRevealState d)
    (directions : List (CubicDirection d))
    (hrooted : S.RootedOpen (thresholdConfiguration pFinal X) cubicOrigin)
    (hpFinal : (p : ℝ) ≤ (pFinal : ℝ))
    (hbounded : W.FinalThresholdBoundedOnPrefixes p pFinal incremented X S directions) :
    (W.runPostRadialExtensions p incremented X S directions).RootedOpen
      (thresholdConfiguration pFinal X) cubicOrigin := by
  induction directions generalizing S with
  | nil => exact hrooted
  | cons a rest ih =>
      let Q := S.framedQuery (W.physicalCenter a) a
        (oppositeTransverseRestartFlip a)
      let S' := S.next (Q.restartSupport m n) p (incremented S a) X
      have hfirst : ∀ e, (incremented S a e : ℝ) ≤ (pFinal : ℝ) := by
        intro e
        simpa using hbounded 0 (by simp) e
      have hrooted' : S'.RootedOpen
          (thresholdConfiguration pFinal X) cubicOrigin := by
        exact S.rootedOpen_next (Q.restartSupport m n) p pFinal
          (incremented S a) X hrooted hpFinal hfirst
      apply ih (S := S') hrooted'
      intro j hj e
      have h := hbounded (j + 1) (by simp; omega) e
      simpa [FinalThresholdBoundedOnPrefixes, List.take_succ_cons, Q, S',
        RootRadialSeedProfile.runPostRadialExtensions] using h

/-- Reachable-prefix version of connectivity for the completed root state. -/
theorem completedRootExtensionState_rootedOpen_of_prefixBounds
    {d m n : ℕ} (W : RootRadialSeedProfile d m n)
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
    (W.completedRootExtensionState p radialIncremented incremented X).RootedOpen
      (thresholdConfiguration pFinal X) cubicOrigin := by
  have hseed : X ∈ rootSeedLabelEvent d m p := hcompletion.1.1
  have hpost := rootPostRadialSourceEdgeState_rootedOpen (n := n)
    p radialIncremented pFinal X hseed hpFinal hradialFinal
  simpa [RootRadialSeedProfile.completedRootExtensionState] using
    W.runPostRadialExtensions_rootedOpen_of_prefixBounds p pFinal incremented X
      (rootPostRadialSourceEdgeState d m n p radialIncremented X)
      (rootExtensionDirectionOrder d) hpost hpFinal hbounded

/-- The canonical budgeted policy satisfies the reachable root-prefix final-density bound
whenever the complete `2d` root budget fits below `pFinal`. -/
theorem finalThresholdBoundedOnPrefixes_budgeted
    {d m n : ℕ} (W : RootRadialSeedProfile d m n)
    (p radialIncremented pFinal : I) (delta : ℝ) (hdelta : 0 ≤ delta)
    (X : CubicEdge d → ℝ)
    (htotal : max (p : ℝ) (radialIncremented : ℝ) +
      ((rootExtensionDirectionOrder d).length : ℝ) * delta ≤ (pFinal : ℝ)) :
    W.FinalThresholdBoundedOnPrefixes p pFinal
      (budgetedRootExtensionThresholdPolicy delta hdelta) X
      (rootPostRadialSourceEdgeState d m n p radialIncremented X)
      (rootExtensionDirectionOrder d) := by
  intro j hj e
  let S := W.rootExtensionPrefixState p radialIncremented
    (budgetedRootExtensionThresholdPolicy delta hdelta) id j X
  have hlower : (S.lower e : ℝ) ≤
      max (p : ℝ) (radialIncremented : ℝ) + (j : ℝ) * delta := by
    exact W.coe_rootExtensionPrefixState_budgeted_lower_le p radialIncremented
      delta hdelta id j X e
  have hpolicy :
      (budgetedRootExtensionThresholdPolicy delta hdelta S
        (rootExtensionDirectionOrder d)[j] e : ℝ) ≤
        (S.lower e : ℝ) + delta :=
    coe_budgetedRootExtensionThresholdPolicy_le_add delta hdelta S
      (rootExtensionDirectionOrder d)[j] e
  have hjSucc : j + 1 ≤ (rootExtensionDirectionOrder d).length := by omega
  have hmul : ((j + 1 : ℕ) : ℝ) * delta ≤
      ((rootExtensionDirectionOrder d).length : ℝ) * delta := by
    apply mul_le_mul_of_nonneg_right _ hdelta
    exact_mod_cast hjSucc
  change
    (budgetedRootExtensionThresholdPolicy delta hdelta S
      (rootExtensionDirectionOrder d)[j] e : ℝ) ≤ (pFinal : ℝ)
  calc
    (budgetedRootExtensionThresholdPolicy delta hdelta S
      (rootExtensionDirectionOrder d)[j] e : ℝ) ≤ (S.lower e : ℝ) + delta := hpolicy
    _ ≤ max (p : ℝ) (radialIncremented : ℝ) + ((j + 1 : ℕ) : ℝ) * delta := by
      push_cast
      linarith
    _ ≤ max (p : ℝ) (radialIncremented : ℝ) +
        ((rootExtensionDirectionOrder d).length : ℝ) * delta := by linarith
    _ ≤ (pFinal : ℝ) := htotal

end RootRadialSeedProfile

namespace LaterSiteRuntime

/-- The increment policy is below the final density on the literal prefixes of one total
non-root runtime schedule. -/
def FinalThresholdBoundedOnPrefixes
    {d m n : ℕ} (hmn : 2 * m ≤ n)
    (inletCenter : Cubic d) (incoming : CubicDirection d)
    (firstFlip secondFlip : Fin d → Bool)
    (p pFinal : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) (R : LaterSiteRuntime d) (offset : ℕ)
    (directions : List (CubicDirection d)) : Prop :=
  ∀ j (hj : j < directions.length) e,
    let Rj := runFrom hmn inletCenter incoming firstFlip secondFlip
      p delta incremented X R offset (directions.take j)
    let a := directions[j]
    (incremented Rj.source a e : ℝ) ≤ (pFinal : ℝ)

/-- Root connectivity survives a total later-site runtime under bounds only at the runtime's
actual prefix states. -/
theorem rootedOpen_runFrom_of_prefixBounds
    {d m n : ℕ} (hmn : 2 * m ≤ n)
    (inletCenter : Cubic d) (incoming : CubicDirection d)
    (firstFlip secondFlip : Fin d → Bool)
    (p pFinal : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) (anchor : Cubic d)
    (R : LaterSiteRuntime d) (offset : ℕ)
    (directions : List (CubicDirection d))
    (hrooted : R.source.RootedOpen (thresholdConfiguration pFinal X) anchor)
    (hpFinal : (p : ℝ) ≤ (pFinal : ℝ))
    (hbounded : FinalThresholdBoundedOnPrefixes hmn inletCenter incoming firstFlip
      secondFlip p pFinal delta incremented X R offset directions) :
    (runFrom hmn inletCenter incoming firstFlip secondFlip p delta incremented X
      R offset directions).source.RootedOpen (thresholdConfiguration pFinal X) anchor := by
  induction directions generalizing R offset with
  | nil => exact hrooted
  | cons a rest ih =>
      let R' := R.step hmn inletCenter incoming firstFlip secondFlip
        p delta incremented X a offset
      have hfirst : ∀ e, (incremented R.source a e : ℝ) ≤ (pFinal : ℝ) := by
        intro e
        simpa using hbounded 0 (by simp) e
      have hrooted' : R'.source.RootedOpen
          (thresholdConfiguration pFinal X) anchor := by
        exact R.source.rootedOpen_next
          ((R.restartQuery inletCenter incoming firstFlip secondFlip a offset).restartSupport m n)
          p pFinal (incremented R.source a) X hrooted hpFinal hfirst
      apply ih (R := R') (offset := offset + 1) hrooted'
      intro j hj e
      have h := hbounded (j + 1) (by simp; omega) e
      simpa [FinalThresholdBoundedOnPrefixes, List.take_succ_cons, runFrom, R',
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

end LaterSiteRuntime

end Percolation
