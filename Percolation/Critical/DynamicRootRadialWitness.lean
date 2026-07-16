import Percolation.Critical.DynamicRootCompletion
import Percolation.Critical.DynamicSourceSchedule
import Percolation.Critical.DynamicSeedWitness

/-!
# Selected seeds from the radial root phase

The `2d` post-radial root extensions are centered at the actual seeds selected by the preceding
simultaneous radial event. This file retains those finite witness values and proves that every
radial success supplies a final-density physical connection to its selected seed. The second
root phase can therefore no longer choose unrelated or existentially varying centers.
-/

namespace Percolation

open scoped unitInterval

/-- Deterministic witness selected from the literal mixed-threshold radial restart.  Unlike
`rootRadialSelectedSeed`, this selector cannot introduce a seed that appears only after raising
all coordinates to a later final density. -/
noncomputable def rootRadialMixedSelectedSeed
    (d m n : ℕ) (p : I) (delta : ℝ) (a : CubicDirection d)
    (X : CubicEdge d → ℝ) : Option (RestartSeedWitnessIndex d a.1 m n) :=
  selectedMixedRestartSeedWitness d a.1 m n
    (cubicMetricBox d cubicOrigin m) p (fun _ ↦ 0) delta
    (cubicGraphIsoCouplingReindex
      (cubicRestartFrameIso cubicOrigin a (rootRadialTransverseFlip a)) X)

/-- Every successful radial branch has a deterministic seed witness for the very
mixed-threshold certificate used by the source exploration. -/
theorem exists_rootRadialMixedSelectedSeed_of_success
    {d m n : ℕ} (a : CubicDirection d) {p : I} {delta : ℝ}
    {X : CubicEdge d → ℝ}
    (hsuccess : X ∈ rootBranchSuccessEvent d m n p delta a) :
    ∃ W : RestartSeedWitnessIndex d a.1 m n,
      rootRadialMixedSelectedSeed d m n p delta a X = some W ∧
        W.IsMixedRestartWitness (cubicMetricBox d cubicOrigin m)
          p (fun _ ↦ 0) delta
          (cubicGraphIsoCouplingReindex
            (cubicRestartFrameIso cubicOrigin a (rootRadialTransverseFlip a)) X) := by
  change cubicGraphIsoCouplingReindex
      (cubicRestartFrameIso cubicOrigin a (rootRadialTransverseFlip a)) X ∈
    sprinkledRestartEvent d a.1 m n (cubicMetricBox d cubicOrigin m)
      p (fun _ ↦ 0) delta at hsuccess
  simpa [rootRadialMixedSelectedSeed] using
    (selectedMixedRestartSeedWitness_eq_some_of_success hsuccess)

/-- Deterministic reference-coordinate seed selected by one radial root branch. -/
noncomputable def rootRadialSelectedSeed
    (d m n : ℕ) (pFinal : I) (a : CubicDirection d)
    (X : CubicEdge d → ℝ) : Option (RestartSeedWitnessIndex d a.1 m n) :=
  selectedRestartSeedWitness d a.1 m n
    (framedReferenceThresholdConfiguration cubicOrigin a
      (rootRadialTransverseFlip a) pFinal X)

/-- Physical center of the selected radial seed. -/
noncomputable def rootRadialPhysicalSeedCenter
    (d m n : ℕ) (pFinal : I) (a : CubicDirection d)
    (X : CubicEdge d → ℝ) : Option (Cubic d) :=
  (rootRadialSelectedSeed d m n pFinal a X).map fun W ↦
    cubicRestartFrameIso cubicOrigin a (rootRadialTransverseFlip a) W.seedCenter.1

/-- A successful radial branch selects a concrete seed and connects the central seed box to it
inside the physical radius-`n` box at the final density. -/
theorem exists_rootRadialSelectedSeed_of_success
    {d m n : ℕ} (hmn : m + 1 < n) (a : CubicDirection d)
    {X : CubicEdge d → ℝ} {p pFinal : I} {delta : ℝ}
    (hpFinal : (p : ℝ) ≤ (pFinal : ℝ))
    (hdeltaFinal : delta ≤ (pFinal : ℝ))
    (hsuccess : X ∈ rootBranchSuccessEvent d m n p delta a) :
    ∃ W : RestartSeedWitnessIndex d a.1 m n,
      rootRadialSelectedSeed d m n pFinal a X = some W ∧
      W.IsRealized
        (framedReferenceThresholdConfiguration cubicOrigin a
          (rootRadialTransverseFlip a) pFinal X) ∧
      ∃ z ∈ cubicMetricBox d cubicOrigin m,
        thresholdConfiguration pFinal X ∈
          connectionEventIn d (cubicBoxEdges d cubicOrigin n)
            (cubicRestartFrameIso cubicOrigin a (rootRadialTransverseFlip a) z)
            (cubicRestartFrameIso cubicOrigin a (rootRadialTransverseFlip a)
              W.boundaryPoint.1) := by
  let flip := rootRadialTransverseFlip a
  let Xref := cubicGraphIsoCouplingReindex
    (cubicRestartFrameIso cubicOrigin a flip) X
  have hsuccessRef : Xref ∈ sprinkledRestartEvent d a.1 m n
      (cubicMetricBox d cubicOrigin m) p (fun _ ↦ 0) delta := by
    exact hsuccess
  have hconnection : thresholdConfiguration pFinal Xref ∈
      regionConnectionToFiniteTargetEvent d (cubicMetricBox d cubicOrigin m) n
        (seededBoundaryPointFinset d a.1 m n
          (thresholdConfiguration pFinal Xref)) := by
    apply sprinkledRestartEvent_subset_regionConnectionToSeededTarget
      (beta := fun _ ↦ 0) (delta := delta) hpFinal
      (hAvoid := regionAvoidsSeededBoundaryQuadrant_centralBox hmn a.1)
    · intro e _he
      simpa using hdeltaFinal
    · exact hsuccessRef
  obtain ⟨z, hz, y, hy, hzy⟩ := hconnection
  have hselected := exists_selectedFramedRestartSeed_of_inletConnection
    cubicOrigin a flip pFinal X ⟨z, hz, y, hy, hzy⟩
  simpa [rootRadialSelectedSeed, flip] using hselected

/-- One selected witness for every signed radial direction. -/
abbrev RootRadialSeedProfile (d m n : ℕ) :=
  ∀ a : CubicDirection d, RestartSeedWitnessIndex d a.1 m n

/-- The simultaneous radial event supplies one deterministic mixed-threshold witness in every
signed direction. -/
theorem exists_rootRadialMixedSeedProfile_of_mem
    {d m n : ℕ} {p : I} {delta : ℝ} {X : CubicEdge d → ℝ}
    (hroot : X ∈ rootRadialEvent d m n p delta) :
    ∃ W : RootRadialSeedProfile d m n,
      ∀ a : CubicDirection d,
        rootRadialMixedSelectedSeed d m n p delta a X = some (W a) ∧
          (W a).IsMixedRestartWitness (cubicMetricBox d cubicOrigin m)
            p (fun _ ↦ 0) delta
            (cubicGraphIsoCouplingReindex
              (cubicRestartFrameIso cubicOrigin a (rootRadialTransverseFlip a)) X) := by
  have hbranch : ∀ a : CubicDirection d,
      ∃ W : RestartSeedWitnessIndex d a.1 m n,
        rootRadialMixedSelectedSeed d m n p delta a X = some W ∧
          W.IsMixedRestartWitness (cubicMetricBox d cubicOrigin m)
            p (fun _ ↦ 0) delta
            (cubicGraphIsoCouplingReindex
              (cubicRestartFrameIso cubicOrigin a (rootRadialTransverseFlip a)) X) := by
    intro a
    apply exists_rootRadialMixedSelectedSeed_of_success a
    exact Set.mem_iInter.mp hroot.2 a
  choose W hW using hbranch
  exact ⟨W, hW⟩

/-- Physical center represented by a radial witness profile. -/
def RootRadialSeedProfile.physicalCenter
    {d m n : ℕ} (W : RootRadialSeedProfile d m n) (a : CubicDirection d) : Cubic d :=
  cubicRestartFrameIso cubicOrigin a (rootRadialTransverseFlip a) (W a).seedCenter.1

/-- Physical boundary point at which the radial connection enters the selected seed. -/
def RootRadialSeedProfile.physicalBoundaryPoint
    {d m n : ℕ} (W : RootRadialSeedProfile d m n) (a : CubicDirection d) : Cubic d :=
  cubicRestartFrameIso cubicOrigin a (rootRadialTransverseFlip a) (W a).boundaryPoint.1

/-- The literal radial event supplies all `2d` selected seeds simultaneously, with their
final-density central connections. -/
theorem exists_rootRadialSeedProfile_of_mem
    {d m n : ℕ} (hmn : m + 1 < n) {X : CubicEdge d → ℝ}
    {p pFinal : I} {delta : ℝ}
    (hpFinal : (p : ℝ) ≤ (pFinal : ℝ))
    (hdeltaFinal : delta ≤ (pFinal : ℝ))
    (hroot : X ∈ rootRadialEvent d m n p delta) :
    ∃ W : RootRadialSeedProfile d m n,
      ∀ a : CubicDirection d,
        rootRadialSelectedSeed d m n pFinal a X = some (W a) ∧
        (W a).IsRealized
          (framedReferenceThresholdConfiguration cubicOrigin a
            (rootRadialTransverseFlip a) pFinal X) ∧
        ∃ z ∈ cubicMetricBox d cubicOrigin m,
          thresholdConfiguration pFinal X ∈
            connectionEventIn d (cubicBoxEdges d cubicOrigin n)
              (cubicRestartFrameIso cubicOrigin a (rootRadialTransverseFlip a) z)
              (W.physicalBoundaryPoint a) := by
  classical
  have hall : ∀ a : CubicDirection d,
      ∃ W : RestartSeedWitnessIndex d a.1 m n,
        rootRadialSelectedSeed d m n pFinal a X = some W ∧
        W.IsRealized
          (framedReferenceThresholdConfiguration cubicOrigin a
            (rootRadialTransverseFlip a) pFinal X) ∧
        ∃ z ∈ cubicMetricBox d cubicOrigin m,
          thresholdConfiguration pFinal X ∈
            connectionEventIn d (cubicBoxEdges d cubicOrigin n)
              (cubicRestartFrameIso cubicOrigin a (rootRadialTransverseFlip a) z)
              (cubicRestartFrameIso cubicOrigin a (rootRadialTransverseFlip a)
                W.boundaryPoint.1) := by
    intro a
    apply exists_rootRadialSelectedSeed_of_success hmn a hpFinal hdeltaFinal
    exact Set.mem_iInter.mp hroot.2 a
  choose W hW using hall
  refine ⟨W, ?_⟩
  intro a
  simpa [RootRadialSeedProfile.physicalBoundaryPoint] using hW a

end Percolation
