import Percolation.Critical.DynamicSeedWitness
import Percolation.Critical.DynamicScheduleCells

/-!
# Restart reveal cells retaining the selected target seed

The original finite cell records the explored region and threshold multiplicities.  A dynamic
block chain also needs the concrete seed selected on success.  The augmented cell below remains
finite and records that value from the same reference-coordinate labels.  Its selected-seed
fiber is a cylinder on `seedConnectionSupport`, so this refinement introduces no hidden reveal
coordinates.
-/

namespace Percolation

open MeasureTheory
open scoped unitInterval

/-- Finite restart cell enriched by the deterministic target-seed choice. -/
structure SeededRestartRevealCellIndex (d : ℕ) (i : Fin d) (m n : ℕ) where
  revealCell : RestartRevealCellIndex d i m n
  selectedSeed : Option (RestartSeedWitnessIndex d i m n)

noncomputable instance seededRestartRevealCellIndexDecidableEq
    (d : ℕ) (i : Fin d) (m n : ℕ) :
    DecidableEq (SeededRestartRevealCellIndex d i m n) :=
  Classical.decEq _

def seededRestartRevealCellIndexEquiv (d : ℕ) (i : Fin d) (m n : ℕ) :
    SeededRestartRevealCellIndex d i m n ≃
      RestartRevealCellIndex d i m n ×
        Option (RestartSeedWitnessIndex d i m n) where
  toFun c := (c.revealCell, c.selectedSeed)
  invFun c := ⟨c.1, c.2⟩
  left_inv c := by cases c; rfl
  right_inv c := by cases c; rfl

noncomputable instance seededRestartRevealCellIndexFintype
    (d : ℕ) (i : Fin d) (m n : ℕ) :
    Fintype (SeededRestartRevealCellIndex d i m n) :=
  Fintype.ofEquiv
    (RestartRevealCellIndex d i m n ×
      Option (RestartSeedWitnessIndex d i m n))
    (seededRestartRevealCellIndexEquiv d i m n).symm

/-- Selected-seed fiber on common-uniform labels at a fixed final density. -/
def selectedRestartSeedWitnessLabelEvent
    {d m n : ℕ} (i : Fin d) (pFinal : I)
    (value : Option (RestartSeedWitnessIndex d i m n)) :
    Set (CubicEdge d → ℝ) :=
  {X | selectedRestartSeedWitness d i m n
      (thresholdConfiguration pFinal X) = value}

theorem measurableSet_selectedRestartSeedWitnessLabelEvent
    {d m n : ℕ} (i : Fin d) (pFinal : I)
    (value : Option (RestartSeedWitnessIndex d i m n)) :
    MeasurableSet (selectedRestartSeedWitnessLabelEvent i pFinal value) :=
  (dependsOn_selectedRestartSeedWitnessFiber d i m n value).measurableSet.preimage
    (measurable_thresholdConfiguration pFinal)

/-- The selected-seed fiber reads only the original seeded-connection support. -/
theorem measurableSet_selectedRestartSeedWitnessLabelEvent_coordSigma
    {d m n : ℕ} (i : Fin d) (pFinal : I)
    (value : Option (RestartSeedWitnessIndex d i m n)) :
    MeasurableSet[coordSigma (CubicEdge d)
      (seedConnectionSupport d i m n : Set (CubicEdge d))]
      (selectedRestartSeedWitnessLabelEvent i pFinal value) := by
  apply measurableSet_coordSigma_of_eqOn
    (measurableSet_selectedRestartSeedWitnessLabelEvent i pFinal value)
  intro X Y hXY
  change (selectedRestartSeedWitness d i m n (thresholdConfiguration pFinal X) = value ↔
    selectedRestartSeedWitness d i m n (thresholdConfiguration pFinal Y) = value)
  rw [selectedRestartSeedWitness_congr_of_eqOn_seedConnectionSupport]
  intro e he
  change (X e < (pFinal : ℝ) ↔ Y e < (pFinal : ℝ))
  rw [hXY e he]

/-- Actual augmented cell computed from one label field. -/
noncomputable def realizedSeededRestartRevealCell
    {d m n : ℕ} (i : Fin d) (beta : CubicEdge d → I) (pFinal : I)
    (S : FiniteRevealSchedule (CubicEdge d))
    (hS : S.HasOverlapBound (2 * d + 1))
    (X : CubicEdge d → ℝ) : SeededRestartRevealCellIndex d i m n where
  revealCell := realizedScheduleRevealCell i beta S hS X
  selectedSeed := selectedRestartSeedWitness d i m n
    (thresholdConfiguration pFinal X)

@[simp]
theorem realizedSeededRestartRevealCell_revealCell
    {d m n : ℕ} (i : Fin d) (beta : CubicEdge d → I) (pFinal : I)
    (S : FiniteRevealSchedule (CubicEdge d))
    (hS : S.HasOverlapBound (2 * d + 1)) (X : CubicEdge d → ℝ) :
    (realizedSeededRestartRevealCell (m := m) (n := n)
      i beta pFinal S hS X).revealCell =
      realizedScheduleRevealCell i beta S hS X :=
  rfl

@[simp]
theorem realizedSeededRestartRevealCell_selectedSeed
    {d m n : ℕ} (i : Fin d) (beta : CubicEdge d → I) (pFinal : I)
    (S : FiniteRevealSchedule (CubicEdge d))
    (hS : S.HasOverlapBound (2 * d + 1)) (X : CubicEdge d → ℝ) :
    (realizedSeededRestartRevealCell (m := m) (n := n)
      i beta pFinal S hS X).selectedSeed =
      selectedRestartSeedWitness d i m n (thresholdConfiguration pFinal X) :=
  rfl

theorem realizedSeededRestartRevealCell_eq_iff
    {d m n : ℕ} (i : Fin d) (beta : CubicEdge d → I) (pFinal : I)
    (S : FiniteRevealSchedule (CubicEdge d))
    (hS : S.HasOverlapBound (2 * d + 1))
    (X Y : CubicEdge d → ℝ) :
    realizedSeededRestartRevealCell (m := m) (n := n)
        i beta pFinal S hS X =
      realizedSeededRestartRevealCell i beta pFinal S hS Y ↔
      realizedScheduleRevealCell (m := m) (n := n) i beta S hS X =
          realizedScheduleRevealCell i beta S hS Y ∧
        selectedRestartSeedWitness d i m n (thresholdConfiguration pFinal X) =
          selectedRestartSeedWitness d i m n (thresholdConfiguration pFinal Y) := by
  constructor
  · intro h
    exact ⟨congrArg SeededRestartRevealCellIndex.revealCell h,
      congrArg SeededRestartRevealCellIndex.selectedSeed h⟩
  · rintro ⟨hreveal, hseed⟩
    apply (seededRestartRevealCellIndexEquiv d i m n).injective
    exact Prod.ext hreveal hseed

/-- Fiber characterization used by the later partition constructor. -/
theorem realizedSeededRestartRevealCell_eq_cell_iff
    {d m n : ℕ} (i : Fin d) (beta : CubicEdge d → I) (pFinal : I)
    (S : FiniteRevealSchedule (CubicEdge d))
    (hS : S.HasOverlapBound (2 * d + 1))
    (X : CubicEdge d → ℝ) (c : SeededRestartRevealCellIndex d i m n) :
    realizedSeededRestartRevealCell i beta pFinal S hS X = c ↔
      realizedScheduleRevealCell i beta S hS X = c.revealCell ∧
        X ∈ selectedRestartSeedWitnessLabelEvent i pFinal c.selectedSeed := by
  cases c
  simp [realizedSeededRestartRevealCell,
    selectedRestartSeedWitnessLabelEvent]

namespace SeededRestartRevealCellIndex

/-- Physical center of the selected target seed.  A failed cell has no next center. -/
def nextPhysicalSeedCenter
    {d m n : ℕ} {i : Fin d} (c : SeededRestartRevealCellIndex d i m n)
    (center : Cubic d) (a : CubicDirection d) (transverseFlip : Fin d → Bool) :
    Option (Cubic d) :=
  c.selectedSeed.map fun W ↦
    cubicRestartFrameIso center a transverseFlip W.seedCenter.1

@[simp]
theorem nextPhysicalSeedCenter_of_selected
    {d m n : ℕ} {i : Fin d} (c : SeededRestartRevealCellIndex d i m n)
    (center : Cubic d) (a : CubicDirection d) (transverseFlip : Fin d → Bool)
    (W : RestartSeedWitnessIndex d i m n) (hW : c.selectedSeed = some W) :
    c.nextPhysicalSeedCenter center a transverseFlip =
      some (cubicRestartFrameIso center a transverseFlip W.seedCenter.1) := by
  simp [nextPhysicalSeedCenter, hW]

/-- Compensation mask for continuing in the same reference exit coordinate.  It is computed
from the recorded inlet seed rather than supplied as a theorem parameter. -/
def nextCompensatingTransverseFlip
    {d m n : ℕ} {i : Fin d} (c : SeededRestartRevealCellIndex d i m n)
    (a : CubicDirection d) : Fin d → Bool :=
  match c.selectedSeed with
  | none => fun _ ↦ false
  | some W => inletCompensatingTransverseFlip a W.seedCenter.1

@[simp]
theorem nextCompensatingTransverseFlip_of_selected
    {d m n : ℕ} {i : Fin d} (c : SeededRestartRevealCellIndex d i m n)
    (a : CubicDirection d) (W : RestartSeedWitnessIndex d i m n)
    (hW : c.selectedSeed = some W) :
    c.nextCompensatingTransverseFlip a =
      inletCompensatingTransverseFlip a W.seedCenter.1 := by
  simp [nextCompensatingTransverseFlip, hW]

end SeededRestartRevealCellIndex

end Percolation
