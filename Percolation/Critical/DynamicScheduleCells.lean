import Percolation.Critical.DynamicExploredRegion

/-!
# Reveal schedules as concrete restart-cell multiplicities

This file connects the earlier list-of-support accounting to the finite reveal-cell index.  An
overlap bound `2d+1` turns each natural multiplicity into `Fin (2d+2)`, and the heterogeneous
threshold carried by the realized cell is exactly the schedule's accumulated threshold.
-/

namespace Percolation

open scoped unitInterval

namespace FiniteRevealSchedule

variable {d : ℕ}

/-- Restrict an overlap-bounded schedule multiplicity to the finite range used by reveal cells. -/
noncomputable def boundedMultiplicity
    (S : FiniteRevealSchedule (CubicEdge d))
    (hS : S.HasOverlapBound (2 * d + 1)) (e : CubicEdge d) : Fin (2 * d + 2) :=
  ⟨S.multiplicity e, by have := hS e; omega⟩

@[simp]
theorem boundedMultiplicity_val
    (S : FiniteRevealSchedule (CubicEdge d))
    (hS : S.HasOverlapBound (2 * d + 1)) (e : CubicEdge d) :
    (S.boundedMultiplicity hS e).val = S.multiplicity e :=
  rfl

end FiniteRevealSchedule

namespace RestartRevealCellIndex

/-- Realized cell obtained from a concrete explored configuration and an overlap-bounded global
reveal schedule. -/
noncomputable def ofScheduleExploredRegion
    {d m n : ℕ} (i : Fin d) (omega : EdgeConfiguration d)
    (S : FiniteRevealSchedule (CubicEdge d))
    (hS : S.HasOverlapBound (2 * d + 1)) :
    RestartRevealCellIndex d i m n :=
  ofExploredRegion i omega fun e => S.boundedMultiplicity hS e.1

@[simp]
theorem regionVertices_ofScheduleExploredRegion
    {d m n : ℕ} (i : Fin d) (omega : EdgeConfiguration d)
    (S : FiniteRevealSchedule (CubicEdge d))
    (hS : S.HasOverlapBound (2 * d + 1)) :
    (ofScheduleExploredRegion (m := m) (n := n) i omega S hS).regionVertices =
      restartExploredRegion d omega m n := by
  rfl

theorem edgeMultiplicity_ofScheduleExploredRegion
    {d m n : ℕ} (i : Fin d) (omega : EdgeConfiguration d)
    (S : FiniteRevealSchedule (CubicEdge d))
    (hS : S.HasOverlapBound (2 * d + 1))
    {e : CubicEdge d} (he : e ∈ seedConnectionSupport d i m n) :
    (ofScheduleExploredRegion (m := m) (n := n) i omega S hS).edgeMultiplicity e =
      S.multiplicity e := by
  simp only [edgeMultiplicity, he, dite_true, ofScheduleExploredRegion,
    ofExploredRegion, FiniteRevealSchedule.boundedMultiplicity]

/-- On every coordinate read by the restart, the cell threshold is exactly the threshold
computed by the global reveal schedule. -/
theorem thresholdProfile_ofScheduleExploredRegion
    {d m n : ℕ} (i : Fin d) (omega : EdgeConfiguration d)
    (S : FiniteRevealSchedule (CubicEdge d))
    (hS : S.HasOverlapBound (2 * d + 1))
    (base delta : ℝ) (hbase : 0 ≤ base) (hdelta : 0 ≤ delta)
    (hupper : base + (2 * d + 1 : ℕ) * delta ≤ 1)
    {e : CubicEdge d} (he : e ∈ seedConnectionSupport d i m n) :
    ((ofScheduleExploredRegion (m := m) (n := n) i omega S hS).thresholdProfile
      base delta hbase hdelta hupper e : ℝ) =
      S.accumulatedThreshold base delta e := by
  rw [coe_thresholdProfile,
    edgeMultiplicity_ofScheduleExploredRegion (m := m) (n := n) i omega S hS he]
  rfl

/-- Source specialization of the preceding exact threshold identity. -/
theorem dynamicThresholdProfile_ofScheduleExploredRegion
    {d m n : ℕ} (i : Fin d) (omega : EdgeConfiguration d)
    (S : FiniteRevealSchedule (CubicEdge d))
    (hS : S.HasOverlapBound (2 * d + 1))
    (pc eta : ℝ) (hpc : 0 ≤ pc) (heta : 0 ≤ eta) (htotal : pc + eta ≤ 1)
    {e : CubicEdge d} (he : e ∈ seedConnectionSupport d i m n) :
    ((ofScheduleExploredRegion (m := m) (n := n) i omega S hS).dynamicThresholdProfile
      pc eta hpc heta htotal e : ℝ) =
      S.accumulatedThreshold (dynamicBlockBaseDensity pc eta)
        (dynamicBlockIncrement d eta) e := by
  rw [coe_dynamicThresholdProfile,
    edgeMultiplicity_ofScheduleExploredRegion (m := m) (n := n) i omega S hS he]
  rfl

end RestartRevealCellIndex

end Percolation
