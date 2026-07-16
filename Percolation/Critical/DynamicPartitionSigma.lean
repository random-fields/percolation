import Percolation.Critical.DynamicHistoryReplayPartition
import Mathlib.Data.Fintype.Sigma

/-!
# Combining history-indexed finite restart partitions

The global replay partition and the per-site runtime partition have dependent cell types.
This constructor combines a finite family of framed restart stages by a sigma type while
retaining the exact cell union and pairwise disjointness.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval

/-- Union of a finite family of semantic successful slices. -/
def finiteSuccessSliceUnion {Omega C : Type*} [Fintype C]
    (success : C → Set Omega) : Set Omega :=
  ⋃ c, success c

theorem measurableSet_finiteSuccessSliceUnion
    {Omega C : Type*} [MeasurableSpace Omega] [Fintype C]
    {success : C → Set Omega} (hmeasurable : ∀ c, MeasurableSet (success c)) :
    MeasurableSet (finiteSuccessSliceUnion success) := by
  apply MeasurableSet.iUnion
  exact hmeasurable

theorem finiteSuccessSliceUnion_subset
    {Omega C : Type*} [Fintype C]
    {cell success : C → Set Omega}
    (hsubset : ∀ c, success c ⊆ cell c) :
    finiteSuccessSliceUnion success ⊆ ⋃ c, cell c := by
  intro omega homega
  rw [finiteSuccessSliceUnion, Set.mem_iUnion] at homega
  obtain ⟨c, hc⟩ := homega
  exact Set.mem_iUnion_of_mem c (hsubset c hc)

/-- Finite outer-cell composition for semantic stages.  Each component may itself be a
partitioned framed restart or a sure padding slice; only its measurable cell, successful
subset, and local lower bound are used. -/
theorem mul_measureReal_finiteCellUnion_le_successSliceUnion
    {Omega C : Type*} [MeasurableSpace Omega] [Fintype C] [DecidableEq C]
    {mu : Measure Omega} [IsFiniteMeasure mu]
    (cell success : C → Set Omega) (q : ℝ)
    (hpairwise : Set.PairwiseDisjoint (Set.univ : Set C) cell)
    (hcell : ∀ c, MeasurableSet (cell c))
    (hsuccess : ∀ c, MeasurableSet (success c))
    (hsubset : ∀ c, success c ⊆ cell c)
    (hlower : ∀ c, q * mu.real (cell c) ≤ mu.real (success c)) :
    q * mu.real (⋃ c, cell c) ≤ mu.real (finiteSuccessSliceUnion success) := by
  simpa [finiteSuccessSliceUnion] using
    (mul_measureReal_le_partitionedSuccess
      (Finset.univ : Finset C) cell success (⋃ c, cell c) q
      (by simp) (by simpa using hpairwise)
      (fun c _ ↦ hcell c) (fun c _ ↦ hsuccess c)
      (fun c _ ↦ hsubset c) (fun c _ ↦ hlower c))

namespace DynamicBlockHistoryReplay

variable {d m n : ℕ} {F : Set (Cubic d)} [LinearOrder F]

/-- Successful union indexed by the reachable stable global replay cells of one coarse
history.  Each component will be an active partitioned restart stage or the unchanged cell for
a padded slot. -/
abbrev stableReplaySuccessUnion
    {hd : 0 < d} {hmn : 2 * m ≤ n}
    {W : RootRadialSeedProfile d m n} {root : F}
    {p radialIncremented : I} {delta : ℝ}
    {incremented : RootExtensionThresholdPolicy d}
    {history : List (F × Bool)} {A : Set (CubicEdge d → ℝ)}
    (success : StableReplayStateIndex hd hmn W root p radialIncremented delta
      incremented history A → Set (CubicEdge d → ℝ)) :
    Set (CubicEdge d → ℝ) :=
  finiteSuccessSliceUnion success

/-- Outer stable replay cells sum their local null-safe restart bounds. -/
theorem mul_measureReal_stableReplayHistory_le_successUnion
    (hd : 0 < d) (hmn : 2 * m ≤ n)
    (W : RootRadialSeedProfile d m n) (root : F)
    (p radialIncremented : I) (delta : ℝ)
    (incremented : RootExtensionThresholdPolicy d)
    (history : List (F × Bool)) (A : Set (CubicEdge d → ℝ))
    (q : ℝ)
    (hreplay : ∀ X ∈ A, ∀ Y,
      Y ∈ (replay hd hmn W root p radialIncremented delta incremented X history
        ).source.historyProfile.event →
      replay hd hmn W root p radialIncremented delta incremented Y history =
        replay hd hmn W root p radialIncremented delta incremented X history)
    (hself : ∀ X ∈ A,
      X ∈ (replay hd hmn W root p radialIncremented delta incremented X history
        ).source.historyProfile.event)
    (hstable : ∀ X ∈ A,
      (replay hd hmn W root p radialIncremented delta incremented X history
        ).source.historyProfile.event ⊆ A)
    (success : StableReplayStateIndex hd hmn W root p radialIncremented delta
      incremented history A → Set (CubicEdge d → ℝ))
    (hsuccessMeasurable : ∀ c, MeasurableSet (success c))
    (hsuccessSubset : ∀ c, success c ⊆ c.1.1.source.historyProfile.event)
    (hlower : ∀ c,
      q * (couplingMeasure (CubicEdge d)).real c.1.1.source.historyProfile.event ≤
        (couplingMeasure (CubicEdge d)).real (success c)) :
    q * (couplingMeasure (CubicEdge d)).real A ≤
      (couplingMeasure (CubicEdge d)).real (stableReplaySuccessUnion success) := by
  have hhistory := stableReplayHistory_eq hd hmn W root p radialIncremented delta incremented
    history A hself hstable
  calc
    q * (couplingMeasure (CubicEdge d)).real A =
        q * (couplingMeasure (CubicEdge d)).real
          (stableReplayHistory (hd := hd) (hmn := hmn) (W := W) (root := root)
            (p := p) (radialIncremented := radialIncremented) (delta := delta)
            (incremented := incremented) (history := history) (A := A)) := by
      rw [hhistory]
    _ ≤ (couplingMeasure (CubicEdge d)).real
        (stableReplaySuccessUnion success) := by
      apply mul_measureReal_finiteCellUnion_le_successSliceUnion
        (fun c : StableReplayStateIndex hd hmn W root p radialIncremented delta
          incremented history A ↦ c.1.1.source.historyProfile.event)
        success q
      · intro c _hc c' _hc' hne
        exact pairwiseDisjoint_stableReplayHistory hd hmn W root p radialIncremented delta
          incremented history A hreplay c c' hne
      · intro c
        exact c.1.1.source.historyProfile.measurableSet_event
      · exact hsuccessMeasurable
      · exact hsuccessSubset
      · exact hlower

end DynamicBlockHistoryReplay

namespace AdaptiveSiteExploration.PartitionedFramedRestartStage

variable {d m n : ℕ} {p : I} {delta epsilon : ℝ}
variable {C : Type*} [Fintype C] [DecidableEq C]
variable (D : C → Type*) [∀ c, Fintype (D c)] [∀ c, DecidableEq (D c)]

/-- Sigma-combine a finite family of framed stages whose cell unions are disjoint across
different outer indices. -/
noncomputable def sigma
    (stage : ∀ c, PartitionedFramedRestartStage d (D c) m n p delta epsilon)
    (hcross : ∀ c c', c ≠ c' → Disjoint (stage c).cellUnion (stage c').cellUnion) :
    PartitionedFramedRestartStage d (Σ c, D c) m n p delta epsilon where
  cells := Finset.univ.sigma fun c ↦ (stage c).cells
  query := fun c ↦ (stage c.1).query c.2
  pastSupport := fun c ↦ (stage c.1).pastSupport c.2
  past := fun c ↦ (stage c.1).past c.2
  past_measurable := by
    intro c hc
    exact (stage c.1).past_measurable c.2 (by simpa using hc)
  fresh := by
    intro c hc
    exact (stage c.1).fresh c.2 (by simpa using hc)
  pairwise_cells := by
    intro c hc c' hc' hne
    rcases c with ⟨i, u⟩
    rcases c' with ⟨i', u'⟩
    by_cases hii : i = i'
    · subst i'
      apply (stage i).pairwise_cells
      · simpa using hc
      · simpa using hc'
      · intro huu
        apply hne
        cases huu
        rfl
    · change Disjoint ((stage i).cell u) ((stage i').cell u')
      rw [Set.disjoint_left]
      intro X hXu hXu'
      exact Set.disjoint_left.mp (hcross i i' hii)
        (Set.mem_iUnion_of_mem u <| Set.mem_iUnion_of_mem (by simpa using hc) hXu)
        (Set.mem_iUnion_of_mem u' <| Set.mem_iUnion_of_mem (by simpa using hc') hXu')
  restart_gt := by
    intro c hc
    exact (stage c.1).restart_gt c.2 (by simpa using hc)

/-- The combined history slice is exactly the union of the component history slices. -/
theorem cellUnion_sigma
    (stage : ∀ c, PartitionedFramedRestartStage d (D c) m n p delta epsilon)
    (hcross : ∀ c c', c ≠ c' → Disjoint (stage c).cellUnion (stage c').cellUnion) :
    (sigma D stage hcross).cellUnion = ⋃ c, (stage c).cellUnion := by
  ext X
  simp [sigma, PartitionedFramedRestartStage.cellUnion,
    PartitionedFramedRestartStage.cell]

end AdaptiveSiteExploration.PartitionedFramedRestartStage

end Percolation
