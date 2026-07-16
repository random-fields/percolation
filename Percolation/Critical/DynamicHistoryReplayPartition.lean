import Percolation.Critical.DynamicHistoryReplayStability

/-!
# Finite exact-history partition of a coarse replay

For a fixed coarse history, retain exactly the reachable terminal replay states whose source
history cells lie inside a semantic outer event.  Finite branching and exact-cell replay then
give a genuine finite, pairwise-disjoint partition without adding threshold-pattern data.
-/

namespace Percolation

open scoped unitInterval

namespace DynamicBlockHistoryReplay

variable {d m n : ℕ} {F : Set (Cubic d)} [LinearOrder F]

/-- Finite set of global replay states reachable at one fixed coarse history. -/
noncomputable def replayStateFinset
    (hd : 0 < d) (hmn : 2 * m ≤ n)
    (W : RootRadialSeedProfile d m n) (root : F)
    (p radialIncremented : I) (delta : ℝ)
    (incremented : RootExtensionThresholdPolicy d)
    (history : List (F × Bool)) : Finset (DynamicBlockHistoryState d F) :=
  (finite_range_replay hd hmn W root p radialIncremented delta incremented history).toFinset

@[simp]
theorem mem_replayStateFinset_iff
    (hd : 0 < d) (hmn : 2 * m ≤ n)
    (W : RootRadialSeedProfile d m n) (root : F)
    (p radialIncremented : I) (delta : ℝ)
    (incremented : RootExtensionThresholdPolicy d)
    (history : List (F × Bool)) (S : DynamicBlockHistoryState d F) :
    S ∈ replayStateFinset hd hmn W root p radialIncremented delta incremented history ↔
      ∃ X : CubicEdge d → ℝ,
        replay hd hmn W root p radialIncremented delta incremented X history = S := by
  simp [replayStateFinset]

/-- Reachable replay states whose unchanged terminal source-history cell is stable inside `A`
and has an actual representative in `A`. -/
abbrev StableReplayStateIndex
    (hd : 0 < d) (hmn : 2 * m ≤ n)
    (W : RootRadialSeedProfile d m n) (root : F)
    (p radialIncremented : I) (delta : ℝ)
    (incremented : RootExtensionThresholdPolicy d)
    (history : List (F × Bool)) (A : Set (CubicEdge d → ℝ)) :=
  {S : {S : DynamicBlockHistoryState d F //
      S ∈ replayStateFinset hd hmn W root p radialIncremented delta incremented history} //
    S.1.source.historyProfile.event ⊆ A ∧
      ∃ X ∈ A,
        replay hd hmn W root p radialIncremented delta incremented X history = S.1}

noncomputable instance stableReplayStateIndexFintype
    (hd : 0 < d) (hmn : 2 * m ≤ n)
    (W : RootRadialSeedProfile d m n) (root : F)
    (p radialIncremented : I) (delta : ℝ)
    (incremented : RootExtensionThresholdPolicy d)
    (history : List (F × Bool)) (A : Set (CubicEdge d → ℝ)) :
    Fintype (StableReplayStateIndex hd hmn W root p radialIncremented delta incremented
      history A) :=
  Fintype.ofFinite _

noncomputable instance stableReplayStateIndexDecidableEq
    (hd : 0 < d) (hmn : 2 * m ≤ n)
    (W : RootRadialSeedProfile d m n) (root : F)
    (p radialIncremented : I) (delta : ℝ)
    (incremented : RootExtensionThresholdPolicy d)
    (history : List (F × Bool)) (A : Set (CubicEdge d → ℝ)) :
    DecidableEq (StableReplayStateIndex hd hmn W root p radialIncremented delta incremented
      history A) :=
  Classical.decEq _

/-- Union of the stable terminal source-history cells. -/
def stableReplayHistory
    {hd : 0 < d} {hmn : 2 * m ≤ n}
    {W : RootRadialSeedProfile d m n} {root : F}
    {p radialIncremented : I} {delta : ℝ}
    {incremented : RootExtensionThresholdPolicy d}
    {history : List (F × Bool)} {A : Set (CubicEdge d → ℝ)} :
    Set (CubicEdge d → ℝ) :=
  ⋃ c : StableReplayStateIndex hd hmn W root p radialIncremented delta incremented
      history A,
    c.1.1.source.historyProfile.event

theorem stableReplayHistory_subset
    {hd : 0 < d} {hmn : 2 * m ≤ n}
    {W : RootRadialSeedProfile d m n} {root : F}
    {p radialIncremented : I} {delta : ℝ}
    {incremented : RootExtensionThresholdPolicy d}
    {history : List (F × Bool)} {A : Set (CubicEdge d → ℝ)} :
    stableReplayHistory (hd := hd) (hmn := hmn) (W := W) (root := root)
      (p := p) (radialIncremented := radialIncremented) (delta := delta)
      (incremented := incremented) (history := history) (A := A) ⊆ A := by
  intro X hX
  rw [stableReplayHistory, Set.mem_iUnion] at hX
  obtain ⟨c, hc⟩ := hX
  exact c.2.1 hc

/-- Every point of `A` is covered when its own replay cell contains it and that cell is stable
inside `A`. -/
theorem subset_stableReplayHistory
    (hd : 0 < d) (hmn : 2 * m ≤ n)
    (W : RootRadialSeedProfile d m n) (root : F)
    (p radialIncremented : I) (delta : ℝ)
    (incremented : RootExtensionThresholdPolicy d)
    (history : List (F × Bool)) (A : Set (CubicEdge d → ℝ))
    (hself : ∀ X ∈ A,
      X ∈ (replay hd hmn W root p radialIncremented delta incremented X history
        ).source.historyProfile.event)
    (hstable : ∀ X ∈ A,
      (replay hd hmn W root p radialIncremented delta incremented X history
        ).source.historyProfile.event ⊆ A) :
    A ⊆ stableReplayHistory (hd := hd) (hmn := hmn) (W := W) (root := root)
      (p := p) (radialIncremented := radialIncremented) (delta := delta)
      (incremented := incremented) (history := history) (A := A) := by
  intro X hXA
  let S := replay hd hmn W root p radialIncremented delta incremented X history
  have hSmem : S ∈ replayStateFinset hd hmn W root p radialIncremented delta incremented
      history := by
    rw [mem_replayStateFinset_iff]
    exact ⟨X, rfl⟩
  let c : StableReplayStateIndex hd hmn W root p radialIncremented delta incremented
      history A :=
    ⟨⟨S, hSmem⟩, hstable X hXA, X, hXA, rfl⟩
  rw [stableReplayHistory, Set.mem_iUnion]
  exact ⟨c, hself X hXA⟩

theorem stableReplayHistory_eq
    (hd : 0 < d) (hmn : 2 * m ≤ n)
    (W : RootRadialSeedProfile d m n) (root : F)
    (p radialIncremented : I) (delta : ℝ)
    (incremented : RootExtensionThresholdPolicy d)
    (history : List (F × Bool)) (A : Set (CubicEdge d → ℝ))
    (hself : ∀ X ∈ A,
      X ∈ (replay hd hmn W root p radialIncremented delta incremented X history
        ).source.historyProfile.event)
    (hstable : ∀ X ∈ A,
      (replay hd hmn W root p radialIncremented delta incremented X history
        ).source.historyProfile.event ⊆ A) :
    stableReplayHistory (hd := hd) (hmn := hmn) (W := W) (root := root)
      (p := p) (radialIncremented := radialIncremented) (delta := delta)
      (incremented := incremented) (history := history) (A := A) = A := by
  apply Set.Subset.antisymm stableReplayHistory_subset
  exact subset_stableReplayHistory hd hmn W root p radialIncremented delta incremented
    history A hself hstable

/-- Exact replay on terminal source-history cells makes distinct reachable stable cells
pairwise disjoint. -/
theorem pairwiseDisjoint_stableReplayHistory
    (hd : 0 < d) (hmn : 2 * m ≤ n)
    (W : RootRadialSeedProfile d m n) (root : F)
    (p radialIncremented : I) (delta : ℝ)
    (incremented : RootExtensionThresholdPolicy d)
    (history : List (F × Bool)) (A : Set (CubicEdge d → ℝ))
    (hreplay : ∀ X ∈ A, ∀ Y,
      Y ∈ (replay hd hmn W root p radialIncremented delta incremented X history
        ).source.historyProfile.event →
      replay hd hmn W root p radialIncremented delta incremented Y history =
        replay hd hmn W root p radialIncremented delta incremented X history) :
    ∀ c c' : StableReplayStateIndex hd hmn W root p radialIncremented delta incremented
        history A,
      c ≠ c' → Disjoint c.1.1.source.historyProfile.event
        c'.1.1.source.historyProfile.event := by
  intro c c' hne
  rw [Set.disjoint_left]
  intro Z hZc hZc'
  obtain ⟨X, hXA, hXstate⟩ := c.2.2
  obtain ⟨Y, hYA, hYstate⟩ := c'.2.2
  have hZX :
      replay hd hmn W root p radialIncremented delta incremented Z history = c.1.1 := by
    rw [← hXstate]
    exact hreplay X hXA Z (by simpa [hXstate] using hZc)
  have hZY :
      replay hd hmn W root p radialIncremented delta incremented Z history = c'.1.1 := by
    rw [← hYstate]
    exact hreplay Y hYA Z (by simpa [hYstate] using hZc')
  exact hne (Subtype.ext (Subtype.ext (hZX.symm.trans hZY)))

end DynamicBlockHistoryReplay

end Percolation
