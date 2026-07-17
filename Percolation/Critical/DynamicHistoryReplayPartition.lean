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

/-! ### Runtime-prefix-compatible outer replay cells

The earlier `StableReplayStateIndex` is useful only when the complete source-history cell is
already contained in the outer event.  A sequential restart prefix does not have that property:
before the query is run, its source cell cannot determine the outcomes of future restart slots.
For the actual stage induction we therefore retain every replay state represented in `A` and
use `A ∩ sourceHistory` as its cell.  The following finite partition needs exact replay and
self-membership, but deliberately has no false pre-query stability premise. -/

/-- Reachable replay states having at least one representative in the current outer event. -/
abbrev RepresentedReplayStateIndex
    (hd : 0 < d) (hmn : 2 * m ≤ n)
    (W : RootRadialSeedProfile d m n) (root : F)
    (p radialIncremented : I) (delta : ℝ)
    (incremented : RootExtensionThresholdPolicy d)
    (history : List (F × Bool)) (A : Set (CubicEdge d → ℝ)) :=
  {S : {S : DynamicBlockHistoryState d F //
      S ∈ replayStateFinset hd hmn W root p radialIncremented delta incremented history} //
    ∃ X ∈ A,
      replay hd hmn W root p radialIncremented delta incremented X history = S.1}

noncomputable instance representedReplayStateIndexFintype
    (hd : 0 < d) (hmn : 2 * m ≤ n)
    (W : RootRadialSeedProfile d m n) (root : F)
    (p radialIncremented : I) (delta : ℝ)
    (incremented : RootExtensionThresholdPolicy d)
    (history : List (F × Bool)) (A : Set (CubicEdge d → ℝ)) :
    Fintype (RepresentedReplayStateIndex hd hmn W root p radialIncremented delta
      incremented history A) :=
  Fintype.ofFinite _

noncomputable instance representedReplayStateIndexDecidableEq
    (hd : 0 < d) (hmn : 2 * m ≤ n)
    (W : RootRadialSeedProfile d m n) (root : F)
    (p radialIncremented : I) (delta : ℝ)
    (incremented : RootExtensionThresholdPolicy d)
    (history : List (F × Bool)) (A : Set (CubicEdge d → ℝ)) :
    DecidableEq (RepresentedReplayStateIndex hd hmn W root p radialIncremented delta
      incremented history A) :=
  Classical.decEq _

/-- The correct outer cell for a represented replay state: retain the semantic past `A` while
freezing the incoming source state. -/
def representedReplayCell
    {hd : 0 < d} {hmn : 2 * m ≤ n}
    {W : RootRadialSeedProfile d m n} {root : F}
    {p radialIncremented : I} {delta : ℝ}
    {incremented : RootExtensionThresholdPolicy d}
    {history : List (F × Bool)} {A : Set (CubicEdge d → ℝ)}
    (c : RepresentedReplayStateIndex hd hmn W root p radialIncremented delta
      incremented history A) : Set (CubicEdge d → ℝ) :=
  A ∩ c.1.1.source.historyProfile.event

/-- The represented replay cells cover exactly `A`; no pre-query stability assumption is
needed. -/
theorem iUnion_representedReplayCell_eq
    (hd : 0 < d) (hmn : 2 * m ≤ n)
    (W : RootRadialSeedProfile d m n) (root : F)
    (p radialIncremented : I) (delta : ℝ)
    (incremented : RootExtensionThresholdPolicy d)
    (history : List (F × Bool)) (A : Set (CubicEdge d → ℝ))
    (hself : ∀ X ∈ A,
      X ∈ (replay hd hmn W root p radialIncremented delta incremented X history
        ).source.historyProfile.event) :
    (⋃ c : RepresentedReplayStateIndex hd hmn W root p radialIncremented delta
        incremented history A, representedReplayCell c) = A := by
  apply Set.Subset.antisymm
  · intro X hX
    rw [Set.mem_iUnion] at hX
    obtain ⟨c, hXA, _hXcell⟩ := hX
    exact hXA
  · intro X hXA
    let S := replay hd hmn W root p radialIncremented delta incremented X history
    have hSmem : S ∈ replayStateFinset hd hmn W root p radialIncremented delta
        incremented history := by
      rw [mem_replayStateFinset_iff]
      exact ⟨X, rfl⟩
    let c : RepresentedReplayStateIndex hd hmn W root p radialIncremented delta
        incremented history A := ⟨⟨S, hSmem⟩, X, hXA, rfl⟩
    rw [Set.mem_iUnion]
    exact ⟨c, hXA, by simpa [S] using hself X hXA⟩

/-- Exact replay makes distinct represented outer cells disjoint, even though each cell keeps
the explicit intersection with `A`. -/
theorem pairwiseDisjoint_representedReplayCell
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
    Set.PairwiseDisjoint
      (Set.univ : Set (RepresentedReplayStateIndex hd hmn W root p radialIncremented delta
        incremented history A)) representedReplayCell := by
  intro c _hc c' _hc' hne
  change Disjoint (representedReplayCell c) (representedReplayCell c')
  rw [Set.disjoint_left]
  intro Z hZc hZc'
  obtain ⟨X, hXA, hXstate⟩ := c.2
  obtain ⟨Y, hYA, hYstate⟩ := c'.2
  have hZX : replay hd hmn W root p radialIncremented delta incremented Z history =
      c.1.1 := by
    rw [← hXstate]
    exact hreplay X hXA Z (by simpa [representedReplayCell, hXstate] using hZc.2)
  have hZY : replay hd hmn W root p radialIncremented delta incremented Z history =
      c'.1.1 := by
    rw [← hYstate]
    exact hreplay Y hYA Z (by simpa [representedReplayCell, hYstate] using hZc'.2)
  exact hne (Subtype.ext (Subtype.ext (hZX.symm.trans hZY)))

end DynamicBlockHistoryReplay

end Percolation
