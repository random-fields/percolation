import Percolation.Critical.DynamicLaterSiteRuntimeHistory
import Percolation.Critical.DynamicFramedStateStage

/-!
# Finite accumulated-history partitions for a non-root site

For fixed inlet data and a finite direction schedule, every runtime prefix has finite range.  Restricting
that range to cells which are stable inside an outer event gives a finite, pairwise-disjoint
partition of the event.  The final constructor turns such a partition directly into the framed
restart stage used by `InitializedFinitePartitionedRestartProgram`.
-/

namespace Percolation

open scoped unitInterval

namespace LaterSiteRuntime

/-- Runtime after the first `k` entries of an arbitrary non-root direction schedule. -/
noncomputable def prefixRuntime
    {d m n : ℕ} (hmn : 2 * m ≤ n)
    (source : SourceFiniteEdgeRevealState d) (inletCenter : Cubic d)
    (incoming : CubicDirection d) (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (directions : List (CubicDirection d))
    (k : ℕ) (X : CubicEdge d → ℝ) : LaterSiteRuntime d :=
  runFrom hmn inletCenter incoming firstFlip secondFlip p delta incremented X
    (initial source inletCenter) 0 (directions.take k)

/-- The literal success event of one fixed non-root runtime prefix.  This named event keeps
downstream replay proofs from normalizing the entire executable runtime. -/
noncomputable def prefixQuerySuccessEvent
    {d m n : ℕ} (hmn : 2 * m ≤ n)
    (source : SourceFiniteEdgeRevealState d) (inletCenter : Cubic d)
    (incoming : CubicDirection d) (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (directions : List (CubicDirection d)) (j : ℕ) (a : CubicDirection d) :
    Set (CubicEdge d → ℝ) :=
  {X | X ∈ ((prefixRuntime hmn source inletCenter incoming firstFlip secondFlip
    p delta incremented directions j X).restartQuery inletCenter incoming firstFlip
      secondFlip a j).successEvent m n p delta}

/-- A fixed outer history together with the literal success of one runtime prefix. -/
noncomputable def prefixSemanticSuccessEvent
    {d m n : ℕ} (hmn : 2 * m ≤ n)
    (source : SourceFiniteEdgeRevealState d) (inletCenter : Cubic d)
    (incoming : CubicDirection d) (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (directions : List (CubicDirection d)) (j : ℕ) (a : CubicDirection d)
    (A : Set (CubicEdge d → ℝ)) : Set (CubicEdge d → ℝ) :=
  {X | X ∈ A ∧ X ∈ prefixQuerySuccessEvent hmn source inletCenter incoming firstFlip
    secondFlip p delta incremented directions j a}

/-- Every fixed non-root prefix has finite total-runtime range. -/
theorem finite_range_prefixRuntime
    {d m n : ℕ} (hmn : 2 * m ≤ n)
    (source : SourceFiniteEdgeRevealState d) (inletCenter : Cubic d)
    (incoming : CubicDirection d) (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (directions : List (CubicDirection d))
    (k : ℕ) :
    (Set.range fun X ↦ prefixRuntime hmn source inletCenter incoming
      firstFlip secondFlip p delta incremented directions k X).Finite := by
  let initialRuntime : (CubicEdge d → ℝ) → LaterSiteRuntime d :=
    fun _ ↦ initial source inletCenter
  have hinitial : (Set.range initialRuntime).Finite := by
    have hsubset : Set.range initialRuntime ⊆ {initial source inletCenter} := by
      rintro R ⟨X, rfl⟩
      simp [initialRuntime]
    exact Set.finite_singleton _ |>.subset hsubset
  simpa [prefixRuntime, initialRuntime] using
    finite_range_runFrom hmn inletCenter incoming firstFlip secondFlip
      p delta incremented initialRuntime 0
      (directions.take k) hinitial

/-- Finite set of total runtimes reachable after a fixed non-root prefix. -/
noncomputable def prefixRuntimeFinset
    {d m n : ℕ} (hmn : 2 * m ≤ n)
    (source : SourceFiniteEdgeRevealState d) (inletCenter : Cubic d)
    (incoming : CubicDirection d) (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (directions : List (CubicDirection d))
    (k : ℕ) : Finset (LaterSiteRuntime d) :=
  (finite_range_prefixRuntime hmn source inletCenter incoming firstFlip secondFlip
    p delta incremented directions k).toFinset

@[simp]
theorem mem_prefixRuntimeFinset_iff
    {d m n : ℕ} (hmn : 2 * m ≤ n)
    (source : SourceFiniteEdgeRevealState d) (inletCenter : Cubic d)
    (incoming : CubicDirection d) (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (directions : List (CubicDirection d))
    (k : ℕ) (R : LaterSiteRuntime d) :
    R ∈ prefixRuntimeFinset hmn source inletCenter incoming firstFlip secondFlip
        p delta incremented directions k ↔
      ∃ X : CubicEdge d → ℝ,
        prefixRuntime hmn source inletCenter incoming firstFlip secondFlip
          p delta incremented directions k X = R := by
  simp [prefixRuntimeFinset]

/-- Reachable runtime cells whose accumulated source-history event stays inside `A` and has a
witness in `A`.  Both conditions are semantic: no extra threshold-pattern refinement is hidden
in the index. -/
abbrev StablePrefixRuntimeIndex
    {d m n : ℕ} (hmn : 2 * m ≤ n)
    (source : SourceFiniteEdgeRevealState d) (inletCenter : Cubic d)
    (incoming : CubicDirection d) (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (directions : List (CubicDirection d))
    (k : ℕ) (A : Set (CubicEdge d → ℝ)) :=
  {R : {R : LaterSiteRuntime d //
      R ∈ prefixRuntimeFinset hmn source inletCenter incoming firstFlip secondFlip
        p delta incremented directions k} //
    R.1.source.historyProfile.event ⊆ A ∧
      ∃ X ∈ A,
        prefixRuntime hmn source inletCenter incoming firstFlip secondFlip
          p delta incremented directions k X = R.1}

noncomputable instance stablePrefixRuntimeIndexFintype
    {d m n : ℕ} (hmn : 2 * m ≤ n)
    (source : SourceFiniteEdgeRevealState d) (inletCenter : Cubic d)
    (incoming : CubicDirection d) (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (directions : List (CubicDirection d))
    (k : ℕ) (A : Set (CubicEdge d → ℝ)) :
    Fintype (StablePrefixRuntimeIndex hmn source inletCenter incoming firstFlip secondFlip
      p delta incremented directions k A) :=
  Fintype.ofFinite _

noncomputable instance stablePrefixRuntimeIndexDecidableEq
    {d m n : ℕ} (hmn : 2 * m ≤ n)
    (source : SourceFiniteEdgeRevealState d) (inletCenter : Cubic d)
    (incoming : CubicDirection d) (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (directions : List (CubicDirection d))
    (k : ℕ) (A : Set (CubicEdge d → ℝ)) :
    DecidableEq (StablePrefixRuntimeIndex hmn source inletCenter incoming firstFlip secondFlip
      p delta incremented directions k A) :=
  Classical.decEq _

/-- A represented outer cell supplies a genuine prefix-runtime classifier; no geometric default
is needed for reachable histories. -/
theorem nonempty_stablePrefixRuntimeIndex
    {d m n : ℕ} (hmn : 2 * m ≤ n)
    (source : SourceFiniteEdgeRevealState d) (inletCenter : Cubic d)
    (incoming : CubicDirection d) (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (directions : List (CubicDirection d))
    (k : ℕ) (A : Set (CubicEdge d → ℝ))
    (X : CubicEdge d → ℝ) (hXA : X ∈ A)
    (hstable : (prefixRuntime hmn source inletCenter incoming firstFlip secondFlip
      p delta incremented directions k X).source.historyProfile.event ⊆ A) :
    Nonempty (StablePrefixRuntimeIndex hmn source inletCenter incoming firstFlip secondFlip
      p delta incremented directions k A) := by
  let R := prefixRuntime hmn source inletCenter incoming firstFlip secondFlip
    p delta incremented directions k X
  have hRmem : R ∈ prefixRuntimeFinset hmn source inletCenter incoming firstFlip secondFlip
      p delta incremented directions k := by
    rw [mem_prefixRuntimeFinset_iff]
    exact ⟨X, rfl⟩
  exact ⟨⟨⟨R, hRmem⟩, hstable, X, hXA, rfl⟩⟩

/-- Exact union of the stable accumulated-history cells. -/
def stablePrefixHistory
    {d m n : ℕ} {hmn : 2 * m ≤ n}
    {source : SourceFiniteEdgeRevealState d} {inletCenter : Cubic d}
    {incoming : CubicDirection d} {firstFlip secondFlip : Fin d → Bool}
    {p : I} {delta : ℝ} {incremented : RootExtensionThresholdPolicy d}
    {directions : List (CubicDirection d)}
    {k : ℕ} {A : Set (CubicEdge d → ℝ)} : Set (CubicEdge d → ℝ) :=
  ⋃ c : StablePrefixRuntimeIndex hmn source inletCenter incoming firstFlip secondFlip
      p delta incremented directions k A,
    c.1.1.source.historyProfile.event

theorem stablePrefixHistory_subset
    {d m n : ℕ} {hmn : 2 * m ≤ n}
    {source : SourceFiniteEdgeRevealState d} {inletCenter : Cubic d}
    {incoming : CubicDirection d} {firstFlip secondFlip : Fin d → Bool}
    {p : I} {delta : ℝ} {incremented : RootExtensionThresholdPolicy d}
    {directions : List (CubicDirection d)}
    {k : ℕ} {A : Set (CubicEdge d → ℝ)} :
    stablePrefixHistory (hmn := hmn) (source := source) (inletCenter := inletCenter)
      (incoming := incoming) (firstFlip := firstFlip) (secondFlip := secondFlip)
      (p := p) (delta := delta) (incremented := incremented) (directions := directions)
      (k := k) (A := A) ⊆ A := by
  intro X hX
  rw [stablePrefixHistory, Set.mem_iUnion] at hX
  obtain ⟨c, hc⟩ := hX
  exact c.2.1 hc

/-- If every realization in `A` has a terminal cell contained in `A`, the stable cells cover
`A` on the common nonnegative coupling support. -/
theorem subset_stablePrefixHistory
    {d m n : ℕ} (hmn : 2 * m ≤ n)
    (source : SourceFiniteEdgeRevealState d) (inletCenter : Cubic d)
    (incoming : CubicDirection d) (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (directions : List (CubicDirection d))
    (k : ℕ) (A : Set (CubicEdge d → ℝ))
    (hAcurrent : A ⊆ source.historyProfile.event)
    (hAnonnegative : A ⊆ SourceFiniteEdgeRevealState.nonnegativeCouplingEvent)
    (hstable : ∀ X ∈ A,
      (prefixRuntime hmn source inletCenter incoming firstFlip secondFlip
        p delta incremented directions k X).source.historyProfile.event ⊆ A) :
    A ⊆ stablePrefixHistory (hmn := hmn) (source := source)
      (inletCenter := inletCenter) (incoming := incoming) (firstFlip := firstFlip)
      (secondFlip := secondFlip) (p := p) (delta := delta)
      (incremented := incremented) (directions := directions) (k := k) (A := A) := by
  intro X hX
  let R := prefixRuntime hmn source inletCenter incoming firstFlip secondFlip
    p delta incremented directions k X
  have hRmem : R ∈ prefixRuntimeFinset hmn source inletCenter incoming firstFlip secondFlip
      p delta incremented directions k := by
    rw [mem_prefixRuntimeFinset_iff]
    exact ⟨X, rfl⟩
  let c : StablePrefixRuntimeIndex hmn source inletCenter incoming firstFlip secondFlip
      p delta incremented directions k A :=
    ⟨⟨R, hRmem⟩, hstable X hX, X, hX, rfl⟩
  rw [stablePrefixHistory, Set.mem_iUnion]
  refine ⟨c, ?_⟩
  exact mem_runFrom_historyProfile hmn inletCenter incoming firstFlip secondFlip
    p delta incremented X (initial source inletCenter) 0
      (directions.take k)
      (hAnonnegative hX) (by simpa [initial] using hAcurrent hX)

/-- The stable prefix-history union equals its semantic outer event. -/
theorem stablePrefixHistory_eq
    {d m n : ℕ} (hmn : 2 * m ≤ n)
    (source : SourceFiniteEdgeRevealState d) (inletCenter : Cubic d)
    (incoming : CubicDirection d) (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (directions : List (CubicDirection d))
    (k : ℕ) (A : Set (CubicEdge d → ℝ))
    (hAcurrent : A ⊆ source.historyProfile.event)
    (hAnonnegative : A ⊆ SourceFiniteEdgeRevealState.nonnegativeCouplingEvent)
    (hstable : ∀ X ∈ A,
      (prefixRuntime hmn source inletCenter incoming firstFlip secondFlip
        p delta incremented directions k X).source.historyProfile.event ⊆ A) :
    stablePrefixHistory (hmn := hmn) (source := source)
      (inletCenter := inletCenter) (incoming := incoming) (firstFlip := firstFlip)
      (secondFlip := secondFlip) (p := p) (delta := delta)
      (incremented := incremented) (directions := directions) (k := k) (A := A) = A := by
  apply Set.Subset.antisymm stablePrefixHistory_subset
  exact subset_stablePrefixHistory hmn source inletCenter incoming firstFlip secondFlip
    p delta incremented directions k A hAcurrent hAnonnegative hstable

/-- Distinct stable prefix runtimes have disjoint accumulated-history cells.  The proof uses
exact-history replay twice: a realization in both cells would reproduce both runtimes. -/
theorem pairwiseDisjoint_stablePrefixRuntimeHistory
    {d m n : ℕ} (hmn : 2 * m ≤ n)
    (source : SourceFiniteEdgeRevealState d) (inletCenter : Cubic d)
    (incoming : CubicDirection d) (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (directions : List (CubicDirection d))
    (hmono : ∀ S a e, S.lower e ≤ incremented S a e)
    (k : ℕ) (A : Set (CubicEdge d → ℝ))
    (hAcurrent : A ⊆ source.historyProfile.event)
    (hAnonnegative : A ⊆ SourceFiniteEdgeRevealState.nonnegativeCouplingEvent)
    (hadds : ∀ X ∈ A, ∀ j
      (hj : j < (directions.take k).length) e,
      let Rj := runFrom hmn inletCenter incoming firstFlip secondFlip
        p delta incremented X (LaterSiteRuntime.initial source inletCenter) 0
          ((directions.take k).take j)
      let a := (directions.take k)[j]
      (incremented Rj.source a e : ℝ) = (Rj.source.lower e : ℝ) + delta)
    (hfresh : ∀ X ∈ A, ∀ j
      (hj : j < (directions.take k).length),
      let Rj := runFrom hmn inletCenter incoming firstFlip secondFlip
        p delta incremented X (LaterSiteRuntime.initial source inletCenter) 0
          ((directions.take k).take j)
      let a := (directions.take k)[j]
      let center := Rj.slotCenterFor inletCenter a j
      let flip := Rj.slotTransverseFlip incoming firstFlip secondFlip a j
      let F := cubicRestartFrameIso center a flip
      Disjoint (cubicEdgeEndpointVertices (Rj.source.referenceExploredEdges F))
        (cubicEdgeEndpointVertices (seededBoundaryTargetSupport d a.1 m n))) :
    ∀ c c' : StablePrefixRuntimeIndex hmn source inletCenter incoming firstFlip secondFlip
        p delta incremented directions k A,
      c ≠ c' → Disjoint c.1.1.source.historyProfile.event
        c'.1.1.source.historyProfile.event := by
  intro c c' hne
  rw [Set.disjoint_left]
  intro Z hZc hZc'
  obtain ⟨X, hXA, hXruntime⟩ := c.2.2
  obtain ⟨Y, hYA, hYruntime⟩ := c'.2.2
  have hfreshX : ∀ j
      (hj : j < (directions.take k).length),
      let Rj := runFrom hmn inletCenter incoming firstFlip secondFlip
        p delta incremented X (initial source inletCenter) 0
          ((directions.take k).take j)
      let a := (directions.take k)[j]
      let center := Rj.slotCenterFor inletCenter a (0 + j)
      let flip := Rj.slotTransverseFlip incoming firstFlip secondFlip a (0 + j)
      let F := cubicRestartFrameIso center a flip
      Disjoint (cubicEdgeEndpointVertices (Rj.source.referenceExploredEdges F))
        (cubicEdgeEndpointVertices (seededBoundaryTargetSupport d a.1 m n)) := by
    intro j hj
    simpa using hfresh X hXA j hj
  have hfreshY : ∀ j
      (hj : j < (directions.take k).length),
      let Rj := runFrom hmn inletCenter incoming firstFlip secondFlip
        p delta incremented Y (initial source inletCenter) 0
          ((directions.take k).take j)
      let a := (directions.take k)[j]
      let center := Rj.slotCenterFor inletCenter a (0 + j)
      let flip := Rj.slotTransverseFlip incoming firstFlip secondFlip a (0 + j)
      let F := cubicRestartFrameIso center a flip
      Disjoint (cubicEdgeEndpointVertices (Rj.source.referenceExploredEdges F))
        (cubicEdgeEndpointVertices (seededBoundaryTargetSupport d a.1 m n)) := by
    intro j hj
    simpa using hfresh Y hYA j hj
  have hZcX : Z ∈
      (prefixRuntime hmn source inletCenter incoming firstFlip secondFlip
        p delta incremented directions k X).source.historyProfile.event := by
    rw [hXruntime]
    exact hZc
  have hZcY : Z ∈
      (prefixRuntime hmn source inletCenter incoming firstFlip secondFlip
        p delta incremented directions k Y).source.historyProfile.event := by
    rw [hYruntime]
    exact hZc'
  have hZX := runFrom_eq_of_mem_historyProfile hmn inletCenter incoming
    firstFlip secondFlip p delta incremented hmono X Z
      (initial source inletCenter) 0 (directions.take k)
      (hadds X hXA) hfreshX
      (by simpa [initial] using hAcurrent hXA) (hAnonnegative hXA) (by
        simpa [prefixRuntime] using hZcX)
  have hZY := runFrom_eq_of_mem_historyProfile hmn inletCenter incoming
    firstFlip secondFlip p delta incremented hmono Y Z
      (initial source inletCenter) 0 (directions.take k)
      (hadds Y hYA) hfreshY
      (by simpa [initial] using hAcurrent hYA) (hAnonnegative hYA) (by
        simpa [prefixRuntime] using hZcY)
  have hcc' : c.1.1 = c'.1.1 := by
    rw [← hXruntime, ← hYruntime]
    exact hZX.symm.trans hZY
  exact hne (Subtype.ext (Subtype.ext hcc'))

/-- On the represented outer history, the canonical finite classifier selects the literal
runtime generated by the configuration.  This is the semantic bridge between the finite
interval-profile partition and the executable non-root schedule. -/
theorem realizedStablePrefixRuntime_eq_prefixRuntime
    {d m n : ℕ} (hmn : 2 * m ≤ n)
    (source : SourceFiniteEdgeRevealState d) (inletCenter : Cubic d)
    (incoming : CubicDirection d) (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (hmono : ∀ S a e, S.lower e ≤ incremented S a e)
    (directions : List (CubicDirection d))
    (k : ℕ) (A : Set (CubicEdge d → ℝ))
    (hAcurrent : A ⊆ source.historyProfile.event)
    (hAnonnegative : A ⊆ SourceFiniteEdgeRevealState.nonnegativeCouplingEvent)
    (hstable : ∀ X ∈ A,
      (prefixRuntime hmn source inletCenter incoming firstFlip secondFlip
        p delta incremented directions k X).source.historyProfile.event ⊆ A)
    (hadds : ∀ X ∈ A, ∀ j
      (hj : j < (directions.take k).length) e,
      let Rj := runFrom hmn inletCenter incoming firstFlip secondFlip
        p delta incremented X (LaterSiteRuntime.initial source inletCenter) 0
          ((directions.take k).take j)
      let a := (directions.take k)[j]
      (incremented Rj.source a e : ℝ) = (Rj.source.lower e : ℝ) + delta)
    (hfresh : ∀ X ∈ A, ∀ j
      (hj : j < (directions.take k).length),
      let Rj := runFrom hmn inletCenter incoming firstFlip secondFlip
        p delta incremented X (LaterSiteRuntime.initial source inletCenter) 0
          ((directions.take k).take j)
      let a := (directions.take k)[j]
      let center := Rj.slotCenterFor inletCenter a j
      let flip := Rj.slotTransverseFlip incoming firstFlip secondFlip a j
      let F := cubicRestartFrameIso center a flip
      Disjoint (cubicEdgeEndpointVertices (Rj.source.referenceExploredEdges F))
        (cubicEdgeEndpointVertices (seededBoundaryTargetSupport d a.1 m n)))
    (hnonempty : Nonempty (StablePrefixRuntimeIndex hmn source inletCenter incoming
      firstFlip secondFlip p delta incremented directions k A))
    (X : CubicEdge d → ℝ) (hXA : X ∈ A) :
    let C := StablePrefixRuntimeIndex hmn source inletCenter incoming firstFlip secondFlip
      p delta incremented directions k A
    let profile : C → FiniteRevealIntervalProfile (CubicEdge d) :=
      fun c ↦ c.1.1.source.historyProfile
    (realizedIntervalProfileCell (Classical.choice hnonempty) profile X).1.1 =
      prefixRuntime hmn source inletCenter incoming firstFlip secondFlip
        p delta incremented directions k X := by
  let C := StablePrefixRuntimeIndex hmn source inletCenter incoming firstFlip secondFlip
    p delta incremented directions k A
  let profile : C → FiniteRevealIntervalProfile (CubicEdge d) :=
    fun c ↦ c.1.1.source.historyProfile
  let R := prefixRuntime hmn source inletCenter incoming firstFlip secondFlip
    p delta incremented directions k X
  have hRmem : R ∈ prefixRuntimeFinset hmn source inletCenter incoming firstFlip secondFlip
      p delta incremented directions k := by
    rw [mem_prefixRuntimeFinset_iff]
    exact ⟨X, rfl⟩
  let cX : C := ⟨⟨R, hRmem⟩, hstable X hXA, X, hXA, rfl⟩
  have hXprofile : X ∈ (profile cX).event := by
    exact mem_runFrom_historyProfile hmn inletCenter incoming firstFlip secondFlip
      p delta incremented X (initial source inletCenter) 0 (directions.take k)
      (hAnonnegative hXA) (by simpa [initial] using hAcurrent hXA)
  have hchosen : realizedIntervalProfileCell (Classical.choice hnonempty) profile X = cX := by
    apply realizedIntervalProfileCell_eq_of_mem
      (default := Classical.choice hnonempty) (profile := profile)
    · intro c c' hne
      exact pairwiseDisjoint_stablePrefixRuntimeHistory hmn source inletCenter incoming
        firstFlip secondFlip p delta incremented directions hmono k A hAcurrent
          hAnonnegative hadds hfresh c c' hne
    · exact hXprofile
  have hprojected := congrArg (fun c : C ↦ c.1.1) hchosen
  simpa [C, profile, cX, R] using hprojected

end LaterSiteRuntime

namespace AdaptiveSiteExploration

open LaterSiteRuntime

/-- Construct the `j`-th non-root restart stage from the stable finite runtime partition of its
literal prefix.  The geometric caller supplies only endpoint freshness and the uniform Lemma
7.17 estimate for each concrete cell. -/
noncomputable def partitionedLaterSitePrefixStage
    {d m n : ℕ} (hmn : 2 * m ≤ n)
    (source : SourceFiniteEdgeRevealState d) (inletCenter : Cubic d)
    (incoming : CubicDirection d) (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta epsilon : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (hmono : ∀ S a e, S.lower e ≤ incremented S a e)
    (directions : List (CubicDirection d))
    (j : ℕ) (hj : j < directions.length)
    (A : Set (CubicEdge d → ℝ))
    (hnonempty : Nonempty (StablePrefixRuntimeIndex hmn source inletCenter incoming
      firstFlip secondFlip p delta incremented directions j A))
    (hAcurrent : A ⊆ source.historyProfile.event)
    (hAnonnegative : A ⊆ SourceFiniteEdgeRevealState.nonnegativeCouplingEvent)
    (hstable : ∀ X ∈ A,
      (prefixRuntime hmn source inletCenter incoming firstFlip secondFlip
        p delta incremented directions j X).source.historyProfile.event ⊆ A)
    (hadds : ∀ X ∈ A, ∀ l
      (hl : l < (directions.take j).length) e,
      let Rl := runFrom hmn inletCenter incoming firstFlip secondFlip
        p delta incremented X (LaterSiteRuntime.initial source inletCenter) 0
          ((directions.take j).take l)
      let a := (directions.take j)[l]
      (incremented Rl.source a e : ℝ) = (Rl.source.lower e : ℝ) + delta)
    (hfreshPrefix : ∀ X ∈ A, ∀ l
      (hl : l < (directions.take j).length),
      let Rl := runFrom hmn inletCenter incoming firstFlip secondFlip
        p delta incremented X (LaterSiteRuntime.initial source inletCenter) 0
          ((directions.take j).take l)
      let a := (directions.take j)[l]
      let center := Rl.slotCenterFor inletCenter a l
      let flip := Rl.slotTransverseFlip incoming firstFlip secondFlip a l
      let F := cubicRestartFrameIso center a flip
      Disjoint (cubicEdgeEndpointVertices (Rl.source.referenceExploredEdges F))
        (cubicEdgeEndpointVertices (seededBoundaryTargetSupport d a.1 m n)))
    (hTargetFresh : ∀ c : StablePrefixRuntimeIndex hmn source inletCenter incoming
        firstFlip secondFlip p delta incremented directions j A,
      let R := c.1.1
      let a := directions[j]
      let center := R.slotCenterFor inletCenter a j
      let flip := R.slotTransverseFlip incoming firstFlip secondFlip a j
      let F := cubicRestartFrameIso center a flip
      Disjoint (cubicEdgeEndpointVertices (R.source.referenceExploredEdges F))
        (cubicEdgeEndpointVertices (seededBoundaryTargetSupport d a.1 m n)))
    (hrestart : ∀ c : StablePrefixRuntimeIndex hmn source inletCenter incoming
        firstFlip secondFlip p delta incremented directions j A,
      let R := c.1.1
      let a := directions[j]
      let Q := R.restartQuery inletCenter incoming firstFlip secondFlip a j
      (1 - epsilon) * (couplingMeasure (CubicEdge d)).real
          (Q.boundaryHistoryEvent n) <
        (couplingMeasure (CubicEdge d)).real
          (Q.successEvent m n p delta ∩ Q.boundaryHistoryEvent n)) :
    Percolation.AdaptiveSiteExploration.PartitionedFramedRestartStage d
      (StablePrefixRuntimeIndex hmn source inletCenter incoming firstFlip secondFlip
        p delta incremented directions j A) m n p delta epsilon := by
  let C := StablePrefixRuntimeIndex hmn source inletCenter incoming firstFlip secondFlip
    p delta incremented directions j A
  let profile : C → FiniteRevealIntervalProfile (CubicEdge d) :=
    fun c ↦ c.1.1.source.historyProfile
  let realizedCell : (CubicEdge d → ℝ) → C :=
    realizedIntervalProfileCell (Classical.choice hnonempty) profile
  let a := directions[j]
  apply Percolation.AdaptiveSiteExploration.PartitionedFramedRestartStage.ofCanonicalSourceEdgeStateRealizationOfTargetEndpointFresh
    A realizedCell
      (fun c ↦ c.1.1.slotCenterFor inletCenter a j) (fun _ ↦ a)
      (fun c ↦ c.1.1.slotTransverseFlip incoming firstFlip secondFlip a j)
      (fun c ↦ c.1.1.source)
  · intro c
    simpa [a] using hTargetFresh c
  · intro c
    apply intervalProfile_event_eq_exactRevealCellEvent
      (Classical.choice hnonempty) profile A
    · intro b
      exact b.2.1
    · intro X hX
      have hmem := subset_stablePrefixHistory hmn source inletCenter incoming
        firstFlip secondFlip p delta incremented directions j A hAcurrent hAnonnegative
          hstable hX
      rw [stablePrefixHistory, Set.mem_iUnion] at hmem
      obtain ⟨b, hb⟩ := hmem
      rw [Set.mem_iUnion]
      exact ⟨b, by simpa [profile] using hb⟩
    · intro b b' hne
      exact pairwiseDisjoint_stablePrefixRuntimeHistory hmn source inletCenter incoming
        firstFlip secondFlip p delta incremented directions hmono j A hAcurrent hAnonnegative
          hadds hfreshPrefix b b' hne
  · intro c
    simpa [a, restartQuery] using hrestart c

/-- The concrete prefix stage covers its supplied outer history exactly. -/
theorem partitionedLaterSitePrefixStage_cellUnion_eq
    {d m n : ℕ} (hmn : 2 * m ≤ n)
    (source : SourceFiniteEdgeRevealState d) (inletCenter : Cubic d)
    (incoming : CubicDirection d) (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta epsilon : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (hmono : ∀ S a e, S.lower e ≤ incremented S a e)
    (directions : List (CubicDirection d))
    (j : ℕ) (hj : j < directions.length)
    (A : Set (CubicEdge d → ℝ))
    (hnonempty : Nonempty (StablePrefixRuntimeIndex hmn source inletCenter incoming
      firstFlip secondFlip p delta incremented directions j A))
    (hAcurrent : A ⊆ source.historyProfile.event)
    (hAnonnegative : A ⊆ SourceFiniteEdgeRevealState.nonnegativeCouplingEvent)
    (hstable : ∀ X ∈ A,
      (prefixRuntime hmn source inletCenter incoming firstFlip secondFlip
        p delta incremented directions j X).source.historyProfile.event ⊆ A)
    (hadds : ∀ X ∈ A, ∀ l
      (hl : l < (directions.take j).length) e,
      let Rl := runFrom hmn inletCenter incoming firstFlip secondFlip
        p delta incremented X (LaterSiteRuntime.initial source inletCenter) 0
          ((directions.take j).take l)
      let a := (directions.take j)[l]
      (incremented Rl.source a e : ℝ) = (Rl.source.lower e : ℝ) + delta)
    (hfreshPrefix : ∀ X ∈ A, ∀ l
      (hl : l < (directions.take j).length),
      let Rl := runFrom hmn inletCenter incoming firstFlip secondFlip
        p delta incremented X (LaterSiteRuntime.initial source inletCenter) 0
          ((directions.take j).take l)
      let a := (directions.take j)[l]
      let center := Rl.slotCenterFor inletCenter a l
      let flip := Rl.slotTransverseFlip incoming firstFlip secondFlip a l
      let F := cubicRestartFrameIso center a flip
      Disjoint (cubicEdgeEndpointVertices (Rl.source.referenceExploredEdges F))
        (cubicEdgeEndpointVertices (seededBoundaryTargetSupport d a.1 m n)))
    (hTargetFresh : ∀ c : StablePrefixRuntimeIndex hmn source inletCenter incoming
        firstFlip secondFlip p delta incremented directions j A,
      let R := c.1.1
      let a := directions[j]
      let center := R.slotCenterFor inletCenter a j
      let flip := R.slotTransverseFlip incoming firstFlip secondFlip a j
      let F := cubicRestartFrameIso center a flip
      Disjoint (cubicEdgeEndpointVertices (R.source.referenceExploredEdges F))
        (cubicEdgeEndpointVertices (seededBoundaryTargetSupport d a.1 m n)))
    (hrestart : ∀ c : StablePrefixRuntimeIndex hmn source inletCenter incoming
        firstFlip secondFlip p delta incremented directions j A,
      let R := c.1.1
      let a := directions[j]
      let Q := R.restartQuery inletCenter incoming firstFlip secondFlip a j
      (1 - epsilon) * (couplingMeasure (CubicEdge d)).real
          (Q.boundaryHistoryEvent n) <
        (couplingMeasure (CubicEdge d)).real
          (Q.successEvent m n p delta ∩ Q.boundaryHistoryEvent n)) :
    (partitionedLaterSitePrefixStage hmn source inletCenter incoming firstFlip secondFlip
      p delta epsilon incremented hmono directions j hj A hnonempty hAcurrent
        hAnonnegative hstable hadds hfreshPrefix hTargetFresh hrestart).cellUnion = A := by
  let C := StablePrefixRuntimeIndex hmn source inletCenter incoming firstFlip secondFlip
    p delta incremented directions j A
  let profile : C → FiniteRevealIntervalProfile (CubicEdge d) :=
    fun c ↦ c.1.1.source.historyProfile
  let realizedCell : (CubicEdge d → ℝ) → C :=
    realizedIntervalProfileCell (Classical.choice hnonempty) profile
  let a := directions[j]
  unfold partitionedLaterSitePrefixStage
  apply PartitionedFramedRestartStage.cellUnion_ofCanonicalSourceEdgeStateRealizationOfTargetEndpointFresh

/-- The successful union of the concrete prefix stage is exactly the semantic restart event
selected by the executable runtime, restricted to the supplied outer history. -/
theorem partitionedLaterSitePrefixStage_successEvent_eq
    {d m n : ℕ} (hmn : 2 * m ≤ n)
    (source : SourceFiniteEdgeRevealState d) (inletCenter : Cubic d)
    (incoming : CubicDirection d) (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta epsilon : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (hmono : ∀ S a e, S.lower e ≤ incremented S a e)
    (directions : List (CubicDirection d))
    (j : ℕ) (hj : j < directions.length)
    (A : Set (CubicEdge d → ℝ))
    (hnonempty : Nonempty (StablePrefixRuntimeIndex hmn source inletCenter incoming
      firstFlip secondFlip p delta incremented directions j A))
    (hAcurrent : A ⊆ source.historyProfile.event)
    (hAnonnegative : A ⊆ SourceFiniteEdgeRevealState.nonnegativeCouplingEvent)
    (hstable : ∀ X ∈ A,
      (prefixRuntime hmn source inletCenter incoming firstFlip secondFlip
        p delta incremented directions j X).source.historyProfile.event ⊆ A)
    (hadds : ∀ X ∈ A, ∀ l
      (hl : l < (directions.take j).length) e,
      let Rl := runFrom hmn inletCenter incoming firstFlip secondFlip
        p delta incremented X (LaterSiteRuntime.initial source inletCenter) 0
          ((directions.take j).take l)
      let a := (directions.take j)[l]
      (incremented Rl.source a e : ℝ) = (Rl.source.lower e : ℝ) + delta)
    (hfreshPrefix : ∀ X ∈ A, ∀ l
      (hl : l < (directions.take j).length),
      let Rl := runFrom hmn inletCenter incoming firstFlip secondFlip
        p delta incremented X (LaterSiteRuntime.initial source inletCenter) 0
          ((directions.take j).take l)
      let a := (directions.take j)[l]
      let center := Rl.slotCenterFor inletCenter a l
      let flip := Rl.slotTransverseFlip incoming firstFlip secondFlip a l
      let F := cubicRestartFrameIso center a flip
      Disjoint (cubicEdgeEndpointVertices (Rl.source.referenceExploredEdges F))
        (cubicEdgeEndpointVertices (seededBoundaryTargetSupport d a.1 m n)))
    (hTargetFresh : ∀ c : StablePrefixRuntimeIndex hmn source inletCenter incoming
        firstFlip secondFlip p delta incremented directions j A,
      let R := c.1.1
      let a := directions[j]
      let center := R.slotCenterFor inletCenter a j
      let flip := R.slotTransverseFlip incoming firstFlip secondFlip a j
      let F := cubicRestartFrameIso center a flip
      Disjoint (cubicEdgeEndpointVertices (R.source.referenceExploredEdges F))
        (cubicEdgeEndpointVertices (seededBoundaryTargetSupport d a.1 m n)))
    (hrestart : ∀ c : StablePrefixRuntimeIndex hmn source inletCenter incoming
        firstFlip secondFlip p delta incremented directions j A,
      let R := c.1.1
      let a := directions[j]
      let Q := R.restartQuery inletCenter incoming firstFlip secondFlip a j
      (1 - epsilon) * (couplingMeasure (CubicEdge d)).real
          (Q.boundaryHistoryEvent n) <
        (couplingMeasure (CubicEdge d)).real
          (Q.successEvent m n p delta ∩ Q.boundaryHistoryEvent n)) :
    (partitionedLaterSitePrefixStage hmn source inletCenter incoming firstFlip secondFlip
      p delta epsilon incremented hmono directions j hj A hnonempty hAcurrent
        hAnonnegative hstable hadds hfreshPrefix hTargetFresh hrestart).successEvent =
      {X | X ∈ A ∧
        X ∈ ((prefixRuntime hmn source inletCenter incoming firstFlip secondFlip
          p delta incremented directions j X).restartQuery inletCenter incoming
            firstFlip secondFlip directions[j] j).successEvent m n p delta} := by
  let C := StablePrefixRuntimeIndex hmn source inletCenter incoming firstFlip secondFlip
    p delta incremented directions j A
  let profile : C → FiniteRevealIntervalProfile (CubicEdge d) :=
    fun c ↦ c.1.1.source.historyProfile
  let realizedCell : (CubicEdge d → ℝ) → C :=
    realizedIntervalProfileCell (Classical.choice hnonempty) profile
  let a := directions[j]
  unfold partitionedLaterSitePrefixStage
  rw [PartitionedFramedRestartStage.successEvent_eq_semantic_ofCanonicalSourceEdgeStateRealizationOfTargetEndpointFresh]
  ext X
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨hXA, hsuccess⟩
    refine ⟨hXA, ?_⟩
    have hruntime := realizedStablePrefixRuntime_eq_prefixRuntime hmn source inletCenter
      incoming firstFlip secondFlip p delta incremented hmono directions j A hAcurrent
        hAnonnegative hstable hadds hfreshPrefix hnonempty X hXA
    simpa [realizedCell, profile, a, restartQuery, hruntime] using hsuccess
  · rintro ⟨hXA, hsuccess⟩
    refine ⟨hXA, ?_⟩
    have hruntime := realizedStablePrefixRuntime_eq_prefixRuntime hmn source inletCenter
      incoming firstFlip secondFlip p delta incremented hmono directions j A hAcurrent
        hAnonnegative hstable hadds hfreshPrefix hnonempty X hXA
    simpa [realizedCell, profile, a, restartQuery, hruntime] using hsuccess

/-- The concrete runtime partition exposes its semantic success event as a measurable set and
inherits the cellwise `(1-ε)` probability factor.  Keeping this consequence opaque prevents
downstream replay specializations from rechecking the full finite-partition construction. -/
theorem laterSitePrefixSemantic_measurable_and_lower
    {d m n : ℕ} (hmn : 2 * m ≤ n)
    (source : SourceFiniteEdgeRevealState d) (inletCenter : Cubic d)
    (incoming : CubicDirection d) (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta epsilon : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (hmono : ∀ S a e, S.lower e ≤ incremented S a e)
    (directions : List (CubicDirection d))
    (j : ℕ) (hj : j < directions.length)
    (A : Set (CubicEdge d → ℝ))
    (hnonempty : Nonempty (StablePrefixRuntimeIndex hmn source inletCenter incoming
      firstFlip secondFlip p delta incremented directions j A))
    (hAcurrent : A ⊆ source.historyProfile.event)
    (hAnonnegative : A ⊆ SourceFiniteEdgeRevealState.nonnegativeCouplingEvent)
    (hstable : ∀ X ∈ A,
      (prefixRuntime hmn source inletCenter incoming firstFlip secondFlip
        p delta incremented directions j X).source.historyProfile.event ⊆ A)
    (hadds : ∀ X ∈ A, ∀ l
      (hl : l < (directions.take j).length) e,
      let Rl := runFrom hmn inletCenter incoming firstFlip secondFlip
        p delta incremented X (LaterSiteRuntime.initial source inletCenter) 0
          ((directions.take j).take l)
      let a := (directions.take j)[l]
      (incremented Rl.source a e : ℝ) = (Rl.source.lower e : ℝ) + delta)
    (hfreshPrefix : ∀ X ∈ A, ∀ l
      (hl : l < (directions.take j).length),
      let Rl := runFrom hmn inletCenter incoming firstFlip secondFlip
        p delta incremented X (LaterSiteRuntime.initial source inletCenter) 0
          ((directions.take j).take l)
      let a := (directions.take j)[l]
      let center := Rl.slotCenterFor inletCenter a l
      let flip := Rl.slotTransverseFlip incoming firstFlip secondFlip a l
      let F := cubicRestartFrameIso center a flip
      Disjoint (cubicEdgeEndpointVertices (Rl.source.referenceExploredEdges F))
        (cubicEdgeEndpointVertices (seededBoundaryTargetSupport d a.1 m n)))
    (hTargetFresh : ∀ c : StablePrefixRuntimeIndex hmn source inletCenter incoming
        firstFlip secondFlip p delta incremented directions j A,
      let R := c.1.1
      let a := directions[j]
      let center := R.slotCenterFor inletCenter a j
      let flip := R.slotTransverseFlip incoming firstFlip secondFlip a j
      let F := cubicRestartFrameIso center a flip
      Disjoint (cubicEdgeEndpointVertices (R.source.referenceExploredEdges F))
        (cubicEdgeEndpointVertices (seededBoundaryTargetSupport d a.1 m n)))
    (hrestart : ∀ c : StablePrefixRuntimeIndex hmn source inletCenter incoming
        firstFlip secondFlip p delta incremented directions j A,
      let R := c.1.1
      let a := directions[j]
      let Q := R.restartQuery inletCenter incoming firstFlip secondFlip a j
      (1 - epsilon) * (couplingMeasure (CubicEdge d)).real
          (Q.boundaryHistoryEvent n) <
        (couplingMeasure (CubicEdge d)).real
          (Q.successEvent m n p delta ∩ Q.boundaryHistoryEvent n)) :
    let semanticSuccess := {X | X ∈ A ∧
      X ∈ ((prefixRuntime hmn source inletCenter incoming firstFlip secondFlip
        p delta incremented directions j X).restartQuery inletCenter incoming
          firstFlip secondFlip directions[j] j).successEvent m n p delta}
    MeasurableSet semanticSuccess ∧
      (1 - epsilon) * (couplingMeasure (CubicEdge d)).real A ≤
        (couplingMeasure (CubicEdge d)).real semanticSuccess := by
  let T := partitionedLaterSitePrefixStage hmn source inletCenter incoming firstFlip
    secondFlip p delta epsilon incremented hmono directions j hj A hnonempty hAcurrent
      hAnonnegative hstable hadds hfreshPrefix hTargetFresh hrestart
  have hcell : T.cellUnion = A :=
    partitionedLaterSitePrefixStage_cellUnion_eq hmn source inletCenter incoming firstFlip
      secondFlip p delta epsilon incremented hmono directions j hj A hnonempty hAcurrent
        hAnonnegative hstable hadds hfreshPrefix hTargetFresh hrestart
  have hsuccess : T.successEvent = {X | X ∈ A ∧
      X ∈ ((prefixRuntime hmn source inletCenter incoming firstFlip secondFlip
        p delta incremented directions j X).restartQuery inletCenter incoming
          firstFlip secondFlip directions[j] j).successEvent m n p delta} :=
    partitionedLaterSitePrefixStage_successEvent_eq hmn source inletCenter incoming firstFlip
      secondFlip p delta epsilon incremented hmono directions j hj A hnonempty hAcurrent
        hAnonnegative hstable hadds hfreshPrefix hTargetFresh hrestart
  dsimp only
  constructor
  · rw [← hsuccess]
    exact T.measurableSet_successEvent
  · rw [← hsuccess]
    have hlower := T.success_lower_bound
    rw [hcell] at hlower
    exact hlower

/-- All finite-history obligations for one concrete non-root prefix stage. -/
structure LaterSitePrefixCertificate
    {d m n : ℕ} (hmn : 2 * m ≤ n)
    (source : SourceFiniteEdgeRevealState d) (inletCenter : Cubic d)
    (incoming : CubicDirection d) (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta epsilon : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (directions : List (CubicDirection d)) (j : ℕ)
    (A : Set (CubicEdge d → ℝ)) where
  hj : j < directions.length
  hmono : ∀ S a e, S.lower e ≤ incremented S a e
  hnonempty : Nonempty (StablePrefixRuntimeIndex hmn source inletCenter incoming
    firstFlip secondFlip p delta incremented directions j A)
  hAcurrent : A ⊆ source.historyProfile.event
  hAnonnegative : A ⊆ SourceFiniteEdgeRevealState.nonnegativeCouplingEvent
  hstable : ∀ X ∈ A,
    (prefixRuntime hmn source inletCenter incoming firstFlip secondFlip
      p delta incremented directions j X).source.historyProfile.event ⊆ A
  hadds : ∀ X ∈ A, ∀ l
    (hl : l < (directions.take j).length) e,
    let Rl := runFrom hmn inletCenter incoming firstFlip secondFlip
      p delta incremented X (LaterSiteRuntime.initial source inletCenter) 0
        ((directions.take j).take l)
    let a := (directions.take j)[l]
    (incremented Rl.source a e : ℝ) = (Rl.source.lower e : ℝ) + delta
  hfreshPrefix : ∀ X ∈ A, ∀ l
    (hl : l < (directions.take j).length),
    let Rl := runFrom hmn inletCenter incoming firstFlip secondFlip
      p delta incremented X (LaterSiteRuntime.initial source inletCenter) 0
        ((directions.take j).take l)
    let a := (directions.take j)[l]
    let center := Rl.slotCenterFor inletCenter a l
    let flip := Rl.slotTransverseFlip incoming firstFlip secondFlip a l
    let F := cubicRestartFrameIso center a flip
    Disjoint (cubicEdgeEndpointVertices (Rl.source.referenceExploredEdges F))
      (cubicEdgeEndpointVertices (seededBoundaryTargetSupport d a.1 m n))
  hTargetFresh : ∀ c : StablePrefixRuntimeIndex hmn source inletCenter incoming
      firstFlip secondFlip p delta incremented directions j A,
    let R := c.1.1
    let a := directions[j]
    let center := R.slotCenterFor inletCenter a j
    let flip := R.slotTransverseFlip incoming firstFlip secondFlip a j
    let F := cubicRestartFrameIso center a flip
    Disjoint (cubicEdgeEndpointVertices (R.source.referenceExploredEdges F))
      (cubicEdgeEndpointVertices (seededBoundaryTargetSupport d a.1 m n))
  hrestart : ∀ c : StablePrefixRuntimeIndex hmn source inletCenter incoming
      firstFlip secondFlip p delta incremented directions j A,
    let R := c.1.1
    let a := directions[j]
    let Q := R.restartQuery inletCenter incoming firstFlip secondFlip a j
    (1 - epsilon) * (couplingMeasure (CubicEdge d)).real
        (Q.boundaryHistoryEvent n) <
      (couplingMeasure (CubicEdge d)).real
        (Q.successEvent m n p delta ∩ Q.boundaryHistoryEvent n)

end AdaptiveSiteExploration

end Percolation
