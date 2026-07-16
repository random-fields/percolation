import Percolation.Critical.DynamicRootExtensionState

/-!
# Completing the root block from literal mixed-threshold witnesses

The radial source exploration must continue from seeds that it actually revealed.  Selecting
a seed only after raising every edge to a later uniform density is not sound: that selector may
choose a new seed absent from the mixed-threshold certificate.  This file fixes one finite
profile of named mixed witnesses, proves that some such profile has positive mass, and retains
that profile through the post-radial restart recursion.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval

/-- Event on which every direction of a fixed profile is a witness for the literal mixed
radial restart, together with the common central seed. -/
def RootRadialSeedProfile.mixedRadialEvent
    {d m n : ℕ} (W : RootRadialSeedProfile d m n)
    (p : I) (delta : ℝ) : Set (CubicEdge d → ℝ) :=
  {X | X ∈ rootSeedLabelEvent d m p ∧
    ∀ a : CubicDirection d,
      (W a).IsMixedRestartWitness (cubicMetricBox d cubicOrigin m)
        p (fun _ ↦ 0) delta
        (cubicGraphIsoCouplingReindex
          (cubicRestartFrameIso cubicOrigin a (rootRadialTransverseFlip a)) X)}

@[simp]
theorem RootRadialSeedProfile.mem_mixedRadialEvent_iff
    {d m n : ℕ} {W : RootRadialSeedProfile d m n}
    {p : I} {delta : ℝ} {X : CubicEdge d → ℝ} :
    X ∈ W.mixedRadialEvent p delta ↔
      X ∈ rootSeedLabelEvent d m p ∧
        ∀ a : CubicDirection d,
          (W a).IsMixedRestartWitness (cubicMetricBox d cubicOrigin m)
            p (fun _ ↦ 0) delta
            (cubicGraphIsoCouplingReindex
              (cubicRestartFrameIso cubicOrigin a (rootRadialTransverseFlip a)) X) :=
  Iff.rfl

/-- A fixed mixed witness profile supplies every branch of the simultaneous radial event. -/
theorem RootRadialSeedProfile.mixedRadialEvent_subset_rootRadialEvent
    {d m n : ℕ} (W : RootRadialSeedProfile d m n)
    (p : I) (delta : ℝ) :
    W.mixedRadialEvent p delta ⊆ rootRadialEvent d m n p delta := by
  intro X hX
  refine ⟨hX.1, Set.mem_iInter.mpr fun a ↦ ?_⟩
  change cubicGraphIsoCouplingReindex
      (cubicRestartFrameIso cubicOrigin a (rootRadialTransverseFlip a)) X ∈
    sprinkledRestartEvent d a.1 m n (cubicMetricBox d cubicOrigin m)
      p (fun _ ↦ 0) delta
  apply mem_sprinkledRestartEvent_iff_exists_mixedRestartSeedWitness.mpr
  exact ⟨W a, mem_mixedRestartSeedWitnesses_iff.mpr (hX.2 a)⟩

/-- The radial event is exactly the finite/countable union over its literal named witness
profiles. -/
theorem rootRadialEvent_eq_iUnion_mixedRadialEvent
    {d m n : ℕ} (p : I) (delta : ℝ) :
    rootRadialEvent d m n p delta =
      ⋃ W : RootRadialSeedProfile d m n, W.mixedRadialEvent p delta := by
  apply Set.Subset.antisymm
  · intro X hX
    obtain ⟨W, hW⟩ := exists_rootRadialMixedSeedProfile_of_mem hX
    rw [Set.mem_iUnion]
    exact ⟨W, hX.1, fun a ↦ (hW a).2⟩
  · intro X hX
    rw [Set.mem_iUnion] at hX
    obtain ⟨W, hW⟩ := hX
    exact W.mixedRadialEvent_subset_rootRadialEvent p delta hW

/-- Positive radial mass is carried by one fixed profile of literal mixed witnesses. -/
theorem exists_mixedRadialEvent_measure_pos_of_rootRadialEvent_measure_pos
    {d m n : ℕ} {p : I} {delta : ℝ}
    (hroot : 0 < (couplingMeasure (CubicEdge d)).real
      (rootRadialEvent d m n p delta)) :
    ∃ W : RootRadialSeedProfile d m n,
      0 < (couplingMeasure (CubicEdge d)).real (W.mixedRadialEvent p delta) := by
  let μ : Measure (CubicEdge d → ℝ) := couplingMeasure (CubicEdge d)
  have hunionReal : 0 < μ.real
      (⋃ W : RootRadialSeedProfile d m n, W.mixedRadialEvent p delta) := by
    simpa [μ, ← rootRadialEvent_eq_iUnion_mixedRadialEvent p delta] using hroot
  have hunion : μ (⋃ W : RootRadialSeedProfile d m n,
      W.mixedRadialEvent p delta) ≠ 0 := by
    intro hzero
    have : μ.real (⋃ W : RootRadialSeedProfile d m n,
        W.mixedRadialEvent p delta) = 0 := by
      simp [measureReal_def, hzero]
    exact (ne_of_gt hunionReal) this
  obtain ⟨W, hW⟩ := exists_measure_pos_of_not_measure_iUnion_null hunion
  refine ⟨W, ?_⟩
  rw [measureReal_def]
  exact ENNReal.toReal_pos (ne_of_gt hW) (by finiteness)

/-- A fixed mixed radial profile is stable on the unchanged accumulated-history cell of the
literal radial source state. -/
theorem RootRadialSeedProfile.mixedRadialEvent_of_mem_rootPostRadialSourceHistoryProfile
    {d m n : ℕ} [NeZero d] (hm : 1 ≤ m) (hmn : m + 1 ≤ n)
    (W : RootRadialSeedProfile d m n) (p incremented : I) {delta : ℝ}
    (hdelta : delta = (incremented : ℝ))
    (X Y : CubicEdge d → ℝ)
    (hX : X ∈ W.mixedRadialEvent p delta)
    (hY : Y ∈
      (rootPostRadialSourceEdgeState d m n p incremented X).historyProfile.event) :
    Y ∈ W.mixedRadialEvent p delta := by
  constructor
  · exact rootSeedLabelEvent_of_mem_rootPostRadialSourceHistoryProfile
      p incremented X Y hY
  · intro a
    exact rootRadialMixedWitness_of_mem_rootPostRadialSourceHistoryProfile
      hm hmn a p incremented hdelta X Y (W a) (hX.2 a) hY

/-- Semantic success event through the first `k` post-radial slots, starting from one fixed
literal mixed-witness profile. -/
def RootRadialSeedProfile.mixedExtensionPrefixSuccessEvent
    {d m n : ℕ} (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (delta : ℝ)
    (incremented : RootExtensionThresholdPolicy d) (k : ℕ) :
    Set (CubicEdge d → ℝ) :=
  {X | X ∈ W.mixedRadialEvent p delta ∧
    W.runPostRadialExtensionSuccesses p delta incremented X
      (rootPostRadialSourceEdgeState d m n p radialIncremented X)
      ((rootExtensionDirectionOrder d).take k)}

@[simp]
theorem RootRadialSeedProfile.mixedExtensionPrefixSuccessEvent_zero
    {d m n : ℕ} (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (delta : ℝ)
    (incremented : RootExtensionThresholdPolicy d) :
    W.mixedExtensionPrefixSuccessEvent
      p radialIncremented delta incremented 0 = W.mixedRadialEvent p delta := by
  ext X
  simp [RootRadialSeedProfile.mixedExtensionPrefixSuccessEvent]

theorem RootRadialSeedProfile.mem_mixedExtensionPrefixSuccessEvent_succ_iff
    {d m n : ℕ} (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (delta : ℝ)
    (incremented : RootExtensionThresholdPolicy d) {k : ℕ}
    (hk : k < (rootExtensionDirectionOrder d).length)
    (X : CubicEdge d → ℝ) :
    X ∈ W.mixedExtensionPrefixSuccessEvent
        p radialIncremented delta incremented (k + 1) ↔
      X ∈ W.mixedExtensionPrefixSuccessEvent
          p radialIncremented delta incremented k ∧
        let a := (rootExtensionDirectionOrder d)[k]
        let S := W.rootExtensionPrefixState
          p radialIncremented incremented id k X
        let Q := S.framedQuery (W.physicalCenter a) a
          (oppositeTransverseRestartFlip a)
        X ∈ Q.successEvent m n p delta := by
  rw [RootRadialSeedProfile.mixedExtensionPrefixSuccessEvent,
    RootRadialSeedProfile.mixedExtensionPrefixSuccessEvent,
    ← List.take_concat_get' (rootExtensionDirectionOrder d) k hk]
  change
    (X ∈ W.mixedRadialEvent p delta ∧
      W.runPostRadialExtensionSuccesses p delta incremented X
        (rootPostRadialSourceEdgeState d m n p radialIncremented X)
        ((rootExtensionDirectionOrder d).take k ++
          [(rootExtensionDirectionOrder d)[k]])) ↔
      (X ∈ W.mixedRadialEvent p delta ∧
        W.runPostRadialExtensionSuccesses p delta incremented X
          (rootPostRadialSourceEdgeState d m n p radialIncremented X)
          ((rootExtensionDirectionOrder d).take k)) ∧ _
  rw [W.runPostRadialExtensionSuccesses_append]
  simp only [W.runPostRadialExtensionSuccesses_cons,
    W.runPostRadialExtensionSuccesses_nil, and_true]
  tauto

/-- The fixed-profile semantic prefix is constant on every nonempty accumulated-history cell
that it meets. -/
theorem RootRadialSeedProfile.mixedExtensionPrefixSuccessEvent_of_mem_historyProfile
    {d m n : ℕ} [NeZero d] (hm : 1 ≤ m) (hmn : m + 1 < n)
    (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (delta : ℝ)
    (_hdelta : 0 ≤ delta) (hradialDelta : delta = (radialIncremented : ℝ))
    (incremented : RootExtensionThresholdPolicy d)
    (hincremented : ∀ S b e, S.lower e ≤ incremented S b e)
    (hadds : W.PolicyAddsOnPrefixes p radialIncremented delta incremented)
    (hgeom : ∀ a : CubicDirection d,
      SeedBoxWithinBoundaryLayer d a.1 m n (W a).seedCenter.1)
    {k : ℕ} (hk : k ≤ (rootExtensionDirectionOrder d).length)
    (X Y : CubicEdge d → ℝ)
    (hX : X ∈ W.mixedExtensionPrefixSuccessEvent
      p radialIncremented delta incremented k)
    (hY : Y ∈
      (W.rootExtensionPrefixState p radialIncremented incremented id k X).historyProfile.event) :
    Y ∈ W.mixedExtensionPrefixSuccessEvent
      p radialIncremented delta incremented k := by
  let SX := rootPostRadialSourceEdgeState d m n p radialIncremented X
  let SY := rootPostRadialSourceEdgeState d m n p radialIncremented Y
  let directions := (rootExtensionDirectionOrder d).take k
  have hPost : Y ∈ SX.historyProfile.event :=
    W.runPostRadialExtensions_historyProfile_event_subset
      p incremented hincremented X SX directions hY
  have hInitial : SY = SX :=
    (rootInitialSourceEdgeState d m p).next_eq_of_mem_next_historyProfile
      (rootRadialEdgeSupport d m n) p (fun _ ↦ radialIncremented) X Y hPost
  refine ⟨W.mixedRadialEvent_of_mem_rootPostRadialSourceHistoryProfile
    hm hmn.le p radialIncremented hradialDelta X Y hX.1 hPost, ?_⟩
  change W.runPostRadialExtensionSuccesses p delta incremented Y SY directions
  rw [hInitial]
  apply W.runPostRadialExtensionSuccesses_of_mem_historyProfile
    p delta incremented hincremented X Y SX directions
  · intro j hj e
    have hjk : j < k := hj.trans_le (by
      change ((rootExtensionDirectionOrder d).take k).length ≤ k
      exact List.length_take_le k (rootExtensionDirectionOrder d))
    have hjOrder : j < (rootExtensionDirectionOrder d).length := hjk.trans_le hk
    simpa [SX, directions, List.take_take, Nat.min_eq_left hjk.le,
      RootRadialSeedProfile.rootExtensionPrefixState] using
      hadds X j hjOrder e
  · intro j hj
    have hjk : j < k := hj.trans_le (by
      change ((rootExtensionDirectionOrder d).take k).length ≤ k
      exact List.length_take_le k (rootExtensionDirectionOrder d))
    have hjOrder : j < (rootExtensionDirectionOrder d).length := hjk.trans_le hk
    simpa [directions, List.take_take, Nat.min_eq_left hjk.le,
      RootRadialSeedProfile.postRadialFrame] using
      (rootPostRadialExtensions_prefix_targetEndpointFresh_of_geometry
        hm hmn W p radialIncremented incremented X hgeom hjOrder)
  · exact hX.2
  · exact hY

/-! ### Nonempty stable cells for a fixed mixed profile -/

/-- Reachable accumulated-history cells that are both nonempty and wholly contained in a
semantic event.  Removing empty cells is essential: a vacuous cell contains no realization
from which to recover the named mixed witness needed by the next restart. -/
abbrev WitnessedRootExtensionPrefixStateIndex
    {d m n : ℕ} (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (incremented : RootExtensionThresholdPolicy d) (k : ℕ)
    (A : Set (CubicEdge d → ℝ)) :=
  {c : RootExtensionPrefixStateIndex W p radialIncremented incremented k //
    c.1.historyProfile.event ⊆ A ∧ c.1.historyProfile.event.Nonempty}

noncomputable instance witnessedRootExtensionPrefixStateIndexFintype
    {d m n : ℕ} (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (incremented : RootExtensionThresholdPolicy d) (k : ℕ)
    (A : Set (CubicEdge d → ℝ)) :
    Fintype (WitnessedRootExtensionPrefixStateIndex
      W p radialIncremented incremented k A) :=
  Fintype.ofFinite _

noncomputable instance witnessedRootExtensionPrefixStateIndexDecidableEq
    {d m n : ℕ} (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (incremented : RootExtensionThresholdPolicy d) (k : ℕ)
    (A : Set (CubicEdge d → ℝ)) :
    DecidableEq (WitnessedRootExtensionPrefixStateIndex
      W p radialIncremented incremented k A) :=
  Classical.decEq _

/-- Union of the nonempty canonical accumulated-history cells retained by `A`. -/
def RootRadialSeedProfile.witnessedRootExtensionPrefixHistory
    {d m n : ℕ} (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (incremented : RootExtensionThresholdPolicy d) (k : ℕ)
    (A : Set (CubicEdge d → ℝ)) : Set (CubicEdge d → ℝ) :=
  ⋃ c : WitnessedRootExtensionPrefixStateIndex
      W p radialIncremented incremented k A,
    c.1.1.historyProfile.event

theorem RootRadialSeedProfile.witnessedRootExtensionPrefixHistory_subset
    {d m n : ℕ} (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (incremented : RootExtensionThresholdPolicy d) (k : ℕ)
    (A : Set (CubicEdge d → ℝ)) :
    W.witnessedRootExtensionPrefixHistory p radialIncremented incremented k A ⊆ A := by
  intro X hX
  rw [RootRadialSeedProfile.witnessedRootExtensionPrefixHistory, Set.mem_iUnion] at hX
  obtain ⟨c, hc⟩ := hX
  exact c.2.1 hc

/-- On the common-uniform support, every successful fixed-profile prefix belongs to a
nonempty canonical cell that is stable on that prefix event. -/
theorem RootRadialSeedProfile.mixedExtensionPrefixSuccess_inter_nonnegative_subset_witnessedHistory
    {d m n : ℕ} [NeZero d] (hm : 1 ≤ m) (hmn : m + 1 < n)
    (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (delta : ℝ)
    (hdelta : 0 ≤ delta) (hradialDelta : delta = (radialIncremented : ℝ))
    (incremented : RootExtensionThresholdPolicy d)
    (hincremented : ∀ S b e, S.lower e ≤ incremented S b e)
    (hadds : W.PolicyAddsOnPrefixes p radialIncremented delta incremented)
    (hgeom : ∀ a : CubicDirection d,
      SeedBoxWithinBoundaryLayer d a.1 m n (W a).seedCenter.1)
    {k : ℕ} (hk : k ≤ (rootExtensionDirectionOrder d).length) :
    W.mixedExtensionPrefixSuccessEvent p radialIncremented delta incremented k ∩
        SourceFiniteEdgeRevealState.nonnegativeCouplingEvent ⊆
      W.witnessedRootExtensionPrefixHistory p radialIncremented incremented k
        (W.mixedExtensionPrefixSuccessEvent
          p radialIncremented delta incremented k) := by
  intro X hX
  let S := W.rootExtensionPrefixState p radialIncremented incremented id k X
  let c : RootExtensionPrefixStateIndex W p radialIncremented incremented k :=
    ⟨S, (W.mem_rootExtensionPrefixStateFinset_iff
      p radialIncremented incremented k S).mpr ⟨X, rfl⟩⟩
  have hstable : S.historyProfile.event ⊆
      W.mixedExtensionPrefixSuccessEvent
        p radialIncremented delta incremented k := by
    intro Y hY
    exact W.mixedExtensionPrefixSuccessEvent_of_mem_historyProfile
      hm hmn p radialIncremented delta hdelta hradialDelta incremented
        hincremented hadds hgeom hk X Y hX.1 hY
  have hself : X ∈ S.historyProfile.event := by
    exact W.mem_runPostRadialExtensions_historyProfile p incremented X
      ((rootExtensionDirectionOrder d).take k)
      (rootPostRadialSourceEdgeState d m n p radialIncremented X) hX.2
      (rootRadialEvent_mem_postRadialSourceHistoryProfile
        p radialIncremented delta X
        (W.mixedRadialEvent_subset_rootRadialEvent p delta hX.1.1) hX.2)
  rw [RootRadialSeedProfile.witnessedRootExtensionPrefixHistory, Set.mem_iUnion]
  exact ⟨⟨c, hstable, ⟨X, hself⟩⟩, hself⟩

/-- Exact almost-sure identity between the witnessed-cell union and the fixed-profile
semantic prefix. -/
theorem RootRadialSeedProfile.witnessedHistory_inter_nonnegative_eq_mixedExtensionPrefixSuccess
    {d m n : ℕ} [NeZero d] (hm : 1 ≤ m) (hmn : m + 1 < n)
    (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (delta : ℝ)
    (hdelta : 0 ≤ delta) (hradialDelta : delta = (radialIncremented : ℝ))
    (incremented : RootExtensionThresholdPolicy d)
    (hincremented : ∀ S b e, S.lower e ≤ incremented S b e)
    (hadds : W.PolicyAddsOnPrefixes p radialIncremented delta incremented)
    (hgeom : ∀ a : CubicDirection d,
      SeedBoxWithinBoundaryLayer d a.1 m n (W a).seedCenter.1)
    {k : ℕ} (hk : k ≤ (rootExtensionDirectionOrder d).length) :
    W.witnessedRootExtensionPrefixHistory p radialIncremented incremented k
          (W.mixedExtensionPrefixSuccessEvent
            p radialIncremented delta incremented k) ∩
        SourceFiniteEdgeRevealState.nonnegativeCouplingEvent =
      W.mixedExtensionPrefixSuccessEvent p radialIncremented delta incremented k ∩
        SourceFiniteEdgeRevealState.nonnegativeCouplingEvent := by
  apply Set.Subset.antisymm
  · intro X hX
    exact ⟨W.witnessedRootExtensionPrefixHistory_subset
      p radialIncremented incremented k
        (W.mixedExtensionPrefixSuccessEvent
          p radialIncremented delta incremented k) hX.1, hX.2⟩
  · intro X hX
    exact ⟨W.mixedExtensionPrefixSuccess_inter_nonnegative_subset_witnessedHistory
      hm hmn p radialIncremented delta hdelta hradialDelta incremented
        hincremented hadds hgeom hk hX, hX.2⟩

/-- Every realization in a witnessed canonical cell reproduces the cell's prefix state. -/
theorem RootRadialSeedProfile.rootExtensionPrefixState_eq_witnessedCell
    {d m n : ℕ} (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (incremented : RootExtensionThresholdPolicy d)
    (hincremented : ∀ S b e, S.lower e ≤ incremented S b e)
    (k : ℕ) (A : Set (CubicEdge d → ℝ))
    (c : WitnessedRootExtensionPrefixStateIndex
      W p radialIncremented incremented k A)
    (X : CubicEdge d → ℝ) (hX : X ∈ c.1.1.historyProfile.event) :
    W.rootExtensionPrefixState p radialIncremented incremented id k X = c.1.1 := by
  obtain ⟨R, hR⟩ := (W.mem_rootExtensionPrefixStateFinset_iff
    p radialIncremented incremented k c.1.1).mp c.1.2
  have hXR : X ∈
      (W.rootExtensionPrefixState p radialIncremented incremented id k R).historyProfile.event := by
    rw [hR]
    exact hX
  exact (W.rootExtensionPrefixState_eq_of_mem_historyProfile
    p radialIncremented incremented hincremented k R X hXR).trans hR

/-- Lemma 7.17 applies automatically to every nonempty fixed-profile prefix cell.  The inlet
box comes from the literal mixed witness, the unused layer from steering geometry, and the
upper threshold bound from the finite global sprinkling budget. -/
theorem RootRadialSeedProfile.mixedPrefixCell_uniformRestart
    {d m n : ℕ} [NeZero d] (hm : 1 ≤ m) (hmn : m + 1 < n)
    (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (delta epsilon : ℝ)
    (hdelta : 0 ≤ delta) (hradialDelta : delta = (radialIncremented : ℝ))
    (htotal : max (p : ℝ) (radialIncremented : ℝ) +
      ((rootExtensionDirectionOrder d).length : ℝ) * delta ≤ 1)
    (huniform : UniformRestartBounds d m n p delta epsilon)
    {k : ℕ} (hk : k < (rootExtensionDirectionOrder d).length)
    (c : WitnessedRootExtensionPrefixStateIndex
      W p radialIncremented
        (budgetedRootExtensionThresholdPolicy delta hdelta) k
        (W.mixedExtensionPrefixSuccessEvent p radialIncremented delta
          (budgetedRootExtensionThresholdPolicy delta hdelta) k)) :
    let a := (rootExtensionDirectionOrder d)[k]
    let S := c.1.1
    let Q := S.framedQuery (W.physicalCenter a) a
      (oppositeTransverseRestartFlip a)
    (1 - epsilon) * (couplingMeasure (CubicEdge d)).real
        (Q.boundaryHistoryEvent n) <
      (couplingMeasure (CubicEdge d)).real
        (Q.successEvent m n p delta ∩ Q.boundaryHistoryEvent n) := by
  classical
  let incremented : RootExtensionThresholdPolicy d :=
    budgetedRootExtensionThresholdPolicy delta hdelta
  let X : CubicEdge d → ℝ := Classical.choose c.2.2
  have hXCell : X ∈ c.1.1.historyProfile.event := Classical.choose_spec c.2.2
  have hXPrefix : X ∈ W.mixedExtensionPrefixSuccessEvent
      p radialIncremented delta incremented k := c.2.1 hXCell
  have hState : W.rootExtensionPrefixState
      p radialIncremented incremented id k X = c.1.1 :=
    W.rootExtensionPrefixState_eq_witnessedCell
      p radialIncremented incremented
      (lower_le_budgetedRootExtensionThresholdPolicy delta hdelta)
      k _ c X hXCell
  let a := (rootExtensionDirectionOrder d)[k]
  let S := c.1.1
  let Q := S.framedQuery (W.physicalCenter a) a
    (oppositeTransverseRestartFlip a)
  have hgeom : ∀ b : CubicDirection d,
      SeedBoxWithinBoundaryLayer d b.1 m n (W b).seedCenter.1 := fun b ↦
    (hXPrefix.1.2 b).1.2.2.1
  have hseedPost :
      cubicMetricBox d cubicOrigin m ⊆
        ((rootPostRadialSourceEdgeState d m n p radialIncremented X).framedQuery
          (W.physicalCenter a) a (oppositeTransverseRestartFlip a)).region := by
    exact W.cubicMetricBox_subset_postRadialQuery_region_of_mixedWitness
      hm hmn.le a p radialIncremented hradialDelta X (hXPrefix.1.2 a)
  have hExplored :
      (rootPostRadialSourceEdgeState d m n p radialIncremented X).explored ⊆
        (W.rootExtensionPrefixState p radialIncremented incremented id k X).explored := by
    exact W.explored_subset_runPostRadialExtensions p incremented X
      (rootPostRadialSourceEdgeState d m n p radialIncremented X)
      ((rootExtensionDirectionOrder d).take k)
  have hseed : cubicMetricBox d cubicOrigin m ⊆ Q.region := by
    intro z hz
    have hz' := SourceFiniteEdgeRevealState.framedQuery_region_mono hExplored
      (W.physicalCenter a) a (oppositeTransverseRestartFlip a) (hseedPost hz)
    rw [hState] at hz'
    exact hz'
  have hAvoid : RegionAvoidsSeededBoundaryQuadrant d a.1 n (Q.croppedRegion n) := by
    apply regionAvoidsSeededBoundaryQuadrant_of_coord_add_one_lt
    intro z hz
    have hzRegion : z ∈ Q.region := (Finset.mem_inter.mp hz).1
    change z ∈ cubicEdgeEndpointVertices
      (S.referenceExploredEdges (W.postRadialFrame a)) at hzRegion
    have hzPrefix : z ∈ cubicEdgeEndpointVertices
        ((W.rootExtensionPrefixState
          p radialIncremented incremented id k X).referenceExploredEdges
            (W.postRadialFrame a)) := by
      rw [hState]
      exact hzRegion
    exact rootPostRadialExtensions_prefix_referenceEndpoint_coord_add_one_lt_of_geometry
      hm hmn W p radialIncremented incremented X hgeom hk hzPrefix
  have hbudget : S.HasIncrementBudget delta := by
    have hb := W.rootExtensionPrefixState_hasIncrementBudget
      p radialIncremented delta hdelta htotal id hk X
    rw [hState] at hb
    exact hb
  apply Q.uniformRestartBounds_of_croppedRegion p delta epsilon huniform (by omega) hseed hAvoid
  intro e _he
  change (S.lower ((W.postRadialFrame a).mapEdgeSet e) : ℝ) + delta ≤ 1
  exact hbudget _

namespace AdaptiveSiteExploration

/-- The `k`-th post-radial restart, partitioned only by nonempty canonical cells belonging to
the fixed mixed-witness prefix. -/
noncomputable def RootRadialSeedProfile.mixedExtensionPrefixStage
    {d m n : ℕ} [NeZero d] (hm : 1 ≤ m) (hmn : m + 1 < n)
    (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (delta epsilon : ℝ)
    (hdelta : 0 ≤ delta) (hradialDelta : delta = (radialIncremented : ℝ))
    (htotal : max (p : ℝ) (radialIncremented : ℝ) +
      ((rootExtensionDirectionOrder d).length : ℝ) * delta ≤ 1)
    (huniform : UniformRestartBounds d m n p delta epsilon)
    {k : ℕ}
    (hnonempty : Nonempty (WitnessedRootExtensionPrefixStateIndex
      W p radialIncremented
        (budgetedRootExtensionThresholdPolicy delta hdelta) k
        (W.mixedExtensionPrefixSuccessEvent p radialIncremented delta
          (budgetedRootExtensionThresholdPolicy delta hdelta) k)))
    (hgeom : ∀ a : CubicDirection d,
      SeedBoxWithinBoundaryLayer d a.1 m n (W a).seedCenter.1)
    (hk : k < (rootExtensionDirectionOrder d).length) :
    PartitionedFramedRestartStage d
      (WitnessedRootExtensionPrefixStateIndex
        W p radialIncremented
          (budgetedRootExtensionThresholdPolicy delta hdelta) k
          (W.mixedExtensionPrefixSuccessEvent p radialIncremented delta
            (budgetedRootExtensionThresholdPolicy delta hdelta) k))
      m n p delta epsilon := by
  let incremented : RootExtensionThresholdPolicy d :=
    budgetedRootExtensionThresholdPolicy delta hdelta
  let A := W.mixedExtensionPrefixSuccessEvent
    p radialIncremented delta incremented k
  let C := WitnessedRootExtensionPrefixStateIndex
    W p radialIncremented incremented k A
  let representative : C → CubicEdge d → ℝ := fun c ↦ Classical.choose c.2.2
  have hrepresentative : ∀ c : C,
      W.rootExtensionPrefixState p radialIncremented incremented representative k c =
        c.1.1 := by
    intro c
    exact W.rootExtensionPrefixState_eq_witnessedCell
      p radialIncremented incremented
      (lower_le_budgetedRootExtensionThresholdPolicy delta hdelta)
      k A c (representative c) (Classical.choose_spec c.2.2)
  apply RootRadialSeedProfile.partitionedRootExtensionStageOfProfilePartition
    hm hmn W p radialIncremented delta epsilon incremented
      (W.witnessedRootExtensionPrefixHistory p radialIncremented incremented k A)
      (Classical.choice hnonempty) representative hgeom hk
  · intro c
    rw [hrepresentative c]
    exact Set.subset_iUnion
      (fun c : C ↦ c.1.1.historyProfile.event) c
  · intro X hX
    rw [RootRadialSeedProfile.witnessedRootExtensionPrefixHistory,
      Set.mem_iUnion] at hX
    rw [Set.mem_iUnion]
    obtain ⟨c, hc⟩ := hX
    exact ⟨c, by simpa only [hrepresentative c] using hc⟩
  · intro c c' hne
    rw [hrepresentative c, hrepresentative c']
    apply W.pairwiseDisjoint_rootExtensionPrefixHistory
      p radialIncremented incremented
        (lower_le_budgetedRootExtensionThresholdPolicy delta hdelta) k c.1 c'.1
    intro hval
    exact hne (Subtype.ext hval)
  · intro c
    rw [hrepresentative c]
    exact W.mixedPrefixCell_uniformRestart hm hmn p radialIncremented
      delta epsilon hdelta hradialDelta htotal huniform hk c

@[simp]
theorem RootRadialSeedProfile.mixedExtensionPrefixStage_query
    {d m n : ℕ} [NeZero d] (hm : 1 ≤ m) (hmn : m + 1 < n)
    (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (delta epsilon : ℝ)
    (hdelta : 0 ≤ delta) (hradialDelta : delta = (radialIncremented : ℝ))
    (htotal : max (p : ℝ) (radialIncremented : ℝ) +
      ((rootExtensionDirectionOrder d).length : ℝ) * delta ≤ 1)
    (huniform : UniformRestartBounds d m n p delta epsilon)
    {k : ℕ}
    (hnonempty : Nonempty (WitnessedRootExtensionPrefixStateIndex
      W p radialIncremented
        (budgetedRootExtensionThresholdPolicy delta hdelta) k
        (W.mixedExtensionPrefixSuccessEvent p radialIncremented delta
          (budgetedRootExtensionThresholdPolicy delta hdelta) k)))
    (hgeom : ∀ a : CubicDirection d,
      SeedBoxWithinBoundaryLayer d a.1 m n (W a).seedCenter.1)
    (hk : k < (rootExtensionDirectionOrder d).length)
    (c : WitnessedRootExtensionPrefixStateIndex
      W p radialIncremented
        (budgetedRootExtensionThresholdPolicy delta hdelta) k
        (W.mixedExtensionPrefixSuccessEvent p radialIncremented delta
          (budgetedRootExtensionThresholdPolicy delta hdelta) k)) :
    (RootRadialSeedProfile.mixedExtensionPrefixStage hm hmn W p radialIncremented delta epsilon
      hdelta hradialDelta htotal huniform hnonempty hgeom hk).query c =
      let a := (rootExtensionDirectionOrder d)[k]
      c.1.1.framedQuery (W.physicalCenter a) a
        (oppositeTransverseRestartFlip a) := by
  classical
  unfold RootRadialSeedProfile.mixedExtensionPrefixStage
  unfold RootRadialSeedProfile.partitionedRootExtensionStageOfProfilePartition
  unfold RootRadialSeedProfile.partitionedRootExtensionStage
  rw [PartitionedFramedRestartStage.query_ofCanonicalSourceEdgeStateRealizationOfTargetEndpointFresh]
  have hstate : W.rootExtensionPrefixState p radialIncremented
      (budgetedRootExtensionThresholdPolicy delta hdelta)
      (fun c : WitnessedRootExtensionPrefixStateIndex W p radialIncremented
        (budgetedRootExtensionThresholdPolicy delta hdelta) k
        (W.mixedExtensionPrefixSuccessEvent p radialIncremented delta
          (budgetedRootExtensionThresholdPolicy delta hdelta) k) ↦
          Classical.choose c.2.2) k c = c.1.1 := by
    change W.rootExtensionPrefixState p radialIncremented
      (budgetedRootExtensionThresholdPolicy delta hdelta) id k
        (Classical.choose c.2.2) = c.1.1
    exact W.rootExtensionPrefixState_eq_witnessedCell
      p radialIncremented (budgetedRootExtensionThresholdPolicy delta hdelta)
        (lower_le_budgetedRootExtensionThresholdPolicy delta hdelta)
        k _ c (Classical.choose c.2.2) (Classical.choose_spec c.2.2)
  rw [hstate]

@[simp]
theorem RootRadialSeedProfile.mixedExtensionPrefixStage_cell
    {d m n : ℕ} [NeZero d] (hm : 1 ≤ m) (hmn : m + 1 < n)
    (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (delta epsilon : ℝ)
    (hdelta : 0 ≤ delta) (hradialDelta : delta = (radialIncremented : ℝ))
    (htotal : max (p : ℝ) (radialIncremented : ℝ) +
      ((rootExtensionDirectionOrder d).length : ℝ) * delta ≤ 1)
    (huniform : UniformRestartBounds d m n p delta epsilon)
    {k : ℕ}
    (hnonempty : Nonempty (WitnessedRootExtensionPrefixStateIndex
      W p radialIncremented
        (budgetedRootExtensionThresholdPolicy delta hdelta) k
        (W.mixedExtensionPrefixSuccessEvent p radialIncremented delta
          (budgetedRootExtensionThresholdPolicy delta hdelta) k)))
    (hgeom : ∀ a : CubicDirection d,
      SeedBoxWithinBoundaryLayer d a.1 m n (W a).seedCenter.1)
    (hk : k < (rootExtensionDirectionOrder d).length)
    (c : WitnessedRootExtensionPrefixStateIndex
      W p radialIncremented
        (budgetedRootExtensionThresholdPolicy delta hdelta) k
        (W.mixedExtensionPrefixSuccessEvent p radialIncremented delta
          (budgetedRootExtensionThresholdPolicy delta hdelta) k)) :
    (RootRadialSeedProfile.mixedExtensionPrefixStage hm hmn W p radialIncremented delta epsilon
      hdelta hradialDelta htotal huniform hnonempty hgeom hk).cell c =
        c.1.1.historyProfile.event := by
  classical
  unfold RootRadialSeedProfile.mixedExtensionPrefixStage
  unfold RootRadialSeedProfile.partitionedRootExtensionStageOfProfilePartition
  unfold RootRadialSeedProfile.partitionedRootExtensionStage
  rw [PartitionedFramedRestartStage.cell_ofCanonicalSourceEdgeStateRealizationOfTargetEndpointFresh]
  have hstate : W.rootExtensionPrefixState p radialIncremented
      (budgetedRootExtensionThresholdPolicy delta hdelta)
      (fun c : WitnessedRootExtensionPrefixStateIndex W p radialIncremented
        (budgetedRootExtensionThresholdPolicy delta hdelta) k
        (W.mixedExtensionPrefixSuccessEvent p radialIncremented delta
          (budgetedRootExtensionThresholdPolicy delta hdelta) k) ↦
          Classical.choose c.2.2) k c = c.1.1 := by
    change W.rootExtensionPrefixState p radialIncremented
      (budgetedRootExtensionThresholdPolicy delta hdelta) id k
        (Classical.choose c.2.2) = c.1.1
    exact W.rootExtensionPrefixState_eq_witnessedCell
      p radialIncremented (budgetedRootExtensionThresholdPolicy delta hdelta)
        (lower_le_budgetedRootExtensionThresholdPolicy delta hdelta)
        k _ c (Classical.choose c.2.2) (Classical.choose_spec c.2.2)
  rw [hstate]

theorem RootRadialSeedProfile.mixedExtensionPrefixStage_cellUnion
    {d m n : ℕ} [NeZero d] (hm : 1 ≤ m) (hmn : m + 1 < n)
    (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (delta epsilon : ℝ)
    (hdelta : 0 ≤ delta) (hradialDelta : delta = (radialIncremented : ℝ))
    (htotal : max (p : ℝ) (radialIncremented : ℝ) +
      ((rootExtensionDirectionOrder d).length : ℝ) * delta ≤ 1)
    (huniform : UniformRestartBounds d m n p delta epsilon)
    {k : ℕ}
    (hnonempty : Nonempty (WitnessedRootExtensionPrefixStateIndex
      W p radialIncremented
        (budgetedRootExtensionThresholdPolicy delta hdelta) k
        (W.mixedExtensionPrefixSuccessEvent p radialIncremented delta
          (budgetedRootExtensionThresholdPolicy delta hdelta) k)))
    (hgeom : ∀ a : CubicDirection d,
      SeedBoxWithinBoundaryLayer d a.1 m n (W a).seedCenter.1)
    (hk : k < (rootExtensionDirectionOrder d).length) :
    (RootRadialSeedProfile.mixedExtensionPrefixStage hm hmn W p radialIncremented delta epsilon
      hdelta hradialDelta htotal huniform hnonempty hgeom hk).cellUnion =
      W.witnessedRootExtensionPrefixHistory p radialIncremented
        (budgetedRootExtensionThresholdPolicy delta hdelta) k
        (W.mixedExtensionPrefixSuccessEvent p radialIncremented delta
          (budgetedRootExtensionThresholdPolicy delta hdelta) k) := by
  classical
  unfold RootRadialSeedProfile.mixedExtensionPrefixStage
  apply RootRadialSeedProfile.partitionedRootExtensionStageOfProfilePartition_cellUnion

/-- The successful union of the witnessed `k`-th stage is exactly success through slot
`k+1`, modulo the probability-one common-uniform support. -/
theorem RootRadialSeedProfile.mixedExtensionPrefixStage_successEvent_inter_nonnegative_eq
    {d m n : ℕ} [NeZero d] (hm : 1 ≤ m) (hmn : m + 1 < n)
    (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (delta epsilon : ℝ)
    (hdelta : 0 ≤ delta) (hradialDelta : delta = (radialIncremented : ℝ))
    (htotal : max (p : ℝ) (radialIncremented : ℝ) +
      ((rootExtensionDirectionOrder d).length : ℝ) * delta ≤ 1)
    (huniform : UniformRestartBounds d m n p delta epsilon)
    {k : ℕ}
    (hnonempty : Nonempty (WitnessedRootExtensionPrefixStateIndex
      W p radialIncremented
        (budgetedRootExtensionThresholdPolicy delta hdelta) k
        (W.mixedExtensionPrefixSuccessEvent p radialIncremented delta
          (budgetedRootExtensionThresholdPolicy delta hdelta) k)))
    (hgeom : ∀ a : CubicDirection d,
      SeedBoxWithinBoundaryLayer d a.1 m n (W a).seedCenter.1)
    (hk : k < (rootExtensionDirectionOrder d).length) :
    (RootRadialSeedProfile.mixedExtensionPrefixStage hm hmn W p radialIncremented
      delta epsilon hdelta hradialDelta htotal huniform hnonempty hgeom hk).successEvent ∩
        SourceFiniteEdgeRevealState.nonnegativeCouplingEvent =
      W.mixedExtensionPrefixSuccessEvent p radialIncremented delta
          (budgetedRootExtensionThresholdPolicy delta hdelta) (k + 1) ∩
        SourceFiniteEdgeRevealState.nonnegativeCouplingEvent := by
  classical
  let incremented : RootExtensionThresholdPolicy d :=
    budgetedRootExtensionThresholdPolicy delta hdelta
  let S := RootRadialSeedProfile.mixedExtensionPrefixStage hm hmn W p radialIncremented
    delta epsilon hdelta hradialDelta htotal huniform hnonempty hgeom hk
  change S.successEvent ∩ SourceFiniteEdgeRevealState.nonnegativeCouplingEvent = _
  ext X
  constructor
  · rintro ⟨hSuccess, hNonnegative⟩
    simp only [PartitionedFramedRestartStage.successEvent, Set.mem_iUnion] at hSuccess
    obtain ⟨c, _hc, hSuccessfulCell⟩ := hSuccess
    have hHistory : X ∈ c.1.1.historyProfile.event := by
      rw [← RootRadialSeedProfile.mixedExtensionPrefixStage_cell
        hm hmn W p radialIncremented delta epsilon hdelta hradialDelta htotal
          huniform hnonempty hgeom hk c]
      exact hSuccessfulCell.2
    have hPrefix : X ∈ W.mixedExtensionPrefixSuccessEvent
        p radialIncremented delta incremented k := c.2.1 hHistory
    have hXState : W.rootExtensionPrefixState
        p radialIncremented incremented id k X = c.1.1 :=
      W.rootExtensionPrefixState_eq_witnessedCell
        p radialIncremented incremented
          (lower_le_budgetedRootExtensionThresholdPolicy delta hdelta)
          k _ c X hHistory
    have hStageQuery : X ∈ (S.query c).successEvent m n p delta := hSuccessfulCell.1
    have hQuery :
        let a := (rootExtensionDirectionOrder d)[k]
        let SX := W.rootExtensionPrefixState p radialIncremented incremented id k X
        let Q := SX.framedQuery (W.physicalCenter a) a
          (oppositeTransverseRestartFlip a)
        X ∈ Q.successEvent m n p delta := by
      rw [hXState]
      simpa [S] using hStageQuery
    exact ⟨(W.mem_mixedExtensionPrefixSuccessEvent_succ_iff
      p radialIncremented delta incremented hk X).2 ⟨hPrefix, hQuery⟩,
      hNonnegative⟩
  · rintro ⟨hNext, hNonnegative⟩
    obtain ⟨hPrefix, hQuery⟩ :=
      (W.mem_mixedExtensionPrefixSuccessEvent_succ_iff
        p radialIncremented delta incremented hk X).1 hNext
    have hWitnessed : X ∈ W.witnessedRootExtensionPrefixHistory
        p radialIncremented incremented k
          (W.mixedExtensionPrefixSuccessEvent
            p radialIncremented delta incremented k) :=
      W.mixedExtensionPrefixSuccess_inter_nonnegative_subset_witnessedHistory
        hm hmn p radialIncremented delta hdelta hradialDelta incremented
          (lower_le_budgetedRootExtensionThresholdPolicy delta hdelta)
          (W.budgetedPolicy_addsOnPrefixes
            p radialIncremented delta hdelta htotal)
          hgeom hk.le ⟨hPrefix, hNonnegative⟩
    rw [RootRadialSeedProfile.witnessedRootExtensionPrefixHistory,
      Set.mem_iUnion] at hWitnessed
    obtain ⟨c, hHistory⟩ := hWitnessed
    have hXState : W.rootExtensionPrefixState
        p radialIncremented incremented id k X = c.1.1 :=
      W.rootExtensionPrefixState_eq_witnessedCell
        p radialIncremented incremented
          (lower_le_budgetedRootExtensionThresholdPolicy delta hdelta)
          k _ c X hHistory
    have hStageQuery : X ∈ (S.query c).successEvent m n p delta := by
      rw [RootRadialSeedProfile.mixedExtensionPrefixStage_query
        hm hmn W p radialIncremented delta epsilon hdelta hradialDelta htotal
          huniform hnonempty hgeom hk c, ← hXState]
      exact hQuery
    refine ⟨?_, hNonnegative⟩
    simp only [PartitionedFramedRestartStage.successEvent, Set.mem_iUnion]
    refine ⟨c, Finset.mem_univ c, hStageQuery, ?_⟩
    rw [RootRadialSeedProfile.mixedExtensionPrefixStage_cell
      hm hmn W p radialIncremented delta epsilon hdelta hradialDelta htotal
        huniform hnonempty hgeom hk c]
    exact hHistory

/-- One fixed-profile extension retains the factor `1-epsilon` with all geometric and
probabilistic premises discharged from the source package. -/
theorem RootRadialSeedProfile.mixedExtensionPrefixSuccess_measure_step
    {d m n : ℕ} [NeZero d] (hm : 1 ≤ m) (hmn : m + 1 < n)
    (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (delta epsilon : ℝ)
    (hdelta : 0 ≤ delta) (hradialDelta : delta = (radialIncremented : ℝ))
    (htotal : max (p : ℝ) (radialIncremented : ℝ) +
      ((rootExtensionDirectionOrder d).length : ℝ) * delta ≤ 1)
    (huniform : UniformRestartBounds d m n p delta epsilon)
    {k : ℕ}
    (hnonempty : Nonempty (WitnessedRootExtensionPrefixStateIndex
      W p radialIncremented
        (budgetedRootExtensionThresholdPolicy delta hdelta) k
        (W.mixedExtensionPrefixSuccessEvent p radialIncremented delta
          (budgetedRootExtensionThresholdPolicy delta hdelta) k)))
    (hgeom : ∀ a : CubicDirection d,
      SeedBoxWithinBoundaryLayer d a.1 m n (W a).seedCenter.1)
    (hk : k < (rootExtensionDirectionOrder d).length) :
    (1 - epsilon) * (couplingMeasure (CubicEdge d)).real
        (W.mixedExtensionPrefixSuccessEvent p radialIncremented delta
          (budgetedRootExtensionThresholdPolicy delta hdelta) k) ≤
      (couplingMeasure (CubicEdge d)).real
        (W.mixedExtensionPrefixSuccessEvent p radialIncremented delta
          (budgetedRootExtensionThresholdPolicy delta hdelta) (k + 1)) := by
  let S := RootRadialSeedProfile.mixedExtensionPrefixStage hm hmn W p radialIncremented
    delta epsilon hdelta hradialDelta htotal huniform hnonempty hgeom hk
  apply S.success_lower_bound_of_inter_support_eq
    SourceFiniteEdgeRevealState.nonnegativeCouplingEvent
    (W.mixedExtensionPrefixSuccessEvent p radialIncremented delta
      (budgetedRootExtensionThresholdPolicy delta hdelta) k)
    (W.mixedExtensionPrefixSuccessEvent p radialIncremented delta
      (budgetedRootExtensionThresholdPolicy delta hdelta) (k + 1))
  · exact SourceFiniteEdgeRevealState.measurableSet_nonnegativeCouplingEvent
  · exact SourceFiniteEdgeRevealState.couplingMeasure_real_nonnegativeCouplingEvent
  · dsimp only [S]
    rw [RootRadialSeedProfile.mixedExtensionPrefixStage_cellUnion]
    exact W.witnessedHistory_inter_nonnegative_eq_mixedExtensionPrefixSuccess
      hm hmn p radialIncremented delta hdelta hradialDelta
        (budgetedRootExtensionThresholdPolicy delta hdelta)
        (lower_le_budgetedRootExtensionThresholdPolicy delta hdelta)
        (W.budgetedPolicy_addsOnPrefixes
          p radialIncremented delta hdelta htotal)
        hgeom hk.le
  · dsimp only [S]
    exact RootRadialSeedProfile.mixedExtensionPrefixStage_successEvent_inter_nonnegative_eq
      hm hmn W p radialIncremented delta epsilon hdelta hradialDelta htotal
        huniform hnonempty hgeom hk

/-- Positive mass of a fixed-profile semantic prefix supplies one nonempty stable canonical
cell, exactly the classifier inhabitance needed at the next stage. -/
theorem RootRadialSeedProfile.nonempty_witnessedPrefixStateIndex_of_measure_pos
    {d m n : ℕ} [NeZero d] (hm : 1 ≤ m) (hmn : m + 1 < n)
    (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (delta : ℝ)
    (hdelta : 0 ≤ delta) (hradialDelta : delta = (radialIncremented : ℝ))
    (htotal : max (p : ℝ) (radialIncremented : ℝ) +
      ((rootExtensionDirectionOrder d).length : ℝ) * delta ≤ 1)
    (hgeom : ∀ a : CubicDirection d,
      SeedBoxWithinBoundaryLayer d a.1 m n (W a).seedCenter.1)
    {k : ℕ} (hk : k ≤ (rootExtensionDirectionOrder d).length)
    (hpos : 0 < (couplingMeasure (CubicEdge d)).real
      (W.mixedExtensionPrefixSuccessEvent p radialIncremented delta
        (budgetedRootExtensionThresholdPolicy delta hdelta) k)) :
    Nonempty (WitnessedRootExtensionPrefixStateIndex
      W p radialIncremented
        (budgetedRootExtensionThresholdPolicy delta hdelta) k
        (W.mixedExtensionPrefixSuccessEvent p radialIncremented delta
          (budgetedRootExtensionThresholdPolicy delta hdelta) k)) := by
  let A := W.mixedExtensionPrefixSuccessEvent p radialIncremented delta
    (budgetedRootExtensionThresholdPolicy delta hdelta) k
  have hinter : (couplingMeasure (CubicEdge d)).real
      (A ∩ SourceFiniteEdgeRevealState.nonnegativeCouplingEvent) =
      (couplingMeasure (CubicEdge d)).real A :=
    measureReal_inter_eq_of_measureReal_eq_one
      SourceFiniteEdgeRevealState.nonnegativeCouplingEvent A
      SourceFiniteEdgeRevealState.measurableSet_nonnegativeCouplingEvent
      SourceFiniteEdgeRevealState.couplingMeasure_real_nonnegativeCouplingEvent
  obtain ⟨X, hXA, hXNonnegative⟩ := MeasureTheory.nonempty_of_measureReal_ne_zero
    (μ := couplingMeasure (CubicEdge d))
    (s := A ∩ SourceFiniteEdgeRevealState.nonnegativeCouplingEvent)
    (by rw [hinter]; exact hpos.ne')
  have hWitnessed :=
    W.mixedExtensionPrefixSuccess_inter_nonnegative_subset_witnessedHistory
      hm hmn p radialIncremented delta hdelta hradialDelta
        (budgetedRootExtensionThresholdPolicy delta hdelta)
        (lower_le_budgetedRootExtensionThresholdPolicy delta hdelta)
        (W.budgetedPolicy_addsOnPrefixes p radialIncremented delta hdelta htotal)
        hgeom hk ⟨hXA, hXNonnegative⟩
  rw [RootRadialSeedProfile.witnessedRootExtensionPrefixHistory,
    Set.mem_iUnion] at hWitnessed
  obtain ⟨c, _hc⟩ := hWitnessed
  exact ⟨c⟩

/-- Iterating the automatically generated fixed-profile stages completes all `2d` post-radial
root restarts with positive probability. -/
theorem RootRadialSeedProfile.pow_mul_mixedRadialEvent_le_mixedExtensionCompletion
    {d m n : ℕ} [NeZero d] (hm : 1 ≤ m) (hmn : m + 1 < n)
    (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (delta epsilon : ℝ)
    (hdelta : 0 ≤ delta) (hradialDelta : delta = (radialIncremented : ℝ))
    (hepsilon : epsilon < 1)
    (htotal : max (p : ℝ) (radialIncremented : ℝ) +
      ((rootExtensionDirectionOrder d).length : ℝ) * delta ≤ 1)
    (huniform : UniformRestartBounds d m n p delta epsilon)
    (hgeom : ∀ a : CubicDirection d,
      SeedBoxWithinBoundaryLayer d a.1 m n (W a).seedCenter.1)
    (hmixed : 0 < (couplingMeasure (CubicEdge d)).real
      (W.mixedRadialEvent p delta)) :
    (1 - epsilon) ^ (rootExtensionDirectionOrder d).length *
        (couplingMeasure (CubicEdge d)).real (W.mixedRadialEvent p delta) ≤
      (couplingMeasure (CubicEdge d)).real
        (W.mixedExtensionPrefixSuccessEvent p radialIncremented delta
          (budgetedRootExtensionThresholdPolicy delta hdelta)
          (rootExtensionDirectionOrder d).length) := by
  have hprefixPos : ∀ k, k ≤ (rootExtensionDirectionOrder d).length →
      0 < (couplingMeasure (CubicEdge d)).real
        (W.mixedExtensionPrefixSuccessEvent p radialIncremented delta
          (budgetedRootExtensionThresholdPolicy delta hdelta) k) := by
    intro k hk
    induction k with
    | zero => simpa only [W.mixedExtensionPrefixSuccessEvent_zero] using hmixed
    | succ k ih =>
        have hklt : k < (rootExtensionDirectionOrder d).length := by omega
        have hpos := ih (by omega)
        have hnonempty := RootRadialSeedProfile.nonempty_witnessedPrefixStateIndex_of_measure_pos
          hm hmn W p radialIncremented delta hdelta hradialDelta htotal hgeom
            hklt.le hpos
        have hstep := RootRadialSeedProfile.mixedExtensionPrefixSuccess_measure_step
          hm hmn W p radialIncremented delta epsilon hdelta hradialDelta htotal
            huniform hnonempty hgeom hklt
        exact (mul_pos (sub_pos.mpr hepsilon) hpos).trans_le hstep
  have hpow := pow_mul_measureReal_le_of_step
    (mu := couplingMeasure (CubicEdge d))
    (fun k ↦ W.mixedExtensionPrefixSuccessEvent p radialIncremented delta
      (budgetedRootExtensionThresholdPolicy delta hdelta) k)
    (1 - epsilon) (sub_nonneg.mpr hepsilon.le)
    (rootExtensionDirectionOrder d).length
    (fun k hk ↦ RootRadialSeedProfile.mixedExtensionPrefixSuccess_measure_step
      hm hmn W p radialIncremented delta epsilon hdelta hradialDelta htotal
        huniform
        (RootRadialSeedProfile.nonempty_witnessedPrefixStateIndex_of_measure_pos
          hm hmn W p radialIncremented delta hdelta hradialDelta htotal hgeom
            hk.le (hprefixPos k hk.le))
        hgeom hk)
  simpa only [W.mixedExtensionPrefixSuccessEvent_zero] using hpow

/-- In the source-facing `2d` normalization, the complete fixed-profile root event has
positive mass. -/
theorem RootRadialSeedProfile.mixedExtensionCompletion_measure_pos
    {d m n : ℕ} [NeZero d] (hm : 1 ≤ m) (hmn : m + 1 < n)
    (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (delta epsilon : ℝ)
    (hdelta : 0 ≤ delta) (hradialDelta : delta = (radialIncremented : ℝ))
    (hepsilon : epsilon < 1)
    (htotal : max (p : ℝ) (radialIncremented : ℝ) +
      ((rootExtensionDirectionOrder d).length : ℝ) * delta ≤ 1)
    (huniform : UniformRestartBounds d m n p delta epsilon)
    (hgeom : ∀ a : CubicDirection d,
      SeedBoxWithinBoundaryLayer d a.1 m n (W a).seedCenter.1)
    (hmixed : 0 < (couplingMeasure (CubicEdge d)).real
      (W.mixedRadialEvent p delta)) :
    0 < (couplingMeasure (CubicEdge d)).real
      (W.mixedExtensionPrefixSuccessEvent p radialIncremented delta
        (budgetedRootExtensionThresholdPolicy delta hdelta) (2 * d)) := by
  have hbound := RootRadialSeedProfile.pow_mul_mixedRadialEvent_le_mixedExtensionCompletion
    hm hmn W p radialIncremented delta epsilon hdelta hradialDelta hepsilon
      htotal huniform hgeom hmixed
  rw [rootExtensionDirectionOrder_length] at hbound
  exact (mul_pos (pow_pos (sub_pos.mpr hepsilon) _) hmixed).trans_le hbound

/-- Every intermediate fixed-profile prefix has positive mass. -/
theorem RootRadialSeedProfile.mixedExtensionPrefix_measure_pos
    {d m n : ℕ} [NeZero d] (hm : 1 ≤ m) (hmn : m + 1 < n)
    (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (delta epsilon : ℝ)
    (hdelta : 0 ≤ delta) (hradialDelta : delta = (radialIncremented : ℝ))
    (hepsilon : epsilon < 1)
    (htotal : max (p : ℝ) (radialIncremented : ℝ) +
      ((rootExtensionDirectionOrder d).length : ℝ) * delta ≤ 1)
    (huniform : UniformRestartBounds d m n p delta epsilon)
    (hgeom : ∀ a : CubicDirection d,
      SeedBoxWithinBoundaryLayer d a.1 m n (W a).seedCenter.1)
    (hmixed : 0 < (couplingMeasure (CubicEdge d)).real
      (W.mixedRadialEvent p delta))
    (k : ℕ) (hk : k ≤ (rootExtensionDirectionOrder d).length) :
    0 < (couplingMeasure (CubicEdge d)).real
      (W.mixedExtensionPrefixSuccessEvent p radialIncremented delta
        (budgetedRootExtensionThresholdPolicy delta hdelta) k) := by
  induction k with
  | zero => simpa only [W.mixedExtensionPrefixSuccessEvent_zero] using hmixed
  | succ k ih =>
      have hklt : k < (rootExtensionDirectionOrder d).length := by omega
      have hpos := ih (by omega)
      have hnonempty := RootRadialSeedProfile.nonempty_witnessedPrefixStateIndex_of_measure_pos
        hm hmn W p radialIncremented delta hdelta hradialDelta htotal hgeom
          hklt.le hpos
      have hstep := RootRadialSeedProfile.mixedExtensionPrefixSuccess_measure_step
        hm hmn W p radialIncremented delta epsilon hdelta hradialDelta htotal
          huniform hnonempty hgeom hklt
      exact (mul_pos (sub_pos.mpr hepsilon) hpos).trans_le hstep

/-- Measurable completion event used to initialize the later coarse-site exploration.  The
semantic fixed-profile prefix need not itself be presented as a cylinder: the final concrete
partitioned stage is measurable, and intersecting it with the probability-one uniform support
makes its source semantics literal even on totalized junk labels. -/
noncomputable def RootRadialSeedProfile.mixedCompletedRootEvent
    {d m n : ℕ} [NeZero d] (hm : 1 ≤ m) (hmn : m + 1 < n)
    (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (delta epsilon : ℝ)
    (hdelta : 0 ≤ delta) (hradialDelta : delta = (radialIncremented : ℝ))
    (hepsilon : epsilon < 1)
    (htotal : max (p : ℝ) (radialIncremented : ℝ) +
      ((rootExtensionDirectionOrder d).length : ℝ) * delta ≤ 1)
    (huniform : UniformRestartBounds d m n p delta epsilon)
    (hgeom : ∀ a : CubicDirection d,
      SeedBoxWithinBoundaryLayer d a.1 m n (W a).seedCenter.1)
    (hmixed : 0 < (couplingMeasure (CubicEdge d)).real
      (W.mixedRadialEvent p delta)) : Set (CubicEdge d → ℝ) := by
  let k := 2 * d - 1
  have hk : k < (rootExtensionDirectionOrder d).length := by
    simp only [k, rootExtensionDirectionOrder_length]
    have hd : 0 < d := NeZero.pos d
    omega
  have hprefix := RootRadialSeedProfile.mixedExtensionPrefix_measure_pos
    hm hmn W p radialIncremented
    delta epsilon hdelta hradialDelta hepsilon htotal huniform hgeom hmixed k hk.le
  let hnonempty := RootRadialSeedProfile.nonempty_witnessedPrefixStateIndex_of_measure_pos
    hm hmn W p radialIncremented delta hdelta hradialDelta htotal hgeom hk.le hprefix
  exact (RootRadialSeedProfile.mixedExtensionPrefixStage hm hmn W p radialIncremented
    delta epsilon hdelta hradialDelta htotal huniform hnonempty hgeom hk).successEvent ∩
      SourceFiniteEdgeRevealState.nonnegativeCouplingEvent

theorem RootRadialSeedProfile.measurableSet_mixedCompletedRootEvent
    {d m n : ℕ} [NeZero d] (hm : 1 ≤ m) (hmn : m + 1 < n)
    (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (delta epsilon : ℝ)
    (hdelta : 0 ≤ delta) (hradialDelta : delta = (radialIncremented : ℝ))
    (hepsilon : epsilon < 1)
    (htotal : max (p : ℝ) (radialIncremented : ℝ) +
      ((rootExtensionDirectionOrder d).length : ℝ) * delta ≤ 1)
    (huniform : UniformRestartBounds d m n p delta epsilon)
    (hgeom : ∀ a : CubicDirection d,
      SeedBoxWithinBoundaryLayer d a.1 m n (W a).seedCenter.1)
    (hmixed : 0 < (couplingMeasure (CubicEdge d)).real
      (W.mixedRadialEvent p delta)) :
    MeasurableSet (RootRadialSeedProfile.mixedCompletedRootEvent hm hmn W p radialIncremented
      delta epsilon hdelta hradialDelta hepsilon htotal huniform hgeom hmixed) := by
  classical
  unfold RootRadialSeedProfile.mixedCompletedRootEvent
  apply MeasurableSet.inter
  · exact PartitionedFramedRestartStage.measurableSet_successEvent _
  · exact SourceFiniteEdgeRevealState.measurableSet_nonnegativeCouplingEvent

theorem RootRadialSeedProfile.mixedCompletedRootEvent_measure_pos
    {d m n : ℕ} [NeZero d] (hm : 1 ≤ m) (hmn : m + 1 < n)
    (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (delta epsilon : ℝ)
    (hdelta : 0 ≤ delta) (hradialDelta : delta = (radialIncremented : ℝ))
    (hepsilon : epsilon < 1)
    (htotal : max (p : ℝ) (radialIncremented : ℝ) +
      ((rootExtensionDirectionOrder d).length : ℝ) * delta ≤ 1)
    (huniform : UniformRestartBounds d m n p delta epsilon)
    (hgeom : ∀ a : CubicDirection d,
      SeedBoxWithinBoundaryLayer d a.1 m n (W a).seedCenter.1)
    (hmixed : 0 < (couplingMeasure (CubicEdge d)).real
      (W.mixedRadialEvent p delta)) :
    0 < (couplingMeasure (CubicEdge d)).real
      (RootRadialSeedProfile.mixedCompletedRootEvent hm hmn W p radialIncremented delta epsilon
        hdelta hradialDelta hepsilon htotal huniform hgeom hmixed) := by
  classical
  let k := 2 * d - 1
  have hk : k < (rootExtensionDirectionOrder d).length := by
    simp only [k, rootExtensionDirectionOrder_length]
    have hd : 0 < d := NeZero.pos d
    omega
  have hprefix := RootRadialSeedProfile.mixedExtensionPrefix_measure_pos
    hm hmn W p radialIncremented
    delta epsilon hdelta hradialDelta hepsilon htotal huniform hgeom hmixed k hk.le
  let hnonempty := RootRadialSeedProfile.nonempty_witnessedPrefixStateIndex_of_measure_pos
    hm hmn W p radialIncremented delta hdelta hradialDelta htotal hgeom hk.le hprefix
  have hfinal := RootRadialSeedProfile.mixedExtensionPrefix_measure_pos
    hm hmn W p radialIncremented
    delta epsilon hdelta hradialDelta hepsilon htotal huniform hgeom hmixed (2 * d)
      (by simp)
  have heq := RootRadialSeedProfile.mixedExtensionPrefixStage_successEvent_inter_nonnegative_eq
    hm hmn W p radialIncremented delta epsilon hdelta hradialDelta htotal huniform
      hnonempty hgeom hk
  have hsucc : k + 1 = 2 * d := by
    dsimp [k]
    have hd : 0 < d := NeZero.pos d
    omega
  rw [hsucc] at heq
  unfold RootRadialSeedProfile.mixedCompletedRootEvent
  rw [heq]
  rw [measureReal_inter_eq_of_measureReal_eq_one
    SourceFiniteEdgeRevealState.nonnegativeCouplingEvent
    (W.mixedExtensionPrefixSuccessEvent p radialIncremented delta
      (budgetedRootExtensionThresholdPolicy delta hdelta) (2 * d))
    SourceFiniteEdgeRevealState.measurableSet_nonnegativeCouplingEvent
    SourceFiniteEdgeRevealState.couplingMeasure_real_nonnegativeCouplingEvent]
  exact hfinal

end AdaptiveSiteExploration

end Percolation
