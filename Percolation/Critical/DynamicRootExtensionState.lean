import Percolation.Critical.DynamicRootSteeringGeometry
import Percolation.Critical.DynamicFramedSuccessStability

/-!
# Sequential post-radial root extensions

The simultaneous radial phase selects one concrete seed in every signed coordinate direction.
Grimmett then processes the resulting `2d` extensions in a fixed finite order.  This file runs
the literal changing-region source recursion in that order and proves that every prefix leaves
the next direction's target coordinates fresh.
-/

namespace Percolation

open scoped unitInterval

/-- A threshold policy may inspect the current interval state before assigning the incremented
thresholds for the next signed direction.  This is general enough for the source construction,
where the increment is applied to the current lower boundary profile. -/
abbrev RootExtensionThresholdPolicy (d : ℕ) :=
  SourceFiniteEdgeRevealState d → CubicDirection d → CubicEdge d → I

/-- Total canonical policy implementing Grimmett's update `beta(e) + delta`.  On a state with
the required budget it uses `revealThresholdIncrement`; on an unreachable budget-violating
junk state it leaves the threshold unchanged.  This makes the policy a total Lean function
without silently clamping a source threshold above one. -/
noncomputable def budgetedRootExtensionThresholdPolicy
    {d : ℕ} (delta : ℝ) (hdelta : 0 ≤ delta) : RootExtensionThresholdPolicy d := by
  classical
  exact fun S _a ↦
    if hbudget : S.HasIncrementBudget delta then
      revealThresholdIncrement S.lower delta hdelta hbudget
    else
      S.lower

theorem coe_budgetedRootExtensionThresholdPolicy_of_hasIncrementBudget
    {d : ℕ} (delta : ℝ) (hdelta : 0 ≤ delta)
    (S : SourceFiniteEdgeRevealState d) (a : CubicDirection d)
    (hbudget : S.HasIncrementBudget delta) (e : CubicEdge d) :
    (budgetedRootExtensionThresholdPolicy delta hdelta S a e : ℝ) =
      (S.lower e : ℝ) + delta := by
  classical
  simp [budgetedRootExtensionThresholdPolicy, hbudget,
    coe_revealThresholdIncrement]

/-- The total budgeted policy never exceeds the formal `lower + delta` update, including on
unreachable junk states where it leaves the old threshold unchanged. -/
theorem coe_budgetedRootExtensionThresholdPolicy_le_add
    {d : ℕ} (delta : ℝ) (hdelta : 0 ≤ delta)
    (S : SourceFiniteEdgeRevealState d) (a : CubicDirection d)
    (e : CubicEdge d) :
    (budgetedRootExtensionThresholdPolicy delta hdelta S a e : ℝ) ≤
      (S.lower e : ℝ) + delta := by
  classical
  by_cases hbudget : S.HasIncrementBudget delta
  · rw [coe_budgetedRootExtensionThresholdPolicy_of_hasIncrementBudget
      delta hdelta S a hbudget e]
  · simp [budgetedRootExtensionThresholdPolicy, hbudget,
      le_add_of_nonneg_right hdelta]

theorem lower_le_budgetedRootExtensionThresholdPolicy_of_hasIncrementBudget
    {d : ℕ} (delta : ℝ) (hdelta : 0 ≤ delta)
    (S : SourceFiniteEdgeRevealState d) (a : CubicDirection d)
    (hbudget : S.HasIncrementBudget delta) (e : CubicEdge d) :
    S.lower e ≤ budgetedRootExtensionThresholdPolicy delta hdelta S a e := by
  rw [← Subtype.coe_le_coe]
  rw [coe_budgetedRootExtensionThresholdPolicy_of_hasIncrementBudget
    delta hdelta S a hbudget e]
  exact le_add_of_nonneg_right hdelta

/-- The total budgeted policy is monotone even on unreachable junk states: when the budget
proof is unavailable it leaves the old lower threshold unchanged. -/
theorem lower_le_budgetedRootExtensionThresholdPolicy
    {d : ℕ} (delta : ℝ) (hdelta : 0 ≤ delta)
    (S : SourceFiniteEdgeRevealState d) (a : CubicDirection d) (e : CubicEdge d) :
    S.lower e ≤ budgetedRootExtensionThresholdPolicy delta hdelta S a e := by
  classical
  by_cases hbudget : S.HasIncrementBudget delta
  · exact lower_le_budgetedRootExtensionThresholdPolicy_of_hasIncrementBudget
      delta hdelta S a hbudget e
  · simp [budgetedRootExtensionThresholdPolicy, hbudget]

/-! ### Finite-pattern stability of the simultaneous radial history -/

/-- Agreement of the background-density threshold pattern on the radial support preserves the
central seed event. -/
theorem rootSeedLabelEvent_congr_of_labelsBelow_rootRadialEdgeSupport
    {d m n : ℕ} {p : I} {X Y : CubicEdge d → ℝ}
    (hp : FiniteRevealIntervalProfile.labelsBelow
        (rootRadialEdgeSupport d m n) p X =
      FiniteRevealIntervalProfile.labelsBelow
        (rootRadialEdgeSupport d m n) p Y) :
    X ∈ rootSeedLabelEvent d m p ↔ Y ∈ rootSeedLabelEvent d m p := by
  have hpIff := (FiniteRevealIntervalProfile.labelsBelow_eq_iff
    (rootRadialEdgeSupport d m n) p X Y).mp hp
  change (∀ e ∈ cubicBoxEdges d cubicOrigin m, X e < (p : ℝ)) ↔
    ∀ e ∈ cubicBoxEdges d cubicOrigin m, Y e < (p : ℝ)
  constructor
  · intro h e he
    exact (hpIff e (Finset.mem_union_left _ (Finset.mem_union_left _ he))).mp (h e he)
  · intro h e he
    exact (hpIff e (Finset.mem_union_left _ (Finset.mem_union_left _ he))).mpr (h e he)

/-- A simultaneous radial branch is determined by two finite Boolean patterns: background
`p`-openness throughout its support and increment-openness on its old boundary. -/
theorem rootBranchSuccessEvent_congr_of_labelsBelow_rootRadialEdgeSupport
    {d m n : ℕ} (a : CubicDirection d) {p radialIncremented : I}
    {delta : ℝ} (hdelta : delta = (radialIncremented : ℝ))
    {X Y : CubicEdge d → ℝ}
    (hp : FiniteRevealIntervalProfile.labelsBelow
        (rootRadialEdgeSupport d m n) p X =
      FiniteRevealIntervalProfile.labelsBelow
        (rootRadialEdgeSupport d m n) p Y)
    (hincremented : FiniteRevealIntervalProfile.labelsBelow
        (rootRadialEdgeSupport d m n) radialIncremented X =
      FiniteRevealIntervalProfile.labelsBelow
        (rootRadialEdgeSupport d m n) radialIncremented Y) :
    X ∈ rootBranchSuccessEvent d m n p delta a ↔
      Y ∈ rootBranchSuccessEvent d m n p delta a := by
  classical
  let F := cubicRestartFrameIso cubicOrigin a (rootRadialTransverseFlip a)
  have hpIff := (FiniteRevealIntervalProfile.labelsBelow_eq_iff
    (rootRadialEdgeSupport d m n) p X Y).mp hp
  have hincrementedIff := (FiniteRevealIntervalProfile.labelsBelow_eq_iff
    (rootRadialEdgeSupport d m n) radialIncremented X Y).mp hincremented
  change cubicGraphIsoCouplingReindex F X ∈
      sprinkledRestartEvent d a.1 m n (cubicMetricBox d cubicOrigin m)
        p (fun _ ↦ 0) delta ↔
    cubicGraphIsoCouplingReindex F Y ∈
      sprinkledRestartEvent d a.1 m n (cubicMetricBox d cubicOrigin m)
        p (fun _ ↦ 0) delta
  apply sprinkledRestartEvent_congr_of_thresholdIffOn_restartEventSupport
  · intro e heSupport
    have hePhysicalBranch : F.mapEdgeSet e ∈
        (rootBranchQuery d m a).restartSupport m n := by
      exact Finset.mem_image.mpr ⟨e, heSupport, rfl⟩
    have hePhysical : F.mapEdgeSet e ∈ rootRadialEdgeSupport d m n := by
      apply Finset.mem_union_right
      rw [Finset.mem_biUnion]
      exact ⟨a, Finset.mem_univ a, hePhysicalBranch⟩
    simpa [cubicGraphIsoCouplingReindex, couplingReindex] using
      hpIff (F.mapEdgeSet e) hePhysical
  · intro e heBoundary
    have heSupport : e ∈ restartEventSupport d a.1 m n
        (cubicMetricBox d cubicOrigin m) :=
      boundary_subset_restartEventSupport d a.1 m n
        (cubicMetricBox d cubicOrigin m) heBoundary
    have hePhysicalBranch : F.mapEdgeSet e ∈
        (rootBranchQuery d m a).restartSupport m n := by
      exact Finset.mem_image.mpr ⟨e, heSupport, rfl⟩
    have hePhysical : F.mapEdgeSet e ∈ rootRadialEdgeSupport d m n := by
      apply Finset.mem_union_right
      rw [Finset.mem_biUnion]
      exact ⟨a, Finset.mem_univ a, hePhysicalBranch⟩
    simpa [hdelta, cubicGraphIsoCouplingReindex, couplingReindex] using
      hincrementedIff (F.mapEdgeSet e) hePhysical

/-- Consequently the complete radial-success event is constant on every pair of exact
background/increment threshold-pattern fibers. -/
theorem rootRadialEvent_congr_of_labelsBelow_rootRadialEdgeSupport
    {d m n : ℕ} {p radialIncremented : I} {delta : ℝ}
    (hdelta : delta = (radialIncremented : ℝ)) {X Y : CubicEdge d → ℝ}
    (hp : FiniteRevealIntervalProfile.labelsBelow
        (rootRadialEdgeSupport d m n) p X =
      FiniteRevealIntervalProfile.labelsBelow
        (rootRadialEdgeSupport d m n) p Y)
    (hincremented : FiniteRevealIntervalProfile.labelsBelow
        (rootRadialEdgeSupport d m n) radialIncremented X =
      FiniteRevealIntervalProfile.labelsBelow
        (rootRadialEdgeSupport d m n) radialIncremented Y) :
    X ∈ rootRadialEvent d m n p delta ↔
      Y ∈ rootRadialEvent d m n p delta := by
  constructor
  · rintro ⟨hseed, hbranches⟩
    refine ⟨(rootSeedLabelEvent_congr_of_labelsBelow_rootRadialEdgeSupport hp).mp hseed, ?_⟩
    apply Set.mem_iInter.mpr
    intro a
    exact (rootBranchSuccessEvent_congr_of_labelsBelow_rootRadialEdgeSupport
      a hdelta hp hincremented).mp (Set.mem_iInter.mp hbranches a)
  · rintro ⟨hseed, hbranches⟩
    refine ⟨(rootSeedLabelEvent_congr_of_labelsBelow_rootRadialEdgeSupport hp).mpr hseed, ?_⟩
    apply Set.mem_iInter.mpr
    intro a
    exact (rootBranchSuccessEvent_congr_of_labelsBelow_rootRadialEdgeSupport
      a hdelta hp hincremented).mpr (Set.mem_iInter.mp hbranches a)

/-- Every coordinate used to select a radial seed is present in the simultaneous physical
radial support.  Internal central-box edges use `E₁`; every other coordinate belongs to the
branch restart support. -/
theorem mapEdgeSet_mem_rootRadialEdgeSupport_of_mem_seedConnectionSupport
    {d m n : ℕ} (a : CubicDirection d) {e : CubicEdge d}
    (he : e ∈ seedConnectionSupport d a.1 m n) :
    (cubicRestartFrameIso cubicOrigin a (rootRadialTransverseFlip a)).mapEdgeSet e ∈
      rootRadialEdgeSupport d m n := by
  classical
  let F := cubicRestartFrameIso cubicOrigin a (rootRadialTransverseFlip a)
  by_cases heInitial : e ∈ cubicBoxEdges d cubicOrigin m
  · apply Finset.mem_union_left
    apply Finset.mem_union_left
    have heImage : F.mapEdgeSet e ∈
        (cubicBoxEdges d cubicOrigin m).image F.mapEdgeSet :=
      Finset.mem_image.mpr ⟨e, heInitial, rfl⟩
    rw [show (cubicBoxEdges d cubicOrigin m).image F.mapEdgeSet =
        cubicBoxEdges d cubicOrigin m by
      simpa [F] using cubicRestartFrameIso_image_cubicBoxEdges_eq
        (n := m) cubicOrigin a (rootRadialTransverseFlip a)] at heImage
    exact heImage
  · have heRestart : e ∈ restartEventSupport d a.1 m n
        (cubicMetricBox d cubicOrigin m) := by
      by_cases heBox : e ∈ cubicBoxEdges d cubicOrigin n
      · by_cases hfst : e.1.out.1 ∈ cubicMetricBox d cubicOrigin m
        · have hsnd : e.1.out.2 ∉ cubicMetricBox d cubicOrigin m := by
            intro hsnd
            exact heInitial (mem_cubicBoxEdges_of_endpoints fun z hz ↦ by
              rw [← e.1.out_eq, Sym2.mem_iff] at hz
              exact hz.elim (fun h ↦ h ▸ hfst) (fun h ↦ h ▸ hsnd))
          apply boundary_subset_restartEventSupport d a.1 m n
          exact mem_cubicRegionBoundaryEdgesWithinBox_of_endpoints heBox
            (Sym2.out_fst_mem e.1) (Sym2.out_snd_mem e.1) hfst hsnd
        · by_cases hsnd : e.1.out.2 ∈ cubicMetricBox d cubicOrigin m
          · apply boundary_subset_restartEventSupport d a.1 m n
            exact mem_cubicRegionBoundaryEdgesWithinBox_of_endpoints heBox
              (Sym2.out_snd_mem e.1) (Sym2.out_fst_mem e.1) hsnd hfst
          · apply exterior_subset_restartEventSupport d a.1 m n
            rw [mem_cubicRegionExteriorEdgesWithinBox_iff]
            refine ⟨heBox, ?_⟩
            intro z hz
            rw [← e.1.out_eq, Sym2.mem_iff] at hz
            exact hz.elim (fun h ↦ h ▸ hfst) (fun h ↦ h ▸ hsnd)
      · apply target_subset_restartEventSupport d a.1 m n
        exact Finset.mem_sdiff.mpr ⟨he, heBox⟩
    apply Finset.mem_union_right
    rw [Finset.mem_biUnion]
    refine ⟨a, Finset.mem_univ a, ?_⟩
    exact Finset.mem_image.mpr ⟨e, heRestart, rfl⟩

/-- The canonical seed chosen by one radial branch is also determined by the final-density
threshold pattern on the same finite radial support. -/
theorem rootRadialSelectedSeed_congr_of_labelsBelow_rootRadialEdgeSupport
    {d m n : ℕ} (a : CubicDirection d) {pFinal : I}
    {X Y : CubicEdge d → ℝ}
    (hpFinal : FiniteRevealIntervalProfile.labelsBelow
        (rootRadialEdgeSupport d m n) pFinal X =
      FiniteRevealIntervalProfile.labelsBelow
        (rootRadialEdgeSupport d m n) pFinal Y) :
    rootRadialSelectedSeed d m n pFinal a X =
      rootRadialSelectedSeed d m n pFinal a Y := by
  classical
  let F := cubicRestartFrameIso cubicOrigin a (rootRadialTransverseFlip a)
  have hpFinalIff := (FiniteRevealIntervalProfile.labelsBelow_eq_iff
    (rootRadialEdgeSupport d m n) pFinal X Y).mp hpFinal
  unfold rootRadialSelectedSeed
  apply selectedRestartSeedWitness_congr_of_eqOn_seedConnectionSupport
  intro e heSupport
  have hePhysical : F.mapEdgeSet e ∈ rootRadialEdgeSupport d m n := by
    exact mapEdgeSet_mem_rootRadialEdgeSupport_of_mem_seedConnectionSupport a heSupport
  simpa [thresholdConfiguration, cubicGraphIsoCouplingReindex, couplingReindex] using
    hpFinalIff (F.mapEdgeSet e) hePhysical

/-- A coordinate of the finite simultaneous radial support. -/
abbrev RootRadialSupportCoordinate (d m n : ℕ) :=
  {e : CubicEdge d // e ∈ rootRadialEdgeSupport d m n}

noncomputable instance rootRadialSupportCoordinateFintype (d m n : ℕ) :
    Fintype (RootRadialSupportCoordinate d m n) :=
  Fintype.ofFinite _

/-- One exact finite `< q` pattern on the radial support. -/
abbrev RootRadialThresholdPattern (d m n : ℕ) :=
  Finset (RootRadialSupportCoordinate d m n)

/-- Forget the support-membership proofs in a radial threshold pattern. -/
noncomputable def RootRadialThresholdPattern.physical
    {d m n : ℕ} (A : RootRadialThresholdPattern d m n) : Finset (CubicEdge d) :=
  A.map (Function.Embedding.subtype _)

theorem RootRadialThresholdPattern.physical_subset
    {d m n : ℕ} (A : RootRadialThresholdPattern d m n) :
    A.physical ⊆ rootRadialEdgeSupport d m n := by
  intro e he
  rw [RootRadialThresholdPattern.physical, Finset.mem_map] at he
  obtain ⟨e', _heA, rfl⟩ := he
  exact e'.2

/-- Threshold pattern actually realized by a label configuration. -/
noncomputable def realizedRootRadialThresholdPattern
    (d m n : ℕ) (q : I) (X : CubicEdge d → ℝ) :
    RootRadialThresholdPattern d m n := by
  classical
  exact Finset.univ.filter fun e ↦ X e.1 < (q : ℝ)

theorem physical_realizedRootRadialThresholdPattern
    (d m n : ℕ) (q : I) (X : CubicEdge d → ℝ) :
    (realizedRootRadialThresholdPattern d m n q X).physical =
      FiniteRevealIntervalProfile.labelsBelow
        (rootRadialEdgeSupport d m n) q X := by
  classical
  ext e
  rw [FiniteRevealIntervalProfile.mem_labelsBelow_iff]
  constructor
  · intro he
    rw [RootRadialThresholdPattern.physical, Finset.mem_map] at he
    obtain ⟨e', hePattern, rfl⟩ := he
    have heOpen : X e'.1 < (q : ℝ) := by
      simpa [realizedRootRadialThresholdPattern] using hePattern
    exact ⟨e'.2, heOpen⟩
  · rintro ⟨heSupport, heOpen⟩
    rw [RootRadialThresholdPattern.physical, Finset.mem_map]
    refine ⟨⟨e, heSupport⟩, ?_, rfl⟩
    simpa [realizedRootRadialThresholdPattern] using heOpen

/-- Run the literal source recursion through a supplied list of post-radial root directions.
The finite stage region at each step is the actual framed restart support extracted from the
current state, not a precomputed ambient box. -/
noncomputable def RootRadialSeedProfile.runPostRadialExtensions
    {d m n : ℕ} (W : RootRadialSeedProfile d m n) (p : I)
    (incremented : RootExtensionThresholdPolicy d) (X : CubicEdge d → ℝ)
    (S : SourceFiniteEdgeRevealState d) :
    List (CubicDirection d) → SourceFiniteEdgeRevealState d
  | [] => S
  | b :: rest =>
      let Q := S.framedQuery (W.physicalCenter b) b
        (oppositeTransverseRestartFlip b)
      W.runPostRadialExtensions p incremented X
        (S.next (Q.restartSupport m n) p (incremented S b) X) rest

@[simp]
theorem RootRadialSeedProfile.runPostRadialExtensions_nil
    {d m n : ℕ} (W : RootRadialSeedProfile d m n) (p : I)
    (incremented : RootExtensionThresholdPolicy d) (X : CubicEdge d → ℝ)
    (S : SourceFiniteEdgeRevealState d) :
    W.runPostRadialExtensions p incremented X S [] = S :=
  rfl

@[simp]
theorem RootRadialSeedProfile.runPostRadialExtensions_cons
    {d m n : ℕ} (W : RootRadialSeedProfile d m n) (p : I)
    (incremented : RootExtensionThresholdPolicy d) (X : CubicEdge d → ℝ)
    (S : SourceFiniteEdgeRevealState d) (b : CubicDirection d)
    (rest : List (CubicDirection d)) :
    W.runPostRadialExtensions p incremented X S (b :: rest) =
      let Q := S.framedQuery (W.physicalCenter b) b
        (oppositeTransverseRestartFlip b)
      W.runPostRadialExtensions p incremented X
        (S.next (Q.restartSupport m n) p (incremented S b) X) rest :=
  rfl

/-- The literal source recursion only adds explored edges. -/
theorem RootRadialSeedProfile.explored_subset_runPostRadialExtensions
    {d m n : ℕ} (W : RootRadialSeedProfile d m n) (p : I)
    (incremented : RootExtensionThresholdPolicy d) (X : CubicEdge d → ℝ)
    (S : SourceFiniteEdgeRevealState d) (directions : List (CubicDirection d)) :
    S.explored ⊆
      (W.runPostRadialExtensions p incremented X S directions).explored := by
  induction directions generalizing S with
  | nil => exact Finset.Subset.rfl
  | cons b rest ih =>
      let Q := S.framedQuery (W.physicalCenter b) b
        (oppositeTransverseRestartFlip b)
      let S' := S.next (Q.restartSupport m n) p (incremented S b) X
      exact (S.explored_subset_nextExplored
        (Q.restartSupport m n) p (incremented S b) X).trans
          (ih (S := S'))

/-- Under the total budgeted policy, every source step can increase the uniform lower-threshold
bound by at most `delta`; a newly created boundary receives density `p`, already assumed below
the incoming bound. -/
theorem RootRadialSeedProfile.coe_runPostRadialExtensions_budgeted_lower_le
    {d m n : ℕ} (W : RootRadialSeedProfile d m n) (p : I)
    (delta : ℝ) (hdelta : 0 ≤ delta) (X : CubicEdge d → ℝ)
    (S : SourceFiniteEdgeRevealState d) (directions : List (CubicDirection d))
    (B : ℝ) (hlower : ∀ e, (S.lower e : ℝ) ≤ B)
    (hp : (p : ℝ) ≤ B) (e : CubicEdge d) :
    ((W.runPostRadialExtensions p
      (budgetedRootExtensionThresholdPolicy delta hdelta) X S directions).lower e : ℝ) ≤
      B + (directions.length : ℝ) * delta := by
  induction directions generalizing S B with
  | nil => simpa using hlower e
  | cons b rest ih =>
      let Q := S.framedQuery (W.physicalCenter b) b
        (oppositeTransverseRestartFlip b)
      let S' := S.next (Q.restartSupport m n) p
        (budgetedRootExtensionThresholdPolicy delta hdelta S b) X
      have hlower' : ∀ f, (S'.lower f : ℝ) ≤ B + delta := by
        intro f
        apply S.coe_next_lower_le_of_le
        · intro g
          exact (hlower g).trans (le_add_of_nonneg_right hdelta)
        · intro g
          exact (coe_budgetedRootExtensionThresholdPolicy_le_add
            delta hdelta S b g).trans (by linarith [hlower g])
        · exact hp.trans (le_add_of_nonneg_right hdelta)
      have hp' : (p : ℝ) ≤ B + delta :=
        hp.trans (le_add_of_nonneg_right hdelta)
      have hrest := ih S' (B + delta) hlower' hp'
      change
        ((W.runPostRadialExtensions p
          (budgetedRootExtensionThresholdPolicy delta hdelta) X S' rest).lower e : ℝ) ≤
          B + ((b :: rest).length : ℝ) * delta
      calc
        ((W.runPostRadialExtensions p
          (budgetedRootExtensionThresholdPolicy delta hdelta) X S' rest).lower e : ℝ) ≤
            (B + delta) + (rest.length : ℝ) * delta := hrest
        _ = B + ((b :: rest).length : ℝ) * delta := by
          simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
          ring

/-- Running the source recursion through an appended direction list is literal sequential
composition. -/
theorem RootRadialSeedProfile.runPostRadialExtensions_append
    {d m n : ℕ} (W : RootRadialSeedProfile d m n) (p : I)
    (incremented : RootExtensionThresholdPolicy d) (X : CubicEdge d → ℝ)
    (S : SourceFiniteEdgeRevealState d) (first second : List (CubicDirection d)) :
    W.runPostRadialExtensions p incremented X S (first ++ second) =
      W.runPostRadialExtensions p incremented X
        (W.runPostRadialExtensions p incremented X S first) second := by
  induction first generalizing S with
  | nil => rfl
  | cons b rest ih =>
      simp only [List.cons_append, W.runPostRadialExtensions_cons]
      exact ih _

/-- Literal conjunction of successful framed restarts along a supplied source-state schedule. -/
def RootRadialSeedProfile.runPostRadialExtensionSuccesses
    {d m n : ℕ} (W : RootRadialSeedProfile d m n) (p : I) (delta : ℝ)
    (incremented : RootExtensionThresholdPolicy d) (X : CubicEdge d → ℝ)
    (S : SourceFiniteEdgeRevealState d) : List (CubicDirection d) → Prop
  | [] => True
  | b :: rest =>
      let Q := S.framedQuery (W.physicalCenter b) b
        (oppositeTransverseRestartFlip b)
      X ∈ Q.successEvent m n p delta ∧
        W.runPostRadialExtensionSuccesses p delta incremented X
          (S.next (Q.restartSupport m n) p (incremented S b) X) rest

@[simp]
theorem RootRadialSeedProfile.runPostRadialExtensionSuccesses_nil
    {d m n : ℕ} (W : RootRadialSeedProfile d m n) (p : I) (delta : ℝ)
    (incremented : RootExtensionThresholdPolicy d) (X : CubicEdge d → ℝ)
    (S : SourceFiniteEdgeRevealState d) :
    W.runPostRadialExtensionSuccesses p delta incremented X S [] :=
  trivial

@[simp]
theorem RootRadialSeedProfile.runPostRadialExtensionSuccesses_cons
    {d m n : ℕ} (W : RootRadialSeedProfile d m n) (p : I) (delta : ℝ)
    (incremented : RootExtensionThresholdPolicy d) (X : CubicEdge d → ℝ)
    (S : SourceFiniteEdgeRevealState d) (b : CubicDirection d)
    (rest : List (CubicDirection d)) :
    W.runPostRadialExtensionSuccesses p delta incremented X S (b :: rest) ↔
      let Q := S.framedQuery (W.physicalCenter b) b
        (oppositeTransverseRestartFlip b)
      X ∈ Q.successEvent m n p delta ∧
        W.runPostRadialExtensionSuccesses p delta incremented X
          (S.next (Q.restartSupport m n) p (incremented S b) X) rest :=
  Iff.rfl

/-- Success along an appended schedule is success along the first schedule followed by success
from its literal terminal state. -/
theorem RootRadialSeedProfile.runPostRadialExtensionSuccesses_append
    {d m n : ℕ} (W : RootRadialSeedProfile d m n) (p : I) (delta : ℝ)
    (incremented : RootExtensionThresholdPolicy d) (X : CubicEdge d → ℝ)
    (S : SourceFiniteEdgeRevealState d) (first second : List (CubicDirection d)) :
    W.runPostRadialExtensionSuccesses p delta incremented X S (first ++ second) ↔
      W.runPostRadialExtensionSuccesses p delta incremented X S first ∧
        W.runPostRadialExtensionSuccesses p delta incremented X
          (W.runPostRadialExtensions p incremented X S first) second := by
  induction first generalizing S with
  | nil => simp
  | cons b rest ih =>
      simp only [List.cons_append, W.runPostRadialExtensionSuccesses_cons,
        W.runPostRadialExtensions_cons]
      rw [ih]
      tauto

/-- Exact interval-profile preservation through the state-dependent post-radial root
schedule.  The finite support at slot `j` is computed from the actual prefix state, so this
cannot be reduced definitionally to `SourceFiniteEdgeRevealState.run`.  As in the underlying
source recursion, the only extra realization premise is nonnegativity on the newly exposed
global boundary. -/
theorem RootRadialSeedProfile.mem_runPostRadialExtensions_profile
    {d m n : ℕ} (W : RootRadialSeedProfile d m n) (p : I)
    (incremented : RootExtensionThresholdPolicy d) (X : CubicEdge d → ℝ)
    (directions : List (CubicDirection d)) (S : SourceFiniteEdgeRevealState d)
    (hnonneg : ∀ j (hj : j < directions.length),
      let state := W.runPostRadialExtensions p incremented X S (directions.take j)
      let b := directions[j]
      let Q := state.framedQuery (W.physicalCenter b) b
        (oppositeTransverseRestartFlip b)
      X ∈ SourceFiniteEdgeRevealState.nonnegativeBoundaryEvent
        (cubicEdgeBoundary
          (state.nextExplored (Q.restartSupport m n) p (incremented state b) X)))
    (hcurrent : X ∈ S.profile.event) :
    X ∈ (W.runPostRadialExtensions p incremented X S directions).profile.event := by
  induction directions generalizing S with
  | nil => exact hcurrent
  | cons b rest ih =>
      let Q := S.framedQuery (W.physicalCenter b) b
        (oppositeTransverseRestartFlip b)
      let S' := S.next (Q.restartSupport m n) p (incremented S b) X
      have hfirst : X ∈ SourceFiniteEdgeRevealState.nonnegativeBoundaryEvent
          (cubicEdgeBoundary
            (S.nextExplored (Q.restartSupport m n) p (incremented S b) X)) := by
        simpa [Q] using hnonneg 0 (by simp)
      apply ih (S := S')
      · intro j hj
        have hs := hnonneg (j + 1) (by simp; omega)
        simpa [List.take_succ_cons, Q, S', RootRadialSeedProfile.runPostRadialExtensions]
          using hs
      · exact S.mem_next_profile_of_mem_nonnegativeBoundaryEvent
          (Q.restartSupport m n) p (incremented S b) X hcurrent hfirst

/-- Exact accumulated-history preservation through the state-dependent root schedule on the
single probability-one common-uniform support. -/
theorem RootRadialSeedProfile.mem_runPostRadialExtensions_historyProfile
    {d m n : ℕ} (W : RootRadialSeedProfile d m n) (p : I)
    (incremented : RootExtensionThresholdPolicy d) (X : CubicEdge d → ℝ)
    (directions : List (CubicDirection d)) (S : SourceFiniteEdgeRevealState d)
    (hnonneg : X ∈ SourceFiniteEdgeRevealState.nonnegativeCouplingEvent)
    (hcurrent : X ∈ S.historyProfile.event) :
    X ∈ (W.runPostRadialExtensions p incremented X S directions).historyProfile.event := by
  induction directions generalizing S with
  | nil => exact hcurrent
  | cons b rest ih =>
      let Q := S.framedQuery (W.physicalCenter b) b
        (oppositeTransverseRestartFlip b)
      exact ih (S := S.next (Q.restartSupport m n) p (incremented S b) X)
        (S.mem_next_historyProfile (Q.restartSupport m n) p (incremented S b) X
          hcurrent hnonneg)

/-- A state-dependent post-radial root schedule has finite state range whenever its incoming
state does.  Each step branches only through the finite powerset of its concrete restart
support. -/
theorem RootRadialSeedProfile.finite_range_runPostRadialExtensions
    {d m n : ℕ} (W : RootRadialSeedProfile d m n) (p : I)
    (incremented : RootExtensionThresholdPolicy d)
    (state : (CubicEdge d → ℝ) → SourceFiniteEdgeRevealState d)
    (directions : List (CubicDirection d))
    (hstate : (Set.range state).Finite) :
    (Set.range fun X ↦
      W.runPostRadialExtensions p incremented X (state X) directions).Finite := by
  induction directions generalizing state with
  | nil => simpa using hstate
  | cons b rest ih =>
      let nextState : (CubicEdge d → ℝ) → SourceFiniteEdgeRevealState d := fun X ↦
        let S := state X
        let Q := S.framedQuery (W.physicalCenter b) b
          (oppositeTransverseRestartFlip b)
        S.next (Q.restartSupport m n) p (incremented S b) X
      have hnext : (Set.range nextState).Finite := by
        apply SourceFiniteEdgeRevealState.finite_range_next_of_finite_range
          state
          (fun S ↦ (S.framedQuery (W.physicalCenter b) b
            (oppositeTransverseRestartFlip b)).restartSupport m n)
          p (fun S ↦ incremented S b) hstate
      simpa [RootRadialSeedProfile.runPostRadialExtensions, nextState] using
        ih nextState hnext

/-- Under a monotone threshold policy, the final accumulated-history cell of a root schedule
refines the incoming history cell. -/
theorem RootRadialSeedProfile.runPostRadialExtensions_historyProfile_event_subset
    {d m n : ℕ} (W : RootRadialSeedProfile d m n) (p : I)
    (incremented : RootExtensionThresholdPolicy d)
    (hincremented : ∀ S b e, S.lower e ≤ incremented S b e)
    (X : CubicEdge d → ℝ) (S : SourceFiniteEdgeRevealState d)
    (directions : List (CubicDirection d)) :
    (W.runPostRadialExtensions p incremented X S directions).historyProfile.event ⊆
      S.historyProfile.event := by
  induction directions generalizing S with
  | nil => exact Set.Subset.rfl
  | cons b rest ih =>
      let Q := S.framedQuery (W.physicalCenter b) b
        (oppositeTransverseRestartFlip b)
      let S' := S.next (Q.restartSupport m n) p (incremented S b) X
      exact (ih (S := S')).trans
        (S.next_historyProfile_event_subset_historyProfile_event
          (Q.restartSupport m n) p (incremented S b) X (hincremented S b))

/-- Every preceding successful restart remains true throughout the accumulated-history cell
at the end of the supplied direction list.  This is the semantic induction invariant needed
for exact root-prefix partitions. -/
theorem RootRadialSeedProfile.runPostRadialExtensionSuccesses_of_mem_historyProfile
    {d m n : ℕ} (W : RootRadialSeedProfile d m n) (p : I) (delta : ℝ)
    (incremented : RootExtensionThresholdPolicy d)
    (hmono : ∀ S b e, S.lower e ≤ incremented S b e)
    (X Y : CubicEdge d → ℝ) (S : SourceFiniteEdgeRevealState d)
    (directions : List (CubicDirection d))
    (hadds : ∀ j (hj : j < directions.length) e,
      let state := W.runPostRadialExtensions p incremented X S (directions.take j)
      let b := directions[j]
      (incremented state b e : ℝ) = (state.lower e : ℝ) + delta)
    (hfresh : ∀ j (hj : j < directions.length),
      let state := W.runPostRadialExtensions p incremented X S (directions.take j)
      let b := directions[j]
      let F := cubicRestartFrameIso (W.physicalCenter b) b
        (oppositeTransverseRestartFlip b)
      Disjoint (cubicEdgeEndpointVertices (state.referenceExploredEdges F))
        (cubicEdgeEndpointVertices (seededBoundaryTargetSupport d b.1 m n)))
    (hsuccess : W.runPostRadialExtensionSuccesses
      p delta incremented X S directions)
    (hY : Y ∈ (W.runPostRadialExtensions
      p incremented X S directions).historyProfile.event) :
    W.runPostRadialExtensionSuccesses p delta incremented Y S directions := by
  induction directions generalizing S with
  | nil => trivial
  | cons b rest ih =>
      let Q := S.framedQuery (W.physicalCenter b) b
        (oppositeTransverseRestartFlip b)
      let SX := S.next (Q.restartSupport m n) p (incremented S b) X
      let SY := S.next (Q.restartSupport m n) p (incremented S b) Y
      have hYnext : Y ∈ SX.historyProfile.event := by
        exact W.runPostRadialExtensions_historyProfile_event_subset
          p incremented hmono X SX rest hY
      have hfreshFirst :
          let F := cubicRestartFrameIso (W.physicalCenter b) b
            (oppositeTransverseRestartFlip b)
          Disjoint (cubicEdgeEndpointVertices (S.referenceExploredEdges F))
            (cubicEdgeEndpointVertices (seededBoundaryTargetSupport d b.1 m n)) := by
        simpa using hfresh 0 (by simp)
      have hfirstY : Y ∈ Q.successEvent m n p delta := by
        apply S.framedSuccessEvent_of_mem_nextHistoryProfile
          (W.physicalCenter b) b (oppositeTransverseRestartFlip b)
          p delta (incremented S b) X Y hfreshFirst
        · intro e _he
          rw [S.framedQuery_physicalBoundaryThreshold]
          simpa using hadds 0 (by simp) e
        · exact hsuccess.1
        · exact hYnext
      have hstate : SY = SX := by
        exact S.next_eq_of_mem_next_historyProfile
          (Q.restartSupport m n) p (incremented S b) X Y hYnext
      refine ⟨hfirstY, ?_⟩
      change W.runPostRadialExtensionSuccesses p delta incremented Y SY rest
      rw [hstate]
      apply ih SX
      · intro j hj e
        have hs := hadds (j + 1) (by simp; omega) e
        simpa [List.take_succ_cons, Q, SX,
          RootRadialSeedProfile.runPostRadialExtensions] using hs
      · intro j hj
        have hs := hfresh (j + 1) (by simp; omega)
        simpa [List.take_succ_cons, Q, SX,
          RootRadialSeedProfile.runPostRadialExtensions] using hs
      · exact hsuccess.2
      · exact hY

/-- Every realization in the final history cell reproduces the entire state-dependent root
schedule.  This makes distinct reachable final states have disjoint history cells. -/
theorem RootRadialSeedProfile.runPostRadialExtensions_eq_of_mem_historyProfile
    {d m n : ℕ} (W : RootRadialSeedProfile d m n) (p : I)
    (incremented : RootExtensionThresholdPolicy d)
    (hincremented : ∀ S b e, S.lower e ≤ incremented S b e)
    (X Y : CubicEdge d → ℝ) (S : SourceFiniteEdgeRevealState d)
    (directions : List (CubicDirection d))
    (hY : Y ∈
      (W.runPostRadialExtensions p incremented X S directions).historyProfile.event) :
    W.runPostRadialExtensions p incremented Y S directions =
      W.runPostRadialExtensions p incremented X S directions := by
  induction directions generalizing S with
  | nil => rfl
  | cons b rest ih =>
      let Q := S.framedQuery (W.physicalCenter b) b
        (oppositeTransverseRestartFlip b)
      let SX := S.next (Q.restartSupport m n) p (incremented S b) X
      let SY := S.next (Q.restartSupport m n) p (incremented S b) Y
      have hFirst : Y ∈ SX.historyProfile.event :=
        W.runPostRadialExtensions_historyProfile_event_subset
          p incremented hincremented X SX rest hY
      have hState : SY = SX :=
        S.next_eq_of_mem_next_historyProfile
          (Q.restartSupport m n) p (incremented S b) X Y hFirst
      simp only [RootRadialSeedProfile.runPostRadialExtensions]
      change W.runPostRadialExtensions p incremented Y SY rest =
        W.runPostRadialExtensions p incremented X SX rest
      rw [hState]
      exact ih (S := SX) hY

/-- Processing a list that omits direction `a` preserves the behind-target invariant for `a`.
This is the induction principle that turns pairwise steering separation into freshness of an
arbitrarily long root prefix. -/
theorem RootRadialSeedProfile.referenceEndpoint_coord_lt_run_of_not_mem
    {d m n : ℕ} (hm : 1 ≤ m) (hmn : m + 1 < n)
    (W : RootRadialSeedProfile d m n)
    (hgeom : ∀ c : CubicDirection d,
      SeedBoxWithinBoundaryLayer d c.1 m n (W c).seedCenter.1)
    (p : I) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) {a : CubicDirection d}
    (directions : List (CubicDirection d)) (S : SourceFiniteEdgeRevealState d)
    (ha : a ∉ directions)
    (hBehind : ∀ z ∈ cubicEdgeEndpointVertices
      (S.referenceExploredEdges (W.postRadialFrame a)), z a.1 < (n : ℤ))
    {z : Cubic d}
    (hz : z ∈ cubicEdgeEndpointVertices
      ((W.runPostRadialExtensions p incremented X S directions).referenceExploredEdges
        (W.postRadialFrame a))) :
    z a.1 < (n : ℤ) := by
  induction directions generalizing S with
  | nil =>
      exact hBehind z (by simpa using hz)
  | cons b rest ih =>
      have hba : b ≠ a := by
        intro h
        subst b
        exact ha (by simp)
      have haRest : a ∉ rest := by
        intro har
        exact ha (by simp [har])
      let Q := S.framedQuery (W.physicalCenter b) b
        (oppositeTransverseRestartFlip b)
      let S' := S.next (Q.restartSupport m n) p (incremented S b) X
      have hStep : ∀ y ∈ cubicEdgeEndpointVertices
          (S'.referenceExploredEdges (W.postRadialFrame a)),
          y a.1 < (n : ℤ) := by
        intro y hy
        exact W.referenceEndpoint_coord_lt_next_of_ne
          hm hmn hgeom hba S p (incremented S b) X hBehind hy
      apply ih (S := S') haRest hStep
      simpa [RootRadialSeedProfile.runPostRadialExtensions, Q, S'] using hz

/-- Processing directions other than `a` preserves a complete unused vertex layer before the
`a` target face. -/
theorem RootRadialSeedProfile.referenceEndpoint_coord_add_one_lt_run_of_not_mem
    {d m n : ℕ} (hm : 1 ≤ m) (hmn : m + 1 < n)
    (W : RootRadialSeedProfile d m n)
    (hgeom : ∀ c : CubicDirection d,
      SeedBoxWithinBoundaryLayer d c.1 m n (W c).seedCenter.1)
    (p : I) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) {a : CubicDirection d}
    (directions : List (CubicDirection d)) (S : SourceFiniteEdgeRevealState d)
    (ha : a ∉ directions)
    (hBehind : ∀ z ∈ cubicEdgeEndpointVertices
      (S.referenceExploredEdges (W.postRadialFrame a)), z a.1 + 1 < (n : ℤ))
    {z : Cubic d}
    (hz : z ∈ cubicEdgeEndpointVertices
      ((W.runPostRadialExtensions p incremented X S directions).referenceExploredEdges
        (W.postRadialFrame a))) :
    z a.1 + 1 < (n : ℤ) := by
  induction directions generalizing S with
  | nil =>
      exact hBehind z (by simpa using hz)
  | cons b rest ih =>
      have hba : b ≠ a := by
        intro h
        subst b
        exact ha (by simp)
      have haRest : a ∉ rest := by
        intro har
        exact ha (by simp [har])
      let Q := S.framedQuery (W.physicalCenter b) b
        (oppositeTransverseRestartFlip b)
      let S' := S.next (Q.restartSupport m n) p (incremented S b) X
      have hStep : ∀ y ∈ cubicEdgeEndpointVertices
          (S'.referenceExploredEdges (W.postRadialFrame a)),
          y a.1 + 1 < (n : ℤ) := by
        intro y hy
        exact W.referenceEndpoint_coord_add_one_lt_next_of_ne
          hm hmn hgeom hba S p (incremented S b) X hBehind hy
      apply ih (S := S') haRest hStep
      simpa [RootRadialSeedProfile.runPostRadialExtensions, Q, S'] using hz

/-- In a nodup direction list, the direction at position `k` does not occur in the prefix of
length `k`. -/
theorem List.getElem_not_mem_take_of_nodup
    {α : Type*} {l : List α} (hl : l.Nodup) {k : ℕ} (hk : k < l.length) :
    l[k] ∉ l.take k := by
  intro hmem
  rw [List.mem_iff_getElem] at hmem
  obtain ⟨j, hj, heq⟩ := hmem
  have hjk : j < k := by
    simpa [List.length_take, Nat.min_eq_left hk.le] using hj
  have hjl : j < l.length := hjk.trans hk
  have htake : (l.take k)[j] = l[j] := List.getElem_take
  have heq' : l[j] = l[k] := htake.symm.trans heq
  exact hjk.ne ((hl.getElem_inj_iff).mp heq')

/-- Before the `k`-th root extension is processed, every already explored endpoint is still
strictly behind that extension's target face. -/
theorem rootPostRadialExtensions_prefix_referenceEndpoint_coord_lt_of_geometry
    {d m n : ℕ} [NeZero d] (hm : 1 ≤ m) (hmn : m + 1 < n)
    (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ)
    (hgeom : ∀ a : CubicDirection d,
      SeedBoxWithinBoundaryLayer d a.1 m n (W a).seedCenter.1)
    {k : ℕ}
    (hk : k < (rootExtensionDirectionOrder d).length)
    {z : Cubic d}
    (hz : z ∈ cubicEdgeEndpointVertices
      (((W.runPostRadialExtensions p incremented X
        (rootPostRadialSourceEdgeState d m n p radialIncremented X)
        ((rootExtensionDirectionOrder d).take k)).referenceExploredEdges
          (W.postRadialFrame ((rootExtensionDirectionOrder d)[k]))))) :
    z ((rootExtensionDirectionOrder d)[k]).1 < (n : ℤ) := by
  let a := (rootExtensionDirectionOrder d)[k]
  apply W.referenceEndpoint_coord_lt_run_of_not_mem hm hmn
    hgeom p incremented X (a := a)
      ((rootExtensionDirectionOrder d).take k)
      (rootPostRadialSourceEdgeState d m n p radialIncremented X)
  · exact List.getElem_not_mem_take_of_nodup
      (rootExtensionDirectionOrder_nodup d) hk
  · intro y hy
    exact rootPostRadialSourceEdgeState_referenceEndpoint_coord_lt_of_geometry
      hm hmn W a p radialIncremented X (hgeom a) hy
  · simpa [a] using hz

/-- Before every root-extension slot, the explored endpoint region leaves one whole unused
vertex layer before the selected target face. -/
theorem rootPostRadialExtensions_prefix_referenceEndpoint_coord_add_one_lt_of_geometry
    {d m n : ℕ} [NeZero d] (hm : 1 ≤ m) (hmn : m + 1 < n)
    (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ)
    (hgeom : ∀ a : CubicDirection d,
      SeedBoxWithinBoundaryLayer d a.1 m n (W a).seedCenter.1)
    {k : ℕ} (hk : k < (rootExtensionDirectionOrder d).length)
    {z : Cubic d}
    (hz : z ∈ cubicEdgeEndpointVertices
      (((W.runPostRadialExtensions p incremented X
        (rootPostRadialSourceEdgeState d m n p radialIncremented X)
        ((rootExtensionDirectionOrder d).take k)).referenceExploredEdges
          (W.postRadialFrame ((rootExtensionDirectionOrder d)[k]))))) :
    z ((rootExtensionDirectionOrder d)[k]).1 + 1 < (n : ℤ) := by
  let a := (rootExtensionDirectionOrder d)[k]
  apply W.referenceEndpoint_coord_add_one_lt_run_of_not_mem hm hmn
    hgeom p incremented X (a := a)
      ((rootExtensionDirectionOrder d).take k)
      (rootPostRadialSourceEdgeState d m n p radialIncremented X)
  · exact List.getElem_not_mem_take_of_nodup
      (rootExtensionDirectionOrder_nodup d) hk
  · intro y hy
    exact rootPostRadialSourceEdgeState_referenceEndpoint_coord_add_one_lt_of_geometry
      hm hmn W a p radialIncremented X (hgeom a) hy
  · simpa [a] using hz

/-- Realization-facing wrapper for sequential root-prefix endpoint separation. -/
theorem rootPostRadialExtensions_prefix_referenceEndpoint_coord_lt
    {d m n : ℕ} [NeZero d] (hm : 1 ≤ m) (hmn : m + 1 < n)
    (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ)
    (hW : ∀ a : CubicDirection d, (W a).IsRealized
      (framedReferenceThresholdConfiguration cubicOrigin a
        (rootRadialTransverseFlip a) p X))
    {k : ℕ} (hk : k < (rootExtensionDirectionOrder d).length)
    {z : Cubic d}
    (hz : z ∈ cubicEdgeEndpointVertices
      (((W.runPostRadialExtensions p incremented X
        (rootPostRadialSourceEdgeState d m n p radialIncremented X)
        ((rootExtensionDirectionOrder d).take k)).referenceExploredEdges
          (W.postRadialFrame ((rootExtensionDirectionOrder d)[k]))))) :
    z ((rootExtensionDirectionOrder d)[k]).1 < (n : ℤ) :=
  rootPostRadialExtensions_prefix_referenceEndpoint_coord_lt_of_geometry
    hm hmn W p radialIncremented incremented X (fun a ↦ (hW a).2.2.1) hk hz

/-- Source-facing endpoint freshness at every root-extension slot. -/
theorem rootPostRadialExtensions_prefix_targetEndpointFresh_of_geometry
    {d m n : ℕ} [NeZero d] (hm : 1 ≤ m) (hmn : m + 1 < n)
    (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ)
    (hgeom : ∀ a : CubicDirection d,
      SeedBoxWithinBoundaryLayer d a.1 m n (W a).seedCenter.1)
    {k : ℕ}
    (hk : k < (rootExtensionDirectionOrder d).length) :
    let a := (rootExtensionDirectionOrder d)[k]
    let S := W.runPostRadialExtensions p incremented X
      (rootPostRadialSourceEdgeState d m n p radialIncremented X)
      ((rootExtensionDirectionOrder d).take k)
    Disjoint (cubicEdgeEndpointVertices
      (S.referenceExploredEdges (W.postRadialFrame a)))
      (cubicEdgeEndpointVertices (seededBoundaryTargetSupport d a.1 m n)) := by
  dsimp only
  apply disjoint_endpointVertices_seededBoundaryTargetSupport_of_coord_lt
  intro z hz
  exact rootPostRadialExtensions_prefix_referenceEndpoint_coord_lt_of_geometry
    hm hmn W p radialIncremented incremented X hgeom hk hz

/-- Realization-facing wrapper for source target freshness at a root-prefix slot. -/
theorem rootPostRadialExtensions_prefix_targetEndpointFresh
    {d m n : ℕ} [NeZero d] (hm : 1 ≤ m) (hmn : m + 1 < n)
    (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ)
    (hW : ∀ a : CubicDirection d, (W a).IsRealized
      (framedReferenceThresholdConfiguration cubicOrigin a
        (rootRadialTransverseFlip a) p X))
    {k : ℕ} (hk : k < (rootExtensionDirectionOrder d).length) :
    let a := (rootExtensionDirectionOrder d)[k]
    let S := W.runPostRadialExtensions p incremented X
      (rootPostRadialSourceEdgeState d m n p radialIncremented X)
      ((rootExtensionDirectionOrder d).take k)
    Disjoint (cubicEdgeEndpointVertices
      (S.referenceExploredEdges (W.postRadialFrame a)))
      (cubicEdgeEndpointVertices (seededBoundaryTargetSupport d a.1 m n)) :=
  rootPostRadialExtensions_prefix_targetEndpointFresh_of_geometry
    hm hmn W p radialIncremented incremented X (fun a ↦ (hW a).2.2.1) hk

/-- At every slot of the root order, the canonical framed boundary is exactly the current
global source boundary intersected with the finite restart support. -/
theorem rootPostRadialExtensions_prefix_framedQuery_boundarySupport_eq
    {d m n : ℕ} [NeZero d] (hm : 1 ≤ m) (hmn : m + 1 < n)
    (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ)
    (hW : ∀ a : CubicDirection d, (W a).IsRealized
      (framedReferenceThresholdConfiguration cubicOrigin a
        (rootRadialTransverseFlip a) p X))
    {k : ℕ} (hk : k < (rootExtensionDirectionOrder d).length) :
    let a := (rootExtensionDirectionOrder d)[k]
    let S := W.runPostRadialExtensions p incremented X
      (rootPostRadialSourceEdgeState d m n p radialIncremented X)
      ((rootExtensionDirectionOrder d).take k)
    let Q := S.framedQuery (W.physicalCenter a) a
      (oppositeTransverseRestartFlip a)
    Q.boundarySupport n = S.boundary ∩ Q.restartSupport m n := by
  dsimp only
  apply SourceFiniteEdgeRevealState.framedQuery_boundarySupport_eq_boundary_inter_restartSupport_of_targetEndpointFresh
  simpa [RootRadialSeedProfile.postRadialFrame] using
    rootPostRadialExtensions_prefix_targetEndpointFresh
      hm hmn W p radialIncremented incremented X hW hk

/-- No open edge explored in an earlier root slot is reread by the current slot's restart
support. -/
theorem rootPostRadialExtensions_prefix_explored_disjoint_restartSupport
    {d m n : ℕ} [NeZero d] (hm : 1 ≤ m) (hmn : m + 1 < n)
    (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ)
    (hW : ∀ a : CubicDirection d, (W a).IsRealized
      (framedReferenceThresholdConfiguration cubicOrigin a
        (rootRadialTransverseFlip a) p X))
    {k : ℕ} (hk : k < (rootExtensionDirectionOrder d).length) :
    let a := (rootExtensionDirectionOrder d)[k]
    let S := W.runPostRadialExtensions p incremented X
      (rootPostRadialSourceEdgeState d m n p radialIncremented X)
      ((rootExtensionDirectionOrder d).take k)
    let Q := S.framedQuery (W.physicalCenter a) a
      (oppositeTransverseRestartFlip a)
    Disjoint (S.explored : Set (CubicEdge d))
      (Q.restartSupport m n : Set (CubicEdge d)) := by
  dsimp only
  apply SourceFiniteEdgeRevealState.framedQuery_explored_disjoint_restartSupport_of_targetEndpointFresh
  simpa [RootRadialSeedProfile.postRadialFrame] using
    rootPostRadialExtensions_prefix_targetEndpointFresh
      hm hmn W p radialIncremented incremented X hW hk

/-- State after all `2d` post-radial root extensions have been processed. -/
noncomputable def RootRadialSeedProfile.completedRootExtensionState
    {d m n : ℕ} (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) : SourceFiniteEdgeRevealState d :=
  W.runPostRadialExtensions p incremented X
    (rootPostRadialSourceEdgeState d m n p radialIncremented X)
    (rootExtensionDirectionOrder d)

/-- Source-facing exact interval invariant after the radial phase and all `2d` root
extensions.  The three nonnegativity families are deliberately explicit: coupling labels are
real-valued in the ambient measurable space, while each such finite cylinder has coupling
probability one. -/
theorem rootRadialEvent_mem_completedRootExtensionProfile
    {d m n : ℕ} [NeZero d]
    (W : RootRadialSeedProfile d m n) (p radialIncremented : I)
    (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ)
    (hradial : X ∈ rootRadialEvent d m n p delta)
    (hinitial : X ∈ SourceFiniteEdgeRevealState.nonnegativeBoundaryEvent
      (cubicEdgeBoundary (rootInitialExploredEdges d m)))
    (hpostRadial : X ∈ SourceFiniteEdgeRevealState.nonnegativeBoundaryEvent
      (cubicEdgeBoundary
        ((rootInitialSourceEdgeState d m p).nextExplored
          (rootRadialEdgeSupport d m n) p (fun _ ↦ radialIncremented) X)))
    (hnonneg : ∀ k (hk : k < (rootExtensionDirectionOrder d).length),
      let state := W.runPostRadialExtensions p incremented X
        (rootPostRadialSourceEdgeState d m n p radialIncremented X)
        ((rootExtensionDirectionOrder d).take k)
      let a := (rootExtensionDirectionOrder d)[k]
      let Q := state.framedQuery (W.physicalCenter a) a
        (oppositeTransverseRestartFlip a)
      X ∈ SourceFiniteEdgeRevealState.nonnegativeBoundaryEvent
        (cubicEdgeBoundary
          (state.nextExplored (Q.restartSupport m n) p (incremented state a) X))) :
    X ∈ (W.completedRootExtensionState p radialIncremented incremented X).profile.event := by
  unfold RootRadialSeedProfile.completedRootExtensionState
  apply W.mem_runPostRadialExtensions_profile p incremented X
      (rootExtensionDirectionOrder d)
      (rootPostRadialSourceEdgeState d m n p radialIncremented X) hnonneg
  exact rootRadialEvent_mem_postRadialSourceProfile
    p radialIncremented delta X hradial hinitial hpostRadial

/-- On the probability-one support of the common-uniform coupling, the radial event alone
initializes and preserves the exact interval profile through the complete root schedule. -/
theorem rootRadialEvent_mem_completedRootExtensionProfile_of_mem_nonnegativeCouplingEvent
    {d m n : ℕ} [NeZero d]
    (W : RootRadialSeedProfile d m n) (p radialIncremented : I)
    (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ)
    (hradial : X ∈ rootRadialEvent d m n p delta)
    (hX : X ∈ SourceFiniteEdgeRevealState.nonnegativeCouplingEvent) :
    X ∈ (W.completedRootExtensionState p radialIncremented incremented X).profile.event := by
  apply rootRadialEvent_mem_completedRootExtensionProfile
    W p radialIncremented delta incremented X hradial
  · exact SourceFiniteEdgeRevealState.mem_nonnegativeBoundaryEvent_of_mem_nonnegativeCouplingEvent
      hX
  · exact SourceFiniteEdgeRevealState.mem_nonnegativeBoundaryEvent_of_mem_nonnegativeCouplingEvent
      hX
  · intro k hk
    exact SourceFiniteEdgeRevealState.mem_nonnegativeBoundaryEvent_of_mem_nonnegativeCouplingEvent
      hX

/-- The radial event determines the exact accumulated root history, including both endpoints
on every boundary edge absorbed by a later extension. -/
theorem rootRadialEvent_mem_completedRootExtensionHistoryProfile
    {d m n : ℕ} [NeZero d]
    (W : RootRadialSeedProfile d m n) (p radialIncremented : I)
    (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ)
    (hradial : X ∈ rootRadialEvent d m n p delta)
    (hX : X ∈ SourceFiniteEdgeRevealState.nonnegativeCouplingEvent) :
    X ∈
      (W.completedRootExtensionState p radialIncremented incremented X).historyProfile.event := by
  unfold RootRadialSeedProfile.completedRootExtensionState
  apply W.mem_runPostRadialExtensions_historyProfile p incremented X
      (rootExtensionDirectionOrder d)
      (rootPostRadialSourceEdgeState d m n p radialIncremented X) hX
  exact rootRadialEvent_mem_postRadialSourceHistoryProfile
    p radialIncremented delta X hradial hX

/-! ### Exact finite-cell stage adapter -/

/-- Prefix source state represented by a finite reveal cell.  The representative is used only
to compute the deterministic explored set and interval endpoints attached to that cell. -/
noncomputable def RootRadialSeedProfile.rootExtensionPrefixState
    {d m n : ℕ} {C : Type*} (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (incremented : RootExtensionThresholdPolicy d)
    (representative : C → CubicEdge d → ℝ) (k : ℕ) (c : C) :
    SourceFiniteEdgeRevealState d :=
  W.runPostRadialExtensions p incremented (representative c)
    (rootPostRadialSourceEdgeState d m n p radialIncremented (representative c))
    ((rootExtensionDirectionOrder d).take k)

/-- Before slot `k`, the canonical budgeted recursion has spent at most `k` post-radial
increments on any coordinate. -/
theorem RootRadialSeedProfile.coe_rootExtensionPrefixState_budgeted_lower_le
    {d m n : ℕ} (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (delta : ℝ) (hdelta : 0 ≤ delta)
    {C : Type*} (representative : C → CubicEdge d → ℝ)
    (k : ℕ) (c : C) (e : CubicEdge d) :
    ((W.rootExtensionPrefixState p radialIncremented
      (budgetedRootExtensionThresholdPolicy delta hdelta) representative k c).lower e : ℝ) ≤
      max (p : ℝ) (radialIncremented : ℝ) + (k : ℝ) * delta := by
  have hrun := W.coe_runPostRadialExtensions_budgeted_lower_le
    p delta hdelta (representative c)
    (rootPostRadialSourceEdgeState d m n p radialIncremented (representative c))
    ((rootExtensionDirectionOrder d).take k)
    (max (p : ℝ) (radialIncremented : ℝ))
    (fun f ↦ coe_rootPostRadialSourceEdgeState_lower_le_max
      p radialIncremented (representative c) f)
    (le_max_left _ _) e
  change
    ((W.rootExtensionPrefixState p radialIncremented
      (budgetedRootExtensionThresholdPolicy delta hdelta) representative k c).lower e : ℝ) ≤
      _ at hrun
  have hlength : ((rootExtensionDirectionOrder d).take k).length ≤ k :=
    List.length_take_le k (rootExtensionDirectionOrder d)
  have hlengthReal : (((rootExtensionDirectionOrder d).take k).length : ℝ) ≤ (k : ℝ) := by
    exact_mod_cast hlength
  have hmul := mul_le_mul_of_nonneg_right hlengthReal hdelta
  linarith

/-- A global arithmetic budget supplies the literal `HasIncrementBudget` property on every
reachable prefix state before the end of the root schedule. -/
theorem RootRadialSeedProfile.rootExtensionPrefixState_hasIncrementBudget
    {d m n : ℕ} (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (delta : ℝ) (hdelta : 0 ≤ delta)
    (htotal : max (p : ℝ) (radialIncremented : ℝ) +
      ((rootExtensionDirectionOrder d).length : ℝ) * delta ≤ 1)
    {C : Type*} (representative : C → CubicEdge d → ℝ)
    {k : ℕ} (hk : k < (rootExtensionDirectionOrder d).length) (c : C) :
    (W.rootExtensionPrefixState p radialIncremented
      (budgetedRootExtensionThresholdPolicy delta hdelta) representative k c).HasIncrementBudget
        delta := by
  intro e
  have hlower := W.coe_rootExtensionPrefixState_budgeted_lower_le
    p radialIncremented delta hdelta representative k c e
  have hcast : (k + 1 : ℕ) ≤ (rootExtensionDirectionOrder d).length := by omega
  have hmul : ((k + 1 : ℕ) : ℝ) * delta ≤
      ((rootExtensionDirectionOrder d).length : ℝ) * delta := by
    apply mul_le_mul_of_nonneg_right _ hdelta
    exact_mod_cast hcast
  calc
    ((W.rootExtensionPrefixState p radialIncremented
        (budgetedRootExtensionThresholdPolicy delta hdelta) representative k c).lower e : ℝ) +
        delta ≤
      (max (p : ℝ) (radialIncremented : ℝ) + (k : ℝ) * delta) + delta :=
        by linarith
    _ = max (p : ℝ) (radialIncremented : ℝ) + ((k + 1 : ℕ) : ℝ) * delta := by
      push_cast
      ring
    _ ≤ max (p : ℝ) (radialIncremented : ℝ) +
        ((rootExtensionDirectionOrder d).length : ℝ) * delta :=
      by linarith
    _ ≤ 1 := htotal

/-- On every reachable root-prefix state, the canonical total policy takes its genuine
`lower + delta` branch. -/
theorem RootRadialSeedProfile.coe_budgetedPolicy_prefixState_eq_add
    {d m n : ℕ} (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (delta : ℝ) (hdelta : 0 ≤ delta)
    (htotal : max (p : ℝ) (radialIncremented : ℝ) +
      ((rootExtensionDirectionOrder d).length : ℝ) * delta ≤ 1)
    {C : Type*} (representative : C → CubicEdge d → ℝ)
    {k : ℕ} (hk : k < (rootExtensionDirectionOrder d).length) (c : C)
    (a : CubicDirection d) (e : CubicEdge d) :
    (budgetedRootExtensionThresholdPolicy delta hdelta
      (W.rootExtensionPrefixState p radialIncremented
        (budgetedRootExtensionThresholdPolicy delta hdelta) representative k c) a e : ℝ) =
      ((W.rootExtensionPrefixState p radialIncremented
        (budgetedRootExtensionThresholdPolicy delta hdelta) representative k c).lower e : ℝ) +
        delta := by
  apply coe_budgetedRootExtensionThresholdPolicy_of_hasIncrementBudget
  exact W.rootExtensionPrefixState_hasIncrementBudget
    p radialIncremented delta hdelta htotal representative hk c

/-- A threshold policy implements the literal `lower + delta` update on every state that can
actually occur before a root-extension slot.  Unlike a global pointwise condition, this does
not make a false demand on unreachable budget-violating junk states. -/
def RootRadialSeedProfile.PolicyAddsOnPrefixes
    {d m n : ℕ} (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (delta : ℝ)
    (incremented : RootExtensionThresholdPolicy d) : Prop :=
  ∀ (X : CubicEdge d → ℝ) k
      (hk : k < (rootExtensionDirectionOrder d).length) (e : CubicEdge d),
    let S := W.rootExtensionPrefixState p radialIncremented incremented id k X
    let a := (rootExtensionDirectionOrder d)[k]
    (incremented S a e : ℝ) = (S.lower e : ℝ) + delta

/-- A globally exact policy is exact on reachable prefixes. -/
theorem RootRadialSeedProfile.policyAddsOnPrefixes_of_forall
    {d m n : ℕ} (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (delta : ℝ)
    (incremented : RootExtensionThresholdPolicy d)
    (hadds : ∀ S b e,
      (incremented S b e : ℝ) = (S.lower e : ℝ) + delta) :
    W.PolicyAddsOnPrefixes p radialIncremented delta incremented := by
  intro X k hk e
  exact hadds _ _ e

/-- The canonical budgeted policy is exact on every reachable prefix under the global root
schedule budget. -/
theorem RootRadialSeedProfile.budgetedPolicy_addsOnPrefixes
    {d m n : ℕ} (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (delta : ℝ) (hdelta : 0 ≤ delta)
    (htotal : max (p : ℝ) (radialIncremented : ℝ) +
      ((rootExtensionDirectionOrder d).length : ℝ) * delta ≤ 1) :
    W.PolicyAddsOnPrefixes p radialIncremented delta
      (budgetedRootExtensionThresholdPolicy delta hdelta) := by
  intro X k hk e
  exact W.coe_budgetedPolicy_prefixState_eq_add
    p radialIncremented delta hdelta htotal id hk X _ e

/-- The state at prefix `k+1` is one literal successor of the state at prefix `k`. -/
theorem RootRadialSeedProfile.rootExtensionPrefixState_succ
    {d m n : ℕ} {C : Type*} (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (incremented : RootExtensionThresholdPolicy d)
    (representative : C → CubicEdge d → ℝ) {k : ℕ}
    (hk : k < (rootExtensionDirectionOrder d).length) (c : C) :
    W.rootExtensionPrefixState p radialIncremented incremented representative (k + 1) c =
      let S := W.rootExtensionPrefixState
        p radialIncremented incremented representative k c
      let a := (rootExtensionDirectionOrder d)[k]
      let Q := S.framedQuery (W.physicalCenter a) a
        (oppositeTransverseRestartFlip a)
      S.next (Q.restartSupport m n) p (incremented S a) (representative c) := by
  rw [RootRadialSeedProfile.rootExtensionPrefixState,
    ← List.take_concat_get' (rootExtensionDirectionOrder d) k hk,
    W.runPostRadialExtensions_append]
  rfl

/-- Semantic outer event before root-extension slot `k`: the simultaneous radial phase and
every one of the first `k` framed restarts have succeeded. -/
def RootRadialSeedProfile.rootExtensionPrefixSuccessEvent
    {d m n : ℕ} (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (delta : ℝ)
    (incremented : RootExtensionThresholdPolicy d) (k : ℕ) :
    Set (CubicEdge d → ℝ) :=
  {X | X ∈ rootRadialEvent d m n p delta ∧
    W.runPostRadialExtensionSuccesses p delta incremented X
      (rootPostRadialSourceEdgeState d m n p radialIncremented X)
      ((rootExtensionDirectionOrder d).take k)}

@[simp]
theorem RootRadialSeedProfile.rootExtensionPrefixSuccessEvent_zero
    {d m n : ℕ} (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (delta : ℝ)
    (incremented : RootExtensionThresholdPolicy d) :
    W.rootExtensionPrefixSuccessEvent p radialIncremented delta incremented 0 =
      rootRadialEvent d m n p delta := by
  ext X
  simp [RootRadialSeedProfile.rootExtensionPrefixSuccessEvent]

/-- One more semantic prefix success is exactly the preceding prefix success together with
success of the framed query computed from that realization's literal prefix state. -/
theorem RootRadialSeedProfile.mem_rootExtensionPrefixSuccessEvent_succ_iff
    {d m n : ℕ} (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (delta : ℝ)
    (incremented : RootExtensionThresholdPolicy d) {k : ℕ}
    (hk : k < (rootExtensionDirectionOrder d).length)
    (X : CubicEdge d → ℝ) :
    X ∈ W.rootExtensionPrefixSuccessEvent
        p radialIncremented delta incremented (k + 1) ↔
      X ∈ W.rootExtensionPrefixSuccessEvent
          p radialIncremented delta incremented k ∧
        let a := (rootExtensionDirectionOrder d)[k]
        let S := W.rootExtensionPrefixState
          p radialIncremented incremented id k X
        let Q := S.framedQuery (W.physicalCenter a) a
          (oppositeTransverseRestartFlip a)
        X ∈ Q.successEvent m n p delta := by
  rw [RootRadialSeedProfile.rootExtensionPrefixSuccessEvent,
    RootRadialSeedProfile.rootExtensionPrefixSuccessEvent,
    ← List.take_concat_get' (rootExtensionDirectionOrder d) k hk]
  change
    (X ∈ rootRadialEvent d m n p delta ∧
      W.runPostRadialExtensionSuccesses p delta incremented X
        (rootPostRadialSourceEdgeState d m n p radialIncremented X)
        ((rootExtensionDirectionOrder d).take k ++
          [(rootExtensionDirectionOrder d)[k]])) ↔
      (X ∈ rootRadialEvent d m n p delta ∧
        W.runPostRadialExtensionSuccesses p delta incremented X
          (rootPostRadialSourceEdgeState d m n p radialIncremented X)
          ((rootExtensionDirectionOrder d).take k)) ∧ _
  rw [W.runPostRadialExtensionSuccesses_append]
  simp only [W.runPostRadialExtensionSuccesses_cons,
    W.runPostRadialExtensionSuccesses_nil, and_true]
  tauto

/-- The entire semantic prefix event is constant on each canonical prefix accumulated-history
cell.  The radial factor uses the explored radial certificate; the sequential factor uses the
one-step framed-success stability theorem inductively. -/
theorem RootRadialSeedProfile.rootExtensionPrefixSuccessEvent_of_mem_historyProfile
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
    (hX : X ∈ W.rootExtensionPrefixSuccessEvent
      p radialIncremented delta incremented k)
    (hY : Y ∈
      (W.rootExtensionPrefixState p radialIncremented incremented id k X).historyProfile.event) :
    Y ∈ W.rootExtensionPrefixSuccessEvent
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
  refine ⟨rootRadialEvent_of_mem_rootPostRadialSourceHistoryProfile
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

/-- The concrete state before root-extension slot `k` has finite range over all coupling-label
realizations. -/
theorem RootRadialSeedProfile.finite_range_rootExtensionPrefixState
    {d m n : ℕ} (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (incremented : RootExtensionThresholdPolicy d) (k : ℕ) :
    (Set.range fun X : CubicEdge d → ℝ ↦
      W.rootExtensionPrefixState p radialIncremented incremented id k X).Finite := by
  let initialState : (CubicEdge d → ℝ) → SourceFiniteEdgeRevealState d := fun X ↦
    rootPostRadialSourceEdgeState d m n p radialIncremented X
  have hinitial : (Set.range initialState).Finite := by
    simpa [initialState, rootPostRadialSourceEdgeState] using
      (rootInitialSourceEdgeState d m p).finite_range_next
        (rootRadialEdgeSupport d m n) p (fun _ ↦ radialIncremented)
  simpa [RootRadialSeedProfile.rootExtensionPrefixState, initialState] using
    W.finite_range_runPostRadialExtensions p incremented initialState
      ((rootExtensionDirectionOrder d).take k) hinitial

/-- A label realization in a concrete root-prefix accumulated-history cell reproduces that
prefix state. -/
theorem RootRadialSeedProfile.rootExtensionPrefixState_eq_of_mem_historyProfile
    {d m n : ℕ} (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (incremented : RootExtensionThresholdPolicy d)
    (hincremented : ∀ S b e, S.lower e ≤ incremented S b e)
    (k : ℕ) (X Y : CubicEdge d → ℝ)
    (hY : Y ∈
      (W.rootExtensionPrefixState p radialIncremented incremented id k X).historyProfile.event) :
    W.rootExtensionPrefixState p radialIncremented incremented id k Y =
      W.rootExtensionPrefixState p radialIncremented incremented id k X := by
  let SX := rootPostRadialSourceEdgeState d m n p radialIncremented X
  let SY := rootPostRadialSourceEdgeState d m n p radialIncremented Y
  let directions := (rootExtensionDirectionOrder d).take k
  have hPost : Y ∈ SX.historyProfile.event :=
    W.runPostRadialExtensions_historyProfile_event_subset
      p incremented hincremented X SX directions hY
  have hRadial : SY = SX :=
    (rootInitialSourceEdgeState d m p).next_eq_of_mem_next_historyProfile
      (rootRadialEdgeSupport d m n) p (fun _ ↦ radialIncremented) X Y hPost
  change W.runPostRadialExtensions p incremented Y SY directions =
    W.runPostRadialExtensions p incremented X SX directions
  rw [hRadial]
  exact W.runPostRadialExtensions_eq_of_mem_historyProfile
    p incremented hincremented X Y SX directions hY

/-- Every canonical root-prefix accumulated-history cell still forces the original central
seed to be `p`-open.  Thus the unresolved radial-event stability problem concerns only the
directional target hits, not the seed factor common to all branches. -/
theorem RootRadialSeedProfile.rootSeedLabelEvent_of_mem_prefixHistoryProfile
    {d m n : ℕ} (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (incremented : RootExtensionThresholdPolicy d)
    (hincremented : ∀ S b e, S.lower e ≤ incremented S b e)
    (k : ℕ) (X Y : CubicEdge d → ℝ)
    (hY : Y ∈
      (W.rootExtensionPrefixState p radialIncremented incremented id k X).historyProfile.event) :
    Y ∈ rootSeedLabelEvent d m p := by
  let S := rootPostRadialSourceEdgeState d m n p radialIncremented X
  have hPost : Y ∈ S.historyProfile.event :=
    W.runPostRadialExtensions_historyProfile_event_subset
      p incremented hincremented X S ((rootExtensionDirectionOrder d).take k) hY
  exact rootSeedLabelEvent_of_mem_rootPostRadialSourceHistoryProfile
    p radialIncremented X Y hPost

/-- The complete radial success event is stable throughout every later root-prefix
accumulated-history cell. -/
theorem RootRadialSeedProfile.rootRadialEvent_of_mem_prefixHistoryProfile
    {d m n : ℕ} [NeZero d] (hm : 1 ≤ m) (hmn : m + 1 ≤ n)
    (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) {delta : ℝ}
    (hdelta : delta = (radialIncremented : ℝ))
    (incremented : RootExtensionThresholdPolicy d)
    (hincremented : ∀ S b e, S.lower e ≤ incremented S b e)
    (k : ℕ) (X Y : CubicEdge d → ℝ)
    (hX : X ∈ rootRadialEvent d m n p delta)
    (hY : Y ∈
      (W.rootExtensionPrefixState p radialIncremented incremented id k X).historyProfile.event) :
    Y ∈ rootRadialEvent d m n p delta := by
  let S := rootPostRadialSourceEdgeState d m n p radialIncremented X
  have hPost : Y ∈ S.historyProfile.event :=
    W.runPostRadialExtensions_historyProfile_event_subset
      p incremented hincremented X S ((rootExtensionDirectionOrder d).take k) hY
  exact rootRadialEvent_of_mem_rootPostRadialSourceHistoryProfile
    hm hmn p radialIncremented hdelta X Y hX hPost

/-- Distinct reachable root-prefix states have disjoint accumulated-history cells. -/
theorem RootRadialSeedProfile.disjoint_historyProfile_of_mem_prefixStateRange
    {d m n : ℕ} (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (incremented : RootExtensionThresholdPolicy d)
    (hincremented : ∀ S b e, S.lower e ≤ incremented S b e)
    (k : ℕ) {S T : SourceFiniteEdgeRevealState d}
    (hS : S ∈ Set.range (fun X : CubicEdge d → ℝ ↦
      W.rootExtensionPrefixState p radialIncremented incremented id k X))
    (hT : T ∈ Set.range (fun X : CubicEdge d → ℝ ↦
      W.rootExtensionPrefixState p radialIncremented incremented id k X))
    (hne : S ≠ T) : Disjoint S.historyProfile.event T.historyProfile.event := by
  rw [Set.disjoint_left]
  rintro Y hYS hYT
  obtain ⟨X, rfl⟩ := hS
  obtain ⟨Z, rfl⟩ := hT
  apply hne
  exact (W.rootExtensionPrefixState_eq_of_mem_historyProfile
    p radialIncremented incremented hincremented k X Y hYS).symm.trans
      (W.rootExtensionPrefixState_eq_of_mem_historyProfile
        p radialIncremented incremented hincremented k Z Y hYT)

/-- Finite collection of every source state reachable before root-extension slot `k`. -/
noncomputable def RootRadialSeedProfile.rootExtensionPrefixStateFinset
    {d m n : ℕ} (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (incremented : RootExtensionThresholdPolicy d) (k : ℕ) :
    Finset (SourceFiniteEdgeRevealState d) :=
  (W.finite_range_rootExtensionPrefixState p radialIncremented incremented k).toFinset

@[simp]
theorem RootRadialSeedProfile.mem_rootExtensionPrefixStateFinset_iff
    {d m n : ℕ} (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (incremented : RootExtensionThresholdPolicy d) (k : ℕ)
    (S : SourceFiniteEdgeRevealState d) :
    S ∈ W.rootExtensionPrefixStateFinset p radialIncremented incremented k ↔
      ∃ X : CubicEdge d → ℝ,
        W.rootExtensionPrefixState p radialIncremented incremented id k X = S := by
  simp [RootRadialSeedProfile.rootExtensionPrefixStateFinset]

/-- Finite index type of concrete reachable prefix states. -/
abbrev RootExtensionPrefixStateIndex {d m n : ℕ}
    (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (incremented : RootExtensionThresholdPolicy d) (k : ℕ) :=
  {S : SourceFiniteEdgeRevealState d //
    S ∈ W.rootExtensionPrefixStateFinset p radialIncremented incremented k}

/-- A reachable prefix state refined by the three finite threshold patterns needed to retain
the exact root history: the radial background density, the first boundary increment, and the
final density used by canonical seed selection. -/
structure RootExtensionRefinedCellIndex {d m n : ℕ}
    (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (incremented : RootExtensionThresholdPolicy d) (k : ℕ) where
  state : RootExtensionPrefixStateIndex W p radialIncremented incremented k
  backgroundPattern : RootRadialThresholdPattern d m n
  incrementPattern : RootRadialThresholdPattern d m n
  finalPattern : RootRadialThresholdPattern d m n

theorem rootExtensionRefinedCellIndex_ext
    {d m n : ℕ} {W : RootRadialSeedProfile d m n}
    {p radialIncremented : I} {incremented : RootExtensionThresholdPolicy d} {k : ℕ}
    {c c' : RootExtensionRefinedCellIndex W p radialIncremented incremented k}
    (hstate : c.state = c'.state)
    (hbackground : c.backgroundPattern = c'.backgroundPattern)
    (hincrement : c.incrementPattern = c'.incrementPattern)
    (hfinal : c.finalPattern = c'.finalPattern) : c = c' := by
  cases c
  cases c'
  simp_all

noncomputable instance rootExtensionRefinedCellIndexDecidableEq
    {d m n : ℕ} (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (incremented : RootExtensionThresholdPolicy d) (k : ℕ) :
    DecidableEq (RootExtensionRefinedCellIndex W p radialIncremented incremented k) :=
  Classical.decEq _

def rootExtensionRefinedCellIndexEquiv
    {d m n : ℕ} (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (incremented : RootExtensionThresholdPolicy d) (k : ℕ) :
    RootExtensionRefinedCellIndex W p radialIncremented incremented k ≃
      RootExtensionPrefixStateIndex W p radialIncremented incremented k ×
        RootRadialThresholdPattern d m n × RootRadialThresholdPattern d m n ×
          RootRadialThresholdPattern d m n where
  toFun c := (c.state, c.backgroundPattern, c.incrementPattern, c.finalPattern)
  invFun c := ⟨c.1, c.2.1, c.2.2.1, c.2.2.2⟩
  left_inv c := by cases c; rfl
  right_inv c := by rcases c with ⟨state, background, increment, final⟩; rfl

noncomputable instance rootExtensionRefinedCellIndexFintype
    {d m n : ℕ} (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (incremented : RootExtensionThresholdPolicy d) (k : ℕ) :
    Fintype (RootExtensionRefinedCellIndex W p radialIncremented incremented k) :=
  Fintype.ofEquiv
    (RootExtensionPrefixStateIndex W p radialIncremented incremented k ×
      RootRadialThresholdPattern d m n × RootRadialThresholdPattern d m n ×
        RootRadialThresholdPattern d m n)
    (rootExtensionRefinedCellIndexEquiv W p radialIncremented incremented k).symm

/-- Single interval profile obtained by merging all three radial threshold patterns into the
reachable accumulated-history cell. -/
noncomputable def RootExtensionRefinedCellIndex.profile
    {d m n : ℕ} {W : RootRadialSeedProfile d m n}
    {p radialIncremented : I} {incremented : RootExtensionThresholdPolicy d} {k : ℕ}
    (pFinal : I) (c : RootExtensionRefinedCellIndex W p radialIncremented incremented k) :
    FiniteRevealIntervalProfile (CubicEdge d) :=
  (((c.state.1.historyProfile.refineAtThreshold
      (rootRadialEdgeSupport d m n) p c.backgroundPattern.physical).refineAtThreshold
      (rootRadialEdgeSupport d m n) radialIncremented c.incrementPattern.physical).refineAtThreshold
      (rootRadialEdgeSupport d m n) pFinal c.finalPattern.physical)

/-- Exact set semantics of a refined root cell. -/
theorem RootExtensionRefinedCellIndex.profile_event_eq
    {d m n : ℕ} {W : RootRadialSeedProfile d m n}
    {p radialIncremented : I} {incremented : RootExtensionThresholdPolicy d} {k : ℕ}
    (pFinal : I) (c : RootExtensionRefinedCellIndex W p radialIncremented incremented k) :
    (c.profile pFinal).event =
      ((c.state.1.historyProfile.event ∩
          {X | FiniteRevealIntervalProfile.labelsBelow
            (rootRadialEdgeSupport d m n) p X = c.backgroundPattern.physical}) ∩
        {X | FiniteRevealIntervalProfile.labelsBelow
          (rootRadialEdgeSupport d m n) radialIncremented X = c.incrementPattern.physical}) ∩
      {X | FiniteRevealIntervalProfile.labelsBelow
        (rootRadialEdgeSupport d m n) pFinal X = c.finalPattern.physical} := by
  rw [RootExtensionRefinedCellIndex.profile,
    FiniteRevealIntervalProfile.refineAtThreshold_event_eq,
    FiniteRevealIntervalProfile.refineAtThreshold_event_eq,
    FiniteRevealIntervalProfile.refineAtThreshold_event_eq]
  rw [Finset.inter_eq_right.mpr c.backgroundPattern.physical_subset,
    Finset.inter_eq_right.mpr c.incrementPattern.physical_subset,
    Finset.inter_eq_right.mpr c.finalPattern.physical_subset]

/-- Refined cell canonically realized by a label configuration. -/
noncomputable def RootRadialSeedProfile.realizedRootExtensionRefinedCell
    {d m n : ℕ} (W : RootRadialSeedProfile d m n)
    (p radialIncremented pFinal : I) (incremented : RootExtensionThresholdPolicy d)
    (k : ℕ) (X : CubicEdge d → ℝ) :
    RootExtensionRefinedCellIndex W p radialIncremented incremented k where
  state := ⟨W.rootExtensionPrefixState p radialIncremented incremented id k X,
    (W.mem_rootExtensionPrefixStateFinset_iff p radialIncremented incremented k _).mpr
      ⟨X, rfl⟩⟩
  backgroundPattern := realizedRootRadialThresholdPattern d m n p X
  incrementPattern := realizedRootRadialThresholdPattern d m n radialIncremented X
  finalPattern := realizedRootRadialThresholdPattern d m n pFinal X

/-- A realization belonging to its reachable state history also belongs to its fully refined
root cell. -/
theorem RootRadialSeedProfile.mem_realizedRootExtensionRefinedCell_profile
    {d m n : ℕ} (W : RootRadialSeedProfile d m n)
    (p radialIncremented pFinal : I) (incremented : RootExtensionThresholdPolicy d)
    (k : ℕ) (X : CubicEdge d → ℝ)
    (hX : X ∈ (W.rootExtensionPrefixState p radialIncremented incremented id k X).historyProfile.event) :
    X ∈ ((W.realizedRootExtensionRefinedCell
      p radialIncremented pFinal incremented k X).profile pFinal).event := by
  rw [RootExtensionRefinedCellIndex.profile_event_eq]
  refine ⟨⟨⟨hX, ?_⟩, ?_⟩, ?_⟩
  · exact (physical_realizedRootRadialThresholdPattern d m n p X).symm
  · exact (physical_realizedRootRadialThresholdPattern d m n radialIncremented X).symm
  · exact (physical_realizedRootRadialThresholdPattern d m n pFinal X).symm

/-- Canonical label representative of a reachable prefix state. -/
noncomputable def RootRadialSeedProfile.rootExtensionPrefixRepresentative
    {d m n : ℕ} (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (incremented : RootExtensionThresholdPolicy d) (k : ℕ) :
    RootExtensionPrefixStateIndex W p radialIncremented incremented k →
      CubicEdge d → ℝ := fun c ↦
  Classical.choose
    ((W.mem_rootExtensionPrefixStateFinset_iff p radialIncremented incremented k c.1).mp c.2)

@[simp]
theorem RootRadialSeedProfile.rootExtensionPrefixState_representative
    {d m n : ℕ} (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (incremented : RootExtensionThresholdPolicy d) (k : ℕ)
    (c : RootExtensionPrefixStateIndex W p radialIncremented incremented k) :
    W.rootExtensionPrefixState p radialIncremented incremented
      (W.rootExtensionPrefixRepresentative p radialIncremented incremented k) k c = c.1 :=
  Classical.choose_spec
    ((W.mem_rootExtensionPrefixStateFinset_iff p radialIncremented incremented k c.1).mp c.2)

/-- Union of all concrete accumulated-history cells reachable before slot `k`. -/
def RootRadialSeedProfile.rootExtensionPrefixHistory
    {d m n : ℕ} (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (incremented : RootExtensionThresholdPolicy d) (k : ℕ) :
    Set (CubicEdge d → ℝ) :=
  ⋃ c : RootExtensionPrefixStateIndex W p radialIncremented incremented k,
    c.1.historyProfile.event

theorem RootRadialSeedProfile.historyProfile_subset_rootExtensionPrefixHistory
    {d m n : ℕ} (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (incremented : RootExtensionThresholdPolicy d) (k : ℕ)
    (c : RootExtensionPrefixStateIndex W p radialIncremented incremented k) :
    c.1.historyProfile.event ⊆
      W.rootExtensionPrefixHistory p radialIncremented incremented k :=
  Set.subset_iUnion (fun c : RootExtensionPrefixStateIndex W p radialIncremented incremented k ↦
    c.1.historyProfile.event) c

theorem RootRadialSeedProfile.pairwiseDisjoint_rootExtensionPrefixHistory
    {d m n : ℕ} (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (incremented : RootExtensionThresholdPolicy d)
    (hincremented : ∀ S b e, S.lower e ≤ incremented S b e) (k : ℕ) :
    ∀ c c' : RootExtensionPrefixStateIndex W p radialIncremented incremented k,
      c ≠ c' → Disjoint c.1.historyProfile.event c'.1.historyProfile.event := by
  intro c c' hne
  apply W.disjoint_historyProfile_of_mem_prefixStateRange
      p radialIncremented incremented hincremented k
  · exact (W.mem_rootExtensionPrefixStateFinset_iff
      p radialIncremented incremented k c.1).mp c.2
  · exact (W.mem_rootExtensionPrefixStateFinset_iff
      p radialIncremented incremented k c'.1).mp c'.2
  · intro hval
    exact hne (Subtype.ext hval)

/-! ### Event-stable subpartitions of the reachable state cells -/

/-- A reachable root-prefix state whose complete accumulated-history cell is contained in a
semantic event `A`.  This is the source-faithful way to retain an earlier success event: the
cell itself is unchanged, so no current boundary threshold is strengthened and the already
proved restart-support freshness remains available. -/
abbrev StableRootExtensionPrefixStateIndex
    {d m n : ℕ} (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (incremented : RootExtensionThresholdPolicy d) (k : ℕ)
    (A : Set (CubicEdge d → ℝ)) :=
  {c : RootExtensionPrefixStateIndex W p radialIncremented incremented k //
    c.1.historyProfile.event ⊆ A}

noncomputable instance stableRootExtensionPrefixStateIndexFintype
    {d m n : ℕ} (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (incremented : RootExtensionThresholdPolicy d) (k : ℕ)
    (A : Set (CubicEdge d → ℝ)) :
    Fintype (StableRootExtensionPrefixStateIndex
      W p radialIncremented incremented k A) :=
  Fintype.ofFinite _

noncomputable instance stableRootExtensionPrefixStateIndexDecidableEq
    {d m n : ℕ} (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (incremented : RootExtensionThresholdPolicy d) (k : ℕ)
    (A : Set (CubicEdge d → ℝ)) :
    DecidableEq (StableRootExtensionPrefixStateIndex
      W p radialIncremented incremented k A) :=
  Classical.decEq _

/-- Union of precisely those canonical reachable cells on which `A` is stable. -/
def RootRadialSeedProfile.stableRootExtensionPrefixHistory
    {d m n : ℕ} (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (incremented : RootExtensionThresholdPolicy d) (k : ℕ)
    (A : Set (CubicEdge d → ℝ)) : Set (CubicEdge d → ℝ) :=
  ⋃ c : StableRootExtensionPrefixStateIndex
      W p radialIncremented incremented k A,
    c.1.1.historyProfile.event

/-- Every retained stable cell lies in the semantic event by construction. -/
theorem RootRadialSeedProfile.stableRootExtensionPrefixHistory_subset
    {d m n : ℕ} (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (incremented : RootExtensionThresholdPolicy d) (k : ℕ)
    (A : Set (CubicEdge d → ℝ)) :
    W.stableRootExtensionPrefixHistory p radialIncremented incremented k A ⊆ A := by
  intro X hX
  rw [RootRadialSeedProfile.stableRootExtensionPrefixHistory, Set.mem_iUnion] at hX
  obtain ⟨c, hc⟩ := hX
  exact c.2 hc

/-- A point of `A` belongs to the stable subpartition as soon as one canonical cell containing
it has been proved stable.  This statement isolates the remaining radial-success obligation
without introducing a stronger label-space fiber. -/
theorem RootRadialSeedProfile.mem_stableRootExtensionPrefixHistory_of_cell
    {d m n : ℕ} (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (incremented : RootExtensionThresholdPolicy d) (k : ℕ)
    (A : Set (CubicEdge d → ℝ))
    (c : RootExtensionPrefixStateIndex W p radialIncremented incremented k)
    (hstable : c.1.historyProfile.event ⊆ A)
    {X : CubicEdge d → ℝ} (hX : X ∈ c.1.historyProfile.event) :
    X ∈ W.stableRootExtensionPrefixHistory p radialIncremented incremented k A := by
  rw [RootRadialSeedProfile.stableRootExtensionPrefixHistory, Set.mem_iUnion]
  exact ⟨⟨c, hstable⟩, hX⟩

/-- Exact characterization of a stable subhistory from a pointwise canonical-cell stability
proof.  The reverse inclusion is automatic and the forward inclusion asks only for the actual
semantic theorem, not for any additional threshold-pattern reveal. -/
theorem RootRadialSeedProfile.stableRootExtensionPrefixHistory_eq
    {d m n : ℕ} (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (incremented : RootExtensionThresholdPolicy d) (k : ℕ)
    (A : Set (CubicEdge d → ℝ))
    (hcell : ∀ X ∈ A,
      let c : RootExtensionPrefixStateIndex W p radialIncremented incremented k :=
        ⟨W.rootExtensionPrefixState p radialIncremented incremented id k X,
          (W.mem_rootExtensionPrefixStateFinset_iff
            p radialIncremented incremented k _).mpr ⟨X, rfl⟩⟩
      c.1.historyProfile.event ⊆ A)
    (hrealize : ∀ X ∈ A,
      X ∈ (W.rootExtensionPrefixState
        p radialIncremented incremented id k X).historyProfile.event) :
    W.stableRootExtensionPrefixHistory p radialIncremented incremented k A = A := by
  apply Set.Subset.antisymm
  · exact W.stableRootExtensionPrefixHistory_subset
      p radialIncremented incremented k A
  · intro X hXA
    let c : RootExtensionPrefixStateIndex W p radialIncremented incremented k :=
      ⟨W.rootExtensionPrefixState p radialIncremented incremented id k X,
        (W.mem_rootExtensionPrefixStateFinset_iff
          p radialIncremented incremented k _).mpr ⟨X, rfl⟩⟩
    exact W.mem_stableRootExtensionPrefixHistory_of_cell
      p radialIncremented incremented k A c (hcell X hXA) (hrealize X hXA)

/-- On the probability-one common-uniform support, the stable unchanged-cell subpartition
covers every radial-success realization. -/
theorem RootRadialSeedProfile.rootRadialEvent_inter_nonnegative_subset_stablePrefixHistory
    {d m n : ℕ} [NeZero d] (hm : 1 ≤ m) (hmn : m + 1 ≤ n)
    (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (delta : ℝ)
    (hdelta : delta = (radialIncremented : ℝ))
    (incremented : RootExtensionThresholdPolicy d)
    (hincremented : ∀ S b e, S.lower e ≤ incremented S b e) (k : ℕ) :
    rootRadialEvent d m n p delta ∩
        SourceFiniteEdgeRevealState.nonnegativeCouplingEvent ⊆
      W.stableRootExtensionPrefixHistory p radialIncremented incremented k
        (rootRadialEvent d m n p delta) := by
  intro X hX
  let S := W.rootExtensionPrefixState p radialIncremented incremented id k X
  let c : RootExtensionPrefixStateIndex W p radialIncremented incremented k :=
    ⟨S, (W.mem_rootExtensionPrefixStateFinset_iff
      p radialIncremented incremented k S).mpr ⟨X, rfl⟩⟩
  apply W.mem_stableRootExtensionPrefixHistory_of_cell
    p radialIncremented incremented k (rootRadialEvent d m n p delta) c
  · intro Y hY
    exact W.rootRadialEvent_of_mem_prefixHistoryProfile
      hm hmn p radialIncremented hdelta incremented hincremented k X Y hX.1 hY
  · change X ∈ S.historyProfile.event
    exact W.mem_runPostRadialExtensions_historyProfile p incremented X
      ((rootExtensionDirectionOrder d).take k)
      (rootPostRadialSourceEdgeState d m n p radialIncremented X) hX.2
      (rootRadialEvent_mem_postRadialSourceHistoryProfile
        p radialIncremented delta X hX.1 hX.2)

/-- Exact almost-sure identity: restricting the unchanged stable-cell union to the common
uniform support recovers precisely the original simultaneous radial event there. -/
theorem RootRadialSeedProfile.stablePrefixHistory_inter_nonnegative_eq_rootRadial
    {d m n : ℕ} [NeZero d] (hm : 1 ≤ m) (hmn : m + 1 ≤ n)
    (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (delta : ℝ)
    (hdelta : delta = (radialIncremented : ℝ))
    (incremented : RootExtensionThresholdPolicy d)
    (hincremented : ∀ S b e, S.lower e ≤ incremented S b e) (k : ℕ) :
    W.stableRootExtensionPrefixHistory p radialIncremented incremented k
          (rootRadialEvent d m n p delta) ∩
        SourceFiniteEdgeRevealState.nonnegativeCouplingEvent =
      rootRadialEvent d m n p delta ∩
        SourceFiniteEdgeRevealState.nonnegativeCouplingEvent := by
  apply Set.Subset.antisymm
  · intro X hX
    exact ⟨W.stableRootExtensionPrefixHistory_subset
      p radialIncremented incremented k (rootRadialEvent d m n p delta) hX.1, hX.2⟩
  · intro X hX
    exact ⟨W.rootRadialEvent_inter_nonnegative_subset_stablePrefixHistory
      hm hmn p radialIncremented delta hdelta incremented hincremented k hX, hX.2⟩

/-- On the common-uniform support, the unchanged stable cells at prefix `k` cover the complete
semantic event consisting of radial success and the first `k` successful extensions. -/
theorem RootRadialSeedProfile.rootExtensionPrefixSuccess_inter_nonnegative_subset_stableHistory
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
    W.rootExtensionPrefixSuccessEvent p radialIncremented delta incremented k ∩
        SourceFiniteEdgeRevealState.nonnegativeCouplingEvent ⊆
      W.stableRootExtensionPrefixHistory p radialIncremented incremented k
        (W.rootExtensionPrefixSuccessEvent p radialIncremented delta incremented k) := by
  intro X hX
  let S := W.rootExtensionPrefixState p radialIncremented incremented id k X
  let c : RootExtensionPrefixStateIndex W p radialIncremented incremented k :=
    ⟨S, (W.mem_rootExtensionPrefixStateFinset_iff
      p radialIncremented incremented k S).mpr ⟨X, rfl⟩⟩
  apply W.mem_stableRootExtensionPrefixHistory_of_cell
    p radialIncremented incremented k
      (W.rootExtensionPrefixSuccessEvent p radialIncremented delta incremented k) c
  · intro Y hY
    exact W.rootExtensionPrefixSuccessEvent_of_mem_historyProfile
      hm hmn p radialIncremented delta hdelta hradialDelta incremented
        hincremented hadds hgeom hk
        X Y hX.1 hY
  · change X ∈ S.historyProfile.event
    exact W.mem_runPostRadialExtensions_historyProfile p incremented X
      ((rootExtensionDirectionOrder d).take k)
      (rootPostRadialSourceEdgeState d m n p radialIncremented X) hX.2
      (rootRadialEvent_mem_postRadialSourceHistoryProfile
        p radialIncremented delta X hX.1.1 hX.2)

/-- Exact almost-sure stable-cell identity for the full successful root prefix. -/
theorem RootRadialSeedProfile.stableHistory_inter_nonnegative_eq_rootExtensionPrefixSuccess
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
    W.stableRootExtensionPrefixHistory p radialIncremented incremented k
          (W.rootExtensionPrefixSuccessEvent p radialIncremented delta incremented k) ∩
        SourceFiniteEdgeRevealState.nonnegativeCouplingEvent =
      W.rootExtensionPrefixSuccessEvent p radialIncremented delta incremented k ∩
        SourceFiniteEdgeRevealState.nonnegativeCouplingEvent := by
  apply Set.Subset.antisymm
  · intro X hX
    exact ⟨W.stableRootExtensionPrefixHistory_subset
      p radialIncremented incremented k
        (W.rootExtensionPrefixSuccessEvent p radialIncremented delta incremented k) hX.1,
      hX.2⟩
  · intro X hX
    exact ⟨W.rootExtensionPrefixSuccess_inter_nonnegative_subset_stableHistory
      hm hmn p radialIncremented delta hdelta hradialDelta incremented
        hincremented hadds hgeom hk hX,
      hX.2⟩

/-- Stable subhistory cells inherit pairwise disjointness from the full reachable-state
partition. -/
theorem RootRadialSeedProfile.pairwiseDisjoint_stableRootExtensionPrefixHistory
    {d m n : ℕ} (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (incremented : RootExtensionThresholdPolicy d)
    (hincremented : ∀ S b e, S.lower e ≤ incremented S b e) (k : ℕ)
    (A : Set (CubicEdge d → ℝ)) :
    ∀ c c' : StableRootExtensionPrefixStateIndex
        W p radialIncremented incremented k A,
      c ≠ c' → Disjoint c.1.1.historyProfile.event c'.1.1.historyProfile.event := by
  intro c c' hne
  apply W.pairwiseDisjoint_rootExtensionPrefixHistory
      p radialIncremented incremented hincremented k c.1 c'.1
  intro hval
  exact hne (Subtype.ext hval)

/-! ### Exact radial-witness refinement of the reachable partition -/

/-- Finite event that the canonical final-density selected seed in every radial direction is
the prescribed profile `W`. -/
def RootRadialSeedProfile.selectedSeedEvent
    {d m n : ℕ} (W : RootRadialSeedProfile d m n) (pFinal : I) :
    Set (CubicEdge d → ℝ) :=
  {X | ∀ a : CubicDirection d,
    rootRadialSelectedSeed d m n pFinal a X = some (W a)}

/-- A refined prefix cell is retained precisely when it contains a radial success with the
prescribed selected-seed profile.  Pattern stability below proves that then every realization
in the cell has the same property. -/
def RootExtensionRefinedCellIndex.Compatible
    {d m n : ℕ} {W : RootRadialSeedProfile d m n}
    {p radialIncremented : I} {incremented : RootExtensionThresholdPolicy d} {k : ℕ}
    (pFinal : I) (delta : ℝ)
    (c : RootExtensionRefinedCellIndex W p radialIncremented incremented k) : Prop :=
  ∃ X : CubicEdge d → ℝ,
    X ∈ (c.profile pFinal).event ∧
      X ∈ rootRadialEvent d m n p delta ∧ X ∈ W.selectedSeedEvent pFinal

/-- Finite type of compatible refined root cells. -/
abbrev CompatibleRootExtensionRefinedCellIndex
    {d m n : ℕ} (W : RootRadialSeedProfile d m n)
    (p radialIncremented pFinal : I) (delta : ℝ)
    (incremented : RootExtensionThresholdPolicy d) (k : ℕ) :=
  {c : RootExtensionRefinedCellIndex W p radialIncremented incremented k //
    c.Compatible pFinal delta}

noncomputable instance compatibleRootExtensionRefinedCellIndexFintype
    {d m n : ℕ} (W : RootRadialSeedProfile d m n)
    (p radialIncremented pFinal : I) (delta : ℝ)
    (incremented : RootExtensionThresholdPolicy d) (k : ℕ) :
    Fintype (CompatibleRootExtensionRefinedCellIndex
      W p radialIncremented pFinal delta incremented k) :=
  Fintype.ofFinite _

/-- Exact finite union of all compatible refined accumulated-history cells. -/
def RootRadialSeedProfile.refinedRootExtensionPrefixHistory
    {d m n : ℕ} (W : RootRadialSeedProfile d m n)
    (p radialIncremented pFinal : I) (delta : ℝ)
    (incremented : RootExtensionThresholdPolicy d) (k : ℕ) :
    Set (CubicEdge d → ℝ) :=
  ⋃ c : CompatibleRootExtensionRefinedCellIndex
      W p radialIncremented pFinal delta incremented k,
    (c.1.profile pFinal).event

/-- Every compatible refined cell consists only of radial successes with the same selected
seed profile and lies inside the reachable prefix-history union. -/
theorem RootRadialSeedProfile.refinedCell_subset_radial_selected_prefixHistory
    {d m n : ℕ} (W : RootRadialSeedProfile d m n)
    (p radialIncremented pFinal : I) (delta : ℝ)
    (hdelta : delta = (radialIncremented : ℝ))
    (incremented : RootExtensionThresholdPolicy d) (k : ℕ)
    (c : CompatibleRootExtensionRefinedCellIndex
      W p radialIncremented pFinal delta incremented k) :
    (c.1.profile pFinal).event ⊆
      (rootRadialEvent d m n p delta ∩ W.selectedSeedEvent pFinal) ∩
        W.rootExtensionPrefixHistory p radialIncremented incremented k := by
  intro Y hY
  obtain ⟨X, hX, hXRadial, hXSelected⟩ := c.2
  rw [RootExtensionRefinedCellIndex.profile_event_eq] at hX hY
  have hp : FiniteRevealIntervalProfile.labelsBelow
      (rootRadialEdgeSupport d m n) p X =
        FiniteRevealIntervalProfile.labelsBelow
          (rootRadialEdgeSupport d m n) p Y :=
    hX.1.1.2.trans hY.1.1.2.symm
  have hincremented : FiniteRevealIntervalProfile.labelsBelow
      (rootRadialEdgeSupport d m n) radialIncremented X =
        FiniteRevealIntervalProfile.labelsBelow
          (rootRadialEdgeSupport d m n) radialIncremented Y :=
    hX.1.2.trans hY.1.2.symm
  have hpFinal : FiniteRevealIntervalProfile.labelsBelow
      (rootRadialEdgeSupport d m n) pFinal X =
        FiniteRevealIntervalProfile.labelsBelow
          (rootRadialEdgeSupport d m n) pFinal Y :=
    hX.2.trans hY.2.symm
  refine ⟨⟨(rootRadialEvent_congr_of_labelsBelow_rootRadialEdgeSupport
    hdelta hp hincremented).mp hXRadial, ?_⟩, ?_⟩
  · intro a
    exact (rootRadialSelectedSeed_congr_of_labelsBelow_rootRadialEdgeSupport
      a hpFinal) ▸ hXSelected a
  · exact W.historyProfile_subset_rootExtensionPrefixHistory
      p radialIncremented incremented k c.1.state hY.1.1.1

/-- The union of compatible refined cells has the same semantic upper bound. -/
theorem RootRadialSeedProfile.refinedRootExtensionPrefixHistory_subset
    {d m n : ℕ} (W : RootRadialSeedProfile d m n)
    (p radialIncremented pFinal : I) (delta : ℝ)
    (hdelta : delta = (radialIncremented : ℝ))
    (incremented : RootExtensionThresholdPolicy d) (k : ℕ) :
    W.refinedRootExtensionPrefixHistory p radialIncremented pFinal delta incremented k ⊆
      (rootRadialEvent d m n p delta ∩ W.selectedSeedEvent pFinal) ∩
        W.rootExtensionPrefixHistory p radialIncremented incremented k := by
  intro X hX
  rw [RootRadialSeedProfile.refinedRootExtensionPrefixHistory, Set.mem_iUnion] at hX
  obtain ⟨c, hc⟩ := hX
  exact W.refinedCell_subset_radial_selected_prefixHistory
    p radialIncremented pFinal delta hdelta incremented k c hc

/-- On the probability-one common-uniform support, every radial success with selected profile
`W` belongs to its canonically realized compatible refined cell. -/
theorem RootRadialSeedProfile.radial_selected_nonnegative_subset_refinedPrefixHistory
    {d m n : ℕ} [NeZero d] (W : RootRadialSeedProfile d m n)
    (p radialIncremented pFinal : I) (delta : ℝ)
    (incremented : RootExtensionThresholdPolicy d) (k : ℕ) :
    (rootRadialEvent d m n p delta ∩ W.selectedSeedEvent pFinal) ∩
        SourceFiniteEdgeRevealState.nonnegativeCouplingEvent ⊆
      W.refinedRootExtensionPrefixHistory
        p radialIncremented pFinal delta incremented k := by
  rintro X ⟨⟨hRadial, hSelected⟩, hNonnegative⟩
  have hState : X ∈
      (W.rootExtensionPrefixState p radialIncremented incremented id k X).historyProfile.event :=
    W.mem_runPostRadialExtensions_historyProfile p incremented X
      ((rootExtensionDirectionOrder d).take k)
      (rootPostRadialSourceEdgeState d m n p radialIncremented X) hNonnegative
      (rootRadialEvent_mem_postRadialSourceHistoryProfile
        p radialIncremented delta X hRadial hNonnegative)
  let c := W.realizedRootExtensionRefinedCell
    p radialIncremented pFinal incremented k X
  have hc : X ∈ (c.profile pFinal).event :=
    W.mem_realizedRootExtensionRefinedCell_profile
      p radialIncremented pFinal incremented k X hState
  have hcompatible : c.Compatible pFinal delta :=
    ⟨X, hc, hRadial, hSelected⟩
  rw [RootRadialSeedProfile.refinedRootExtensionPrefixHistory, Set.mem_iUnion]
  exact ⟨⟨c, hcompatible⟩, hc⟩

/-- Exact almost-sure identity: after intersecting with the common-uniform support, the
compatible finite interval partition is precisely the radial event with selected profile `W`.
This is the source-faithful replacement for the earlier one-sided coverage statement. -/
theorem RootRadialSeedProfile.refinedPrefixHistory_inter_nonnegative_eq
    {d m n : ℕ} [NeZero d] (W : RootRadialSeedProfile d m n)
    (p radialIncremented pFinal : I) (delta : ℝ)
    (hdelta : delta = (radialIncremented : ℝ))
    (incremented : RootExtensionThresholdPolicy d) (k : ℕ) :
    W.refinedRootExtensionPrefixHistory p radialIncremented pFinal delta incremented k ∩
        SourceFiniteEdgeRevealState.nonnegativeCouplingEvent =
      (rootRadialEvent d m n p delta ∩ W.selectedSeedEvent pFinal) ∩
        SourceFiniteEdgeRevealState.nonnegativeCouplingEvent := by
  apply Set.Subset.antisymm
  · rintro X ⟨hRefined, hNonnegative⟩
    exact ⟨(W.refinedRootExtensionPrefixHistory_subset
      p radialIncremented pFinal delta hdelta incremented k hRefined).1, hNonnegative⟩
  · intro X hX
    exact ⟨W.radial_selected_nonnegative_subset_refinedPrefixHistory
      p radialIncremented pFinal delta incremented k hX, hX.2⟩

/-- Compatible refined cells are pairwise disjoint. -/
theorem RootRadialSeedProfile.pairwiseDisjoint_refinedRootExtensionPrefixHistory
    {d m n : ℕ} (W : RootRadialSeedProfile d m n)
    (p radialIncremented pFinal : I) (delta : ℝ)
    (incremented : RootExtensionThresholdPolicy d)
    (hincremented : ∀ S b e, S.lower e ≤ incremented S b e) (k : ℕ) :
    ∀ c c' : CompatibleRootExtensionRefinedCellIndex
      W p radialIncremented pFinal delta incremented k,
      c ≠ c' → Disjoint (c.1.profile pFinal).event (c'.1.profile pFinal).event := by
  intro c c' hne
  rw [Set.disjoint_left]
  intro X hX hX'
  rw [RootExtensionRefinedCellIndex.profile_event_eq] at hX hX'
  have hstate : c.1.state = c'.1.state := by
    by_contra hstateNe
    exact Set.disjoint_left.mp
      (W.pairwiseDisjoint_rootExtensionPrefixHistory
        p radialIncremented incremented hincremented k c.1.state c'.1.state hstateNe)
      hX.1.1.1 hX'.1.1.1
  have hbackground : c.1.backgroundPattern = c'.1.backgroundPattern := by
    apply Finset.map_injective (Function.Embedding.subtype _)
    exact hX.1.1.2.symm.trans hX'.1.1.2
  have hinc : c.1.incrementPattern = c'.1.incrementPattern := by
    apply Finset.map_injective (Function.Embedding.subtype _)
    exact hX.1.2.symm.trans hX'.1.2
  have hfinal : c.1.finalPattern = c'.1.finalPattern := by
    apply Finset.map_injective (Function.Embedding.subtype _)
    exact hX.2.symm.trans hX'.2
  apply hne
  apply Subtype.ext
  exact rootExtensionRefinedCellIndex_ext hstate hbackground hinc hfinal

/-- Every radial-success realization on the common-uniform support belongs to one concrete
reachable prefix history cell. -/
theorem RootRadialSeedProfile.rootRadialEvent_inter_nonnegative_subset_prefixHistory
    {d m n : ℕ} [NeZero d] (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (delta : ℝ)
    (incremented : RootExtensionThresholdPolicy d) (k : ℕ) :
    rootRadialEvent d m n p delta ∩
        SourceFiniteEdgeRevealState.nonnegativeCouplingEvent ⊆
      W.rootExtensionPrefixHistory p radialIncremented incremented k := by
  intro X hX
  let S := W.rootExtensionPrefixState p radialIncremented incremented id k X
  let c : RootExtensionPrefixStateIndex W p radialIncremented incremented k :=
    ⟨S, (W.mem_rootExtensionPrefixStateFinset_iff
      p radialIncremented incremented k S).mpr ⟨X, rfl⟩⟩
  apply W.historyProfile_subset_rootExtensionPrefixHistory
    p radialIncremented incremented k c
  change X ∈ S.historyProfile.event
  exact W.mem_runPostRadialExtensions_historyProfile p incremented X
    ((rootExtensionDirectionOrder d).take k)
    (rootPostRadialSourceEdgeState d m n p radialIncremented X) hX.2
    (rootRadialEvent_mem_postRadialSourceHistoryProfile
      p radialIncremented delta X hX.1 hX.2)

namespace AdaptiveSiteExploration

variable {C : Type*} [Fintype C] [DecidableEq C]

/-- Canonical reachable prefix-state index used as the default classifier value. -/
noncomputable def RootRadialSeedProfile.rootExtensionPrefixDefault
    {d m n : ℕ} (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (incremented : RootExtensionThresholdPolicy d) (k : ℕ) :
    RootExtensionPrefixStateIndex W p radialIncremented incremented k := by
  let X : CubicEdge d → ℝ := 0
  let S := W.rootExtensionPrefixState p radialIncremented incremented id k X
  exact ⟨S, (W.mem_rootExtensionPrefixStateFinset_iff
    p radialIncremented incremented k S).mpr ⟨X, rfl⟩⟩

/-- Construct the `k`-th root-extension stage from exact finite interval fibers.  All geometric
freshness premises of the generic partition theorem are discharged by the sequential steering
theorem; the remaining inputs are precisely the exact fiber identity and Lemma 7.17's
ratio-free restart estimate on each cell. -/
noncomputable def RootRadialSeedProfile.partitionedRootExtensionStage
    {d m n : ℕ} [NeZero d] (hm : 1 ≤ m) (hmn : m + 1 < n)
    (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (delta epsilon : ℝ)
    (incremented : RootExtensionThresholdPolicy d)
    (history : Set (CubicEdge d → ℝ))
    (realizedCell : (CubicEdge d → ℝ) → C)
    (representative : C → CubicEdge d → ℝ)
    (hgeom : ∀ a : CubicDirection d,
      SeedBoxWithinBoundaryLayer d a.1 m n (W a).seedCenter.1)
    {k : ℕ} (hk : k < (rootExtensionDirectionOrder d).length)
    (hfiber : ∀ c,
      (W.rootExtensionPrefixState p radialIncremented incremented representative k c).historyProfile.event =
        exactRevealCellEvent history realizedCell c)
    (hrestart : ∀ c,
      let a := (rootExtensionDirectionOrder d)[k]
      let S := W.rootExtensionPrefixState p radialIncremented incremented representative k c
      let Q := S.framedQuery (W.physicalCenter a) a
        (oppositeTransverseRestartFlip a)
      (1 - epsilon) * (couplingMeasure (CubicEdge d)).real
          (Q.boundaryHistoryEvent n) <
        (couplingMeasure (CubicEdge d)).real
          (Q.successEvent m n p delta ∩ Q.boundaryHistoryEvent n)) :
    PartitionedFramedRestartStage d C m n p delta epsilon := by
  let a := (rootExtensionDirectionOrder d)[k]
  apply PartitionedFramedRestartStage.ofCanonicalSourceEdgeStateRealizationOfTargetEndpointFresh
      history realizedCell (fun _ ↦ W.physicalCenter a) (fun _ ↦ a)
      (fun _ ↦ oppositeTransverseRestartFlip a)
      (fun c ↦ W.rootExtensionPrefixState p radialIncremented incremented representative k c)
  · intro c
    simpa [RootRadialSeedProfile.rootExtensionPrefixState,
      RootRadialSeedProfile.postRadialFrame, a] using
        (rootPostRadialExtensions_prefix_targetEndpointFresh_of_geometry
          hm hmn W p radialIncremented incremented (representative c) hgeom hk)
  · exact hfiber
  · simpa [a] using hrestart

/-- Construct the `k`-th root-extension stage directly from a finite partition by interval
profiles.  Unlike `partitionedRootExtensionStage`, this interface does not ask the caller to
invent a realized-cell function or prove its fibers by hand: the canonical classifier from
`DynamicRevealIntervals` supplies both. -/
noncomputable def RootRadialSeedProfile.partitionedRootExtensionStageOfProfilePartition
    {d m n : ℕ} [NeZero d] (hm : 1 ≤ m) (hmn : m + 1 < n)
    (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (delta epsilon : ℝ)
    (incremented : RootExtensionThresholdPolicy d)
    (history : Set (CubicEdge d → ℝ))
    (default : C)
    (representative : C → CubicEdge d → ℝ)
    (hgeom : ∀ a : CubicDirection d,
      SeedBoxWithinBoundaryLayer d a.1 m n (W a).seedCenter.1)
    {k : ℕ} (hk : k < (rootExtensionDirectionOrder d).length)
    (hsub : ∀ c,
      (W.rootExtensionPrefixState p radialIncremented incremented representative k c).historyProfile.event
        ⊆ history)
    (hcover : history ⊆ ⋃ c,
      (W.rootExtensionPrefixState p radialIncremented incremented representative k c).historyProfile.event)
    (hpairwise : ∀ c c', c ≠ c' → Disjoint
      (W.rootExtensionPrefixState p radialIncremented incremented representative k c).historyProfile.event
      (W.rootExtensionPrefixState p radialIncremented incremented representative k c').historyProfile.event)
    (hrestart : ∀ c,
      let a := (rootExtensionDirectionOrder d)[k]
      let S := W.rootExtensionPrefixState p radialIncremented incremented representative k c
      let Q := S.framedQuery (W.physicalCenter a) a
        (oppositeTransverseRestartFlip a)
      (1 - epsilon) * (couplingMeasure (CubicEdge d)).real
          (Q.boundaryHistoryEvent n) <
        (couplingMeasure (CubicEdge d)).real
          (Q.successEvent m n p delta ∩ Q.boundaryHistoryEvent n)) :
    PartitionedFramedRestartStage d C m n p delta epsilon := by
  let profile : C → FiniteRevealIntervalProfile (CubicEdge d) := fun c ↦
    (W.rootExtensionPrefixState p radialIncremented incremented representative k c).historyProfile
  let realizedCell : (CubicEdge d → ℝ) → C :=
    realizedIntervalProfileCell default profile
  apply RootRadialSeedProfile.partitionedRootExtensionStage hm hmn W p radialIncremented
    delta epsilon incremented history realizedCell representative hgeom hk
  · intro c
    exact intervalProfile_event_eq_exactRevealCellEvent default profile history
      hsub hcover hpairwise c
  · exact hrestart

/-- The canonical interval-profile classifier retains the whole supplied prefix history. -/
theorem RootRadialSeedProfile.partitionedRootExtensionStageOfProfilePartition_cellUnion
    {d m n : ℕ} [NeZero d] (hm : 1 ≤ m) (hmn : m + 1 < n)
    (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (delta epsilon : ℝ)
    (incremented : RootExtensionThresholdPolicy d)
    (history : Set (CubicEdge d → ℝ))
    (default : C)
    (representative : C → CubicEdge d → ℝ)
    (hgeom : ∀ a : CubicDirection d,
      SeedBoxWithinBoundaryLayer d a.1 m n (W a).seedCenter.1)
    {k : ℕ} (hk : k < (rootExtensionDirectionOrder d).length)
    (hsub : ∀ c,
      (W.rootExtensionPrefixState p radialIncremented incremented representative k c).historyProfile.event
        ⊆ history)
    (hcover : history ⊆ ⋃ c,
      (W.rootExtensionPrefixState p radialIncremented incremented representative k c).historyProfile.event)
    (hpairwise : ∀ c c', c ≠ c' → Disjoint
      (W.rootExtensionPrefixState p radialIncremented incremented representative k c).historyProfile.event
      (W.rootExtensionPrefixState p radialIncremented incremented representative k c').historyProfile.event)
    (hrestart : ∀ c,
      let a := (rootExtensionDirectionOrder d)[k]
      let S := W.rootExtensionPrefixState p radialIncremented incremented representative k c
      let Q := S.framedQuery (W.physicalCenter a) a
        (oppositeTransverseRestartFlip a)
      (1 - epsilon) * (couplingMeasure (CubicEdge d)).real
          (Q.boundaryHistoryEvent n) <
        (couplingMeasure (CubicEdge d)).real
          (Q.successEvent m n p delta ∩ Q.boundaryHistoryEvent n)) :
    (RootRadialSeedProfile.partitionedRootExtensionStageOfProfilePartition
      hm hmn W p radialIncremented delta epsilon incremented history default representative
      hgeom hk hsub hcover hpairwise hrestart).cellUnion = history := by
  classical
  unfold RootRadialSeedProfile.partitionedRootExtensionStageOfProfilePartition
  unfold RootRadialSeedProfile.partitionedRootExtensionStage
  apply PartitionedFramedRestartStage.cellUnion_ofCanonicalSourceEdgeStateRealizationOfTargetEndpointFresh

/-- Construct the `k`-th root stage on an event-stable subfamily of the canonical reachable
state cells.  Unlike a threshold-pattern refinement, this construction leaves every interval
profile unchanged; consequently all boundary thresholds and residual-freshness theorems from
the source recursion apply verbatim. -/
noncomputable def RootRadialSeedProfile.partitionedRootExtensionStageOfStableHistory
    {d m n : ℕ} [NeZero d] (hm : 1 ≤ m) (hmn : m + 1 < n)
    (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (delta epsilon : ℝ)
    (incremented : RootExtensionThresholdPolicy d)
    (hincremented : ∀ S b e, S.lower e ≤ incremented S b e)
    {k : ℕ}
    (A : Set (CubicEdge d → ℝ))
    (hnonempty : Nonempty (StableRootExtensionPrefixStateIndex
      W p radialIncremented incremented k A))
    (hgeom : ∀ a : CubicDirection d,
      SeedBoxWithinBoundaryLayer d a.1 m n (W a).seedCenter.1)
    (hk : k < (rootExtensionDirectionOrder d).length)
    (hrestart : ∀ c : StableRootExtensionPrefixStateIndex
        W p radialIncremented incremented k A,
      let a := (rootExtensionDirectionOrder d)[k]
      let S := c.1.1
      let Q := S.framedQuery (W.physicalCenter a) a
        (oppositeTransverseRestartFlip a)
      (1 - epsilon) * (couplingMeasure (CubicEdge d)).real
          (Q.boundaryHistoryEvent n) <
        (couplingMeasure (CubicEdge d)).real
          (Q.successEvent m n p delta ∩ Q.boundaryHistoryEvent n)) :
    PartitionedFramedRestartStage d
      (StableRootExtensionPrefixStateIndex
        W p radialIncremented incremented k A)
      m n p delta epsilon := by
  let representative : StableRootExtensionPrefixStateIndex
      W p radialIncremented incremented k A → CubicEdge d → ℝ := fun c ↦
    W.rootExtensionPrefixRepresentative p radialIncremented incremented k c.1
  have hrepresentative : ∀ c : StableRootExtensionPrefixStateIndex
      W p radialIncremented incremented k A,
      W.rootExtensionPrefixState p radialIncremented incremented representative k c =
        c.1.1 := by
    intro c
    change W.rootExtensionPrefixState p radialIncremented incremented
      (W.rootExtensionPrefixRepresentative p radialIncremented incremented k) k c.1 =
        c.1.1
    exact W.rootExtensionPrefixState_representative
      p radialIncremented incremented k c.1
  apply RootRadialSeedProfile.partitionedRootExtensionStageOfProfilePartition
    hm hmn W p radialIncremented delta epsilon incremented
    (W.stableRootExtensionPrefixHistory p radialIncremented incremented k A)
    (Classical.choice hnonempty) representative hgeom hk
  · intro c
    rw [hrepresentative c]
    exact Set.subset_iUnion
      (fun c : StableRootExtensionPrefixStateIndex
          W p radialIncremented incremented k A ↦ c.1.1.historyProfile.event) c
  · intro X hX
    rw [RootRadialSeedProfile.stableRootExtensionPrefixHistory,
      Set.mem_iUnion] at hX
    rw [Set.mem_iUnion]
    obtain ⟨c, hc⟩ := hX
    exact ⟨c, by simpa only [hrepresentative c] using hc⟩
  · intro c c' hne
    rw [hrepresentative c, hrepresentative c']
    exact W.pairwiseDisjoint_stableRootExtensionPrefixHistory
      p radialIncremented incremented hincremented k A c c' hne
  · intro c
    rw [hrepresentative c]
    exact hrestart c

/-- The stable-history stage covers exactly the semantic stable-cell union supplied to it. -/
theorem RootRadialSeedProfile.partitionedRootExtensionStageOfStableHistory_cellUnion
    {d m n : ℕ} [NeZero d] (hm : 1 ≤ m) (hmn : m + 1 < n)
    (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (delta epsilon : ℝ)
    (incremented : RootExtensionThresholdPolicy d)
    (hincremented : ∀ S b e, S.lower e ≤ incremented S b e)
    {k : ℕ}
    (A : Set (CubicEdge d → ℝ))
    (hnonempty : Nonempty (StableRootExtensionPrefixStateIndex
      W p radialIncremented incremented k A))
    (hgeom : ∀ a : CubicDirection d,
      SeedBoxWithinBoundaryLayer d a.1 m n (W a).seedCenter.1)
    (hk : k < (rootExtensionDirectionOrder d).length)
    (hrestart : ∀ c : StableRootExtensionPrefixStateIndex
        W p radialIncremented incremented k A,
      let a := (rootExtensionDirectionOrder d)[k]
      let S := c.1.1
      let Q := S.framedQuery (W.physicalCenter a) a
        (oppositeTransverseRestartFlip a)
      (1 - epsilon) * (couplingMeasure (CubicEdge d)).real
          (Q.boundaryHistoryEvent n) <
        (couplingMeasure (CubicEdge d)).real
          (Q.successEvent m n p delta ∩ Q.boundaryHistoryEvent n)) :
    (RootRadialSeedProfile.partitionedRootExtensionStageOfStableHistory
      hm hmn W p radialIncremented delta epsilon incremented hincremented
      A hnonempty hgeom hk hrestart).cellUnion =
        W.stableRootExtensionPrefixHistory p radialIncremented incremented k A := by
  classical
  unfold RootRadialSeedProfile.partitionedRootExtensionStageOfStableHistory
  apply RootRadialSeedProfile.partitionedRootExtensionStageOfProfilePartition_cellUnion

@[simp]
theorem RootRadialSeedProfile.partitionedRootExtensionStageOfStableHistory_query
    {d m n : ℕ} [NeZero d] (hm : 1 ≤ m) (hmn : m + 1 < n)
    (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (delta epsilon : ℝ)
    (incremented : RootExtensionThresholdPolicy d)
    (hincremented : ∀ S b e, S.lower e ≤ incremented S b e)
    {k : ℕ}
    (A : Set (CubicEdge d → ℝ))
    (hnonempty : Nonempty (StableRootExtensionPrefixStateIndex
      W p radialIncremented incremented k A))
    (hgeom : ∀ a : CubicDirection d,
      SeedBoxWithinBoundaryLayer d a.1 m n (W a).seedCenter.1)
    (hk : k < (rootExtensionDirectionOrder d).length)
    (hrestart : ∀ c : StableRootExtensionPrefixStateIndex
        W p radialIncremented incremented k A,
      let a := (rootExtensionDirectionOrder d)[k]
      let S := c.1.1
      let Q := S.framedQuery (W.physicalCenter a) a
        (oppositeTransverseRestartFlip a)
      (1 - epsilon) * (couplingMeasure (CubicEdge d)).real
          (Q.boundaryHistoryEvent n) <
        (couplingMeasure (CubicEdge d)).real
          (Q.successEvent m n p delta ∩ Q.boundaryHistoryEvent n))
    (c : StableRootExtensionPrefixStateIndex
      W p radialIncremented incremented k A) :
    (RootRadialSeedProfile.partitionedRootExtensionStageOfStableHistory
      hm hmn W p radialIncremented delta epsilon incremented hincremented
        A hnonempty hgeom hk hrestart).query c =
      let a := (rootExtensionDirectionOrder d)[k]
      c.1.1.framedQuery (W.physicalCenter a) a
        (oppositeTransverseRestartFlip a) := by
  classical
  unfold RootRadialSeedProfile.partitionedRootExtensionStageOfStableHistory
  unfold RootRadialSeedProfile.partitionedRootExtensionStageOfProfilePartition
  unfold RootRadialSeedProfile.partitionedRootExtensionStage
  rw [PartitionedFramedRestartStage.query_ofCanonicalSourceEdgeStateRealizationOfTargetEndpointFresh]
  have hstate : W.rootExtensionPrefixState p radialIncremented incremented
      (fun c : StableRootExtensionPrefixStateIndex
        W p radialIncremented incremented k A ↦
          W.rootExtensionPrefixRepresentative p radialIncremented incremented k c.1)
      k c = c.1.1 := by
    change W.rootExtensionPrefixState p radialIncremented incremented
      (W.rootExtensionPrefixRepresentative p radialIncremented incremented k) k c.1 = c.1.1
    exact W.rootExtensionPrefixState_representative
      p radialIncremented incremented k c.1
  rw [hstate]

/-- Each concrete cell of the stable root stage is the unchanged accumulated-history cell of
its reachable prefix state. -/
theorem RootRadialSeedProfile.partitionedRootExtensionStageOfStableHistory_cell
    {d m n : ℕ} [NeZero d] (hm : 1 ≤ m) (hmn : m + 1 < n)
    (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (delta epsilon : ℝ)
    (incremented : RootExtensionThresholdPolicy d)
    (hincremented : ∀ S b e, S.lower e ≤ incremented S b e)
    {k : ℕ}
    (A : Set (CubicEdge d → ℝ))
    (hnonempty : Nonempty (StableRootExtensionPrefixStateIndex
      W p radialIncremented incremented k A))
    (hgeom : ∀ a : CubicDirection d,
      SeedBoxWithinBoundaryLayer d a.1 m n (W a).seedCenter.1)
    (hk : k < (rootExtensionDirectionOrder d).length)
    (hrestart : ∀ c : StableRootExtensionPrefixStateIndex
        W p radialIncremented incremented k A,
      let a := (rootExtensionDirectionOrder d)[k]
      let S := c.1.1
      let Q := S.framedQuery (W.physicalCenter a) a
        (oppositeTransverseRestartFlip a)
      (1 - epsilon) * (couplingMeasure (CubicEdge d)).real
          (Q.boundaryHistoryEvent n) <
        (couplingMeasure (CubicEdge d)).real
          (Q.successEvent m n p delta ∩ Q.boundaryHistoryEvent n))
    (c : StableRootExtensionPrefixStateIndex
      W p radialIncremented incremented k A) :
    (RootRadialSeedProfile.partitionedRootExtensionStageOfStableHistory
      hm hmn W p radialIncremented delta epsilon incremented hincremented
        A hnonempty hgeom hk hrestart).cell c = c.1.1.historyProfile.event := by
  classical
  unfold RootRadialSeedProfile.partitionedRootExtensionStageOfStableHistory
  unfold RootRadialSeedProfile.partitionedRootExtensionStageOfProfilePartition
  unfold RootRadialSeedProfile.partitionedRootExtensionStage
  rw [PartitionedFramedRestartStage.cell_ofCanonicalSourceEdgeStateRealizationOfTargetEndpointFresh]
  have hstate : W.rootExtensionPrefixState p radialIncremented incremented
      (fun c : StableRootExtensionPrefixStateIndex
        W p radialIncremented incremented k A ↦
          W.rootExtensionPrefixRepresentative p radialIncremented incremented k c.1)
      k c = c.1.1 := by
    change W.rootExtensionPrefixState p radialIncremented incremented
      (W.rootExtensionPrefixRepresentative p radialIncremented incremented k) k c.1 = c.1.1
    exact W.rootExtensionPrefixState_representative
      p radialIncremented incremented k c.1
  rw [hstate]

/-- The concrete `k`-th root stage, restricted to precisely those canonical history cells on
which the first `k` restart successes are stable. -/
noncomputable def RootRadialSeedProfile.rootExtensionPrefixSuccessStage
    {d m n : ℕ} [NeZero d] (hm : 1 ≤ m) (hmn : m + 1 < n)
    (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (delta epsilon : ℝ)
    (incremented : RootExtensionThresholdPolicy d)
    (hincremented : ∀ S b e, S.lower e ≤ incremented S b e)
    {k : ℕ}
    (hnonempty : Nonempty (StableRootExtensionPrefixStateIndex
      W p radialIncremented incremented k
        (W.rootExtensionPrefixSuccessEvent
          p radialIncremented delta incremented k)))
    (hgeom : ∀ a : CubicDirection d,
      SeedBoxWithinBoundaryLayer d a.1 m n (W a).seedCenter.1)
    (hk : k < (rootExtensionDirectionOrder d).length)
    (hrestart : ∀ c : StableRootExtensionPrefixStateIndex
        W p radialIncremented incremented k
          (W.rootExtensionPrefixSuccessEvent
            p radialIncremented delta incremented k),
      let a := (rootExtensionDirectionOrder d)[k]
      let S := c.1.1
      let Q := S.framedQuery (W.physicalCenter a) a
        (oppositeTransverseRestartFlip a)
      (1 - epsilon) * (couplingMeasure (CubicEdge d)).real
          (Q.boundaryHistoryEvent n) <
        (couplingMeasure (CubicEdge d)).real
          (Q.successEvent m n p delta ∩ Q.boundaryHistoryEvent n)) :
    PartitionedFramedRestartStage d
      (StableRootExtensionPrefixStateIndex
        W p radialIncremented incremented k
          (W.rootExtensionPrefixSuccessEvent
            p radialIncremented delta incremented k))
      m n p delta epsilon :=
  RootRadialSeedProfile.partitionedRootExtensionStageOfStableHistory
    hm hmn W p radialIncremented
    delta epsilon incremented hincremented
      (W.rootExtensionPrefixSuccessEvent p radialIncremented delta incremented k)
      hnonempty hgeom hk hrestart

@[simp]
theorem RootRadialSeedProfile.rootExtensionPrefixSuccessStage_query
    {d m n : ℕ} [NeZero d] (hm : 1 ≤ m) (hmn : m + 1 < n)
    (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (delta epsilon : ℝ)
    (incremented : RootExtensionThresholdPolicy d)
    (hincremented : ∀ S b e, S.lower e ≤ incremented S b e)
    {k : ℕ}
    (hnonempty : Nonempty (StableRootExtensionPrefixStateIndex
      W p radialIncremented incremented k
        (W.rootExtensionPrefixSuccessEvent
          p radialIncremented delta incremented k)))
    (hgeom : ∀ a : CubicDirection d,
      SeedBoxWithinBoundaryLayer d a.1 m n (W a).seedCenter.1)
    (hk : k < (rootExtensionDirectionOrder d).length)
    (hrestart : ∀ c : StableRootExtensionPrefixStateIndex
        W p radialIncremented incremented k
          (W.rootExtensionPrefixSuccessEvent
            p radialIncremented delta incremented k),
      let a := (rootExtensionDirectionOrder d)[k]
      let S := c.1.1
      let Q := S.framedQuery (W.physicalCenter a) a
        (oppositeTransverseRestartFlip a)
      (1 - epsilon) * (couplingMeasure (CubicEdge d)).real
          (Q.boundaryHistoryEvent n) <
        (couplingMeasure (CubicEdge d)).real
          (Q.successEvent m n p delta ∩ Q.boundaryHistoryEvent n))
    (c : StableRootExtensionPrefixStateIndex
      W p radialIncremented incremented k
        (W.rootExtensionPrefixSuccessEvent
          p radialIncremented delta incremented k)) :
    (RootRadialSeedProfile.rootExtensionPrefixSuccessStage
      hm hmn W p radialIncremented delta epsilon
      incremented hincremented hnonempty hgeom hk hrestart).query c =
      let a := (rootExtensionDirectionOrder d)[k]
      c.1.1.framedQuery (W.physicalCenter a) a
        (oppositeTransverseRestartFlip a) := by
  unfold RootRadialSeedProfile.rootExtensionPrefixSuccessStage
  apply RootRadialSeedProfile.partitionedRootExtensionStageOfStableHistory_query

@[simp]
theorem RootRadialSeedProfile.rootExtensionPrefixSuccessStage_cell
    {d m n : ℕ} [NeZero d] (hm : 1 ≤ m) (hmn : m + 1 < n)
    (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (delta epsilon : ℝ)
    (incremented : RootExtensionThresholdPolicy d)
    (hincremented : ∀ S b e, S.lower e ≤ incremented S b e)
    {k : ℕ}
    (hnonempty : Nonempty (StableRootExtensionPrefixStateIndex
      W p radialIncremented incremented k
        (W.rootExtensionPrefixSuccessEvent
          p radialIncremented delta incremented k)))
    (hgeom : ∀ a : CubicDirection d,
      SeedBoxWithinBoundaryLayer d a.1 m n (W a).seedCenter.1)
    (hk : k < (rootExtensionDirectionOrder d).length)
    (hrestart : ∀ c : StableRootExtensionPrefixStateIndex
        W p radialIncremented incremented k
          (W.rootExtensionPrefixSuccessEvent
            p radialIncremented delta incremented k),
      let a := (rootExtensionDirectionOrder d)[k]
      let S := c.1.1
      let Q := S.framedQuery (W.physicalCenter a) a
        (oppositeTransverseRestartFlip a)
      (1 - epsilon) * (couplingMeasure (CubicEdge d)).real
          (Q.boundaryHistoryEvent n) <
        (couplingMeasure (CubicEdge d)).real
          (Q.successEvent m n p delta ∩ Q.boundaryHistoryEvent n))
    (c : StableRootExtensionPrefixStateIndex
      W p radialIncremented incremented k
        (W.rootExtensionPrefixSuccessEvent
          p radialIncremented delta incremented k)) :
    (RootRadialSeedProfile.rootExtensionPrefixSuccessStage
      hm hmn W p radialIncremented delta epsilon
      incremented hincremented hnonempty hgeom hk hrestart).cell c =
      c.1.1.historyProfile.event := by
  unfold RootRadialSeedProfile.rootExtensionPrefixSuccessStage
  apply RootRadialSeedProfile.partitionedRootExtensionStageOfStableHistory_cell

/-- The concrete `k`-th stage covers the semantic first-`k` success event modulo the single
probability-one common-uniform support. -/
theorem RootRadialSeedProfile.rootExtensionPrefixSuccessStage_cellUnion_inter_nonnegative_eq
    {d m n : ℕ} [NeZero d] (hm : 1 ≤ m) (hmn : m + 1 < n)
    (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (delta epsilon : ℝ)
    (hdelta : 0 ≤ delta) (hradialDelta : delta = (radialIncremented : ℝ))
    (incremented : RootExtensionThresholdPolicy d)
    (hincremented : ∀ S b e, S.lower e ≤ incremented S b e)
    (hadds : W.PolicyAddsOnPrefixes p radialIncremented delta incremented)
    {k : ℕ}
    (hnonempty : Nonempty (StableRootExtensionPrefixStateIndex
      W p radialIncremented incremented k
        (W.rootExtensionPrefixSuccessEvent
          p radialIncremented delta incremented k)))
    (hgeom : ∀ a : CubicDirection d,
      SeedBoxWithinBoundaryLayer d a.1 m n (W a).seedCenter.1)
    (hk : k < (rootExtensionDirectionOrder d).length)
    (hrestart : ∀ c : StableRootExtensionPrefixStateIndex
        W p radialIncremented incremented k
          (W.rootExtensionPrefixSuccessEvent
            p radialIncremented delta incremented k),
      let a := (rootExtensionDirectionOrder d)[k]
      let S := c.1.1
      let Q := S.framedQuery (W.physicalCenter a) a
        (oppositeTransverseRestartFlip a)
      (1 - epsilon) * (couplingMeasure (CubicEdge d)).real
          (Q.boundaryHistoryEvent n) <
        (couplingMeasure (CubicEdge d)).real
          (Q.successEvent m n p delta ∩ Q.boundaryHistoryEvent n)) :
    (RootRadialSeedProfile.rootExtensionPrefixSuccessStage
      hm hmn W p radialIncremented delta epsilon incremented hincremented
        hnonempty hgeom hk hrestart).cellUnion ∩
        SourceFiniteEdgeRevealState.nonnegativeCouplingEvent =
      W.rootExtensionPrefixSuccessEvent p radialIncremented delta incremented k ∩
        SourceFiniteEdgeRevealState.nonnegativeCouplingEvent := by
  rw [RootRadialSeedProfile.rootExtensionPrefixSuccessStage,
    RootRadialSeedProfile.partitionedRootExtensionStageOfStableHistory_cellUnion]
  exact W.stableHistory_inter_nonnegative_eq_rootExtensionPrefixSuccess
    hm hmn p radialIncremented delta hdelta hradialDelta incremented
      hincremented hadds hgeom hk.le

/-- The successful union of the concrete `k`-th stage is exactly semantic success through
slot `k`, modulo the common probability-one coupling support. -/
theorem RootRadialSeedProfile.rootExtensionPrefixSuccessStage_successEvent_inter_nonnegative_eq
    {d m n : ℕ} [NeZero d] (hm : 1 ≤ m) (hmn : m + 1 < n)
    (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (delta epsilon : ℝ)
    (hdelta : 0 ≤ delta) (hradialDelta : delta = (radialIncremented : ℝ))
    (incremented : RootExtensionThresholdPolicy d)
    (hincremented : ∀ S b e, S.lower e ≤ incremented S b e)
    (hadds : W.PolicyAddsOnPrefixes p radialIncremented delta incremented)
    {k : ℕ}
    (hnonempty : Nonempty (StableRootExtensionPrefixStateIndex
      W p radialIncremented incremented k
        (W.rootExtensionPrefixSuccessEvent
          p radialIncremented delta incremented k)))
    (hgeom : ∀ a : CubicDirection d,
      SeedBoxWithinBoundaryLayer d a.1 m n (W a).seedCenter.1)
    (hk : k < (rootExtensionDirectionOrder d).length)
    (hrestart : ∀ c : StableRootExtensionPrefixStateIndex
        W p radialIncremented incremented k
          (W.rootExtensionPrefixSuccessEvent
            p radialIncremented delta incremented k),
      let a := (rootExtensionDirectionOrder d)[k]
      let S := c.1.1
      let Q := S.framedQuery (W.physicalCenter a) a
        (oppositeTransverseRestartFlip a)
      (1 - epsilon) * (couplingMeasure (CubicEdge d)).real
          (Q.boundaryHistoryEvent n) <
        (couplingMeasure (CubicEdge d)).real
          (Q.successEvent m n p delta ∩ Q.boundaryHistoryEvent n)) :
    (RootRadialSeedProfile.rootExtensionPrefixSuccessStage
      hm hmn W p radialIncremented delta epsilon incremented hincremented
        hnonempty hgeom hk hrestart).successEvent ∩
        SourceFiniteEdgeRevealState.nonnegativeCouplingEvent =
      W.rootExtensionPrefixSuccessEvent
          p radialIncremented delta incremented (k + 1) ∩
        SourceFiniteEdgeRevealState.nonnegativeCouplingEvent := by
  classical
  let S := RootRadialSeedProfile.rootExtensionPrefixSuccessStage
    hm hmn W p radialIncremented delta epsilon incremented hincremented
      hnonempty hgeom hk hrestart
  change S.successEvent ∩ SourceFiniteEdgeRevealState.nonnegativeCouplingEvent = _
  ext X
  constructor
  · rintro ⟨hSuccess, hNonnegative⟩
    simp only [PartitionedFramedRestartStage.successEvent, Set.mem_iUnion] at hSuccess
    obtain ⟨c, hcCells, hSuccessfulCell⟩ := hSuccess
    have hCellEq : S.cell c = c.1.1.historyProfile.event := by
      dsimp only [S]
      apply RootRadialSeedProfile.rootExtensionPrefixSuccessStage_cell
    have hQueryEq : S.query c =
        let a := (rootExtensionDirectionOrder d)[k]
        c.1.1.framedQuery (W.physicalCenter a) a
          (oppositeTransverseRestartFlip a) := by
      dsimp only [S]
      apply RootRadialSeedProfile.rootExtensionPrefixSuccessStage_query
    have hHistory : X ∈ c.1.1.historyProfile.event := by
      rw [← hCellEq]
      exact hSuccessfulCell.2
    have hPrefix : X ∈ W.rootExtensionPrefixSuccessEvent
        p radialIncremented delta incremented k := c.2 hHistory
    let R := W.rootExtensionPrefixRepresentative
      p radialIncremented incremented k c.1
    have hRState : W.rootExtensionPrefixState
        p radialIncremented incremented id k R = c.1.1 := by
      change W.rootExtensionPrefixState p radialIncremented incremented
        (W.rootExtensionPrefixRepresentative p radialIncremented incremented k) k c.1 = c.1.1
      exact W.rootExtensionPrefixState_representative
        p radialIncremented incremented k c.1
    have hInRState : X ∈
        (W.rootExtensionPrefixState
          p radialIncremented incremented id k R).historyProfile.event := by
      rw [hRState]
      exact hHistory
    have hXState : W.rootExtensionPrefixState
        p radialIncremented incremented id k X = c.1.1 :=
      (W.rootExtensionPrefixState_eq_of_mem_historyProfile
        p radialIncremented incremented hincremented k R X hInRState).trans hRState
    have hQuery :
        let a := (rootExtensionDirectionOrder d)[k]
        let SX := W.rootExtensionPrefixState
          p radialIncremented incremented id k X
        let Q := SX.framedQuery (W.physicalCenter a) a
          (oppositeTransverseRestartFlip a)
        X ∈ Q.successEvent m n p delta := by
      rw [hXState]
      have hStageQuery : X ∈ (S.query c).successEvent m n p delta :=
        hSuccessfulCell.1
      rw [hQueryEq] at hStageQuery
      exact hStageQuery
    exact ⟨(W.mem_rootExtensionPrefixSuccessEvent_succ_iff
      p radialIncremented delta incremented hk X).2 ⟨hPrefix, hQuery⟩,
      hNonnegative⟩
  · rintro ⟨hNext, hNonnegative⟩
    obtain ⟨hPrefix, hQuery⟩ :=
      (W.mem_rootExtensionPrefixSuccessEvent_succ_iff
        p radialIncremented delta incremented hk X).1 hNext
    have hStable : X ∈ W.stableRootExtensionPrefixHistory
        p radialIncremented incremented k
          (W.rootExtensionPrefixSuccessEvent
            p radialIncremented delta incremented k) :=
      W.rootExtensionPrefixSuccess_inter_nonnegative_subset_stableHistory
        hm hmn p radialIncremented delta hdelta hradialDelta incremented
          hincremented hadds hgeom
          hk.le ⟨hPrefix, hNonnegative⟩
    rw [RootRadialSeedProfile.stableRootExtensionPrefixHistory,
      Set.mem_iUnion] at hStable
    obtain ⟨c, hHistory⟩ := hStable
    have hCellEq : S.cell c = c.1.1.historyProfile.event := by
      dsimp only [S]
      apply RootRadialSeedProfile.rootExtensionPrefixSuccessStage_cell
    have hQueryEq : S.query c =
        let a := (rootExtensionDirectionOrder d)[k]
        c.1.1.framedQuery (W.physicalCenter a) a
          (oppositeTransverseRestartFlip a) := by
      dsimp only [S]
      apply RootRadialSeedProfile.rootExtensionPrefixSuccessStage_query
    let R := W.rootExtensionPrefixRepresentative
      p radialIncremented incremented k c.1
    have hRState : W.rootExtensionPrefixState
        p radialIncremented incremented id k R = c.1.1 := by
      change W.rootExtensionPrefixState p radialIncremented incremented
        (W.rootExtensionPrefixRepresentative p radialIncremented incremented k) k c.1 = c.1.1
      exact W.rootExtensionPrefixState_representative
        p radialIncremented incremented k c.1
    have hInRState : X ∈
        (W.rootExtensionPrefixState
          p radialIncremented incremented id k R).historyProfile.event := by
      rw [hRState]
      exact hHistory
    have hXState : W.rootExtensionPrefixState
        p radialIncremented incremented id k X = c.1.1 :=
      (W.rootExtensionPrefixState_eq_of_mem_historyProfile
        p radialIncremented incremented hincremented k R X hInRState).trans hRState
    have hStageQuery : X ∈ (S.query c).successEvent m n p delta := by
      rw [hQueryEq, ← hXState]
      exact hQuery
    refine ⟨?_, hNonnegative⟩
    simp only [PartitionedFramedRestartStage.successEvent, Set.mem_iUnion]
    refine ⟨c, ?_, ?_⟩
    · change c ∈ (Finset.univ : Finset
        (StableRootExtensionPrefixStateIndex
          W p radialIncremented incremented k
            (W.rootExtensionPrefixSuccessEvent
              p radialIncremented delta incremented k)))
      exact Finset.mem_univ c
    exact ⟨hStageQuery, hCellEq.symm ▸ hHistory⟩

/-- One source-faithful root extension multiplies the probability of the semantic successful
prefix by at least `1 - epsilon`.  The proof composes the cellwise Lemma 7.17 estimates through
the almost-sure stable-history identifications, with no common cell type across stages. -/
theorem RootRadialSeedProfile.rootExtensionPrefixSuccess_measure_step
    {d m n : ℕ} [NeZero d] (hm : 1 ≤ m) (hmn : m + 1 < n)
    (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (delta epsilon : ℝ)
    (hdelta : 0 ≤ delta) (hradialDelta : delta = (radialIncremented : ℝ))
    (incremented : RootExtensionThresholdPolicy d)
    (hincremented : ∀ S b e, S.lower e ≤ incremented S b e)
    (hadds : W.PolicyAddsOnPrefixes p radialIncremented delta incremented)
    {k : ℕ}
    (hnonempty : Nonempty (StableRootExtensionPrefixStateIndex
      W p radialIncremented incremented k
        (W.rootExtensionPrefixSuccessEvent
          p radialIncremented delta incremented k)))
    (hgeom : ∀ a : CubicDirection d,
      SeedBoxWithinBoundaryLayer d a.1 m n (W a).seedCenter.1)
    (hk : k < (rootExtensionDirectionOrder d).length)
    (hrestart : ∀ c : StableRootExtensionPrefixStateIndex
        W p radialIncremented incremented k
          (W.rootExtensionPrefixSuccessEvent
            p radialIncremented delta incremented k),
      let a := (rootExtensionDirectionOrder d)[k]
      let S := c.1.1
      let Q := S.framedQuery (W.physicalCenter a) a
        (oppositeTransverseRestartFlip a)
      (1 - epsilon) * (couplingMeasure (CubicEdge d)).real
          (Q.boundaryHistoryEvent n) <
        (couplingMeasure (CubicEdge d)).real
          (Q.successEvent m n p delta ∩ Q.boundaryHistoryEvent n)) :
    (1 - epsilon) * (couplingMeasure (CubicEdge d)).real
        (W.rootExtensionPrefixSuccessEvent
          p radialIncremented delta incremented k) ≤
      (couplingMeasure (CubicEdge d)).real
        (W.rootExtensionPrefixSuccessEvent
          p radialIncremented delta incremented (k + 1)) := by
  let S := RootRadialSeedProfile.rootExtensionPrefixSuccessStage
    hm hmn W p radialIncremented delta epsilon incremented hincremented
      hnonempty hgeom hk hrestart
  apply S.success_lower_bound_of_inter_support_eq
    SourceFiniteEdgeRevealState.nonnegativeCouplingEvent
    (W.rootExtensionPrefixSuccessEvent
      p radialIncremented delta incremented k)
    (W.rootExtensionPrefixSuccessEvent
      p radialIncremented delta incremented (k + 1))
  · exact SourceFiniteEdgeRevealState.measurableSet_nonnegativeCouplingEvent
  · exact SourceFiniteEdgeRevealState.couplingMeasure_real_nonnegativeCouplingEvent
  · dsimp only [S]
    exact RootRadialSeedProfile.rootExtensionPrefixSuccessStage_cellUnion_inter_nonnegative_eq
      hm hmn W p radialIncremented delta epsilon hdelta hradialDelta incremented
        hincremented hadds hnonempty hgeom hk hrestart
  · dsimp only [S]
    exact RootRadialSeedProfile.rootExtensionPrefixSuccessStage_successEvent_inter_nonnegative_eq
      hm hmn W p radialIncremented delta epsilon hdelta hradialDelta incremented
        hincremented hadds hnonempty hgeom hk hrestart

/-- Positive mass of a semantic prefix event supplies an actual stable canonical history cell.
This discharges the nonempty-default requirement of the finite classifier without inventing a
junk cell. -/
theorem RootRadialSeedProfile.nonempty_stableRootExtensionPrefixStateIndex_of_measure_pos
    {d m n : ℕ} [NeZero d] (hm : 1 ≤ m) (hmn : m + 1 < n)
    (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (delta : ℝ)
    (hdelta : 0 ≤ delta) (hradialDelta : delta = (radialIncremented : ℝ))
    (incremented : RootExtensionThresholdPolicy d)
    (hincremented : ∀ S b e, S.lower e ≤ incremented S b e)
    (hadds : W.PolicyAddsOnPrefixes p radialIncremented delta incremented)
    (hgeom : ∀ a : CubicDirection d,
      SeedBoxWithinBoundaryLayer d a.1 m n (W a).seedCenter.1)
    {k : ℕ} (hk : k ≤ (rootExtensionDirectionOrder d).length)
    (hpos : 0 < (couplingMeasure (CubicEdge d)).real
      (W.rootExtensionPrefixSuccessEvent
        p radialIncremented delta incremented k)) :
    Nonempty (StableRootExtensionPrefixStateIndex
      W p radialIncremented incremented k
        (W.rootExtensionPrefixSuccessEvent
          p radialIncremented delta incremented k)) := by
  have hinter : (couplingMeasure (CubicEdge d)).real
      (W.rootExtensionPrefixSuccessEvent
          p radialIncremented delta incremented k ∩
        SourceFiniteEdgeRevealState.nonnegativeCouplingEvent) =
      (couplingMeasure (CubicEdge d)).real
        (W.rootExtensionPrefixSuccessEvent
          p radialIncremented delta incremented k) :=
    measureReal_inter_eq_of_measureReal_eq_one
      SourceFiniteEdgeRevealState.nonnegativeCouplingEvent
      (W.rootExtensionPrefixSuccessEvent
        p radialIncremented delta incremented k)
      SourceFiniteEdgeRevealState.measurableSet_nonnegativeCouplingEvent
      SourceFiniteEdgeRevealState.couplingMeasure_real_nonnegativeCouplingEvent
  obtain ⟨X, hXPrefix, hXNonnegative⟩ := MeasureTheory.nonempty_of_measureReal_ne_zero
    (μ := couplingMeasure (CubicEdge d))
    (s := W.rootExtensionPrefixSuccessEvent
        p radialIncremented delta incremented k ∩
      SourceFiniteEdgeRevealState.nonnegativeCouplingEvent)
    (by rw [hinter]; exact hpos.ne')
  have hStable :=
    W.rootExtensionPrefixSuccess_inter_nonnegative_subset_stableHistory
      hm hmn p radialIncremented delta hdelta hradialDelta incremented
        hincremented hadds hgeom hk
        ⟨hXPrefix, hXNonnegative⟩
  rw [RootRadialSeedProfile.stableRootExtensionPrefixHistory,
    Set.mem_iUnion] at hStable
  obtain ⟨c, _hc⟩ := hStable
  exact ⟨c⟩

/-- Iteration of the stage-specific finite partitions through the complete root direction
schedule.  No common classifier type is required: each step supplies its own reachable-state
subtype and only the semantic prefix events are shared across the recurrence. -/
theorem RootRadialSeedProfile.pow_mul_rootRadialEvent_le_rootExtensionPrefixSuccess
    {d m n : ℕ} [NeZero d] (hm : 1 ≤ m) (hmn : m + 1 < n)
    (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (delta epsilon : ℝ)
    (hdelta : 0 ≤ delta) (hradialDelta : delta = (radialIncremented : ℝ))
    (hepsilon : epsilon ≤ 1)
    (incremented : RootExtensionThresholdPolicy d)
    (hincremented : ∀ S b e, S.lower e ≤ incremented S b e)
    (hadds : W.PolicyAddsOnPrefixes p radialIncremented delta incremented)
    (hgeom : ∀ a : CubicDirection d,
      SeedBoxWithinBoundaryLayer d a.1 m n (W a).seedCenter.1)
    (hnonempty : ∀ k (_hk : k < (rootExtensionDirectionOrder d).length),
      Nonempty (StableRootExtensionPrefixStateIndex
        W p radialIncremented incremented k
          (W.rootExtensionPrefixSuccessEvent
            p radialIncremented delta incremented k)))
    (hrestart : ∀ k (_hk : k < (rootExtensionDirectionOrder d).length)
        (c : StableRootExtensionPrefixStateIndex
          W p radialIncremented incremented k
            (W.rootExtensionPrefixSuccessEvent
              p radialIncremented delta incremented k)),
      let a := (rootExtensionDirectionOrder d)[k]
      let S := c.1.1
      let Q := S.framedQuery (W.physicalCenter a) a
        (oppositeTransverseRestartFlip a)
      (1 - epsilon) * (couplingMeasure (CubicEdge d)).real
          (Q.boundaryHistoryEvent n) <
        (couplingMeasure (CubicEdge d)).real
          (Q.successEvent m n p delta ∩ Q.boundaryHistoryEvent n)) :
    (1 - epsilon) ^ (rootExtensionDirectionOrder d).length *
        (couplingMeasure (CubicEdge d)).real (rootRadialEvent d m n p delta) ≤
      (couplingMeasure (CubicEdge d)).real
        (W.rootExtensionPrefixSuccessEvent p radialIncremented delta incremented
          (rootExtensionDirectionOrder d).length) := by
  have hpow := pow_mul_measureReal_le_of_step
    (mu := couplingMeasure (CubicEdge d))
    (fun k ↦ W.rootExtensionPrefixSuccessEvent
      p radialIncremented delta incremented k)
    (1 - epsilon) (sub_nonneg.mpr hepsilon)
    (rootExtensionDirectionOrder d).length
    (fun k hk ↦ RootRadialSeedProfile.rootExtensionPrefixSuccess_measure_step
      hm hmn W p radialIncremented delta epsilon hdelta hradialDelta incremented
        hincremented hadds (hnonempty k hk) hgeom hk (hrestart k hk))
  simpa only [W.rootExtensionPrefixSuccessEvent_zero] using hpow

/-- The nonempty stage cells required above follow inductively from positive radial mass and
`epsilon < 1`.  Thus the final source-facing composition theorem asks only for the uniform
cellwise restart estimates, not a separate classifier inhabitance hypothesis. -/
theorem RootRadialSeedProfile.pow_mul_rootRadialEvent_le_rootExtensionPrefixSuccess_of_pos
    {d m n : ℕ} [NeZero d] (hm : 1 ≤ m) (hmn : m + 1 < n)
    (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (delta epsilon : ℝ)
    (hdelta : 0 ≤ delta) (hradialDelta : delta = (radialIncremented : ℝ))
    (hepsilon : epsilon < 1)
    (incremented : RootExtensionThresholdPolicy d)
    (hincremented : ∀ S b e, S.lower e ≤ incremented S b e)
    (hadds : W.PolicyAddsOnPrefixes p radialIncremented delta incremented)
    (hgeom : ∀ a : CubicDirection d,
      SeedBoxWithinBoundaryLayer d a.1 m n (W a).seedCenter.1)
    (hroot : 0 < (couplingMeasure (CubicEdge d)).real
      (rootRadialEvent d m n p delta))
    (hrestart : ∀ k (_hk : k < (rootExtensionDirectionOrder d).length)
        (c : StableRootExtensionPrefixStateIndex
          W p radialIncremented incremented k
            (W.rootExtensionPrefixSuccessEvent
              p radialIncremented delta incremented k)),
      let a := (rootExtensionDirectionOrder d)[k]
      let S := c.1.1
      let Q := S.framedQuery (W.physicalCenter a) a
        (oppositeTransverseRestartFlip a)
      (1 - epsilon) * (couplingMeasure (CubicEdge d)).real
          (Q.boundaryHistoryEvent n) <
        (couplingMeasure (CubicEdge d)).real
          (Q.successEvent m n p delta ∩ Q.boundaryHistoryEvent n)) :
    (1 - epsilon) ^ (rootExtensionDirectionOrder d).length *
        (couplingMeasure (CubicEdge d)).real (rootRadialEvent d m n p delta) ≤
      (couplingMeasure (CubicEdge d)).real
        (W.rootExtensionPrefixSuccessEvent p radialIncremented delta incremented
          (rootExtensionDirectionOrder d).length) := by
  have hprefixPos : ∀ k, k ≤ (rootExtensionDirectionOrder d).length →
      0 < (couplingMeasure (CubicEdge d)).real
        (W.rootExtensionPrefixSuccessEvent
          p radialIncremented delta incremented k) := by
    intro k hk
    induction k with
    | zero => simpa only [W.rootExtensionPrefixSuccessEvent_zero] using hroot
    | succ k ih =>
        have hklt : k < (rootExtensionDirectionOrder d).length := by omega
        have hpos := ih (by omega)
        have hnonempty :=
          RootRadialSeedProfile.nonempty_stableRootExtensionPrefixStateIndex_of_measure_pos
            hm hmn W p radialIncremented delta hdelta hradialDelta incremented
              hincremented hadds hgeom
              hklt.le hpos
        have hstep := RootRadialSeedProfile.rootExtensionPrefixSuccess_measure_step
          hm hmn W p radialIncremented delta epsilon hdelta hradialDelta incremented
            hincremented hadds hnonempty hgeom hklt (hrestart k hklt)
        exact (mul_pos (sub_pos.mpr hepsilon) hpos).trans_le hstep
  apply RootRadialSeedProfile.pow_mul_rootRadialEvent_le_rootExtensionPrefixSuccess
    hm hmn W p radialIncremented delta epsilon hdelta hradialDelta hepsilon.le
      incremented hincremented hadds hgeom
  · intro k hk
    exact RootRadialSeedProfile.nonempty_stableRootExtensionPrefixStateIndex_of_measure_pos
      hm hmn W p radialIncremented delta hdelta hradialDelta incremented
        hincremented hadds hgeom
        hk.le (hprefixPos k hk.le)
  · exact hrestart

/-- Source-facing `2d` form of the complete post-radial root composition. -/
theorem RootRadialSeedProfile.pow_two_mul_mul_rootRadialEvent_le_rootExtensionPrefixSuccess_of_pos
    {d m n : ℕ} [NeZero d] (hm : 1 ≤ m) (hmn : m + 1 < n)
    (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (delta epsilon : ℝ)
    (hdelta : 0 ≤ delta) (hradialDelta : delta = (radialIncremented : ℝ))
    (hepsilon : epsilon < 1)
    (incremented : RootExtensionThresholdPolicy d)
    (hincremented : ∀ S b e, S.lower e ≤ incremented S b e)
    (hadds : W.PolicyAddsOnPrefixes p radialIncremented delta incremented)
    (hgeom : ∀ a : CubicDirection d,
      SeedBoxWithinBoundaryLayer d a.1 m n (W a).seedCenter.1)
    (hroot : 0 < (couplingMeasure (CubicEdge d)).real
      (rootRadialEvent d m n p delta))
    (hrestart : ∀ k (_hk : k < (rootExtensionDirectionOrder d).length)
        (c : StableRootExtensionPrefixStateIndex
          W p radialIncremented incremented k
            (W.rootExtensionPrefixSuccessEvent
              p radialIncremented delta incremented k)),
      let a := (rootExtensionDirectionOrder d)[k]
      let S := c.1.1
      let Q := S.framedQuery (W.physicalCenter a) a
        (oppositeTransverseRestartFlip a)
      (1 - epsilon) * (couplingMeasure (CubicEdge d)).real
          (Q.boundaryHistoryEvent n) <
        (couplingMeasure (CubicEdge d)).real
          (Q.successEvent m n p delta ∩ Q.boundaryHistoryEvent n)) :
    (1 - epsilon) ^ (2 * d) *
        (couplingMeasure (CubicEdge d)).real (rootRadialEvent d m n p delta) ≤
      (couplingMeasure (CubicEdge d)).real
        (W.rootExtensionPrefixSuccessEvent
          p radialIncremented delta incremented (2 * d)) := by
  simpa only [rootExtensionDirectionOrder_length] using
    RootRadialSeedProfile.pow_mul_rootRadialEvent_le_rootExtensionPrefixSuccess_of_pos
      hm hmn W p radialIncremented delta epsilon hdelta hradialDelta hepsilon
        incremented hincremented hadds hgeom hroot hrestart

/-- Complete post-radial root composition for the canonical total budgeted policy.  The global
arithmetic bound proves that every reachable state takes the genuine `lower + delta` branch;
no equality is asserted for unreachable junk states. -/
theorem RootRadialSeedProfile.pow_two_mul_mul_rootRadialEvent_le_budgetedPrefixSuccess
    {d m n : ℕ} [NeZero d] (hm : 1 ≤ m) (hmn : m + 1 < n)
    (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (delta epsilon : ℝ)
    (hdelta : 0 ≤ delta) (hradialDelta : delta = (radialIncremented : ℝ))
    (hepsilon : epsilon < 1)
    (htotal : max (p : ℝ) (radialIncremented : ℝ) +
      ((rootExtensionDirectionOrder d).length : ℝ) * delta ≤ 1)
    (hgeom : ∀ a : CubicDirection d,
      SeedBoxWithinBoundaryLayer d a.1 m n (W a).seedCenter.1)
    (hroot : 0 < (couplingMeasure (CubicEdge d)).real
      (rootRadialEvent d m n p delta))
    (hrestart : ∀ k (_hk : k < (rootExtensionDirectionOrder d).length)
        (c : StableRootExtensionPrefixStateIndex
          W p radialIncremented
            (budgetedRootExtensionThresholdPolicy delta hdelta) k
            (W.rootExtensionPrefixSuccessEvent p radialIncremented delta
              (budgetedRootExtensionThresholdPolicy delta hdelta) k)),
      let a := (rootExtensionDirectionOrder d)[k]
      let S := c.1.1
      let Q := S.framedQuery (W.physicalCenter a) a
        (oppositeTransverseRestartFlip a)
      (1 - epsilon) * (couplingMeasure (CubicEdge d)).real
          (Q.boundaryHistoryEvent n) <
        (couplingMeasure (CubicEdge d)).real
          (Q.successEvent m n p delta ∩ Q.boundaryHistoryEvent n)) :
    (1 - epsilon) ^ (2 * d) *
        (couplingMeasure (CubicEdge d)).real (rootRadialEvent d m n p delta) ≤
      (couplingMeasure (CubicEdge d)).real
        (W.rootExtensionPrefixSuccessEvent p radialIncremented delta
          (budgetedRootExtensionThresholdPolicy delta hdelta) (2 * d)) := by
  apply RootRadialSeedProfile.pow_two_mul_mul_rootRadialEvent_le_rootExtensionPrefixSuccess_of_pos
    hm hmn W p radialIncremented delta epsilon hdelta hradialDelta hepsilon
      (budgetedRootExtensionThresholdPolicy delta hdelta)
      (lower_le_budgetedRootExtensionThresholdPolicy delta hdelta)
      (W.budgetedPolicy_addsOnPrefixes p radialIncremented delta hdelta htotal)
      hgeom hroot hrestart

/-- The exact finite cells of the canonical `k`-th root stage cover its supplied prefix
history. -/
theorem RootRadialSeedProfile.partitionedRootExtensionStage_cellUnion
    {d m n : ℕ} [NeZero d] (hm : 1 ≤ m) (hmn : m + 1 < n)
    (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (delta epsilon : ℝ)
    (incremented : RootExtensionThresholdPolicy d)
    (history : Set (CubicEdge d → ℝ))
    (realizedCell : (CubicEdge d → ℝ) → C)
    (representative : C → CubicEdge d → ℝ)
    (hgeom : ∀ a : CubicDirection d,
      SeedBoxWithinBoundaryLayer d a.1 m n (W a).seedCenter.1)
    {k : ℕ} (hk : k < (rootExtensionDirectionOrder d).length)
    (hfiber : ∀ c,
      (W.rootExtensionPrefixState p radialIncremented incremented representative k c).historyProfile.event =
        exactRevealCellEvent history realizedCell c)
    (hrestart : ∀ c,
      let a := (rootExtensionDirectionOrder d)[k]
      let S := W.rootExtensionPrefixState p radialIncremented incremented representative k c
      let Q := S.framedQuery (W.physicalCenter a) a
        (oppositeTransverseRestartFlip a)
      (1 - epsilon) * (couplingMeasure (CubicEdge d)).real
          (Q.boundaryHistoryEvent n) <
        (couplingMeasure (CubicEdge d)).real
          (Q.successEvent m n p delta ∩ Q.boundaryHistoryEvent n)) :
    (RootRadialSeedProfile.partitionedRootExtensionStage hm hmn W p radialIncremented
      delta epsilon incremented history realizedCell representative hgeom hk hfiber
      hrestart).cellUnion = history := by
  classical
  unfold RootRadialSeedProfile.partitionedRootExtensionStage
  apply PartitionedFramedRestartStage.cellUnion_ofCanonicalSourceEdgeStateRealizationOfTargetEndpointFresh

/-! ### Fully generated finite prefix partition -/

/-- The `k`-th root restart over the union of all reachable accumulated-history cells.  The
finite classifier, representatives, coverage, and pairwise-disjointness proofs are generated
from the deterministic source recursion; callers supply only static seed geometry and the
cellwise Lemma 7.17 estimate. -/
noncomputable def RootRadialSeedProfile.partitionedRootExtensionStageOfReachableHistory
    {d m n : ℕ} [NeZero d] (hm : 1 ≤ m) (hmn : m + 1 < n)
    (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (delta epsilon : ℝ)
    (incremented : RootExtensionThresholdPolicy d)
    (hincremented : ∀ S b e, S.lower e ≤ incremented S b e)
    (hgeom : ∀ a : CubicDirection d,
      SeedBoxWithinBoundaryLayer d a.1 m n (W a).seedCenter.1)
    {k : ℕ} (hk : k < (rootExtensionDirectionOrder d).length)
    (hrestart : ∀ c : RootExtensionPrefixStateIndex W p radialIncremented incremented k,
      let a := (rootExtensionDirectionOrder d)[k]
      let S := c.1
      let Q := S.framedQuery (W.physicalCenter a) a
        (oppositeTransverseRestartFlip a)
      (1 - epsilon) * (couplingMeasure (CubicEdge d)).real
          (Q.boundaryHistoryEvent n) <
        (couplingMeasure (CubicEdge d)).real
          (Q.successEvent m n p delta ∩ Q.boundaryHistoryEvent n)) :
    PartitionedFramedRestartStage d
      (RootExtensionPrefixStateIndex W p radialIncremented incremented k)
      m n p delta epsilon := by
  let representative :=
    W.rootExtensionPrefixRepresentative p radialIncremented incremented k
  apply RootRadialSeedProfile.partitionedRootExtensionStageOfProfilePartition
    hm hmn W p radialIncremented
    delta epsilon incremented
    (W.rootExtensionPrefixHistory p radialIncremented incremented k)
    (RootRadialSeedProfile.rootExtensionPrefixDefault
      W p radialIncremented incremented k)
    representative hgeom hk
  · intro c
    rw [W.rootExtensionPrefixState_representative
      p radialIncremented incremented k c]
    exact W.historyProfile_subset_rootExtensionPrefixHistory
      p radialIncremented incremented k c
  · intro X hX
    simp only [RootRadialSeedProfile.rootExtensionPrefixHistory,
      Set.mem_iUnion] at hX ⊢
    obtain ⟨c, hc⟩ := hX
    refine ⟨c, ?_⟩
    simpa [representative] using hc
  · intro c c' hne
    simpa [representative] using
      (W.pairwiseDisjoint_rootExtensionPrefixHistory
        p radialIncremented incremented hincremented k c c' hne)
  · intro c
    simpa [representative] using hrestart c

/-- Exact coverage of the generated reachable-history union. -/
theorem RootRadialSeedProfile.partitionedRootExtensionStageOfReachableHistory_cellUnion
    {d m n : ℕ} [NeZero d] (hm : 1 ≤ m) (hmn : m + 1 < n)
    (W : RootRadialSeedProfile d m n)
    (p radialIncremented : I) (delta epsilon : ℝ)
    (incremented : RootExtensionThresholdPolicy d)
    (hincremented : ∀ S b e, S.lower e ≤ incremented S b e)
    (hgeom : ∀ a : CubicDirection d,
      SeedBoxWithinBoundaryLayer d a.1 m n (W a).seedCenter.1)
    {k : ℕ} (hk : k < (rootExtensionDirectionOrder d).length)
    (hrestart : ∀ c : RootExtensionPrefixStateIndex W p radialIncremented incremented k,
      let a := (rootExtensionDirectionOrder d)[k]
      let S := c.1
      let Q := S.framedQuery (W.physicalCenter a) a
        (oppositeTransverseRestartFlip a)
      (1 - epsilon) * (couplingMeasure (CubicEdge d)).real
          (Q.boundaryHistoryEvent n) <
        (couplingMeasure (CubicEdge d)).real
          (Q.successEvent m n p delta ∩ Q.boundaryHistoryEvent n)) :
    (RootRadialSeedProfile.partitionedRootExtensionStageOfReachableHistory
      hm hmn W p radialIncremented
      delta epsilon incremented hincremented hgeom hk hrestart).cellUnion =
        W.rootExtensionPrefixHistory p radialIncremented incremented k := by
  classical
  unfold RootRadialSeedProfile.partitionedRootExtensionStageOfReachableHistory
  apply RootRadialSeedProfile.partitionedRootExtensionStageOfProfilePartition_cellUnion

end AdaptiveSiteExploration

end Percolation
