import Percolation.Critical.DynamicLaterSiteHistory

/-!
# Total runtime for a non-root dynamic block

The probabilistic construction needs a total query rule, including on histories where an inlet
restart fails.  The source-faithful entry point is `runFrom` on the expanded schedule: two inlet
applications and a face-seed/half-way-link pair for every fresh outgoing direction.  The older
compressed `run` wrapper is retained only for compatibility with local helper theorems.  Both use the canonical mixed-witness
selector.  A fixed geometric default is used only on a failed restart; on success the selected
center is proved to be an actual mixed-threshold seed.
-/

namespace Percolation

open scoped unitInterval

/-- Canonical point at the center of the positive `i`-face. -/
def canonicalRestartBoundaryPoint {d : ℕ} (i : Fin d) (n : ℕ) : Cubic d :=
  fun j ↦ if j = i then n else 0

theorem canonicalRestartBoundaryPoint_mem_seededBoundaryQuadrant
    {d n : ℕ} (i : Fin d) :
    canonicalRestartBoundaryPoint i n ∈ seededBoundaryQuadrant d i n := by
  rw [mem_seededBoundaryQuadrant_iff, mem_cubicBoxFace]
  constructor
  · constructor
    · simp [canonicalRestartBoundaryPoint, cubicOrigin]
    · intro j hji
      simp [canonicalRestartBoundaryPoint, cubicOrigin, hji]
  · intro j hji
    simp [canonicalRestartBoundaryPoint, hji]

/-- A total default witness.  It is geometric data only and is never advertised as open. -/
noncomputable def defaultRestartSeedWitness
    {d m n : ℕ} (i : Fin d) (hmn : 2 * m ≤ n) :
    RestartSeedWitnessIndex d i m n :=
  let y : RestartBoundaryPoint d i n :=
    ⟨canonicalRestartBoundaryPoint i n,
      canonicalRestartBoundaryPoint_mem_seededBoundaryQuadrant i⟩
  { boundaryPoint := y
    seedCenter :=
      ⟨canonicalBoundarySeedCenter i m n y.1,
        seedCenter_mem_seededBoundaryPossibleCenters y.2
          (cubicStepFrom_mem_canonicalBoundarySeedBox i hmn y.2)⟩ }

/-- Runtime information retained while processing one non-root coarse site. -/
@[ext]
structure LaterSiteRuntime (d : ℕ) where
  source : SourceFiniteEdgeRevealState d
  firstTarget : Cubic d
  firstReferenceTarget : Cubic d
  centralTarget : Cubic d
  outgoing : CubicDirection d → Option (LaterSiteOutgoingSeed d)

namespace LaterSiteRuntime

/-- Every seed center stored by a runtime is backed by the complete physical seed box in the
current explored edge set.  This invariant distinguishes usable published seeds from the
geometric defaults carried by the total runtime on failed configurations. -/
def SeedBoxesInstalled {d : ℕ} (m : ℕ) (R : LaterSiteRuntime d) : Prop :=
  cubicBoxEdges d R.firstTarget m ⊆ R.source.explored ∧
    cubicBoxEdges d R.centralTarget m ⊆ R.source.explored ∧
      ∀ a U, R.outgoing a = some U →
        cubicBoxEdges d U.physicalCenter m ⊆ R.source.explored

/-- Runtime before the first inlet restart. -/
noncomputable def initial {d : ℕ}
    (source : SourceFiniteEdgeRevealState d) (inletCenter : Cubic d) :
    LaterSiteRuntime d where
  source := source
  firstTarget := inletCenter
  firstReferenceTarget := cubicOrigin
  centralTarget := inletCenter
  outgoing := fun _ ↦ none

/-- An inlet seed already present in the incoming source state initializes the installed-seed
invariant of the total runtime. -/
theorem seedBoxesInstalled_initial {d m : ℕ}
    (source : SourceFiniteEdgeRevealState d) (inletCenter : Cubic d)
    (hseed : cubicBoxEdges d inletCenter m ⊆ source.explored) :
    (initial source inletCenter).SeedBoxesInstalled m := by
  refine ⟨hseed, hseed, ?_⟩
  intro a U hU
  simp [initial] at hU

/-- Physical center from which a numeric slot starts. -/
def slotCenter {d : ℕ} (R : LaterSiteRuntime d)
    (inletCenter : Cubic d) (k : ℕ) : Cubic d :=
  if k = 0 then inletCenter else if k = 1 then R.firstTarget else R.centralTarget

/-- Physical center for a direction-aware restart slot.  The first occurrence of an outgoing
direction starts from the central seed; its second occurrence starts from the face seed stored
by the first occurrence. -/
def slotCenterFor {d : ℕ} (R : LaterSiteRuntime d)
    (inletCenter : Cubic d) (a : CubicDirection d) (k : ℕ) : Cubic d :=
  if k = 0 then inletCenter
  else if k = 1 then R.firstTarget
  else (R.outgoing a).map LaterSiteOutgoingSeed.physicalCenter |>.getD R.centralTarget

/-- From slot one onward, the runtime always starts at one of its installed seed fields: the
first target, the central target, or an already published outgoing target. -/
theorem SeedBoxesInstalled.cubicBoxEdges_slotCenterFor_subset_explored_of_one_le
    {d m : ℕ} {R : LaterSiteRuntime d} (hR : R.SeedBoxesInstalled m)
    (inletCenter : Cubic d) (a : CubicDirection d) {k : ℕ} (hk : 1 ≤ k) :
    cubicBoxEdges d (R.slotCenterFor inletCenter a k) m ⊆ R.source.explored := by
  rcases hR with ⟨hfirst, hcentral, houtgoing⟩
  by_cases hk1 : k = 1
  · subst k
    simpa [slotCenterFor] using hfirst
  · have hk0 : k ≠ 0 := by omega
    cases hU : R.outgoing a with
    | none => simpa [slotCenterFor, hk0, hk1, hU] using hcentral
    | some U =>
        simpa [slotCenterFor, hk0, hk1, hU] using houtgoing a U hU

/-- Steering mask used at a numeric slot. -/
noncomputable def slotTransverseFlip {d : ℕ} (R : LaterSiteRuntime d)
    (incoming : CubicDirection d) (firstFlip secondFlip : Fin d → Bool)
    (a : CubicDirection d) (k : ℕ) : Fin d → Bool :=
  if k = 0 then firstFlip
  else if k = 1 then inletCompensatingTransverseFlip incoming R.firstReferenceTarget
  else
    match R.outgoing a with
    | none => awayFromInletTransverseFlip incoming a
    | some U => inletCompensatingTransverseFlip a U.referenceCenter

/-- Canonical query at a numeric slot. -/
noncomputable def query {d : ℕ} (R : LaterSiteRuntime d)
    (inletCenter : Cubic d) (incoming : CubicDirection d)
    (firstFlip secondFlip : Fin d → Bool) (a : CubicDirection d) (k : ℕ) :
    FramedRestartQuery d :=
  R.source.framedQuery (R.slotCenter inletCenter k) a
    (R.slotTransverseFlip incoming firstFlip secondFlip a k)

/-- Direction-aware query used by the fully expanded later-site runtime. -/
noncomputable def restartQuery {d : ℕ} (R : LaterSiteRuntime d)
    (inletCenter : Cubic d) (incoming : CubicDirection d)
    (firstFlip secondFlip : Fin d → Bool) (a : CubicDirection d) (k : ℕ) :
    FramedRestartQuery d :=
  R.source.framedQuery (R.slotCenterFor inletCenter a k) a
    (R.slotTransverseFlip incoming firstFlip secondFlip a k)

/-- Installed seed boxes provide the inlet-region hypothesis of Lemma 7.17 at every nonzero
runtime slot. -/
theorem SeedBoxesInstalled.cubicMetricBox_subset_restartQuery_region_of_one_le
    {d m : ℕ} [NeZero d] {R : LaterSiteRuntime d} (hR : R.SeedBoxesInstalled m)
    (hm : 1 ≤ m) (inletCenter : Cubic d) (incoming : CubicDirection d)
    (firstFlip secondFlip : Fin d → Bool) (a : CubicDirection d)
    {k : ℕ} (hk : 1 ≤ k) :
    cubicMetricBox d cubicOrigin m ⊆
      (R.restartQuery inletCenter incoming firstFlip secondFlip a k).region := by
  apply R.source.cubicMetricBox_subset_framedQuery_region_of_seedBox hm
  exact hR.cubicBoxEdges_slotCenterFor_subset_explored_of_one_le inletCenter a hk

/-- The first runtime slot consumes the inlet seed already installed by its accepted parent. -/
theorem cubicMetricBox_subset_initial_restartQuery_region
    {d m : ℕ} [NeZero d] (hm : 1 ≤ m)
    (source : SourceFiniteEdgeRevealState d) (inletCenter : Cubic d)
    (incoming : CubicDirection d) (firstFlip secondFlip : Fin d → Bool)
    (hseed : cubicBoxEdges d inletCenter m ⊆ source.explored) :
    cubicMetricBox d cubicOrigin m ⊆
      ((initial source inletCenter).restartQuery inletCenter incoming
        firstFlip secondFlip incoming 0).region := by
  simpa [restartQuery, initial, slotCenterFor, slotTransverseFlip] using
    source.cubicMetricBox_subset_framedQuery_region_of_seedBox
      hm inletCenter incoming firstFlip hseed

/-- Selected witness at a slot, with the geometric default used exactly when the mixed restart
has no witness. -/
noncomputable def selectedWitness {d m n : ℕ} (hmn : 2 * m ≤ n)
    (R : LaterSiteRuntime d) (inletCenter : Cubic d)
    (incoming : CubicDirection d) (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (X : CubicEdge d → ℝ)
    (a : CubicDirection d) (k : ℕ) : RestartSeedWitnessIndex d a.1 m n :=
  (R.source.selectedMixedWitness (m := m) (n := n)
    (R.slotCenterFor inletCenter a k) a
    (R.slotTransverseFlip incoming firstFlip secondFlip a k) p delta X).getD
      (defaultRestartSeedWitness a.1 hmn)

/-- Physical target center selected at a slot. -/
noncomputable def selectedTarget {d m n : ℕ} (hmn : 2 * m ≤ n)
    (R : LaterSiteRuntime d) (inletCenter : Cubic d)
    (incoming : CubicDirection d) (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (X : CubicEdge d → ℝ)
    (a : CubicDirection d) (k : ℕ) : Cubic d :=
  cubicRestartFrameIso (R.slotCenterFor inletCenter a k) a
    (R.slotTransverseFlip incoming firstFlip secondFlip a k)
    (R.selectedWitness hmn inletCenter incoming firstFlip secondFlip p delta X a k).seedCenter.1

/-- One total source step.  Only branch slots (`k≥2`) publish outgoing anchors. -/
noncomputable def step {d m n : ℕ} (hmn : 2 * m ≤ n)
    (R : LaterSiteRuntime d) (inletCenter : Cubic d)
    (incoming : CubicDirection d) (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) (a : CubicDirection d) (k : ℕ) : LaterSiteRuntime d :=
  let Q := R.restartQuery inletCenter incoming firstFlip secondFlip a k
  let witness := R.selectedWitness hmn inletCenter incoming firstFlip secondFlip
    p delta X a k
  let target := cubicRestartFrameIso (R.slotCenterFor inletCenter a k) a
    (R.slotTransverseFlip incoming firstFlip secondFlip a k) witness.seedCenter.1
  let published : LaterSiteOutgoingSeed d :=
    ⟨target, witness.seedCenter.1⟩
  { source := R.source.next (Q.restartSupport m n) p (incremented R.source a) X
    firstTarget := if k = 0 then target else R.firstTarget
    firstReferenceTarget := if k = 0 then witness.seedCenter.1 else R.firstReferenceTarget
    centralTarget := if k = 1 then target else R.centralTarget
    outgoing := if 2 ≤ k then Function.update R.outgoing a (some published) else R.outgoing }

/-- One total later-site step has finite range whenever its incoming runtime does.  The proof
factors the output through the finite incoming-runtime range, the finite successor-source range,
and the finite type of seed witnesses. -/
theorem finite_range_step_of_finite_range
    {d m n : ℕ} (hmn : 2 * m ≤ n)
    (inletCenter : Cubic d) (incoming : CubicDirection d)
    (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (runtime : (CubicEdge d → ℝ) → LaterSiteRuntime d)
    (a : CubicDirection d) (k : ℕ)
    (hruntime : (Set.range runtime).Finite) :
    (Set.range fun X ↦ (runtime X).step hmn inletCenter incoming
      firstFlip secondFlip p delta incremented X a k).Finite := by
  classical
  let nextSource : (CubicEdge d → ℝ) → SourceFiniteEdgeRevealState d := fun X ↦
    let R := runtime X
    let Q := R.restartQuery inletCenter incoming firstFlip secondFlip a k
    R.source.next (Q.restartSupport m n) p (incremented R.source a) X
  have hnextSource : (Set.range nextSource).Finite := by
    apply (hruntime.biUnion fun R _ ↦
      R.source.finite_range_next
        ((R.restartQuery inletCenter incoming firstFlip secondFlip a k).restartSupport m n)
        p (incremented R.source a)).subset
    rintro S ⟨X, rfl⟩
    simp only [Set.mem_iUnion]
    exact ⟨runtime X, ⟨⟨X, rfl⟩, ⟨X, rfl⟩⟩⟩
  let witness : (CubicEdge d → ℝ) → RestartSeedWitnessIndex d a.1 m n := fun X ↦
    (runtime X).selectedWitness hmn inletCenter incoming firstFlip secondFlip
      p delta X a k
  have hwitness : (Set.range witness).Finite :=
    Set.finite_univ.subset (Set.subset_univ _)
  let data : (CubicEdge d → ℝ) →
      (LaterSiteRuntime d × SourceFiniteEdgeRevealState d) ×
        RestartSeedWitnessIndex d a.1 m n :=
    fun X ↦ ((runtime X, nextSource X), witness X)
  have hdata : (Set.range data).Finite := by
    have hpair : (Set.range fun X ↦ (runtime X, nextSource X)).Finite :=
      (hruntime.prod hnextSource).subset (Set.range_pair_subset runtime nextSource)
    exact (hpair.prod hwitness).subset
      (Set.range_pair_subset (fun X ↦ (runtime X, nextSource X)) witness)
  let assemble :
      ((LaterSiteRuntime d × SourceFiniteEdgeRevealState d) ×
        RestartSeedWitnessIndex d a.1 m n) → LaterSiteRuntime d := fun t ↦
    let R := t.1.1
    let target := cubicRestartFrameIso (R.slotCenterFor inletCenter a k) a
      (R.slotTransverseFlip incoming firstFlip secondFlip a k) t.2.seedCenter.1
    let published : LaterSiteOutgoingSeed d := ⟨target, t.2.seedCenter.1⟩
    { source := t.1.2
      firstTarget := if k = 0 then target else R.firstTarget
      firstReferenceTarget := if k = 0 then t.2.seedCenter.1 else R.firstReferenceTarget
      centralTarget := if k = 1 then target else R.centralTarget
      outgoing := if 2 ≤ k then Function.update R.outgoing a (some published) else R.outgoing }
  apply (hdata.image assemble).subset
  rintro T ⟨X, rfl⟩
  refine ⟨data X, ⟨X, rfl⟩, ?_⟩
  simp only [step, selectedTarget, data, assemble, nextSource, witness]

/-- Run a list of directions whose numeric slot indices start at `offset`. -/
noncomputable def runFrom {d m n : ℕ} (hmn : 2 * m ≤ n)
    (inletCenter : Cubic d) (incoming : CubicDirection d)
    (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) : LaterSiteRuntime d → ℕ →
      List (CubicDirection d) → LaterSiteRuntime d
  | R, _, [] => R
  | R, k, a :: rest =>
      runFrom hmn inletCenter incoming firstFlip secondFlip p delta incremented X
        (R.step hmn inletCenter incoming firstFlip secondFlip p delta incremented X a k)
        (k + 1) rest

/-- A complete runtime schedule only enlarges the explored edge set, independently of whether
its restart events succeed.  This monotonicity lets old published seed certificates survive
later accepted and rejected coarse-site decisions alike. -/
theorem source_explored_subset_runFrom
    {d m n : ℕ} (hmn : 2 * m ≤ n)
    (inletCenter : Cubic d) (incoming : CubicDirection d)
    (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) (R : LaterSiteRuntime d) (offset : ℕ)
    (directions : List (CubicDirection d)) :
    R.source.explored ⊆
      (runFrom hmn inletCenter incoming firstFlip secondFlip p delta incremented X
        R offset directions).source.explored := by
  induction directions generalizing R offset with
  | nil => exact Finset.Subset.rfl
  | cons a rest ih =>
      let Q := R.restartQuery inletCenter incoming firstFlip secondFlip a offset
      let Rnext := R.step hmn inletCenter incoming firstFlip secondFlip
        p delta incremented X a offset
      exact (R.source.explored_subset_nextExplored
        (Q.restartSupport m n) p (incremented R.source a) X).trans
          (by simpa [runFrom, Rnext, Q, step, restartQuery] using
            (ih (R := Rnext) (offset := offset + 1)))

/-- A complete total non-root schedule has finite runtime range whenever its incoming runtime
does.  This is the finite-branching input for exact accumulated-history partitions. -/
theorem finite_range_runFrom
    {d m n : ℕ} (hmn : 2 * m ≤ n)
    (inletCenter : Cubic d) (incoming : CubicDirection d)
    (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (runtime : (CubicEdge d → ℝ) → LaterSiteRuntime d) (offset : ℕ)
    (directions : List (CubicDirection d))
    (hruntime : (Set.range runtime).Finite) :
    (Set.range fun X ↦ runFrom hmn inletCenter incoming firstFlip secondFlip
      p delta incremented X (runtime X) offset directions).Finite := by
  induction directions generalizing runtime offset with
  | nil => simpa using hruntime
  | cons a rest ih =>
      let nextRuntime : (CubicEdge d → ℝ) → LaterSiteRuntime d := fun X ↦
        (runtime X).step hmn inletCenter incoming firstFlip secondFlip
          p delta incremented X a offset
      have hnext : (Set.range nextRuntime).Finite := by
        exact finite_range_step_of_finite_range hmn inletCenter incoming
          firstFlip secondFlip p delta incremented runtime a offset hruntime
      simpa [runFrom, nextRuntime] using ih nextRuntime (offset + 1) hnext

@[simp]
theorem runFrom_nil {d m n : ℕ} (hmn : 2 * m ≤ n)
    (inletCenter : Cubic d) (incoming : CubicDirection d)
    (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) (R : LaterSiteRuntime d) (k : ℕ) :
    runFrom hmn inletCenter incoming firstFlip secondFlip p delta incremented X R k [] = R :=
  rfl

/-- Runtime composition across an appended direction list. -/
theorem runFrom_append {d m n : ℕ} (hmn : 2 * m ≤ n)
    (inletCenter : Cubic d) (incoming : CubicDirection d)
    (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) (R : LaterSiteRuntime d) (k : ℕ)
    (first second : List (CubicDirection d)) :
    runFrom hmn inletCenter incoming firstFlip secondFlip p delta incremented X R k
        (first ++ second) =
      runFrom hmn inletCenter incoming firstFlip secondFlip p delta incremented X
        (runFrom hmn inletCenter incoming firstFlip secondFlip p delta incremented X
          R k first) (k + first.length) second := by
  induction first generalizing R k with
  | nil => simp
  | cons a rest ih =>
      simp only [List.cons_append, runFrom]
      rw [ih]
      simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- A restart step in direction `b` does not alter an outgoing anchor stored under a different
direction `a`. -/
theorem step_outgoing_eq_of_ne {d m n : ℕ} (hmn : 2 * m ≤ n)
    (R : LaterSiteRuntime d) (inletCenter : Cubic d)
    (incoming : CubicDirection d) (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) (a b : CubicDirection d) (k : ℕ)
    (hab : a ≠ b) :
    (R.step hmn inletCenter incoming firstFlip secondFlip p delta incremented X b k
      ).outgoing a = R.outgoing a := by
  by_cases hk : 2 ≤ k
  · simp [step, hk, hab]
  · simp [step, hk]

/-- Running directions none of which equal `a` preserves the outgoing anchor at `a`. -/
theorem runFrom_outgoing_eq_of_not_mem {d m n : ℕ} (hmn : 2 * m ≤ n)
    (inletCenter : Cubic d) (incoming : CubicDirection d)
    (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) (R : LaterSiteRuntime d) (k : ℕ)
    (directions : List (CubicDirection d)) (a : CubicDirection d)
    (ha : a ∉ directions) :
    (runFrom hmn inletCenter incoming firstFlip secondFlip p delta incremented X
      R k directions).outgoing a = R.outgoing a := by
  induction directions generalizing R k with
  | nil => rfl
  | cons b rest ih =>
      simp only [List.mem_cons, not_or] at ha
      simp only [runFrom]
      rw [ih _ _ ha.2]
      exact step_outgoing_eq_of_ne hmn R inletCenter incoming firstFlip secondFlip
        p delta incremented X a b k ha.1

/-- After the two applications assigned to one fresh branch, its table entry is populated.
The first application places the face seed; the second starts from that seed and overwrites the
entry with the final half-way-box seed. -/
theorem exists_outgoing_runFrom_restartPair {d m n : ℕ} (hmn : 2 * m ≤ n)
    (inletCenter : Cubic d) (incoming : CubicDirection d)
    (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) (R : LaterSiteRuntime d) (k : ℕ)
    (a : CubicDirection d) (hk : 2 ≤ k) :
    ∃ U : LaterSiteOutgoingSeed d,
      (runFrom hmn inletCenter incoming firstFlip secondFlip p delta incremented X
        R k (laterSiteBranchRestartPair a)).outgoing a = some U := by
  let R1 := R.step hmn inletCenter incoming firstFlip secondFlip
    p delta incremented X a k
  let W := R1.selectedWitness hmn inletCenter incoming firstFlip secondFlip p delta X a (k + 1)
  let U : LaterSiteOutgoingSeed d :=
    ⟨cubicRestartFrameIso (R1.slotCenterFor inletCenter a (k + 1)) a
        (R1.slotTransverseFlip incoming firstFlip secondFlip a (k + 1)) W.seedCenter.1,
      W.seedCenter.1⟩
  refine ⟨U, ?_⟩
  change (R1.step hmn inletCenter incoming firstFlip secondFlip
    p delta incremented X a (k + 1)).outgoing a = some U
  have hk' : 2 ≤ k + 1 := by omega
  simp [step, U, W, hk']

/-- The link-up application for a fresh branch starts at the physical face seed produced by
the immediately preceding application. -/
theorem slotCenterFor_step_same_succ_of_two_le {d m n : ℕ} (hmn : 2 * m ≤ n)
    (R : LaterSiteRuntime d) (inletCenter : Cubic d)
    (incoming : CubicDirection d) (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) (a : CubicDirection d) (k : ℕ) (hk : 2 ≤ k) :
    (R.step hmn inletCenter incoming firstFlip secondFlip p delta incremented X a k
      ).slotCenterFor inletCenter a (k + 1) =
      R.selectedTarget hmn inletCenter incoming firstFlip secondFlip p delta X a k := by
  have hk0 : k + 1 ≠ 0 := by omega
  have hk1 : k + 1 ≠ 1 := by omega
  have hkBase0 : k ≠ 0 := by omega
  have hkBase1 : k ≠ 1 := by omega
  simp [slotCenterFor, step, selectedTarget, hk, hk0, hk1, hkBase0, hkBase1]

/-- The second inlet application starts at the seed selected by the first inlet application. -/
theorem slotCenterFor_step_zero_one {d m n : ℕ} (hmn : 2 * m ≤ n)
    (R : LaterSiteRuntime d) (inletCenter : Cubic d)
    (incoming : CubicDirection d) (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) (a : CubicDirection d) :
    (R.step hmn inletCenter incoming firstFlip secondFlip p delta incremented X a 0
      ).slotCenterFor inletCenter a 1 =
      R.selectedTarget hmn inletCenter incoming firstFlip secondFlip p delta X a 0 := by
  simp [slotCenterFor, step, selectedTarget]

/-- After the second inlet application, the first unused outgoing branch starts at the new
central seed.  The only premise records that no earlier slot populated that branch entry. -/
theorem slotCenterFor_step_one_two_of_outgoing_eq_none
    {d m n : ℕ} (hmn : 2 * m ≤ n)
    (R : LaterSiteRuntime d) (inletCenter : Cubic d)
    (incoming : CubicDirection d) (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) (a b : CubicDirection d)
    (hnone : R.outgoing b = none) :
    (R.step hmn inletCenter incoming firstFlip secondFlip p delta incremented X a 1
      ).slotCenterFor inletCenter b 2 =
      R.selectedTarget hmn inletCenter incoming firstFlip secondFlip p delta X a 1 := by
  simp [slotCenterFor, step, selectedTarget, hnone]

/-- The second application steers relative to the reference coordinates of the face seed
selected by the first application. -/
theorem slotTransverseFlip_step_same_succ_of_two_le
    {d m n : ℕ} (hmn : 2 * m ≤ n)
    (R : LaterSiteRuntime d) (inletCenter : Cubic d)
    (incoming : CubicDirection d) (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) (a : CubicDirection d) (k : ℕ) (hk : 2 ≤ k) :
    (R.step hmn inletCenter incoming firstFlip secondFlip p delta incremented X a k
      ).slotTransverseFlip incoming firstFlip secondFlip a (k + 1) =
      inletCompensatingTransverseFlip a
        (R.selectedWitness hmn inletCenter incoming firstFlip secondFlip
          p delta X a k).seedCenter.1 := by
  have hk0 : k + 1 ≠ 0 := by omega
  have hk1 : k + 1 ≠ 1 := by omega
  have hkBase0 : k ≠ 0 := by omega
  have hkBase1 : k ≠ 1 := by omega
  simp [slotTransverseFlip, step, hk, hk0, hk1, hkBase0, hkBase1]

/-- Every direction in a duplicate-pair branch schedule has a final published outgoing seed.
No later pair overwrites it because the branch list has no duplicates. -/
theorem exists_outgoing_runFrom_branchPairs {d m n : ℕ} (hmn : 2 * m ≤ n)
    (inletCenter : Cubic d) (incoming : CubicDirection d)
    (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) (R : LaterSiteRuntime d) (k : ℕ)
    (branches : List (CubicDirection d)) (hnodup : branches.Nodup)
    (a : CubicDirection d) (ha : a ∈ branches) (hk : 2 ≤ k) :
    ∃ U : LaterSiteOutgoingSeed d,
      (runFrom hmn inletCenter incoming firstFlip secondFlip p delta incremented X
        R k (branches.flatMap laterSiteBranchRestartPair)).outgoing a = some U := by
  induction branches generalizing R k with
  | nil => simp at ha
  | cons b rest ih =>
      rw [List.nodup_cons] at hnodup
      simp only [List.mem_cons] at ha
      simp only [List.flatMap_cons]
      rw [runFrom_append]
      by_cases hab : a = b
      · subst b
        obtain ⟨U, hU⟩ := exists_outgoing_runFrom_restartPair hmn inletCenter incoming
          firstFlip secondFlip p delta incremented X R k a hk
        refine ⟨U, ?_⟩
        rw [runFrom_outgoing_eq_of_not_mem hmn inletCenter incoming firstFlip secondFlip
          p delta incremented X _ _ (rest.flatMap laterSiteBranchRestartPair) a]
        · exact hU
        · simpa [laterSiteBranchRestartPair] using hnodup.1
      · apply ih
          (R := runFrom hmn inletCenter incoming firstFlip secondFlip p delta incremented X
            R k (laterSiteBranchRestartPair b))
          (k := k + (laterSiteBranchRestartPair b).length)
          hnodup.2 (ha.resolve_left hab)
        simp [laterSiteBranchRestartPair]

/-- Compatibility runtime for the book's compressed one-entry-per-branch schedule.  The global
history replay uses `runFrom` with the fully expanded two-entry branch schedule. -/
noncomputable def run {d m n : ℕ} (hd : 0 < d) (hmn : 2 * m ≤ n)
    (source : SourceFiniteEdgeRevealState d) (inletCenter : Cubic d)
    (incoming : CubicDirection d) (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) : LaterSiteRuntime d :=
  runFrom hmn inletCenter incoming firstFlip secondFlip p delta incremented X
    (initial source inletCenter) 0 (laterSiteDirectionOrder incoming)

/-- Literal success conjunction along the same total runtime. -/
def succeedsFrom {d m n : ℕ} (hmn : 2 * m ≤ n)
    (inletCenter : Cubic d) (incoming : CubicDirection d)
    (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) : LaterSiteRuntime d → ℕ →
      List (CubicDirection d) → Prop
  | _, _, [] => True
  | R, k, a :: rest =>
      X ∈ (R.restartQuery inletCenter incoming firstFlip secondFlip a k
        ).successEvent m n p delta ∧
        succeedsFrom hmn inletCenter incoming firstFlip secondFlip p delta incremented X
          (R.step hmn inletCenter incoming firstFlip secondFlip p delta incremented X a k)
          (k + 1) rest

@[simp]
theorem succeedsFrom_nil {d m n : ℕ} (hmn : 2 * m ≤ n)
    (inletCenter : Cubic d) (incoming : CubicDirection d)
    (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) (R : LaterSiteRuntime d) (k : ℕ) :
    succeedsFrom hmn inletCenter incoming firstFlip secondFlip p delta incremented X R k [] :=
  trivial

/-- Success along an appended total schedule splits at the literal intermediate runtime. -/
theorem succeedsFrom_append {d m n : ℕ} (hmn : 2 * m ≤ n)
    (inletCenter : Cubic d) (incoming : CubicDirection d)
    (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) (R : LaterSiteRuntime d) (offset : ℕ)
    (first second : List (CubicDirection d)) :
    succeedsFrom hmn inletCenter incoming firstFlip secondFlip p delta incremented X R offset
        (first ++ second) ↔
      succeedsFrom hmn inletCenter incoming firstFlip secondFlip p delta incremented X R offset
          first ∧
        succeedsFrom hmn inletCenter incoming firstFlip secondFlip p delta incremented X
          (runFrom hmn inletCenter incoming firstFlip secondFlip p delta incremented X
            R offset first) (offset + first.length) second := by
  induction first generalizing R offset with
  | nil => simp
  | cons a rest ih =>
      simp only [List.cons_append, succeedsFrom, runFrom]
      rw [ih]
      simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      tauto

/-- Success of a duplicate-pair branch schedule exposes both successful restart applications
assigned to each branch: first the face-seed step, then the half-way-box link-up. -/
theorem exists_successful_restartPair_of_mem {d m n : ℕ} (hmn : 2 * m ≤ n)
    (inletCenter : Cubic d) (incoming : CubicDirection d)
    (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) (R : LaterSiteRuntime d) (k : ℕ)
    (branches : List (CubicDirection d))
    (hsuccess : succeedsFrom hmn inletCenter incoming firstFlip secondFlip
      p delta incremented X R k (branches.flatMap laterSiteBranchRestartPair))
    (a : CubicDirection d) (ha : a ∈ branches) :
    ∃ (Rpre : LaterSiteRuntime d) (j : ℕ),
      X ∈ (Rpre.restartQuery inletCenter incoming firstFlip secondFlip a j
        ).successEvent m n p delta ∧
      X ∈ ((Rpre.step hmn inletCenter incoming firstFlip secondFlip
        p delta incremented X a j).restartQuery inletCenter incoming
          firstFlip secondFlip a (j + 1)).successEvent m n p delta := by
  induction branches generalizing R k with
  | nil => simp at ha
  | cons b rest ih =>
      simp only [List.flatMap_cons] at hsuccess
      rw [succeedsFrom_append] at hsuccess
      simp only [List.mem_cons] at ha
      by_cases hab : a = b
      · subst b
        refine ⟨R, k, hsuccess.1.1, ?_⟩
        simpa [laterSiteBranchRestartPair, succeedsFrom, runFrom] using hsuccess.1.2.1
      · apply ih
          (R := runFrom hmn inletCenter incoming firstFlip secondFlip p delta incremented X
            R k (laterSiteBranchRestartPair b))
          (k := k + (laterSiteBranchRestartPair b).length)
          hsuccess.2 (ha.resolve_left hab)

/-- A successful total schedule succeeds at each concrete list slot. -/
theorem succeedsFrom_getElem {d m n : ℕ} (hmn : 2 * m ≤ n)
    (inletCenter : Cubic d) (incoming : CubicDirection d)
    (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) (R : LaterSiteRuntime d) (offset : ℕ)
    (directions : List (CubicDirection d))
    (hsuccess : succeedsFrom hmn inletCenter incoming firstFlip secondFlip
      p delta incremented X R offset directions)
    (j : ℕ) (hj : j < directions.length) :
    let Rj := runFrom hmn inletCenter incoming firstFlip secondFlip
      p delta incremented X R offset (directions.take j)
    let a := directions[j]
    X ∈ (Rj.restartQuery inletCenter incoming firstFlip secondFlip a (offset + j)
      ).successEvent m n p delta := by
  have hsplit : directions = directions.take j ++ directions.drop j :=
    (List.take_append_drop j directions).symm
  rw [hsplit, succeedsFrom_append] at hsuccess
  have htail := hsuccess.2
  rw [List.drop_eq_getElem_cons hj] at htail
  have hlen : (directions.take j).length = j := List.length_take_of_le (Nat.le_of_lt hj)
  simpa [hlen] using htail.1

/-- Slotwise characterization of success along an arbitrary total runtime schedule. -/
theorem succeedsFrom_iff_forall_getElem {d m n : ℕ} (hmn : 2 * m ≤ n)
    (inletCenter : Cubic d) (incoming : CubicDirection d)
    (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) (R : LaterSiteRuntime d) (offset : ℕ)
    (directions : List (CubicDirection d)) :
    succeedsFrom hmn inletCenter incoming firstFlip secondFlip
        p delta incremented X R offset directions ↔
      ∀ j (hj : j < directions.length),
        let Rj := runFrom hmn inletCenter incoming firstFlip secondFlip
          p delta incremented X R offset (directions.take j)
        let a := directions[j]
        X ∈ (Rj.restartQuery inletCenter incoming firstFlip secondFlip a (offset + j)
          ).successEvent m n p delta := by
  constructor
  · intro hsuccess j hj
    exact succeedsFrom_getElem hmn inletCenter incoming firstFlip secondFlip
      p delta incremented X R offset directions hsuccess j hj
  · intro hall
    induction directions generalizing R offset with
    | nil => trivial
    | cons a rest ih =>
        constructor
        · simpa using hall 0 (by simp)
        · apply ih
          intro j hj
          have hs := hall (j + 1) (by simp; omega)
          simpa [List.take_succ_cons, runFrom, Nat.add_assoc,
            Nat.add_comm, Nat.add_left_comm] using hs

/-- A schedule whose length is bounded by `budget` is equivalently the conjunction of its
literal restart slots, padded by `True` up to that uniform budget.  This is the small generic
bridge used by the history-replayed block program, where every site receives the same `4d`
probability exponent even though boundary directions may shorten its active schedule. -/
theorem succeedsFrom_iff_forall_padded {d m n : ℕ} (hmn : 2 * m ≤ n)
    (inletCenter : Cubic d) (incoming : CubicDirection d)
    (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) (R : LaterSiteRuntime d) (offset budget : ℕ)
    (directions : List (CubicDirection d))
    (hlength : directions.length ≤ budget) :
    succeedsFrom hmn inletCenter incoming firstFlip secondFlip
        p delta incremented X R offset directions ↔
      ∀ j < budget,
        if hj : j < directions.length then
          let Rj := runFrom hmn inletCenter incoming firstFlip secondFlip
            p delta incremented X R offset (directions.take j)
          let a := directions[j]
          X ∈ (Rj.restartQuery inletCenter incoming firstFlip secondFlip a (offset + j)
            ).successEvent m n p delta
        else True := by
  rw [succeedsFrom_iff_forall_getElem]
  constructor
  · intro hall j _hjBudget
    split_ifs with hj
    · exact hall j hj
  · intro hall j hj
    have hjBudget : j < budget := lt_of_lt_of_le hj hlength
    simpa [hj] using hall j hjBudget

/-- Compatibility success event for the compressed book schedule.  The source-faithful global
answer uses `succeedsFrom` with `activeLaterSiteDirectionOrder`. -/
def succeeds {d m n : ℕ} (hd : 0 < d) (hmn : 2 * m ≤ n)
    (source : SourceFiniteEdgeRevealState d) (inletCenter : Cubic d)
    (incoming : CubicDirection d) (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) : Prop :=
  succeedsFrom hmn inletCenter incoming firstFlip secondFlip p delta incremented X
    (initial source inletCenter) 0 (laterSiteDirectionOrder incoming)

/-- On a successful slot, the runtime selector is an actual mixed-threshold witness rather
than the default. -/
theorem selectedWitness_isMixed_of_success
    {d m n : ℕ} {hmn : 2 * m ≤ n}
    (R : LaterSiteRuntime d) (inletCenter : Cubic d)
    (incoming : CubicDirection d) (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (X : CubicEdge d → ℝ)
    (a : CubicDirection d) (k : ℕ)
    (hsuccess : X ∈ (R.restartQuery inletCenter incoming firstFlip secondFlip a k
      ).successEvent m n p delta) :
    (R.selectedWitness hmn inletCenter incoming firstFlip secondFlip p delta X a k
      ).IsMixedRestartWitness
        (R.restartQuery inletCenter incoming firstFlip secondFlip a k).region p
        (R.restartQuery inletCenter incoming firstFlip secondFlip a k).beta delta
        (cubicGraphIsoCouplingReindex
          (cubicRestartFrameIso (R.slotCenterFor inletCenter a k) a
            (R.slotTransverseFlip incoming firstFlip secondFlip a k)) X) := by
  obtain ⟨W, hselected, hW⟩ := R.source.exists_selectedMixedWitness_of_success
    (R.slotCenterFor inletCenter a k) a
    (R.slotTransverseFlip incoming firstFlip secondFlip a k) p delta X hsuccess
  rw [selectedWitness, hselected]
  exact hW

/-- A successful runtime slot installs the selected physical seed in the explored edge set of
the successor runtime.  Unlike the total target selector, this theorem is used only on the
successful branch, so its center is certified by the actual mixed-threshold witness. -/
theorem selectedTarget_seedBox_subset_step_source_explored_of_success
    {d m n : ℕ} {hmn : 2 * m ≤ n}
    (R : LaterSiteRuntime d) (inletCenter : Cubic d)
    (incoming : CubicDirection d) (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) (a : CubicDirection d) (k : ℕ)
    (hTargetFresh :
      let F := cubicRestartFrameIso (R.slotCenterFor inletCenter a k) a
        (R.slotTransverseFlip incoming firstFlip secondFlip a k)
      Disjoint (cubicEdgeEndpointVertices (R.source.referenceExploredEdges F))
        (cubicEdgeEndpointVertices (seededBoundaryTargetSupport d a.1 m n)))
    (hincremented : ∀ e ∈
        (R.restartQuery inletCenter incoming firstFlip secondFlip a k).boundarySupport n,
      ((R.restartQuery inletCenter incoming firstFlip secondFlip a k
        ).physicalBoundaryThreshold e : ℝ) + delta ≤
        (incremented R.source a e : ℝ))
    (hsuccess : X ∈ (R.restartQuery inletCenter incoming firstFlip secondFlip a k
      ).successEvent m n p delta) :
    cubicBoxEdges d
        (R.selectedTarget hmn inletCenter incoming firstFlip secondFlip p delta X a k) m ⊆
      (R.step hmn inletCenter incoming firstFlip secondFlip
        p delta incremented X a k).source.explored := by
  let W := R.selectedWitness hmn inletCenter incoming firstFlip secondFlip p delta X a k
  have hW := R.selectedWitness_isMixed_of_success (hmn := hmn)
    inletCenter incoming firstFlip secondFlip p delta X a k hsuccess
  have hseed := R.source.mixedWitness_seedBox_subset_nextExplored
    (R.slotCenterFor inletCenter a k) a
    (R.slotTransverseFlip incoming firstFlip secondFlip a k)
    p delta (incremented R.source a) X W hTargetFresh hincremented hW
  simpa [W, selectedTarget, step, restartQuery] using hseed

/-- Whenever the next runtime query is centered at the seed selected by the current slot, its
reference region contains the full standard inlet box.  The next direction and steering mask
may be arbitrary; only the physical center matters for this handoff. -/
theorem cubicMetricBox_subset_step_restartQuery_region_of_success
    {d m n : ℕ} [NeZero d] {hmn : 2 * m ≤ n}
    (hm : 1 ≤ m) (R : LaterSiteRuntime d) (inletCenter : Cubic d)
    (incoming : CubicDirection d) (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) (a : CubicDirection d) (k : ℕ)
    (hTargetFresh :
      let F := cubicRestartFrameIso (R.slotCenterFor inletCenter a k) a
        (R.slotTransverseFlip incoming firstFlip secondFlip a k)
      Disjoint (cubicEdgeEndpointVertices (R.source.referenceExploredEdges F))
        (cubicEdgeEndpointVertices (seededBoundaryTargetSupport d a.1 m n)))
    (hincremented : ∀ e ∈
        (R.restartQuery inletCenter incoming firstFlip secondFlip a k).boundarySupport n,
      ((R.restartQuery inletCenter incoming firstFlip secondFlip a k
        ).physicalBoundaryThreshold e : ℝ) + delta ≤
        (incremented R.source a e : ℝ))
    (hsuccess : X ∈ (R.restartQuery inletCenter incoming firstFlip secondFlip a k
      ).successEvent m n p delta)
    (b : CubicDirection d) (l : ℕ)
    (hcenter :
      (R.step hmn inletCenter incoming firstFlip secondFlip
        p delta incremented X a k).slotCenterFor inletCenter b l =
        R.selectedTarget hmn inletCenter incoming firstFlip secondFlip p delta X a k) :
    cubicMetricBox d cubicOrigin m ⊆
      ((R.step hmn inletCenter incoming firstFlip secondFlip
        p delta incremented X a k).restartQuery inletCenter incoming
          firstFlip secondFlip b l).region := by
  let Rnext := R.step hmn inletCenter incoming firstFlip secondFlip
    p delta incremented X a k
  have hseed := R.selectedTarget_seedBox_subset_step_source_explored_of_success
    (hmn := hmn)
    inletCenter incoming firstFlip secondFlip p delta incremented X a k
      hTargetFresh hincremented hsuccess
  change cubicMetricBox d cubicOrigin m ⊆
    (Rnext.source.framedQuery (Rnext.slotCenterFor inletCenter b l) b
      (Rnext.slotTransverseFlip incoming firstFlip secondFlip b l)).region
  rw [hcenter]
  exact Rnext.source.cubicMetricBox_subset_framedQuery_region_of_seedBox
    hm _ _ _ hseed

/-- A successful runtime step preserves every previously installed seed box and installs the
new selected target in whichever runtime field the slot updates. -/
theorem seedBoxesInstalled_step_of_success
    {d m n : ℕ} {hmn : 2 * m ≤ n}
    (R : LaterSiteRuntime d) (inletCenter : Cubic d)
    (incoming : CubicDirection d) (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) (a : CubicDirection d) (k : ℕ)
    (hinstalled : R.SeedBoxesInstalled m)
    (hTargetFresh :
      let F := cubicRestartFrameIso (R.slotCenterFor inletCenter a k) a
        (R.slotTransverseFlip incoming firstFlip secondFlip a k)
      Disjoint (cubicEdgeEndpointVertices (R.source.referenceExploredEdges F))
        (cubicEdgeEndpointVertices (seededBoundaryTargetSupport d a.1 m n)))
    (hincremented : ∀ e ∈
        (R.restartQuery inletCenter incoming firstFlip secondFlip a k).boundarySupport n,
      ((R.restartQuery inletCenter incoming firstFlip secondFlip a k
        ).physicalBoundaryThreshold e : ℝ) + delta ≤
        (incremented R.source a e : ℝ))
    (hsuccess : X ∈ (R.restartQuery inletCenter incoming firstFlip secondFlip a k
      ).successEvent m n p delta) :
    (R.step hmn inletCenter incoming firstFlip secondFlip
      p delta incremented X a k).SeedBoxesInstalled m := by
  let Rnext := R.step hmn inletCenter incoming firstFlip secondFlip
    p delta incremented X a k
  have hmono : R.source.explored ⊆ Rnext.source.explored := by
    exact R.source.explored_subset_nextExplored
      ((R.restartQuery inletCenter incoming firstFlip secondFlip a k).restartSupport m n)
      p (incremented R.source a) X
  have hnew := R.selectedTarget_seedBox_subset_step_source_explored_of_success
    (hmn := hmn) inletCenter incoming firstFlip secondFlip p delta incremented X a k
      hTargetFresh hincremented hsuccess
  rcases hinstalled with ⟨hfirst, hcentral, houtgoing⟩
  refine ⟨?_, ?_, ?_⟩
  · by_cases hk : k = 0
    · subst k
      simpa [Rnext, step, selectedTarget] using hnew
    · simpa [Rnext, step, hk] using fun e he ↦ hmono (hfirst he)
  · by_cases hk : k = 1
    · subst k
      simpa [Rnext, step, selectedTarget] using hnew
    · simpa [Rnext, step, hk] using fun e he ↦ hmono (hcentral he)
  · intro b U hU
    by_cases hk : 2 ≤ k
    · by_cases hba : b = a
      · subst b
        have hU' : U =
            { physicalCenter :=
                R.selectedTarget hmn inletCenter incoming firstFlip secondFlip p delta X a k
              referenceCenter :=
                (R.selectedWitness hmn inletCenter incoming firstFlip secondFlip
                  p delta X a k).seedCenter.1 } := by
          have hsome : some U = some
              { physicalCenter :=
                  R.selectedTarget hmn inletCenter incoming firstFlip secondFlip p delta X a k
                referenceCenter :=
                  (R.selectedWitness hmn inletCenter incoming firstFlip secondFlip
                    p delta X a k).seedCenter.1 } := by
            simpa [Rnext, step, selectedTarget, hk] using hU.symm
          exact Option.some.inj hsome
        subst U
        simpa using hnew
      · have hUold : R.outgoing b = some U := by
          simpa [Rnext, step, hk, hba] using hU
        exact fun e he ↦ hmono (houtgoing b U hUold he)
    · have hUold : R.outgoing b = some U := by
        simpa [Rnext, step, hk] using hU
      exact fun e he ↦ hmono (houtgoing b U hUold he)

/-- Slotwise freshness and literal increment bounds propagate the installed-seed invariant
through an arbitrary successful runtime schedule. -/
theorem seedBoxesInstalled_runFrom_of_succeedsFrom
    {d m n : ℕ} {hmn : 2 * m ≤ n}
    (inletCenter : Cubic d) (incoming : CubicDirection d)
    (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) (R : LaterSiteRuntime d) (offset : ℕ)
    (directions : List (CubicDirection d))
    (hinstalled : R.SeedBoxesInstalled m)
    (hsuccess : succeedsFrom hmn inletCenter incoming firstFlip secondFlip
      p delta incremented X R offset directions)
    (hready : ∀ j (hj : j < directions.length),
      let Rj := runFrom hmn inletCenter incoming firstFlip secondFlip
        p delta incremented X R offset (directions.take j)
      let a := directions[j]
      Disjoint
          (cubicEdgeEndpointVertices (Rj.source.referenceExploredEdges
            (cubicRestartFrameIso (Rj.slotCenterFor inletCenter a (offset + j)) a
              (Rj.slotTransverseFlip incoming firstFlip secondFlip a (offset + j)))))
          (cubicEdgeEndpointVertices (seededBoundaryTargetSupport d a.1 m n)) ∧
      ∀ e ∈ (Rj.restartQuery inletCenter incoming firstFlip secondFlip a (offset + j)
        ).boundarySupport n,
        ((Rj.restartQuery inletCenter incoming firstFlip secondFlip a (offset + j)
          ).physicalBoundaryThreshold e : ℝ) + delta ≤
          (incremented Rj.source a e : ℝ)) :
    (runFrom hmn inletCenter incoming firstFlip secondFlip p delta incremented X
      R offset directions).SeedBoxesInstalled m := by
  induction directions generalizing R offset with
  | nil => exact hinstalled
  | cons a rest ih =>
      have hlocal := hready 0 (by simp)
      have hfresh :
          let frame := cubicRestartFrameIso (R.slotCenterFor inletCenter a offset) a
            (R.slotTransverseFlip incoming firstFlip secondFlip a offset)
          Disjoint (cubicEdgeEndpointVertices (R.source.referenceExploredEdges frame))
            (cubicEdgeEndpointVertices (seededBoundaryTargetSupport d a.1 m n)) := by
        simpa [runFrom] using hlocal.1
      have hinc : ∀ e ∈
          (R.restartQuery inletCenter incoming firstFlip secondFlip a offset).boundarySupport n,
        ((R.restartQuery inletCenter incoming firstFlip secondFlip a offset
          ).physicalBoundaryThreshold e : ℝ) + delta ≤
          (incremented R.source a e : ℝ) := by
        simpa [runFrom] using hlocal.2
      have hnextInstalled := R.seedBoxesInstalled_step_of_success (hmn := hmn)
        inletCenter incoming firstFlip secondFlip p delta incremented X a offset
          hinstalled hfresh hinc hsuccess.1
      apply ih
        (R := R.step hmn inletCenter incoming firstFlip secondFlip
          p delta incremented X a offset)
        (offset := offset + 1) hnextInstalled hsuccess.2
      intro j hj
      have h := hready (j + 1) (by simp; omega)
      simpa [List.take_succ_cons, runFrom, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using h

/-- Numeric slot of a non-backtracking branch direction. -/
noncomputable def branchSlotIndex {d : ℕ}
    (incoming a : CubicDirection d) : ℕ :=
  (laterSiteBranchDirections incoming).toList.idxOf a + 2

theorem branchSlotIndex_lt {d : ℕ} (hd : 0 < d)
    (incoming a : CubicDirection d)
    (ha : a ≠ reverseCubicDirection incoming) :
    branchSlotIndex incoming a < (laterSiteDirectionOrder incoming).length := by
  have hamem : a ∈ (laterSiteBranchDirections incoming).toList := by
    simpa [mem_laterSiteBranchDirections_iff] using ha
  have hidx := List.idxOf_lt_length_of_mem hamem
  have hcard := laterSiteBranchDirections_card hd incoming
  have hlen : (laterSiteBranchDirections incoming).toList.length = 2 * d - 1 := by
    simpa using hcard
  rw [hlen] at hidx
  rw [branchSlotIndex, laterSiteDirectionOrder_length hd]
  omega

@[simp]
theorem laterSiteDirectionOrder_get_branchSlotIndex {d : ℕ} (hd : 0 < d)
    (incoming a : CubicDirection d)
    (ha : a ≠ reverseCubicDirection incoming) :
    (laterSiteDirectionOrder incoming)[branchSlotIndex incoming a]'(
      branchSlotIndex_lt hd incoming a ha) = a := by
  have hamem : a ∈ (laterSiteBranchDirections incoming).toList := by
    simpa [mem_laterSiteBranchDirections_iff] using ha
  have hidx := List.idxOf_lt_length_of_mem hamem
  simpa [laterSiteDirectionOrder, branchSlotIndex] using
    (List.getElem_idxOf hidx)

/-- Runtime immediately before the outgoing branch in direction `a`. -/
noncomputable def branchPrefixRuntime {d m n : ℕ}
    (hd : 0 < d) (hmn : 2 * m ≤ n)
    (source : SourceFiniteEdgeRevealState d) (inletCenter : Cubic d)
    (incoming a : CubicDirection d) (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) : LaterSiteRuntime d :=
  runFrom hmn inletCenter incoming firstFlip secondFlip p delta incremented X
    (initial source inletCenter) 0
    ((laterSiteDirectionOrder incoming).take (branchSlotIndex incoming a))

/-- Full outgoing seed record selected by a non-backtracking branch. -/
noncomputable def outgoingSeed {d m n : ℕ}
    (hd : 0 < d) (hmn : 2 * m ≤ n)
    (source : SourceFiniteEdgeRevealState d) (inletCenter : Cubic d)
    (incoming a : CubicDirection d) (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) : LaterSiteOutgoingSeed d :=
  let R := branchPrefixRuntime hd hmn source inletCenter incoming a
    firstFlip secondFlip p delta incremented X
  let k := branchSlotIndex incoming a
  let W := R.selectedWitness hmn inletCenter incoming firstFlip secondFlip p delta X a k
  ⟨cubicRestartFrameIso (R.slotCenterFor inletCenter a k) a
      (R.slotTransverseFlip incoming firstFlip secondFlip a k) W.seedCenter.1,
    W.seedCenter.1⟩

/-- Actual physical center of the selected outgoing seed. -/
noncomputable def outgoingSeedCenter {d m n : ℕ}
    (hd : 0 < d) (hmn : 2 * m ≤ n)
    (source : SourceFiniteEdgeRevealState d) (inletCenter : Cubic d)
    (incoming a : CubicDirection d) (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) : Cubic d :=
  (outgoingSeed hd hmn source inletCenter incoming a firstFlip secondFlip
    p delta incremented X).physicalCenter

@[simp]
theorem outgoingSeed_referenceCenter
    {d m n : ℕ} (hd : 0 < d) (hmn : 2 * m ≤ n)
    (source : SourceFiniteEdgeRevealState d) (inletCenter : Cubic d)
    (incoming a : CubicDirection d) (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) :
    (outgoingSeed hd hmn source inletCenter incoming a firstFlip secondFlip
      p delta incremented X).referenceCenter =
      let R := branchPrefixRuntime hd hmn source inletCenter incoming a
        firstFlip secondFlip p delta incremented X
      R.selectedWitness hmn inletCenter incoming firstFlip secondFlip p delta X a
        (branchSlotIndex incoming a) |>.seedCenter.1 := by
  rfl

/-- Completion of a non-root site exposes a literal mixed-threshold outgoing seed in every
direction except back toward its parent. -/
theorem outgoingSeed_isMixed_of_succeeds
    {d m n : ℕ} (hd : 0 < d) (hmn : 2 * m ≤ n)
    (source : SourceFiniteEdgeRevealState d) (inletCenter : Cubic d)
    (incoming a : CubicDirection d) (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ)
    (hsuccess : succeeds hd hmn source inletCenter incoming firstFlip secondFlip
      p delta incremented X)
    (ha : a ≠ reverseCubicDirection incoming) :
    let R := branchPrefixRuntime hd hmn source inletCenter incoming a
      firstFlip secondFlip p delta incremented X
    let k := branchSlotIndex incoming a
    (R.selectedWitness hmn inletCenter incoming firstFlip secondFlip p delta X a k
      ).IsMixedRestartWitness
        (R.restartQuery inletCenter incoming firstFlip secondFlip a k).region p
        (R.restartQuery inletCenter incoming firstFlip secondFlip a k).beta delta
        (cubicGraphIsoCouplingReindex
          (cubicRestartFrameIso (R.slotCenterFor inletCenter a k) a
            (R.slotTransverseFlip incoming firstFlip secondFlip a k)) X) := by
  let k := branchSlotIndex incoming a
  have hk := branchSlotIndex_lt hd incoming a ha
  have hslot := succeedsFrom_getElem hmn inletCenter incoming firstFlip secondFlip
    p delta incremented X (initial source inletCenter) 0
      (laterSiteDirectionOrder incoming) hsuccess k hk
  have hdir := laterSiteDirectionOrder_get_branchSlotIndex hd incoming a ha
  rw [hdir] at hslot
  exact selectedWitness_isMixed_of_success
    (branchPrefixRuntime hd hmn source inletCenter incoming a firstFlip secondFlip
      p delta incremented X)
    inletCenter incoming firstFlip secondFlip p delta X a k hslot

end LaterSiteRuntime

end Percolation
