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
  /-- Deterministic coarse-site center relative to which the two inlet steering moves are
  recomputed. -/
  inletReferenceBase : Cubic d
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

/-- Runtime before the first inlet restart, with an explicit destination coarse-site center. -/
noncomputable def initialAt {d : ℕ}
    (source : SourceFiniteEdgeRevealState d) (inletCenter referenceBase : Cubic d) :
    LaterSiteRuntime d where
  source := source
  inletReferenceBase := referenceBase
  firstTarget := inletCenter
  firstReferenceTarget := cubicOrigin
  centralTarget := inletCenter
  outgoing := fun _ ↦ none

/-- Compatibility initializer for local runtime lemmas which do not distinguish the inlet
anchor from the destination reference center. -/
noncomputable def initial {d : ℕ}
    (source : SourceFiniteEdgeRevealState d) (inletCenter : Cubic d) :
    LaterSiteRuntime d :=
  initialAt source inletCenter inletCenter

/-- An inlet seed already present in the incoming source state initializes the installed-seed
invariant of the total runtime. -/
theorem seedBoxesInstalled_initial {d m : ℕ}
    (source : SourceFiniteEdgeRevealState d) (inletCenter : Cubic d)
    (hseed : cubicBoxEdges d inletCenter m ⊆ source.explored) :
    (initial source inletCenter).SeedBoxesInstalled m := by
  refine ⟨hseed, hseed, ?_⟩
  intro a U hU
  simp [initial, initialAt] at hU

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
    | none => inletCompensatingTransverseFlip a
        (cubicRelativePosition R.inletReferenceBase R.centralTarget)
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

/-- Even on a failed restart, the total runtime's default witness has the same geometric
box-in-layer certificate as a genuine mixed witness.  Consequently every later slot has a
uniform deterministic displacement bound, independently of success. -/
theorem selectedWitness_seedBoxWithinBoundaryLayer
    {d m n : ℕ} (hmn : 2 * m ≤ n)
    (R : LaterSiteRuntime d) (inletCenter : Cubic d)
    (incoming : CubicDirection d) (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (X : CubicEdge d → ℝ)
    (a : CubicDirection d) (k : ℕ) :
    SeedBoxWithinBoundaryLayer d a.1 m n
      (R.selectedWitness hmn inletCenter incoming firstFlip secondFlip
        p delta X a k).seedCenter.1 := by
  classical
  unfold selectedWitness SourceFiniteEdgeRevealState.selectedMixedWitness
    selectedMixedRestartSeedWitness
  split
  next hnonempty =>
    simp only [Option.getD_some]
    exact (mem_mixedRestartSeedWitnesses_iff.mp hnonempty.choose_spec).1.2.2.1
  next _hempty =>
    simp only [Option.getD_none]
    unfold defaultRestartSeedWitness
    dsimp only
    exact canonicalBoundarySeedBoxWithinBoundaryLayer a.1 hmn
      (canonicalRestartBoundaryPoint_mem_seededBoundaryQuadrant a.1)

/-- Physical target center selected at a slot. -/
noncomputable def selectedTarget {d m n : ℕ} (hmn : 2 * m ≤ n)
    (R : LaterSiteRuntime d) (inletCenter : Cubic d)
    (incoming : CubicDirection d) (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (X : CubicEdge d → ℝ)
    (a : CubicDirection d) (k : ℕ) : Cubic d :=
  cubicRestartFrameIso (R.slotCenterFor inletCenter a k) a
    (R.slotTransverseFlip incoming firstFlip secondFlip a k)
    (R.selectedWitness hmn inletCenter incoming firstFlip secondFlip p delta X a k).seedCenter.1

/-- A total selected target is at `L∞` distance at most `2(m+n+1)` from the slot center. -/
theorem selectedTarget_mem_centeredBox
    {d m n : ℕ} (hmn : 2 * m ≤ n)
    (R : LaterSiteRuntime d) (inletCenter : Cubic d)
    (incoming : CubicDirection d) (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (X : CubicEdge d → ℝ)
    (a : CubicDirection d) (k : ℕ) :
    R.selectedTarget hmn inletCenter incoming firstFlip secondFlip p delta X a k ∈
      cubicMetricBox d (R.slotCenterFor inletCenter a k) (2 * (m + n + 1)) := by
  let W := R.selectedWitness hmn inletCenter incoming firstFlip secondFlip p delta X a k
  have hcenterBox : W.seedCenter.1 ∈ cubicMetricBox d W.seedCenter.1 m := by
    rw [mem_cubicMetricBox]
    intro j
    omega
  have hcenterLayer : W.seedCenter.1 ∈ seededBoundaryLayerRegion d a.1 m n :=
    R.selectedWitness_seedBoxWithinBoundaryLayer hmn inletCenter incoming firstFlip
      secondFlip p delta X a k W.seedCenter.1 hcenterBox
  have hreference : W.seedCenter.1 ∈
      cubicMetricBox d cubicOrigin (2 * (m + n + 1)) :=
    positiveSeededRestartRegion_subset_doubleScaleBox d a.1 m n (Or.inr hcenterLayer)
  have hframed := (cubicRestartFrameIso_mem_cubicMetricBox_iff
    (R.slotCenterFor inletCenter a k) a
    (R.slotTransverseFlip incoming firstFlip secondFlip a k)
    cubicOrigin W.seedCenter.1).2 hreference
  simpa [selectedTarget, W] using hframed

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
  let inletDisplacement := cubicRelativePosition R.inletReferenceBase target
  let published : LaterSiteOutgoingSeed d :=
    ⟨target, inletDisplacement⟩
  { source := R.source.next (Q.restartSupport m n) p (incremented R.source a) X
    inletReferenceBase := R.inletReferenceBase
    firstTarget := if k = 0 then target else R.firstTarget
    firstReferenceTarget := if k = 0 then inletDisplacement else R.firstReferenceTarget
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
    let inletDisplacement := cubicRelativePosition R.inletReferenceBase target
    let published : LaterSiteOutgoingSeed d := ⟨target, inletDisplacement⟩
    { source := t.1.2
      inletReferenceBase := R.inletReferenceBase
      firstTarget := if k = 0 then target else R.firstTarget
      firstReferenceTarget := if k = 0 then inletDisplacement else R.firstReferenceTarget
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

/-- Literal finite union of all restart supports read by a total runtime.  Unlike a coarse
bounding box, this remembers the actual selected centers, signed frames, and chronological
source states. -/
noncomputable def restartSupportUnionFrom
    {d m n : ℕ} (hmn : 2 * m ≤ n)
    (inletCenter : Cubic d) (incoming : CubicDirection d)
    (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) : LaterSiteRuntime d → ℕ →
      List (CubicDirection d) → Finset (CubicEdge d)
  | _, _, [] => ∅
  | R, k, a :: rest =>
      (R.restartQuery inletCenter incoming firstFlip secondFlip a k).restartSupport m n ∪
        restartSupportUnionFrom hmn inletCenter incoming firstFlip secondFlip p delta
          incremented X
          (R.step hmn inletCenter incoming firstFlip secondFlip p delta incremented X a k)
          (k + 1) rest

/-- Exact support accounting for a total runtime: no edge can enter the explored state except
from the incoming explored set or one of the chronologically listed restart supports. -/
theorem runFrom_explored_subset_initial_union_restartSupportUnionFrom
    {d m n : ℕ} (hmn : 2 * m ≤ n)
    (inletCenter : Cubic d) (incoming : CubicDirection d)
    (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) (R : LaterSiteRuntime d) (offset : ℕ)
    (directions : List (CubicDirection d)) :
    (runFrom hmn inletCenter incoming firstFlip secondFlip p delta incremented X
      R offset directions).source.explored ⊆
      R.source.explored ∪
        restartSupportUnionFrom hmn inletCenter incoming firstFlip secondFlip p delta
          incremented X R offset directions := by
  induction directions generalizing R offset with
  | nil =>
      intro e he
      simpa [runFrom, restartSupportUnionFrom] using he
  | cons a rest ih =>
      let Q := R.restartQuery inletCenter incoming firstFlip secondFlip a offset
      let Rnext := R.step hmn inletCenter incoming firstFlip secondFlip
        p delta incremented X a offset
      have hnext : Rnext.source.explored ⊆ R.source.explored ∪ Q.restartSupport m n := by
        simpa [Rnext, step, Q] using
          R.source.nextExplored_subset_explored_union_stageRegion
            (Q.restartSupport m n) p (incremented R.source a) X
      have hrest := ih Rnext (offset + 1)
      intro e he
      have he' : e ∈ Rnext.source.explored ∪
          restartSupportUnionFrom hmn inletCenter incoming firstFlip secondFlip p delta
            incremented X Rnext (offset + 1) rest := by
        exact hrest (by simpa [runFrom, Rnext] using he)
      rcases Finset.mem_union.mp he' with heNext | heRest
      · rcases Finset.mem_union.mp (hnext heNext) with heOld | heLocal
        · exact Finset.mem_union_left _ heOld
        · exact Finset.mem_union_right _ <| Finset.mem_union_left _ heLocal
      · exact Finset.mem_union_right _ <| Finset.mem_union_right _ heRest

/-- Endpoint-set version of the exact runtime support accounting theorem. -/
theorem endpointVertices_runFrom_subset_initial_union_restartSupportUnionFrom
    {d m n : ℕ} (hmn : 2 * m ≤ n)
    (inletCenter : Cubic d) (incoming : CubicDirection d)
    (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) (R : LaterSiteRuntime d) (offset : ℕ)
    (directions : List (CubicDirection d)) :
    cubicEdgeEndpointVertices
        ((runFrom hmn inletCenter incoming firstFlip secondFlip p delta incremented X
          R offset directions).source.explored) ⊆
      cubicEdgeEndpointVertices R.source.explored ∪
        cubicEdgeEndpointVertices
          (restartSupportUnionFrom hmn inletCenter incoming firstFlip secondFlip p delta
            incremented X R offset directions) := by
  intro z hz
  obtain ⟨e, he, hze⟩ := mem_cubicEdgeEndpointVertices_iff.mp hz
  have heUnion := runFrom_explored_subset_initial_union_restartSupportUnionFrom hmn
    inletCenter incoming firstFlip secondFlip p delta incremented X R offset directions he
  rcases Finset.mem_union.mp heUnion with heInitial | heSupport
  · exact Finset.mem_union_left _ <|
      mem_cubicEdgeEndpointVertices_iff.mpr ⟨e, heInitial, hze⟩
  · exact Finset.mem_union_right _ <|
      mem_cubicEdgeEndpointVertices_iff.mpr ⟨e, heSupport, hze⟩

/-- Under a policy which spends at most `delta` per step, a finite runtime raises a uniform
lower-threshold bound by at most its number of restart applications. -/
theorem coe_runFrom_lower_le_add_length
    {d m n : ℕ} (hmn : 2 * m ≤ n)
    (inletCenter : Cubic d) (incoming : CubicDirection d)
    (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (hdelta : 0 ≤ delta)
    (incremented : RootExtensionThresholdPolicy d)
    (hpolicy : ∀ S a e,
      (incremented S a e : ℝ) ≤ (S.lower e : ℝ) + delta)
    (X : CubicEdge d → ℝ) (R : LaterSiteRuntime d) (offset : ℕ)
    (directions : List (CubicDirection d)) (B : ℝ)
    (hlower : ∀ e, (R.source.lower e : ℝ) ≤ B)
    (hp : (p : ℝ) ≤ B) (e : CubicEdge d) :
    ((runFrom hmn inletCenter incoming firstFlip secondFlip p delta incremented X
      R offset directions).source.lower e : ℝ) ≤
        B + (directions.length : ℝ) * delta := by
  induction directions generalizing R offset B with
  | nil => simpa using hlower e
  | cons a rest ih =>
      let Q := R.restartQuery inletCenter incoming firstFlip secondFlip a offset
      let R' := R.step hmn inletCenter incoming firstFlip secondFlip
        p delta incremented X a offset
      have hlower' : ∀ f, (R'.source.lower f : ℝ) ≤ B + delta := by
        intro f
        apply R.source.coe_next_lower_le_of_le
        · intro g
          exact (hlower g).trans (le_add_of_nonneg_right hdelta)
        · intro g
          exact (hpolicy R.source a g).trans (by linarith [hlower g])
        · exact hp.trans (le_add_of_nonneg_right hdelta)
      have hp' : (p : ℝ) ≤ B + delta :=
        hp.trans (le_add_of_nonneg_right hdelta)
      have hrest := ih R' (offset + 1) (B + delta) hlower' hp'
      change
        ((runFrom hmn inletCenter incoming firstFlip secondFlip p delta incremented X
          R' (offset + 1) rest).source.lower e : ℝ) ≤
            B + ((a :: rest).length : ℝ) * delta
      calc
        ((runFrom hmn inletCenter incoming firstFlip secondFlip p delta incremented X
          R' (offset + 1) rest).source.lower e : ℝ) ≤
            (B + delta) + (rest.length : ℝ) * delta := hrest
        _ = B + ((a :: rest).length : ℝ) * delta := by
          simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
          ring

/-- Pointwise version of the runtime threshold estimate.  This is the form needed for global
spatial accounting, because the number of earlier influencing coarse queries depends on the
endpoint of the particular edge being bounded. -/
theorem coe_runFrom_lower_le_add_length_at
    {d m n : ℕ} (hmn : 2 * m ≤ n)
    (inletCenter : Cubic d) (incoming : CubicDirection d)
    (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (hdelta : 0 ≤ delta)
    (incremented : RootExtensionThresholdPolicy d)
    (hpolicy : ∀ S a e,
      (incremented S a e : ℝ) ≤ (S.lower e : ℝ) + delta)
    (X : CubicEdge d → ℝ) (R : LaterSiteRuntime d) (offset : ℕ)
    (directions : List (CubicDirection d)) (B : ℝ)
    (e : CubicEdge d) (hlower : (R.source.lower e : ℝ) ≤ B)
    (hp : (p : ℝ) ≤ B) :
    ((runFrom hmn inletCenter incoming firstFlip secondFlip p delta incremented X
      R offset directions).source.lower e : ℝ) ≤
        B + (directions.length : ℝ) * delta := by
  induction directions generalizing R offset B with
  | nil => simpa using hlower
  | cons a rest ih =>
      let Q := R.restartQuery inletCenter incoming firstFlip secondFlip a offset
      let R' := R.step hmn inletCenter incoming firstFlip secondFlip
        p delta incremented X a offset
      have hlower' : (R'.source.lower e : ℝ) ≤ B + delta := by
        apply R.source.coe_next_lower_le_of_le_at
        · exact hlower.trans (le_add_of_nonneg_right hdelta)
        · exact (hpolicy R.source a e).trans (by linarith)
        · exact hp.trans (le_add_of_nonneg_right hdelta)
      have hp' : (p : ℝ) ≤ B + delta :=
        hp.trans (le_add_of_nonneg_right hdelta)
      have hrest := ih R' (offset + 1) (B + delta) hlower' hp'
      change
        ((runFrom hmn inletCenter incoming firstFlip secondFlip p delta incremented X
          R' (offset + 1) rest).source.lower e : ℝ) ≤
            B + ((a :: rest).length : ℝ) * delta
      calc
        ((runFrom hmn inletCenter incoming firstFlip secondFlip p delta incremented X
          R' (offset + 1) rest).source.lower e : ℝ) ≤
            (B + delta) + (rest.length : ℝ) * delta := hrest
        _ = B + ((a :: rest).length : ℝ) * delta := by
          simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
          ring

/-- Every literal restart support in a runtime schedule is confined to `A`.  This recursive
encoding follows the executable runtime exactly and avoids arithmetic on flattened pair-list
indices in later replay proofs. -/
def SupportsWithin {d m n : ℕ} (hmn : 2 * m ≤ n)
    (inletCenter : Cubic d) (incoming : CubicDirection d)
    (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) (A : Set (Cubic d)) : LaterSiteRuntime d → ℕ →
      List (CubicDirection d) → Prop
  | _, _, [] => True
  | R, k, a :: rest =>
      (cubicEdgeEndpointVertices
        ((R.restartQuery inletCenter incoming firstFlip secondFlip a k
          ).restartSupport m n) : Set (Cubic d)) ⊆ A ∧
        SupportsWithin hmn inletCenter incoming firstFlip secondFlip p delta incremented X A
          (R.step hmn inletCenter incoming firstFlip secondFlip
            p delta incremented X a k) (k + 1) rest

/-- If one endpoint of an edge lies outside a region containing every runtime support, the
runtime never changes that edge's lower threshold. -/
theorem runFrom_lower_eq_of_supportsWithin_of_endpoint_not_mem
    {d m n : ℕ} (hmn : 2 * m ≤ n)
    (inletCenter : Cubic d) (incoming : CubicDirection d)
    (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) (A : Set (Cubic d))
    (R : LaterSiteRuntime d) (offset : ℕ)
    (directions : List (CubicDirection d))
    (hwithin : SupportsWithin hmn inletCenter incoming firstFlip secondFlip
      p delta incremented X A R offset directions)
    (e : CubicEdge d) (hout : e.1.out.1 ∉ A) :
    (runFrom hmn inletCenter incoming firstFlip secondFlip p delta incremented X
      R offset directions).source.lower e = R.source.lower e := by
  induction directions generalizing R offset with
  | nil => rfl
  | cons a rest ih =>
      let Q := R.restartQuery inletCenter incoming firstFlip secondFlip a offset
      let R' := R.step hmn inletCenter incoming firstFlip secondFlip
        p delta incremented X a offset
      have heNotSupport : e ∉ Q.restartSupport m n := by
        intro he
        apply hout
        apply hwithin.1
        apply mem_cubicEdgeEndpointVertices_iff.mpr
        refine ⟨e, he, ?_⟩
        rw [← e.1.out_eq, Sym2.mem_iff]
        simp
      have hfirst : R'.source.lower e = R.source.lower e := by
        exact R.source.next_lower_eq_of_not_mem_stageRegion
          (Q.restartSupport m n) p (incremented R.source a) X heNotSupport
      have hrest := ih R' (offset + 1) hwithin.2
      change
        (runFrom hmn inletCenter incoming firstFlip secondFlip p delta incremented X
          R' (offset + 1) rest).source.lower e = R.source.lower e
      exact hrest.trans hfirst

/-- Literal support confinement is inherited by every prefix of a runtime schedule. -/
theorem supportsWithin_take
    {d m n : ℕ} (hmn : 2 * m ≤ n)
    (inletCenter : Cubic d) (incoming : CubicDirection d)
    (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) (A : Set (Cubic d))
    (R : LaterSiteRuntime d) (offset : ℕ)
    (directions : List (CubicDirection d))
    (hwithin : SupportsWithin hmn inletCenter incoming firstFlip secondFlip
      p delta incremented X A R offset directions) (k : ℕ) :
    SupportsWithin hmn inletCenter incoming firstFlip secondFlip
      p delta incremented X A R offset (directions.take k) := by
  induction directions generalizing R offset k with
  | nil =>
      simp only [List.take_nil]
      trivial
  | cons a rest ih =>
      cases k with
      | zero =>
          simp only [List.take_zero]
          trivial
      | succ k =>
          rw [List.take_succ_cons]
          exact ⟨hwithin.1, ih _ _ hwithin.2 k⟩

@[simp]
theorem supportsWithin_nil {d m n : ℕ} (hmn : 2 * m ≤ n)
    (inletCenter : Cubic d) (incoming : CubicDirection d)
    (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) (A : Set (Cubic d)) (R : LaterSiteRuntime d) (k : ℕ) :
    SupportsWithin hmn inletCenter incoming firstFlip secondFlip p delta incremented X A
      R k [] :=
  trivial

/-- Confinement along an appended schedule splits at the same intermediate runtime as
`runFrom_append`. -/
theorem supportsWithin_append {d m n : ℕ} (hmn : 2 * m ≤ n)
    (inletCenter : Cubic d) (incoming : CubicDirection d)
    (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) (A : Set (Cubic d))
    (R : LaterSiteRuntime d) (offset : ℕ)
    (first second : List (CubicDirection d)) :
    SupportsWithin hmn inletCenter incoming firstFlip secondFlip p delta incremented X A
        R offset (first ++ second) ↔
      SupportsWithin hmn inletCenter incoming firstFlip secondFlip p delta incremented X A
          R offset first ∧
        SupportsWithin hmn inletCenter incoming firstFlip secondFlip p delta incremented X A
          (runFrom hmn inletCenter incoming firstFlip secondFlip p delta incremented X
            R offset first) (offset + first.length) second := by
  induction first generalizing R offset with
  | nil =>
      have hrun : runFrom hmn inletCenter incoming firstFlip secondFlip p delta
          incremented X R offset [] = R := rfl
      simp only [List.nil_append, SupportsWithin, true_and, List.length_nil,
        Nat.add_zero, hrun]
  | cons a rest ih =>
      simp only [List.cons_append, SupportsWithin, runFrom]
      rw [ih]
      simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      tauto

/-- Recursive confinement supplies the pointwise prefix obligation used by the connectivity
replay theorem. -/
theorem SupportsWithin.getElem {d m n : ℕ} (hmn : 2 * m ≤ n)
    (inletCenter : Cubic d) (incoming : CubicDirection d)
    (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) (A : Set (Cubic d))
    (R : LaterSiteRuntime d) (offset : ℕ) (directions : List (CubicDirection d))
    (hwithin : SupportsWithin hmn inletCenter incoming firstFlip secondFlip
      p delta incremented X A R offset directions)
    (j : ℕ) (hj : j < directions.length) :
    let Rj := runFrom hmn inletCenter incoming firstFlip secondFlip
      p delta incremented X R offset (directions.take j)
    let a := directions[j]
    (cubicEdgeEndpointVertices
      ((Rj.restartQuery inletCenter incoming firstFlip secondFlip a (offset + j)
        ).restartSupport m n) : Set (Cubic d)) ⊆ A := by
  have hsplit : directions = directions.take j ++ directions.drop j :=
    (List.take_append_drop j directions).symm
  rw [hsplit, supportsWithin_append] at hwithin
  have htail := hwithin.2
  rw [List.drop_eq_getElem_cons hj] at htail
  have hlen : (directions.take j).length = j := List.length_take_of_le (Nat.le_of_lt hj)
  simpa [SupportsWithin, hlen] using htail.1

/-- Spatial support accounting for a complete runtime.  Every edge present after a confined
schedule was either already explored on entry, or all of its endpoints lie in the advertised
confinement region.  This is stronger than a mere final-threshold bound: it is the inductive
form needed to compare a later target seed with the literal geometry of every earlier coarse
query. -/
theorem explored_mem_initial_or_endpoints_mem_of_supportsWithin
    {d m n : ℕ} (hmn : 2 * m ≤ n)
    (inletCenter : Cubic d) (incoming : CubicDirection d)
    (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) (A : Set (Cubic d))
    (R : LaterSiteRuntime d) (offset : ℕ)
    (directions : List (CubicDirection d))
    (hwithin : SupportsWithin hmn inletCenter incoming firstFlip secondFlip
      p delta incremented X A R offset directions)
    {e : CubicEdge d}
    (he : e ∈ (runFrom hmn inletCenter incoming firstFlip secondFlip p delta
      incremented X R offset directions).source.explored) :
    e ∈ R.source.explored ∨ ∀ z ∈ (e : Sym2 (Cubic d)), z ∈ A := by
  induction directions generalizing R offset with
  | nil =>
      exact Or.inl he
  | cons a rest ih =>
      let Q := R.restartQuery inletCenter incoming firstFlip secondFlip a offset
      let Rnext := R.step hmn inletCenter incoming firstFlip secondFlip
        p delta incremented X a offset
      have hlocal :
          (cubicEdgeEndpointVertices (Q.restartSupport m n) : Set (Cubic d)) ⊆ A := by
        simpa [LaterSiteRuntime.SupportsWithin, Q] using hwithin.1
      have hrest : SupportsWithin hmn inletCenter incoming firstFlip secondFlip
          p delta incremented X A Rnext (offset + 1) rest := by
        simpa [LaterSiteRuntime.SupportsWithin, Q, Rnext] using hwithin.2
      have hfinal : e ∈
          (runFrom hmn inletCenter incoming firstFlip secondFlip p delta incremented X
            Rnext (offset + 1) rest).source.explored := by
        simpa [runFrom, Rnext] using he
      rcases ih Rnext (offset + 1) hrest hfinal with heNext | heA
      · have hallowed : e ∈ R.source.explored ∪ Q.restartSupport m n := by
          have hsubset := R.source.nextExplored_subset_explored_union_stageRegion
            (Q.restartSupport m n) p (incremented R.source a) X
          exact hsubset (by simpa [Rnext, step, Q] using heNext)
        rcases Finset.mem_union.mp hallowed with heOld | heSupport
        · exact Or.inl heOld
        · refine Or.inr ?_
          intro z hze
          exact hlocal <| mem_cubicEdgeEndpointVertices_iff.mpr
            ⟨e, heSupport, hze⟩
      · exact Or.inr heA

/-- Endpoint-set form of
`explored_mem_initial_or_endpoints_mem_of_supportsWithin`. -/
theorem endpointVertices_runFrom_subset_initial_union_of_supportsWithin
    {d m n : ℕ} (hmn : 2 * m ≤ n)
    (inletCenter : Cubic d) (incoming : CubicDirection d)
    (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) (A : Set (Cubic d))
    (R : LaterSiteRuntime d) (offset : ℕ)
    (directions : List (CubicDirection d))
    (hwithin : SupportsWithin hmn inletCenter incoming firstFlip secondFlip
      p delta incremented X A R offset directions) :
    (cubicEdgeEndpointVertices
        ((runFrom hmn inletCenter incoming firstFlip secondFlip p delta incremented X
          R offset directions).source.explored) : Set (Cubic d)) ⊆
      (cubicEdgeEndpointVertices R.source.explored : Set (Cubic d)) ∪ A := by
  intro z hz
  obtain ⟨e, he, hze⟩ := mem_cubicEdgeEndpointVertices_iff.mp hz
  rcases explored_mem_initial_or_endpoints_mem_of_supportsWithin hmn inletCenter incoming
      firstFlip secondFlip p delta incremented X A R offset directions hwithin he with
    heInitial | heA
  · exact Or.inl <| mem_cubicEdgeEndpointVertices_iff.mpr ⟨e, heInitial, hze⟩
  · exact Or.inr <| heA z hze

/-- With the destination coarse center stored in `initialAt`, the two inlet applications
recenter the incoming half-way seed inside the destination radius-`N` site box. -/
theorem centralTarget_runFrom_inletPair_initialAt_mem_destinationSiteBox
    {d m n : ℕ} (hmn : 2 * m ≤ n)
    (source : SourceFiniteEdgeRevealState d) (x inlet : Cubic d)
    (incoming : CubicDirection d) (firstFlip secondFlip : Fin d → Bool)
    (hfirst : firstFlip = inletCompensatingTransverseFlip incoming
      (cubicRelativePosition
        (grimmettMarstrandSiteCenter (m + n + 1) (cubicStepFrom x incoming)) inlet))
    (hinlet : inlet ∈ grimmettMarstrandHalfwayBox d (m + n + 1) x incoming)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) :
    (runFrom hmn inlet incoming firstFlip secondFlip p delta incremented X
      (initialAt source inlet
        (grimmettMarstrandSiteCenter (m + n + 1) (cubicStepFrom x incoming)))
      0 [incoming, incoming]).centralTarget ∈
        cubicMetricBox d
          (grimmettMarstrandSiteCenter (m + n + 1) (cubicStepFrom x incoming))
          (m + n + 1) := by
  let destination :=
    grimmettMarstrandSiteCenter (m + n + 1) (cubicStepFrom x incoming)
  let R0 := initialAt source inlet destination
  let c := (R0.selectedWitness hmn inlet incoming firstFlip secondFlip
    p delta X incoming 0).seedCenter.1
  let R1 := R0.step hmn inlet incoming firstFlip secondFlip
    p delta incremented X incoming 0
  let q := (R1.selectedWitness hmn inlet incoming firstFlip secondFlip
    p delta X incoming 1).seedCenter.1
  have hc : SeedBoxWithinBoundaryLayer d incoming.1 m n c := by
    exact R0.selectedWitness_seedBoxWithinBoundaryLayer hmn inlet incoming
      firstFlip secondFlip p delta X incoming 0
  have hq : SeedBoxWithinBoundaryLayer d incoming.1 m n q := by
    exact R1.selectedWitness_seedBoxWithinBoundaryLayer hmn inlet incoming
      firstFlip secondFlip p delta X incoming 1
  have hlocated := pairedInletCompensatingTarget_mem_destinationSiteBox
    (m := m) (n := n) hinlet hc hq
  simpa [runFrom, R0, R1, c, q, destination, initialAt, slotCenterFor,
    slotTransverseFlip, step, selectedTarget, hfirst] using hlocated

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

/-- Every restart step retains the deterministic coarse-site reference base. -/
@[simp]
theorem step_inletReferenceBase {d m n : ℕ} (hmn : 2 * m ≤ n)
    (R : LaterSiteRuntime d) (inletCenter : Cubic d)
    (incoming : CubicDirection d) (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) (a : CubicDirection d) (k : ℕ) :
    (R.step hmn inletCenter incoming firstFlip secondFlip p delta incremented X a k
      ).inletReferenceBase = R.inletReferenceBase := by
  simp [step]

/-- A complete runtime retains the deterministic coarse-site reference base. -/
theorem runFrom_inletReferenceBase {d m n : ℕ} (hmn : 2 * m ≤ n)
    (inletCenter : Cubic d) (incoming : CubicDirection d)
    (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) (R : LaterSiteRuntime d) (k : ℕ)
    (directions : List (CubicDirection d)) :
    (runFrom hmn inletCenter incoming firstFlip secondFlip p delta incremented X
      R k directions).inletReferenceBase = R.inletReferenceBase := by
  induction directions generalizing R k with
  | nil => rfl
  | cons a rest ih =>
      simp only [runFrom]
      rw [ih]
      exact step_inletReferenceBase hmn R inletCenter incoming firstFlip secondFlip
        p delta incremented X a k

/-- Once the two inlet slots have been consumed, later branch restarts do not move the central
seed selected for the coarse site. -/
theorem step_centralTarget_of_two_le {d m n : ℕ} (hmn : 2 * m ≤ n)
    (R : LaterSiteRuntime d) (inletCenter : Cubic d)
    (incoming : CubicDirection d) (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) (a : CubicDirection d) (k : ℕ) (hk : 2 ≤ k) :
    (R.step hmn inletCenter incoming firstFlip secondFlip p delta incremented X a k
      ).centralTarget = R.centralTarget := by
  have hk1 : k ≠ 1 := by omega
  simp [step, hk1]

/-- A branch-only suffix beginning at slot two preserves the central coarse-site seed. -/
theorem runFrom_centralTarget_of_two_le {d m n : ℕ} (hmn : 2 * m ≤ n)
    (inletCenter : Cubic d) (incoming : CubicDirection d)
    (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) (R : LaterSiteRuntime d) (k : ℕ)
    (directions : List (CubicDirection d)) (hk : 2 ≤ k) :
    (runFrom hmn inletCenter incoming firstFlip secondFlip p delta incremented X
      R k directions).centralTarget = R.centralTarget := by
  induction directions generalizing R k with
  | nil => rfl
  | cons a rest ih =>
      simp only [runFrom]
      rw [ih (R := R.step hmn inletCenter incoming firstFlip secondFlip p delta
        incremented X a k) (k := k + 1) (by omega)]
      exact step_centralTarget_of_two_le hmn R inletCenter incoming firstFlip secondFlip
        p delta incremented X a k hk

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
      cubicRelativePosition R1.inletReferenceBase
        (cubicRestartFrameIso (R1.slotCenterFor inletCenter a (k + 1)) a
          (R1.slotTransverseFlip incoming firstFlip secondFlip a (k + 1))
          W.seedCenter.1)⟩
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
selected by the first application, measured from the deterministic center of the publishing
coarse site. -/
theorem slotTransverseFlip_step_same_succ_of_two_le
    {d m n : ℕ} (hmn : 2 * m ≤ n)
    (R : LaterSiteRuntime d) (inletCenter : Cubic d)
    (incoming : CubicDirection d) (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) (a : CubicDirection d) (k : ℕ) (hk : 2 ≤ k) :
    (R.step hmn inletCenter incoming firstFlip secondFlip p delta incremented X a k
      ).slotTransverseFlip incoming firstFlip secondFlip a (k + 1) =
      inletCompensatingTransverseFlip a
        (cubicRelativePosition R.inletReferenceBase
          (R.selectedTarget hmn inletCenter incoming firstFlip secondFlip
            p delta X a k)) := by
  have hk0 : k + 1 ≠ 0 := by omega
  have hk1 : k + 1 ≠ 1 := by omega
  have hkBase0 : k ≠ 0 := by omega
  have hkBase1 : k ≠ 1 := by omega
  simp [slotTransverseFlip, step, selectedTarget, hk, hk0, hk1, hkBase0, hkBase1]

/-- The support read by the first inlet application is fresh for the target of the immediately
following application.  This is the runtime wrapper around the same-direction recentering
lemma; it does not assume that either restart succeeds. -/
theorem firstInletRestartSupport_targetFresh_for_second
    {d m n : ℕ} (hmn : 2 * m ≤ n) (hmnStrict : m + 1 < n)
    (R : LaterSiteRuntime d) (inletCenter : Cubic d)
    (incoming : CubicDirection d) (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) :
    let Rnext := R.step hmn inletCenter incoming firstFlip secondFlip
      p delta incremented X incoming 0
    let Fnext := cubicRestartFrameIso
      (Rnext.slotCenterFor inletCenter incoming 1) incoming
      (Rnext.slotTransverseFlip incoming firstFlip secondFlip incoming 1)
    Disjoint
      (cubicEdgeEndpointVertices
        ((R.restartQuery inletCenter incoming firstFlip secondFlip incoming 0
          ).restartSupport m n |>.image Fnext.symm.mapEdgeSet))
      (cubicEdgeEndpointVertices (seededBoundaryTargetSupport d incoming.1 m n)) := by
  dsimp only
  let c := (R.selectedWitness hmn inletCenter incoming firstFlip secondFlip
    p delta X incoming 0).seedCenter.1
  have hc := R.selectedWitness_seedBoxWithinBoundaryLayer hmn inletCenter incoming
    firstFlip secondFlip p delta X incoming 0
  have hcenter := R.slotCenterFor_step_zero_one hmn inletCenter incoming firstFlip
    secondFlip p delta incremented X incoming
  simpa [restartQuery, SourceFiniteEdgeRevealState.framedQuery, selectedTarget, c,
    hcenter] using
    framedRestartSupport_compensatingFrame_targetEndpointFresh hmnStrict
      (R.slotCenterFor inletCenter incoming 0) c incoming
      (R.slotTransverseFlip incoming firstFlip secondFlip incoming 0)
      ((R.step hmn inletCenter incoming firstFlip secondFlip
        p delta incremented X incoming 0).slotTransverseFlip
          incoming firstFlip secondFlip incoming 1)
      hc
      (cubicEdgeEndpointVertices (R.source.referenceExploredEdges
        (cubicRestartFrameIso (R.slotCenterFor inletCenter incoming 0) incoming
          (R.slotTransverseFlip incoming firstFlip secondFlip incoming 0))))

/-- For every outgoing duplicate pair, the first branch support is fresh for the second
link-up target. -/
theorem outgoingRestartSupport_targetFresh_for_link
    {d m n : ℕ} (hmn : 2 * m ≤ n) (hmnStrict : m + 1 < n)
    (R : LaterSiteRuntime d) (inletCenter : Cubic d)
    (incoming : CubicDirection d) (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) (a : CubicDirection d) (k : ℕ) (hk : 2 ≤ k) :
    let Rnext := R.step hmn inletCenter incoming firstFlip secondFlip
      p delta incremented X a k
    let Fnext := cubicRestartFrameIso
      (Rnext.slotCenterFor inletCenter a (k + 1)) a
      (Rnext.slotTransverseFlip incoming firstFlip secondFlip a (k + 1))
    Disjoint
      (cubicEdgeEndpointVertices
        ((R.restartQuery inletCenter incoming firstFlip secondFlip a k
          ).restartSupport m n |>.image Fnext.symm.mapEdgeSet))
      (cubicEdgeEndpointVertices (seededBoundaryTargetSupport d a.1 m n)) := by
  dsimp only
  let c := (R.selectedWitness hmn inletCenter incoming firstFlip secondFlip
    p delta X a k).seedCenter.1
  have hc := R.selectedWitness_seedBoxWithinBoundaryLayer hmn inletCenter incoming
    firstFlip secondFlip p delta X a k
  have hcenter := R.slotCenterFor_step_same_succ_of_two_le hmn inletCenter incoming
    firstFlip secondFlip p delta incremented X a k hk
  simpa [restartQuery, SourceFiniteEdgeRevealState.framedQuery, selectedTarget, c,
    hcenter] using
    framedRestartSupport_compensatingFrame_targetEndpointFresh hmnStrict
      (R.slotCenterFor inletCenter a k) c a
      (R.slotTransverseFlip incoming firstFlip secondFlip a k)
      ((R.step hmn inletCenter incoming firstFlip secondFlip
        p delta incremented X a k).slotTransverseFlip
          incoming firstFlip secondFlip a (k + 1))
      hc
      (cubicEdgeEndpointVertices (R.source.referenceExploredEdges
        (cubicRestartFrameIso (R.slotCenterFor inletCenter a k) a
          (R.slotTransverseFlip incoming firstFlip secondFlip a k))))

/-- The second inlet query is fresh after the first update whenever the incoming explored state
is already fresh in the second query's frame.  The new part is discharged unconditionally by
`firstInletRestartSupport_targetFresh_for_second`. -/
theorem targetFresh_step_firstInlet_for_second_of_priorFresh
    {d m n : ℕ} (hmn : 2 * m ≤ n) (hmnStrict : m + 1 < n)
    (R : LaterSiteRuntime d) (inletCenter : Cubic d)
    (incoming : CubicDirection d) (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ)
    (hOld :
      let Rnext := R.step hmn inletCenter incoming firstFlip secondFlip
        p delta incremented X incoming 0
      let Fnext := cubicRestartFrameIso
        (Rnext.slotCenterFor inletCenter incoming 1) incoming
        (Rnext.slotTransverseFlip incoming firstFlip secondFlip incoming 1)
      Disjoint (cubicEdgeEndpointVertices (R.source.referenceExploredEdges Fnext))
        (cubicEdgeEndpointVertices (seededBoundaryTargetSupport d incoming.1 m n))) :
    let Rnext := R.step hmn inletCenter incoming firstFlip secondFlip
      p delta incremented X incoming 0
    let Fnext := cubicRestartFrameIso
      (Rnext.slotCenterFor inletCenter incoming 1) incoming
      (Rnext.slotTransverseFlip incoming firstFlip secondFlip incoming 1)
    Disjoint (cubicEdgeEndpointVertices (Rnext.source.referenceExploredEdges Fnext))
      (cubicEdgeEndpointVertices (seededBoundaryTargetSupport d incoming.1 m n)) := by
  dsimp only at hOld ⊢
  let Rnext := R.step hmn inletCenter incoming firstFlip secondFlip
    p delta incremented X incoming 0
  let Fnext := cubicRestartFrameIso
    (Rnext.slotCenterFor inletCenter incoming 1) incoming
    (Rnext.slotTransverseFlip incoming firstFlip secondFlip incoming 1)
  have hStage := R.firstInletRestartSupport_targetFresh_for_second
    hmn hmnStrict inletCenter incoming firstFlip secondFlip p delta incremented X
  simpa [Rnext, step, restartQuery] using
    R.source.targetEndpointFresh_next_of_old_and_stage
      ((R.restartQuery inletCenter incoming firstFlip secondFlip incoming 0
        ).restartSupport m n)
      p (incremented R.source incoming) X Fnext
      (seededBoundaryTargetSupport d incoming.1 m n) hOld hStage

/-- Link-up freshness for an outgoing duplicate pair reduces entirely to freshness of the
incoming explored state in the link-up frame. -/
theorem targetFresh_step_outgoing_for_link_of_priorFresh
    {d m n : ℕ} (hmn : 2 * m ≤ n) (hmnStrict : m + 1 < n)
    (R : LaterSiteRuntime d) (inletCenter : Cubic d)
    (incoming : CubicDirection d) (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) (a : CubicDirection d) (k : ℕ) (hk : 2 ≤ k)
    (hOld :
      let Rnext := R.step hmn inletCenter incoming firstFlip secondFlip
        p delta incremented X a k
      let Fnext := cubicRestartFrameIso
        (Rnext.slotCenterFor inletCenter a (k + 1)) a
        (Rnext.slotTransverseFlip incoming firstFlip secondFlip a (k + 1))
      Disjoint (cubicEdgeEndpointVertices (R.source.referenceExploredEdges Fnext))
        (cubicEdgeEndpointVertices (seededBoundaryTargetSupport d a.1 m n))) :
    let Rnext := R.step hmn inletCenter incoming firstFlip secondFlip
      p delta incremented X a k
    let Fnext := cubicRestartFrameIso
      (Rnext.slotCenterFor inletCenter a (k + 1)) a
      (Rnext.slotTransverseFlip incoming firstFlip secondFlip a (k + 1))
    Disjoint (cubicEdgeEndpointVertices (Rnext.source.referenceExploredEdges Fnext))
      (cubicEdgeEndpointVertices (seededBoundaryTargetSupport d a.1 m n)) := by
  dsimp only at hOld ⊢
  let Rnext := R.step hmn inletCenter incoming firstFlip secondFlip
    p delta incremented X a k
  let Fnext := cubicRestartFrameIso
    (Rnext.slotCenterFor inletCenter a (k + 1)) a
    (Rnext.slotTransverseFlip incoming firstFlip secondFlip a (k + 1))
  have hStage := R.outgoingRestartSupport_targetFresh_for_link
    hmn hmnStrict inletCenter incoming firstFlip secondFlip p delta incremented X a k hk
  simpa [Rnext, step, restartQuery] using
    R.source.targetEndpointFresh_next_of_old_and_stage
      ((R.restartQuery inletCenter incoming firstFlip secondFlip a k).restartSupport m n)
      p (incremented R.source a) X Fnext
      (seededBoundaryTargetSupport d a.1 m n) hOld hStage

/-- Before the coarse-site location invariant is imposed, the link-up query still has the
uniform deterministic centered-box bound supplied by its literal signed frame. -/
theorem endpointVertices_restartQuery_step_same_succ_subset_endpointBoxes
    {d m n : ℕ} (hm : 1 ≤ m) (hmn : 2 * m ≤ n)
    (R : LaterSiteRuntime d) (inletCenter : Cubic d)
    (incoming : CubicDirection d) (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) (a : CubicDirection d) (k : ℕ) (hk : 2 ≤ k) :
    let Rnext := R.step hmn inletCenter incoming firstFlip secondFlip
      p delta incremented X a k
    (cubicEdgeEndpointVertices
        ((Rnext.restartQuery inletCenter incoming firstFlip secondFlip a (k + 1)
          ).restartSupport m n) : Set (Cubic d)) ⊆
      cubicMetricBox d
        (Rnext.slotCenterFor inletCenter a (k + 1)) (2 * (m + n + 1)) := by
  dsimp only
  let Rnext := R.step hmn inletCenter incoming firstFlip secondFlip
    p delta incremented X a k
  let Qnext := Rnext.restartQuery inletCenter incoming firstFlip secondFlip a (k + 1)
  simpa [Qnext, Rnext, restartQuery, SourceFiniteEdgeRevealState.framedQuery] using
    Qnext.endpointVertices_restartSupport_subset_centeredBox (m := m) (n := n)

/-- The second inlet query obeys the same two-endpoint containment, with the literal inlet
center as the base of the first signed frame. -/
theorem endpointVertices_secondInletQuery_subset_endpointBoxes
    {d m n : ℕ} (hm : 1 ≤ m) (hmn : 2 * m ≤ n)
    (R : LaterSiteRuntime d) (inletCenter : Cubic d)
    (hbase : R.inletReferenceBase = inletCenter)
    (incoming : CubicDirection d) (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) :
    let Rnext := R.step hmn inletCenter incoming firstFlip secondFlip
      p delta incremented X incoming 0
    (cubicEdgeEndpointVertices
        ((Rnext.restartQuery inletCenter incoming firstFlip secondFlip incoming 1
          ).restartSupport m n) : Set (Cubic d)) ⊆
      (cubicMetricBox d inletCenter (2 * (m + n + 1)) : Set (Cubic d)) ∪
        (cubicMetricBox d
          (cubicRestartFrameIso inletCenter incoming firstFlip
            (grimmettMarstrandSiteCenter (m + n + 1)
              (cubicStepFrom cubicOrigin (incoming.1, true))))
          (2 * (m + n + 1)) : Set (Cubic d)) := by
  dsimp only
  intro z hz
  let Rnext := R.step hmn inletCenter incoming firstFlip secondFlip
    p delta incremented X incoming 0
  let Qnext := Rnext.restartQuery inletCenter incoming firstFlip secondFlip incoming 1
  have hzRegion := Qnext.endpointVertices_restartSupport_subset_frameRegion hz
  have hcenter := R.slotCenterFor_step_zero_one hmn inletCenter incoming
    firstFlip secondFlip p delta incremented X incoming
  have hgeom := R.selectedWitness_seedBoxWithinBoundaryLayer hmn inletCenter incoming
    firstFlip secondFlip p delta X incoming 0
  apply pairedRestartRegion_subset_endpointBoxes_of_geometry inletCenter
    (R.selectedWitness hmn inletCenter incoming firstFlip secondFlip
      p delta X incoming 0).seedCenter.1 incoming firstFlip hm hgeom
  simpa [Qnext, Rnext, restartQuery, SourceFiniteEdgeRevealState.framedQuery,
    hcenter, step, selectedTarget, slotTransverseFlip, slotCenterFor, hbase] using hzRegion

/-- After the first inlet restart, its selected face seed lies in the directional corridor
from the parent coarse site to the queried child. -/
theorem selectedTarget_zero_directionalBounds_of_inletHalfway
    {d m n : ℕ} (hmn : 2 * m ≤ n)
    (R : LaterSiteRuntime d) (x inletCenter : Cubic d)
    (incoming : CubicDirection d) (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (X : CubicEdge d → ℝ)
    (hinlet : inletCenter ∈
      grimmettMarstrandHalfwayBox d (m + n + 1) x incoming)
    (hfirst : firstFlip = inletCompensatingTransverseFlip incoming
      (cubicRelativePosition
        (grimmettMarstrandSiteCenter (m + n + 1) (cubicStepFrom x incoming))
        inletCenter)) :
    (if incoming.2 then
        grimmettMarstrandSiteCenter (m + n + 1) x incoming.1 - (m + n + 1 : ℕ) ≤
            R.selectedTarget hmn inletCenter incoming firstFlip secondFlip
              p delta X incoming 0 incoming.1 ∧
          R.selectedTarget hmn inletCenter incoming firstFlip secondFlip
              p delta X incoming 0 incoming.1 ≤
            grimmettMarstrandSiteCenter (m + n + 1) x incoming.1 +
              4 * (m + n + 1 : ℕ)
      else
        grimmettMarstrandSiteCenter (m + n + 1) x incoming.1 -
              4 * (m + n + 1 : ℕ) ≤
            R.selectedTarget hmn inletCenter incoming firstFlip secondFlip
              p delta X incoming 0 incoming.1 ∧
          R.selectedTarget hmn inletCenter incoming firstFlip secondFlip
              p delta X incoming 0 incoming.1 ≤
            grimmettMarstrandSiteCenter (m + n + 1) x incoming.1 +
              (m + n + 1 : ℕ)) ∧
      (∀ j, j ≠ incoming.1 →
        grimmettMarstrandSiteCenter (m + n + 1) x j - (m + n + 1 : ℕ) ≤
            R.selectedTarget hmn inletCenter incoming firstFlip secondFlip
              p delta X incoming 0 j ∧
          R.selectedTarget hmn inletCenter incoming firstFlip secondFlip
              p delta X incoming 0 j ≤
            grimmettMarstrandSiteCenter (m + n + 1) x j + (m + n + 1 : ℕ)) := by
  let first := inletCompensatingTransverseFlip incoming
    (cubicRelativePosition
      (grimmettMarstrandSiteCenter (m + n + 1) (cubicStepFrom x incoming)) inletCenter)
  have hfirst' : firstFlip = first := by simpa [first] using hfirst
  rw [hfirst']
  let c := (R.selectedWitness hmn inletCenter incoming first secondFlip
    p delta X incoming 0).seedCenter.1
  have hc : SeedBoxWithinBoundaryLayer d incoming.1 m n c := by
    exact R.selectedWitness_seedBoxWithinBoundaryLayer hmn inletCenter incoming first
      secondFlip p delta X incoming 0
  constructor
  · have hcAxis := seedCenter_axis_eq_of_boxWithinBoundaryLayer incoming.1 hc
    have hinletAxis := mem_cubicMetricBox.mp hinlet incoming.1
    rcases incoming with ⟨i, positive⟩
    have hcAxis' :
        (R.selectedWitness hmn inletCenter (i, positive) first secondFlip
          p delta X (i, positive) 0).seedCenter.1 i = (n + m + 1 : ℕ) := by
      simpa [c] using hcAxis
    cases positive <;>
      simp [selectedTarget, slotCenterFor, slotTransverseFlip,
        cubicRestartFrameIso_apply, cubicRestartFrameFlip,
        grimmettMarstrandHalfwayBox, grimmettMarstrandBondBox,
        grimmettMarstrandBondCenter, grimmettMarstrandSiteCenter, cubicScale,
        cubicStepFrom, cubicDirectionIncrement, hcAxis'] at hinletAxis ⊢ <;>
      ring_nf at hinletAxis ⊢ <;> omega
  · intro j hja
    have hinletj := mem_cubicMetricBox.mp hinlet j
    have hinletDestination :
        grimmettMarstrandSiteCenter (m + n + 1) (cubicStepFrom x incoming) j -
              (m + n + 1 : ℕ) ≤ inletCenter j ∧
          inletCenter j ≤
            grimmettMarstrandSiteCenter (m + n + 1) (cubicStepFrom x incoming) j +
              (m + n + 1 : ℕ) := by
      rcases incoming with ⟨i, positive⟩
      have hji : j ≠ i := hja
      cases positive <;>
        simp [grimmettMarstrandHalfwayBox, grimmettMarstrandBondBox,
          grimmettMarstrandBondCenter, grimmettMarstrandSiteCenter, cubicScale,
          cubicStepFrom, cubicDirectionIncrement, hji] at hinletj ⊢ <;>
        ring_nf at hinletj ⊢ <;> exact hinletj
    have hj := inletCompensatingTarget_transverse_bounds_of_bounds
      hinletDestination hc hja
    rcases incoming with ⟨i, positive⟩
    have hji : j ≠ i := hja
    simpa [selectedTarget, slotCenterFor, slotTransverseFlip, first,
      grimmettMarstrandSiteCenter, cubicScale, cubicStepFrom,
      cubicDirectionIncrement, hji] using hj

/-- The second inlet restart also remains inside the two enlarged endpoint boxes of the
parent-child coarse bond. -/
theorem endpointVertices_secondInletQuery_subset_endpointBoxes_of_coarseLocated
    {d m n : ℕ} (hmn : 2 * m ≤ n)
    (R : LaterSiteRuntime d) (x inletCenter : Cubic d)
    (incoming : CubicDirection d) (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ)
    (hinlet : inletCenter ∈
      grimmettMarstrandHalfwayBox d (m + n + 1) x incoming)
    (hfirst : firstFlip = inletCompensatingTransverseFlip incoming
      (cubicRelativePosition
        (grimmettMarstrandSiteCenter (m + n + 1) (cubicStepFrom x incoming))
        inletCenter)) :
    let R1 := R.step hmn inletCenter incoming firstFlip secondFlip
      p delta incremented X incoming 0
    (cubicEdgeEndpointVertices
        ((R1.restartQuery inletCenter incoming firstFlip secondFlip incoming 1
          ).restartSupport m n) : Set (Cubic d)) ⊆
      (cubicMetricBox d (grimmettMarstrandSiteCenter (m + n + 1) x)
          (2 * (m + n + 1)) : Set (Cubic d)) ∪
        (cubicMetricBox d
          (grimmettMarstrandSiteCenter (m + n + 1) (cubicStepFrom x incoming))
          (2 * (m + n + 1)) : Set (Cubic d)) := by
  dsimp only
  let R1 := R.step hmn inletCenter incoming firstFlip secondFlip
    p delta incremented X incoming 0
  have hcenter := R.slotCenterFor_step_zero_one hmn inletCenter incoming firstFlip
    secondFlip p delta incremented X incoming
  have hb := R.selectedTarget_zero_directionalBounds_of_inletHalfway hmn x inletCenter
    incoming firstFlip secondFlip p delta X hinlet hfirst
  simpa [restartQuery, SourceFiniteEdgeRevealState.framedQuery, R1, hcenter] using
    cubicEdgeEndpointVertices_framedRestartSupport_subset_endpointBoxes_of_directionalBounds
      (m := m) (n := n)
      (R.selectedTarget hmn inletCenter incoming firstFlip secondFlip
        p delta X incoming 0) incoming
      (R1.slotTransverseFlip incoming firstFlip secondFlip incoming 1)
      (cubicEdgeEndpointVertices (R1.source.referenceExploredEdges
        (cubicRestartFrameIso
          (R.selectedTarget hmn inletCenter incoming firstFlip secondFlip
            p delta X incoming 0) incoming
          (R1.slotTransverseFlip incoming firstFlip secondFlip incoming 1)))) x hb.1 hb.2

/-- The two inlet restarts are confined to `A` whenever the enlarged boxes of the parent and
queried child lie in `A`. -/
theorem supportsWithin_inletPair_of_coarseLocated
    {d m n : ℕ} (hmn : 2 * m ≤ n)
    (R : LaterSiteRuntime d) (x inletCenter : Cubic d)
    (incoming : CubicDirection d) (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) (A : Set (Cubic d))
    (hinlet : inletCenter ∈
      grimmettMarstrandHalfwayBox d (m + n + 1) x incoming)
    (hfirst : firstFlip = inletCompensatingTransverseFlip incoming
      (cubicRelativePosition
        (grimmettMarstrandSiteCenter (m + n + 1) (cubicStepFrom x incoming))
        inletCenter))
    (hboxes :
      (cubicMetricBox d (grimmettMarstrandSiteCenter (m + n + 1) x)
          (2 * (m + n + 1)) : Set (Cubic d)) ∪
        (cubicMetricBox d
          (grimmettMarstrandSiteCenter (m + n + 1) (cubicStepFrom x incoming))
          (2 * (m + n + 1)) : Set (Cubic d)) ⊆ A) :
    SupportsWithin hmn inletCenter incoming firstFlip secondFlip p delta incremented X A
      R 0 [incoming, incoming] := by
  have hfirstSupport :
      (cubicEdgeEndpointVertices
        ((R.restartQuery inletCenter incoming firstFlip secondFlip incoming 0
          ).restartSupport m n) : Set (Cubic d)) ⊆
        (cubicMetricBox d (grimmettMarstrandSiteCenter (m + n + 1) x)
            (2 * (m + n + 1)) : Set (Cubic d)) ∪
          (cubicMetricBox d
            (grimmettMarstrandSiteCenter (m + n + 1) (cubicStepFrom x incoming))
            (2 * (m + n + 1)) : Set (Cubic d)) := by
    simpa [restartQuery, SourceFiniteEdgeRevealState.framedQuery, slotCenterFor,
      slotTransverseFlip] using
      cubicEdgeEndpointVertices_framedRestartSupport_subset_endpointBoxes_of_center_mem_halfwayBox
        (m := m) (n := n) inletCenter incoming firstFlip
          (cubicEdgeEndpointVertices (R.source.referenceExploredEdges
            (cubicRestartFrameIso inletCenter incoming firstFlip))) x hinlet
  have hsecondSupport :=
    R.endpointVertices_secondInletQuery_subset_endpointBoxes_of_coarseLocated hmn x
      inletCenter incoming firstFlip secondFlip p delta incremented X hinlet hfirst
  change _ ∧ _ ∧ True
  exact ⟨hfirstSupport.trans hboxes, hsecondSupport.trans hboxes, trivial⟩

/-- The first member of a fresh outgoing pair starts at the central seed and reads only the
two enlarged boxes of the advertised coarse bond. -/
theorem endpointVertices_outgoingQuery_subset_endpointBoxes_of_coarseLocated
    {d m n : ℕ} (hmn : 2 * m ≤ n)
    (R : LaterSiteRuntime d) (x inletCenter : Cubic d)
    (incoming : CubicDirection d) (firstFlip secondFlip : Fin d → Bool)
    (a : CubicDirection d) (k : ℕ) (hk : 2 ≤ k)
    (hcentral : R.centralTarget ∈
      cubicMetricBox d (grimmettMarstrandSiteCenter (m + n + 1) x) (m + n + 1))
    (hnone : R.outgoing a = none) :
    (cubicEdgeEndpointVertices
        ((R.restartQuery inletCenter incoming firstFlip secondFlip a k
          ).restartSupport m n) : Set (Cubic d)) ⊆
      (cubicMetricBox d (grimmettMarstrandSiteCenter (m + n + 1) x)
          (2 * (m + n + 1)) : Set (Cubic d)) ∪
        (cubicMetricBox d
          (grimmettMarstrandSiteCenter (m + n + 1) (cubicStepFrom x a))
          (2 * (m + n + 1)) : Set (Cubic d)) := by
  have hk0 : k ≠ 0 := by omega
  have hk1 : k ≠ 1 := by omega
  have hcenter : R.slotCenterFor inletCenter a k = R.centralTarget := by
    simp [slotCenterFor, hk0, hk1, hnone]
  simpa [restartQuery, SourceFiniteEdgeRevealState.framedQuery, hcenter] using
    cubicEdgeEndpointVertices_framedRestartSupport_subset_endpointBoxes_of_center_mem_siteBox
      (m := m) (n := n) R.centralTarget x a
        (R.slotTransverseFlip incoming firstFlip secondFlip a k)
        (cubicEdgeEndpointVertices (R.source.referenceExploredEdges
          (cubicRestartFrameIso R.centralTarget a
            (R.slotTransverseFlip incoming firstFlip secondFlip a k)))) hcentral

/-- The provisional face seed selected by the first member of a fresh outgoing pair lies in
the directional corridor from the publishing site to its signed neighbor. -/
theorem selectedTarget_directionalBounds_of_coarseLocated
    {d m n : ℕ} (hmn : 2 * m ≤ n)
    (R : LaterSiteRuntime d) (x inletCenter : Cubic d)
    (incoming : CubicDirection d) (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (X : CubicEdge d → ℝ)
    (a : CubicDirection d) (k : ℕ) (hk : 2 ≤ k)
    (hbase : R.inletReferenceBase = grimmettMarstrandSiteCenter (m + n + 1) x)
    (hcentral : R.centralTarget ∈
      cubicMetricBox d (grimmettMarstrandSiteCenter (m + n + 1) x) (m + n + 1))
    (hnone : R.outgoing a = none) :
    (if a.2 then
        grimmettMarstrandSiteCenter (m + n + 1) x a.1 - (m + n + 1 : ℕ) ≤
            R.selectedTarget hmn inletCenter incoming firstFlip secondFlip
              p delta X a k a.1 ∧
          R.selectedTarget hmn inletCenter incoming firstFlip secondFlip
              p delta X a k a.1 ≤
            grimmettMarstrandSiteCenter (m + n + 1) x a.1 +
              4 * (m + n + 1 : ℕ)
      else
        grimmettMarstrandSiteCenter (m + n + 1) x a.1 -
              4 * (m + n + 1 : ℕ) ≤
            R.selectedTarget hmn inletCenter incoming firstFlip secondFlip
              p delta X a k a.1 ∧
          R.selectedTarget hmn inletCenter incoming firstFlip secondFlip
              p delta X a k a.1 ≤
            grimmettMarstrandSiteCenter (m + n + 1) x a.1 + (m + n + 1 : ℕ)) ∧
      (∀ j, j ≠ a.1 →
        grimmettMarstrandSiteCenter (m + n + 1) x j - (m + n + 1 : ℕ) ≤
            R.selectedTarget hmn inletCenter incoming firstFlip secondFlip
              p delta X a k j ∧
          R.selectedTarget hmn inletCenter incoming firstFlip secondFlip
              p delta X a k j ≤
            grimmettMarstrandSiteCenter (m + n + 1) x j + (m + n + 1 : ℕ)) := by
  let c := (R.selectedWitness hmn inletCenter incoming firstFlip secondFlip
    p delta X a k).seedCenter.1
  have hc : SeedBoxWithinBoundaryLayer d a.1 m n c := by
    exact R.selectedWitness_seedBoxWithinBoundaryLayer hmn inletCenter incoming firstFlip
      secondFlip p delta X a k
  have hk0 : k ≠ 0 := by omega
  have hk1 : k ≠ 1 := by omega
  have hcenter : R.slotCenterFor inletCenter a k = R.centralTarget := by
    simp [slotCenterFor, hk0, hk1, hnone]
  have hflip : R.slotTransverseFlip incoming firstFlip secondFlip a k =
      inletCompensatingTransverseFlip a
        (cubicRelativePosition (grimmettMarstrandSiteCenter (m + n + 1) x)
          R.centralTarget) := by
    simp [slotTransverseFlip, hk0, hk1, hnone, hbase]
  constructor
  · have hcAxis := seedCenter_axis_eq_of_boxWithinBoundaryLayer a.1 hc
    have hcentralAxis := mem_cubicMetricBox.mp hcentral a.1
    rcases a with ⟨i, positive⟩
    have hcAxis' :
        (R.selectedWitness hmn inletCenter incoming firstFlip secondFlip
          p delta X (i, positive) k).seedCenter.1 i = (n + m + 1 : ℕ) := by
      simpa [c] using hcAxis
    cases positive <;>
      simp [selectedTarget, hcenter, hflip, cubicRestartFrameIso_apply,
        cubicRestartFrameFlip, hcAxis'] at hcentralAxis ⊢ <;>
      ring_nf at hcentralAxis ⊢ <;> omega
  · intro j hja
    have hj := inletCompensatingTarget_transverse_bounds hcentral hc hja
    simpa [selectedTarget, c, hcenter, hflip] using hj

/-- The second member of a fresh outgoing pair starts at the provisional face seed, which
still satisfies the same directional corridor bound. -/
theorem endpointVertices_secondOutgoingQuery_subset_endpointBoxes_of_coarseLocated
    {d m n : ℕ} (hmn : 2 * m ≤ n)
    (R : LaterSiteRuntime d) (x inletCenter : Cubic d)
    (incoming : CubicDirection d) (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) (a : CubicDirection d) (k : ℕ) (hk : 2 ≤ k)
    (hbase : R.inletReferenceBase = grimmettMarstrandSiteCenter (m + n + 1) x)
    (hcentral : R.centralTarget ∈
      cubicMetricBox d (grimmettMarstrandSiteCenter (m + n + 1) x) (m + n + 1))
    (hnone : R.outgoing a = none) :
    let R1 := R.step hmn inletCenter incoming firstFlip secondFlip
      p delta incremented X a k
    (cubicEdgeEndpointVertices
        ((R1.restartQuery inletCenter incoming firstFlip secondFlip a (k + 1)
          ).restartSupport m n) : Set (Cubic d)) ⊆
      (cubicMetricBox d (grimmettMarstrandSiteCenter (m + n + 1) x)
          (2 * (m + n + 1)) : Set (Cubic d)) ∪
        (cubicMetricBox d
          (grimmettMarstrandSiteCenter (m + n + 1) (cubicStepFrom x a))
          (2 * (m + n + 1)) : Set (Cubic d)) := by
  dsimp only
  let R1 := R.step hmn inletCenter incoming firstFlip secondFlip
    p delta incremented X a k
  have hcenter := R.slotCenterFor_step_same_succ_of_two_le hmn inletCenter incoming
    firstFlip secondFlip p delta incremented X a k hk
  have hb := R.selectedTarget_directionalBounds_of_coarseLocated hmn x inletCenter
    incoming firstFlip secondFlip p delta X a k hk hbase hcentral hnone
  simpa [restartQuery, SourceFiniteEdgeRevealState.framedQuery, R1, hcenter] using
    cubicEdgeEndpointVertices_framedRestartSupport_subset_endpointBoxes_of_directionalBounds
      (m := m) (n := n)
      (R.selectedTarget hmn inletCenter incoming firstFlip secondFlip p delta X a k) a
      (R1.slotTransverseFlip incoming firstFlip secondFlip a (k + 1))
      (cubicEdgeEndpointVertices (R1.source.referenceExploredEdges
        (cubicRestartFrameIso
          (R.selectedTarget hmn inletCenter incoming firstFlip secondFlip p delta X a k) a
          (R1.slotTransverseFlip incoming firstFlip secondFlip a (k + 1))))) x hb.1 hb.2

/-- Both literal slots of one fresh outgoing branch pair are confined to `A` once the two
endpoint boxes of that coarse bond lie in `A`. -/
theorem supportsWithin_restartPair_of_coarseLocated
    {d m n : ℕ} (hmn : 2 * m ≤ n)
    (R : LaterSiteRuntime d) (x inletCenter : Cubic d)
    (incoming : CubicDirection d) (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) (A : Set (Cubic d))
    (a : CubicDirection d) (k : ℕ) (hk : 2 ≤ k)
    (hbase : R.inletReferenceBase = grimmettMarstrandSiteCenter (m + n + 1) x)
    (hcentral : R.centralTarget ∈
      cubicMetricBox d (grimmettMarstrandSiteCenter (m + n + 1) x) (m + n + 1))
    (hnone : R.outgoing a = none)
    (hboxes :
      (cubicMetricBox d (grimmettMarstrandSiteCenter (m + n + 1) x)
          (2 * (m + n + 1)) : Set (Cubic d)) ∪
        (cubicMetricBox d
          (grimmettMarstrandSiteCenter (m + n + 1) (cubicStepFrom x a))
          (2 * (m + n + 1)) : Set (Cubic d)) ⊆ A) :
    SupportsWithin hmn inletCenter incoming firstFlip secondFlip p delta incremented X A
      R k (laterSiteBranchRestartPair a) := by
  have hfirst := R.endpointVertices_outgoingQuery_subset_endpointBoxes_of_coarseLocated
    hmn x inletCenter incoming firstFlip secondFlip a k hk hcentral hnone
  have hsecond := R.endpointVertices_secondOutgoingQuery_subset_endpointBoxes_of_coarseLocated
    hmn x inletCenter incoming firstFlip secondFlip p delta incremented X a k hk
      hbase hcentral hnone
  change _ ∧ _ ∧ True
  exact ⟨hfirst.trans hboxes, hsecond.trans hboxes, trivial⟩

/-- A duplicate-pair schedule over distinct fresh directions is confined to `A` when each
advertised neighboring coarse box belongs to `A`. -/
theorem supportsWithin_branchPairs_of_coarseLocated
    {d m n : ℕ} (hmn : 2 * m ≤ n)
    (inletCenter : Cubic d) (incoming : CubicDirection d)
    (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) (A : Set (Cubic d))
    (R : LaterSiteRuntime d) (k : ℕ) (x : Cubic d)
    (branches : List (CubicDirection d)) (hnodup : branches.Nodup)
    (hbase : R.inletReferenceBase = grimmettMarstrandSiteCenter (m + n + 1) x)
    (hcentral : R.centralTarget ∈
      cubicMetricBox d (grimmettMarstrandSiteCenter (m + n + 1) x) (m + n + 1))
    (hclear : ∀ a, a ∈ branches → R.outgoing a = none)
    (hboxes : ∀ a, a ∈ branches →
      (cubicMetricBox d (grimmettMarstrandSiteCenter (m + n + 1) x)
          (2 * (m + n + 1)) : Set (Cubic d)) ∪
        (cubicMetricBox d
          (grimmettMarstrandSiteCenter (m + n + 1) (cubicStepFrom x a))
          (2 * (m + n + 1)) : Set (Cubic d)) ⊆ A)
    (hk : 2 ≤ k) :
    SupportsWithin hmn inletCenter incoming firstFlip secondFlip p delta incremented X A
      R k (branches.flatMap laterSiteBranchRestartPair) := by
  induction branches generalizing R k with
  | nil => trivial
  | cons b rest ih =>
      rw [List.nodup_cons] at hnodup
      simp only [List.flatMap_cons]
      rw [supportsWithin_append]
      let Rb := runFrom hmn inletCenter incoming firstFlip secondFlip p delta incremented X
        R k (laterSiteBranchRestartPair b)
      have hbaseRb :
          Rb.inletReferenceBase = grimmettMarstrandSiteCenter (m + n + 1) x := by
        rw [show Rb.inletReferenceBase = R.inletReferenceBase by
          exact runFrom_inletReferenceBase hmn inletCenter incoming firstFlip secondFlip
            p delta incremented X R k (laterSiteBranchRestartPair b)]
        exact hbase
      have hcentralRb : Rb.centralTarget ∈
          cubicMetricBox d (grimmettMarstrandSiteCenter (m + n + 1) x)
            (m + n + 1) := by
        rw [show Rb.centralTarget = R.centralTarget by
          exact runFrom_centralTarget_of_two_le hmn inletCenter incoming firstFlip secondFlip
            p delta incremented X R k (laterSiteBranchRestartPair b) hk]
        exact hcentral
      have hclearRb : ∀ a, a ∈ rest → Rb.outgoing a = none := by
        intro a ha
        rw [show Rb.outgoing a = R.outgoing a by
          exact runFrom_outgoing_eq_of_not_mem hmn inletCenter incoming firstFlip secondFlip
            p delta incremented X R k (laterSiteBranchRestartPair b) a (by
              simpa [laterSiteBranchRestartPair] using (Ne.symm (by
                intro hab
                subst a
                exact hnodup.1 ha)))]
        exact hclear a (by simp [ha])
      constructor
      · exact supportsWithin_restartPair_of_coarseLocated hmn R x inletCenter incoming
          firstFlip secondFlip p delta incremented X A b k hk hbase hcentral
            (hclear b (by simp)) (hboxes b (by simp))
      · apply ih (R := Rb) (k := k + (laterSiteBranchRestartPair b).length)
          hnodup.2 hbaseRb hcentralRb hclearRb
        · intro a ha
          exact hboxes a (by simp [ha])
        · simp [laterSiteBranchRestartPair]

/-- The record published by a fresh duplicate branch lies in the uniform centered box of its
second signed restart.  The stronger literal half-way-box statement is recovered below from
the coarse-site location invariant. -/
theorem outgoing_runFrom_restartPair_mem_framedHalfwayBox
    {d m n : ℕ} (hm : 1 ≤ m) (hmn : 2 * m ≤ n)
    (R : LaterSiteRuntime d) (inletCenter : Cubic d)
    (incoming : CubicDirection d) (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) (a : CubicDirection d) (k : ℕ) (hk : 2 ≤ k)
    {U : LaterSiteOutgoingSeed d}
    (hU : (runFrom hmn inletCenter incoming firstFlip secondFlip p delta incremented X
      R k (laterSiteBranchRestartPair a)).outgoing a = some U) :
    let R1 := R.step hmn inletCenter incoming firstFlip secondFlip
      p delta incremented X a k
    U.physicalCenter ∈
      cubicMetricBox d (R1.slotCenterFor inletCenter a (k + 1))
        (2 * (m + n + 1)) := by
  dsimp only
  let R1 := R.step hmn inletCenter incoming firstFlip secondFlip
    p delta incremented X a k
  change U.physicalCenter ∈
    cubicMetricBox d (R1.slotCenterFor inletCenter a (k + 1))
      (2 * (m + n + 1))
  let q := (R1.selectedWitness hmn inletCenter incoming firstFlip secondFlip
    p delta X a (k + 1)).seedCenter.1
  change (R1.step hmn inletCenter incoming firstFlip secondFlip p delta incremented X
    a (k + 1)).outgoing a = some U at hU
  have hk' : 2 ≤ k + 1 := by omega
  have hphysical : U.physicalCenter =
      cubicRestartFrameIso (R1.slotCenterFor inletCenter a (k + 1)) a
        (R1.slotTransverseFlip incoming firstFlip secondFlip a (k + 1)) q := by
    symm
    simpa [step, hk', q] using congrArg (fun V ↦ Option.map
      LaterSiteOutgoingSeed.physicalCenter V) hU
  rw [hphysical]
  change R1.selectedTarget hmn inletCenter incoming firstFlip secondFlip p delta X a
      (k + 1) ∈
    cubicMetricBox d (R1.slotCenterFor inletCenter a (k + 1))
      (2 * (m + n + 1))
  exact R1.selectedTarget_mem_centeredBox hmn inletCenter incoming
    firstFlip secondFlip p delta X a (k + 1)

/-- Source-faithful location theorem for a fresh outgoing pair.  When the runtime retains the
deterministic publishing-site center and its central seed is in that site's radius-`N` box,
the two compensated applications publish in the literal coarse-bond half-way box. -/
theorem outgoing_runFrom_restartPair_mem_halfwayBox_of_coarseLocated
    {d m n : ℕ} (hmn : 2 * m ≤ n)
    (R : LaterSiteRuntime d) (x inletCenter : Cubic d)
    (incoming : CubicDirection d) (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) (a : CubicDirection d) (k : ℕ) (hk : 2 ≤ k)
    (hbase : R.inletReferenceBase = grimmettMarstrandSiteCenter (m + n + 1) x)
    (hcentral : R.centralTarget ∈
      cubicMetricBox d (grimmettMarstrandSiteCenter (m + n + 1) x) (m + n + 1))
    (hnone : R.outgoing a = none)
    {U : LaterSiteOutgoingSeed d}
    (hU : (runFrom hmn inletCenter incoming firstFlip secondFlip p delta incremented X
      R k (laterSiteBranchRestartPair a)).outgoing a = some U) :
    U.physicalCenter ∈ grimmettMarstrandHalfwayBox d (m + n + 1) x a := by
  let c := (R.selectedWitness hmn inletCenter incoming firstFlip secondFlip
    p delta X a k).seedCenter.1
  let R1 := R.step hmn inletCenter incoming firstFlip secondFlip
    p delta incremented X a k
  let q := (R1.selectedWitness hmn inletCenter incoming firstFlip secondFlip
    p delta X a (k + 1)).seedCenter.1
  have hc : SeedBoxWithinBoundaryLayer d a.1 m n c := by
    exact R.selectedWitness_seedBoxWithinBoundaryLayer hmn inletCenter incoming firstFlip
      secondFlip p delta X a k
  have hq : SeedBoxWithinBoundaryLayer d a.1 m n q := by
    exact R1.selectedWitness_seedBoxWithinBoundaryLayer hmn inletCenter incoming firstFlip
      secondFlip p delta X a (k + 1)
  have hlocated := pairedInletCompensatingTarget_mem_halfwayBox hcentral hc hq
  have hcenter := R.slotCenterFor_step_same_succ_of_two_le hmn inletCenter incoming
    firstFlip secondFlip p delta incremented X a k hk
  have hflip := R.slotTransverseFlip_step_same_succ_of_two_le hmn inletCenter incoming
    firstFlip secondFlip p delta incremented X a k hk
  have hk0 : k ≠ 0 := by omega
  have hk1 : k ≠ 1 := by omega
  have hstartCenter : R.slotCenterFor inletCenter a k = R.centralTarget := by
    simp [slotCenterFor, hk0, hk1, hnone]
  have hstartFlip : R.slotTransverseFlip incoming firstFlip secondFlip a k =
      inletCompensatingTransverseFlip a
        (cubicRelativePosition (grimmettMarstrandSiteCenter (m + n + 1) x)
          R.centralTarget) := by
    simp [slotTransverseFlip, hk0, hk1, hnone, hbase]
  have hselected :
      R.selectedTarget hmn inletCenter incoming firstFlip secondFlip p delta X a k =
        cubicRestartFrameIso R.centralTarget a
          (inletCompensatingTransverseFlip a
            (cubicRelativePosition (grimmettMarstrandSiteCenter (m + n + 1) x)
              R.centralTarget)) c := by
    simp [selectedTarget, c, hstartCenter, hstartFlip]
  change (R1.step hmn inletCenter incoming firstFlip secondFlip p delta incremented X
    a (k + 1)).outgoing a = some U at hU
  have hk' : 2 ≤ k + 1 := by omega
  have hphysical : U.physicalCenter =
      cubicRestartFrameIso (R1.slotCenterFor inletCenter a (k + 1)) a
        (R1.slotTransverseFlip incoming firstFlip secondFlip a (k + 1)) q := by
    symm
    simpa [step, hk', q] using congrArg (fun V ↦ Option.map
      LaterSiteOutgoingSeed.physicalCenter V) hU
  rw [hphysical, hcenter, hflip, hbase, hselected]
  simpa [c, q, R1, selectedTarget] using hlocated

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

/-- Every branch published by a duplicate-pair schedule lies in the literal half-way box of
that signed coarse bond, provided the branch phase starts from a central seed in the current
site box and all scheduled outgoing slots are fresh. -/
theorem exists_outgoing_runFrom_branchPairs_mem_halfwayBox_of_coarseLocated
    {d m n : ℕ} (hmn : 2 * m ≤ n)
    (inletCenter : Cubic d) (incoming : CubicDirection d)
    (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) (R : LaterSiteRuntime d) (k : ℕ)
    (x : Cubic d) (branches : List (CubicDirection d))
    (hnodup : branches.Nodup)
    (hbase : R.inletReferenceBase = grimmettMarstrandSiteCenter (m + n + 1) x)
    (hcentral : R.centralTarget ∈
      cubicMetricBox d (grimmettMarstrandSiteCenter (m + n + 1) x) (m + n + 1))
    (hclear : ∀ a, a ∈ branches → R.outgoing a = none)
    (a : CubicDirection d) (ha : a ∈ branches) (hk : 2 ≤ k) :
    ∃ U : LaterSiteOutgoingSeed d,
      (runFrom hmn inletCenter incoming firstFlip secondFlip p delta incremented X
        R k (branches.flatMap laterSiteBranchRestartPair)).outgoing a = some U ∧
      U.physicalCenter ∈ grimmettMarstrandHalfwayBox d (m + n + 1) x a := by
  induction branches generalizing R k with
  | nil => simp at ha
  | cons b rest ih =>
      rw [List.nodup_cons] at hnodup
      simp only [List.mem_cons] at ha
      simp only [List.flatMap_cons]
      rw [runFrom_append]
      let Rb := runFrom hmn inletCenter incoming firstFlip secondFlip p delta incremented X
        R k (laterSiteBranchRestartPair b)
      have hbaseRb :
          Rb.inletReferenceBase = grimmettMarstrandSiteCenter (m + n + 1) x := by
        rw [show Rb.inletReferenceBase = R.inletReferenceBase by
          exact runFrom_inletReferenceBase hmn inletCenter incoming firstFlip secondFlip
            p delta incremented X R k (laterSiteBranchRestartPair b)]
        exact hbase
      have hcentralRb : Rb.centralTarget ∈
          cubicMetricBox d (grimmettMarstrandSiteCenter (m + n + 1) x)
            (m + n + 1) := by
        rw [show Rb.centralTarget = R.centralTarget by
          exact runFrom_centralTarget_of_two_le hmn inletCenter incoming firstFlip secondFlip
            p delta incremented X R k (laterSiteBranchRestartPair b) hk]
        exact hcentral
      have hclearRb : ∀ c, c ∈ rest → Rb.outgoing c = none := by
        intro c hc
        rw [show Rb.outgoing c = R.outgoing c by
          exact runFrom_outgoing_eq_of_not_mem hmn inletCenter incoming firstFlip secondFlip
            p delta incremented X R k (laterSiteBranchRestartPair b) c (by
              simpa [laterSiteBranchRestartPair] using (Ne.symm (by
                intro hcb
                subst c
                exact hnodup.1 hc)))]
        exact hclear c (by simp [hc])
      by_cases hab : a = b
      · subst b
        obtain ⟨U, hU⟩ := exists_outgoing_runFrom_restartPair hmn inletCenter incoming
          firstFlip secondFlip p delta incremented X R k a hk
        have hlocated := outgoing_runFrom_restartPair_mem_halfwayBox_of_coarseLocated
          hmn R x inletCenter incoming firstFlip secondFlip p delta incremented X a k hk
            hbase hcentral (hclear a (by simp)) hU
        refine ⟨U, ?_, hlocated⟩
        rw [runFrom_outgoing_eq_of_not_mem hmn inletCenter incoming firstFlip secondFlip
          p delta incremented X Rb (k + (laterSiteBranchRestartPair a).length)
            (rest.flatMap laterSiteBranchRestartPair) a]
        · exact hU
        · simpa [laterSiteBranchRestartPair] using hnodup.1
      · apply ih
          (R := Rb) (k := k + (laterSiteBranchRestartPair b).length)
          hnodup.2 hbaseRb hcentralRb hclearRb (ha.resolve_left hab)
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
                cubicRelativePosition R.inletReferenceBase
                  (R.selectedTarget hmn inletCenter incoming firstFlip secondFlip
                    p delta X a k) } := by
          have hsome : some U = some
              { physicalCenter :=
                  R.selectedTarget hmn inletCenter incoming firstFlip secondFlip p delta X a k
                referenceCenter :=
                  cubicRelativePosition R.inletReferenceBase
                    (R.selectedTarget hmn inletCenter incoming firstFlip secondFlip
                      p delta X a k) } := by
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
  let target := cubicRestartFrameIso (R.slotCenterFor inletCenter a k) a
    (R.slotTransverseFlip incoming firstFlip secondFlip a k) W.seedCenter.1
  ⟨target, cubicRelativePosition (R.slotCenterFor inletCenter a k) target⟩

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
      let k := branchSlotIndex incoming a
      let W := R.selectedWitness hmn inletCenter incoming firstFlip secondFlip p delta X a k
      cubicRelativePosition (R.slotCenterFor inletCenter a k)
        (cubicRestartFrameIso (R.slotCenterFor inletCenter a k) a
          (R.slotTransverseFlip incoming firstFlip secondFlip a k) W.seedCenter.1) := by
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
