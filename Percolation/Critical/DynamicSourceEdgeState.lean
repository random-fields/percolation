import Percolation.Critical.DynamicRecursiveEdgeState

/-!
# Source-faithful global edge-boundary recursion

Grimmett's `ΔE_k` is the boundary of `E_k` in the whole cubic line graph.  The finite region
`E_Z` changes from stage to stage and only restricts which exits and exterior edges are read.
This file keeps those notions separate.  It supersedes the fixed-ambient helper for the actual
source construction while retaining that helper for finite local calculations.
-/

namespace Percolation

open MeasureTheory
open scoped unitInterval

/-- The active part of the global boundary in the current finite stage region. -/
noncomputable def activeCubicEdgeBoundary {d : ℕ}
    (explored stageRegion : Finset (CubicEdge d)) : Finset (CubicEdge d) :=
  cubicEdgeBoundary explored ∩ stageRegion

/-- Edges of the current finite region that are neither explored nor on the global boundary. -/
noncomputable def sourceStageExterior {d : ℕ}
    (explored stageRegion : Finset (CubicEdge d)) : Finset (CubicEdge d) :=
  stageRegion \ (explored ∪ cubicEdgeBoundary explored)

/-- Literal source successor in a finite region: enter through increment-open edges of the
global boundary that lie in `E_Z`, then take the complete `p`-open line-graph closure through
the exterior portion of `E_Z`. -/
noncomputable def sourceExploredEdgeStep {d : ℕ}
    (explored stageRegion : Finset (CubicEdge d)) (p : I)
    (incremented : CubicEdge d → I) (X : CubicEdge d → ℝ) :
    Finset (CubicEdge d) :=
  exploredEdgeStepFamily explored (activeCubicEdgeBoundary explored stageRegion)
    (sourceStageExterior explored stageRegion) p incremented X

theorem explored_subset_sourceExploredEdgeStep {d : ℕ}
    (explored stageRegion : Finset (CubicEdge d)) (p : I)
    (incremented : CubicEdge d → I) (X : CubicEdge d → ℝ) :
    explored ⊆ sourceExploredEdgeStep explored stageRegion p incremented X :=
  oldExplored_subset_exploredEdgeStepFamily _ _ _ _ _ _

/-- A changing-region source step can add only edges from its declared finite stage region. -/
theorem sourceExploredEdgeStep_subset_explored_union_stageRegion {d : ℕ}
    (explored stageRegion : Finset (CubicEdge d)) (p : I)
    (incremented : CubicEdge d → I) (X : CubicEdge d → ℝ) :
    sourceExploredEdgeStep explored stageRegion p incremented X ⊆
      explored ∪ stageRegion := by
  intro e he
  have hallowed := exploredEdgeStepFamily_subset
    explored (activeCubicEdgeBoundary explored stageRegion)
      (sourceStageExterior explored stageRegion) p incremented X he
  simp only [Finset.mem_union] at hallowed ⊢
  rcases hallowed with (heOld | heBoundary) | heExterior
  · exact Or.inl heOld
  · exact Or.inr (Finset.mem_inter.mp heBoundary).2
  · exact Or.inr (Finset.mem_sdiff.mp heExterior).1

theorem activeCubicEdgeBoundary_disjoint_explored {d : ℕ}
    (explored stageRegion : Finset (CubicEdge d)) :
    Disjoint (activeCubicEdgeBoundary explored stageRegion) explored := by
  rw [Finset.disjoint_left]
  intro e heActive heExplored
  exact (mem_cubicEdgeBoundary_iff.mp (Finset.mem_inter.mp heActive).1).1 heExplored

theorem activeCubicEdgeBoundary_disjoint_sourceStageExterior {d : ℕ}
    (explored stageRegion : Finset (CubicEdge d)) :
    Disjoint (activeCubicEdgeBoundary explored stageRegion)
      (sourceStageExterior explored stageRegion) := by
  rw [Finset.disjoint_left]
  intro e heActive heExterior
  exact (Finset.mem_sdiff.mp heExterior).2
    (Finset.mem_union_right _ (Finset.mem_inter.mp heActive).1)

theorem sourceStageExterior_eq_sdiff_activeBoundary {d : ℕ}
    (explored stageRegion : Finset (CubicEdge d)) :
    sourceStageExterior explored stageRegion =
      stageRegion \ (explored ∪ activeCubicEdgeBoundary explored stageRegion) := by
  classical
  ext e
  rw [sourceStageExterior, Finset.mem_sdiff, Finset.mem_union,
    Finset.mem_sdiff, Finset.mem_union]
  constructor
  · rintro ⟨heStage, hnot⟩
    refine ⟨heStage, ?_⟩
    rintro (heExplored | heActive)
    · exact hnot (Or.inl heExplored)
    · exact hnot (Or.inr (Finset.mem_inter.mp heActive).1)
  · rintro ⟨heStage, hnot⟩
    refine ⟨heStage, ?_⟩
    rintro (heExplored | heBoundary)
    · exact hnot (Or.inl heExplored)
    · exact hnot (Or.inr (Finset.mem_inter.mpr ⟨heBoundary, heStage⟩))

theorem cubicEdgeBoundaryWithin_subset_activeCubicEdgeBoundary {d : ℕ}
    (explored stageRegion : Finset (CubicEdge d)) :
    cubicEdgeBoundaryWithin explored stageRegion ⊆
      activeCubicEdgeBoundary explored stageRegion := by
  rw [cubicEdgeBoundaryWithin_eq_inter, activeCubicEdgeBoundary,
    Finset.inter_comm]

/-! ### Relating the edge-line boundary to a restart's vertex boundary -/

/-- Every box edge leaving the endpoint set of `E` is a literal edge-line boundary edge of
`E`.  This is the direction needed to show that the Lemma 7.17 history is already present in
the source interval profile. -/
theorem cubicRegionBoundaryEdgesWithinBox_endpointVertices_subset_cubicEdgeBoundary
    {d n : ℕ} (E : Finset (CubicEdge d)) :
    cubicRegionBoundaryEdgesWithinBox d (cubicEdgeEndpointVertices E) n ⊆
      cubicEdgeBoundary E := by
  intro e heRegion
  let x := cubicRegionBoundaryInsideEndpoint (cubicEdgeEndpointVertices E) e
  let y := cubicRegionBoundaryOutsideEndpoint (cubicEdgeEndpointVertices E) e
  have hxRegion : x ∈ cubicEdgeEndpointVertices E :=
    cubicRegionBoundaryInsideEndpoint_mem heRegion
  have hyNotRegion : y ∉ cubicEdgeEndpointVertices E :=
    cubicRegionBoundaryOutsideEndpoint_not_mem heRegion
  have hxe : x ∈ (e : Sym2 (Cubic d)) := by
    rw [← cubicRegionBoundaryEndpoints_edge heRegion]
    simp [x]
  have hye : y ∈ (e : Sym2 (Cubic d)) := by
    rw [← cubicRegionBoundaryEndpoints_edge heRegion]
    simp [y]
  obtain ⟨f, hfE, hxf⟩ := mem_cubicEdgeEndpointVertices_iff.mp hxRegion
  have heNotE : e ∉ E := by
    intro heE
    exact hyNotRegion (mem_cubicEdgeEndpointVertices_iff.mpr ⟨e, heE, hye⟩)
  apply mem_cubicEdgeBoundary_iff.mpr
  refine ⟨heNotE, f, hfE, ?_⟩
  rw [cubicEdgeLineGraph_adj_iff]
  exact ⟨fun hfe ↦ heNotE (hfe ▸ hfE), x, hxf, hxe⟩

/-- A literal edge-line boundary edge cannot be exterior to the endpoint set of `E`: its
shared endpoint witnesses incidence with that set. -/
theorem disjoint_cubicEdgeBoundary_regionExterior_endpointVertices
    {d n : ℕ} (E : Finset (CubicEdge d)) :
    Disjoint (cubicEdgeBoundary E : Set (CubicEdge d))
      (cubicRegionExteriorEdgesWithinBox d (cubicEdgeEndpointVertices E) n :
        Set (CubicEdge d)) := by
  rw [Set.disjoint_left]
  intro e heBoundary heExterior
  obtain ⟨_heNotE, f, hfE, _hfe, x, _hxf, hxe⟩ :=
    mem_cubicEdgeBoundary_iff.mp heBoundary
  have hxRegion : x ∈ cubicEdgeEndpointVertices E :=
    mem_cubicEdgeEndpointVertices_iff.mpr ⟨f, hfE, _hxf⟩
  exact (mem_cubicRegionExteriorEdgesWithinBox_iff.mp heExterior).2 x hxe hxRegion

/-- Exact active-boundary identity for an unframed restart.  The restart support excludes
internal chords and exterior edges automatically; the only geometric freshness premise is
that its new target-seed coordinates avoid the old global boundary. -/
theorem cubicRegionBoundary_endpointVertices_eq_boundary_inter_restartEventSupport
    {d m n : ℕ} (E : Finset (CubicEdge d)) (i : Fin d)
    (hTargetFresh : Disjoint (cubicEdgeBoundary E)
      (seededBoundaryTargetSupport d i m n)) :
    cubicRegionBoundaryEdgesWithinBox d (cubicEdgeEndpointVertices E) n =
      cubicEdgeBoundary E ∩
        restartEventSupport d i m n (cubicEdgeEndpointVertices E) := by
  apply Finset.Subset.antisymm
  · intro e heRegion
    exact Finset.mem_inter.mpr
      ⟨cubicRegionBoundaryEdgesWithinBox_endpointVertices_subset_cubicEdgeBoundary E
          heRegion,
        boundary_subset_restartEventSupport d i m n (cubicEdgeEndpointVertices E) heRegion⟩
  · intro e he
    obtain ⟨heBoundary, heRestart⟩ := Finset.mem_inter.mp he
    change e ∈ restartEventSupport d i m n (cubicEdgeEndpointVertices E) at heRestart
    simp only [restartEventSupport, Finset.mem_union] at heRestart
    rcases heRestart with (heRegion | heExterior) | heTarget
    · exact heRegion
    · exact (Set.disjoint_left.mp
        (disjoint_cubicEdgeBoundary_regionExterior_endpointVertices
          (n := n) E) heBoundary heExterior).elim
    · exact (Finset.disjoint_left.mp hTargetFresh heBoundary heTarget).elim

/-- Vertex-level separation from a target support implies edge-line-boundary separation. -/
theorem disjoint_cubicEdgeBoundary_target_of_endpointVertices
    {d : ℕ} (E T : Finset (CubicEdge d))
    (hVertices : Disjoint (cubicEdgeEndpointVertices E)
      (cubicEdgeEndpointVertices T)) :
    Disjoint (cubicEdgeBoundary E) T := by
  rw [Finset.disjoint_left]
  intro e heBoundary heTarget
  obtain ⟨_heNotE, f, hfE, _hfe, x, hxf, hxe⟩ :=
    mem_cubicEdgeBoundary_iff.mp heBoundary
  exact Finset.disjoint_left.mp hVertices
    (mem_cubicEdgeEndpointVertices_iff.mpr ⟨f, hfE, hxf⟩)
    (mem_cubicEdgeEndpointVertices_iff.mpr ⟨e, heTarget, hxe⟩)

/-- If the new target support has no endpoint previously incident to `E`, then `E` is disjoint
from the entire restart support built from its endpoint region.  Boundary and exterior
freshness are automatic; only target separation is substantive. -/
theorem disjoint_explored_restartEventSupport_of_targetEndpointFresh
    {d m n : ℕ} (E : Finset (CubicEdge d)) (i : Fin d)
    (hVertices : Disjoint (cubicEdgeEndpointVertices E)
      (cubicEdgeEndpointVertices (seededBoundaryTargetSupport d i m n))) :
    Disjoint E (restartEventSupport d i m n (cubicEdgeEndpointVertices E)) := by
  rw [Finset.disjoint_left]
  intro e heE heRestart
  simp only [restartEventSupport, Finset.mem_union] at heRestart
  rcases heRestart with (heRegion | heExterior) | heTarget
  · let y := cubicRegionBoundaryOutsideEndpoint (cubicEdgeEndpointVertices E) e
    have hyEdge : y ∈ (e : Sym2 (Cubic d)) := by
      rw [← cubicRegionBoundaryEndpoints_edge heRegion]
      simp [y]
    exact cubicRegionBoundaryOutsideEndpoint_not_mem heRegion
      (mem_cubicEdgeEndpointVertices_iff.mpr ⟨e, heE, hyEdge⟩)
  · have hxEdge : e.1.out.1 ∈ (e : Sym2 (Cubic d)) := Sym2.out_fst_mem e.1
    exact (mem_cubicRegionExteriorEdgesWithinBox_iff.mp heExterior).2
      e.1.out.1 hxEdge
      (mem_cubicEdgeEndpointVertices_iff.mpr ⟨e, heE, hxEdge⟩)
  · have hxEdge : e.1.out.1 ∈ (e : Sym2 (Cubic d)) := Sym2.out_fst_mem e.1
    exact Finset.disjoint_left.mp hVertices
      (mem_cubicEdgeEndpointVertices_iff.mpr ⟨e, heE, hxEdge⟩)
      (mem_cubicEdgeEndpointVertices_iff.mpr ⟨e, heTarget, hxEdge⟩)

/-- A reference explored set lying strictly behind the positive `i`-face has endpoint support
disjoint from the next target.  This packages the concrete coordinate obligation used by the
root and later-site steering schedules. -/
theorem disjoint_endpointVertices_seededBoundaryTargetSupport_of_coord_lt
    {d m n : ℕ} (E : Finset (CubicEdge d)) (i : Fin d)
    (hBehind : ∀ z ∈ cubicEdgeEndpointVertices E, z i < (n : ℤ)) :
    Disjoint (cubicEdgeEndpointVertices E)
      (cubicEdgeEndpointVertices (seededBoundaryTargetSupport d i m n)) := by
  rw [Finset.disjoint_left]
  intro z hzE hzTarget
  obtain ⟨e, heTarget, hze⟩ :=
    mem_cubicEdgeEndpointVertices_iff.mp hzTarget
  exact (not_lt_of_ge
    (endpoint_mem_seededBoundaryTargetSupport_coord_ge heTarget hze))
      (hBehind z hzE)

/-- Recursive source state.  The lower threshold is zero on every edge that has never been
explored or exposed as a global boundary edge; this is the invariant needed when a changing
stage region creates a new boundary edge outside its own support. -/
structure SourceFiniteEdgeRevealState (d : ℕ) where
  explored : Finset (CubicEdge d)
  lower : CubicEdge d → I
  upper : CubicEdge d → I
  lower_eq_zero_off : ∀ e, e ∉ explored → e ∉ cubicEdgeBoundary explored → lower e = 0

noncomputable instance sourceFiniteEdgeRevealStateDecidableEq (d : ℕ) :
    DecidableEq (SourceFiniteEdgeRevealState d) :=
  Classical.decEq _

namespace SourceFiniteEdgeRevealState

/-- A source state has room for one further sprinkling increment on every boundary
coordinate.  The predicate belongs to the source-state API because both the generic framed
restart law and the later root/lattice runtimes use it. -/
def HasIncrementBudget {d : ℕ}
    (S : SourceFiniteEdgeRevealState d) (delta : ℝ) : Prop :=
  ∀ e, (S.lower e : ℝ) + delta ≤ 1

noncomputable def boundary {d : ℕ} (S : SourceFiniteEdgeRevealState d) :
    Finset (CubicEdge d) :=
  cubicEdgeBoundary S.explored

/-- Complete nontrivial history at a source stage: the global boundary is lower-closed and the
explored edge set is upper-open. -/
noncomputable def profile {d : ℕ} (S : SourceFiniteEdgeRevealState d) :
    FiniteRevealIntervalProfile (CubicEdge d) where
  closedSupport := S.boundary
  openSupport := S.explored
  lower := S.lower
  upper := S.upper

/-- Exact accumulated reveal history.  In addition to the current global boundary, every
explored edge retains its previous lower endpoint.  Thus an absorbed boundary edge is recorded
by the genuine interval `lower(e) ≤ X(e) < upper(e)`, rather than only by its new upper bound.
The lighter `profile` above remains useful as the Markov state needed to reproduce one step. -/
noncomputable def historyProfile {d : ℕ} (S : SourceFiniteEdgeRevealState d) :
    FiniteRevealIntervalProfile (CubicEdge d) where
  closedSupport := S.explored ∪ S.boundary
  openSupport := S.explored
  lower := S.lower
  upper := S.upper

/-- An exact accumulated-history cell implies the lighter current-state cell. -/
theorem historyProfile_event_subset_profile_event {d : ℕ}
    (S : SourceFiniteEdgeRevealState d) :
    S.historyProfile.event ⊆ S.profile.event := by
  intro X hX
  constructor
  · intro e he
    exact hX.1 e (Finset.mem_union_right _ he)
  · exact hX.2

/-- Finite probability-one support condition for labels on the next global boundary. -/
def nonnegativeBoundaryEvent {d : ℕ} (E : Finset (CubicEdge d)) :
    Set (CubicEdge d → ℝ) :=
  boundaryClosedHistoryEvent E (fun _ ↦ 0)

/-- Probability-one support of the common-uniform coupling.  Keeping this global event
separate from a finite boundary cylinder lets a state-dependent exploration discharge every
new-boundary nonnegativity obligation with one realization hypothesis. -/
def nonnegativeCouplingEvent {d : ℕ} : Set (CubicEdge d → ℝ) :=
  Set.univ.pi fun _ ↦ Set.Ici (0 : ℝ)

@[simp]
theorem mem_nonnegativeCouplingEvent_iff {d : ℕ} {X : CubicEdge d → ℝ} :
    X ∈ nonnegativeCouplingEvent ↔ ∀ e, 0 ≤ X e := by
  rw [nonnegativeCouplingEvent, Set.mem_pi]
  constructor
  · intro h e
    exact h e (Set.mem_univ e)
  · intro h e _he
    exact h e

theorem measurableSet_nonnegativeCouplingEvent {d : ℕ} :
    MeasurableSet (nonnegativeCouplingEvent : Set (CubicEdge d → ℝ)) := by
  exact MeasurableSet.univ_pi fun _ ↦ measurableSet_Ici

/-- All coupling coordinates are nonnegative almost surely, simultaneously. -/
theorem couplingMeasure_real_nonnegativeCouplingEvent {d : ℕ} :
    (couplingMeasure (CubicEdge d)).real nonnegativeCouplingEvent = 1 := by
  rw [measureReal_def, couplingMeasure, nonnegativeCouplingEvent,
    Measure.infinitePi_pi_univ _ (fun _ ↦ measurableSet_Ici)]
  have hset : Set.Ici (0 : ℝ) ∩ Set.Icc 0 1 = Set.Icc 0 1 :=
    Set.inter_eq_right.mpr fun _ hx ↦ hx.1
  simp [Measure.restrict_apply, hset, Real.volume_Icc]

/-- A realization in the global probability-one support satisfies every finite boundary
condition used by the source recursion. -/
theorem mem_nonnegativeBoundaryEvent_of_mem_nonnegativeCouplingEvent
    {d : ℕ} {E : Finset (CubicEdge d)} {X : CubicEdge d → ℝ}
    (hX : X ∈ nonnegativeCouplingEvent) :
    X ∈ nonnegativeBoundaryEvent E := by
  exact fun e _he ↦ mem_nonnegativeCouplingEvent_iff.mp hX e

@[simp]
theorem mem_nonnegativeBoundaryEvent_iff {d : ℕ}
    {E : Finset (CubicEdge d)} {X : CubicEdge d → ℝ} :
    X ∈ nonnegativeBoundaryEvent E ↔ ∀ e ∈ E, 0 ≤ X e := by
  rfl

theorem couplingMeasure_real_nonnegativeBoundaryEvent {d : ℕ}
    (E : Finset (CubicEdge d)) :
    (couplingMeasure (CubicEdge d)).real (nonnegativeBoundaryEvent E) = 1 := by
  rw [nonnegativeBoundaryEvent,
    couplingMeasure_real_boundaryClosedHistoryEvent]
  simp

noncomputable def nextExplored {d : ℕ} (S : SourceFiniteEdgeRevealState d)
    (stageRegion : Finset (CubicEdge d)) (p : I)
    (incremented : CubicEdge d → I) (X : CubicEdge d → ℝ) :
    Finset (CubicEdge d) :=
  sourceExploredEdgeStep S.explored stageRegion p incremented X

noncomputable def updateData {d : ℕ} (S : SourceFiniteEdgeRevealState d)
    (stageRegion : Finset (CubicEdge d)) (p : I)
    (incremented : CubicEdge d → I) (X : CubicEdge d → ℝ) :
    RevealThresholdUpdateData (CubicEdge d) where
  oldExplored := S.explored
  nextExplored := S.nextExplored stageRegion p incremented X
  oldBoundary := S.boundary
  nextBoundary := cubicEdgeBoundary (S.nextExplored stageRegion p incremented X)
  ambient := stageRegion
  lower := S.lower
  upper := S.upper
  incremented := incremented
  density := p

/-- One literal changing-region source update. -/
noncomputable def next {d : ℕ} (S : SourceFiniteEdgeRevealState d)
    (stageRegion : Finset (CubicEdge d)) (p : I)
    (incremented : CubicEdge d → I) (X : CubicEdge d → ℝ) :
    SourceFiniteEdgeRevealState d where
  explored := S.nextExplored stageRegion p incremented X
  lower := (S.updateData stageRegion p incremented X).updatedLower
  upper := (S.updateData stageRegion p incremented X).updatedUpper
  lower_eq_zero_off := by
    intro e heNotNext heNotNextBoundary
    have hmono : S.explored ⊆ S.nextExplored stageRegion p incremented X :=
      explored_subset_sourceExploredEdgeStep _ _ _ _ _
    have heNotOld : e ∉ S.explored := fun heOld ↦ heNotNext (hmono heOld)
    have heNotOldBoundary : e ∉ S.boundary := by
      intro heOldBoundary
      obtain ⟨_heNotOld', f, hfOld, hfe⟩ := mem_cubicEdgeBoundary_iff.mp heOldBoundary
      apply heNotNextBoundary
      apply mem_cubicEdgeBoundary_iff.mpr
      exact ⟨heNotNext, f, hmono hfOld, hfe⟩
    have hzero := S.lower_eq_zero_off e heNotOld heNotOldBoundary
    by_cases heStage : e ∈ stageRegion
    · simp [RevealThresholdUpdateData.updatedLower, updateData, heStage,
        heNotOldBoundary, heNotNextBoundary, hzero]
    · exact (S.updateData stageRegion p incremented X).updatedLower_eq_old_of_not_mem_ambient
        heStage |>.trans hzero

/-- A uniform threshold bound is preserved by one literal source-state update. -/
theorem next_lower_le_of_le {d : ℕ} (S : SourceFiniteEdgeRevealState d)
    (stageRegion : Finset (CubicEdge d)) (p : I)
    (incremented : CubicEdge d → I) (X : CubicEdge d → ℝ) (q : I)
    (hlower : ∀ e, S.lower e ≤ q)
    (hincremented : ∀ e, incremented e ≤ q)
    (hp : p ≤ q) (e : CubicEdge d) :
    (S.next stageRegion p incremented X).lower e ≤ q := by
  exact (S.updateData stageRegion p incremented X).updatedLower_le_of_le
    q hlower hincremented hp e

/-- Real-valued uniform bound for one literal source-state update. -/
theorem coe_next_lower_le_of_le {d : ℕ} (S : SourceFiniteEdgeRevealState d)
    (stageRegion : Finset (CubicEdge d)) (p : I)
    (incremented : CubicEdge d → I) (X : CubicEdge d → ℝ) (q : ℝ)
    (hlower : ∀ e, (S.lower e : ℝ) ≤ q)
    (hincremented : ∀ e, (incremented e : ℝ) ≤ q)
    (hp : (p : ℝ) ≤ q) (e : CubicEdge d) :
    ((S.next stageRegion p incremented X).lower e : ℝ) ≤ q := by
  exact (S.updateData stageRegion p incremented X).coe_updatedLower_le_of_le
    q hlower hincremented hp e

theorem explored_subset_nextExplored {d : ℕ} (S : SourceFiniteEdgeRevealState d)
    (stageRegion : Finset (CubicEdge d)) (p : I)
    (incremented : CubicEdge d → I) (X : CubicEdge d → ℝ) :
    S.explored ⊆ S.nextExplored stageRegion p incremented X :=
  explored_subset_sourceExploredEdgeStep _ _ _ _ _

/-- State-level form of the finite stage-region bound. -/
theorem nextExplored_subset_explored_union_stageRegion {d : ℕ}
    (S : SourceFiniteEdgeRevealState d) (stageRegion : Finset (CubicEdge d)) (p : I)
    (incremented : CubicEdge d → I) (X : CubicEdge d → ℝ) :
    S.nextExplored stageRegion p incremented X ⊆ S.explored ∪ stageRegion :=
  sourceExploredEdgeStep_subset_explored_union_stageRegion
    S.explored stageRegion p incremented X

/-- Deterministic semantics of one literal source update.  The nonnegativity hypothesis is
only needed for a genuinely new global boundary edge outside the current finite region, where
the source leaves its threshold at the initial value zero.  It holds almost surely under the
common-uniform coupling and will be included explicitly in exact reveal cells. -/
theorem mem_next_profile {d : ℕ} (S : SourceFiniteEdgeRevealState d)
    (stageRegion : Finset (CubicEdge d)) (p : I)
    (incremented : CubicEdge d → I) (X : CubicEdge d → ℝ)
    (hcurrent : X ∈ S.profile.event)
    (hnonneg : ∀ e ∈ cubicEdgeBoundary (S.nextExplored stageRegion p incremented X),
      0 ≤ X e) :
    X ∈ (S.next stageRegion p incremented X).profile.event := by
  let oldBoundary := S.boundary
  let activeBoundary := activeCubicEdgeBoundary S.explored stageRegion
  let exterior := sourceStageExterior S.explored stageRegion
  let nextExplored := S.nextExplored stageRegion p incremented X
  let nextBoundary := cubicEdgeBoundary nextExplored
  let D := S.updateData stageRegion p incremented X
  change (∀ e ∈ nextBoundary, (D.updatedLower e : ℝ) ≤ X e) ∧
    ∀ e ∈ nextExplored, X e < (D.updatedUpper e : ℝ)
  have hactiveDisjoint : Disjoint activeBoundary S.explored :=
    activeCubicEdgeBoundary_disjoint_explored _ _
  have hactiveExterior : Disjoint activeBoundary exterior :=
    activeCubicEdgeBoundary_disjoint_sourceStageExterior _ _
  have hline : cubicEdgeBoundaryWithin S.explored stageRegion ⊆ activeBoundary :=
    cubicEdgeBoundaryWithin_subset_activeCubicEdgeBoundary _ _
  constructor
  · intro e heNextBoundary
    by_cases heOldBoundary : e ∈ oldBoundary
    · have heNotNext : e ∉ nextExplored :=
        (mem_cubicEdgeBoundary_iff.mp heNextBoundary).1
      by_cases heStage : e ∈ stageRegion
      · rw [RevealThresholdUpdateData.updatedLower_eq_incremented_of_mem_oldBoundary_not_nextExplored
            D heStage heOldBoundary heNotNext]
        apply incremented_le_label_of_mem_oldBoundary_not_mem_exploredEdgeStepFamily
          S.explored activeBoundary exterior p incremented X
        · exact Finset.mem_inter.mpr ⟨heOldBoundary, heStage⟩
        · exact heNotNext
      · rw [RevealThresholdUpdateData.updatedLower_eq_old_of_not_mem_ambient D heStage]
        exact hcurrent.1 e heOldBoundary
    · by_cases heStage : e ∈ stageRegion
      · rw [RevealThresholdUpdateData.updatedLower_eq_density_of_mem_newBoundary
            D heStage heNextBoundary heOldBoundary]
        apply density_le_label_of_mem_newBoundaryFamily_not_oldBoundary
          S.explored activeBoundary stageRegion exterior p incremented X hline
            (show exterior = stageRegion \ (S.explored ∪ activeBoundary) by
              dsimp [exterior, activeBoundary]
              exact sourceStageExterior_eq_sdiff_activeBoundary _ _)
        · rw [cubicEdgeBoundaryWithin_eq_inter]
          exact Finset.mem_inter.mpr ⟨heStage, heNextBoundary⟩
        · exact fun heActive ↦ heOldBoundary (Finset.mem_inter.mp heActive).1
      · rw [RevealThresholdUpdateData.updatedLower_eq_old_of_not_mem_ambient D heStage]
        have heNotOld : e ∉ S.explored := by
          intro heOld
          exact (mem_cubicEdgeBoundary_iff.mp heNextBoundary).1
            (S.explored_subset_nextExplored stageRegion p incremented X heOld)
        change (S.lower e : ℝ) ≤ X e
        rw [S.lower_eq_zero_off e heNotOld heOldBoundary]
        exact hnonneg e heNextBoundary
  · intro e heNext
    by_cases heOld : e ∈ S.explored
    · rw [RevealThresholdUpdateData.updatedUpper_eq_old_of_mem_oldExplored D heOld]
      exact hcurrent.2 e heOld
    · by_cases heOldBoundary : e ∈ oldBoundary
      · rw [RevealThresholdUpdateData.updatedUpper_eq_incremented_of_mem_absorbedBoundary
            D heOld heOldBoundary heNext]
        have heActive : e ∈ activeBoundary := by
          have heAllowed := exploredEdgeStepFamily_subset
            S.explored activeBoundary exterior p incremented X heNext
          rw [Finset.mem_union, Finset.mem_union] at heAllowed
          rcases heAllowed with (heOld' | heActive) | heExterior
          · exact (heOld heOld').elim
          · exact heActive
          · exact (Finset.mem_sdiff.mp heExterior).2
              (Finset.mem_union_right _ heOldBoundary) |>.elim
        exact label_lt_incremented_of_mem_oldBoundary_mem_exploredEdgeStepFamily
          S.explored activeBoundary exterior p incremented X
          hactiveDisjoint hactiveExterior heActive heNext
      · rw [RevealThresholdUpdateData.updatedUpper_eq_density_of_mem_newInterior
            D heOld heOldBoundary heNext]
        exact label_lt_density_of_mem_exploredEdgeStepFamily_not_old_not_boundary
          S.explored activeBoundary exterior p incremented X heNext heOld
          (fun heActive ↦ heOldBoundary (Finset.mem_inter.mp heActive).1)

/-- Exact accumulated-history invariance for one changing-region source update.  The global
probability-one nonnegative support supplies the otherwise invisible lower endpoint zero on a
newly explored exterior edge. -/
theorem mem_next_historyProfile {d : ℕ} (S : SourceFiniteEdgeRevealState d)
    (stageRegion : Finset (CubicEdge d)) (p : I)
    (incremented : CubicEdge d → I) (X : CubicEdge d → ℝ)
    (hcurrent : X ∈ S.historyProfile.event)
    (hnonneg : X ∈ nonnegativeCouplingEvent) :
    X ∈ (S.next stageRegion p incremented X).historyProfile.event := by
  have hnextProfile : X ∈ (S.next stageRegion p incremented X).profile.event :=
    S.mem_next_profile stageRegion p incremented X
      (S.historyProfile_event_subset_profile_event hcurrent)
      (fun _ _ ↦ mem_nonnegativeCouplingEvent_iff.mp hnonneg _)
  constructor
  · intro e he
    rcases Finset.mem_union.mp he with heNext | heBoundary
    · change
        ((S.updateData stageRegion p incremented X).updatedLower e : ℝ) ≤ X e
      rw [RevealThresholdUpdateData.updatedLower_eq_old_of_mem_nextExplored
        _ (disjoint_cubicEdgeBoundary_left
          (S.nextExplored stageRegion p incremented X)) heNext]
      by_cases heOld : e ∈ S.explored
      · exact hcurrent.1 e (Finset.mem_union_left _ heOld)
      · by_cases heOldBoundary : e ∈ S.boundary
        · exact hcurrent.1 e (Finset.mem_union_right _ heOldBoundary)
        · change (S.lower e : ℝ) ≤ X e
          rw [S.lower_eq_zero_off e heOld heOldBoundary]
          exact mem_nonnegativeCouplingEvent_iff.mp hnonneg e
    · exact hnextProfile.1 e heBoundary
  · exact hnextProfile.2

/-- A source successor's complete interval profile is a deterministic cell for its explored
edge set: every second label realization satisfying that profile reproduces exactly the same
finite line-graph closure. -/
theorem nextExplored_eq_of_mem_next_profile {d : ℕ}
    (S : SourceFiniteEdgeRevealState d)
    (stageRegion : Finset (CubicEdge d)) (p : I)
    (incremented : CubicEdge d → I) (X Y : CubicEdge d → ℝ)
    (hY : Y ∈ (S.next stageRegion p incremented X).profile.event) :
    S.nextExplored stageRegion p incremented Y =
      S.nextExplored stageRegion p incremented X := by
  classical
  let active := activeCubicEdgeBoundary S.explored stageRegion
  let exterior := sourceStageExterior S.explored stageRegion
  let BX := finiteEdgesBelowFamily active incremented X
  let AX := BX ∪ finiteEdgesBelow exterior p X
  let CX := finiteEdgeReachableClosure AX BX
  let BY := finiteEdgesBelowFamily active incremented Y
  let AY := BY ∪ finiteEdgesBelow exterior p Y
  let CY := finiteEdgeReachableClosure AY BY
  have hactiveOld : Disjoint active S.explored :=
    activeCubicEdgeBoundary_disjoint_explored _ _
  have boundary_mem_next_of_mem_BX : ∀ {e}, e ∈ BX →
      e ∈ S.nextExplored stageRegion p incremented X := by
    intro e he
    exact openBoundary_subset_exploredEdgeStepFamily
      S.explored active exterior p incremented X he
  have boundary_mem_BY_of_mem_BX : BX ⊆ BY := by
    intro e heBX
    have heActive := (mem_finiteEdgesBelowFamily_iff.mp heBX).1
    have heNext := boundary_mem_next_of_mem_BX heBX
    have hUpper := hY.2 e heNext
    have heNotOld := fun heOld ↦
      Finset.disjoint_left.mp hactiveOld heActive heOld
    have heOldBoundary : e ∈ S.boundary := (Finset.mem_inter.mp heActive).1
    change Y e <
      ((S.updateData stageRegion p incremented X).updatedUpper e : ℝ) at hUpper
    rw [RevealThresholdUpdateData.updatedUpper_eq_incremented_of_mem_absorbedBoundary
      _ heNotOld heOldBoundary heNext] at hUpper
    exact mem_finiteEdgesBelowFamily_iff.mpr ⟨heActive, hUpper⟩
  have hCXCY : CX ⊆ CY := by
    have htarget : CX ⊆ CX ∩ CY := by
      apply finiteEdgeReachableClosure_subset_of_closed
      · intro e he
        have heBX := (Finset.mem_inter.mp he).2
        have heCX : e ∈ CX := sources_subset_finiteEdgeReachableClosure
          (allowed := AX) (sources := BX) Finset.subset_union_left heBX
        have heBY := boundary_mem_BY_of_mem_BX heBX
        have heCY : e ∈ CY := sources_subset_finiteEdgeReachableClosure
          (allowed := AY) (sources := BY) Finset.subset_union_left heBY
        exact Finset.mem_inter.mpr ⟨heCX, heCY⟩
      · intro e heTarget f hfAX hef
        have heCX := (Finset.mem_inter.mp heTarget).1
        have heCY := (Finset.mem_inter.mp heTarget).2
        have hfCX := mem_finiteEdgeReachableClosure_of_adj heCX hfAX hef
        have hfNext : f ∈ S.nextExplored stageRegion p incremented X :=
          Finset.mem_union_right S.explored hfCX
        have hfAY : f ∈ AY := by
          rcases Finset.mem_union.mp hfAX with hfBX | hfExterior
          · exact Finset.mem_union_left _ (boundary_mem_BY_of_mem_BX hfBX)
          · have hfExteriorMem := (mem_finiteEdgesBelow_iff.mp hfExterior).1
            have hfNotOld : f ∉ S.explored := by
              intro hfOld
              exact (Finset.mem_sdiff.mp hfExteriorMem).2
                (Finset.mem_union_left _ hfOld)
            have hfNotBoundary : f ∉ S.boundary := by
              intro hfBoundary
              exact (Finset.mem_sdiff.mp hfExteriorMem).2
                (Finset.mem_union_right _ hfBoundary)
            have hUpper := hY.2 f hfNext
            change Y f <
              ((S.updateData stageRegion p incremented X).updatedUpper f : ℝ) at hUpper
            rw [RevealThresholdUpdateData.updatedUpper_eq_density_of_mem_newInterior
              _ hfNotOld hfNotBoundary hfNext] at hUpper
            exact Finset.mem_union_right _
              (mem_finiteEdgesBelow_iff.mpr ⟨hfExteriorMem, hUpper⟩)
        have hfCY := mem_finiteEdgeReachableClosure_of_adj heCY hfAY hef
        exact Finset.mem_inter.mpr ⟨hfCX, hfCY⟩
    exact fun e he ↦ (Finset.mem_inter.mp (htarget he)).2
  have hCYNX : CY ⊆ S.nextExplored stageRegion p incremented X := by
    apply finiteEdgeReachableClosure_subset_of_closed
    · intro e he
      have heBY := (Finset.mem_inter.mp he).2
      have heActive := (mem_finiteEdgesBelowFamily_iff.mp heBY).1
      have heYOpen := (mem_finiteEdgesBelowFamily_iff.mp heBY).2
      by_contra heNotNext
      have heOldBoundary : e ∈ S.boundary := (Finset.mem_inter.mp heActive).1
      obtain ⟨f, hfOld, hfe⟩ := (mem_cubicEdgeBoundary_iff.mp heOldBoundary).2
      have hfNext := S.explored_subset_nextExplored stageRegion p incremented X hfOld
      have heNextBoundary : e ∈
          cubicEdgeBoundary (S.nextExplored stageRegion p incremented X) :=
        mem_cubicEdgeBoundary_iff.mpr ⟨heNotNext, f, hfNext, hfe⟩
      have hLower := hY.1 e heNextBoundary
      change ((S.updateData stageRegion p incremented X).updatedLower e : ℝ) ≤
        Y e at hLower
      rw [RevealThresholdUpdateData.updatedLower_eq_incremented_of_mem_oldBoundary_not_nextExplored
        _ (Finset.mem_inter.mp heActive).2 heOldBoundary heNotNext] at hLower
      exact (not_lt_of_ge hLower) heYOpen
    · intro e heNext f hfAY hef
      by_contra hfNotNext
      have hfNextBoundary : f ∈
          cubicEdgeBoundary (S.nextExplored stageRegion p incremented X) :=
        mem_cubicEdgeBoundary_iff.mpr ⟨hfNotNext, e, heNext, hef⟩
      have hLower := hY.1 f hfNextBoundary
      rcases Finset.mem_union.mp hfAY with hfBY | hfExterior
      · have hfActive := (mem_finiteEdgesBelowFamily_iff.mp hfBY).1
        have hfYOpen := (mem_finiteEdgesBelowFamily_iff.mp hfBY).2
        have hfOldBoundary : f ∈ S.boundary := (Finset.mem_inter.mp hfActive).1
        change ((S.updateData stageRegion p incremented X).updatedLower f : ℝ) ≤
          Y f at hLower
        rw [RevealThresholdUpdateData.updatedLower_eq_incremented_of_mem_oldBoundary_not_nextExplored
          _ (Finset.mem_inter.mp hfActive).2 hfOldBoundary hfNotNext] at hLower
        exact (not_lt_of_ge hLower) hfYOpen
      · have hfExteriorMem := (mem_finiteEdgesBelow_iff.mp hfExterior).1
        have hfYOpen := (mem_finiteEdgesBelow_iff.mp hfExterior).2
        have hfStage := (Finset.mem_sdiff.mp hfExteriorMem).1
        have hfNotOldBoundary : f ∉ S.boundary := by
          intro hfBoundary
          exact (Finset.mem_sdiff.mp hfExteriorMem).2
            (Finset.mem_union_right _ hfBoundary)
        change ((S.updateData stageRegion p incremented X).updatedLower f : ℝ) ≤
          Y f at hLower
        rw [RevealThresholdUpdateData.updatedLower_eq_density_of_mem_newBoundary
          _ hfStage hfNextBoundary hfNotOldBoundary] at hLower
        exact (not_lt_of_ge hLower) hfYOpen
  change S.explored ∪ CY = S.explored ∪ CX
  apply Finset.Subset.antisymm
  · intro e he
    rcases Finset.mem_union.mp he with heOld | heCY
    · exact Finset.mem_union_left _ heOld
    · exact hCYNX heCY
  · intro e he
    rcases Finset.mem_union.mp he with heOld | heCX
    · exact Finset.mem_union_left _ heOld
    · exact Finset.mem_union_right _ (hCXCY heCX)

/-- The complete source successor state, including its lower and upper threshold functions,
is constant throughout each successor interval cell. -/
theorem eq_of_explored_lower_upper {d : ℕ}
    {S T : SourceFiniteEdgeRevealState d}
    (hexplored : S.explored = T.explored)
    (hlower : S.lower = T.lower) (hupper : S.upper = T.upper) : S = T := by
  cases S
  cases T
  simp_all

/-- Once the finite successor explored set is fixed, the complete successor state is fixed.
This is the finite branching principle behind the concrete history partition. -/
theorem next_eq_of_nextExplored_eq {d : ℕ}
    (S : SourceFiniteEdgeRevealState d)
    (stageRegion : Finset (CubicEdge d)) (p : I)
    (incremented : CubicEdge d → I) (X Y : CubicEdge d → ℝ)
    (hexplored : S.nextExplored stageRegion p incremented Y =
      S.nextExplored stageRegion p incremented X) :
    S.next stageRegion p incremented Y =
      S.next stageRegion p incremented X := by
  have hdata : S.updateData stageRegion p incremented Y =
      S.updateData stageRegion p incremented X := by
    unfold updateData
    rw [hexplored]
  apply eq_of_explored_lower_upper
  · exact hexplored
  · funext e
    simp only [next]
    exact congrArg (fun D ↦ D.updatedLower e) hdata
  · funext e
    simp only [next]
    exact congrArg (fun D ↦ D.updatedUpper e) hdata

/-- A single source update has finite state range, although its label realization ranges over
an infinite product.  The update factors through the powerset of the finite set consisting of
the old explored edges and the current stage region. -/
theorem finite_range_next {d : ℕ}
    (S : SourceFiniteEdgeRevealState d)
    (stageRegion : Finset (CubicEdge d)) (p : I)
    (incremented : CubicEdge d → I) :
    (Set.range fun X : CubicEdge d → ℝ ↦
      S.next stageRegion p incremented X).Finite := by
  classical
  let exploredSet : (CubicEdge d → ℝ) → Finset (CubicEdge d) := fun X ↦
    S.nextExplored stageRegion p incremented X
  have hExplored : (Set.range exploredSet).Finite := by
    apply ((S.explored ∪ stageRegion).powerset.finite_toSet).subset
    rintro E ⟨X, rfl⟩
    exact Finset.mem_powerset.mpr
      (S.nextExplored_subset_explored_union_stageRegion stageRegion p incremented X)
  letI : Fintype (Set.range exploredSet) := hExplored.fintype
  let representative : Set.range exploredSet → CubicEdge d → ℝ := fun E ↦
    Classical.choose E.property
  apply (Set.finite_range fun E : Set.range exploredSet ↦
    S.next stageRegion p incremented (representative E)).subset
  rintro T ⟨X, rfl⟩
  let E : Set.range exploredSet := ⟨exploredSet X, ⟨X, rfl⟩⟩
  refine ⟨E, ?_⟩
  apply S.next_eq_of_nextExplored_eq stageRegion p incremented
  change exploredSet (representative E) = exploredSet X
  simpa [E] using Classical.choose_spec E.property

/-- Finite branching is stable when the incoming state itself has finite range and the next
region and threshold family are deterministic functions of that state. -/
theorem finite_range_next_of_finite_range {d : ℕ}
    (state : (CubicEdge d → ℝ) → SourceFiniteEdgeRevealState d)
    (stageRegion : SourceFiniteEdgeRevealState d → Finset (CubicEdge d))
    (p : I)
    (incremented : SourceFiniteEdgeRevealState d → CubicEdge d → I)
    (hstate : (Set.range state).Finite) :
    (Set.range fun X ↦
      (state X).next (stageRegion (state X)) p (incremented (state X)) X).Finite := by
  classical
  apply (hstate.biUnion fun S _ ↦
    S.finite_range_next (stageRegion S) p (incremented S)).subset
  rintro T ⟨X, rfl⟩
  simp only [Set.mem_iUnion]
  exact ⟨state X, ⟨⟨X, rfl⟩, ⟨X, rfl⟩⟩⟩

/-- Under a genuinely monotone boundary update, every successor history cell refines its
predecessor history cell.  This is the backward implication needed to prove disjointness of
the concrete finite state cells. -/
theorem next_historyProfile_event_subset_historyProfile_event {d : ℕ}
    (S : SourceFiniteEdgeRevealState d)
    (stageRegion : Finset (CubicEdge d)) (p : I)
    (incremented : CubicEdge d → I) (X : CubicEdge d → ℝ)
    (hincremented : ∀ e, S.lower e ≤ incremented e) :
    (S.next stageRegion p incremented X).historyProfile.event ⊆
      S.historyProfile.event := by
  intro Y hY
  constructor
  · intro e heOld
    rcases Finset.mem_union.mp heOld with heOldExplored | heOldBoundary
    · have heNext := S.explored_subset_nextExplored
          stageRegion p incremented X heOldExplored
      have hLower := hY.1 e (Finset.mem_union_left _ heNext)
      change ((S.updateData stageRegion p incremented X).updatedLower e : ℝ) ≤ Y e at hLower
      rw [RevealThresholdUpdateData.updatedLower_eq_old_of_mem_nextExplored _
        (disjoint_cubicEdgeBoundary_left _) heNext] at hLower
      exact hLower
    · by_cases heNext : e ∈ S.nextExplored stageRegion p incremented X
      · have hLower := hY.1 e (Finset.mem_union_left _ heNext)
        change ((S.updateData stageRegion p incremented X).updatedLower e : ℝ) ≤ Y e at hLower
        rw [RevealThresholdUpdateData.updatedLower_eq_old_of_mem_nextExplored _
          (disjoint_cubicEdgeBoundary_left _) heNext] at hLower
        exact hLower
      · obtain ⟨_heNotOld, f, hfOld, hfe⟩ :=
          mem_cubicEdgeBoundary_iff.mp heOldBoundary
        have hfNext := S.explored_subset_nextExplored
          stageRegion p incremented X hfOld
        have heNextBoundary : e ∈
            cubicEdgeBoundary (S.nextExplored stageRegion p incremented X) :=
          mem_cubicEdgeBoundary_iff.mpr ⟨heNext, f, hfNext, hfe⟩
        have hLower := hY.1 e (Finset.mem_union_right _ heNextBoundary)
        change ((S.updateData stageRegion p incremented X).updatedLower e : ℝ) ≤ Y e at hLower
        by_cases heStage : e ∈ stageRegion
        · rw [RevealThresholdUpdateData.updatedLower_eq_incremented_of_mem_oldBoundary_not_nextExplored
            _ heStage heOldBoundary heNext] at hLower
          exact (show (S.lower e : ℝ) ≤ (incremented e : ℝ) from
            Subtype.coe_le_coe.mpr (hincremented e)).trans hLower
        · rw [RevealThresholdUpdateData.updatedLower_eq_old_of_not_mem_ambient _ heStage]
            at hLower
          exact hLower
  · intro e heOldExplored
    have heNext := S.explored_subset_nextExplored
      stageRegion p incremented X heOldExplored
    have hUpper := hY.2 e heNext
    change Y e < ((S.updateData stageRegion p incremented X).updatedUpper e : ℝ) at hUpper
    rw [RevealThresholdUpdateData.updatedUpper_eq_old_of_mem_oldExplored _ heOldExplored]
      at hUpper
    exact hUpper

theorem next_eq_of_mem_next_profile {d : ℕ}
    (S : SourceFiniteEdgeRevealState d)
    (stageRegion : Finset (CubicEdge d)) (p : I)
    (incremented : CubicEdge d → I) (X Y : CubicEdge d → ℝ)
    (hY : Y ∈ (S.next stageRegion p incremented X).profile.event) :
    S.next stageRegion p incremented Y =
      S.next stageRegion p incremented X := by
  have hexplored :=
    S.nextExplored_eq_of_mem_next_profile stageRegion p incremented X Y hY
  have hdata : S.updateData stageRegion p incremented Y =
      S.updateData stageRegion p incremented X := by
    unfold updateData
    rw [hexplored]
  apply eq_of_explored_lower_upper
  · exact hexplored
  · funext e
    simp only [next]
    exact congrArg (fun D ↦ D.updatedLower e) hdata
  · funext e
    simp only [next]
    exact congrArg (fun D ↦ D.updatedUpper e) hdata

/-- Exact accumulated-history membership is sufficient to reproduce the whole successor
state. -/
theorem next_eq_of_mem_next_historyProfile {d : ℕ}
    (S : SourceFiniteEdgeRevealState d)
    (stageRegion : Finset (CubicEdge d)) (p : I)
    (incremented : CubicEdge d → I) (X Y : CubicEdge d → ℝ)
    (hY : Y ∈ (S.next stageRegion p incremented X).historyProfile.event) :
    S.next stageRegion p incremented Y =
      S.next stageRegion p incremented X :=
  S.next_eq_of_mem_next_profile stageRegion p incremented X Y
    ((S.next stageRegion p incremented X).historyProfile_event_subset_profile_event hY)

/-- Event-form wrapper around the source step semantics. -/
theorem mem_next_profile_of_mem_nonnegativeBoundaryEvent {d : ℕ}
    (S : SourceFiniteEdgeRevealState d)
    (stageRegion : Finset (CubicEdge d)) (p : I)
    (incremented : CubicEdge d → I) (X : CubicEdge d → ℝ)
    (hcurrent : X ∈ S.profile.event)
    (hnonneg : X ∈ nonnegativeBoundaryEvent
      (cubicEdgeBoundary (S.nextExplored stageRegion p incremented X))) :
    X ∈ (S.next stageRegion p incremented X).profile.event :=
  S.mem_next_profile stageRegion p incremented X hcurrent hnonneg

/-- Iterate the source-faithful recursion through changing finite regions. -/
noncomputable def run {d : ℕ} (S : SourceFiniteEdgeRevealState d) (p : I)
    (X : CubicEdge d → ℝ) :
    List (Finset (CubicEdge d) × (CubicEdge d → I)) →
      SourceFiniteEdgeRevealState d
  | [] => S
  | (stageRegion, incremented) :: rest =>
      (S.next stageRegion p incremented X).run p X rest

@[simp]
theorem run_nil {d : ℕ} (S : SourceFiniteEdgeRevealState d) (p : I)
    (X : CubicEdge d → ℝ) : S.run p X [] = S :=
  rfl

@[simp]
theorem run_cons {d : ℕ} (S : SourceFiniteEdgeRevealState d) (p : I)
    (X : CubicEdge d → ℝ) (stageRegion : Finset (CubicEdge d))
    (incremented : CubicEdge d → I)
    (rest : List (Finset (CubicEdge d) × (CubicEdge d → I))) :
    S.run p X ((stageRegion, incremented) :: rest) =
      (S.next stageRegion p incremented X).run p X rest :=
  rfl

/-- Exact interval invariance through any finite changing-region source schedule.  Each
nonnegativity premise is a finite cylinder of coupling probability one. -/
theorem mem_run_profile {d : ℕ} (S : SourceFiniteEdgeRevealState d) (p : I)
    (X : CubicEdge d → ℝ)
    (stages : List (Finset (CubicEdge d) × (CubicEdge d → I)))
    (hnonneg : ∀ j (hj : j < stages.length),
      let state := S.run p X (stages.take j)
      let stage := stages[j]
      X ∈ nonnegativeBoundaryEvent
        (cubicEdgeBoundary (state.nextExplored stage.1 p stage.2 X)))
    (hcurrent : X ∈ S.profile.event) :
    X ∈ (S.run p X stages).profile.event := by
  induction stages generalizing S with
  | nil => exact hcurrent
  | cons stage rest ih =>
      rcases stage with ⟨stageRegion, incremented⟩
      have hfirst : X ∈ nonnegativeBoundaryEvent
          (cubicEdgeBoundary (S.nextExplored stageRegion p incremented X)) := by
        simpa using hnonneg 0 (by simp)
      apply ih (S := S.next stageRegion p incremented X)
      · intro j hj
        have hs := hnonneg (j + 1) (by simp; omega)
        simpa [List.take_succ_cons] using hs
      · exact S.mem_next_profile_of_mem_nonnegativeBoundaryEvent
          stageRegion p incremented X hcurrent hfirst

/-- Exact accumulated-history invariance through any finite changing-region schedule on the
single probability-one common-uniform support. -/
theorem mem_run_historyProfile {d : ℕ} (S : SourceFiniteEdgeRevealState d) (p : I)
    (X : CubicEdge d → ℝ)
    (stages : List (Finset (CubicEdge d) × (CubicEdge d → I)))
    (hnonneg : X ∈ nonnegativeCouplingEvent)
    (hcurrent : X ∈ S.historyProfile.event) :
    X ∈ (S.run p X stages).historyProfile.event := by
  induction stages generalizing S with
  | nil => exact hcurrent
  | cons stage rest ih =>
      rcases stage with ⟨stageRegion, incremented⟩
      exact ih (S := S.next stageRegion p incremented X)
        (S.mem_next_historyProfile stageRegion p incremented X hcurrent hnonneg)

end SourceFiniteEdgeRevealState

end Percolation
