import Percolation.Critical.DynamicScheduleCells

/-!
# Fresh coordinates for dynamic reveal cells

Once the explored region `R` of a Grimmett--Marstrand restart is frozen, the information used
to construct `R` is carried by edges whose two endpoints lie in `R`.  The next restart instead
reads boundary edges, edges completely outside `R`, and target-seed edges beyond the exploratory
box.  This file proves those coordinate sets are literally disjoint.  It is the geometric
freshness fact needed to factor an exact reveal fiber into earlier information and the current
closed-boundary cell.
-/

namespace Percolation

open scoped unitInterval

/-- Edges of `B(n)` whose two endpoints lie in the frozen region `R`. -/
noncomputable def cubicRegionInternalEdgesWithinBox
    (d : ℕ) (R : Finset (Cubic d)) (n : ℕ) : Finset (CubicEdge d) := by
  classical
  exact (cubicBoxEdges d cubicOrigin n).filter fun e =>
    ∀ x ∈ (e : Sym2 (Cubic d)), x ∈ R

@[simp]
theorem mem_cubicRegionInternalEdgesWithinBox_iff
    {d n : ℕ} {R : Finset (Cubic d)} {e : CubicEdge d} :
    e ∈ cubicRegionInternalEdgesWithinBox d R n ↔
      e ∈ cubicBoxEdges d cubicOrigin n ∧
        ∀ x ∈ (e : Sym2 (Cubic d)), x ∈ R := by
  classical
  simp [cubicRegionInternalEdgesWithinBox]

theorem disjoint_cubicRegionInternalEdgesWithinBox_boundary
    (d : ℕ) (R : Finset (Cubic d)) (n : ℕ) :
    Disjoint (cubicRegionInternalEdgesWithinBox d R n : Set (CubicEdge d))
      (cubicRegionBoundaryEdgesWithinBox d R n : Set (CubicEdge d)) := by
  rw [Set.disjoint_left]
  intro e heInternal heBoundary
  have hends := (mem_cubicRegionInternalEdgesWithinBox_iff.mp heInternal).2
  rcases (mem_cubicRegionBoundaryEdgesWithinBox_iff.mp heBoundary).2 with h | h
  · exact h.2 (hends e.1.out.2 (Sym2.out_snd_mem e.1))
  · exact h.2 (hends e.1.out.1 (Sym2.out_fst_mem e.1))

theorem disjoint_cubicRegionInternalEdgesWithinBox_exterior
    (d : ℕ) (R : Finset (Cubic d)) (n : ℕ) :
    Disjoint (cubicRegionInternalEdgesWithinBox d R n : Set (CubicEdge d))
      (cubicRegionExteriorEdgesWithinBox d R n : Set (CubicEdge d)) := by
  rw [Set.disjoint_left]
  intro e heInternal heExterior
  have hendsInternal := (mem_cubicRegionInternalEdgesWithinBox_iff.mp heInternal).2
  have hendsExterior := (mem_cubicRegionExteriorEdgesWithinBox_iff.mp heExterior).2
  have heEndpoint : e.1.out.1 ∈ (e : Sym2 (Cubic d)) := by
    exact Sym2.out_fst_mem e.1
  exact hendsExterior e.1.out.1 heEndpoint
    (hendsInternal e.1.out.1 heEndpoint)

theorem disjoint_cubicRegionInternalEdgesWithinBox_target
    (d : ℕ) (R : Finset (Cubic d)) (i : Fin d) (m n : ℕ) :
    Disjoint (cubicRegionInternalEdgesWithinBox d R n : Set (CubicEdge d))
      (seededBoundaryTargetSupport d i m n : Set (CubicEdge d)) := by
  rw [Set.disjoint_left]
  intro e heInternal heTarget
  exact (Finset.mem_sdiff.mp heTarget).2
    (mem_cubicRegionInternalEdgesWithinBox_iff.mp heInternal).1

/-- Exact reference-frame freshness: edges internal to the frozen explored region are disjoint
from every coordinate read by the next restart. -/
theorem disjoint_cubicRegionInternalEdgesWithinBox_restartEventSupport
    (d : ℕ) (R : Finset (Cubic d)) (i : Fin d) (m n : ℕ) :
    Disjoint (cubicRegionInternalEdgesWithinBox d R n : Set (CubicEdge d))
      (restartEventSupport d i m n R : Set (CubicEdge d)) := by
  rw [Set.disjoint_left]
  intro e heInternal heRestart
  change e ∈ restartEventSupport d i m n R at heRestart
  simp only [restartEventSupport, Finset.mem_union] at heRestart
  rcases heRestart with (heBoundary | heExterior) | heTarget
  · exact Set.disjoint_left.mp
      (disjoint_cubicRegionInternalEdgesWithinBox_boundary d R n)
        heInternal heBoundary
  · exact Set.disjoint_left.mp
      (disjoint_cubicRegionInternalEdgesWithinBox_exterior d R n)
        heInternal heExterior
  · exact Set.disjoint_left.mp
      (disjoint_cubicRegionInternalEdgesWithinBox_target d R i m n)
        heInternal heTarget

/-- The same freshness statement after transporting the reference restart to an arbitrary
block center and signed direction. -/
theorem disjoint_orientedInternalEdges_restartSupport
    {d : ℕ} (center : Cubic d) (a : CubicDirection d)
    (R : Finset (Cubic d)) (m n : ℕ) :
    Disjoint
      ((cubicRegionInternalEdgesWithinBox d R n).image
        (cubicDirectionOrientationIso center a).mapEdgeSet : Set (CubicEdge d))
      (orientedRestartSupport center a m n R : Set (CubicEdge d)) := by
  rw [Set.disjoint_left]
  intro e heInternal heRestart
  rw [Finset.mem_coe, Finset.mem_image] at heInternal
  rw [Finset.mem_coe, orientedRestartSupport, Finset.mem_image] at heRestart
  obtain ⟨f, hfInternal, rfl⟩ := heInternal
  obtain ⟨g, hgRestart, hgf⟩ := heRestart
  have hfg : f = g := by
    exact (cubicDirectionOrientationIso center a).mapEdgeSet.injective hgf.symm
  subst g
  exact Set.disjoint_left.mp
    (disjoint_cubicRegionInternalEdgesWithinBox_restartEventSupport d R a.1 m n)
      hfInternal hgRestart

/-! ## The measurable earlier-information cell -/

/-- Keep only the edges internal to `R`. -/
def internalizedRestartConfiguration
    {d : ℕ} (R : Finset (Cubic d)) (n : ℕ) (omega : EdgeConfiguration d) :
    EdgeConfiguration d :=
  omega ∩ (cubicRegionInternalEdgesWithinBox d R n : Set (CubicEdge d))

/-- The Boolean-configuration event that exploring only internal edges reconstructs exactly
the candidate region `R`. -/
def restartInternalRegionEvent
    (d : ℕ) (R : Finset (Cubic d)) (m n : ℕ) : Set (EdgeConfiguration d) :=
  {omega | restartExploredRegion d
      (internalizedRestartConfiguration R n omega) m n = R}

theorem dependsOn_restartInternalRegionEvent
    (d : ℕ) (R : Finset (Cubic d)) (m n : ℕ) :
    DependsOn (cubicRegionInternalEdgesWithinBox d R n)
      (restartInternalRegionEvent d R m n) := by
  intro omega eta hagree
  have hconfig : internalizedRestartConfiguration R n omega =
      internalizedRestartConfiguration R n eta := by
    ext e
    simp only [internalizedRestartConfiguration, Set.mem_inter_iff, Finset.mem_coe]
    by_cases he : e ∈ cubicRegionInternalEdgesWithinBox d R n
    · simp [he, hagree e he]
    · simp [he]
  simp only [restartInternalRegionEvent, Set.mem_setOf_eq]
  rw [hconfig]

theorem measurableSet_restartInternalRegionEvent
    (d : ℕ) (R : Finset (Cubic d)) (m n : ℕ) :
    MeasurableSet (restartInternalRegionEvent d R m n) :=
  (dependsOn_restartInternalRegionEvent d R m n).measurableSet

/-- Common-uniform-label form of the earlier internal-region information. -/
def restartInternalRegionLabelEvent
    {d : ℕ} (R : Finset (Cubic d)) (m n : ℕ) (beta : CubicEdge d → I) :
    Set (CubicEdge d → ℝ) :=
  heterogeneousThresholdConfiguration beta ⁻¹'
    restartInternalRegionEvent d R m n

theorem measurableSet_restartInternalRegionLabelEvent
    {d : ℕ} (R : Finset (Cubic d)) (m n : ℕ) (beta : CubicEdge d → I) :
    MeasurableSet (restartInternalRegionLabelEvent R m n beta) :=
  (measurableSet_restartInternalRegionEvent d R m n).preimage
    (measurable_heterogeneousThresholdConfiguration beta)

/-- The earlier-information cell is measurable using only edges internal to `R`. -/
theorem measurableSet_restartInternalRegionLabelEvent_coordSigma
    {d : ℕ} (R : Finset (Cubic d)) (m n : ℕ) (beta : CubicEdge d → I) :
    @MeasurableSet (CubicEdge d → ℝ)
      (coordSigma (CubicEdge d)
        (cubicRegionInternalEdgesWithinBox d R n : Set (CubicEdge d)))
      (restartInternalRegionLabelEvent R m n beta) := by
  apply measurableSet_coordSigma_of_eqOn
    (measurableSet_restartInternalRegionLabelEvent R m n beta)
  intro X Y hXY
  apply dependsOn_restartInternalRegionEvent d R m n
  intro e he
  simp only [mem_heterogeneousThresholdConfiguration_iff]
  rw [hXY e he]

/-- The measurable internal-region cell is supported on coordinates disjoint from the next
reference restart. -/
theorem restartInternalRegionLabelEvent_fresh
    {d : ℕ} (R : Finset (Cubic d)) (i : Fin d) (m n : ℕ) :
    Disjoint (cubicRegionInternalEdgesWithinBox d R n : Set (CubicEdge d))
      (restartEventSupport d i m n R : Set (CubicEdge d)) :=
  disjoint_cubicRegionInternalEdgesWithinBox_restartEventSupport d R i m n

/-! ## Exact explored-region factorization -/

theorem finiteBoxOpenGraph_mono_of_subset
    {d : ℕ} {omega eta : EdgeConfiguration d} {n : ℕ}
    (hsub : omega ⊆ eta) :
    finiteBoxOpenGraph d omega cubicOrigin n ≤
      finiteBoxOpenGraph d eta cubicOrigin n := by
  intro u v huv
  have hopen := SimpleGraph.induce_adj.mp huv
  exact SimpleGraph.induce_adj.mpr <| cubicOpenGraph_adj.mpr
    ⟨(cubicOpenGraph_adj.mp hopen).1, hsub (cubicOpenGraph_adj.mp hopen).2⟩

/-- A walk in the box cannot cross the boundary of `R` when every boundary edge is closed. -/
theorem finiteBoxOpenWalk_endpoint_mem_of_boundary_closed
    {d n : ℕ} {R : Finset (Cubic d)} {omega : EdgeConfiguration d}
    (hclosed : omega ∈ closedEdgeSetEvent d
      (cubicRegionBoundaryEdgesWithinBox d R n))
    {z y : RestartBoxVertex d n}
    (hzR : z.1 ∈ R)
    (w : (finiteBoxOpenGraph d omega cubicOrigin n).Walk z y) :
    y.1 ∈ R := by
  have hdisjoint := (mem_closedEdgeSetEvent d
    (cubicRegionBoundaryEdgesWithinBox d R n) omega).mp hclosed
  induction w with
  | nil => exact hzR
  | @cons u v y huv tail ih =>
      have huvOpen := SimpleGraph.induce_adj.mp huv
      obtain ⟨huvCubic, heOpen⟩ := cubicOpenGraph_adj.mp huvOpen
      let e : CubicEdge d :=
        ⟨s(u.1, v.1), (cubicGraph d).mem_edgeSet.mpr huvCubic⟩
      have heBox : e ∈ cubicBoxEdges d cubicOrigin n := by
        obtain ⟨a, hva⟩ := (cubicGraph_adj_iff_exists_stepFrom u.1 v.1).mp huvCubic
        have heq : e = cubicStepEdge u.1 a := by
          apply Subtype.ext
          simp [e, cubicStepEdge, hva]
        rw [heq]
        exact cubicStepEdge_mem_cubicBoxEdges u.2 (by simpa [hva] using v.2)
      have hvR : v.1 ∈ R := by
        by_contra hvNot
        have heBoundary : e ∈ cubicRegionBoundaryEdgesWithinBox d R n :=
          mem_cubicRegionBoundaryEdgesWithinBox_of_endpoints heBox
            (by simp [e]) (by simp [e]) hzR hvNot
        exact Set.disjoint_left.mp hdisjoint heBoundary (by simpa [e] using heOpen)
      exact ih hvR

theorem finiteBoxOpenGraph_internalized_adj
    {d n : ℕ} {R : Finset (Cubic d)} {omega : EdgeConfiguration d}
    {u v : RestartBoxVertex d n}
    (huv : (finiteBoxOpenGraph d omega cubicOrigin n).Adj u v)
    (huR : u.1 ∈ R) (hvR : v.1 ∈ R) :
    (finiteBoxOpenGraph d (internalizedRestartConfiguration R n omega)
      cubicOrigin n).Adj u v := by
  have huvOpen := SimpleGraph.induce_adj.mp huv
  obtain ⟨huvCubic, heOpen⟩ := cubicOpenGraph_adj.mp huvOpen
  let e : CubicEdge d := ⟨s(u.1, v.1), (cubicGraph d).mem_edgeSet.mpr huvCubic⟩
  have heBox : e ∈ cubicBoxEdges d cubicOrigin n := by
    obtain ⟨a, hva⟩ := (cubicGraph_adj_iff_exists_stepFrom u.1 v.1).mp huvCubic
    have heq : e = cubicStepEdge u.1 a := by
      apply Subtype.ext
      simp [e, cubicStepEdge, hva]
    rw [heq]
    exact cubicStepEdge_mem_cubicBoxEdges u.2 (by simpa [hva] using v.2)
  have heInternal : e ∈ cubicRegionInternalEdgesWithinBox d R n := by
    rw [mem_cubicRegionInternalEdgesWithinBox_iff]
    refine ⟨heBox, ?_⟩
    intro x hx
    rw [show (e : Sym2 (Cubic d)) = s(u.1, v.1) by rfl, Sym2.mem_iff] at hx
    rcases hx with rfl | rfl
    · exact huR
    · exact hvR
  exact SimpleGraph.induce_adj.mpr <| cubicOpenGraph_adj.mpr
    ⟨huvCubic, heOpen, heInternal⟩

theorem finiteBoxOpenGraph_reachable_internalized_of_region_eq
    {d m n : ℕ} {R : Finset (Cubic d)} {omega : EdgeConfiguration d}
    (hregion : restartExploredRegion d omega m n = R)
    {z y : RestartBoxVertex d n}
    (hzSeed : z.1 ∈ cubicMetricBox d cubicOrigin m)
    (hzy : (finiteBoxOpenGraph d omega cubicOrigin n).Reachable z y) :
    (finiteBoxOpenGraph d (internalizedRestartConfiguration R n omega)
      cubicOrigin n).Reachable z y := by
  obtain ⟨w⟩ := hzy
  have convert : ∀ {u v : RestartBoxVertex d n},
      (finiteBoxOpenGraph d omega cubicOrigin n).Walk u v →
      (finiteBoxOpenGraph d omega cubicOrigin n).Reachable z u →
      Nonempty ((finiteBoxOpenGraph d (internalizedRestartConfiguration R n omega)
        cubicOrigin n).Walk u v) := by
    intro u v q hzu
    induction q with
    | nil => exact ⟨.nil⟩
    | @cons u v y huv tail ih =>
        have huR : u.1 ∈ R := by
          rw [← hregion, mem_restartExploredRegion_iff]
          exact ⟨u.2, z, hzSeed, hzu⟩
        have hzv := hzu.trans huv.reachable
        have hvR : v.1 ∈ R := by
          rw [← hregion, mem_restartExploredRegion_iff]
          exact ⟨v.2, z, hzSeed, hzv⟩
        obtain ⟨tailInternal⟩ := ih hzv
        exact ⟨.cons (finiteBoxOpenGraph_internalized_adj huv huR hvR) tailInternal⟩
  exact convert w ⟨.nil⟩

theorem restartExploredRegion_internalized_eq_of_eq
    {d m n : ℕ} {R : Finset (Cubic d)} {omega : EdgeConfiguration d}
    (hregion : restartExploredRegion d omega m n = R) :
    restartExploredRegion d (internalizedRestartConfiguration R n omega) m n = R := by
  apply Finset.Subset.antisymm
  · intro y hy
    obtain ⟨hyBox, z, hzSeed, hzy⟩ := mem_restartExploredRegion_iff.mp hy
    have hsub : internalizedRestartConfiguration R n omega ⊆ omega := Set.inter_subset_left
    rw [← hregion, mem_restartExploredRegion_iff]
    exact ⟨hyBox, z, hzSeed, hzy.mono (finiteBoxOpenGraph_mono_of_subset hsub)⟩
  · intro y hyR
    have hyFull : y ∈ restartExploredRegion d omega m n := hregion.symm ▸ hyR
    obtain ⟨hyBox, z, hzSeed, hzy⟩ := mem_restartExploredRegion_iff.mp hyFull
    rw [mem_restartExploredRegion_iff]
    exact ⟨hyBox, z, hzSeed,
      finiteBoxOpenGraph_reachable_internalized_of_region_eq hregion hzSeed hzy⟩

theorem closedEdgeSetEvent_of_restartExploredRegion_eq
    {d m n : ℕ} {R : Finset (Cubic d)} {omega : EdgeConfiguration d}
    (hregion : restartExploredRegion d omega m n = R) :
    omega ∈ closedEdgeSetEvent d (cubicRegionBoundaryEdgesWithinBox d R n) := by
  rw [mem_closedEdgeSetEvent, Set.disjoint_left]
  intro e heBoundary heOpen
  have heActual : e ∈ cubicRegionBoundaryEdgesWithinBox d
      (restartExploredRegion d omega m n) n := hregion ▸ heBoundary
  exact (restartExploredRegion_boundary_not_open heActual) heOpen

theorem restartExploredRegion_eq_of_internalized_eq_of_boundaryClosed
    {d m n : ℕ} {R : Finset (Cubic d)} {omega : EdgeConfiguration d}
    (hseed : cubicMetricBox d cubicOrigin m ⊆ R)
    (hInternal : restartExploredRegion d
      (internalizedRestartConfiguration R n omega) m n = R)
    (hclosed : omega ∈ closedEdgeSetEvent d
      (cubicRegionBoundaryEdgesWithinBox d R n)) :
    restartExploredRegion d omega m n = R := by
  apply Finset.Subset.antisymm
  · intro y hy
    obtain ⟨_, z, hzSeed, ⟨w⟩⟩ := mem_restartExploredRegion_iff.mp hy
    exact finiteBoxOpenWalk_endpoint_mem_of_boundary_closed hclosed (hseed hzSeed) w
  · intro y hyR
    have hyInternal : y ∈ restartExploredRegion d
        (internalizedRestartConfiguration R n omega) m n := hInternal.symm ▸ hyR
    obtain ⟨hyBox, z, hzSeed, hzy⟩ := mem_restartExploredRegion_iff.mp hyInternal
    rw [mem_restartExploredRegion_iff]
    exact ⟨hyBox, z, hzSeed,
      hzy.mono (finiteBoxOpenGraph_mono_of_subset Set.inter_subset_left)⟩

/-- Freezing `R` splits its exact realization into an internal-edge event and closure of its
edge boundary.  This is the deterministic factorization used by the random reveal cells. -/
theorem restartExploredRegion_eq_iff_internal_and_boundaryClosed
    {d m n : ℕ} {R : Finset (Cubic d)} {omega : EdgeConfiguration d}
    (hseed : cubicMetricBox d cubicOrigin m ⊆ R) :
    restartExploredRegion d omega m n = R ↔
      restartExploredRegion d (internalizedRestartConfiguration R n omega) m n = R ∧
        omega ∈ closedEdgeSetEvent d (cubicRegionBoundaryEdgesWithinBox d R n) := by
  constructor
  · intro hregion
    exact ⟨restartExploredRegion_internalized_eq_of_eq hregion,
      closedEdgeSetEvent_of_restartExploredRegion_eq hregion⟩
  · rintro ⟨hInternal, hclosed⟩
    exact restartExploredRegion_eq_of_internalized_eq_of_boundaryClosed
      hseed hInternal hclosed

theorem mem_boundaryClosedHistoryEvent_iff_threshold_closedEdgeSetEvent
    {d : ℕ} {E : Finset (CubicEdge d)} {beta : CubicEdge d → I}
    {X : CubicEdge d → ℝ} :
    X ∈ boundaryClosedHistoryEvent E beta ↔
      heterogeneousThresholdConfiguration beta X ∈ closedEdgeSetEvent d E := by
  rw [mem_closedEdgeSetEvent, Set.disjoint_left]
  constructor
  · intro hclosed e heE heOpen
    exact (not_lt_of_ge (hclosed e heE)) heOpen
  · intro hclosed e heE
    exact not_lt.mp fun heOpen => hclosed heE heOpen

/-- Exact label-space factorization of a frozen explored-region fiber. -/
theorem restartInternalRegionLabelEvent_inter_boundaryClosed
    {d m n : ℕ} (R : Finset (Cubic d)) (beta : CubicEdge d → I)
    (hseed : cubicMetricBox d cubicOrigin m ⊆ R) :
    restartInternalRegionLabelEvent R m n beta ∩
        boundaryClosedHistoryEvent
          (cubicRegionBoundaryEdgesWithinBox d R n) beta =
      {X | restartExploredRegion d
        (heterogeneousThresholdConfiguration beta X) m n = R} := by
  ext X
  simp only [Set.mem_inter_iff, restartInternalRegionLabelEvent,
    Set.mem_preimage, restartInternalRegionEvent, Set.mem_setOf_eq]
  rw [mem_boundaryClosedHistoryEvent_iff_threshold_closedEdgeSetEvent]
  exact (restartExploredRegion_eq_iff_internal_and_boundaryClosed hseed).symm

/-! ## Exact finite reveal-cell fibers -/

/-- The schedule cell actually realized by common-uniform labels at the current heterogeneous
threshold profile. -/
noncomputable def realizedScheduleRevealCell
    {d m n : ℕ} (i : Fin d) (beta : CubicEdge d → I)
    (S : FiniteRevealSchedule (CubicEdge d))
    (hS : S.HasOverlapBound (2 * d + 1))
    (X : CubicEdge d → ℝ) : RestartRevealCellIndex d i m n :=
  RestartRevealCellIndex.ofScheduleExploredRegion i
    (heterogeneousThresholdConfiguration beta X) S hS

@[simp]
theorem realizedScheduleRevealCell_regionVertices
    {d m n : ℕ} (i : Fin d) (beta : CubicEdge d → I)
    (S : FiniteRevealSchedule (CubicEdge d))
    (hS : S.HasOverlapBound (2 * d + 1))
    (X : CubicEdge d → ℝ) :
    (realizedScheduleRevealCell (m := m) (n := n) i beta S hS X).regionVertices =
      restartExploredRegion d (heterogeneousThresholdConfiguration beta X) m n := by
  rfl

theorem realizedScheduleRevealCell_eq_iff
    {d m n : ℕ} (i : Fin d) (beta : CubicEdge d → I)
    (S : FiniteRevealSchedule (CubicEdge d))
    (hS : S.HasOverlapBound (2 * d + 1))
    (X Y : CubicEdge d → ℝ) :
    realizedScheduleRevealCell (m := m) (n := n) i beta S hS X =
        realizedScheduleRevealCell i beta S hS Y ↔
      restartExploredRegion d (heterogeneousThresholdConfiguration beta X) m n =
        restartExploredRegion d (heterogeneousThresholdConfiguration beta Y) m n := by
  constructor
  · intro h
    exact congrArg RestartRevealCellIndex.regionVertices h
  · intro hregion
    unfold realizedScheduleRevealCell
    unfold RestartRevealCellIndex.ofScheduleExploredRegion
    unfold RestartRevealCellIndex.ofExploredRegion
    congr 1
    exact (Finset.map_injective (Function.Embedding.subtype _)) hregion

/-- An exact schedule-cell fiber is exactly the corresponding explored-region fiber. -/
theorem exactRevealCellEvent_realizedScheduleRevealCell
    {d m n : ℕ} (i : Fin d) (beta : CubicEdge d → I)
    (S : FiniteRevealSchedule (CubicEdge d))
    (hS : S.HasOverlapBound (2 * d + 1))
    (history : Set (CubicEdge d → ℝ)) (X0 : CubicEdge d → ℝ) :
    exactRevealCellEvent history
        (realizedScheduleRevealCell (m := m) (n := n) i beta S hS)
        (realizedScheduleRevealCell i beta S hS X0) =
      history ∩ {X | restartExploredRegion d
        (heterogeneousThresholdConfiguration beta X) m n =
          restartExploredRegion d
            (heterogeneousThresholdConfiguration beta X0) m n} := by
  ext X
  simp only [exactRevealCellEvent, Set.mem_inter_iff, Set.mem_setOf_eq]
  exact and_congr Iff.rfl
    (realizedScheduleRevealCell_eq_iff i beta S hS X X0)

/-- The exact factorization required by
`PartitionedOrientedRestartStage.ofFiniteRealization`: the outer history and internal-region
information form the independent past, while the current boundary closure is left to Lemma
7.17. -/
theorem exactRevealCellEvent_eq_past_inter_boundary
    {d m n : ℕ} (i : Fin d) (beta : CubicEdge d → I)
    (S : FiniteRevealSchedule (CubicEdge d))
    (hS : S.HasOverlapBound (2 * d + 1))
    (history : Set (CubicEdge d → ℝ)) (X0 : CubicEdge d → ℝ)
    (hmn : m ≤ n) :
    (history ∩ restartInternalRegionLabelEvent
          (restartExploredRegion d
            (heterogeneousThresholdConfiguration beta X0) m n) m n beta) ∩
        boundaryClosedHistoryEvent
          (cubicRegionBoundaryEdgesWithinBox d
            (restartExploredRegion d
              (heterogeneousThresholdConfiguration beta X0) m n) n) beta =
      exactRevealCellEvent history
        (realizedScheduleRevealCell (m := m) (n := n) i beta S hS)
        (realizedScheduleRevealCell i beta S hS X0) := by
  let R := restartExploredRegion d
    (heterogeneousThresholdConfiguration beta X0) m n
  have hseed : cubicMetricBox d cubicOrigin m ⊆ R :=
    cubicMetricBox_subset_restartExploredRegion hmn
  rw [Set.inter_assoc, restartInternalRegionLabelEvent_inter_boundaryClosed R beta hseed]
  exact (exactRevealCellEvent_realizedScheduleRevealCell
    i beta S hS history X0).symm

end Percolation
