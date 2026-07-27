import Percolation.Critical.DynamicRevealCells
import Percolation.Critical.StaticBlocks

/-!
# The finite explored region of a dynamic restart

For a fixed heterogeneous edge configuration, the explored region is the union of all open
components inside `B(n)` which meet the inlet seed box `B(m)`.  This file proves the deterministic
fact needed to identify an exact reveal fiber with a closed-boundary history: every internal
box edge leaving the explored region is closed.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval

/-- Threshold every edge at its own density. -/
def heterogeneousThresholdConfiguration {ι : Type*}
    (beta : ι → I) (X : ι → ℝ) : Set ι :=
  {e | X e < (beta e : ℝ)}

theorem measurable_heterogeneousThresholdConfiguration {ι : Type*}
    (beta : ι → I) :
    Measurable (heterogeneousThresholdConfiguration beta : (ι → ℝ) → Set ι) := by
  change Measurable
    ((fun P : ι → Prop => {i | P i}) ∘
      fun (X : ι → ℝ) (e : ι) => (X e < (beta e : ℝ) : Prop))
  refine Measurable.comp (by fun_prop) ?_
  exact measurable_pi_lambda _ fun e =>
    (measurable_lt_prop _).comp (measurable_pi_apply e)

@[simp]
theorem mem_heterogeneousThresholdConfiguration_iff
    {ι : Type*} {beta : ι → I} {X : ι → ℝ} {e : ι} :
    e ∈ heterogeneousThresholdConfiguration beta X ↔ X e < (beta e : ℝ) :=
  Iff.rfl

/-- Box-subtype vertices reachable by an open path from some inlet-seed vertex. -/
noncomputable def restartReachableBoxVertices
    (d : ℕ) (omega : EdgeConfiguration d) (m n : ℕ) :
    Finset (RestartBoxVertex d n) := by
  classical
  let G := finiteBoxOpenGraph d omega cubicOrigin n
  exact Finset.univ.filter fun y =>
    ∃ z : RestartBoxVertex d n,
      z.1 ∈ cubicMetricBox d cubicOrigin m ∧ G.Reachable z y

/-- Ambient form of the explored restart region. -/
noncomputable def restartExploredRegion
    (d : ℕ) (omega : EdgeConfiguration d) (m n : ℕ) : Finset (Cubic d) :=
  (restartReachableBoxVertices d omega m n).map (Function.Embedding.subtype _)

@[simp]
theorem mem_restartReachableBoxVertices_iff
    {d m n : ℕ} {omega : EdgeConfiguration d} {y : RestartBoxVertex d n} :
    y ∈ restartReachableBoxVertices d omega m n ↔
      ∃ z : RestartBoxVertex d n,
        z.1 ∈ cubicMetricBox d cubicOrigin m ∧
          (finiteBoxOpenGraph d omega cubicOrigin n).Reachable z y := by
  classical
  simp [restartReachableBoxVertices]

@[simp]
theorem mem_restartExploredRegion_iff
    {d m n : ℕ} {omega : EdgeConfiguration d} {y : Cubic d} :
    y ∈ restartExploredRegion d omega m n ↔
      ∃ hy : y ∈ cubicMetricBox d cubicOrigin n,
        ∃ z : RestartBoxVertex d n,
          z.1 ∈ cubicMetricBox d cubicOrigin m ∧
            (finiteBoxOpenGraph d omega cubicOrigin n).Reachable z ⟨y, hy⟩ := by
  classical
  simp [restartExploredRegion]

theorem restartExploredRegion_subset_box
    (d : ℕ) (omega : EdgeConfiguration d) (m n : ℕ) :
    restartExploredRegion d omega m n ⊆ cubicMetricBox d cubicOrigin n := by
  intro y hy
  exact (mem_restartExploredRegion_iff.mp hy).choose

theorem cubicMetricBox_subset_restartExploredRegion
    {d m n : ℕ} {omega : EdgeConfiguration d} (hmn : m ≤ n) :
    cubicMetricBox d cubicOrigin m ⊆ restartExploredRegion d omega m n := by
  intro y hym
  have hyn : y ∈ cubicMetricBox d cubicOrigin n := by
    rw [mem_cubicMetricBox] at hym ⊢
    intro j
    have hj := hym j
    omega
  rw [mem_restartExploredRegion_iff]
  refine ⟨hyn, ⟨y, hyn⟩, hym, ?_⟩
  exact ⟨SimpleGraph.Walk.nil⟩

/-- Every edge of the internal boundary of the explored region is closed in the configuration
used to construct that region. -/
theorem restartExploredRegion_boundary_not_open
    {d m n : ℕ} {omega : EdgeConfiguration d} {e : CubicEdge d}
    (he : e ∈ cubicRegionBoundaryEdgesWithinBox d
      (restartExploredRegion d omega m n) n) :
    e ∉ omega := by
  intro heOpen
  let x := cubicRegionBoundaryInsideEndpoint
    (restartExploredRegion d omega m n) e
  let y := cubicRegionBoundaryOutsideEndpoint
    (restartExploredRegion d omega m n) e
  have hxR : x ∈ restartExploredRegion d omega m n :=
    cubicRegionBoundaryInsideEndpoint_mem he
  have hyR : y ∉ restartExploredRegion d omega m n :=
    cubicRegionBoundaryOutsideEndpoint_not_mem he
  obtain ⟨hxBox, z, hzSeed, hzx⟩ := mem_restartExploredRegion_iff.mp hxR
  have hyEdge : y ∈ (e : Sym2 (Cubic d)) := by
    rw [← cubicRegionBoundaryEndpoints_edge he]
    simp [y]
  have hyBox : y ∈ cubicMetricBox d cubicOrigin n :=
    endpoint_mem_cubicMetricBox_of_edge_mem_cubicBoxEdges
      (mem_cubicRegionBoundaryEdgesWithinBox_iff.mp he).1 hyEdge
  have hadjCubic : (cubicGraph d).Adj x y := by
    rw [← (cubicGraph d).mem_edgeSet]
    rw [cubicRegionBoundaryEndpoints_edge he]
    exact e.2
  have hadjOpen : (finiteBoxOpenGraph d omega cubicOrigin n).Adj
      (⟨x, hxBox⟩ : RestartBoxVertex d n) ⟨y, hyBox⟩ := by
    let f : CubicEdge d :=
      ⟨s(x, y), (cubicGraph d).mem_edgeSet.mpr hadjCubic⟩
    have hfe : f = e := by
      apply Subtype.ext
      exact cubicRegionBoundaryEndpoints_edge he
    have hfOpen : f ∈ omega := by simpa [hfe] using heOpen
    exact cubicOpenGraph_adj.mpr ⟨hadjCubic, by simpa [f] using hfOpen⟩
  have hzy : (finiteBoxOpenGraph d omega cubicOrigin n).Reachable z ⟨y, hyBox⟩ :=
    hzx.trans hadjOpen.reachable
  apply hyR
  rw [mem_restartExploredRegion_iff]
  exact ⟨hyBox, z, hzSeed, hzy⟩

/-- In common-uniform labels, the explored region's boundary is exactly closed at its
heterogeneous current thresholds. -/
theorem restartExploredRegion_mem_boundaryClosedHistoryEvent
    {d m n : ℕ} (beta : CubicEdge d → I) (X : CubicEdge d → ℝ) :
    X ∈ boundaryClosedHistoryEvent
      (cubicRegionBoundaryEdgesWithinBox d
        (restartExploredRegion d (heterogeneousThresholdConfiguration beta X) m n) n)
      beta := by
  intro e he
  exact not_lt.mp (restartExploredRegion_boundary_not_open he)

/-- Package an actually explored region together with the already accumulated finite
multiplicity profile. -/
noncomputable def RestartRevealCellIndex.ofExploredRegion
    {d m n : ℕ} (i : Fin d) (omega : EdgeConfiguration d)
    (multiplicity : RestartSupportCoordinate d i m n → Fin (2 * d + 2)) :
    RestartRevealCellIndex d i m n where
  region := restartReachableBoxVertices d omega m n
  multiplicity := multiplicity

@[simp]
theorem RestartRevealCellIndex.regionVertices_ofExploredRegion
    {d m n : ℕ} (i : Fin d) (omega : EdgeConfiguration d)
    (multiplicity : RestartSupportCoordinate d i m n → Fin (2 * d + 2)) :
    (RestartRevealCellIndex.ofExploredRegion i omega multiplicity).regionVertices =
      restartExploredRegion d omega m n := by
  rfl

/-- The realized explored-region cell automatically supplies the closed-boundary part of the
restart history. -/
theorem RestartRevealCellIndex.ofExploredRegion_boundary_closed
    {d m n : ℕ} (i : Fin d) (beta : CubicEdge d → I) (X : CubicEdge d → ℝ)
    (multiplicity : RestartSupportCoordinate d i m n → Fin (2 * d + 2)) :
    X ∈ boundaryClosedHistoryEvent
      (cubicRegionBoundaryEdgesWithinBox d
        (RestartRevealCellIndex.ofExploredRegion i
          (heterogeneousThresholdConfiguration beta X) multiplicity).regionVertices n)
      beta := by
  simpa using restartExploredRegion_mem_boundaryClosedHistoryEvent
    (m := m) (n := n) beta X

end Percolation
