import Percolation.Critical.DynamicRootEdgeState
import Percolation.Critical.DynamicRecursiveEdgeState

/-!
# Root state for recursive dynamic exploration

This file identifies the concrete first radial update with the canonical recursive state whose
closed support is its actual line-graph boundary.  It is the deterministic handoff from the
special root construction (7.28)--(7.32) to the repeated post-radial and later-site updates.
-/

namespace Percolation

open scoped unitInterval

/-- In positive dimension and for a nontrivial seed box, every vertex-region boundary edge is
line-adjacent to an internal seed edge. -/
theorem rootInitialBoundaryEdges_subset_rootEdgeLineBoundary
    {d m n : ℕ} [NeZero d] (hm : 1 ≤ m) :
    rootInitialBoundaryEdges d m n ⊆
      cubicEdgeBoundaryWithin (rootInitialExploredEdges d m)
        (rootRadialEdgeSupport d m n) := by
  classical
  intro f hf
  let R := cubicMetricBox d cubicOrigin m
  change f ∈ cubicRegionBoundaryEdgesWithinBox d R n at hf
  let x := cubicRegionBoundaryInsideEndpoint R f
  have hxR : x ∈ R := cubicRegionBoundaryInsideEndpoint_mem hf
  have hxf : x ∈ (f : Sym2 (Cubic d)) := by
    rw [← cubicRegionBoundaryEndpoints_edge hf]
    simp [x]
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  let i : Fin d := ⟨0, hd⟩
  let positive : Bool := decide (x i < (m : ℤ))
  let a : CubicDirection d := (i, positive)
  let y := cubicStepFrom x a
  have hyR : y ∈ R := by
    rw [mem_cubicMetricBox]
    intro j
    have hxj := mem_cubicMetricBox.mp hxR j
    simp [cubicOrigin] at hxj ⊢
    by_cases hji : j = i
    · subst j
      by_cases hlt : x i < (m : ℤ)
      · simp [y, a, positive, hlt, cubicStepFrom, cubicDirectionIncrement]
        omega
      · simp [y, a, positive, hlt, cubicStepFrom, cubicDirectionIncrement]
        omega
    · simp [y, a, cubicStepFrom, hji]
      exact hxj
  let e : CubicEdge d := cubicStepEdge x a
  have heInitial : e ∈ rootInitialExploredEdges d m :=
    cubicStepEdge_mem_cubicBoxEdges hxR hyR
  have hfe : (cubicEdgeLineGraph d).Adj e f := by
    refine ⟨?_, x, ?_, hxf⟩
    · intro hef
      apply (mem_cubicRegionBoundaryEdgesWithinBox_iff.mp hf).2.elim
      · intro h
        exact h.2 (endpoint_mem_cubicMetricBox_of_edge_mem_cubicBoxEdges
          (hef ▸ heInitial) (Sym2.out_snd_mem f.1))
      · intro h
        exact h.2 (endpoint_mem_cubicMetricBox_of_edge_mem_cubicBoxEdges
          (hef ▸ heInitial) (Sym2.out_fst_mem f.1))
    · simp [e, cubicStepEdge]
  rw [mem_cubicEdgeBoundaryWithin_iff]
  exact ⟨rootInitialBoundaryEdges_subset_rootRadialEdgeSupport d m n hf,
    fun hfInitial ↦ Finset.disjoint_left.mp
      (disjoint_rootInitialBoundaryEdges_rootInitialExploredEdges d m n) hf hfInitial,
    e, heInitial, hfe⟩

theorem rootEdgeLineBoundary_eq_rootInitialBoundaryEdges
    {d m n : ℕ} [NeZero d] (hm : 1 ≤ m) (hmn : m + 1 ≤ n) :
    cubicEdgeBoundaryWithin (rootInitialExploredEdges d m)
        (rootRadialEdgeSupport d m n) =
      rootInitialBoundaryEdges d m n := by
  apply Finset.Subset.antisymm
  · exact rootEdgeLineBoundary_subset_rootInitialBoundaryEdges hmn
  · exact rootInitialBoundaryEdges_subset_rootEdgeLineBoundary hm

/-- Canonical recursive state immediately after the simultaneous radial phase. -/
noncomputable def rootPostRadialEdgeState
    (d m n : ℕ) (p incremented : I) (X : CubicEdge d → ℝ) :
    FiniteEdgeRevealState d where
  ambient := rootRadialEdgeSupport d m n
  explored := rootRadialExploredEdges d m n p incremented X
  lower := (rootRadialRevealThresholdUpdate d m n p incremented X).updatedLower
  upper := (rootRadialRevealThresholdUpdate d m n p incremented X).updatedUpper

theorem rootRadial_updatedClosedSupport_eq_newBoundary
    {d m n : ℕ} [NeZero d] (hm : 1 ≤ m) (hmn : m + 1 ≤ n)
    (p incremented : I) (X : CubicEdge d → ℝ) :
    (rootRadialRevealThresholdUpdate d m n p incremented X).updatedClosedSupport =
      rootRadialNewBoundaryEdges d m n p incremented X := by
  change rootInitialBoundaryEdges d m n \
        rootRadialExploredEdges d m n p incremented X ∪
      ((rootRadialNewBoundaryEdges d m n p incremented X \
        rootInitialBoundaryEdges d m n) ∩ rootRadialEdgeSupport d m n) =
      rootRadialNewBoundaryEdges d m n p incremented X
  rw [rootRadialNewBoundaryEdges]
  rw [← rootEdgeLineBoundary_eq_rootInitialBoundaryEdges hm hmn]
  exact edgeBoundary_sdiff_update_eq
    (rootInitialExploredEdges d m)
    (rootRadialExploredEdges d m n p incremented X)
    (rootRadialEdgeSupport d m n)
    (rootInitialExploredEdges_subset_rootRadialExploredEdges d m n p incremented X)

/-- The canonical recursive profile is exactly the first-update interval profile. -/
theorem rootPostRadial_profile_eq_updatedProfile
    {d m n : ℕ} [NeZero d] (hm : 1 ≤ m) (hmn : m + 1 ≤ n)
    (p incremented : I) (X : CubicEdge d → ℝ) :
    (rootPostRadialEdgeState d m n p incremented X).profile =
      (rootRadialRevealThresholdUpdate d m n p incremented X).updatedProfile := by
  unfold FiniteEdgeRevealState.profile rootPostRadialEdgeState
    FiniteEdgeRevealState.boundary
  rw [show cubicEdgeBoundaryWithin
      (rootRadialExploredEdges d m n p incremented X)
      (rootRadialEdgeSupport d m n) =
      (rootRadialRevealThresholdUpdate d m n p incremented X).updatedClosedSupport by
    exact (rootRadial_updatedClosedSupport_eq_newBoundary hm hmn p incremented X).symm]
  rfl

/-- Every radial-event realization initializes the recursive interval invariant. -/
theorem rootRadialEvent_subset_postRadialProfile
    {d m n : ℕ} [NeZero d] (hm : 1 ≤ m) (hmn : m + 1 ≤ n)
    (p incremented : I) (delta : ℝ) :
    rootRadialEvent d m n p delta ⊆
      {X | X ∈ (rootPostRadialEdgeState d m n p incremented X).profile.event} := by
  intro X hX
  change X ∈ (rootPostRadialEdgeState d m n p incremented X).profile.event
  rw [rootPostRadial_profile_eq_updatedProfile hm hmn p incremented X]
  exact rootRadialExploredEdges_mem_updatedProfile hmn p incremented X hX.1

end Percolation
