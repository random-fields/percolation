import Percolation.Extensions.Invasion

/-!
# Deterministic sublevel-cluster capture for invasion percolation

The probabilistic input to Grimmett's (12.29) is that the invasion eventually meets an infinite
`y`-open cluster.  This file proves the exact deterministic consequence: from that stage onward
every greedily chosen label is at most `y`.
-/

namespace Percolation

open Set

/-- Bonds whose invasion labels do not exceed a fixed level. -/
def invasionSublevelConfiguration {d : ℕ} (label : CubicEdge d → ℝ) (y : ℝ) :
    EdgeConfiguration d :=
  {e | label e ≤ y}

private theorem walkIsOpen_tail_of_cons {d : ℕ} {ω : EdgeConfiguration d}
    {u v z : Cubic d} {h : (cubicGraph d).Adj u v}
    {w : (cubicGraph d).Walk v z}
    (hopen : walkIsOpen ω (SimpleGraph.Walk.cons h w)) : walkIsOpen ω w := by
  intro e he
  exact hopen e (by simp [he])

/-- An open walk which exits a finite edge-closed invasion state contains a frontier edge, and
that frontier edge is open in the supplied configuration. -/
theorem InvasionState.exists_frontier_mem_of_open_walk_leaves {d : ℕ}
    (S : InvasionState d) (hclosed : S.EdgeClosed) {ω : EdgeConfiguration d}
    {x z : Cubic d} (hx : x ∈ S.vertices) (hz : z ∉ S.vertices)
    (w : (cubicGraph d).Walk x z) (hopen : walkIsOpen ω w) :
    ∃ e ∈ S.frontier, e ∈ ω := by
  induction w with
  | nil => exact (hz hx).elim
  | @cons u v z huv p ih =>
      by_cases hv : v ∈ S.vertices
      · exact ih hv hz (walkIsOpen_tail_of_cons hopen)
      · let e : CubicEdge d :=
          ⟨s(u, v), (SimpleGraph.mem_edgeSet (cubicGraph d)).2 huv⟩
        have heIncident : e ∈ cubicIncidentEdges d S.vertices := by
          apply mem_cubicIncidentEdges_of_endpoint hx
          simp [e]
        have heNotSelected : e ∉ S.edges := by
          intro he
          exact hv (hclosed e he v (by simp [e]))
        refine ⟨e, Finset.mem_sdiff.mpr ⟨heIncident, heNotSelected⟩, ?_⟩
        exact hopen s(u, v) (by simp [e])

/-- If the current invaded vertex set meets an infinite `y`-open cluster, its frontier contains
a bond of label at most `y`. -/
theorem InvasionState.exists_frontier_label_le_of_meets_infiniteSublevelCluster
    {d : ℕ} (S : InvasionState d) (hclosed : S.EdgeClosed)
    (label : CubicEdge d → ℝ) (y : ℝ)
    {x : Cubic d} (hxS : x ∈ S.vertices)
    (hinfinite : (cubicOpenClusterFrom d (invasionSublevelConfiguration label y) x).Infinite) :
    ∃ e ∈ S.frontier, label e ≤ y := by
  have hnotSubset : ¬cubicOpenClusterFrom d (invasionSublevelConfiguration label y) x ⊆
      (S.vertices : Set (Cubic d)) := by
    intro hsubset
    exact hinfinite (S.vertices.finite_toSet.subset hsubset)
  obtain ⟨z, hzCluster, hzS⟩ := Set.not_subset.mp hnotSubset
  rcases hzCluster with ⟨w, hopen⟩
  obtain ⟨e, heFrontier, heOpen⟩ :=
    S.exists_frontier_mem_of_open_walk_leaves hclosed hxS hzS w hopen
  exact ⟨e, heFrontier, heOpen⟩

/-- The greedy edge chosen from a state meeting an infinite sublevel cluster has label at most
that level. -/
theorem invasionEdge_label_le_of_state_meets_infiniteSublevelCluster
    {d : ℕ} (hd : 0 < d) (label : CubicEdge d → ℝ) (y : ℝ) (n : ℕ)
    {x : Cubic d} (hxS : x ∈ (invasionState label n).vertices)
    (hinfinite : (cubicOpenClusterFrom d (invasionSublevelConfiguration label y) x).Infinite) :
    label (invasionEdge hd label n) ≤ y := by
  obtain ⟨e, heFrontier, hey⟩ :=
    (invasionState label n).exists_frontier_label_le_of_meets_infiniteSublevelCluster
      (invasionState_edgeClosed label n) label y hxS hinfinite
  exact (invasionLeastEdge_label_le label _
    (invasionState_frontier_nonempty hd label n) heFrontier).trans hey

theorem invasionState_vertices_mono_nat {d : ℕ} (label : CubicEdge d → ℝ) :
    Monotone fun n ↦ (invasionState label n).vertices := by
  intro n m hnm
  induction m, hnm using Nat.le_induction with
  | base => exact Finset.Subset.rfl
  | succ m hnm ih =>
      exact ih.trans (invasionStep_vertices_mono label (invasionState label m))

/-- Once an infinite sublevel cluster has been hit, every later selected label stays below that
level. -/
theorem invasionEdge_eventually_label_le_of_state_meets_infiniteSublevelCluster
    {d : ℕ} (hd : 0 < d) (label : CubicEdge d → ℝ) (y : ℝ) (N : ℕ)
    {x : Cubic d} (hxS : x ∈ (invasionState label N).vertices)
    (hinfinite : (cubicOpenClusterFrom d (invasionSublevelConfiguration label y) x).Infinite) :
    ∀ n, N ≤ n → label (invasionEdge hd label n) ≤ y := by
  intro n hNn
  exact invasionEdge_label_le_of_state_meets_infiniteSublevelCluster hd label y n
    (invasionState_vertices_mono_nat label hNn hxS) hinfinite

end Percolation
