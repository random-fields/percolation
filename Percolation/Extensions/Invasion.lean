import Percolation.Critical.DynamicEdgeExploration
import Mathlib.Data.Finset.Max

/-!
# Deterministic invasion percolation

The probabilistic limit theorems (12.29)--(12.30) rest on a completely deterministic greedy
process.  This file defines that process on the cubic lattice, including a fixed enumeration used
only to break label ties.
-/

namespace Percolation

open Set

/-- A finite stage of invasion: the vertices reached so far and the selected edges. -/
structure InvasionState (d : ℕ) where
  vertices : Finset (Cubic d)
  edges : Finset (CubicEdge d)

/-- Edges incident to the current vertex set which have not yet been selected. -/
noncomputable def InvasionState.frontier {d : ℕ} (S : InvasionState d) :
    Finset (CubicEdge d) :=
  cubicIncidentEdges d S.vertices \ S.edges

/-- A canonical injective code for cubic edges. -/
noncomputable def cubicEdgeCode {d : ℕ} (e : CubicEdge d) : ℕ := by
  letI := Encodable.ofCountable (CubicEdge d)
  exact Encodable.encode e

theorem cubicEdgeCode_injective {d : ℕ} :
    Function.Injective (cubicEdgeCode : CubicEdge d → ℕ) := by
  letI := Encodable.ofCountable (CubicEdge d)
  exact Encodable.encode_injective

/-- Lexicographic key: the edge label first, the canonical code only on a tie. -/
noncomputable def invasionKey {d : ℕ} (label : CubicEdge d → ℝ)
    (e : CubicEdge d) : Lex (ℝ × ℕ) :=
  toLex (label e, cubicEdgeCode e)

theorem invasionKey_injective {d : ℕ} (label : CubicEdge d → ℝ) :
    Function.Injective (invasionKey label) := by
  intro e f h
  apply cubicEdgeCode_injective
  exact congrArg Prod.snd h

/-- Least-labelled edge of a nonempty finite frontier, with canonical tie-breaking. -/
noncomputable def invasionLeastEdge {d : ℕ} (label : CubicEdge d → ℝ)
    (B : Finset (CubicEdge d)) (hB : B.Nonempty) : CubicEdge d := by
  letI : LinearOrder (CubicEdge d) :=
    LinearOrder.lift' (invasionKey label) (invasionKey_injective label)
  exact B.min' hB

theorem invasionLeastEdge_mem {d : ℕ} (label : CubicEdge d → ℝ)
    (B : Finset (CubicEdge d)) (hB : B.Nonempty) :
    invasionLeastEdge label B hB ∈ B := by
  letI : LinearOrder (CubicEdge d) :=
    LinearOrder.lift' (invasionKey label) (invasionKey_injective label)
  exact Finset.min'_mem B hB

/-- The chosen edge has label no larger than any other frontier label.  The enumeration affects
only the equal-label branch of the lexicographic order. -/
theorem invasionLeastEdge_label_le {d : ℕ} (label : CubicEdge d → ℝ)
    (B : Finset (CubicEdge d)) (hB : B.Nonempty) {e : CubicEdge d} (he : e ∈ B) :
    label (invasionLeastEdge label B hB) ≤ label e := by
  letI : LinearOrder (CubicEdge d) :=
    LinearOrder.lift' (invasionKey label) (invasionKey_injective label)
  have hle := Finset.min'_le B e he
  change invasionKey label (invasionLeastEdge label B hB) ≤ invasionKey label e at hle
  rw [invasionKey, invasionKey, Prod.Lex.toLex_le_toLex] at hle
  rcases hle with hlt | ⟨heq, _⟩
  · exact hlt.le
  · exact heq.le

/-- Add one frontier edge and both of its endpoints. -/
noncomputable def InvasionState.adjoinEdge {d : ℕ} (S : InvasionState d)
    (e : CubicEdge d) : InvasionState d where
  vertices := S.vertices ∪ cubicEdgeEndpointVertices {e}
  edges := insert e S.edges

/-- One total greedy step.  The exhausted-frontier branch makes the recursion total; it is ruled
out for positive-dimensional cubic lattices by the frontier theorem below. -/
noncomputable def invasionNextEdge {d : ℕ} (label : CubicEdge d → ℝ)
    (S : InvasionState d) : Option (CubicEdge d) := by
  classical
  if hB : S.frontier.Nonempty then
    exact some (invasionLeastEdge label S.frontier hB)
  else
    exact none

noncomputable def invasionStep {d : ℕ} (label : CubicEdge d → ℝ)
    (S : InvasionState d) : InvasionState d := by
  classical
  match invasionNextEdge label S with
  | some e => exact S.adjoinEdge e
  | none => exact S

/-- Initial invasion state rooted at the origin. -/
def invasionInitialState (d : ℕ) : InvasionState d where
  vertices := {cubicOrigin}
  edges := ∅

/-- State after `n` greedy additions. -/
noncomputable def invasionState {d : ℕ} (label : CubicEdge d → ℝ) :
    ℕ → InvasionState d
  | 0 => invasionInitialState d
  | n + 1 => invasionStep label (invasionState label n)

/-- The finite invasion cluster after `n` steps. -/
noncomputable def invasionClusterAt {d : ℕ} (label : CubicEdge d → ℝ) (n : ℕ) :
    Finset (CubicEdge d) :=
  (invasionState label n).edges

/-- The infinite invasion cluster is the union of the finite stages. -/
noncomputable def invasionCluster {d : ℕ} (label : CubicEdge d → ℝ) :
    Set (CubicEdge d) :=
  ⋃ n : ℕ, (invasionClusterAt label n : Set (CubicEdge d))

/-- The edge selected at step `n`, if the frontier is nonempty. -/
noncomputable def invasionEdge? {d : ℕ} (label : CubicEdge d → ℝ) (n : ℕ) :
    Option (CubicEdge d) :=
  invasionNextEdge label (invasionState label n)

/-- Empirical distribution function of labels on the first `n` selected edges.  At `n=0` the
totalized quotient is zero; all limit theorems are stated at `atTop`. -/
noncomputable def invasionEmpiricalCDF {d : ℕ} (label : CubicEdge d → ℝ)
    (n : ℕ) (y : ℝ) : ℝ :=
  ((invasionClusterAt label n).filter fun e ↦ label e ≤ y).card / n

theorem invasionInitialState_origin_mem (d : ℕ) :
    cubicOrigin ∈ (invasionInitialState d).vertices := by simp [invasionInitialState]

theorem InvasionState.vertices_subset_adjoinEdge {d : ℕ} (S : InvasionState d)
    (e : CubicEdge d) : S.vertices ⊆ (S.adjoinEdge e).vertices := by
  intro x hx
  exact Finset.mem_union_left _ hx

theorem InvasionState.edges_subset_adjoinEdge {d : ℕ} (S : InvasionState d)
    (e : CubicEdge d) : S.edges ⊆ (S.adjoinEdge e).edges := by
  intro f hf
  exact Finset.mem_insert_of_mem hf

/-- Every selected edge has both endpoints in the recorded vertex set. -/
def InvasionState.EdgeClosed {d : ℕ} (S : InvasionState d) : Prop :=
  ∀ e ∈ S.edges, ∀ x, x ∈ (e.1 : Sym2 (Cubic d)) → x ∈ S.vertices

theorem invasionInitialState_edgeClosed (d : ℕ) :
    (invasionInitialState d).EdgeClosed := by
  intro e he
  simp [invasionInitialState] at he

theorem InvasionState.adjoinEdge_edgeClosed {d : ℕ} {S : InvasionState d}
    (hS : S.EdgeClosed) (e : CubicEdge d) : (S.adjoinEdge e).EdgeClosed := by
  intro f hf x hxf
  rw [InvasionState.adjoinEdge, Finset.mem_insert] at hf
  rw [InvasionState.adjoinEdge, Finset.mem_union]
  rcases hf with hfe | hf
  · right
    exact mem_cubicEdgeEndpointVertices_iff.mpr ⟨f, by simpa [hfe], hxf⟩
  · exact Or.inl (hS f hf x hxf)

/-- A finite nonempty edge-closed state in positive dimension always has a frontier edge. -/
theorem InvasionState.frontier_nonempty {d : ℕ} (hd : 0 < d)
    (S : InvasionState d) (hV : S.vertices.Nonempty) (hS : S.EdgeClosed) :
    S.frontier.Nonempty := by
  let i : Fin d := ⟨0, hd⟩
  obtain ⟨x, hx, hmax⟩ := Finset.exists_max_image S.vertices (fun z ↦ z i) hV
  let y := cubicStepFrom x (i, true)
  let e := cubicStepEdge x (i, true)
  have hyEdge : y ∈ (e.1 : Sym2 (Cubic d)) := by
    simp [e, y, cubicStepEdge]
  have hyNot : y ∉ S.vertices := by
    intro hy
    have hle := hmax y hy
    simp [y, cubicStepFrom, cubicDirectionIncrement] at hle
  have heNot : e ∉ S.edges := by
    intro he
    exact hyNot (hS e he y hyEdge)
  refine ⟨e, Finset.mem_sdiff.mpr ⟨?_, heNot⟩⟩
  exact cubicStepEdge_mem_cubicIncidentEdges hx (i, true)

theorem invasionStep_vertices_mono {d : ℕ} (label : CubicEdge d → ℝ)
    (S : InvasionState d) : S.vertices ⊆ (invasionStep label S).vertices := by
  classical
  unfold invasionStep
  split
  · exact S.vertices_subset_adjoinEdge _
  · exact Finset.Subset.rfl

theorem invasionStep_edges_mono {d : ℕ} (label : CubicEdge d → ℝ)
    (S : InvasionState d) : S.edges ⊆ (invasionStep label S).edges := by
  classical
  unfold invasionStep
  split
  · exact S.edges_subset_adjoinEdge _
  · exact Finset.Subset.rfl

theorem invasionState_vertices_nonempty {d : ℕ} (label : CubicEdge d → ℝ) :
    ∀ n, (invasionState label n).vertices.Nonempty
  | 0 => ⟨cubicOrigin, invasionInitialState_origin_mem d⟩
  | n + 1 =>
      (invasionState_vertices_nonempty label n).mono
        (invasionStep_vertices_mono label (invasionState label n))

theorem invasionState_edgeClosed {d : ℕ} (label : CubicEdge d → ℝ) :
    ∀ n, (invasionState label n).EdgeClosed
  | 0 => invasionInitialState_edgeClosed d
  | n + 1 => by
      rw [invasionState]
      unfold invasionStep
      split
      · exact InvasionState.adjoinEdge_edgeClosed
          (invasionState_edgeClosed label n) _
      · exact invasionState_edgeClosed label n

theorem invasionState_frontier_nonempty {d : ℕ} (hd : 0 < d)
    (label : CubicEdge d → ℝ) (n : ℕ) :
    (invasionState label n).frontier.Nonempty :=
  (invasionState label n).frontier_nonempty hd
    (invasionState_vertices_nonempty label n) (invasionState_edgeClosed label n)

theorem invasionNextEdge_eq_some_of_frontier_nonempty {d : ℕ}
    (label : CubicEdge d → ℝ) (S : InvasionState d) (hB : S.frontier.Nonempty) :
    invasionNextEdge label S = some (invasionLeastEdge label S.frontier hB) := by
  simp [invasionNextEdge, hB]

theorem invasionStep_eq_adjoinEdge_of_frontier_nonempty {d : ℕ}
    (label : CubicEdge d → ℝ) (S : InvasionState d) (hB : S.frontier.Nonempty) :
    invasionStep label S = S.adjoinEdge (invasionLeastEdge label S.frontier hB) := by
  unfold invasionStep
  rw [invasionNextEdge_eq_some_of_frontier_nonempty label S hB]

/-- In positive dimension the source-facing selected edge is total. -/
noncomputable def invasionEdge {d : ℕ} (hd : 0 < d)
    (label : CubicEdge d → ℝ) (n : ℕ) : CubicEdge d :=
  invasionLeastEdge label (invasionState label n).frontier
    (invasionState_frontier_nonempty hd label n)

theorem invasionEdge_mem_frontier {d : ℕ} (hd : 0 < d)
    (label : CubicEdge d → ℝ) (n : ℕ) :
    invasionEdge hd label n ∈ (invasionState label n).frontier :=
  invasionLeastEdge_mem label _ _

theorem invasionEdge_not_mem_clusterAt {d : ℕ} (hd : 0 < d)
    (label : CubicEdge d → ℝ) (n : ℕ) :
    invasionEdge hd label n ∉ invasionClusterAt label n := by
  exact (Finset.mem_sdiff.mp (invasionEdge_mem_frontier hd label n)).2

theorem invasionClusterAt_succ {d : ℕ} (hd : 0 < d)
    (label : CubicEdge d → ℝ) (n : ℕ) :
    invasionClusterAt label (n + 1) =
      insert (invasionEdge hd label n) (invasionClusterAt label n) := by
  rw [invasionClusterAt, invasionState,
    invasionStep_eq_adjoinEdge_of_frontier_nonempty label _
      (invasionState_frontier_nonempty hd label n)]
  rfl

/-- Exactly one previously unseen edge is invaded at every step. -/
theorem invasionClusterAt_card {d : ℕ} (hd : 0 < d)
    (label : CubicEdge d → ℝ) : ∀ n,
    (invasionClusterAt label n).card = n
  | 0 => by simp [invasionClusterAt, invasionState, invasionInitialState]
  | n + 1 => by
      rw [invasionClusterAt_succ hd, Finset.card_insert_of_notMem
        (invasionEdge_not_mem_clusterAt hd label n), invasionClusterAt_card hd label n]

@[simp]
theorem invasionEmpiricalCDF_zero {d : ℕ} (label : CubicEdge d → ℝ) (y : ℝ) :
    invasionEmpiricalCDF label 0 y = 0 := by
  simp [invasionEmpiricalCDF]

theorem invasionEmpiricalCDF_nonneg {d : ℕ} (label : CubicEdge d → ℝ)
    (n : ℕ) (y : ℝ) : 0 ≤ invasionEmpiricalCDF label n y := by
  unfold invasionEmpiricalCDF
  positivity

theorem invasionEmpiricalCDF_le_one {d : ℕ} (hd : 0 < d)
    (label : CubicEdge d → ℝ) (n : ℕ) (y : ℝ) :
    invasionEmpiricalCDF label n y ≤ 1 := by
  by_cases hn : n = 0
  · subst n
    simp
  · unfold invasionEmpiricalCDF
    rw [div_le_one (by positivity : (0 : ℝ) < n)]
    exact_mod_cast (Finset.card_filter_le
      (s := invasionClusterAt label n) (p := fun e ↦ label e ≤ y) |>.trans_eq
        (invasionClusterAt_card hd label n))

theorem invasionClusterAt_mono {d : ℕ} (label : CubicEdge d → ℝ) :
    Monotone (invasionClusterAt label) := by
  intro m n hmn
  induction n, hmn using Nat.le_induction with
  | base => exact Finset.Subset.rfl
  | succ n hmn ih =>
      exact ih.trans (invasionStep_edges_mono label (invasionState label n))

theorem invasionClusterAt_subset_cluster {d : ℕ} (label : CubicEdge d → ℝ)
    (n : ℕ) :
    (invasionClusterAt label n : Set (CubicEdge d)) ⊆ invasionCluster label := by
  intro e he
  exact Set.mem_iUnion.2 ⟨n, he⟩

end Percolation
