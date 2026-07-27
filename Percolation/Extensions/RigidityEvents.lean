import Percolation.Extensions.Rigidity
import Percolation.Critical.OpenClusterDensity
import Percolation.Bernoulli.Increasing
import Percolation.Bernoulli.FiniteCube

/-!
# Finite rigidity events in cubic bond percolation

This file supplies the finite-cylinder layer required by Grimmett's rigidity-percolation
discussion.  Rigidity of the open graph induced by a finite vertex set is decided by exactly the
cubic edges with both endpoints in that set; it is therefore measurable and increasing.
-/

namespace Percolation

open Set SimpleGraph

/-- Cubic edges whose two endpoints lie in a prescribed finite vertex set. -/
noncomputable def cubicInternalEdgeFinset (d : ℕ) (U : Finset (Cubic d)) :
    Finset (CubicEdge d) := by
  classical
  exact ((U.sym2.filter fun e ↦ e ∈ (cubicGraph d).edgeSet).attach).image fun e ↦
    (⟨e.1, (Finset.mem_filter.mp e.2).2⟩ : CubicEdge d)

theorem mem_cubicInternalEdgeFinset_iff {d : ℕ} {U : Finset (Cubic d)}
    {e : CubicEdge d} :
    e ∈ cubicInternalEdgeFinset d U ↔ ∀ x ∈ (e : Sym2 (Cubic d)), x ∈ U := by
  classical
  constructor
  · intro he x hx
    rw [cubicInternalEdgeFinset, Finset.mem_image] at he
    obtain ⟨f, hf, hfe⟩ := he
    have hsym : f.1 = e.1 := congrArg Subtype.val hfe
    have hmem : f.1 ∈ U.sym2 := (Finset.mem_filter.mp f.2).1
    rw [Finset.mem_sym2_iff] at hmem
    exact hmem x (hsym ▸ hx)
  · intro hendpoints
    rw [cubicInternalEdgeFinset, Finset.mem_image]
    let f : (U.sym2.filter fun q ↦ q ∈ (cubicGraph d).edgeSet) :=
      ⟨e.1, Finset.mem_filter.mpr ⟨Finset.mem_sym2_iff.mpr hendpoints, e.2⟩⟩
    exact ⟨f, Finset.mem_attach _ _, Subtype.ext rfl⟩

/-- Event that the open graph induced by `U` is generically rigid in dimension `d`. -/
def finiteRigidityEvent (d : ℕ) (U : Finset (Cubic d)) :
    Set (EdgeConfiguration d) :=
  {omega | genericallyRigidInducedOn (cubicOpenGraph d omega) d U}

theorem dependsOn_finiteRigidityEvent (d : ℕ) (U : Finset (Cubic d)) :
    DependsOn (cubicInternalEdgeFinset d U) (finiteRigidityEvent d U) := by
  intro omega eta hagree
  have hgraph :
      (cubicOpenGraph d omega).induce (U : Set (Cubic d)) =
        (cubicOpenGraph d eta).induce (U : Set (Cubic d)) := by
    ext x y
    simp only [SimpleGraph.induce_adj, cubicOpenGraph_adj]
    constructor
    · rintro ⟨hxy, hopen⟩
      refine ⟨hxy, ?_⟩
      let e : CubicEdge d := ⟨s(x.1, y.1),
        (SimpleGraph.mem_edgeSet (cubicGraph d)).2 hxy⟩
      have heU : e ∈ cubicInternalEdgeFinset d U := by
        rw [mem_cubicInternalEdgeFinset_iff]
        intro z hz
        rcases (Sym2.mem_iff'.mp hz) with rfl | rfl
        · exact x.2
        · exact y.2
      exact (hagree e heU).mp (by simpa [e] using hopen)
    · rintro ⟨hxy, hopen⟩
      refine ⟨hxy, ?_⟩
      let e : CubicEdge d := ⟨s(x.1, y.1),
        (SimpleGraph.mem_edgeSet (cubicGraph d)).2 hxy⟩
      have heU : e ∈ cubicInternalEdgeFinset d U := by
        rw [mem_cubicInternalEdgeFinset_iff]
        intro z hz
        rcases (Sym2.mem_iff'.mp hz) with rfl | rfl
        · exact x.2
        · exact y.2
      exact (hagree e heU).mpr (by simpa [e] using hopen)
  change GenericallyRigid ((cubicOpenGraph d omega).induce (U : Set (Cubic d))) d ↔
    GenericallyRigid ((cubicOpenGraph d eta).induce (U : Set (Cubic d))) d
  rw [hgraph]

theorem measurableSet_finiteRigidityEvent (d : ℕ) (U : Finset (Cubic d)) :
    MeasurableSet (finiteRigidityEvent d U) :=
  (dependsOn_finiteRigidityEvent d U).measurableSet

theorem isIncreasingEvent_finiteRigidityEvent (d : ℕ) (U : Finset (Cubic d)) :
    IsIncreasingEvent (finiteRigidityEvent d U) := by
  intro omega eta hmono homega
  change GenericallyRigid ((cubicOpenGraph d omega).induce (U : Set (Cubic d))) d at homega
  change GenericallyRigid ((cubicOpenGraph d eta).induce (U : Set (Cubic d))) d
  apply homega.mono
  intro x y hxy
  rw [SimpleGraph.induce_adj] at hxy ⊢
  obtain ⟨hadj, hopen⟩ := cubicOpenGraph_adj.mp hxy
  exact cubicOpenGraph_adj.mpr ⟨hadj, hmono hopen⟩

end Percolation
