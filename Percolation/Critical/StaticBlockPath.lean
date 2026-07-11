import Percolation.Critical.StaticBlockAdjacency

/-!
# Lifting good-block walks to open bond connectivity

Neighboring good blocks have intersecting selected clusters.  Iterating that deterministic
fact along a coarse-lattice walk shows that its endpoint clusters lie in one open bond
component.  This is the path-level form of equation (7.59) used by static renormalization.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval

/-- Ambient vertices of the canonical cluster selected by the good-block construction at a
coarse vertex `x`. -/
noncomputable def epsilonGoodBlockClusterVertices
    (d : ℕ) (ω : EdgeConfiguration d) (n : ℕ) (x : Cubic d) : Finset (Cubic d) :=
  finiteBoxGraphComponentVertices
    (finiteBoxGraphLargestComponent (epsilonGoodBlockCenter n x) n
      (finiteBoxOpenGraph d ω (epsilonGoodBlockCenter n x) n))

theorem finiteBoxGraphComponentVertices_reachable_cubicOpenGraph
    {d n : ℕ} {ω : EdgeConfiguration d} {x : Cubic d}
    {C : (finiteBoxOpenGraph d ω x n).ConnectedComponent}
    {u v : Cubic d}
    (hu : u ∈ finiteBoxGraphComponentVertices C)
    (hv : v ∈ finiteBoxGraphComponentVertices C) :
    (cubicOpenGraph d ω).Reachable u v := by
  simp only [finiteBoxGraphComponentVertices, Finset.mem_filter] at hu hv
  obtain ⟨huBox, _huBox', huSupp⟩ := hu
  obtain ⟨hvBox, _hvBox', hvSupp⟩ := hv
  let uBox : {z : Cubic d // z ∈ cubicMetricBox d x n} := ⟨u, huBox⟩
  let vBox : {z : Cubic d // z ∈ cubicMetricBox d x n} := ⟨v, hvBox⟩
  have huSupp' : uBox ∈ C.supp := by simpa [uBox] using huSupp
  have hvSupp' : vBox ∈ C.supp := by simpa [vBox] using hvSupp
  let emb := SimpleGraph.Embedding.induce
    (G := cubicOpenGraph d ω) (cubicMetricBox d x n : Set (Cubic d))
  have hmap := (C.reachable_of_mem_supp huSupp' hvSupp').map emb.toHom
  simpa [uBox, vBox, emb] using hmap

theorem epsilonGoodBlockClusterVertices_inter_of_step
    {d n : ℕ} (p : I) (ε : ℝ) (ω : EdgeConfiguration d)
    (x : Cubic d) (a : CubicDirection d)
    (hx : ω ∈ epsilonGoodBoxEvent d p ε (epsilonGoodBlockCenter n x) n)
    (hy : ω ∈ epsilonGoodBoxEvent d p ε
      (epsilonGoodBlockCenter n (cubicStepFrom x a)) n) :
    ∃ u : Cubic d,
      u ∈ epsilonGoodBlockClusterVertices d ω n x ∧
      u ∈ epsilonGoodBlockClusterVertices d ω n (cubicStepFrom x a) := by
  simpa [epsilonGoodBlockClusterVertices] using
    finiteBoxGraphLargestComponents_inter_of_mem_goodBoxEvents p ε ω x a hx hy

/-- A coarse cubic walk consisting entirely of good blocks lifts to open-bond reachability
between arbitrary vertices of its selected endpoint clusters. -/
theorem epsilonGoodBlockClusterVertices_reachable_of_good_walk
    {d n : ℕ} (p : I) (ε : ℝ) (ω : EdgeConfiguration d)
    {x y : Cubic d} (w : (cubicGraph d).Walk x y)
    (hgood : ∀ z ∈ w.support,
      ω ∈ epsilonGoodBoxEvent d p ε (epsilonGoodBlockCenter n z) n)
    {u v : Cubic d}
    (hu : u ∈ epsilonGoodBlockClusterVertices d ω n x)
    (hv : v ∈ epsilonGoodBlockClusterVertices d ω n y) :
    (cubicOpenGraph d ω).Reachable u v := by
  induction w generalizing u with
  | nil =>
      exact finiteBoxGraphComponentVertices_reachable_cubicOpenGraph hu hv
  | @cons x₀ x₁ y₀ hx₀x₁ q ih =>
      obtain ⟨a, rfl⟩ := (cubicGraph_adj_iff_exists_stepFrom x₀ x₁).mp hx₀x₁
      have hxGood : ω ∈ epsilonGoodBoxEvent d p ε
          (epsilonGoodBlockCenter n x₀) n :=
        hgood x₀ (by simp)
      have hx₁Good : ω ∈ epsilonGoodBoxEvent d p ε
          (epsilonGoodBlockCenter n (cubicStepFrom x₀ a)) n :=
        hgood (cubicStepFrom x₀ a) (by simp)
      obtain ⟨s, hs₀, hs₁⟩ :=
        epsilonGoodBlockClusterVertices_inter_of_step p ε ω x₀ a hxGood hx₁Good
      have hus : (cubicOpenGraph d ω).Reachable u s :=
        finiteBoxGraphComponentVertices_reachable_cubicOpenGraph hu hs₀
      have hgoodTail : ∀ z ∈ q.support,
          ω ∈ epsilonGoodBoxEvent d p ε (epsilonGoodBlockCenter n z) n := by
        intro z hz
        exact hgood z (by simp [hz])
      exact hus.trans (ih hgoodTail hs₁ hv)

end Percolation
