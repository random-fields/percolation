import Percolation.Planar.TriangularPeierlsNormalize
import Percolation.Critical.Translation
import Percolation.Extensions.MixedPercolation

/-!
# Translation invariance for homogeneous triangular bond percolation

The square-coordinate realization of the triangular lattice is invariant under integer
translations.  This file records the induced graph automorphism, configuration pullback, and
rooted infinite-cluster probability invariance needed by the standard-only Peierls argument.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory SimpleGraph
open scoped Sym2 unitInterval

/-- The open cluster rooted at an arbitrary triangular-lattice vertex. -/
def triangularOpenClusterFrom (ω : TriangularConfiguration) (root : SquareVertex) :
    Set SquareVertex :=
  {x | (triangularOpenGraph ω).Reachable root x}

@[simp]
theorem triangularOpenClusterFrom_origin (ω : TriangularConfiguration) :
    triangularOpenClusterFrom ω cubicOrigin = triangularOpenCluster ω := by
  rfl

/-- Triangular primal neighbors commute with every integer translation. -/
theorem cubicTranslate_triangularPrimalNeighbor
    (x y z : SquareVertex) (k : Fin 6) :
    cubicTranslate x y (triangularPrimalNeighbor z k) =
      triangularPrimalNeighbor (cubicTranslate x y z) k := by
  fin_cases k
  all_goals
    ext i
    fin_cases i <;>
      simp [cubicTranslate, triangularPrimalNeighbor, squareVertex] <;> omega

/-- Integer translation as an automorphism of the triangular lattice. -/
def triangularTranslationIso (x y : SquareVertex) :
    triangularGraph ≃g triangularGraph where
  toEquiv := cubicTranslationEquiv x y
  map_rel_iff' := by
    intro u v
    rw [triangularGraph_adj_iff_exists_neighbor,
      triangularGraph_adj_iff_exists_neighbor]
    constructor
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      apply cubicTranslate_injective x y
      simpa only [cubicTranslate_triangularPrimalNeighbor] using hk
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      simpa only [cubicTranslate_triangularPrimalNeighbor] using
        congrArg (cubicTranslate x y) hk

@[simp]
theorem triangularTranslationIso_apply (x y z : SquareVertex) :
    triangularTranslationIso x y z = cubicTranslate x y z := rfl

/-- Pull a triangular bond configuration back along a lattice translation. -/
def triangularTranslationConfigurationPullback (x y : SquareVertex)
    (ω : TriangularConfiguration) : TriangularConfiguration :=
  (triangularTranslationIso x y).mapEdgeSet ⁻¹' ω

theorem measurable_triangularTranslationConfigurationPullback
    (x y : SquareVertex) :
    Measurable (triangularTranslationConfigurationPullback x y) :=
  measurable_preimage_embedding
    (triangularTranslationIso x y).mapEdgeSet.toEmbedding

/-- The homogeneous triangular Bernoulli law is invariant under translation. -/
theorem inhomogeneousTriangularBondMeasure_map_translationPullback
    (p : I) (x y : SquareVertex) :
    (inhomogeneousTriangularBondMeasure p p p).map
        (triangularTranslationConfigurationPullback x y) =
      inhomogeneousTriangularBondMeasure p p p := by
  have hdensity : inhomogeneousTriangularEdgeDensity p p p =
      fun _ : TriangularEdge ↦ p := by
    funext e
    simp [inhomogeneousTriangularEdgeDensity]
  rw [inhomogeneousTriangularBondMeasure, hdensity,
    inhomogeneousSetBernoulli_const]
  simpa [triangularTranslationConfigurationPullback] using
    setBernoulli_map_preimage_univ
      (triangularTranslationIso x y).mapEdgeSet.toEmbedding p

/-- Translation identifies the pulled-back open graph with the translated open graph. -/
def triangularTranslationOpenGraphIso (x y : SquareVertex)
    (ω : TriangularConfiguration) :
    triangularOpenGraph (triangularTranslationConfigurationPullback x y ω) ≃g
      triangularOpenGraph ω where
  toEquiv := cubicTranslationEquiv x y
  map_rel_iff' := by
    intro u v
    let F := triangularTranslationIso x y
    have hedge (huv : triangularGraph.Adj u v) :
        F.mapEdgeSet
            (⟨s(u, v), (SimpleGraph.mem_edgeSet triangularGraph).2 huv⟩ :
              TriangularEdge) =
          ⟨s(F u, F v),
            (SimpleGraph.mem_edgeSet triangularGraph).2 (F.map_rel_iff.mpr huv)⟩ := by
      apply Subtype.ext
      rw [SimpleGraph.Iso.mapEdgeSet_apply]
      rfl
    constructor
    · rintro ⟨huv, hopen⟩
      have huv' : triangularGraph.Adj u v := F.map_rel_iff.mp huv
      refine ⟨huv', ?_⟩
      change F.mapEdgeSet
          (⟨s(u, v), (SimpleGraph.mem_edgeSet triangularGraph).2 huv'⟩ :
            TriangularEdge) ∈ ω
      rw [hedge huv']
      exact hopen
    · rintro ⟨huv, hopen⟩
      have huv' : triangularGraph.Adj (F u) (F v) := F.map_rel_iff.mpr huv
      refine ⟨huv', ?_⟩
      change F.mapEdgeSet
          (⟨s(u, v), (SimpleGraph.mem_edgeSet triangularGraph).2 huv⟩ :
            TriangularEdge) ∈ ω at hopen
      rw [hedge huv] at hopen
      exact hopen

/-- Pullback transports infinitude of a rooted triangular open cluster exactly. -/
theorem triangularTranslationConfigurationPullback_cluster_infinite_iff
    (x y : SquareVertex) (ω : TriangularConfiguration) (root : SquareVertex) :
    (triangularOpenClusterFrom
        (triangularTranslationConfigurationPullback x y ω) root).Infinite ↔
      (triangularOpenClusterFrom ω (triangularTranslationIso x y root)).Infinite := by
  let F := triangularTranslationIso x y
  let O := triangularTranslationOpenGraphIso x y ω
  have hcluster : F '' triangularOpenClusterFrom
      (triangularTranslationConfigurationPullback x y ω) root =
        triangularOpenClusterFrom ω (F root) := by
    ext z
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact O.reachable_iff.mpr hv
    · intro hz
      refine ⟨O.symm z, ?_, ?_⟩
      · apply O.reachable_iff.mp
        simpa [O, F, triangularTranslationOpenGraphIso] using hz
      · exact (cubicTranslationEquiv x y).apply_symm_apply z
  rw [← hcluster, Set.infinite_image_iff F.injective.injOn]

/-- The rooted infinite-cluster event is measurable at every triangular-lattice vertex. -/
theorem measurableSet_infinite_triangularOpenClusterFrom (root : SquareVertex) :
    MeasurableSet {ω : TriangularConfiguration |
      (triangularOpenClusterFrom ω root).Infinite} := by
  let A : Set (MixedConfiguration triangularGraph) :=
    {η | (mixedOpenCluster triangularGraph η root).Infinite}
  have hA : MeasurableSet A :=
    measurableSet_infinite_mixedOpenCluster triangularGraph root
  have hpre :
      (fun ω : TriangularConfiguration ↦
        ((Set.univ : Set SquareVertex), ω)) ⁻¹' A =
        {ω | (triangularOpenClusterFrom ω root).Infinite} := by
    ext ω
    change (mixedOpenCluster triangularGraph
      ((Set.univ : Set SquareVertex), ω) root).Infinite ↔
        (triangularOpenClusterFrom ω root).Infinite
    have hclusters : mixedOpenCluster triangularGraph
        ((Set.univ : Set SquareVertex), ω) root =
          triangularOpenClusterFrom ω root := by
      have hgraphs : mixedOpenGraph triangularGraph
          ((Set.univ : Set SquareVertex), ω) = triangularOpenGraph ω := by
        ext u v
        simp [triangularOpenGraph, mixedOpenGraph]
      ext z
      simp only [triangularOpenClusterFrom, mixedOpenCluster, Set.mem_setOf_eq]
      rw [hgraphs]
    rw [hclusters]
  rw [← hpre]
  exact hA.preimage (by fun_prop)

/-- Homogeneous triangular infinite-cluster probability is independent of the root. -/
theorem inhomogeneousTriangularBondMeasure_real_infiniteClusterFrom_eq_origin
    (p : I) (root : SquareVertex) :
    (inhomogeneousTriangularBondMeasure p p p).real
        {ω | (triangularOpenClusterFrom ω root).Infinite} =
      (inhomogeneousTriangularBondMeasure p p p).real
        {ω | (triangularOpenCluster ω).Infinite} := by
  let T := triangularTranslationConfigurationPullback cubicOrigin root
  let A : Set TriangularConfiguration :=
    {ω | (triangularOpenClusterFrom ω cubicOrigin).Infinite}
  have hpre : T ⁻¹' A =
      {ω | (triangularOpenClusterFrom ω root).Infinite} := by
    ext ω
    simpa [T, A] using
      (triangularTranslationConfigurationPullback_cluster_infinite_iff
        cubicOrigin root ω cubicOrigin)
  have hmap := congrArg (fun μ : Measure TriangularConfiguration ↦ μ A)
    (inhomogeneousTriangularBondMeasure_map_translationPullback
      p cubicOrigin root)
  change (Measure.map T (inhomogeneousTriangularBondMeasure p p p)) A =
      (inhomogeneousTriangularBondMeasure p p p) A at hmap
  rw [Measure.map_apply
    (measurable_triangularTranslationConfigurationPullback cubicOrigin root)
    (measurableSet_infinite_triangularOpenClusterFrom cubicOrigin), hpre] at hmap
  simpa [MeasureTheory.measureReal_def, A] using congrArg ENNReal.toReal hmap

end Percolation
