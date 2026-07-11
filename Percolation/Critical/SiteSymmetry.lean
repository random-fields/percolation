import Percolation.Critical.Regions

/-!
# Graph-isomorphism invariance of site percolation

The dynamic and half-space block constructions use site fields on translated and rotated
copies of an auxiliary graph.  This file proves that site connections, infinite clusters,
their Bernoulli probability, and the critical site density are invariant under graph
isomorphism.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval

/-- Pull a site configuration back along a graph isomorphism. -/
def siteGraphIsoConfigurationPullback {V W : Type*} {G : SimpleGraph V}
    {H : SimpleGraph W} (F : G ≃g H) (η : Set W) : Set V :=
  F ⁻¹' η

@[simp]
theorem siteGraphIsoConfigurationPullback_symm {V W : Type*} {G : SimpleGraph V}
    {H : SimpleGraph W} (F : G ≃g H) (η : Set W) :
    siteGraphIsoConfigurationPullback F.symm
        (siteGraphIsoConfigurationPullback F η) = η := by
  ext y
  simp [siteGraphIsoConfigurationPullback]

theorem measurable_siteGraphIsoConfigurationPullback {V W : Type*}
    {G : SimpleGraph V} {H : SimpleGraph W} (F : G ≃g H) :
    Measurable (siteGraphIsoConfigurationPullback F) :=
  measurable_preimage_embedding F.toEquiv.toEmbedding

theorem setBernoulli_map_siteGraphIsoConfigurationPullback {V W : Type*}
    {G : SimpleGraph V} {H : SimpleGraph W} (F : G ≃g H) (p : I) :
    setBer((Set.univ : Set W), p).map (siteGraphIsoConfigurationPullback F) =
      setBer((Set.univ : Set V), p) := by
  simpa [siteGraphIsoConfigurationPullback] using
    setBernoulli_map_preimage_univ F.toEquiv.toEmbedding p

theorem siteGraphIsoConfigurationPullback_mem_siteConnectionEvent_iff
    {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (F : G ≃g H) (η : Set W) (x y : V) :
    siteGraphIsoConfigurationPullback F η ∈ siteConnectionEvent G x y ↔
      η ∈ siteConnectionEvent H (F x) (F y) := by
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨w.map F.toHom, ?_⟩
    intro z hz
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hz
    obtain ⟨z₀, hz₀, rfl⟩ := hz
    exact hw z₀ hz₀
  · rintro ⟨w, hw⟩
    let q := w.map F.symm.toHom
    refine ⟨q.copy (by simp) (by simp), ?_⟩
    intro z hz
    change z ∈ (q.copy (by simp) (by simp)).support at hz
    rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map, List.mem_map] at hz
    obtain ⟨z₀, hz₀, rfl⟩ := hz
    have hzOpen : z₀ ∈ η := hw z₀ hz₀
    change F (F.symm z₀) ∈ η
    simpa using hzOpen

private theorem hasInfiniteSiteCluster_map
    {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (F : G ≃g H) (η : Set W)
    (h : hasInfiniteSiteCluster G (siteGraphIsoConfigurationPullback F η)) :
    hasInfiniteSiteCluster H η := by
  rcases h with ⟨x, hxInf⟩
  refine ⟨F x, ?_⟩
  have himage : (F '' siteOpenCluster G (siteGraphIsoConfigurationPullback F η) x).Infinite :=
    Set.Infinite.image F.injective.injOn hxInf
  exact himage.mono fun y hy ↦ by
    rcases hy with ⟨z, hz, rfl⟩
    exact (siteGraphIsoConfigurationPullback_mem_siteConnectionEvent_iff F η x z).mp hz

theorem siteGraphIsoConfigurationPullback_hasInfiniteSiteCluster_iff
    {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (F : G ≃g H) (η : Set W) :
    hasInfiniteSiteCluster G (siteGraphIsoConfigurationPullback F η) ↔
      hasInfiniteSiteCluster H η := by
  constructor
  · exact hasInfiniteSiteCluster_map F η
  · intro h
    have h' : hasInfiniteSiteCluster H
        (siteGraphIsoConfigurationPullback F.symm
          (siteGraphIsoConfigurationPullback F η)) := by
      simpa using h
    simpa using hasInfiniteSiteCluster_map F.symm
      (siteGraphIsoConfigurationPullback F η) h'

/-- Site-percolation probability is invariant under graph isomorphism. -/
theorem siteTheta_graphIso {V W : Type*} [Countable V] [Countable W]
    {G : SimpleGraph V} {H : SimpleGraph W} (F : G ≃g H) (p : I) :
    siteTheta H p = siteTheta G p := by
  let T := siteGraphIsoConfigurationPullback F
  have hpre : T ⁻¹' {η : Set V | hasInfiniteSiteCluster G η} =
      {η : Set W | hasInfiniteSiteCluster H η} := by
    ext η
    exact siteGraphIsoConfigurationPullback_hasInfiniteSiteCluster_iff F η
  have hmap := congrArg
    (fun μ : Measure (Set V) ↦ μ.real {η : Set V | hasInfiniteSiteCluster G η})
    (setBernoulli_map_siteGraphIsoConfigurationPullback F p)
  change (Measure.map T setBer((Set.univ : Set W), p)).real
      {η : Set V | hasInfiniteSiteCluster G η} =
    setBer((Set.univ : Set V), p).real
      {η : Set V | hasInfiniteSiteCluster G η} at hmap
  rw [map_measureReal_apply (measurable_siteGraphIsoConfigurationPullback F)
    (measurableSet_hasInfiniteSiteCluster G), hpre] at hmap
  simpa [siteTheta] using hmap

/-- Critical site density is invariant under graph isomorphism. -/
theorem siteCriticalProbability_graphIso {V W : Type*} [Countable V] [Countable W]
    {G : SimpleGraph V} {H : SimpleGraph W} (F : G ≃g H) :
    siteCriticalProbability H = siteCriticalProbability G := by
  unfold siteCriticalProbability
  congr 1
  ext q
  constructor <;> rintro ⟨p, hp, rfl⟩
  · exact ⟨p, by simpa [siteTheta_graphIso F] using hp, rfl⟩
  · exact ⟨p, by simpa [siteTheta_graphIso F] using hp, rfl⟩

end Percolation
