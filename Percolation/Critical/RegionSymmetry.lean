import Percolation.Critical.CubicSymmetry
import Percolation.Critical.Regions

/-!
# Cubic-automorphism invariance of induced-region percolation

Chapter 7 repeatedly rotates and reflects slabs, faces, and bricks.  This file transports
vertex-constrained paths and infinite components through an arbitrary automorphism of the cubic
graph, then proves invariance of the corresponding Bernoulli probability and critical value.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval

/-- Image of a vertex region under an automorphism of the cubic graph. -/
def cubicGraphIsoRegion {d : ℕ} (F : cubicGraph d ≃g cubicGraph d)
    (A : Set (Cubic d)) : Set (Cubic d) :=
  F '' A

@[simp]
theorem cubicGraphIso_mem_region_iff {d : ℕ} (F : cubicGraph d ≃g cubicGraph d)
    (A : Set (Cubic d)) (x : Cubic d) :
    F x ∈ cubicGraphIsoRegion F A ↔ x ∈ A := by
  constructor
  · rintro ⟨y, hy, hxy⟩
    exact F.injective hxy ▸ hy
  · exact fun hx ↦ ⟨x, hx, rfl⟩

@[simp]
theorem cubicGraphIsoRegion_symm {d : ℕ} (F : cubicGraph d ≃g cubicGraph d)
    (A : Set (Cubic d)) :
    cubicGraphIsoRegion F.symm (cubicGraphIsoRegion F A) = A := by
  ext x
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    simpa using hz
  · intro hx
    exact ⟨F x, ⟨x, hx, rfl⟩, by simp⟩

@[simp]
theorem cubicGraphIsoRegion_univ {d : ℕ} (F : cubicGraph d ≃g cubicGraph d) :
    cubicGraphIsoRegion F (Set.univ : Set (Cubic d)) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  exact ⟨F.symm x, Set.mem_univ _, by simp⟩

private theorem cubicGraphIsoConfigurationPullback_mem_connectionEventWithinVertices_of_map
    {d : ℕ} (F : cubicGraph d ≃g cubicGraph d) (A : Set (Cubic d))
    (ω : EdgeConfiguration d) (x y : Cubic d) :
    cubicGraphIsoConfigurationPullback F ω ∈ connectionEventWithinVertices d A x y →
      ω ∈ connectionEventWithinVertices d (cubicGraphIsoRegion F A) (F x) (F y) := by
  rintro ⟨w, hwopen, hwA⟩
  refine ⟨w.map F.toHom, walkIsOpen_map_cubicGraphIso F w hwopen, ?_⟩
  intro z hz
  rw [SimpleGraph.Walk.support_map] at hz
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hz
  exact (cubicGraphIso_mem_region_iff F A u).2 (hwA u hu)

/-- Vertex-constrained connectivity is transported exactly by any cubic graph automorphism. -/
theorem cubicGraphIsoConfigurationPullback_mem_connectionEventWithinVertices_iff
    {d : ℕ} (F : cubicGraph d ≃g cubicGraph d) (A : Set (Cubic d))
    (ω : EdgeConfiguration d) (x y : Cubic d) :
    cubicGraphIsoConfigurationPullback F ω ∈ connectionEventWithinVertices d A x y ↔
      ω ∈ connectionEventWithinVertices d (cubicGraphIsoRegion F A) (F x) (F y) := by
  constructor
  · exact cubicGraphIsoConfigurationPullback_mem_connectionEventWithinVertices_of_map
      F A ω x y
  · intro h
    have h' : cubicGraphIsoConfigurationPullback F.symm
        (cubicGraphIsoConfigurationPullback F ω) ∈
          connectionEventWithinVertices d (cubicGraphIsoRegion F A) (F x) (F y) := by
      simpa using h
    have hback :=
      cubicGraphIsoConfigurationPullback_mem_connectionEventWithinVertices_of_map
        F.symm (cubicGraphIsoRegion F A) (cubicGraphIsoConfigurationPullback F ω)
          (F x) (F y) h'
    simpa using hback

/-- Bernoulli probability of a vertex-constrained connection is invariant under cubic graph
automorphisms. -/
theorem bernoulliBondMeasure_real_connectionEventWithinVertices_graphIso
    {d : ℕ} (F : cubicGraph d ≃g cubicGraph d) (A : Set (Cubic d))
    (p : I) (x y : Cubic d) :
    (bernoulliBondMeasure d p).real (connectionEventWithinVertices d A x y) =
      (bernoulliBondMeasure d p).real
        (connectionEventWithinVertices d (cubicGraphIsoRegion F A) (F x) (F y)) := by
  let T := cubicGraphIsoConfigurationPullback F
  have hpre : T ⁻¹' connectionEventWithinVertices d A x y =
      connectionEventWithinVertices d (cubicGraphIsoRegion F A) (F x) (F y) := by
    ext ω
    exact cubicGraphIsoConfigurationPullback_mem_connectionEventWithinVertices_iff
      F A ω x y
  have hmap := congrArg
    (fun μ : Measure (EdgeConfiguration d) ↦ μ.real (connectionEventWithinVertices d A x y))
    (bernoulliBondMeasure_map_cubicGraphIsoConfigurationPullback p F)
  change (Measure.map T (bernoulliBondMeasure d p)).real
      (connectionEventWithinVertices d A x y) =
    (bernoulliBondMeasure d p).real (connectionEventWithinVertices d A x y) at hmap
  rw [map_measureReal_apply (measurable_cubicGraphIsoConfigurationPullback F)
    (measurableSet_connectionEventWithinVertices d A x y), hpre] at hmap
  exact hmap.symm

private theorem hasOpenPathOfLengthAtLeastWithinVertices_graphIso
    {d n : ℕ} {A : Set (Cubic d)} {ω : EdgeConfiguration d}
    (F : cubicGraph d ≃g cubicGraph d) (x : Cubic d)
    (h : hasOpenPathOfLengthAtLeastWithinVertices d A
      (cubicGraphIsoConfigurationPullback F ω) x n) :
    hasOpenPathOfLengthAtLeastWithinVertices d (cubicGraphIsoRegion F A) ω (F x) n := by
  rcases h with ⟨y, w, hwPath, hwLength, hwOpen, hwA⟩
  let w' := w.map F.toHom
  refine ⟨F y, w', ?_, ?_, ?_, ?_⟩
  · change (w.map F.toHom).IsPath
    rw [SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_map]
    exact hwPath.support_nodup.map F.injective
  · change n ≤ (w.map F.toHom).length
    simpa using hwLength
  · exact walkIsOpen_map_cubicGraphIso F w hwOpen
  · intro z hz
    change z ∈ (w.map F.toHom).support at hz
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hz
    obtain ⟨z₀, hz₀, rfl⟩ := hz
    exact ⟨z₀, hwA z₀ hz₀, rfl⟩

theorem hasOpenPathOfLengthAtLeastWithinVertices_graphIso_iff
    {d n : ℕ} (F : cubicGraph d ≃g cubicGraph d) (A : Set (Cubic d))
    (ω : EdgeConfiguration d) (x : Cubic d) :
    hasOpenPathOfLengthAtLeastWithinVertices d A
        (cubicGraphIsoConfigurationPullback F ω) x n ↔
      hasOpenPathOfLengthAtLeastWithinVertices d (cubicGraphIsoRegion F A) ω (F x) n := by
  constructor
  · exact hasOpenPathOfLengthAtLeastWithinVertices_graphIso F x
  · intro h
    have h' : hasOpenPathOfLengthAtLeastWithinVertices d (cubicGraphIsoRegion F A)
        (cubicGraphIsoConfigurationPullback F.symm
          (cubicGraphIsoConfigurationPullback F ω)) (F x) n := by
      simpa using h
    have hback := hasOpenPathOfLengthAtLeastWithinVertices_graphIso
      (A := cubicGraphIsoRegion F A)
      (ω := cubicGraphIsoConfigurationPullback F ω) F.symm (F x) h'
    simpa using hback

theorem cubicGraphIsoConfigurationPullback_clusterWithin_infinite_iff
    {d : ℕ} (F : cubicGraph d ≃g cubicGraph d) (A : Set (Cubic d))
    (ω : EdgeConfiguration d) (x : Cubic d) :
    (cubicOpenClusterWithinVertices d A
        (cubicGraphIsoConfigurationPullback F ω) x).Infinite ↔
      (cubicOpenClusterWithinVertices d (cubicGraphIsoRegion F A) ω (F x)).Infinite := by
  rw [cubicOpenClusterWithinVertices_infinite_iff_arbitrarilyLong,
    cubicOpenClusterWithinVertices_infinite_iff_arbitrarilyLong]
  exact forall_congr' fun n ↦
    hasOpenPathOfLengthAtLeastWithinVertices_graphIso_iff F A ω x

theorem cubicGraphIsoConfigurationPullback_hasInfiniteOpenClusterFrom_iff
    {d : ℕ} (F : cubicGraph d ≃g cubicGraph d)
    (ω : EdgeConfiguration d) (x : Cubic d) :
    hasInfiniteOpenClusterFrom d (cubicGraphIsoConfigurationPullback F ω) x ↔
      hasInfiniteOpenClusterFrom d ω (F x) := by
  simpa [hasInfiniteOpenClusterFrom, cubicOpenClusterWithinVertices_univ] using
    (cubicGraphIsoConfigurationPullback_clusterWithin_infinite_iff
      F (Set.univ : Set (Cubic d)) ω x)

private theorem hasInfiniteOpenClusterInVertices_graphIso
    {d : ℕ} {A : Set (Cubic d)} {ω : EdgeConfiguration d}
    (F : cubicGraph d ≃g cubicGraph d)
    (h : hasInfiniteOpenClusterInVertices d A
      (cubicGraphIsoConfigurationPullback F ω)) :
    hasInfiniteOpenClusterInVertices d (cubicGraphIsoRegion F A) ω := by
  rcases h with ⟨x, hxA, hxInf⟩
  refine ⟨F x, (cubicGraphIso_mem_region_iff F A x).2 hxA, ?_⟩
  apply cubicOpenClusterWithinVertices_infinite_iff_arbitrarilyLong.mpr
  intro n
  apply (hasOpenPathOfLengthAtLeastWithinVertices_graphIso_iff F A ω x).mp
  exact cubicOpenClusterWithinVertices_infinite_iff_arbitrarilyLong.mp hxInf n

theorem cubicGraphIsoConfigurationPullback_hasInfiniteOpenClusterInVertices_iff
    {d : ℕ} (F : cubicGraph d ≃g cubicGraph d) (A : Set (Cubic d))
    (ω : EdgeConfiguration d) :
    hasInfiniteOpenClusterInVertices d A (cubicGraphIsoConfigurationPullback F ω) ↔
      hasInfiniteOpenClusterInVertices d (cubicGraphIsoRegion F A) ω := by
  constructor
  · exact hasInfiniteOpenClusterInVertices_graphIso F
  · intro h
    have h' : hasInfiniteOpenClusterInVertices d (cubicGraphIsoRegion F A)
        (cubicGraphIsoConfigurationPullback F.symm
          (cubicGraphIsoConfigurationPullback F ω)) := by
      simpa using h
    have hback := hasInfiniteOpenClusterInVertices_graphIso
      (A := cubicGraphIsoRegion F A)
      (ω := cubicGraphIsoConfigurationPullback F ω) F.symm h'
    simpa using hback

theorem bernoulliBondMeasure_real_hasInfiniteOpenClusterInVertices_graphIso
    {d : ℕ} (F : cubicGraph d ≃g cubicGraph d) (A : Set (Cubic d)) (p : I) :
    (bernoulliBondMeasure d p).real {ω | hasInfiniteOpenClusterInVertices d A ω} =
      (bernoulliBondMeasure d p).real
        {ω | hasInfiniteOpenClusterInVertices d (cubicGraphIsoRegion F A) ω} := by
  let T := cubicGraphIsoConfigurationPullback F
  have hpre : T ⁻¹' {ω | hasInfiniteOpenClusterInVertices d A ω} =
      {ω | hasInfiniteOpenClusterInVertices d (cubicGraphIsoRegion F A) ω} := by
    ext ω
    exact cubicGraphIsoConfigurationPullback_hasInfiniteOpenClusterInVertices_iff F A ω
  have hmap := congrArg
    (fun μ : Measure (EdgeConfiguration d) ↦
      μ.real {ω | hasInfiniteOpenClusterInVertices d A ω})
    (bernoulliBondMeasure_map_cubicGraphIsoConfigurationPullback p F)
  change (Measure.map T (bernoulliBondMeasure d p)).real
      {ω | hasInfiniteOpenClusterInVertices d A ω} =
    (bernoulliBondMeasure d p).real
      {ω | hasInfiniteOpenClusterInVertices d A ω} at hmap
  rw [map_measureReal_apply (measurable_cubicGraphIsoConfigurationPullback F)
    (measurableSet_hasInfiniteOpenClusterInVertices d A), hpre] at hmap
  exact hmap.symm

theorem regionHasInfiniteClusterProbability_graphIso {d : ℕ}
    (F : cubicGraph d ≃g cubicGraph d) (A : Set (Cubic d)) (p : I) :
    regionHasInfiniteClusterProbability d (cubicGraphIsoRegion F A) p =
      regionHasInfiniteClusterProbability d A p := by
  exact (bernoulliBondMeasure_real_hasInfiniteOpenClusterInVertices_graphIso F A p).symm

/-- Region critical probability is invariant under every automorphism of the cubic graph. -/
theorem regionCriticalProbability_graphIso {d : ℕ}
    (F : cubicGraph d ≃g cubicGraph d) (A : Set (Cubic d)) :
    regionCriticalProbability d (cubicGraphIsoRegion F A) =
      regionCriticalProbability d A := by
  unfold regionCriticalProbability
  congr 1
  ext q
  constructor <;> rintro ⟨p, hp, rfl⟩
  · exact ⟨p, by simpa [regionHasInfiniteClusterProbability_graphIso] using hp, rfl⟩
  · exact ⟨p, by simpa [regionHasInfiniteClusterProbability_graphIso] using hp, rfl⟩

theorem regionCriticalProbability_coordinatePermutation {d : ℕ}
    (e : Fin d ≃ Fin d) (A : Set (Cubic d)) :
    regionCriticalProbability d
        (cubicGraphIsoRegion (cubicCoordinatePermutationIso e) A) =
      regionCriticalProbability d A :=
  regionCriticalProbability_graphIso (cubicCoordinatePermutationIso e) A

theorem regionCriticalProbability_coordinateReflection {d : ℕ}
    (i : Fin d) (A : Set (Cubic d)) :
    regionCriticalProbability d
        (cubicGraphIsoRegion (cubicCoordinateReflectionIso i) A) =
      regionCriticalProbability d A :=
  regionCriticalProbability_graphIso (cubicCoordinateReflectionIso i) A

end Percolation
