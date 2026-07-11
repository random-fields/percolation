import Percolation.Critical.Regions
import Percolation.Critical.Translation

/-!
# Translation invariance of induced-region percolation

The Chapter 7 block constructions repeatedly translate induced regions.  This module proves
translation covariance first for constrained paths and infinite-cluster events, then transports
the Bernoulli probability and the region critical probability.  Thus later uses of stationarity
do not rely on an informal symmetry argument.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval

/-- Translate a vertex region by the cubic translation taking `x` to `y`. -/
def cubicTranslateRegion {d : ℕ} (x y : Cubic d) (A : Set (Cubic d)) : Set (Cubic d) :=
  cubicTranslate x y '' A

@[simp]
theorem cubicTranslate_mem_translateRegion_iff {d : ℕ} (x y z : Cubic d)
    (A : Set (Cubic d)) :
    cubicTranslate x y z ∈ cubicTranslateRegion x y A ↔ z ∈ A := by
  constructor
  · rintro ⟨w, hw, hEq⟩
    exact (cubicTranslate_injective x y hEq).symm ▸ hw
  · intro hz
    exact ⟨z, hz, rfl⟩

theorem cubicTranslateRegion_inverse {d : ℕ} (x y : Cubic d) (A : Set (Cubic d)) :
    cubicTranslateRegion y x (cubicTranslateRegion x y A) = A := by
  ext z
  constructor
  · rintro ⟨w, ⟨u, hu, rfl⟩, rfl⟩
    have hEq : cubicTranslate y x (cubicTranslate x y u) = u := by
      ext i
      simp [cubicTranslate]
      ring
    simpa [hEq] using hu
  · intro hz
    refine ⟨cubicTranslate x y z, ⟨z, hz, rfl⟩, ?_⟩
    ext i
    simp [cubicTranslate]
    ring

private theorem hasOpenPathOfLengthAtLeastWithinVertices_translate
    {d n : ℕ} {A : Set (Cubic d)} {ω : EdgeConfiguration d}
    (x y z : Cubic d)
    (h : hasOpenPathOfLengthAtLeastWithinVertices d A
      (cubicTranslationConfigurationPullback x y ω) z n) :
    hasOpenPathOfLengthAtLeastWithinVertices d (cubicTranslateRegion x y A) ω
      (cubicTranslate x y z) n := by
  rcases h with ⟨v, w, hwPath, hwLength, hwOpen, hwA⟩
  let w' := w.map (cubicTranslationIso x y).toHom
  refine ⟨cubicTranslate x y v, w', ?_, ?_, ?_, ?_⟩
  · change (w.map (cubicTranslationIso x y).toHom).IsPath
    rw [SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_map]
    exact hwPath.support_nodup.map (cubicTranslationIso x y).injective
  · change n ≤ (w.map (cubicTranslationIso x y).toHom).length
    rw [SimpleGraph.Walk.length_map]
    exact hwLength
  · exact walkIsOpen_map_cubicTranslation w hwOpen
  · intro q hq
    change q ∈ (w.map (cubicTranslationIso x y).toHom).support at hq
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hq
    obtain ⟨q₀, hq₀, rfl⟩ := hq
    exact ⟨q₀, hwA q₀ hq₀, rfl⟩

theorem hasOpenPathOfLengthAtLeastWithinVertices_translate_iff
    {d n : ℕ} (A : Set (Cubic d)) (ω : EdgeConfiguration d)
    (x y z : Cubic d) :
    hasOpenPathOfLengthAtLeastWithinVertices d A
        (cubicTranslationConfigurationPullback x y ω) z n ↔
      hasOpenPathOfLengthAtLeastWithinVertices d (cubicTranslateRegion x y A) ω
        (cubicTranslate x y z) n := by
  constructor
  · exact hasOpenPathOfLengthAtLeastWithinVertices_translate x y z
  · intro h
    have h' : hasOpenPathOfLengthAtLeastWithinVertices d (cubicTranslateRegion x y A)
        (cubicTranslationConfigurationPullback y x
          (cubicTranslationConfigurationPullback x y ω))
        (cubicTranslate x y z) n := by
      simpa using h
    have hback := hasOpenPathOfLengthAtLeastWithinVertices_translate
      (A := cubicTranslateRegion x y A)
      (ω := cubicTranslationConfigurationPullback x y ω)
      y x (cubicTranslate x y z) h'
    have hEq : cubicTranslate y x (cubicTranslate x y z) = z := by
      ext i
      simp [cubicTranslate]
      ring
    simpa [cubicTranslateRegion_inverse, hEq] using hback

private theorem hasInfiniteOpenClusterInVertices_translate
    {d : ℕ} {A : Set (Cubic d)} {ω : EdgeConfiguration d}
    (x y : Cubic d)
    (h : hasInfiniteOpenClusterInVertices d A
      (cubicTranslationConfigurationPullback x y ω)) :
    hasInfiniteOpenClusterInVertices d (cubicTranslateRegion x y A) ω := by
  rcases h with ⟨z, hzA, hzInf⟩
  refine ⟨cubicTranslate x y z, (cubicTranslate_mem_translateRegion_iff x y z A).2 hzA, ?_⟩
  apply cubicOpenClusterWithinVertices_infinite_iff_arbitrarilyLong.mpr
  intro n
  apply (hasOpenPathOfLengthAtLeastWithinVertices_translate_iff A ω x y z).mp
  exact cubicOpenClusterWithinVertices_infinite_iff_arbitrarilyLong.mp hzInf n

theorem cubicTranslationConfigurationPullback_hasInfiniteOpenClusterInVertices_iff
    {d : ℕ} (A : Set (Cubic d)) (ω : EdgeConfiguration d) (x y : Cubic d) :
    hasInfiniteOpenClusterInVertices d A
        (cubicTranslationConfigurationPullback x y ω) ↔
      hasInfiniteOpenClusterInVertices d (cubicTranslateRegion x y A) ω := by
  constructor
  · exact hasInfiniteOpenClusterInVertices_translate x y
  · intro h
    have h' : hasInfiniteOpenClusterInVertices d (cubicTranslateRegion x y A)
        (cubicTranslationConfigurationPullback y x
          (cubicTranslationConfigurationPullback x y ω)) := by
      simpa using h
    have hback := hasInfiniteOpenClusterInVertices_translate
      (A := cubicTranslateRegion x y A)
      (ω := cubicTranslationConfigurationPullback x y ω) y x h'
    simpa [cubicTranslateRegion_inverse] using hback

theorem bernoulliBondMeasure_real_hasInfiniteOpenClusterInVertices_translate
    {d : ℕ} (A : Set (Cubic d)) (p : I) (x y : Cubic d) :
    (bernoulliBondMeasure d p).real {ω | hasInfiniteOpenClusterInVertices d A ω} =
      (bernoulliBondMeasure d p).real
        {ω | hasInfiniteOpenClusterInVertices d (cubicTranslateRegion x y A) ω} := by
  let T := cubicTranslationConfigurationPullback x y
  have hpre : T ⁻¹' {ω | hasInfiniteOpenClusterInVertices d A ω} =
      {ω | hasInfiniteOpenClusterInVertices d (cubicTranslateRegion x y A) ω} := by
    ext ω
    exact cubicTranslationConfigurationPullback_hasInfiniteOpenClusterInVertices_iff A ω x y
  have hmap := congrArg
    (fun μ : Measure (EdgeConfiguration d) ↦
      μ.real {ω | hasInfiniteOpenClusterInVertices d A ω})
    (bernoulliBondMeasure_map_cubicTranslationConfigurationPullback p x y)
  change (Measure.map T (bernoulliBondMeasure d p)).real
      {ω | hasInfiniteOpenClusterInVertices d A ω} =
    (bernoulliBondMeasure d p).real
      {ω | hasInfiniteOpenClusterInVertices d A ω} at hmap
  rw [map_measureReal_apply (measurable_cubicTranslationConfigurationPullback x y)
    (measurableSet_hasInfiniteOpenClusterInVertices d A), hpre] at hmap
  exact hmap.symm

theorem regionHasInfiniteClusterProbability_translate {d : ℕ}
    (A : Set (Cubic d)) (p : I) (x y : Cubic d) :
    regionHasInfiniteClusterProbability d (cubicTranslateRegion x y A) p =
      regionHasInfiniteClusterProbability d A p := by
  exact (bernoulliBondMeasure_real_hasInfiniteOpenClusterInVertices_translate A p x y).symm

/-- Region critical probability is invariant under every cubic translation. -/
theorem regionCriticalProbability_translate {d : ℕ}
    (A : Set (Cubic d)) (x y : Cubic d) :
    regionCriticalProbability d (cubicTranslateRegion x y A) =
      regionCriticalProbability d A := by
  unfold regionCriticalProbability
  congr 1
  ext q
  constructor <;> rintro ⟨p, hp, rfl⟩
  · exact ⟨p, by simpa [regionHasInfiniteClusterProbability_translate] using hp, rfl⟩
  · exact ⟨p, by simpa [regionHasInfiniteClusterProbability_translate] using hp, rfl⟩

end Percolation
