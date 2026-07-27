import Percolation.Critical.Radius

/-!
# Translation invariance on the cubic lattice

The i.i.d. bond law and the finite radius events are invariant under lattice
translations.  These lemmas are used by both the pivotal-sausage conditioning
argument and the block decomposition of radius events.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval

/-- Translation taking `x` to `y`, as an equivalence of cubic-lattice vertices. -/
def cubicTranslationEquiv {d : ℕ} (x y : Cubic d) : Cubic d ≃ Cubic d where
  toFun := cubicTranslate x y
  invFun := cubicTranslate y x
  left_inv := by
    intro z
    ext i
    simp [cubicTranslate]
    omega
  right_inv := by
    intro z
    ext i
    simp [cubicTranslate]
    omega

theorem cubicTranslate_stepFrom_right {d : ℕ} (x y z : Cubic d)
    (a : CubicDirection d) :
    cubicTranslate x y (cubicStepFrom z a) =
      cubicStepFrom (cubicTranslate x y z) a := by
  rcases a with ⟨i, b⟩
  ext j
  by_cases hji : j = i
  · subst j
    simp [cubicTranslate, cubicStepFrom, cubicDirectionIncrement]
    ring
  · simp [cubicTranslate, cubicStepFrom, cubicDirectionIncrement,
      Function.update_of_ne hji]

/-- Translation as a graph automorphism of the cubic lattice. -/
def cubicTranslationIso {d : ℕ} (x y : Cubic d) :
    cubicGraph d ≃g cubicGraph d where
  toEquiv := cubicTranslationEquiv x y
  map_rel_iff' := by
    intro u v
    rw [cubicGraph_adj_iff_exists_stepFrom, cubicGraph_adj_iff_exists_stepFrom]
    constructor
    · rintro ⟨a, ha⟩
      refine ⟨a, cubicTranslate_injective x y ?_⟩
      exact ha.trans (cubicTranslate_stepFrom_right x y u a).symm
    · rintro ⟨a, ha⟩
      exact ⟨a, (congrArg (cubicTranslate x y) ha).trans
        (cubicTranslate_stepFrom_right x y u a)⟩

@[simp]
theorem cubicTranslationIso_apply {d : ℕ} (x y z : Cubic d) :
    cubicTranslationIso x y z = cubicTranslate x y z := rfl

theorem cubicL1Dist_translate {d : ℕ} (x y u v : Cubic d) :
    cubicL1Dist (cubicTranslate x y u) (cubicTranslate x y v) =
      cubicL1Dist u v := by
  unfold cubicL1Dist cubicTranslate
  apply Finset.sum_congr rfl
  intro i _hi
  congr 1
  omega

theorem cubicTranslate_mem_sphere_iff {d n : ℕ} (x y u : Cubic d) :
    cubicTranslate x y u ∈ cubicMetricSphere d y n ↔
      u ∈ cubicMetricSphere d x n := by
  rw [mem_cubicMetricSphere_iff_l1Dist_eq,
    mem_cubicMetricSphere_iff_l1Dist_eq]
  rw [show cubicL1Dist y (cubicTranslate x y u) = cubicL1Dist x u by
    simpa using cubicL1Dist_translate x y x u]

/-- Pull a target configuration back along the edge bijection induced by the
translation taking `x` to `y`. -/
def cubicTranslationConfigurationPullback {d : ℕ} (x y : Cubic d)
    (omega : EdgeConfiguration d) : EdgeConfiguration d :=
  (cubicTranslationIso x y).mapEdgeSet ⁻¹' omega

theorem walkIsOpen_map_cubicTranslation {d : ℕ} {x y u v : Cubic d}
    {omega : EdgeConfiguration d} (w : (cubicGraph d).Walk u v)
    (hw : walkIsOpen (cubicTranslationConfigurationPullback x y omega) w) :
    walkIsOpen omega (w.map (cubicTranslationIso x y).toHom) := by
  intro e he
  rw [SimpleGraph.Walk.edges_map] at he
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp he
  let ef : CubicEdge d := ⟨f, w.edges_subset_edgeSet hf⟩
  exact hw ef.1 hf

/-- Pulling back twice along inverse translations recovers the configuration. -/
@[simp]
theorem cubicTranslationConfigurationPullback_inverse {d : ℕ}
    (x y : Cubic d) (omega : EdgeConfiguration d) :
    cubicTranslationConfigurationPullback y x
        (cubicTranslationConfigurationPullback x y omega) = omega := by
  ext e
  simp only [cubicTranslationConfigurationPullback, Set.mem_preimage]
  change (cubicTranslationIso x y).mapEdgeSet
      ((cubicTranslationIso y x).mapEdgeSet e) ∈ omega ↔ e ∈ omega
  have hsymm : cubicTranslationIso y x = (cubicTranslationIso x y).symm := by
    ext z
    rfl
  rw [hsymm]
  change (cubicTranslationIso x y).mapEdgeSet
      ((cubicTranslationIso x y).mapEdgeSet.symm e) ∈ omega ↔ e ∈ omega
  rw [Equiv.apply_symm_apply]

private theorem cubicTranslationConfigurationPullback_mem_radiusConnectionEvent
    {d n : ℕ} (x y : Cubic d) (omega : EdgeConfiguration d)
    (h : cubicTranslationConfigurationPullback x y omega ∈
      radiusConnectionEvent d x n) :
    omega ∈ radiusConnectionEvent d y n := by
  rw [mem_radiusConnectionEvent_iff_exists_connection] at h ⊢
  rcases h with ⟨z, hz, w, hw⟩
  let w' := w.map (cubicTranslationIso x y).toHom
  let w'' : (cubicGraph d).Walk y (cubicTranslate x y z) :=
    w'.copy (by simp [cubicTranslationIso_apply]) rfl
  refine ⟨cubicTranslate x y z, (cubicTranslate_mem_sphere_iff x y z).2 hz,
    w'', ?_⟩
  exact (walkIsOpen_copy w' (by simp [cubicTranslationIso_apply]) rfl).mpr
    (walkIsOpen_map_cubicTranslation w hw)

/-- A translated pullback satisfies the source radius event exactly when the
original configuration satisfies the translated target event. -/
theorem cubicTranslationConfigurationPullback_mem_radiusConnectionEvent_iff
    {d n : ℕ} (x y : Cubic d) (omega : EdgeConfiguration d) :
    cubicTranslationConfigurationPullback x y omega ∈ radiusConnectionEvent d x n ↔
      omega ∈ radiusConnectionEvent d y n := by
  constructor
  · exact cubicTranslationConfigurationPullback_mem_radiusConnectionEvent x y omega
  · intro homega
    have hback : cubicTranslationConfigurationPullback y x
        (cubicTranslationConfigurationPullback x y omega) ∈
          radiusConnectionEvent d y n := by
      simpa using homega
    exact cubicTranslationConfigurationPullback_mem_radiusConnectionEvent
      y x (cubicTranslationConfigurationPullback x y omega) hback

theorem measurable_cubicTranslationConfigurationPullback {d : ℕ} (x y : Cubic d) :
    Measurable (cubicTranslationConfigurationPullback x y) :=
  measurable_preimage_embedding (cubicTranslationIso x y).mapEdgeSet.toEmbedding

/-- The i.i.d. Bernoulli bond law is invariant under every cubic translation. -/
theorem bernoulliBondMeasure_map_cubicTranslationConfigurationPullback
    {d : ℕ} (p : I) (x y : Cubic d) :
    (bernoulliBondMeasure d p).map (cubicTranslationConfigurationPullback x y) =
      bernoulliBondMeasure d p := by
  simpa [bernoulliBondMeasure, cubicTranslationConfigurationPullback] using
    setBernoulli_map_preimage_univ
      (cubicTranslationIso x y).mapEdgeSet.toEmbedding p

/-- Radius-event probabilities do not depend on their centre. -/
theorem bernoulliBondMeasure_real_radiusConnectionEvent_eq_radiusTail
    {d n : ℕ} (p : I) (x : Cubic d) :
    (bernoulliBondMeasure d p).real (radiusConnectionEvent d x n) =
      radiusTail d p n := by
  let T := cubicTranslationConfigurationPullback cubicOrigin x
  have hpre : T ⁻¹' radiusConnectionEvent d cubicOrigin n =
      radiusConnectionEvent d x n := by
    ext omega
    exact cubicTranslationConfigurationPullback_mem_radiusConnectionEvent_iff
      cubicOrigin x omega
  have hmap := congrArg
    (fun mu : Measure (EdgeConfiguration d) ↦ mu (radiusConnectionEvent d cubicOrigin n))
    (bernoulliBondMeasure_map_cubicTranslationConfigurationPullback
      p cubicOrigin x)
  change (Measure.map (cubicTranslationConfigurationPullback cubicOrigin x)
      (bernoulliBondMeasure d p)) (radiusConnectionEvent d cubicOrigin n) =
    (bernoulliBondMeasure d p) (radiusConnectionEvent d cubicOrigin n) at hmap
  rw [Measure.map_apply
    (measurable_cubicTranslationConfigurationPullback cubicOrigin x)
    (measurableSet_radiusConnectionEvent d cubicOrigin n), hpre] at hmap
  simpa [MeasureTheory.measureReal_def, radiusTail] using congrArg ENNReal.toReal hmap

#print axioms bernoulliBondMeasure_real_radiusConnectionEvent_eq_radiusTail

end Percolation
