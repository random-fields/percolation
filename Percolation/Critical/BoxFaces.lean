import Percolation.Critical.CubicSymmetry

/-!
# Face-connection events for coordinate boxes

These events and their symmetry identities supply equation (6.22) in Grimmett's proof of
Theorem 6.10.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval BigOperators

/-- Connection from `x` to a specified signed face of its coordinate box. -/
def boxFaceConnectionEvent (d : ℕ) (x : Cubic d) (n : ℕ)
    (i : Fin d) (positive : Bool) : Set (EdgeConfiguration d) :=
  {ω | ∃ y, y ∈ cubicBoxFace d x n i positive ∧ ω ∈ connectionEvent d x y}

theorem measurableSet_boxFaceConnectionEvent (d : ℕ) (x : Cubic d) (n : ℕ)
    (i : Fin d) (positive : Bool) :
    MeasurableSet (boxFaceConnectionEvent d x n i positive) := by
  have heq : boxFaceConnectionEvent d x n i positive =
      ⋃ y ∈ cubicBoxFace d x n i positive, connectionEvent d x y := by
    ext ω
    simp [boxFaceConnectionEvent]
  rw [heq]
  exact (cubicBoxFace d x n i positive).measurableSet_biUnion fun y _hy ↦
    measurableSet_connectionEvent d x y

theorem isIncreasingEvent_boxFaceConnectionEvent (d : ℕ) (x : Cubic d) (n : ℕ)
    (i : Fin d) (positive : Bool) :
    IsIncreasingEvent (boxFaceConnectionEvent d x n i positive) := by
  rintro ω η hωη ⟨y, hy, hconn⟩
  exact ⟨y, hy, isIncreasingEvent_connectionEvent d x y hωη hconn⟩

noncomputable def boxFaceTail (d : ℕ) (p : I) (n : ℕ)
    (i : Fin d) (positive : Bool) : ℝ :=
  (bernoulliBondMeasure d p).real
    (boxFaceConnectionEvent d cubicOrigin n i positive)

theorem cubicTranslate_mem_boxFace_iff {d n : ℕ} (x y u : Cubic d)
    (i : Fin d) (positive : Bool) :
    cubicTranslate x y u ∈ cubicBoxFace d y n i positive ↔
      u ∈ cubicBoxFace d x n i positive := by
  rw [mem_cubicBoxFace, mem_cubicBoxFace]
  constructor
  · rintro ⟨hi, hrest⟩
    constructor
    · rcases positive with _ | _ <;> simp [cubicTranslate] at hi ⊢ <;> omega
    · intro j hji
      have hj := hrest j hji
      simp [cubicTranslate] at hj ⊢
      omega
  · rintro ⟨hi, hrest⟩
    constructor
    · rcases positive with _ | _ <;> simp [cubicTranslate] at hi ⊢ <;> omega
    · intro j hji
      have hj := hrest j hji
      simp [cubicTranslate] at hj ⊢
      omega

private theorem cubicTranslationConfigurationPullback_mem_boxFaceConnectionEvent
    {d n : ℕ} (x y : Cubic d) (i : Fin d) (positive : Bool)
    (ω : EdgeConfiguration d)
    (h : cubicTranslationConfigurationPullback x y ω ∈
      boxFaceConnectionEvent d x n i positive) :
    ω ∈ boxFaceConnectionEvent d y n i positive := by
  rcases h with ⟨z, hz, w, hw⟩
  let w' := w.map (cubicTranslationIso x y).toHom
  let w'' : (cubicGraph d).Walk y (cubicTranslate x y z) :=
    w'.copy (by simp [cubicTranslationIso_apply]) rfl
  refine ⟨cubicTranslate x y z, (cubicTranslate_mem_boxFace_iff x y z i positive).2 hz,
    w'', ?_⟩
  exact (walkIsOpen_copy w' (by simp [cubicTranslationIso_apply]) rfl).mpr
    (walkIsOpen_map_cubicTranslation w hw)

theorem cubicTranslationConfigurationPullback_mem_boxFaceConnectionEvent_iff
    {d n : ℕ} (x y : Cubic d) (i : Fin d) (positive : Bool)
    (ω : EdgeConfiguration d) :
    cubicTranslationConfigurationPullback x y ω ∈
        boxFaceConnectionEvent d x n i positive ↔
      ω ∈ boxFaceConnectionEvent d y n i positive := by
  constructor
  · exact cubicTranslationConfigurationPullback_mem_boxFaceConnectionEvent
      x y i positive ω
  · intro hω
    have hback : cubicTranslationConfigurationPullback y x
        (cubicTranslationConfigurationPullback x y ω) ∈
          boxFaceConnectionEvent d y n i positive := by
      simpa using hω
    exact cubicTranslationConfigurationPullback_mem_boxFaceConnectionEvent
      y x i positive (cubicTranslationConfigurationPullback x y ω) hback

theorem bernoulliBondMeasure_real_boxFaceConnectionEvent_eq_boxFaceTail
    {d n : ℕ} (p : I) (x : Cubic d) (i : Fin d) (positive : Bool) :
    (bernoulliBondMeasure d p).real (boxFaceConnectionEvent d x n i positive) =
      boxFaceTail d p n i positive := by
  let T := cubicTranslationConfigurationPullback cubicOrigin x
  have hpre : T ⁻¹' boxFaceConnectionEvent d cubicOrigin n i positive =
      boxFaceConnectionEvent d x n i positive := by
    ext ω
    exact cubicTranslationConfigurationPullback_mem_boxFaceConnectionEvent_iff
      cubicOrigin x i positive ω
  have hmap := congrArg
    (fun μ : Measure (EdgeConfiguration d) ↦
      μ (boxFaceConnectionEvent d cubicOrigin n i positive))
    (bernoulliBondMeasure_map_cubicTranslationConfigurationPullback p cubicOrigin x)
  change (Measure.map T (bernoulliBondMeasure d p))
      (boxFaceConnectionEvent d cubicOrigin n i positive) =
    (bernoulliBondMeasure d p)
      (boxFaceConnectionEvent d cubicOrigin n i positive) at hmap
  rw [Measure.map_apply
    (measurable_cubicTranslationConfigurationPullback cubicOrigin x)
    (measurableSet_boxFaceConnectionEvent d cubicOrigin n i positive), hpre] at hmap
  simpa [MeasureTheory.measureReal_def, boxFaceTail] using congrArg ENNReal.toReal hmap

private theorem cubicGraphIsoConfigurationPullback_mem_boxFaceConnectionEvent_of_map
    {d n : ℕ} {i j : Fin d} {positive negative : Bool}
    (F : cubicGraph d ≃g cubicGraph d)
    (hF0 : F cubicOrigin = cubicOrigin)
    (hface : ∀ y, y ∈ cubicBoxFace d cubicOrigin n i positive →
      F y ∈ cubicBoxFace d cubicOrigin n j negative)
    (ω : EdgeConfiguration d)
    (hω : cubicGraphIsoConfigurationPullback F ω ∈
      boxFaceConnectionEvent d cubicOrigin n i positive) :
    ω ∈ boxFaceConnectionEvent d cubicOrigin n j negative := by
  rcases hω with ⟨y, hy, w, hw⟩
  let w' := w.map F.toHom
  let w'' : (cubicGraph d).Walk cubicOrigin (F y) := w'.copy hF0 rfl
  refine ⟨F y, hface y hy, w'', ?_⟩
  exact (walkIsOpen_copy w' hF0 rfl).mpr (walkIsOpen_map_cubicGraphIso F w hw)

private theorem cubicGraphIsoConfigurationPullback_mem_boxFaceConnectionEvent_iff
    {d n : ℕ} {i j : Fin d} {positive negative : Bool}
    (F : cubicGraph d ≃g cubicGraph d)
    (hF0 : F cubicOrigin = cubicOrigin)
    (hFsymm0 : F.symm cubicOrigin = cubicOrigin)
    (hface : ∀ y, y ∈ cubicBoxFace d cubicOrigin n i positive →
      F y ∈ cubicBoxFace d cubicOrigin n j negative)
    (hfaceBack : ∀ y, y ∈ cubicBoxFace d cubicOrigin n j negative →
      F.symm y ∈ cubicBoxFace d cubicOrigin n i positive)
    (ω : EdgeConfiguration d) :
    cubicGraphIsoConfigurationPullback F ω ∈
        boxFaceConnectionEvent d cubicOrigin n i positive ↔
      ω ∈ boxFaceConnectionEvent d cubicOrigin n j negative := by
  constructor
  · exact cubicGraphIsoConfigurationPullback_mem_boxFaceConnectionEvent_of_map
      F hF0 hface ω
  · intro hω
    have hback : cubicGraphIsoConfigurationPullback F.symm
        (cubicGraphIsoConfigurationPullback F ω) ∈
          boxFaceConnectionEvent d cubicOrigin n j negative := by
      simpa using hω
    exact cubicGraphIsoConfigurationPullback_mem_boxFaceConnectionEvent_of_map
      F.symm hFsymm0 hfaceBack (cubicGraphIsoConfigurationPullback F ω) hback

private theorem boxFaceProbability_eq_of_iso
    {d n : ℕ} {i j : Fin d} {positive negative : Bool}
    (p : I) (F : cubicGraph d ≃g cubicGraph d)
    (hF0 : F cubicOrigin = cubicOrigin)
    (hFsymm0 : F.symm cubicOrigin = cubicOrigin)
    (hface : ∀ y, y ∈ cubicBoxFace d cubicOrigin n i positive →
      F y ∈ cubicBoxFace d cubicOrigin n j negative)
    (hfaceBack : ∀ y, y ∈ cubicBoxFace d cubicOrigin n j negative →
      F.symm y ∈ cubicBoxFace d cubicOrigin n i positive) :
    (bernoulliBondMeasure d p).real
        (boxFaceConnectionEvent d cubicOrigin n i positive) =
      (bernoulliBondMeasure d p).real
        (boxFaceConnectionEvent d cubicOrigin n j negative) := by
  let T := cubicGraphIsoConfigurationPullback F
  have hpre : T ⁻¹' boxFaceConnectionEvent d cubicOrigin n i positive =
      boxFaceConnectionEvent d cubicOrigin n j negative := by
    ext ω
    exact cubicGraphIsoConfigurationPullback_mem_boxFaceConnectionEvent_iff
      F hF0 hFsymm0 hface hfaceBack ω
  have hmap := congrArg
    (fun μ : Measure (EdgeConfiguration d) ↦
      μ (boxFaceConnectionEvent d cubicOrigin n i positive))
    (bernoulliBondMeasure_map_cubicGraphIsoConfigurationPullback p F)
  change (Measure.map T (bernoulliBondMeasure d p))
      (boxFaceConnectionEvent d cubicOrigin n i positive) =
    (bernoulliBondMeasure d p)
      (boxFaceConnectionEvent d cubicOrigin n i positive) at hmap
  rw [Measure.map_apply (measurable_cubicGraphIsoConfigurationPullback F)
    (measurableSet_boxFaceConnectionEvent d cubicOrigin n i positive), hpre] at hmap
  exact (congrArg ENNReal.toReal hmap).symm

theorem cubicCoordinatePermutation_mem_boxFace {d n : ℕ} (e : Fin d ≃ Fin d)
    (i : Fin d) (positive : Bool) {y : Cubic d}
    (hy : y ∈ cubicBoxFace d cubicOrigin n i positive) :
    cubicCoordinatePermutationEquiv e y ∈
      cubicBoxFace d cubicOrigin n (e i) positive := by
  rw [mem_cubicBoxFace] at hy ⊢
  constructor
  · simpa [cubicOrigin] using hy.1
  · intro k hki
    have hsymm : e.symm k ≠ i := by
      intro h
      apply hki
      simpa using congrArg e h
    simpa [cubicOrigin] using hy.2 (e.symm k) hsymm

theorem boxFaceTail_permutation {d n : ℕ} (p : I) (e : Fin d ≃ Fin d)
    (i : Fin d) (positive : Bool) :
    boxFaceTail d p n i positive = boxFaceTail d p n (e i) positive := by
  let F := cubicCoordinatePermutationIso e
  apply boxFaceProbability_eq_of_iso p F
  · ext k
    simp [F, cubicCoordinatePermutationIso, cubicOrigin]
  · ext k
    simp [F, cubicCoordinatePermutationIso, cubicCoordinatePermutationEquiv, cubicOrigin]
  · intro y hy
    exact cubicCoordinatePermutation_mem_boxFace e i positive hy
  · intro y hy
    simpa [F] using
      (cubicCoordinatePermutation_mem_boxFace e.symm (e i) positive hy)

theorem cubicCoordinateReflection_mem_boxFace_true {d n : ℕ} (i : Fin d)
    {y : Cubic d} (hy : y ∈ cubicBoxFace d cubicOrigin n i true) :
    cubicCoordinateReflectionEquiv i y ∈ cubicBoxFace d cubicOrigin n i false := by
  rw [mem_cubicBoxFace] at hy ⊢
  constructor
  · simpa [cubicCoordinateReflectionEquiv, cubicOrigin] using congrArg Neg.neg hy.1
  · intro k hki
    simpa [cubicCoordinateReflectionEquiv, cubicOrigin, hki] using hy.2 k hki

theorem cubicCoordinateReflection_mem_boxFace_false {d n : ℕ} (i : Fin d)
    {y : Cubic d} (hy : y ∈ cubicBoxFace d cubicOrigin n i false) :
    cubicCoordinateReflectionEquiv i y ∈ cubicBoxFace d cubicOrigin n i true := by
  rw [mem_cubicBoxFace] at hy ⊢
  constructor
  · simpa [cubicCoordinateReflectionEquiv, cubicOrigin] using congrArg Neg.neg hy.1
  · intro k hki
    simpa [cubicCoordinateReflectionEquiv, cubicOrigin, hki] using hy.2 k hki

theorem boxFaceTail_true_eq_false {d n : ℕ} (p : I) (i : Fin d) :
    boxFaceTail d p n i true = boxFaceTail d p n i false := by
  let F := cubicCoordinateReflectionIso i
  apply boxFaceProbability_eq_of_iso p F
  · ext k
    simp [F, cubicCoordinateReflectionIso, cubicCoordinateReflectionEquiv, cubicOrigin]
  · ext k
    simp [F, cubicCoordinateReflectionIso, cubicCoordinateReflectionEquiv, cubicOrigin]
  · exact fun y hy ↦ cubicCoordinateReflection_mem_boxFace_true i hy
  · exact fun y hy ↦ cubicCoordinateReflection_mem_boxFace_false i hy

theorem cubicBoxFace_subset_surface {d n : ℕ} (x : Cubic d)
    (i : Fin d) (positive : Bool) :
    cubicBoxFace d x n i positive ⊆ cubicBoxSurface d x n := by
  intro y hy
  rw [mem_cubicBoxFace] at hy
  rw [mem_cubicBoxSurface]
  apply le_antisymm
  · rw [← mem_cubicMetricBox_iff_lInfDist_le]
    rw [mem_cubicMetricBox]
    intro j
    by_cases hji : j = i
    · subst j
      rcases positive with _ | _ <;> simp_all <;> omega
    · exact hy.2 j hji
  · exact (cubicLInfDist_coord_le x y i).trans_eq' <| by
      rcases positive with _ | _ <;> simp_all [cubicOrigin]

/-- Two outward-facing box faces concatenate to the corresponding face of the sum-radius box. -/
theorem mem_cubicBoxSurface_add_of_mem_faces {d m n : ℕ} {x y : Cubic d}
    {i : Fin d} {positive : Bool}
    (hx : x ∈ cubicBoxFace d cubicOrigin m i positive)
    (hy : y ∈ cubicBoxFace d x n i positive) :
    y ∈ cubicBoxSurface d cubicOrigin (m + n) := by
  rw [mem_cubicBoxFace] at hx hy
  rw [mem_cubicBoxSurface]
  apply le_antisymm
  · rw [← mem_cubicMetricBox_iff_lInfDist_le]
    rw [mem_cubicMetricBox]
    intro j
    by_cases hji : j = i
    · subst j
      rcases positive with _ | _ <;> simp_all [cubicOrigin] <;> omega
    · have hxj := hx.2 j hji
      have hyj := hy.2 j hji
      simp [cubicOrigin] at hxj ⊢
      omega
  · refine (cubicLInfDist_coord_le cubicOrigin y i).trans_eq' ?_
    rcases positive with _ | _
    · simp_all [cubicOrigin]
      have hz : ((((-((m : ℤ)) - (n : ℤ)).natAbs : ℕ) : ℤ)) =
          ((m + n : ℕ) : ℤ) := by
        rw [show (-((m : ℤ)) - (n : ℤ)) = -((m : ℤ) + (n : ℤ)) by ring,
          Int.natAbs_neg, Int.natAbs_of_nonneg (by positivity)]
        omega
      exact_mod_cast hz
    · simp_all [cubicOrigin]
      have hz : (((((m : ℤ) + (n : ℤ)).natAbs : ℕ) : ℤ)) = ((m + n : ℕ) : ℤ) := by
        rw [Int.natAbs_of_nonneg (by positivity)]
        omega
      exact_mod_cast hz

theorem boxFaceConnectionEvent_subset_boxRadiusConnectionEvent
    (d : ℕ) (x : Cubic d) (n : ℕ) (i : Fin d) (positive : Bool) :
    boxFaceConnectionEvent d x n i positive ⊆ boxRadiusConnectionEvent d x n := by
  rintro ω ⟨y, hy, hconn⟩
  rw [mem_boxRadiusConnectionEvent_iff_exists_connection]
  exact ⟨y, cubicBoxFace_subset_surface x i positive hy, hconn⟩

theorem boxFaceTail_le_boxRadiusTail
    {d n : ℕ} (p : I) (i : Fin d) (positive : Bool) :
    boxFaceTail d p n i positive ≤ boxRadiusTail d p n := by
  exact measureReal_mono
    (boxFaceConnectionEvent_subset_boxRadiusConnectionEvent
      d cubicOrigin n i positive)

theorem boxRadiusConnectionEvent_subset_iUnion_boxFaceConnectionEvent
    {d n : ℕ} (hd : 0 < d) :
    boxRadiusConnectionEvent d cubicOrigin n ⊆
      ⋃ i : Fin d,
        (boxFaceConnectionEvent d cubicOrigin n i true ∪
          boxFaceConnectionEvent d cubicOrigin n i false) := by
  intro ω hω
  rw [mem_boxRadiusConnectionEvent_iff_exists_connection] at hω
  rcases hω with ⟨y, hy, hconn⟩
  have hyfaces := cubicBoxSurface_subset_faces (x := cubicOrigin) hd hy
  rw [cubicBoxFaces, Finset.mem_biUnion] at hyfaces
  rcases hyfaces with ⟨i, _hi, hyface⟩
  apply Set.mem_iUnion.mpr
  refine ⟨i, ?_⟩
  rw [Finset.mem_union] at hyface
  rcases hyface with hpos | hneg
  · exact Or.inl ⟨y, hpos, hconn⟩
  · exact Or.inr ⟨y, hneg, hconn⟩

/-- Equation (6.22): one face has probability within the factor `2d` of the whole surface event.
By symmetry every face has that probability. -/
theorem boxRadiusTail_le_two_mul_card_mul_boxFaceTail
    {d n : ℕ} (hd : 0 < d) (p : I) (i0 : Fin d) :
    boxRadiusTail d p n ≤ 2 * d * boxFaceTail d p n i0 true := by
  let μ := bernoulliBondMeasure d p
  have hcover := boxRadiusConnectionEvent_subset_iUnion_boxFaceConnectionEvent
    (d := d) (n := n) hd
  have hunion : μ.real (boxRadiusConnectionEvent d cubicOrigin n) ≤
      ∑ i : Fin d,
        (μ.real (boxFaceConnectionEvent d cubicOrigin n i true) +
          μ.real (boxFaceConnectionEvent d cubicOrigin n i false)) := by
    calc
      μ.real (boxRadiusConnectionEvent d cubicOrigin n) ≤
          μ.real (⋃ i : Fin d,
            (boxFaceConnectionEvent d cubicOrigin n i true ∪
              boxFaceConnectionEvent d cubicOrigin n i false)) :=
        measureReal_mono hcover
      _ ≤ ∑ i : Fin d,
          μ.real (boxFaceConnectionEvent d cubicOrigin n i true ∪
            boxFaceConnectionEvent d cubicOrigin n i false) := by
        exact measureReal_iUnion_fintype_le _
      _ ≤ ∑ i : Fin d,
          (μ.real (boxFaceConnectionEvent d cubicOrigin n i true) +
            μ.real (boxFaceConnectionEvent d cubicOrigin n i false)) := by
        apply Finset.sum_le_sum
        intro i _hi
        exact measureReal_union_le _ _
  calc
    boxRadiusTail d p n ≤ ∑ i : Fin d,
        (boxFaceTail d p n i true + boxFaceTail d p n i false) := hunion
    _ = ∑ _i : Fin d,
        (boxFaceTail d p n i0 true + boxFaceTail d p n i0 true) := by
      apply Finset.sum_congr rfl
      intro i _hi
      have hperm : boxFaceTail d p n i true = boxFaceTail d p n i0 true := by
        simpa using boxFaceTail_permutation p (Equiv.swap i i0) i true
      rw [← boxFaceTail_true_eq_false p i, hperm]
    _ = 2 * d * boxFaceTail d p n i0 true := by
      simp
      ring

end Percolation
