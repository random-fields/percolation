import Percolation.Critical.BoxRadiusProperties
import Percolation.Bernoulli.FKGInfinite
import Mathlib.Analysis.Subadditive

/-!
# Two-point connectivity on the cubic lattice

This file starts Grimmett's Section 6.2.  It packages connection probabilities, their lattice
symmetries, and the exact submultiplicative axis argument preceding Theorem 6.44.
-/

namespace Percolation

open Filter Set Topology MeasureTheory ProbabilityTheory
open scoped unitInterval ENNReal BigOperators

/-- Grimmett's two-point connectivity `τₚ(x,y)`. -/
noncomputable def twoPointConnectivity (d : ℕ) (p : I) (x y : Cubic d) : ℝ :=
  (bernoulliBondMeasure d p).real (connectionEvent d x y)

/-- Probability that every supplied terminal lies in one open cluster.  The empty and singleton
families have probability one by this rooted-pair formulation. -/
noncomputable def multiPointConnectivity (d : ℕ) (p : I) (terminals : Finset (Cubic d)) : ℝ :=
  (bernoulliBondMeasure d p).real
    {ω | ∀ x ∈ terminals, ∀ y ∈ terminals, ω ∈ connectionEvent d x y}

@[simp]
theorem twoPointConnectivity_self (d : ℕ) (p : I) (x : Cubic d) :
    twoPointConnectivity d p x x = 1 := by
  have heq : connectionEvent d x x = Set.univ := by
    apply Set.eq_univ_of_forall
    intro ω
    exact ⟨SimpleGraph.Walk.nil, by simp [walkIsOpen]⟩
  simp [twoPointConnectivity, heq]

theorem connectionEvent_comm (d : ℕ) (x y : Cubic d) :
    connectionEvent d x y = connectionEvent d y x := by
  ext ω
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨w.reverse, walkIsOpen_reverse hw⟩
  · rintro ⟨w, hw⟩
    exact ⟨w.reverse, walkIsOpen_reverse hw⟩

theorem twoPointConnectivity_comm (d : ℕ) (p : I) (x y : Cubic d) :
    twoPointConnectivity d p x y = twoPointConnectivity d p y x := by
  rw [twoPointConnectivity, twoPointConnectivity, connectionEvent_comm]

theorem twoPointConnectivity_nonneg (d : ℕ) (p : I) (x y : Cubic d) :
    0 ≤ twoPointConnectivity d p x y := measureReal_nonneg

theorem twoPointConnectivity_le_one (d : ℕ) (p : I) (x y : Cubic d) :
    twoPointConnectivity d p x y ≤ 1 := measureReal_le_one

theorem twoPointConnectivity_pos (d : ℕ) {p : I} (hp : 0 < (p : ℝ))
    (x y : Cubic d) :
    0 < twoPointConnectivity d p x y :=
  bernoulliBondMeasure_real_connectionEvent_pos d hp x y

/-- Pulling a configuration back by a graph automorphism turns connection of the source
vertices into connection of their images. -/
theorem cubicGraphIsoConfigurationPullback_mem_connectionEvent_iff
    {d : ℕ} (F : cubicGraph d ≃g cubicGraph d) (ω : EdgeConfiguration d)
    (x y : Cubic d) :
    cubicGraphIsoConfigurationPullback F ω ∈ connectionEvent d x y ↔
      ω ∈ connectionEvent d (F x) (F y) := by
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨w.map F.toHom, walkIsOpen_map_cubicGraphIso F w hw⟩
  · rintro ⟨w, hw⟩
    have hback : cubicGraphIsoConfigurationPullback F.symm
        (cubicGraphIsoConfigurationPullback F ω) ∈ connectionEvent d (F x) (F y) := by
      simpa using ⟨w, hw⟩
    rcases hback with ⟨q, hq⟩
    let q' := q.map F.symm.toHom
    have hq' := walkIsOpen_map_cubicGraphIso F.symm q hq
    refine ⟨q'.copy (by simp [q']) (by simp [q']), ?_⟩
    exact (walkIsOpen_copy q' (by simp [q']) (by simp [q'])).mpr hq'

/-- Every cubic graph automorphism preserves the two-point function. -/
theorem twoPointConnectivity_graphIso
    {d : ℕ} (p : I) (F : cubicGraph d ≃g cubicGraph d) (x y : Cubic d) :
    twoPointConnectivity d p (F x) (F y) = twoPointConnectivity d p x y := by
  let T := cubicGraphIsoConfigurationPullback F
  have hpre : T ⁻¹' connectionEvent d x y = connectionEvent d (F x) (F y) := by
    ext ω
    exact cubicGraphIsoConfigurationPullback_mem_connectionEvent_iff F ω x y
  have hmap := congrArg
    (fun μ : Measure (EdgeConfiguration d) ↦ μ (connectionEvent d x y))
    (bernoulliBondMeasure_map_cubicGraphIsoConfigurationPullback p F)
  change (Measure.map T (bernoulliBondMeasure d p)) (connectionEvent d x y) =
      (bernoulliBondMeasure d p) (connectionEvent d x y) at hmap
  rw [Measure.map_apply (measurable_cubicGraphIsoConfigurationPullback F)
    (measurableSet_connectionEvent d x y), hpre] at hmap
  simpa [twoPointConnectivity, MeasureTheory.measureReal_def] using
    congrArg ENNReal.toReal hmap

theorem twoPointConnectivity_translate
    {d : ℕ} (p : I) (a b x y : Cubic d) :
    twoPointConnectivity d p (cubicTranslate a b x) (cubicTranslate a b y) =
      twoPointConnectivity d p x y := by
  simpa [cubicTranslationIso_apply] using
    twoPointConnectivity_graphIso p (cubicTranslationIso a b) x y

theorem twoPointConnectivity_coordinatePermutation
    {d : ℕ} (p : I) (e : Fin d ≃ Fin d) (x y : Cubic d) :
    twoPointConnectivity d p (cubicCoordinatePermutationEquiv e x)
        (cubicCoordinatePermutationEquiv e y) = twoPointConnectivity d p x y := by
  exact twoPointConnectivity_graphIso p (cubicCoordinatePermutationIso e) x y

theorem twoPointConnectivity_coordinateReflection
    {d : ℕ} (p : I) (i : Fin d) (x y : Cubic d) :
    twoPointConnectivity d p (cubicCoordinateReflectionEquiv i x)
        (cubicCoordinateReflectionEquiv i y) = twoPointConnectivity d p x y := by
  exact twoPointConnectivity_graphIso p (cubicCoordinateReflectionIso i) x y

theorem cubicTranslate_axisVertex_axisVertex {d m n : ℕ} (hd : 0 < d) :
    cubicTranslate cubicOrigin (cubicAxisVertex d m) (cubicAxisVertex d n) =
      cubicAxisVertex d (m + n) := by
  ext i
  by_cases hi : (i : ℕ) = 0
  · simp [cubicTranslate, cubicAxisVertex, cubicOrigin, hi, add_comm]
  · simp [cubicTranslate, cubicAxisVertex, cubicOrigin, hi]

theorem cubicTranslate_origin_axisVertex {d n : ℕ} :
    cubicTranslate cubicOrigin (cubicAxisVertex d n) cubicOrigin = cubicAxisVertex d n := by
  ext i
  simp [cubicTranslate, cubicOrigin]

/-- FKG concatenation along the first coordinate axis, equation (6.58). -/
theorem twoPointConnectivity_axis_mul_le
    {d : ℕ} (hd : 0 < d) (p : I) (m n : ℕ) :
    twoPointConnectivity d p cubicOrigin (cubicAxisVertex d m) *
        twoPointConnectivity d p cubicOrigin (cubicAxisVertex d n) ≤
      twoPointConnectivity d p cubicOrigin (cubicAxisVertex d (m + n)) := by
  let em := cubicAxisVertex d m
  let en := cubicAxisVertex d n
  let emn := cubicAxisVertex d (m + n)
  let A := connectionEvent d cubicOrigin em
  let B := connectionEvent d em emn
  have hB : (bernoulliBondMeasure d p).real B =
      twoPointConnectivity d p cubicOrigin en := by
    have ht := twoPointConnectivity_translate p cubicOrigin em cubicOrigin en
    rw [cubicTranslate_origin_axisVertex,
      cubicTranslate_axisVertex_axisVertex hd] at ht
    simpa [twoPointConnectivity, B, em, en, emn] using ht
  have hfkg := bernoulliBondMeasure_real_fkg p
    (isIncreasingEvent_connectionEvent d cubicOrigin em)
    (isIncreasingEvent_connectionEvent d em emn)
    (measurableSet_connectionEvent d cubicOrigin em)
    (measurableSet_connectionEvent d em emn)
  have hsubset : A ∩ B ⊆ connectionEvent d cubicOrigin emn := by
    rintro ω ⟨⟨w, hw⟩, ⟨q, hq⟩⟩
    exact ⟨w.append q, walkIsOpen_append hw hq⟩
  calc
    twoPointConnectivity d p cubicOrigin em *
        twoPointConnectivity d p cubicOrigin en =
      (bernoulliBondMeasure d p).real A * (bernoulliBondMeasure d p).real B := by
        simp [twoPointConnectivity, A, hB]
    _ ≤ (bernoulliBondMeasure d p).real (A ∩ B) := hfkg
    _ ≤ twoPointConnectivity d p cubicOrigin emn := measureReal_mono hsubset

/-- Negative logarithm of the axis two-point function. -/
noncomputable def axisConnectivityNegLog (d : ℕ) (p : I) (n : ℕ) : ℝ :=
  -Real.log (twoPointConnectivity d p cubicOrigin (cubicAxisVertex d n))

theorem axisConnectivityNegLog_subadditive
    {d : ℕ} (hd : 0 < d) {p : I} (hp : 0 < (p : ℝ)) :
    Subadditive (axisConnectivityNegLog d p) := by
  intro m n
  have hm := twoPointConnectivity_pos d hp cubicOrigin (cubicAxisVertex d m)
  have hn := twoPointConnectivity_pos d hp cubicOrigin (cubicAxisVertex d n)
  have hmn := twoPointConnectivity_pos d hp cubicOrigin (cubicAxisVertex d (m + n))
  have hmul := twoPointConnectivity_axis_mul_le hd p m n
  have hlog := Real.log_le_log (mul_pos hm hn) hmul
  rw [Real.log_mul hm.ne' hn.ne'] at hlog
  simpa [axisConnectivityNegLog, add_comm] using neg_le_neg hlog

theorem axisConnectivityNegLog_div_bddBelow
    (d : ℕ) (p : I) :
    BddBelow (Set.range fun n : ℕ ↦ axisConnectivityNegLog d p n / n) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨n, rfl⟩
  by_cases hn : n = 0
  · simp [hn]
  have hlog : Real.log
      (twoPointConnectivity d p cubicOrigin (cubicAxisVertex d n)) ≤ 0 :=
    Real.log_nonpos (twoPointConnectivity_nonneg d p _ _)
      (twoPointConnectivity_le_one d p _ _)
  exact div_nonneg (neg_nonneg.mpr hlog) (Nat.cast_nonneg n)

/-- The Fekete rate of the axis two-point function. -/
noncomputable def axisConnectivityDecayRate (d : ℕ) (p : I) : ℝ :=
  sInf ((fun n : ℕ ↦ axisConnectivityNegLog d p n / n) '' Set.Ici 1)

theorem twoPointConnectivity_axis_logRate_tendsto_aux
    {d : ℕ} (hd : 0 < d) {p : I} (hp : 0 < (p : ℝ)) :
    Tendsto (fun n : ℕ ↦
      -Real.log (twoPointConnectivity d p cubicOrigin (cubicAxisVertex d n)) / n)
      atTop (𝓝 (axisConnectivityDecayRate d p)) := by
  have hsub := axisConnectivityNegLog_subadditive hd hp
  have hlim := hsub.tendsto_lim (axisConnectivityNegLog_div_bddBelow d p)
  simpa [axisConnectivityNegLog, axisConnectivityDecayRate, Subadditive.lim] using hlim

/-- The exact Fekete upper exponential bound for every axis distance. -/
theorem twoPointConnectivity_axis_le_exp_rate
    {d : ℕ} (hd : 0 < d) {p : I} (hp : 0 < (p : ℝ)) {n : ℕ} (hn : 0 < n) :
    twoPointConnectivity d p cubicOrigin (cubicAxisVertex d n) ≤
      Real.exp (-(n : ℝ) * axisConnectivityDecayRate d p) := by
  have hsub := axisConnectivityNegLog_subadditive hd hp
  have hle := hsub.lim_le_div (axisConnectivityNegLog_div_bddBelow d p) hn.ne'
  have hpos := twoPointConnectivity_pos d hp cubicOrigin (cubicAxisVertex d n)
  rw [Subadditive.lim] at hle
  have hle' : axisConnectivityDecayRate d p ≤ axisConnectivityNegLog d p n / n := by
    simpa [axisConnectivityDecayRate] using hle
  apply (Real.log_le_iff_le_exp hpos).mp
  have hnreal : (0 : ℝ) < n := by positivity
  have hmul := (le_div_iff₀ hnreal).mp hle'
  dsimp [axisConnectivityNegLog] at hmul
  nlinarith

/-! ### Selecting a well-connected point on the positive face -/

theorem boxFaceTail_le_sum_twoPointConnectivity
    {d n : ℕ} (p : I) (i : Fin d) (positive : Bool) :
    boxFaceTail d p n i positive ≤
      ∑ y ∈ cubicBoxFace d cubicOrigin n i positive,
        twoPointConnectivity d p cubicOrigin y := by
  have heq : boxFaceConnectionEvent d cubicOrigin n i positive =
      ⋃ y ∈ cubicBoxFace d cubicOrigin n i positive, connectionEvent d cubicOrigin y := by
    ext ω
    simp [boxFaceConnectionEvent]
  rw [boxFaceTail, heq]
  exact measureReal_biUnion_finset_le _ _

theorem cubicAxisVertex_mem_positive_first_face
    {d n : ℕ} (hd : 0 < d) :
    cubicAxisVertex d n ∈
      cubicBoxFace d cubicOrigin n (⟨0, hd⟩ : Fin d) true := by
  rw [mem_cubicBoxFace]
  constructor
  · simp [cubicAxisVertex, cubicOrigin]
  · intro j hj
    have hj0 : (j : ℕ) ≠ 0 := by
      intro h
      apply hj
      apply Fin.ext
      exact h
    simp [cubicAxisVertex, cubicOrigin, hj0]

/-- Equation (6.60): some point on the positive first face carries at least the average
connection mass of that face. -/
theorem exists_positive_first_face_boxRadiusTail_le_card_mul_twoPoint
    {d : ℕ} (hd : 0 < d) (p : I) (n : ℕ) :
    ∃ y ∈ cubicBoxFace d cubicOrigin n (⟨0, hd⟩ : Fin d) true,
      boxRadiusTail d p n ≤
        (2 * d : ℝ) * ((2 * n + 1 : ℕ) : ℝ) ^ (d - 1) *
          twoPointConnectivity d p cubicOrigin y := by
  let i0 : Fin d := ⟨0, hd⟩
  let F := cubicBoxFace d cubicOrigin n i0 true
  have hF : F.Nonempty := ⟨cubicAxisVertex d n,
    cubicAxisVertex_mem_positive_first_face hd⟩
  obtain ⟨y, hy, hmax⟩ := Finset.exists_max_image F
    (fun z ↦ twoPointConnectivity d p cubicOrigin z) hF
  refine ⟨y, hy, ?_⟩
  have hfaceSum := boxFaceTail_le_sum_twoPointConnectivity (n := n) p i0 true
  have hsum : (∑ z ∈ F, twoPointConnectivity d p cubicOrigin z) ≤
      (F.card : ℝ) * twoPointConnectivity d p cubicOrigin y := by
    simpa [nsmul_eq_mul] using
      (Finset.sum_le_card_nsmul F
        (fun z ↦ twoPointConnectivity d p cubicOrigin z)
        (twoPointConnectivity d p cubicOrigin y) hmax)
  have hbox := boxRadiusTail_le_two_mul_card_mul_boxFaceTail (n := n) hd p i0
  have hcard : F.card = (2 * n + 1) ^ (d - 1) := by
    simpa [F, i0] using cubicBoxFace_card cubicOrigin i0 true
  have hcardR : (F.card : ℝ) = ((2 * n + 1 : ℕ) : ℝ) ^ (d - 1) := by
    norm_cast
  calc
    boxRadiusTail d p n ≤ (2 * d : ℝ) * boxFaceTail d p n i0 true := by
      simpa using hbox
    _ ≤ (2 * d : ℝ) * (∑ z ∈ F, twoPointConnectivity d p cubicOrigin z) := by
      gcongr
    _ ≤ (2 * d : ℝ) * ((F.card : ℝ) *
        twoPointConnectivity d p cubicOrigin y) := by
      gcongr
    _ = (2 * d : ℝ) * ((2 * n + 1 : ℕ) : ℝ) ^ (d - 1) *
        twoPointConnectivity d p cubicOrigin y := by rw [hcardR]; ring

/-! ### Reflection through the selected face and the even-axis lower bound -/

/-- Reflection in the affine hyperplane whose first coordinate is `n`. -/
def cubicAxisHyperplaneReflectionIso {d : ℕ} (hd : 0 < d) (n : ℕ) :
    cubicGraph d ≃g cubicGraph d :=
  (cubicCoordinateReflectionIso (⟨0, hd⟩ : Fin d)).trans
    (cubicTranslationIso cubicOrigin (cubicAxisVertex d (2 * n)))

@[simp]
theorem cubicAxisHyperplaneReflectionIso_origin
    {d n : ℕ} (hd : 0 < d) :
    cubicAxisHyperplaneReflectionIso hd n cubicOrigin = cubicAxisVertex d (2 * n) := by
  ext i
  simp [cubicAxisHyperplaneReflectionIso, cubicCoordinateReflectionIso,
    cubicCoordinateReflectionEquiv, cubicTranslationIso_apply, cubicTranslate,
    cubicAxisVertex, cubicOrigin]

theorem cubicAxisHyperplaneReflectionIso_fix_positive_face
    {d n : ℕ} (hd : 0 < d) {y : Cubic d}
    (hy : y ∈ cubicBoxFace d cubicOrigin n (⟨0, hd⟩ : Fin d) true) :
    cubicAxisHyperplaneReflectionIso hd n y = y := by
  rw [mem_cubicBoxFace] at hy
  ext i
  by_cases hi : (i : ℕ) = 0
  · have hii : i = (⟨0, hd⟩ : Fin d) := Fin.ext hi
    subst i
    simp [cubicAxisHyperplaneReflectionIso, cubicCoordinateReflectionIso,
      cubicCoordinateReflectionEquiv, cubicTranslationIso_apply, cubicTranslate,
      cubicAxisVertex, cubicOrigin] at hy ⊢
    omega
  · have hii : i ≠ (⟨0, hd⟩ : Fin d) := by
      intro h
      apply hi
      exact congrArg Fin.val h
    simp [cubicAxisHyperplaneReflectionIso, cubicCoordinateReflectionIso,
      cubicCoordinateReflectionEquiv, cubicTranslationIso_apply, cubicTranslate,
      cubicAxisVertex, cubicOrigin, hi, hii]

theorem twoPointConnectivity_positive_face_reflection
    {d n : ℕ} (hd : 0 < d) (p : I) {y : Cubic d}
    (hy : y ∈ cubicBoxFace d cubicOrigin n (⟨0, hd⟩ : Fin d) true) :
    twoPointConnectivity d p y (cubicAxisVertex d (2 * n)) =
      twoPointConnectivity d p cubicOrigin y := by
  have h := twoPointConnectivity_graphIso p
    (cubicAxisHyperplaneReflectionIso hd n) cubicOrigin y
  rw [twoPointConnectivity_comm]
  simpa [cubicAxisHyperplaneReflectionIso_origin hd,
    cubicAxisHyperplaneReflectionIso_fix_positive_face hd hy] using h

/-- FKG glues the two reflected copies of a face connection into an axis connection. -/
theorem twoPointConnectivity_positive_face_sq_le_axis_even
    {d n : ℕ} (hd : 0 < d) (p : I) {y : Cubic d}
    (hy : y ∈ cubicBoxFace d cubicOrigin n (⟨0, hd⟩ : Fin d) true) :
    twoPointConnectivity d p cubicOrigin y ^ 2 ≤
      twoPointConnectivity d p cubicOrigin (cubicAxisVertex d (2 * n)) := by
  let A := connectionEvent d cubicOrigin y
  let B := connectionEvent d y (cubicAxisVertex d (2 * n))
  have hfkg := bernoulliBondMeasure_real_fkg p
    (isIncreasingEvent_connectionEvent d cubicOrigin y)
    (isIncreasingEvent_connectionEvent d y (cubicAxisVertex d (2 * n)))
    (measurableSet_connectionEvent d cubicOrigin y)
    (measurableSet_connectionEvent d y (cubicAxisVertex d (2 * n)))
  have hsubset : A ∩ B ⊆
      connectionEvent d cubicOrigin (cubicAxisVertex d (2 * n)) := by
    rintro ω ⟨⟨w, hw⟩, ⟨q, hq⟩⟩
    exact ⟨w.append q, walkIsOpen_append hw hq⟩
  calc
    twoPointConnectivity d p cubicOrigin y ^ 2 =
        (bernoulliBondMeasure d p).real A *
          (bernoulliBondMeasure d p).real B := by
      rw [pow_two]
      change twoPointConnectivity d p cubicOrigin y *
          twoPointConnectivity d p cubicOrigin y =
        twoPointConnectivity d p cubicOrigin y *
          twoPointConnectivity d p y (cubicAxisVertex d (2 * n))
      rw [twoPointConnectivity_positive_face_reflection hd p hy]
    _ ≤ (bernoulliBondMeasure d p).real (A ∩ B) := hfkg
    _ ≤ twoPointConnectivity d p cubicOrigin (cubicAxisVertex d (2 * n)) :=
      measureReal_mono hsubset

/-- Squared form of Grimmett's (6.61), before inserting the exponential box-tail estimate. -/
theorem boxRadiusTail_sq_le_faceFactor_sq_mul_axis_even
    {d : ℕ} (hd : 0 < d) (p : I) (n : ℕ) :
    boxRadiusTail d p n ^ 2 ≤
      ((2 * d : ℝ) * ((2 * n + 1 : ℕ) : ℝ) ^ (d - 1)) ^ 2 *
        twoPointConnectivity d p cubicOrigin (cubicAxisVertex d (2 * n)) := by
  obtain ⟨y, hy, hselect⟩ :=
    exists_positive_first_face_boxRadiusTail_le_card_mul_twoPoint hd p n
  have hright : 0 ≤
      (2 * d : ℝ) * ((2 * n + 1 : ℕ) : ℝ) ^ (d - 1) *
        twoPointConnectivity d p cubicOrigin y := by
    exact mul_nonneg
      (mul_nonneg (by positivity) (pow_nonneg (by positivity) _))
      (twoPointConnectivity_nonneg d p _ _)
  have hsq := (sq_le_sq₀ measureReal_nonneg hright).2 hselect
  calc
    boxRadiusTail d p n ^ 2 ≤
        (((2 * d : ℝ) * ((2 * n + 1 : ℕ) : ℝ) ^ (d - 1)) *
          twoPointConnectivity d p cubicOrigin y) ^ 2 := by
      simpa [sq] using hsq
    _ = ((2 * d : ℝ) * ((2 * n + 1 : ℕ) : ℝ) ^ (d - 1)) ^ 2 *
        (twoPointConnectivity d p cubicOrigin y ^ 2) := by ring
    _ ≤ ((2 * d : ℝ) * ((2 * n + 1 : ℕ) : ℝ) ^ (d - 1)) ^ 2 *
        twoPointConnectivity d p cubicOrigin (cubicAxisVertex d (2 * n)) := by
      gcongr
      exact twoPointConnectivity_positive_face_sq_le_axis_even hd p hy

/-- Logarithmic cost of selecting one vertex from the positive first face. -/
noncomputable def faceSelectionLogCorrection (d n : ℕ) : ℝ :=
  Real.log ((2 * d : ℝ) * ((2 * n + 1 : ℕ) : ℝ) ^ (d - 1))

theorem faceSelectionLogCorrection_div_tendsto_zero
    {d : ℕ} (hd : 0 < d) :
    Tendsto (fun n : ℕ ↦ faceSelectionLogCorrection d n / n) atTop (𝓝 0) := by
  have hC : (0 : ℝ) < 2 * d := by exact_mod_cast Nat.mul_pos (by omega) hd
  have heq : ∀ n : ℕ, faceSelectionLogCorrection d n =
      boxRadiusLogCorrection d n - Real.log (2 * d : ℝ) := by
    intro n
    have hK : 0 < (2 * d : ℝ) * ((2 * n + 1 : ℕ) : ℝ) ^ (d - 1) := by positivity
    rw [faceSelectionLogCorrection, boxRadiusLogCorrection, boxRadiusPolynomialFactor]
    rw [show (((2 * n + 1 : ℕ) : ℝ)) = 2 * (n : ℝ) + 1 by norm_num]
    have hK' : 0 < (2 * d : ℝ) * (2 * (n : ℝ) + 1) ^ (d - 1) := by positivity
    have hfactor : (4 * (d : ℝ) ^ 2) * (2 * (n : ℝ) + 1) ^ (d - 1) =
        (2 * d : ℝ) *
          ((2 * d : ℝ) * (2 * (n : ℝ) + 1) ^ (d - 1)) := by ring
    rw [hfactor, Real.log_mul hC.ne' hK'.ne']
    ring
  have hbox := boxRadiusLogCorrection_add_const_div_tendsto_zero hd 0
  have hconst : Tendsto (fun n : ℕ ↦ Real.log (2 * d : ℝ) / (n : ℝ))
      atTop (𝓝 0) := tendsto_const_div_atTop_nhds_zero_nat _
  have hdiff := hbox.sub hconst
  convert hdiff using 1
  · funext n
    rw [heq]
    ring
  · norm_num

/-- One half of the rate identification: the reflected face estimate forces the axis rate to
be no larger than the box-radius rate. -/
theorem axisConnectivityDecayRate_le_boxRadiusDecayRate
    {d : ℕ} (hd : 0 < d) {p : I} (hp : 0 < (p : ℝ)) :
    axisConnectivityDecayRate d p ≤ boxRadiusDecayRate d p := by
  have hbox := boxRadiusTail_logRate_tendsto d hd p hp
  have hcorr := faceSelectionLogCorrection_div_tendsto_zero hd
  have hsum : Tendsto (fun m : ℕ ↦
      -Real.log (boxRadiusTail d p m) / m + faceSelectionLogCorrection d m / m)
      atTop (𝓝 (boxRadiusDecayRate d p)) := by
    simpa using hbox.add hcorr
  have hconst : Tendsto (fun _m : ℕ ↦ axisConnectivityDecayRate d p)
      atTop (𝓝 (axisConnectivityDecayRate d p)) := tendsto_const_nhds
  apply le_of_tendsto_of_tendsto hconst hsum
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
  have hmpos : 0 < m := zero_lt_one.trans_le hm
  let K : ℝ := (2 * d : ℝ) * ((2 * m + 1 : ℕ) : ℝ) ^ (d - 1)
  let τ : ℝ := twoPointConnectivity d p cubicOrigin (cubicAxisVertex d (2 * m))
  let β : ℝ := boxRadiusTail d p m
  have hK : 0 < K := by dsimp [K]; positivity
  have hτ : 0 < τ := twoPointConnectivity_pos d hp _ _
  have hβ : 0 < β := boxRadiusTail_pos_of_pos_density hd hp
  have hsq : β ^ 2 ≤ K ^ 2 * τ := by
    simpa [K, τ, β] using boxRadiusTail_sq_le_faceFactor_sq_mul_axis_even hd p m
  have hlog := Real.log_le_log (pow_pos hβ 2) hsq
  rw [Real.log_pow, Real.log_mul (pow_pos hK 2).ne' hτ.ne', Real.log_pow] at hlog
  have hsub := axisConnectivityNegLog_subadditive hd hp
  have hrate := hsub.lim_le_div (axisConnectivityNegLog_div_bddBelow d p)
    (show 2 * m ≠ 0 by omega)
  rw [Subadditive.lim] at hrate
  have hrate' : axisConnectivityDecayRate d p ≤
      axisConnectivityNegLog d p (2 * m) / (2 * m : ℕ) := by
    simpa [axisConnectivityDecayRate] using hrate
  have h2m : (0 : ℝ) < (2 * m : ℕ) := by positivity
  have hrateMul := (le_div_iff₀ h2m).mp hrate'
  have hmreal : (0 : ℝ) < m := by positivity
  rw [← add_div]
  apply (le_div_iff₀ hmreal).2
  dsimp [axisConnectivityNegLog, τ] at hrateMul
  dsimp [τ, K, β] at hlog
  dsimp [faceSelectionLogCorrection, K, β]
  have hcast : (((2 * m : ℕ) : ℝ)) = 2 * (m : ℝ) := by norm_num
  rw [hcast] at hrateMul
  nlinarith

theorem twoPointConnectivity_axis_le_boxRadiusTail
    {d : ℕ} (hd : 0 < d) (p : I) (n : ℕ) :
    twoPointConnectivity d p cubicOrigin (cubicAxisVertex d n) ≤
      boxRadiusTail d p n := by
  have hsub : connectionEvent d cubicOrigin (cubicAxisVertex d n) ⊆
      boxRadiusConnectionEvent d cubicOrigin n := by
    intro ω hω
    rw [mem_boxRadiusConnectionEvent_iff_exists_connection]
    exact ⟨cubicAxisVertex d n, cubicAxisVertex_mem_boxSurface hd, hω⟩
  exact measureReal_mono hsub

/-- The reverse rate comparison follows directly because the axis point lies on the box surface. -/
theorem boxRadiusDecayRate_le_axisConnectivityDecayRate
    {d : ℕ} (hd : 0 < d) {p : I} (hp : 0 < (p : ℝ)) :
    boxRadiusDecayRate d p ≤ axisConnectivityDecayRate d p := by
  have hbox := boxRadiusTail_logRate_tendsto d hd p hp
  have haxis := twoPointConnectivity_axis_logRate_tendsto_aux hd hp
  apply le_of_tendsto_of_tendsto hbox haxis
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hτ := twoPointConnectivity_pos d hp cubicOrigin (cubicAxisVertex d n)
  have hβ := boxRadiusTail_pos_of_pos_density (d := d) (n := n) hd hp
  have hlog := Real.log_le_log hτ
    (twoPointConnectivity_axis_le_boxRadiusTail hd p n)
  exact div_le_div_of_nonneg_right (neg_le_neg hlog) (Nat.cast_nonneg n)

theorem axisConnectivityDecayRate_eq_boxRadiusDecayRate
    {d : ℕ} (hd : 0 < d) {p : I} (hp : 0 < (p : ℝ)) :
    axisConnectivityDecayRate d p = boxRadiusDecayRate d p :=
  le_antisymm (axisConnectivityDecayRate_le_boxRadiusDecayRate hd hp)
    (boxRadiusDecayRate_le_axisConnectivityDecayRate hd hp)

/-- The logarithmic assertion (6.45) of Grimmett's Theorem 6.44. -/
theorem twoPointConnectivity_axis_logRate_tendsto
    {d : ℕ} (hd : 0 < d) {p : I} (hp : 0 < (p : ℝ)) :
    Tendsto (fun n : ℕ ↦
      -Real.log (twoPointConnectivity d p cubicOrigin (cubicAxisVertex d n)) / n)
      atTop (𝓝 (boxRadiusDecayRate d p)) := by
  simpa [axisConnectivityDecayRate_eq_boxRadiusDecayRate hd hp] using
    twoPointConnectivity_axis_logRate_tendsto_aux hd hp

/-- The exact upper inequality in (6.46). -/
theorem twoPointConnectivity_axis_le_exp_boxRadiusDecayRate
    {d : ℕ} (hd : 0 < d) {p : I} (hp : 0 < (p : ℝ)) {n : ℕ} (hn : 0 < n) :
    twoPointConnectivity d p cubicOrigin (cubicAxisVertex d n) ≤
      Real.exp (-(n : ℝ) * boxRadiusDecayRate d p) := by
  simpa [axisConnectivityDecayRate_eq_boxRadiusDecayRate hd hp] using
    twoPointConnectivity_axis_le_exp_rate hd hp hn

/-- Division form of (6.61), convenient for inserting the lower box-tail estimate. -/
theorem boxRadiusTail_div_faceFactor_sq_le_axis_even
    {d : ℕ} (hd : 0 < d) (p : I) (n : ℕ) :
    (boxRadiusTail d p n /
      ((2 * d : ℝ) * ((2 * n + 1 : ℕ) : ℝ) ^ (d - 1))) ^ 2 ≤
      twoPointConnectivity d p cubicOrigin (cubicAxisVertex d (2 * n)) := by
  have hK : 0 < (2 * d : ℝ) * ((2 * n + 1 : ℕ) : ℝ) ^ (d - 1) := by positivity
  rw [div_pow]
  apply (div_le_iff₀ (pow_pos hK 2)).2
  simpa [mul_comm] using boxRadiusTail_sq_le_faceFactor_sq_mul_axis_even hd p n

/-- A dimension-only constant for the even-axis lower bound. -/
noncomputable def axisConnectivityEvenPrefactor (d : ℕ) (rho : ℝ) : ℝ :=
  (rho / ((2 * d : ℝ) * (3 : ℝ) ^ (d - 1))) ^ 2

theorem axisConnectivityEvenPrefactor_pos
    {d : ℕ} (hd : 0 < d) {rho : ℝ} (hrho : 0 < rho) :
    0 < axisConnectivityEvenPrefactor d rho := by
  unfold axisConnectivityEvenPrefactor
  positivity

/-- Even-distance form of the lower inequality in (6.46), with the exact polynomial power. -/
theorem twoPointConnectivity_axis_even_lower
    (d : ℕ) (hd : 0 < d) :
    ∃ c : ℝ, 0 < c ∧ ∀ (p : I), 0 < (p : ℝ) → ∀ m : ℕ, 0 < m →
      c / (m : ℝ) ^ (4 * (d - 1)) *
          Real.exp (-((2 * m : ℕ) : ℝ) * boxRadiusDecayRate d p) ≤
        twoPointConnectivity d p cubicOrigin (cubicAxisVertex d (2 * m)) := by
  obtain ⟨rho, _sigma, hrho, _hsigma, hbox⟩ := boxRadiusTail_twoSided_decay d hd
  refine ⟨axisConnectivityEvenPrefactor d rho,
    axisConnectivityEvenPrefactor_pos hd hrho, ?_⟩
  intro p hp m hm
  let a : ℕ := d - 1
  let D : ℝ := (2 * d : ℝ) * (3 : ℝ) ^ a
  let A : ℝ := rho / (m : ℝ) ^ a *
    Real.exp (-(m : ℝ) * boxRadiusDecayRate d p)
  let K : ℝ := (2 * d : ℝ) * ((2 * m + 1 : ℕ) : ℝ) ^ a
  have hmR : (0 : ℝ) < m := by positivity
  have hD : 0 < D := by dsimp [D, a]; positivity
  have hK : 0 < K := by dsimp [K, a]; positivity
  have hA : 0 < A := by dsimp [A, a]; positivity
  have hAβ : A ≤ boxRadiusTail d p m := by
    simpa [A, a] using (hbox p hp m hm).1
  have hbase : (((2 * m + 1 : ℕ) : ℝ)) ≤ 3 * (m : ℝ) := by
    norm_cast
    omega
  have hKBound : K ≤ D * (m : ℝ) ^ a := by
    have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ ((2 * m + 1 : ℕ) : ℝ))
      hbase a
    calc
      K ≤ (2 * d : ℝ) * (3 * (m : ℝ)) ^ a := by
        dsimp [K]
        exact mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = D * (m : ℝ) ^ a := by
        dsimp [D]
        rw [mul_pow]
        ring
  have hden : 0 < D * (m : ℝ) ^ a := mul_pos hD (pow_pos hmR a)
  have hdiv : A / (D * (m : ℝ) ^ a) ≤
      boxRadiusTail d p m / K := by
    exact div_le_div₀ measureReal_nonneg hAβ hK hKBound
  have hsq : (A / (D * (m : ℝ) ^ a)) ^ 2 ≤
      (boxRadiusTail d p m / K) ^ 2 :=
    (sq_le_sq₀ (div_nonneg hA.le hden.le)
      (div_nonneg measureReal_nonneg hK.le)).2 hdiv
  have htoAxis := boxRadiusTail_div_faceFactor_sq_le_axis_even hd p m
  have hraw := hsq.trans htoAxis
  have heq : (A / (D * (m : ℝ) ^ a)) ^ 2 =
      axisConnectivityEvenPrefactor d rho / (m : ℝ) ^ (4 * (d - 1)) *
        Real.exp (-((2 * m : ℕ) : ℝ) * boxRadiusDecayRate d p) := by
    dsimp [A, D, a, axisConnectivityEvenPrefactor]
    rw [show (((2 * m : ℕ) : ℝ)) = 2 * (m : ℝ) by norm_num]
    have hexp : Real.exp (-(m : ℝ) * boxRadiusDecayRate d p) ^ 2 =
        Real.exp (-(2 * (m : ℝ)) * boxRadiusDecayRate d p) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    have hpowm : (m : ℝ) ^ (4 * (d - 1)) = ((m : ℝ) ^ (d - 1)) ^ 4 := by
      rw [show 4 * (d - 1) = (d - 1) * 4 by omega, ← pow_mul]
    rw [hpowm]
    simp only [div_pow, mul_pow, hexp]
    field_simp
  rwa [heq] at hraw

/-- The straight axis path gives the elementary lower bound `pⁿ ≤ τₚ(0,eₙ)`. -/
theorem pow_le_twoPointConnectivity_axis
    {d n : ℕ} (hd : 0 < d) (p : I) :
    (p : ℝ) ^ n ≤
      twoPointConnectivity d p cubicOrigin (cubicAxisVertex d n) := by
  let y := cubicAxisVertex d n
  obtain ⟨w, hwlen⟩ := exists_cubicWalk_length_eq_l1Dist d cubicOrigin y
  let q : (cubicGraph d).Walk cubicOrigin y := w.toPath
  have hqlen : q.length ≤ n := by
    calc
      q.length ≤ w.length := by
        simpa [q, SimpleGraph.Walk.toPath] using SimpleGraph.Walk.length_bypass_le w
      _ = n := by simpa [y] using hwlen.trans (cubicL1Dist_origin_axisVertex hd)
  have hpow : (p : ℝ) ^ n ≤ (p : ℝ) ^ q.length :=
    pow_le_pow_of_le_one p.property.1 p.property.2 hqlen
  have hsub : {ω : EdgeConfiguration d | walkIsOpen ω q} ⊆
      connectionEvent d cubicOrigin y := fun ω hω ↦ ⟨q, hω⟩
  calc
    (p : ℝ) ^ n ≤ (p : ℝ) ^ q.length := hpow
    _ = (bernoulliBondMeasure d p).real {ω : EdgeConfiguration d | walkIsOpen ω q} :=
      (bernoulliBondMeasure_real_walkIsOpen p q w.toPath.2.isTrail).symm
    _ ≤ twoPointConnectivity d p cubicOrigin y := measureReal_mono hsub

/-- Adding one axis edge costs at most one factor of `p`. -/
theorem density_mul_twoPointConnectivity_axis_le_succ
    {d : ℕ} (hd : 0 < d) (p : I) (n : ℕ) :
    (p : ℝ) * twoPointConnectivity d p cubicOrigin (cubicAxisVertex d n) ≤
      twoPointConnectivity d p cubicOrigin (cubicAxisVertex d (n + 1)) := by
  calc
    (p : ℝ) * twoPointConnectivity d p cubicOrigin (cubicAxisVertex d n) ≤
        twoPointConnectivity d p cubicOrigin (cubicAxisVertex d 1) *
          twoPointConnectivity d p cubicOrigin (cubicAxisVertex d n) := by
      apply mul_le_mul_of_nonneg_right _ (twoPointConnectivity_nonneg d p _ _)
      simpa using pow_le_twoPointConnectivity_axis (n := 1) hd p
    _ = twoPointConnectivity d p cubicOrigin (cubicAxisVertex d n) *
          twoPointConnectivity d p cubicOrigin (cubicAxisVertex d 1) := by ring
    _ ≤ twoPointConnectivity d p cubicOrigin (cubicAxisVertex d (n + 1)) :=
      twoPointConnectivity_axis_mul_le hd p n 1

/-- **Grimmett, Theorem 6.44, equation (6.46), lower bound.**  The constant is quantified
before `p`, hence depends only on the dimension. -/
theorem twoPointConnectivity_axis_lower_decay
    (d : ℕ) (hd : 0 < d) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ (p : I), 0 < (p : ℝ) → ∀ n : ℕ, 0 < n →
      c * (p : ℝ) / (n : ℝ) ^ (4 * (d - 1)) *
          Real.exp (-(n : ℝ) * boxRadiusDecayRate d p) ≤
        twoPointConnectivity d p cubicOrigin (cubicAxisVertex d n) := by
  obtain ⟨ce, hce, heven⟩ := twoPointConnectivity_axis_even_lower d hd
  let c : ℝ := min ce 1
  have hc : 0 < c := lt_min hce zero_lt_one
  refine ⟨c, hc, min_le_right _ _, ?_⟩
  intro p hp n hn
  have hphi : 0 ≤ boxRadiusDecayRate d p := boxRadiusDecayRate_nonneg d hd p hp
  rcases n.even_or_odd' with ⟨m, rfl | rfl⟩
  · have hm : 0 < m := by omega
    have hbase : (m : ℝ) ≤ ((2 * m : ℕ) : ℝ) := by
      norm_cast
      omega
    have hpow : (m : ℝ) ^ (4 * (d - 1)) ≤
        ((2 * m : ℕ) : ℝ) ^ (4 * (d - 1)) := by gcongr
    have hmPow : 0 < (m : ℝ) ^ (4 * (d - 1)) := by positivity
    have h2mPow : 0 < ((2 * m : ℕ) : ℝ) ^ (4 * (d - 1)) := by positivity
    have hnum : c * (p : ℝ) ≤ ce := by
      calc
        c * (p : ℝ) ≤ c * 1 := mul_le_mul_of_nonneg_left p.property.2 hc.le
        _ = c := by ring
        _ ≤ ce := min_le_left _ _
    have hfrac : c * (p : ℝ) / ((2 * m : ℕ) : ℝ) ^ (4 * (d - 1)) ≤
        ce / (m : ℝ) ^ (4 * (d - 1)) := by
      calc
        c * (p : ℝ) / ((2 * m : ℕ) : ℝ) ^ (4 * (d - 1)) ≤
            ce / ((2 * m : ℕ) : ℝ) ^ (4 * (d - 1)) :=
          div_le_div_of_nonneg_right hnum h2mPow.le
        _ ≤ ce / (m : ℝ) ^ (4 * (d - 1)) :=
          div_le_div_of_nonneg_left hce.le hmPow hpow
    exact (mul_le_mul_of_nonneg_right hfrac (Real.exp_pos _).le).trans
      (heven p hp m hm)
  · by_cases hm0 : m = 0
    · subst m
      have hexp : Real.exp (-boxRadiusDecayRate d p) ≤ 1 := by
        rw [← Real.exp_zero]
        exact Real.exp_le_exp.mpr (neg_nonpos.mpr hphi)
      have hleft : c * (p : ℝ) * Real.exp (-boxRadiusDecayRate d p) ≤ (p : ℝ) := by
        calc
          c * (p : ℝ) * Real.exp (-boxRadiusDecayRate d p) ≤
              c * (p : ℝ) * 1 := mul_le_mul_of_nonneg_left hexp (mul_nonneg hc.le p.property.1)
          _ ≤ (p : ℝ) := by nlinarith [min_le_right ce 1]
      have hpAxis : (p : ℝ) ≤
          twoPointConnectivity d p cubicOrigin (cubicAxisVertex d 1) := by
        simpa using pow_le_twoPointConnectivity_axis (n := 1) hd p
      simpa using hleft.trans hpAxis
    · have hm : 0 < m := Nat.pos_of_ne_zero hm0
      have hncast : (((2 * m + 1 : ℕ) : ℝ)) = 2 * (m : ℝ) + 1 := by norm_num
      have hmle : (m : ℝ) ≤ ((2 * m + 1 : ℕ) : ℝ) := by
        norm_cast
        omega
      have hpow : (m : ℝ) ^ (4 * (d - 1)) ≤
          ((2 * m + 1 : ℕ) : ℝ) ^ (4 * (d - 1)) := by gcongr
      have hmPow : 0 < (m : ℝ) ^ (4 * (d - 1)) := by positivity
      have hnPow : 0 < ((2 * m + 1 : ℕ) : ℝ) ^ (4 * (d - 1)) := by positivity
      have hfrac : c / ((2 * m + 1 : ℕ) : ℝ) ^ (4 * (d - 1)) ≤
          ce / (m : ℝ) ^ (4 * (d - 1)) := by
        calc
          c / ((2 * m + 1 : ℕ) : ℝ) ^ (4 * (d - 1)) ≤
              ce / ((2 * m + 1 : ℕ) : ℝ) ^ (4 * (d - 1)) :=
            div_le_div_of_nonneg_right (min_le_left _ _) hnPow.le
          _ ≤ ce / (m : ℝ) ^ (4 * (d - 1)) :=
            div_le_div_of_nonneg_left hce.le hmPow hpow
      have hexp : Real.exp (-((2 * m + 1 : ℕ) : ℝ) * boxRadiusDecayRate d p) ≤
          Real.exp (-((2 * m : ℕ) : ℝ) * boxRadiusDecayRate d p) := by
        apply Real.exp_le_exp.mpr
        rw [hncast]
        norm_num
        nlinarith
      have hinner : c / ((2 * m + 1 : ℕ) : ℝ) ^ (4 * (d - 1)) *
          Real.exp (-((2 * m + 1 : ℕ) : ℝ) * boxRadiusDecayRate d p) ≤
          ce / (m : ℝ) ^ (4 * (d - 1)) *
            Real.exp (-((2 * m : ℕ) : ℝ) * boxRadiusDecayRate d p) :=
        mul_le_mul hfrac hexp (Real.exp_pos _).le
          (div_nonneg hce.le hmPow.le)
      have hstep := density_mul_twoPointConnectivity_axis_le_succ hd p (2 * m)
      calc
        c * (p : ℝ) / ((2 * m + 1 : ℕ) : ℝ) ^ (4 * (d - 1)) *
            Real.exp (-((2 * m + 1 : ℕ) : ℝ) * boxRadiusDecayRate d p) =
          (p : ℝ) * (c / ((2 * m + 1 : ℕ) : ℝ) ^ (4 * (d - 1)) *
            Real.exp (-((2 * m + 1 : ℕ) : ℝ) * boxRadiusDecayRate d p)) := by ring
        _ ≤ (p : ℝ) * (ce / (m : ℝ) ^ (4 * (d - 1)) *
            Real.exp (-((2 * m : ℕ) : ℝ) * boxRadiusDecayRate d p)) :=
          mul_le_mul_of_nonneg_left hinner p.property.1
        _ ≤ (p : ℝ) * twoPointConnectivity d p cubicOrigin
            (cubicAxisVertex d (2 * m)) :=
          mul_le_mul_of_nonneg_left (heven p hp m hm) p.property.1
        _ ≤ twoPointConnectivity d p cubicOrigin
            (cubicAxisVertex d (2 * m + 1)) := by
          simpa [Nat.add_comm] using hstep

/-- Source-facing bundled two-sided inequality (6.46). -/
theorem twoPointConnectivity_axis_twoSided_decay
    (d : ℕ) (hd : 0 < d) :
    ∃ c : ℝ, 0 < c ∧ ∀ (p : I), 0 < (p : ℝ) → ∀ n : ℕ, 0 < n →
      c * (p : ℝ) / (n : ℝ) ^ (4 * (d - 1)) *
          Real.exp (-(n : ℝ) * boxRadiusDecayRate d p) ≤
          twoPointConnectivity d p cubicOrigin (cubicAxisVertex d n) ∧
        twoPointConnectivity d p cubicOrigin (cubicAxisVertex d n) ≤
          Real.exp (-(n : ℝ) * boxRadiusDecayRate d p) := by
  obtain ⟨c, hc, _hc1, hlower⟩ := twoPointConnectivity_axis_lower_decay d hd
  exact ⟨c, hc, fun p hp n hn ↦
    ⟨hlower p hp n hn, twoPointConnectivity_axis_le_exp_boxRadiusDecayRate hd hp hn⟩⟩

/-! ### Arbitrary vertices: signed symmetries and coordinate concatenation -/

/-- Simultaneously reflect any chosen set of coordinates through the origin. -/
def cubicSignedCoordinateEquiv {d : ℕ} (flip : Fin d → Bool) : Cubic d ≃ Cubic d where
  toFun x i := if flip i then -x i else x i
  invFun x i := if flip i then -x i else x i
  left_inv := by intro x; ext i; by_cases h : flip i <;> simp [h]
  right_inv := by intro x; ext i; by_cases h : flip i <;> simp [h]

@[simp]
theorem cubicSignedCoordinateEquiv_apply_self {d : ℕ} (flip : Fin d → Bool) (x : Cubic d) :
    cubicSignedCoordinateEquiv flip (cubicSignedCoordinateEquiv flip x) = x :=
  (cubicSignedCoordinateEquiv flip).left_inv x

theorem cubicSignedCoordinate_stepFrom {d : ℕ} (flip : Fin d → Bool)
    (x : Cubic d) (a : CubicDirection d) :
    cubicSignedCoordinateEquiv flip (cubicStepFrom x a) =
      cubicStepFrom (cubicSignedCoordinateEquiv flip x)
        (a.1, if flip a.1 then !a.2 else a.2) := by
  rcases a with ⟨i, b⟩
  ext j
  by_cases hji : j = i
  · subst j
    by_cases hf : flip i <;> cases b <;>
      simp [cubicSignedCoordinateEquiv, cubicStepFrom, cubicDirectionIncrement, hf] <;> ring
  · by_cases hf : flip j <;>
      simp [cubicSignedCoordinateEquiv, cubicStepFrom, cubicDirectionIncrement, hji, hf]

/-- Simultaneous coordinate sign changes are cubic-graph automorphisms. -/
def cubicSignedCoordinateIso {d : ℕ} (flip : Fin d → Bool) :
    cubicGraph d ≃g cubicGraph d where
  toEquiv := cubicSignedCoordinateEquiv flip
  map_rel_iff' := by
    intro x y
    rw [cubicGraph_adj_iff_exists_stepFrom, cubicGraph_adj_iff_exists_stepFrom]
    constructor
    · rintro ⟨a, ha⟩
      let a' : CubicDirection d := (a.1, if flip a.1 then !a.2 else a.2)
      refine ⟨a', ?_⟩
      have hh := congrArg (cubicSignedCoordinateEquiv flip) ha
      have hs := cubicSignedCoordinate_stepFrom flip
        (cubicSignedCoordinateEquiv flip x) a
      simpa [a'] using hh.trans hs
    · rintro ⟨a, rfl⟩
      let a' : CubicDirection d := (a.1, if flip a.1 then !a.2 else a.2)
      refine ⟨a', ?_⟩
      rw [cubicSignedCoordinate_stepFrom]

/-- Vertex obtained by taking absolute values coordinatewise. -/
def cubicAbsVertex {d : ℕ} (x : Cubic d) : Cubic d :=
  fun i ↦ (x i).natAbs

theorem cubicSignedCoordinateEquiv_to_absVertex {d : ℕ} (x : Cubic d) :
    cubicSignedCoordinateEquiv (fun i ↦ decide (x i < 0)) x = cubicAbsVertex x := by
  ext i
  by_cases hi : x i < 0
  · simp [cubicSignedCoordinateEquiv, cubicAbsVertex, hi,
      Int.natCast_natAbs, abs_of_neg hi]
  · have hi0 : 0 ≤ x i := le_of_not_gt hi
    simp [cubicSignedCoordinateEquiv, cubicAbsVertex, hi, Int.natAbs_of_nonneg hi0]

theorem twoPointConnectivity_origin_absVertex
    {d : ℕ} (p : I) (x : Cubic d) :
    twoPointConnectivity d p cubicOrigin (cubicAbsVertex x) =
      twoPointConnectivity d p cubicOrigin x := by
  have h := twoPointConnectivity_graphIso p
    (cubicSignedCoordinateIso (fun i ↦ decide (x i < 0))) cubicOrigin x
  have h0 : cubicSignedCoordinateEquiv (fun i ↦ decide (x i < 0)) cubicOrigin =
      cubicOrigin := by
    ext i
    simp [cubicSignedCoordinateEquiv, cubicOrigin]
  calc
    twoPointConnectivity d p cubicOrigin (cubicAbsVertex x) =
        twoPointConnectivity d p
          (cubicSignedCoordinateEquiv (fun i ↦ decide (x i < 0)) cubicOrigin)
          (cubicSignedCoordinateEquiv (fun i ↦ decide (x i < 0)) x) := by
      rw [h0, cubicSignedCoordinateEquiv_to_absVertex]
    _ = twoPointConnectivity d p cubicOrigin x := by
      simpa [cubicSignedCoordinateIso] using h

/-- Axis point in an arbitrary coordinate. -/
def cubicCoordinateAxisVertex {d : ℕ} (i : Fin d) (n : ℕ) : Cubic d :=
  fun j ↦ if j = i then n else 0

/-- Keep the absolute coordinates indexed by `S` and set all other coordinates to zero. -/
def cubicAbsOn {d : ℕ} (x : Cubic d) (S : Finset (Fin d)) : Cubic d :=
  fun i ↦ if i ∈ S then (x i).natAbs else 0

@[simp]
theorem cubicAbsOn_empty {d : ℕ} (x : Cubic d) :
    cubicAbsOn x ∅ = cubicOrigin := by
  ext i
  simp [cubicAbsOn, cubicOrigin]

@[simp]
theorem cubicAbsOn_univ {d : ℕ} (x : Cubic d) :
    cubicAbsOn x Finset.univ = cubicAbsVertex x := by
  ext i
  simp [cubicAbsOn, cubicAbsVertex]

theorem cubicAbsOn_insert_eq_translate_axis
    {d : ℕ} (x : Cubic d) (S : Finset (Fin d)) {i : Fin d} (hi : i ∉ S) :
    cubicAbsOn x (insert i S) =
      cubicTranslate cubicOrigin (cubicAbsOn x S)
        (cubicCoordinateAxisVertex i (x i).natAbs) := by
  ext j
  by_cases hji : j = i
  · subst j
    simp [cubicAbsOn, cubicCoordinateAxisVertex, cubicTranslate, cubicOrigin, hi]
  · simp [cubicAbsOn, cubicCoordinateAxisVertex, cubicTranslate, cubicOrigin, hji]

theorem twoPointConnectivity_coordinateAxis_eq_firstAxis
    {d : ℕ} (hd : 0 < d) (p : I) (i : Fin d) (n : ℕ) :
    twoPointConnectivity d p cubicOrigin (cubicCoordinateAxisVertex i n) =
      twoPointConnectivity d p cubicOrigin (cubicAxisVertex d n) := by
  let i0 : Fin d := ⟨0, hd⟩
  let e : Fin d ≃ Fin d := Equiv.swap i i0
  have h := twoPointConnectivity_coordinatePermutation p e cubicOrigin
    (cubicCoordinateAxisVertex i n)
  have h0 : cubicCoordinatePermutationEquiv e cubicOrigin = cubicOrigin := by
    ext j
    simp [cubicCoordinatePermutationEquiv, cubicOrigin]
  have haxis : cubicCoordinatePermutationEquiv e (cubicCoordinateAxisVertex i n) =
      cubicAxisVertex d n := by
    ext j
    by_cases hj0 : j = i0
    · subst j
      simp [e, i0, cubicCoordinatePermutationEquiv, cubicCoordinateAxisVertex,
        cubicAxisVertex]
    · have hsymm : e.symm j ≠ i := by
        intro h
        apply hj0
        simpa [e, i0] using congrArg e h
      have hjval : (j : ℕ) ≠ 0 := by
        intro hj
        apply hj0
        apply Fin.ext
        exact hj
      change (if e.symm j = i then (n : ℤ) else 0) =
        if (j : ℕ) = 0 then (n : ℤ) else 0
      rw [if_neg hsymm, if_neg hjval]
  simpa [h0, haxis] using h.symm

/-- Generic FKG triangle inequality for the two-point function. -/
theorem twoPointConnectivity_mul_le
    (d : ℕ) (p : I) (x y z : Cubic d) :
    twoPointConnectivity d p x y * twoPointConnectivity d p y z ≤
      twoPointConnectivity d p x z := by
  have hfkg := bernoulliBondMeasure_real_fkg p
    (isIncreasingEvent_connectionEvent d x y)
    (isIncreasingEvent_connectionEvent d y z)
    (measurableSet_connectionEvent d x y)
    (measurableSet_connectionEvent d y z)
  have hsub : connectionEvent d x y ∩ connectionEvent d y z ⊆ connectionEvent d x z := by
    rintro ω ⟨⟨w, hw⟩, ⟨q, hq⟩⟩
    exact ⟨w.append q, walkIsOpen_append hw hq⟩
  exact hfkg.trans (measureReal_mono hsub)

/-- Coordinate-by-coordinate FKG concatenation, the rigorous product form of (6.62)–(6.63). -/
theorem prod_axis_twoPointConnectivity_le_absOn
    {d : ℕ} (hd : 0 < d) (p : I) (x : Cubic d) (S : Finset (Fin d)) :
    (∏ i ∈ S,
      twoPointConnectivity d p cubicOrigin (cubicAxisVertex d (x i).natAbs)) ≤
      twoPointConnectivity d p cubicOrigin (cubicAbsOn x S) := by
  classical
  induction S using Finset.induction with
  | empty => simp
  | @insert i S hi ih =>
      rw [Finset.prod_insert hi]
      let base := cubicAbsOn x S
      let step := cubicCoordinateAxisVertex i (x i).natAbs
      have htranslated :
          twoPointConnectivity d p base (cubicAbsOn x (insert i S)) =
            twoPointConnectivity d p cubicOrigin step := by
        have ht := twoPointConnectivity_translate p cubicOrigin base cubicOrigin step
        have hbase : cubicTranslate cubicOrigin base cubicOrigin = base := by
          ext j
          simp [cubicTranslate, cubicOrigin, base]
        have hout : cubicTranslate cubicOrigin base step = cubicAbsOn x (insert i S) := by
          rw [cubicAbsOn_insert_eq_translate_axis x S hi]
        simpa [hbase, hout] using ht
      have hsegment :
          twoPointConnectivity d p base (cubicAbsOn x (insert i S)) =
            twoPointConnectivity d p cubicOrigin
              (cubicAxisVertex d (x i).natAbs) := by
        exact htranslated.trans
          (twoPointConnectivity_coordinateAxis_eq_firstAxis hd p i (x i).natAbs)
      calc
        twoPointConnectivity d p cubicOrigin (cubicAxisVertex d (x i).natAbs) *
            (∏ j ∈ S,
              twoPointConnectivity d p cubicOrigin (cubicAxisVertex d (x j).natAbs)) ≤
          twoPointConnectivity d p cubicOrigin (cubicAxisVertex d (x i).natAbs) *
            twoPointConnectivity d p cubicOrigin base :=
          mul_le_mul_of_nonneg_left ih (twoPointConnectivity_nonneg d p _ _)
        _ = twoPointConnectivity d p cubicOrigin base *
            twoPointConnectivity d p base (cubicAbsOn x (insert i S)) := by
          rw [hsegment]
          ring
        _ ≤ twoPointConnectivity d p cubicOrigin (cubicAbsOn x (insert i S)) :=
          twoPointConnectivity_mul_le d p cubicOrigin base (cubicAbsOn x (insert i S))

/-- Product lower bound for an arbitrary displacement. -/
theorem prod_axis_twoPointConnectivity_le
    {d : ℕ} (hd : 0 < d) (p : I) (x : Cubic d) :
    (∏ i : Fin d,
      twoPointConnectivity d p cubicOrigin (cubicAxisVertex d (x i).natAbs)) ≤
      twoPointConnectivity d p cubicOrigin x := by
  calc
    (∏ i : Fin d,
      twoPointConnectivity d p cubicOrigin (cubicAxisVertex d (x i).natAbs)) =
        ∏ i ∈ (Finset.univ : Finset (Fin d)),
          twoPointConnectivity d p cubicOrigin (cubicAxisVertex d (x i).natAbs) := by simp
    _ ≤ twoPointConnectivity d p cubicOrigin (cubicAbsOn x Finset.univ) :=
      prod_axis_twoPointConnectivity_le_absOn hd p x Finset.univ
    _ = twoPointConnectivity d p cubicOrigin x := by
      rw [cubicAbsOn_univ, twoPointConnectivity_origin_absVertex]

/-- Source-faithful arbitrary-point lower bound from Proposition 6.47.  The nonzero hypothesis
removes the printed negative-power junk value at `x = 0`. -/
theorem twoPointConnectivity_lower_decay
    (d : ℕ) (hd : 0 < d) :
    ∃ lambda : ℝ, 0 < lambda ∧ ∀ (p : I), 0 < (p : ℝ) → ∀ x : Cubic d, x ≠ cubicOrigin →
      lambda * (p : ℝ) ^ (d * cubicL1Dist cubicOrigin x) /
          (cubicL1Dist cubicOrigin x : ℝ) ^ (4 * d * (d - 1)) *
          Real.exp (-(cubicL1Dist cubicOrigin x : ℝ) * boxRadiusDecayRate d p) ≤
        twoPointConnectivity d p cubicOrigin x := by
  obtain ⟨c, hc, hc1, haxis⟩ := twoPointConnectivity_axis_lower_decay d hd
  refine ⟨c ^ d, pow_pos hc d, ?_⟩
  intro p hp x hx
  let N := cubicL1Dist cubicOrigin x
  let k := 4 * (d - 1)
  have hN : 0 < N := by
    by_contra hzero
    have : cubicL1Dist cubicOrigin x = 0 := Nat.eq_zero_of_not_pos hzero
    exact hx (cubicL1Dist_eq_zero_iff.mp this).symm
  have hphi : 0 ≤ boxRadiusDecayRate d p := boxRadiusDecayRate_nonneg d hd p hp
  have hcoord : ∀ i : Fin d,
      c * (p : ℝ) ^ N / (N : ℝ) ^ k *
          Real.exp (-((x i).natAbs : ℝ) * boxRadiusDecayRate d p) ≤
        twoPointConnectivity d p cubicOrigin (cubicAxisVertex d (x i).natAbs) := by
    intro i
    by_cases hi : (x i).natAbs = 0
    · have hpowP : (p : ℝ) ^ N ≤ 1 := pow_le_one₀ p.property.1 p.property.2
      have hNPow : (1 : ℝ) ≤ (N : ℝ) ^ k := one_le_pow₀ (by exact_mod_cast hN)
      have hfrac : c * (p : ℝ) ^ N / (N : ℝ) ^ k ≤ 1 := by
        apply (div_le_iff₀ (pow_pos (by positivity : (0 : ℝ) < N) k)).2
        calc
          c * (p : ℝ) ^ N ≤ c * 1 :=
            mul_le_mul_of_nonneg_left hpowP hc.le
          _ ≤ 1 := by simpa using hc1
          _ ≤ 1 * (N : ℝ) ^ k := by simpa using hNPow
      have haxis0 : cubicAxisVertex d 0 = cubicOrigin := by
        ext j
        simp [cubicAxisVertex, cubicOrigin]
      rw [hi, haxis0, twoPointConnectivity_self]
      simpa using hfrac
    · have hiPos : 0 < (x i).natAbs := Nat.pos_of_ne_zero hi
      have hiN : (x i).natAbs ≤ N := by
        calc
          (x i).natAbs = (x i - cubicOrigin i).natAbs := by simp [cubicOrigin]
          _ ≤ ∑ j, (x j - cubicOrigin j).natAbs :=
            Finset.single_le_sum
              (fun j _ ↦ Nat.zero_le (x j - cubicOrigin j).natAbs)
              (Finset.mem_univ i)
          _ = N := rfl
      have hpN : (p : ℝ) ^ N ≤ (p : ℝ) := by
        simpa using pow_le_pow_of_le_one p.property.1 p.property.2 hN
      have hpowDen : (((x i).natAbs : ℝ)) ^ k ≤ (N : ℝ) ^ k := by
        exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast hiN) k
      have hiPow : 0 < (((x i).natAbs : ℝ)) ^ k := by positivity
      have hNPow : 0 < (N : ℝ) ^ k := by positivity
      have hfrac : c * (p : ℝ) ^ N / (N : ℝ) ^ k ≤
          c * (p : ℝ) / ((x i).natAbs : ℝ) ^ k := by
        calc
          c * (p : ℝ) ^ N / (N : ℝ) ^ k ≤
              c * (p : ℝ) / (N : ℝ) ^ k :=
            div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left hpN hc.le) hNPow.le
          _ ≤ c * (p : ℝ) / ((x i).natAbs : ℝ) ^ k :=
            div_le_div_of_nonneg_left (mul_nonneg hc.le p.property.1) hiPow hpowDen
      exact (mul_le_mul_of_nonneg_right hfrac (Real.exp_pos _).le).trans
        (by simpa [k] using haxis p hp (x i).natAbs hiPos)
  have hprod : (∏ i : Fin d,
      (c * (p : ℝ) ^ N / (N : ℝ) ^ k *
        Real.exp (-((x i).natAbs : ℝ) * boxRadiusDecayRate d p))) ≤
      ∏ i : Fin d,
        twoPointConnectivity d p cubicOrigin (cubicAxisVertex d (x i).natAbs) := by
    exact Finset.prod_le_prod (fun _ _ ↦ by positivity) (fun i _ ↦ hcoord i)
  have hsum : (∑ i : Fin d, (x i).natAbs : ℝ) = N := by
    norm_cast
    simpa [N, cubicL1Dist, cubicOrigin]
  have heq : (∏ i : Fin d,
      (c * (p : ℝ) ^ N / (N : ℝ) ^ k *
        Real.exp (-((x i).natAbs : ℝ) * boxRadiusDecayRate d p))) =
      c ^ d * (p : ℝ) ^ (d * N) / (N : ℝ) ^ (4 * d * (d - 1)) *
        Real.exp (-(N : ℝ) * boxRadiusDecayRate d p) := by
    rw [Finset.prod_mul_distrib]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [← Real.exp_sum]
    have hexpSum : (∑ i : Fin d, -((x i).natAbs : ℝ) * boxRadiusDecayRate d p) =
        -(N : ℝ) * boxRadiusDecayRate d p := by
      rw [← Finset.sum_mul]
      congr 1
      rw [Finset.sum_neg_distrib, hsum]
    rw [hexpSum]
    dsimp [k]
    rw [div_pow, mul_pow]
    have hpEq : ((p : ℝ) ^ N) ^ d = (p : ℝ) ^ (d * N) := by
      rw [← pow_mul, Nat.mul_comm]
    have hdenEq : (((N : ℝ) ^ (4 * (d - 1))) ^ d) =
        (N : ℝ) ^ (4 * d * (d - 1)) := by
      rw [← pow_mul]
      congr 1
      ring
    rw [hpEq, hdenEq]
  rw [← heq]
  exact hprod.trans (prod_axis_twoPointConnectivity_le hd p x)

/-! ### Proposition 6.47: the arbitrary-point upper bound -/

theorem cubicAbsVertex_mem_positive_face_of_mem_face
    {d n : ℕ} {x : Cubic d} {i : Fin d} {positive : Bool}
    (hx : x ∈ cubicBoxFace d cubicOrigin n i positive) :
    cubicAbsVertex x ∈ cubicBoxFace d cubicOrigin n i true := by
  rw [mem_cubicBoxFace] at hx ⊢
  constructor
  · simp only [cubicAbsVertex, if_true, cubicOrigin, zero_add]
    rcases positive with _ | _
    · simp [cubicOrigin] at hx
      rw [hx.1]
      simp
    · simp [cubicOrigin] at hx
      rw [hx.1]
      simp
  · intro j hji
    have hj := hx.2 j hji
    simp [cubicOrigin] at hj
    constructor
    · have hnonneg : (0 : ℤ) ≤ cubicAbsVertex x j := by
        simp [cubicAbsVertex]
      have hnegN : (-(n : ℤ)) ≤ 0 := neg_nonpos.mpr (by positivity)
      simpa [cubicOrigin] using hnegN.trans hnonneg
    · by_cases hxj : 0 ≤ x j
      · simpa [cubicAbsVertex, cubicOrigin, Int.natAbs_of_nonneg hxj] using hj.2
      · have hxj' : x j ≤ 0 := le_of_not_ge hxj
        have hneg : -(x j) ≤ (n : ℤ) := by linarith [hj.1]
        simpa [cubicAbsVertex, cubicOrigin, Int.natCast_natAbs,
          abs_of_nonpos hxj'] using hneg

theorem exists_absVertex_mem_positive_face_of_mem_surface
    {d n : ℕ} (hd : 0 < d) {x : Cubic d}
    (hx : x ∈ cubicBoxSurface d cubicOrigin n) :
    ∃ i : Fin d,
      cubicAbsVertex x ∈ cubicBoxFace d cubicOrigin n i true := by
  have hfaces := cubicBoxSurface_subset_faces (x := cubicOrigin) hd hx
  rw [cubicBoxFaces, Finset.mem_biUnion] at hfaces
  rcases hfaces with ⟨i, _hi, hface⟩
  rw [Finset.mem_union] at hface
  rcases hface with hpos | hneg
  · exact ⟨i, cubicAbsVertex_mem_positive_face_of_mem_face hpos⟩
  · exact ⟨i, cubicAbsVertex_mem_positive_face_of_mem_face hneg⟩

/-- Reflection in the affine hyperplane whose `i`-th coordinate is `n`. -/
def cubicCoordinateHyperplaneReflectionIso {d : ℕ} (i : Fin d) (n : ℕ) :
    cubicGraph d ≃g cubicGraph d :=
  (cubicCoordinateReflectionIso i).trans
    (cubicTranslationIso cubicOrigin (cubicCoordinateAxisVertex i (2 * n)))

@[simp]
theorem cubicCoordinateHyperplaneReflectionIso_origin
    {d n : ℕ} (i : Fin d) :
    cubicCoordinateHyperplaneReflectionIso i n cubicOrigin =
      cubicCoordinateAxisVertex i (2 * n) := by
  ext j
  simp [cubicCoordinateHyperplaneReflectionIso, cubicCoordinateReflectionIso,
    cubicCoordinateReflectionEquiv, cubicTranslationIso_apply, cubicTranslate,
    cubicCoordinateAxisVertex, cubicOrigin]

theorem cubicCoordinateHyperplaneReflectionIso_fix_positive_face
    {d n : ℕ} (i : Fin d) {y : Cubic d}
    (hy : y ∈ cubicBoxFace d cubicOrigin n i true) :
    cubicCoordinateHyperplaneReflectionIso i n y = y := by
  rw [mem_cubicBoxFace] at hy
  ext j
  by_cases hji : j = i
  · subst j
    simp [cubicCoordinateHyperplaneReflectionIso, cubicCoordinateReflectionIso,
      cubicCoordinateReflectionEquiv, cubicTranslationIso_apply, cubicTranslate,
      cubicCoordinateAxisVertex, cubicOrigin] at hy ⊢
    omega
  · simp [cubicCoordinateHyperplaneReflectionIso, cubicCoordinateReflectionIso,
      cubicCoordinateReflectionEquiv, cubicTranslationIso_apply, cubicTranslate,
      cubicCoordinateAxisVertex, cubicOrigin, hji]

theorem twoPointConnectivity_positive_face_sq_le_coordinateAxis
    {d n : ℕ} (p : I) (i : Fin d) {y : Cubic d}
    (hy : y ∈ cubicBoxFace d cubicOrigin n i true) :
    twoPointConnectivity d p cubicOrigin y ^ 2 ≤
      twoPointConnectivity d p cubicOrigin (cubicCoordinateAxisVertex i (2 * n)) := by
  have hreflect : twoPointConnectivity d p y (cubicCoordinateAxisVertex i (2 * n)) =
      twoPointConnectivity d p cubicOrigin y := by
    have h := twoPointConnectivity_graphIso p
      (cubicCoordinateHyperplaneReflectionIso i n) cubicOrigin y
    rw [twoPointConnectivity_comm]
    simpa [cubicCoordinateHyperplaneReflectionIso_origin,
      cubicCoordinateHyperplaneReflectionIso_fix_positive_face i hy] using h
  let A := connectionEvent d cubicOrigin y
  let B := connectionEvent d y (cubicCoordinateAxisVertex i (2 * n))
  have hfkg := bernoulliBondMeasure_real_fkg p
    (isIncreasingEvent_connectionEvent d cubicOrigin y)
    (isIncreasingEvent_connectionEvent d y (cubicCoordinateAxisVertex i (2 * n)))
    (measurableSet_connectionEvent d cubicOrigin y)
    (measurableSet_connectionEvent d y (cubicCoordinateAxisVertex i (2 * n)))
  have hsub : A ∩ B ⊆ connectionEvent d cubicOrigin (cubicCoordinateAxisVertex i (2 * n)) := by
    rintro ω ⟨⟨w, hw⟩, ⟨q, hq⟩⟩
    exact ⟨w.append q, walkIsOpen_append hw hq⟩
  calc
    twoPointConnectivity d p cubicOrigin y ^ 2 =
        (bernoulliBondMeasure d p).real A * (bernoulliBondMeasure d p).real B := by
      rw [pow_two]
      change twoPointConnectivity d p cubicOrigin y *
          twoPointConnectivity d p cubicOrigin y =
        twoPointConnectivity d p cubicOrigin y *
          twoPointConnectivity d p y (cubicCoordinateAxisVertex i (2 * n))
      rw [hreflect]
    _ ≤ (bernoulliBondMeasure d p).real (A ∩ B) := hfkg
    _ ≤ twoPointConnectivity d p cubicOrigin (cubicCoordinateAxisVertex i (2 * n)) :=
      measureReal_mono hsub

theorem twoPointConnectivity_sq_le_axis_of_mem_surface
    {d n : ℕ} (hd : 0 < d) (p : I) {x : Cubic d}
    (hx : x ∈ cubicBoxSurface d cubicOrigin n) :
    twoPointConnectivity d p cubicOrigin x ^ 2 ≤
      twoPointConnectivity d p cubicOrigin (cubicAxisVertex d (2 * n)) := by
  obtain ⟨i, hi⟩ := exists_absVertex_mem_positive_face_of_mem_surface hd hx
  have hsquare := twoPointConnectivity_positive_face_sq_le_coordinateAxis p i hi
  rw [twoPointConnectivity_coordinateAxis_eq_firstAxis hd p i (2 * n)] at hsquare
  rwa [twoPointConnectivity_origin_absVertex] at hsquare

/-- Upper inequality in Proposition 6.47. -/
theorem twoPointConnectivity_le_exp_neg_lInfDist_mul_rate
    {d : ℕ} (hd : 0 < d) {p : I} (hp : 0 < (p : ℝ)) (x : Cubic d) :
    twoPointConnectivity d p cubicOrigin x ≤
      Real.exp (-(cubicLInfDist cubicOrigin x : ℝ) * boxRadiusDecayRate d p) := by
  let n := cubicLInfDist cubicOrigin x
  by_cases hn : n = 0
  · have hl1 : cubicL1Dist cubicOrigin x = 0 := by
      apply Nat.eq_zero_of_le_zero
      calc
        cubicL1Dist cubicOrigin x ≤ d * cubicLInfDist cubicOrigin x :=
          cubicL1Dist_le_card_mul_lInfDist _ _
        _ = 0 := by rw [show cubicLInfDist cubicOrigin x = 0 from hn]; simp
    have hx0 : x = cubicOrigin := (cubicL1Dist_eq_zero_iff.mp hl1).symm
    subst x
    simp [n, twoPointConnectivity_self]
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have hxSurface : x ∈ cubicBoxSurface d cubicOrigin n := by
    rw [mem_cubicBoxSurface]
  have hsq := twoPointConnectivity_sq_le_axis_of_mem_surface hd p hxSurface
  have haxis := twoPointConnectivity_axis_le_exp_boxRadiusDecayRate hd hp
    (show 0 < 2 * n by omega)
  have hsqExp := hsq.trans haxis
  have hphi := boxRadiusDecayRate_nonneg d hd p hp
  have hexpSq : Real.exp (-(n : ℝ) * boxRadiusDecayRate d p) ^ 2 =
      Real.exp (-((2 * n : ℕ) : ℝ) * boxRadiusDecayRate d p) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    norm_num
    ring
  apply (sq_le_sq₀ (twoPointConnectivity_nonneg d p _ _)
    (Real.exp_pos _).le).mp
  rw [hexpSq]
  exact hsqExp

/-- **Grimmett, Proposition 6.47 (6.48).** Exact lower polynomial/power factor and the
polynomial-free `L∞` upper bound. -/
theorem twoPointConnectivity_twoSided_decay
    (d : ℕ) (hd : 0 < d) :
    ∃ lambda : ℝ, 0 < lambda ∧ ∀ (p : I), 0 < (p : ℝ) → ∀ x : Cubic d,
      (x ≠ cubicOrigin →
        lambda * (p : ℝ) ^ (d * cubicL1Dist cubicOrigin x) /
            (cubicL1Dist cubicOrigin x : ℝ) ^ (4 * d * (d - 1)) *
            Real.exp (-(cubicL1Dist cubicOrigin x : ℝ) * boxRadiusDecayRate d p) ≤
          twoPointConnectivity d p cubicOrigin x) ∧
      twoPointConnectivity d p cubicOrigin x ≤
        Real.exp (-(cubicLInfDist cubicOrigin x : ℝ) * boxRadiusDecayRate d p) := by
  obtain ⟨lambda, hlambda, hlower⟩ := twoPointConnectivity_lower_decay d hd
  exact ⟨lambda, hlambda, fun p hp x ↦
    ⟨hlower p hp x, twoPointConnectivity_le_exp_neg_lInfDist_mul_rate hd hp x⟩⟩

/-! ### Proposition 6.49: susceptibility and correlation length -/

/-- Real shell mass `Eₚ Mₙ` from (6.66). -/
noncomputable def radiusSphereConnectionMassReal (d : ℕ) (p : I) (n : ℕ) : ℝ :=
  (radiusSphereConnectionMass d p n).toReal

theorem radiusTail_mul_radius_le_shellMass_pow
    (d : ℕ) (p : I) (m r : ℕ) :
    radiusTail d p (r * m) ≤ radiusSphereConnectionMassReal d p m ^ r := by
  induction r with
  | zero => simp [radiusSphereConnectionMassReal]
  | succ r ih =>
      have hblock := radiusTail_add_le_sphereConnectionSum_mul d p m (r * m)
      have hmass := radiusSphereConnectionMass_toReal d p m
      rw [← hmass] at hblock
      rw [Nat.succ_mul, pow_succ']
      simpa [radiusSphereConnectionMassReal, Nat.add_comm] using
        hblock.trans (mul_le_mul_of_nonneg_left ih ENNReal.toReal_nonneg)

theorem twoPointConnectivity_le_radiusTail_l1
    (d : ℕ) (p : I) (x : Cubic d) :
    twoPointConnectivity d p cubicOrigin x ≤
      radiusTail d p (cubicL1Dist cubicOrigin x) := by
  have hsub : connectionEvent d cubicOrigin x ⊆
      radiusConnectionEvent d cubicOrigin (cubicL1Dist cubicOrigin x) := by
    intro ω hω
    rw [mem_radiusConnectionEvent_iff_exists_connection]
    exact ⟨x, by rw [mem_cubicMetricSphere_iff_l1Dist_eq], hω⟩
  exact measureReal_mono hsub

/-- Integer dilation of a cubic vertex. -/
def cubicNatScale {d : ℕ} (k : ℕ) (x : Cubic d) : Cubic d :=
  fun i ↦ (k : ℤ) * x i

@[simp]
theorem cubicNatScale_zero {d : ℕ} (x : Cubic d) :
    cubicNatScale 0 x = cubicOrigin := by
  ext i
  simp [cubicNatScale, cubicOrigin]

theorem cubicNatScale_succ {d : ℕ} (k : ℕ) (x : Cubic d) :
    cubicNatScale (k + 1) x =
      cubicTranslate cubicOrigin (cubicNatScale k x) x := by
  ext i
  simp [cubicNatScale, cubicTranslate, cubicOrigin]
  ring

theorem cubicL1Dist_origin_natScale {d : ℕ} (k : ℕ) (x : Cubic d) :
    cubicL1Dist cubicOrigin (cubicNatScale k x) =
      k * cubicL1Dist cubicOrigin x := by
  simp only [cubicL1Dist, cubicOrigin, cubicNatScale, Pi.zero_apply, sub_zero]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Int.natAbs_mul]
  simp

/-- Repeated FKG concatenation along the points `0,u,2u,…,ku`. -/
theorem twoPointConnectivity_pow_le_natScale
    (d : ℕ) (p : I) (x : Cubic d) (k : ℕ) :
    twoPointConnectivity d p cubicOrigin x ^ k ≤
      twoPointConnectivity d p cubicOrigin (cubicNatScale k x) := by
  induction k with
  | zero => simp [twoPointConnectivity_self]
  | succ k ih =>
      have hsegment : twoPointConnectivity d p (cubicNatScale k x)
          (cubicNatScale (k + 1) x) = twoPointConnectivity d p cubicOrigin x := by
        have ht := twoPointConnectivity_translate p cubicOrigin (cubicNatScale k x)
          cubicOrigin x
        have hbase : cubicTranslate cubicOrigin (cubicNatScale k x) cubicOrigin =
            cubicNatScale k x := by
          ext i
          simp [cubicTranslate, cubicOrigin]
        rw [hbase, ← cubicNatScale_succ] at ht
        exact ht
      rw [pow_succ]
      calc
        twoPointConnectivity d p cubicOrigin x ^ k *
            twoPointConnectivity d p cubicOrigin x ≤
          twoPointConnectivity d p cubicOrigin (cubicNatScale k x) *
            twoPointConnectivity d p cubicOrigin x :=
          mul_le_mul_of_nonneg_right ih (twoPointConnectivity_nonneg d p _ _)
        _ = twoPointConnectivity d p cubicOrigin (cubicNatScale k x) *
            twoPointConnectivity d p (cubicNatScale k x) (cubicNatScale (k + 1) x) := by
          rw [hsegment]
        _ ≤ twoPointConnectivity d p cubicOrigin (cubicNatScale (k + 1) x) :=
          twoPointConnectivity_mul_le d p cubicOrigin (cubicNatScale k x)
            (cubicNatScale (k + 1) x)

/-- Finite-`k` estimate behind (6.71). -/
theorem twoPointConnectivity_pow_le_shellMass_pow_floor
    (d : ℕ) (p : I) (x : Cubic d) {m : ℕ} (hm : 0 < m) (k : ℕ) :
    twoPointConnectivity d p cubicOrigin x ^ k ≤
      radiusSphereConnectionMassReal d p m ^
        ((k * cubicL1Dist cubicOrigin x) / m) := by
  let r := (k * cubicL1Dist cubicOrigin x) / m
  have hrm : r * m ≤ k * cubicL1Dist cubicOrigin x := by
    exact Nat.div_mul_le_self _ _
  calc
    twoPointConnectivity d p cubicOrigin x ^ k ≤
        twoPointConnectivity d p cubicOrigin (cubicNatScale k x) :=
      twoPointConnectivity_pow_le_natScale d p x k
    _ ≤ radiusTail d p (k * cubicL1Dist cubicOrigin x) := by
      simpa [cubicL1Dist_origin_natScale] using
        twoPointConnectivity_le_radiusTail_l1 d p (cubicNatScale k x)
    _ ≤ radiusTail d p (r * m) := radiusTail_antitone d p hrm
    _ ≤ radiusSphereConnectionMassReal d p m ^ r :=
      radiusTail_mul_radius_le_shellMass_pow d p m r

theorem summable_radiusSphereConnectionMassReal
    {d : ℕ} {p : I} (hchi : susceptibility d p < ⊤) :
    Summable (radiusSphereConnectionMassReal d p) := by
  apply ENNReal.summable_toReal
  rw [tsum_radiusSphereConnectionMass]
  exact ne_of_lt hchi

theorem tsum_radiusSphereConnectionMassReal
    {d : ℕ} {p : I} (hchi : susceptibility d p < ⊤) :
    ∑' n : ℕ, radiusSphereConnectionMassReal d p n =
      (susceptibility d p).toReal := by
  change (∑' n : ℕ, (radiusSphereConnectionMass d p n).toReal) = _
  rw [← ENNReal.tsum_toReal_eq]
  · rw [tsum_radiusSphereConnectionMass]
  · intro n
    exact ne_of_lt ((ENNReal.le_tsum n).trans_lt <| by
      rw [tsum_radiusSphereConnectionMass]
      exact hchi)

@[simp]
theorem radiusSphereConnectionMassReal_zero (d : ℕ) (p : I) :
    radiusSphereConnectionMassReal d p 0 = 1 := by
  rw [radiusSphereConnectionMassReal, radiusSphereConnectionMass_toReal]
  have hsphere : cubicMetricSphere d cubicOrigin 0 = {cubicOrigin} := by
    ext x
    simp [mem_cubicMetricSphere_iff_l1Dist_eq, cubicL1Dist_eq_zero_iff]
  rw [hsphere]
  simp only [Finset.sum_singleton]
  have hconn : connectionEvent d cubicOrigin cubicOrigin = Set.univ := by
    apply Set.eq_univ_of_forall
    intro ω
    exact ⟨SimpleGraph.Walk.nil, by simp [walkIsOpen]⟩
  rw [hconn]
  simp

theorem density_le_radiusSphereConnectionMassReal_one
    {d : ℕ} (hd : 0 < d) (p : I) :
    (p : ℝ) ≤ radiusSphereConnectionMassReal d p 1 := by
  rw [radiusSphereConnectionMassReal, radiusSphereConnectionMass_toReal]
  have hy : cubicAxisVertex d 1 ∈ cubicMetricSphere d cubicOrigin 1 := by
    rw [mem_cubicMetricSphere_iff_l1Dist_eq, cubicL1Dist_origin_axisVertex hd]
  calc
    (p : ℝ) ≤ twoPointConnectivity d p cubicOrigin (cubicAxisVertex d 1) := by
      simpa using pow_le_twoPointConnectivity_axis (n := 1) hd p
    _ ≤ ∑ y ∈ cubicMetricSphere d cubicOrigin 1,
        (bernoulliBondMeasure d p).real (connectionEvent d cubicOrigin y) := by
      apply Finset.single_le_sum (fun y _ ↦ measureReal_nonneg) hy

theorem one_lt_susceptibility_toReal_of_pos
    {d : ℕ} (hd : 0 < d) {p : I} (hp : 0 < (p : ℝ))
    (hchi : susceptibility d p < ⊤) :
    1 < (susceptibility d p).toReal := by
  have hsumm := summable_radiusSphereConnectionMassReal hchi
  have hpartial := hsumm.sum_le_tsum ({0, 1} : Finset ℕ)
    (fun n _ ↦ ENNReal.toReal_nonneg)
  change (∑ i ∈ ({0, 1} : Finset ℕ), radiusSphereConnectionMassReal d p i) ≤
    ∑' i : ℕ, radiusSphereConnectionMassReal d p i at hpartial
  rw [tsum_radiusSphereConnectionMassReal hchi] at hpartial
  have hmass1 := density_le_radiusSphereConnectionMassReal_one hd p
  simp only [Finset.sum_insert, Finset.mem_singleton, zero_ne_one, not_false_eq_true,
    Finset.sum_singleton, radiusSphereConnectionMassReal_zero] at hpartial
  linarith

/-- The geometric comparison scale (6.72). -/
theorem exists_shellMass_le_one_sub_susceptibility_inv_pow
    {d : ℕ} (hd : 0 < d) {p : I} (hp : 0 < (p : ℝ))
    (hchi : susceptibility d p < ⊤) :
    ∃ m : ℕ, 0 < m ∧
      radiusSphereConnectionMassReal d p m ≤
        (1 - ((susceptibility d p).toReal)⁻¹) ^ m := by
  let chi := (susceptibility d p).toReal
  let q := 1 - chi⁻¹
  have hchi1 : 1 < chi := one_lt_susceptibility_toReal_of_pos hd hp hchi
  have hq0 : 0 < q := by dsimp [q]; exact sub_pos.mpr (inv_lt_one_of_one_lt₀ hchi1)
  have hq1 : q < 1 := by dsimp [q]; exact sub_lt_self _ (inv_pos.mpr (zero_lt_one.trans hchi1))
  have hgeom : Summable (fun n : ℕ ↦ q ^ n) := summable_geometric_of_norm_lt_one (by
    rw [Real.norm_eq_abs, abs_of_pos hq0]
    exact hq1)
  have hmassSumm := summable_radiusSphereConnectionMassReal hchi
  by_contra hnone
  push_neg at hnone
  have hle : ∀ n : ℕ, q ^ n ≤ radiusSphereConnectionMassReal d p n := by
    intro n
    by_cases hn : n = 0
    · subst n
      simp [q]
    · exact (hnone n (Nat.pos_of_ne_zero hn)).le
  have hstrict : q ^ 1 < radiusSphereConnectionMassReal d p 1 :=
    hnone 1 (by omega)
  have htsumlt : ∑' n : ℕ, q ^ n <
      ∑' n : ℕ, radiusSphereConnectionMassReal d p n :=
    hgeom.tsum_lt_tsum hle hstrict hmassSumm
  rw [tsum_geometric_of_norm_lt_one (by
      rw [Real.norm_eq_abs, abs_of_pos hq0]
      exact hq1), tsum_radiusSphereConnectionMassReal hchi] at htsumlt
  dsimp [q, chi] at htsumlt
  have hchi0 : (0 : ℝ) < (susceptibility d p).toReal := zero_lt_one.trans hchi1
  field_simp at htsumlt
  linarith

/-- Grimmett, Proposition 6.49, equation (6.65).  Whenever susceptibility is finite and the
density is positive, the two-point function is bounded by the geometric profile determined by
susceptibility.  The proof takes the finite concatenation estimate at `k = m`; this avoids any
passage to a limit or logarithm and therefore keeps all endpoint conventions explicit. -/
theorem twoPointConnectivity_le_one_sub_susceptibility_inv_pow
    {d : ℕ} (hd : 0 < d) {p : I} (hp : 0 < (p : ℝ))
    (hchi : susceptibility d p < ⊤) (x : Cubic d) :
    twoPointConnectivity d p cubicOrigin x ≤
      (1 - ((susceptibility d p).toReal)⁻¹) ^ cubicL1Dist cubicOrigin x := by
  obtain ⟨m, hm, hmass⟩ :=
    exists_shellMass_le_one_sub_susceptibility_inv_pow hd hp hchi
  let q : ℝ := 1 - ((susceptibility d p).toReal)⁻¹
  let N := cubicL1Dist cubicOrigin x
  have hchi1 : 1 < (susceptibility d p).toReal :=
    one_lt_susceptibility_toReal_of_pos hd hp hchi
  have hq0 : 0 ≤ q := by
    dsimp [q]
    exact (sub_pos.mpr (inv_lt_one_of_one_lt₀ hchi1)).le
  have hfinite := twoPointConnectivity_pow_le_shellMass_pow_floor
    d p x hm m
  have hdiv : (m * N) / m = N := by
    rw [Nat.mul_comm m N, Nat.mul_div_left _ hm]
  change twoPointConnectivity d p cubicOrigin x ^ m ≤
      radiusSphereConnectionMassReal d p m ^ ((m * N) / m) at hfinite
  rw [hdiv] at hfinite
  have hmass' : radiusSphereConnectionMassReal d p m ≤ q ^ m := by
    simpa [q] using hmass
  have hpow : twoPointConnectivity d p cubicOrigin x ^ m ≤ (q ^ N) ^ m := by
    calc
      twoPointConnectivity d p cubicOrigin x ^ m ≤
          radiusSphereConnectionMassReal d p m ^ N := hfinite
      _ ≤ (q ^ m) ^ N :=
        pow_le_pow_left₀ (by exact ENNReal.toReal_nonneg) hmass' N
      _ = (q ^ N) ^ m := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  exact le_of_pow_le_pow_left₀ (Nat.ne_of_gt hm) (pow_nonneg hq0 N) hpow

/-- Subcritical specialization of Proposition 6.49. -/
theorem twoPointConnectivity_le_one_sub_susceptibility_inv_pow_of_lt_critical
    {d : ℕ} (hd : 2 ≤ d) {p : I} (hp : 0 < (p : ℝ))
    (hpc : (p : ℝ) < cubicCriticalProbability d) (x : Cubic d) :
    twoPointConnectivity d p cubicOrigin x ≤
      (1 - ((susceptibility d p).toReal)⁻¹) ^ cubicL1Dist cubicOrigin x :=
  twoPointConnectivity_le_one_sub_susceptibility_inv_pow (by omega) hp
    (susceptibility_lt_top_of_lt_critical d hd p hpc) x

/-- The logarithmic consequence of Proposition 6.49: the inverse susceptibility is a lower
bound for the box-radius decay rate. -/
theorem susceptibility_toReal_inv_le_boxRadiusDecayRate
    {d : ℕ} (hd : 0 < d) {p : I} (hp : 0 < (p : ℝ))
    (hchi : susceptibility d p < ⊤) :
    ((susceptibility d p).toReal)⁻¹ ≤ boxRadiusDecayRate d p := by
  let chi : ℝ := (susceptibility d p).toReal
  let q : ℝ := 1 - chi⁻¹
  have hchi1 : 1 < chi := one_lt_susceptibility_toReal_of_pos hd hp hchi
  have hq0 : 0 < q := by
    dsimp [q]
    exact sub_pos.mpr (inv_lt_one_of_one_lt₀ hchi1)
  have hinvLog : chi⁻¹ ≤ -Real.log q := by
    have hlog := Real.log_le_sub_one_of_pos hq0
    dsimp [q] at hlog
    linarith
  have hlogRate : -Real.log q ≤ boxRadiusDecayRate d p := by
    have hlimit := twoPointConnectivity_axis_logRate_tendsto hd hp
    have hconst : Tendsto (fun _n : ℕ ↦ -Real.log q) atTop (𝓝 (-Real.log q)) :=
      tendsto_const_nhds
    apply le_of_tendsto_of_tendsto hconst hlimit
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (zero_lt_one.trans_le hn)
    have hτ : 0 < twoPointConnectivity d p cubicOrigin (cubicAxisVertex d n) :=
      twoPointConnectivity_pos d hp _ _
    have hbound := twoPointConnectivity_le_one_sub_susceptibility_inv_pow
      hd hp hchi (cubicAxisVertex d n)
    rw [cubicL1Dist_origin_axisVertex hd] at hbound
    change twoPointConnectivity d p cubicOrigin (cubicAxisVertex d n) ≤ q ^ n at hbound
    have hlog := Real.log_le_log hτ hbound
    rw [Real.log_pow] at hlog
    apply (le_div_iff₀ hnpos).2
    nlinarith
  exact hinvLog.trans hlogRate

/-- Grimmett's correlation length `ξ(p)=φ(p)⁻¹`, represented in `ℝ≥0∞` so that a zero decay
rate has infinite correlation length rather than the junk value zero. -/
noncomputable def correlationLength (d : ℕ) (p : I) : ℝ≥0∞ :=
  (ENNReal.ofReal (boxRadiusDecayRate d p))⁻¹

/-- The correlation length is continuous throughout the positive subcritical interval. -/
theorem correlationLength_continuousOn_subcritical (d : ℕ) (hd : 2 ≤ d) :
    ContinuousOn (correlationLength d)
      {p : I | 0 < (p : ℝ) ∧ (p : ℝ) < cubicCriticalProbability d} := by
  let S : Set I := {p : I | 0 < (p : ℝ) ∧ (p : ℝ) < cubicCriticalProbability d}
  have hrate : ContinuousOn (boxRadiusDecayRate d) S :=
    (boxRadiusDecayRate_continuousOn d (by omega)).mono fun _ hp ↦ hp.1
  have hrateNe : ∀ p ∈ S, boxRadiusDecayRate d p ≠ 0 := by
    intro p hp
    exact ne_of_gt (boxRadiusDecayRate_pos_of_lt_critical d hd p hp.1 hp.2)
  have hinv : ContinuousOn (fun p : I ↦ (boxRadiusDecayRate d p)⁻¹) S :=
    hrate.inv₀ hrateNe
  have hofReal : ContinuousOn
      (fun p : I ↦ ENNReal.ofReal ((boxRadiusDecayRate d p)⁻¹)) S :=
    ENNReal.continuous_ofReal.comp_continuousOn hinv
  refine hofReal.congr ?_
  intro p hp
  change (ENNReal.ofReal (boxRadiusDecayRate d p))⁻¹ =
    ENNReal.ofReal ((boxRadiusDecayRate d p)⁻¹)
  exact (ENNReal.ofReal_inv_of_pos
    (boxRadiusDecayRate_pos_of_lt_critical d hd p hp.1 hp.2)).symm

/-- The strict decrease of the inverse correlation rate becomes strict increase of correlation
length on `(0,p_c)`. -/
theorem correlationLength_strictMonoOn_subcritical (d : ℕ) (hd : 2 ≤ d) :
    StrictMonoOn (correlationLength d)
      {p : I | 0 < (p : ℝ) ∧ (p : ℝ) < cubicCriticalProbability d} := by
  let S : Set I := {p : I | 0 < (p : ℝ) ∧ (p : ℝ) < cubicCriticalProbability d}
  intro a ha b hb hab
  have hpa := boxRadiusDecayRate_pos_of_lt_critical d hd a ha.1 ha.2
  have hpb := boxRadiusDecayRate_pos_of_lt_critical d hd b hb.1 hb.2
  have hrate := boxRadiusDecayRate_strictAntiOn_subcritical d hd ha hb hab
  have hinv : (boxRadiusDecayRate d a)⁻¹ < (boxRadiusDecayRate d b)⁻¹ :=
    (inv_lt_inv₀ hpa hpb).2 hrate
  rw [correlationLength, correlationLength,
    ← ENNReal.ofReal_inv_of_pos hpa, ← ENNReal.ofReal_inv_of_pos hpb]
  exact (ENNReal.ofReal_lt_ofReal_iff (inv_pos.mpr hpb)).2 hinv

/-- Real-density endpoint extension used for the source limit `xi(p) -> 0` as `p ↓ 0`. -/
noncomputable def clampedCorrelationLength (d : ℕ) (x : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal (clampedBoxRadiusDecayRate d x))⁻¹

/-- Grimmett (6.55): the correlation length tends to zero at zero density. -/
theorem correlationLength_tendsto_zero_at_zero (d : ℕ) (hd : 0 < d) :
    Tendsto (clampedCorrelationLength d) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hrate := boxRadiusDecayRate_tendsto_top_at_zero d hd
  have hofReal : Tendsto (fun x : ℝ ↦ ENNReal.ofReal (clampedBoxRadiusDecayRate d x))
      (𝓝[>] (0 : ℝ)) (𝓝 ⊤) := ENNReal.tendsto_ofReal_atTop.comp hrate
  simpa [clampedCorrelationLength] using continuous_inv.continuousAt.tendsto.comp hofReal

/-- Proposition 6.49: below criticality, the correlation length is at most susceptibility. -/
theorem correlationLength_le_susceptibility
    {d : ℕ} (hd : 2 ≤ d) {p : I} (hp : 0 < (p : ℝ))
    (hpc : (p : ℝ) < cubicCriticalProbability d) :
    correlationLength d p ≤ susceptibility d p := by
  have hchi : susceptibility d p < ⊤ :=
    susceptibility_lt_top_of_lt_critical d hd p hpc
  have hchi1 : 1 < (susceptibility d p).toReal :=
    one_lt_susceptibility_toReal_of_pos (by omega) hp hchi
  have hphi : 0 < boxRadiusDecayRate d p :=
    boxRadiusDecayRate_pos_of_lt_critical d hd p hp hpc
  have hinv : ((susceptibility d p).toReal)⁻¹ ≤ boxRadiusDecayRate d p :=
    susceptibility_toReal_inv_le_boxRadiusDecayRate (by omega) hp hchi
  have hcorrTop : correlationLength d p ≠ ⊤ := by
    intro h
    rw [correlationLength, ENNReal.inv_eq_top, ENNReal.ofReal_eq_zero] at h
    exact (not_le_of_gt hphi) h
  apply (ENNReal.toReal_le_toReal hcorrTop (ne_of_lt hchi)).mp
  rw [correlationLength, ENNReal.toReal_inv, ENNReal.toReal_ofReal hphi.le]
  exact (inv_le_comm₀ hphi (zero_lt_one.trans hchi1)).2 hinv

@[simp]
theorem correlationLength_critical_eq_top (d : ℕ) (hd : 2 ≤ d) :
    correlationLength d (cubicCriticalProbabilityUnit d hd) = ⊤ := by
  simp [correlationLength, boxRadiusDecayRate_critical_eq_zero d hd]

/-- As the density approaches `p_c` from below, the correlation length diverges. -/
theorem correlationLength_tendsto_top_at_critical (d : ℕ) (hd : 2 ≤ d) :
    Tendsto (correlationLength d)
      (𝓝[<] (cubicCriticalProbabilityUnit d hd)) (𝓝 ⊤) := by
  let pc : I := cubicCriticalProbabilityUnit d hd
  have hpc0 : 0 < (pc : ℝ) := by
    simpa [pc] using (cubicCriticalProbability_pos_lt_one hd).1
  have hopen : IsOpen {p : I | 0 < (p : ℝ)} :=
    isOpen_lt continuous_const continuous_subtype_val
  have hcontAt : ContinuousAt (boxRadiusDecayRate d) pc :=
    ((boxRadiusDecayRate_continuousOn d (by omega)) pc hpc0).continuousAt
      (hopen.mem_nhds hpc0)
  have hrateZero : Tendsto (boxRadiusDecayRate d) (𝓝[<] pc) (𝓝 0) := by
    have h : Tendsto (boxRadiusDecayRate d) (𝓝[<] pc)
        (𝓝 (boxRadiusDecayRate d pc)) :=
      hcontAt.tendsto.mono_left inf_le_left
    simpa [pc, boxRadiusDecayRate_critical_eq_zero d hd] using h
  have hpEventually : ∀ᶠ p : I in 𝓝[<] pc, 0 < (p : ℝ) :=
    Filter.Eventually.filter_mono inf_le_left (hopen.mem_nhds hpc0)
  have hratePos : ∀ᶠ p : I in 𝓝[<] pc, 0 < boxRadiusDecayRate d p := by
    filter_upwards [self_mem_nhdsWithin, hpEventually] with p hppc hp0
    exact boxRadiusDecayRate_pos_of_lt_critical d hd p hp0 (by
      simpa [pc] using (show (p : ℝ) < (pc : ℝ) by exact_mod_cast hppc))
  have hrateGT : Tendsto (boxRadiusDecayRate d) (𝓝[<] pc) (𝓝[>] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hrateZero, hratePos⟩
  have hinv : Tendsto (fun p : I ↦ (boxRadiusDecayRate d p)⁻¹)
      (𝓝[<] pc) atTop := by
    simpa [Function.comp_def] using (tendsto_inv_nhdsGT_zero.comp hrateGT)
  have hofReal : Tendsto (fun p : I ↦ ENNReal.ofReal (boxRadiusDecayRate d p)⁻¹)
      (𝓝[<] pc) (𝓝 ⊤) := ENNReal.tendsto_ofReal_atTop.comp hinv
  have hcorr : Tendsto (correlationLength d) (𝓝[<] pc) (𝓝 ⊤) := by
    apply hofReal.congr'
    filter_upwards [hratePos] with p hp
    rw [correlationLength, ENNReal.ofReal_inv_of_pos hp]
  simpa [pc] using hcorr

/-- Final consequence of Proposition 6.49: susceptibility diverges on approaching the critical
density from below. -/
theorem susceptibility_tendsto_top_at_critical (d : ℕ) (hd : 2 ≤ d) :
    Tendsto (susceptibility d)
      (𝓝[<] (cubicCriticalProbabilityUnit d hd)) (𝓝 ⊤) := by
  let pc : I := cubicCriticalProbabilityUnit d hd
  have hpc0 : 0 < (pc : ℝ) := by
    simpa [pc] using (cubicCriticalProbability_pos_lt_one hd).1
  have hopen : IsOpen {p : I | 0 < (p : ℝ)} :=
    isOpen_lt continuous_const continuous_subtype_val
  have hpEventually : ∀ᶠ p : I in 𝓝[<] pc, 0 < (p : ℝ) :=
    Filter.Eventually.filter_mono inf_le_left (hopen.mem_nhds hpc0)
  have hle : ∀ᶠ p : I in 𝓝[<] pc,
      correlationLength d p ≤ susceptibility d p := by
    filter_upwards [self_mem_nhdsWithin, hpEventually] with p hppc hp0
    exact correlationLength_le_susceptibility hd hp0 (by
      simpa [pc] using (show (p : ℝ) < (pc : ℝ) by exact_mod_cast hppc))
  have hcorr : Tendsto (correlationLength d) (𝓝[<] pc) (𝓝 ⊤) := by
    simpa [pc] using correlationLength_tendsto_top_at_critical d hd
  have hsusc := tendsto_nhds_top_mono hcorr hle
  simpa [pc] using hsusc

#print axioms twoPointConnectivity_axis_logRate_tendsto
#print axioms twoPointConnectivity_axis_twoSided_decay
#print axioms twoPointConnectivity_twoSided_decay
#print axioms twoPointConnectivity_le_one_sub_susceptibility_inv_pow
#print axioms correlationLength_le_susceptibility
#print axioms correlationLength_continuousOn_subcritical
#print axioms correlationLength_strictMonoOn_subcritical
#print axioms correlationLength_tendsto_zero_at_zero
#print axioms susceptibility_tendsto_top_at_critical

end Percolation
