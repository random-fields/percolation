import Percolation.Extensions.ContinuumCentralPorts

/-!
# The iid law of central ports

This file computes the probability that a marked Poisson cube contains a central representative.
It then identifies the full central-cube field with homogeneous iid site percolation.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory Set SimpleGraph
open scoped ENNReal NNReal Nat unitInterval

/-- Lebesgue mass of the one-sided central port for one marked point. -/
noncomputable def continuumCentralMarkMass (d : ℕ) : ℝ≥0 :=
  ⟨(continuumCentralPortRadius d) ^ d,
    pow_nonneg (continuumCentralPortRadius_pos d).le d⟩

@[simp]
theorem coe_continuumCentralMarkMass (d : ℕ) :
    (continuumCentralMarkMass d : ℝ) = (continuumCentralPortRadius d) ^ d := rfl

theorem continuumCentralMarkMass_pos (d : ℕ) :
    0 < continuumCentralMarkMass d := by
  rw [← NNReal.coe_pos]
  simp only [coe_continuumCentralMarkMass]
  exact pow_pos (continuumCentralPortRadius_pos d) d

theorem continuumCentralMarkMass_le_one (d : ℕ) :
    continuumCentralMarkMass d ≤ 1 := by
  rw [← NNReal.coe_le_coe]
  simp only [coe_continuumCentralMarkMass, NNReal.coe_one]
  apply pow_le_one₀ (continuumCentralPortRadius_pos d).le
  unfold continuumCentralPortRadius
  have hden : (0 : ℝ) < 8 * ((d : ℝ) + 1) := by positivity
  rw [div_le_one hden]
  nlinarith [show (0 : ℝ) ≤ d by positivity]

/-- The central coordinate rectangle has exactly the expected product volume. -/
theorem continuumUnitMarkMeasure_central (d : ℕ) :
    continuumUnitMarkMeasure d
        {a : ContinuumUnitMark d | continuumMarkIsCentral d a} =
      continuumCentralMarkMass d := by
  rw [show {a : ContinuumUnitMark d | continuumMarkIsCentral d a} =
      Set.pi ((Finset.univ : Finset (Fin d)) : Set (Fin d))
        (fun _ : Fin d ↦ Set.Icc continuumCentralPortLower
          (continuumCentralPortUpper d)) by
    ext a
    simp only [Set.mem_setOf_eq, continuumMarkIsCentral, Set.mem_pi,
      Finset.mem_coe, Finset.mem_univ, forall_const]]
  unfold continuumUnitMarkMeasure
  rw [Measure.infinitePi_pi]
  · simp [continuumCentralMarkMass, unitInterval.volume_Icc,
      continuumCentralPortUpper, continuumCentralPortLower]
    rw [← ENNReal.ofReal_pow (continuumCentralPortRadius_pos d).le]
    rw [ENNReal.ofReal_eq_coe_nnreal
      (pow_nonneg (continuumCentralPortRadius_pos d).le d)]
    congr
  · intro i _hi
    exact measurableSet_Icc

/-- No central mark occurs among the first `n` entries of a mark stream. -/
def continuumNoCentralMarksBefore (d n : ℕ) : Set (ContinuumMarkStream d) :=
  {marks | ∀ k < n, ¬continuumMarkIsCentral d (marks k)}

theorem measurableSet_continuumNoCentralMarksBefore (d n : ℕ) :
    MeasurableSet (continuumNoCentralMarksBefore d n) := by
  rw [show continuumNoCentralMarksBefore d n =
      ⋂ k : Fin n,
        {marks | ¬continuumMarkIsCentral d (marks k)} by
    ext marks
    simp only [continuumNoCentralMarksBefore, Set.mem_setOf_eq, Set.mem_iInter]
    change (∀ k < n, ¬continuumMarkIsCentral d (marks k)) ↔
      ∀ k : Fin n, ¬continuumMarkIsCentral d (marks k.1)
    constructor
    · intro h k
      exact h k.1 k.2
    · intro h k hk
      exact h ⟨k, hk⟩]
  exact MeasurableSet.iInter fun k : Fin n ↦
    (measurableSet_continuumMarkIsCentral d).compl.preimage
      (measurable_pi_apply k.1)

/-- The iid stream misses the central port in its first `n` trials with probability
`(1-q)^n`. -/
theorem continuumMarkStreamMeasure_noCentralBefore (d n : ℕ) :
    continuumMarkStreamMeasure d (continuumNoCentralMarksBefore d n) =
      (1 - (continuumCentralMarkMass d : ℝ≥0∞)) ^ n := by
  rw [show continuumNoCentralMarksBefore d n =
      Set.pi ((Finset.range n : Finset ℕ) : Set ℕ)
        (fun _ : ℕ ↦
          {a : ContinuumUnitMark d | continuumMarkIsCentral d a}ᶜ) by
    ext marks
    simp [continuumNoCentralMarksBefore]]
  unfold continuumMarkStreamMeasure
  rw [Measure.infinitePi_pi]
  · simp only [Finset.prod_const, Finset.card_range]
    congr 1
    rw [measure_compl (measurableSet_continuumMarkIsCentral d) (measure_ne_top _ _),
      measure_univ, continuumUnitMarkMeasure_central]
  · intro k _hk
    exact (measurableSet_continuumMarkIsCentral d).compl

theorem continuumMarkStreamMeasure_real_noCentralBefore (d n : ℕ) :
    (continuumMarkStreamMeasure d).real (continuumNoCentralMarksBefore d n) =
      (1 - (continuumCentralMarkMass d : ℝ)) ^ n := by
  have h := congrArg ENNReal.toReal
    (continuumMarkStreamMeasure_noCentralBefore d n)
  have hsub : 1 - (continuumCentralMarkMass d : ℝ≥0∞) =
      ((1 - continuumCentralMarkMass d : ℝ≥0) : ℝ≥0∞) := by
    rw [ENNReal.coe_sub]
    rfl
  rw [hsub] at h
  have h' :
      (continuumMarkStreamMeasure d).real (continuumNoCentralMarksBefore d n) =
        ((1 - continuumCentralMarkMass d : ℝ≥0) : ℝ) ^ n := by
    simpa only [Measure.real, ENNReal.toReal_pow, ENNReal.toReal,
      ENNReal.toNNReal_coe, NNReal.coe_pow] using h
  simpa only [NNReal.coe_sub (continuumCentralMarkMass_le_one d)] using h'

/-- The Poisson probability-generating function at `1-q`. -/
theorem integral_pow_one_sub_poissonMeasure (intensity : ℝ≥0) (q : ℝ) :
    ∫ n : ℕ, (1 - q) ^ n ∂poissonMeasure intensity =
      Real.exp (-((intensity : ℝ) * q)) := by
  rw [integral_poissonMeasure]
  simp only [smul_eq_mul]
  calc
    (∑' n : ℕ, (Real.exp (-(intensity : ℝ)) * (intensity : ℝ) ^ n /
        (n)!) * (1 - q) ^ n) =
        Real.exp (-(intensity : ℝ)) *
          ∑' n : ℕ, (((intensity : ℝ) * (1 - q)) ^ n / (n)!) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro n
      rw [mul_pow]
      ring
    _ = Real.exp (-(intensity : ℝ)) *
        Real.exp ((intensity : ℝ) * (1 - q)) := by
      rw [(NormedSpace.expSeries_div_hasSum_exp
        ((intensity : ℝ) * (1 - q))).tsum_eq, Real.exp_eq_exp_ℝ]
    _ = Real.exp (-((intensity : ℝ) * q)) := by
      rw [← Real.exp_add]
      congr 1
      ring

theorem continuumCubeHasCentralPoint_compl_section (d n : ℕ) :
    Prod.mk n ⁻¹' (continuumCubeHasCentralPoint d)ᶜ =
      continuumNoCentralMarksBefore d n := by
  ext marks
  simp [continuumCubeHasCentralPoint, continuumNoCentralMarksBefore]

/-- Exact failure probability for one marked Poisson cube. -/
theorem continuumCubeSampleMeasure_real_noCentralPoint
    (d : ℕ) (intensity : ℝ≥0) :
    (continuumCubeSampleMeasure d intensity).real
        (continuumCubeHasCentralPoint d)ᶜ =
      Real.exp (-((intensity : ℝ) * (continuumCentralMarkMass d : ℝ))) := by
  let A := (continuumCubeHasCentralPoint d)ᶜ
  have hA : MeasurableSet A := (measurableSet_continuumCubeHasCentralPoint d).compl
  calc
    (continuumCubeSampleMeasure d intensity).real A =
        (∫⁻ n : ℕ, continuumMarkStreamMeasure d (Prod.mk n ⁻¹' A)
          ∂poissonMeasure intensity).toReal := by
      rw [Measure.real, continuumCubeSampleMeasure, Measure.prod_apply hA]
    _ = ∫ n : ℕ,
        (continuumMarkStreamMeasure d (Prod.mk n ⁻¹' A)).toReal
          ∂poissonMeasure intensity := by
      symm
      apply integral_toReal
      · exact (measurable_measure_prodMk_left hA).aemeasurable
      · exact Filter.Eventually.of_forall fun n ↦ measure_lt_top _ _
    _ = ∫ n : ℕ, (1 - (continuumCentralMarkMass d : ℝ)) ^ n
          ∂poissonMeasure intensity := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun n ↦ by
        change (continuumMarkStreamMeasure d (Prod.mk n ⁻¹' A)).toReal = _
        rw [show Prod.mk n ⁻¹' A = continuumNoCentralMarksBefore d n by
          simpa [A] using continuumCubeHasCentralPoint_compl_section d n]
        exact continuumMarkStreamMeasure_real_noCentralBefore d n
    _ = Real.exp (-((intensity : ℝ) * (continuumCentralMarkMass d : ℝ))) :=
      integral_pow_one_sub_poissonMeasure intensity _

/-- Iid density of cubes containing a central active mark. -/
noncomputable def continuumCentralCubeDensity (d : ℕ) (intensity : ℝ≥0) : I :=
  ⟨1 - Real.exp (-((intensity : ℝ) * (continuumCentralMarkMass d : ℝ))), by
    constructor
    · have hnonneg : 0 ≤ (intensity : ℝ) * (continuumCentralMarkMass d : ℝ) := by
        positivity
      linarith [Real.exp_le_one_iff.mpr (neg_nonpos.mpr hnonneg)]
    · linarith [Real.exp_nonneg
        (-((intensity : ℝ) * (continuumCentralMarkMass d : ℝ)))]⟩

@[simp]
theorem coe_continuumCentralCubeDensity (d : ℕ) (intensity : ℝ≥0) :
    (continuumCentralCubeDensity d intensity : ℝ) =
      1 - Real.exp (-((intensity : ℝ) * (continuumCentralMarkMass d : ℝ))) := rfl

/-- Exact one-cube success probability. -/
theorem continuumCubeSampleMeasure_real_hasCentralPoint
    (d : ℕ) (intensity : ℝ≥0) :
    (continuumCubeSampleMeasure d intensity).real
        (continuumCubeHasCentralPoint d) =
      continuumCentralCubeDensity d intensity := by
  have hcompl := measureReal_compl
    (μ := continuumCubeSampleMeasure d intensity)
    (measurableSet_continuumCubeHasCentralPoint d)
  rw [probReal_univ, continuumCubeSampleMeasure_real_noCentralPoint] at hcompl
  change (continuumCubeSampleMeasure d intensity).real
      (continuumCubeHasCentralPoint d) =
    1 - Real.exp (-((intensity : ℝ) * (continuumCentralMarkMass d : ℝ)))
  linarith

/-- Thresholding one marked cube by the central-port event gives its exact Bernoulli law. -/
theorem continuumCubeSampleMeasure_map_hasCentralPoint
    (d : ℕ) (intensity : ℝ≥0) :
    (continuumCubeSampleMeasure d intensity).map
        (fun sample ↦ sample ∈ continuumCubeHasCentralPoint d) =
      bernoulliPropMeasure (continuumCentralCubeDensity d intensity) := by
  rw [Measure.ext_iff_singleton]
  intro b
  rw [Measure.map_apply (measurableSet_continuumCubeHasCentralPoint d).mem
    (measurableSet_singleton b)]
  by_cases hb : b
  · have hb' : b = True := propext (iff_true_intro hb)
    subst b
    have hpre :
        (fun sample : ContinuumCubeSample d ↦
          sample ∈ continuumCubeHasCentralPoint d) ⁻¹' ({True} : Set Prop) =
          continuumCubeHasCentralPoint d := by
      ext sample
      simp
    rw [hpre, ← ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)]
    change (continuumCubeSampleMeasure d intensity).real
        (continuumCubeHasCentralPoint d) =
      (bernoulliPropMeasure (continuumCentralCubeDensity d intensity)).real {True}
    rw [continuumCubeSampleMeasure_real_hasCentralPoint, bernoulliPropMeasure]
    simp [Measure.real]
  · have hb' : b = False := propext (iff_false_intro hb)
    subst b
    have hpre :
        (fun sample : ContinuumCubeSample d ↦
          sample ∈ continuumCubeHasCentralPoint d) ⁻¹' ({False} : Set Prop) =
          (continuumCubeHasCentralPoint d)ᶜ := by
      ext sample
      simp
    rw [hpre, ← ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)]
    change (continuumCubeSampleMeasure d intensity).real
        (continuumCubeHasCentralPoint d)ᶜ =
      (bernoulliPropMeasure (continuumCentralCubeDensity d intensity)).real {False}
    rw [continuumCubeSampleMeasure_real_noCentralPoint, bernoulliPropMeasure]
    simp [Measure.real]

/-- The full central-cube process is homogeneous iid site percolation. -/
theorem continuumPoissonMeasure_map_centralCubes
    (d : ℕ) (intensity : ℝ≥0) :
    (continuumPoissonMeasure d intensity).map continuumCentralCubes =
      setBer((Set.univ : Set (Cubic d)),
        continuumCentralCubeDensity d intensity) := by
  have hcomp :
      (continuumCentralCubes :
        ContinuumPoissonConfiguration d → Set (Cubic d)) =
        (fun P : Cubic d → Prop ↦ {x | P x}) ∘
          (fun Xi : ContinuumPoissonConfiguration d ↦
            fun x ↦ Xi x ∈ continuumCubeHasCentralPoint d) := rfl
  have hcoord : Measurable
      (fun Xi : ContinuumPoissonConfiguration d ↦
        fun x ↦ Xi x ∈ continuumCubeHasCentralPoint d) :=
    measurable_pi_lambda _ fun x ↦
      ((measurableSet_continuumCubeHasCentralPoint d).preimage
        (measurable_pi_apply x)).mem
  rw [hcomp, ← Measure.map_map (by fun_prop) hcoord,
    continuumPoissonMeasure]
  have hpi :
      (Measure.infinitePi fun _ : Cubic d ↦
        continuumCubeSampleMeasure d intensity).map
          (fun Xi x ↦ Xi x ∈ continuumCubeHasCentralPoint d) =
        Measure.infinitePi fun _ : Cubic d ↦
          (continuumCubeSampleMeasure d intensity).map
            (fun sample ↦ sample ∈ continuumCubeHasCentralPoint d) := by
    exact Measure.infinitePi_map_pi
      (μ := fun _ : Cubic d ↦ continuumCubeSampleMeasure d intensity)
      (f := fun _ : Cubic d ↦
        fun sample ↦ sample ∈ continuumCubeHasCentralPoint d)
      (fun _ ↦ (measurableSet_continuumCubeHasCentralPoint d).mem)
  rw [hpi, setBernoulli_eq_map]
  congrm Measure.map _ (Measure.infinitePi fun x ↦ ?_)
  exact continuumCubeSampleMeasure_map_hasCentralPoint d intensity

/-- The central-cube field has an infinite nearest-neighbor site cluster. -/
def continuumCentralCubesPercolateEvent (d : ℕ) :
    Set (ContinuumPoissonConfiguration d) :=
  {Xi | hasInfiniteSiteCluster (cubicGraph d) (continuumCentralCubes Xi)}

theorem measurableSet_continuumCentralCubesPercolateEvent (d : ℕ) :
    MeasurableSet (continuumCentralCubesPercolateEvent d) := by
  exact (measurableSet_hasInfiniteSiteCluster (cubicGraph d)).preimage
    measurable_continuumCentralCubes

/-- Percolation probability of the central-cube site field. -/
noncomputable def continuumCentralCubesTheta (d : ℕ) (intensity : ℝ≥0) : ℝ :=
  (continuumPoissonMeasure d intensity).real
    (continuumCentralCubesPercolateEvent d)

theorem continuumCentralCubesTheta_eq_siteTheta
    (d : ℕ) (intensity : ℝ≥0) :
    continuumCentralCubesTheta d intensity =
      siteTheta (cubicGraph d) (continuumCentralCubeDensity d intensity) := by
  unfold continuumCentralCubesTheta continuumCentralCubesPercolateEvent siteTheta
  have hmap := continuumPoissonMeasure_map_centralCubes d intensity
  have hcongr := congrArg (fun μ : Measure (Set (Cubic d)) ↦
      μ {eta | hasInfiniteSiteCluster (cubicGraph d) eta}) hmap
  change (Measure.map continuumCentralCubes (continuumPoissonMeasure d intensity))
      {eta | hasInfiniteSiteCluster (cubicGraph d) eta} = _ at hcongr
  rw [Measure.map_apply measurable_continuumCentralCubes
    (measurableSet_hasInfiniteSiteCluster (cubicGraph d))] at hcongr
  exact congrArg ENNReal.toReal hcongr

/-- The central-cube cluster of the origin is infinite. -/
def continuumCentralOriginPercolatesEvent (d : ℕ) :
    Set (ContinuumPoissonConfiguration d) :=
  {Xi | (siteOpenCluster (cubicGraph d) (continuumCentralCubes Xi)
    cubicOrigin).Infinite}

theorem measurableSet_continuumCentralOriginPercolatesEvent (d : ℕ) :
    MeasurableSet (continuumCentralOriginPercolatesEvent d) := by
  exact (measurableSet_rootedInfiniteSiteClusterEvent (cubicGraph d) cubicOrigin).preimage
    measurable_continuumCentralCubes

/-- Probability that the origin cube has an infinite central-port site cluster. -/
noncomputable def continuumCentralOriginTheta (d : ℕ) (intensity : ℝ≥0) : ℝ :=
  (continuumPoissonMeasure d intensity).real
    (continuumCentralOriginPercolatesEvent d)

theorem continuumCentralOriginTheta_eq_rootedSiteProbability
    (d : ℕ) (intensity : ℝ≥0) :
    continuumCentralOriginTheta d intensity =
      setBer((Set.univ : Set (Cubic d)), continuumCentralCubeDensity d intensity).real
        (rootedInfiniteSiteClusterEvent (cubicGraph d) cubicOrigin) := by
  unfold continuumCentralOriginTheta continuumCentralOriginPercolatesEvent
  rw [← continuumPoissonMeasure_map_centralCubes d intensity]
  rw [Measure.real, Measure.real]
  congr 1
  exact (Measure.map_apply measurable_continuumCentralCubes
    (measurableSet_rootedInfiniteSiteClusterEvent (cubicGraph d) cubicOrigin)).symm

/-- The rooted central-port comparison is source-faithful: it connects the spatial origin to
an infinite Boolean component. -/
theorem continuumCentralOriginTheta_le_continuumTheta
    (d : ℕ) (intensity : ℝ≥0) :
    continuumCentralOriginTheta d intensity ≤ continuumTheta d intensity := by
  unfold continuumCentralOriginTheta continuumTheta
    continuumCentralOriginPercolatesEvent
  exact measureReal_mono fun Xi hXi ↦
    continuumOriginPercolates_of_infiniteCentralOriginCluster hXi

/-- In dimensions at least two, a finite intensity percolates in the literal marked Boolean
model.  The proof is an explicit high-density iid central-port comparison. -/
theorem exists_continuumTheta_pos {d : ℕ} (hd : 2 ≤ d) :
    ∃ intensity : ℝ≥0, 0 < continuumTheta d intensity := by
  let c := siteCriticalProbability (cubicGraph d)
  have hc1 : c < 1 := cubicSiteCriticalProbability_lt_one hd
  have hgap : 0 < 1 - c := sub_pos.mpr hc1
  have hlim : Filter.Tendsto (fun k : ℕ ↦ Real.exp (-(k : ℝ)))
      Filter.atTop (nhds 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop
  have hev : ∀ᶠ k : ℕ in Filter.atTop, Real.exp (-(k : ℝ)) < 1 - c :=
    hlim.eventually (Iio_mem_nhds hgap)
  obtain ⟨k, hk⟩ := hev.exists
  let intensity : ℝ≥0 := (k : ℝ≥0) / continuumCentralMarkMass d
  have hG : (cubicGraph d).Connected := by
    refine ⟨fun x y ↦ ?_⟩
    exact ⟨(exists_cubicWalk_length_eq_l1Dist d x y).choose⟩
  refine ⟨intensity, ?_⟩
  have hroot := rootedInfiniteSiteCluster_probability_pos_of_connected_of_criticalProbability_lt
    hG (continuumCentralCubeDensity d intensity) ?_ cubicOrigin
  rw [← continuumCentralOriginTheta_eq_rootedSiteProbability] at hroot
  exact hroot.trans_le (continuumCentralOriginTheta_le_continuumTheta d intensity)
  have hm0 : (continuumCentralMarkMass d : ℝ) ≠ 0 :=
    ne_of_gt (show 0 < (continuumCentralMarkMass d : ℝ) by
      exact_mod_cast continuumCentralMarkMass_pos d)
  change siteCriticalProbability (cubicGraph d) <
    1 - Real.exp (-((intensity : ℝ) * (continuumCentralMarkMass d : ℝ)))
  have hproduct :
      (intensity : ℝ) * (continuumCentralMarkMass d : ℝ) = k := by
    change (((k : ℝ≥0) / continuumCentralMarkMass d : ℝ≥0) : ℝ) *
      (continuumCentralMarkMass d : ℝ) = (k : ℝ)
    rw [NNReal.coe_div]
    exact div_mul_cancel₀ _ hm0
  rw [hproduct]
  dsimp [c] at hk
  linarith

end Percolation
