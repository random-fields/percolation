import Percolation.Extensions.ContinuumPointProcess

/-!
# The Boolean cluster at the spatial origin

This file implements Grimmett's `W = W(0)`: the set of Poisson centres whose radius-one
spheres lie in the sphere cluster containing the spatial origin.  Its extended cardinality is
used for the mean cluster size in Theorem 12.35.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory Set SimpleGraph
open scoped ENNReal MeasureTheory NNReal

/-- The centres in the Boolean cluster containing the spatial origin. -/
def continuumOriginCluster {d : ℕ}
    (Xi : ContinuumPoissonConfiguration d) : Set (Cubic d × ℕ) :=
  {b | ∃ a : Cubic d × ℕ,
    continuumPoissonPointCoversOrigin Xi a ∧
      (continuumPoissonAmbientGraph Xi).Reachable a b}

theorem measurableSet_mem_continuumOriginCluster {d : ℕ}
    (b : Cubic d × ℕ) :
    MeasurableSet {Xi : ContinuumPoissonConfiguration d |
      b ∈ continuumOriginCluster Xi} := by
  rw [show {Xi : ContinuumPoissonConfiguration d |
        b ∈ continuumOriginCluster Xi} =
      ⋃ a : Cubic d × ℕ,
        {Xi | continuumPoissonPointCoversOrigin Xi a} ∩
          continuumPoissonConnectionEvent a b by
    ext Xi
    simp [continuumOriginCluster, continuumPoissonConnectionEvent]]
  exact MeasurableSet.iUnion fun a ↦
    (measurableSet_continuumPoissonPointCoversOrigin a).inter
      (measurableSet_continuumPoissonConnectionEvent a b)

/-- Extended number of spheres in `W(0)`.  Infinite clusters have value `⊤`. -/
noncomputable def continuumOriginClusterSize {d : ℕ}
    (Xi : ContinuumPoissonConfiguration d) : ℝ≥0∞ :=
  by
    classical
    exact ∑' b : Cubic d × ℕ, if b ∈ continuumOriginCluster Xi then 1 else 0

theorem continuumOriginClusterSize_eq_encard {d : ℕ}
    (Xi : ContinuumPoissonConfiguration d) :
    continuumOriginClusterSize Xi = (continuumOriginCluster Xi).encard := by
  classical
  rw [← ENNReal.tsum_set_one]
  change (∑' b : Cubic d × ℕ,
    (continuumOriginCluster Xi).indicator (fun _ ↦ (1 : ℝ≥0∞)) b) =
      ∑' _ : continuumOriginCluster Xi, (1 : ℝ≥0∞)
  exact (tsum_subtype (continuumOriginCluster Xi) fun _ ↦ (1 : ℝ≥0∞)).symm

theorem measurable_continuumOriginClusterSize (d : ℕ) :
    Measurable (continuumOriginClusterSize (d := d)) := by
  classical
  unfold continuumOriginClusterSize
  apply Measurable.tsum
  intro b
  rw [show (fun Xi : ContinuumPoissonConfiguration d ↦
      if b ∈ continuumOriginCluster Xi then (1 : ℝ≥0∞) else 0) =
      {Xi | b ∈ continuumOriginCluster Xi}.indicator (fun _ ↦ 1) by
    funext Xi
    rfl]
  exact measurable_const.indicator (measurableSet_mem_continuumOriginCluster b)

private theorem continuumPoissonPointCoversOrigin_adj
    {d : ℕ} {Xi : ContinuumPoissonConfiguration d} {a b : Cubic d × ℕ}
    (ha : continuumPoissonPointCoversOrigin Xi a)
    (hb : continuumPoissonPointCoversOrigin Xi b) (hab : a ≠ b) :
    (continuumPoissonAmbientGraph Xi).Adj a b := by
  rw [continuumPoissonAmbientGraph_adj]
  refine ⟨hab, ha.1, hb.1, ?_⟩
  calc
    coordinateEuclideanDist (continuumPoissonPoint Xi a)
        (continuumPoissonPoint Xi b) ≤
        coordinateEuclideanDist (continuumPoissonPoint Xi a)
          (continuumSpatialOrigin d) +
        coordinateEuclideanDist (continuumSpatialOrigin d)
          (continuumPoissonPoint Xi b) :=
      coordinateEuclideanDist_triangle _ _ _
    _ ≤ 1 + 1 := by
      exact add_le_add ha.2
        ((coordinateEuclideanDist_comm _ _).le.trans hb.2)
    _ = 2 := by norm_num

/-- The origin cluster is infinite exactly on the rooted percolation event (12.34). -/
theorem continuumOriginCluster_infinite_iff {d : ℕ}
    (Xi : ContinuumPoissonConfiguration d) :
    (continuumOriginCluster Xi).Infinite ↔
      Xi ∈ continuumOriginPercolatesEvent d := by
  constructor
  · intro hinfinite
    obtain ⟨b, hb⟩ := hinfinite.nonempty
    obtain ⟨a, haCover, hab⟩ := hb
    refine ⟨a, haCover, haCover.1, hinfinite.mono ?_⟩
    intro c hc
    obtain ⟨a', ha'Cover, ha'c⟩ := hc
    by_cases haa' : a = a'
    · simpa [haa'] using ha'c
    · have haa'Reach : (continuumPoissonAmbientGraph Xi).Reachable a a' :=
        ⟨SimpleGraph.Walk.cons
          (continuumPoissonPointCoversOrigin_adj haCover ha'Cover haa')
          SimpleGraph.Walk.nil⟩
      exact haa'Reach.trans ha'c
  · rintro ⟨a, haCover, _haActive, haInfinite⟩
    exact haInfinite.mono fun b hab ↦ ⟨a, haCover, hab⟩

theorem continuumOriginClusterSize_eq_top_iff {d : ℕ}
    (Xi : ContinuumPoissonConfiguration d) :
    continuumOriginClusterSize Xi = ⊤ ↔
      Xi ∈ continuumOriginPercolatesEvent d := by
  rw [continuumOriginClusterSize_eq_encard, ENat.toENNReal_eq_top,
    Set.encard_eq_top_iff, continuumOriginCluster_infinite_iff]

/-- Mean number of spheres in the Boolean cluster `W(0)`. -/
noncomputable def continuumMeanClusterSize (d : ℕ) (intensity : ℝ≥0) : ℝ≥0∞ :=
  ∫⁻ Xi, continuumOriginClusterSize Xi ∂continuumPoissonMeasure d intensity

theorem poissonMeasure_zero_eq_dirac :
    poissonMeasure 0 = Measure.dirac 0 := by
  rw [Measure.ext_iff_singleton]
  intro n
  rw [poissonMeasure_singleton]
  cases n <;> simp

theorem poissonCubeMeasure_zero (d n : ℕ) :
    poissonCubeMeasure d 0 n = Measure.dirac 0 := by
  unfold poissonCubeMeasure continuumCubeRate
  simp only [zero_div, poissonMeasure_zero_eq_dirac, Measure.infinitePi_dirac]
  congr 1

theorem continuumOriginCluster_eq_empty_of_cubeCounts_eq_zero
    {d : ℕ} {Xi : ContinuumPoissonConfiguration d}
    (hzero : continuumPoissonCubeCounts Xi = 0) :
    continuumOriginCluster Xi = ∅ := by
  ext b
  simp only [continuumOriginCluster, Set.mem_setOf_eq, Set.mem_empty_iff_false,
    iff_false]
  rintro ⟨a, haCover, _hab⟩
  have haCount : (Xi a.1).1 = 0 := by
    simpa [continuumPoissonCubeCounts] using congrFun hzero a.1
  have haActive : a.2 < (Xi a.1).1 := haCover.1
  rw [haCount] at haActive
  omega

/-- With zero intensity there are almost surely no spheres, so the mean cluster size is zero. -/
@[simp]
theorem continuumMeanClusterSize_zero (d : ℕ) :
    continuumMeanClusterSize d 0 = 0 := by
  let mu := continuumPoissonMeasure d 0
  have hmap := continuumPoissonMeasure_map_cubeCounts d 0
  rw [poissonCubeMeasure_zero] at hmap
  have hmass := congrArg (fun nu : Measure (PoissonCubeConfiguration d) ↦
    nu ({0} : Set (PoissonCubeConfiguration d))) hmap
  change (Measure.map continuumPoissonCubeCounts
      (continuumPoissonMeasure d 0)) {0} =
    (Measure.dirac (0 : PoissonCubeConfiguration d)) {0} at hmass
  rw [Measure.map_apply measurable_continuumPoissonCubeCounts
      (measurableSet_singleton (0 : PoissonCubeConfiguration d)),
    Measure.dirac_apply' _ (measurableSet_singleton
      (0 : PoissonCubeConfiguration d))] at hmass
  have haeCounts : ∀ᵐ Xi : ContinuumPoissonConfiguration d ∂mu,
      continuumPoissonCubeCounts Xi = 0 := by
    apply (ae_iff_measure_eq ((measurable_continuumPoissonCubeCounts
      (measurableSet_singleton
        (0 : PoissonCubeConfiguration d))).nullMeasurableSet)).2
    rw [show mu Set.univ = 1 by simp [mu]]
    simpa [mu] using hmass
  unfold continuumMeanClusterSize
  apply le_antisymm
  · rw [show (0 : ℝ≥0∞) = ∫⁻ _Xi : ContinuumPoissonConfiguration d, 0 ∂mu by simp]
    apply lintegral_mono_ae
    filter_upwards [haeCounts] with Xi hXi
    rw [continuumOriginClusterSize_eq_encard,
      continuumOriginCluster_eq_empty_of_cubeCounts_eq_zero hXi]
    simp
  · exact bot_le

/-- Finite mean cluster size rules out rooted continuum percolation. -/
theorem continuumTheta_eq_zero_of_meanClusterSize_lt_top
    {d : ℕ} {intensity : ℝ≥0}
    (hfinite : continuumMeanClusterSize d intensity < ⊤) :
    continuumTheta d intensity = 0 := by
  let mu := continuumPoissonMeasure d intensity
  have hae : ∀ᵐ Xi : ContinuumPoissonConfiguration d ∂mu,
      continuumOriginClusterSize Xi < ⊤ :=
    ae_lt_top (measurable_continuumOriginClusterSize d) hfinite.ne
  have hzero : mu {Xi | continuumOriginClusterSize Xi = ⊤} = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hae] with Xi hXi
    exact ne_of_lt hXi
  unfold continuumTheta
  rw [show continuumOriginPercolatesEvent d =
      {Xi | continuumOriginClusterSize Xi = ⊤} by
    ext Xi
    exact (continuumOriginClusterSize_eq_top_iff Xi).symm]
  simp [Measure.real, mu, hzero]

end Percolation
