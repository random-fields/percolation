import Percolation.Critical.SiteSusceptibility
import Percolation.Extensions.ContinuumCluster
import Percolation.Extensions.ContinuumMeanThreshold
import Percolation.Extensions.ContinuumSubcritical
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# A finite-mean low-density regime for the Boolean model

This file develops the quantitative comparison behind Grimmett (12.44) at unit mesh.  Every
sphere in `W(0)` is assigned injectively to its marked-point index in a cube belonging to a
site-open cluster started from one of finitely many cubes around the spatial origin.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory Set SimpleGraph
open scoped ENNReal NNReal unitInterval

/-- The origin cube together with all of its `L₁` neighbours. -/
noncomputable def continuumOriginNeighborCubes (d : ℕ) : Finset (Cubic d) :=
  insert cubicOrigin
    ((continuumApproximationGraph d 1).neighborFinset cubicOrigin)

@[simp]
theorem cubicOrigin_mem_continuumOriginNeighborCubes (d : ℕ) :
    cubicOrigin ∈ continuumOriginNeighborCubes d := by
  simp [continuumOriginNeighborCubes]

theorem continuumOriginNeighborCubes_card_le (d : ℕ) :
    (continuumOriginNeighborCubes d).card ≤ 1 + 9 ^ d := by
  calc
    (continuumOriginNeighborCubes d).card ≤
        1 + ((continuumApproximationGraph d 1).neighborFinset cubicOrigin).card :=
      by simpa [continuumOriginNeighborCubes, Nat.add_comm] using
        Finset.card_insert_le cubicOrigin
          ((continuumApproximationGraph d 1).neighborFinset cubicOrigin)
    _ = 1 + (continuumApproximationGraph d 1).degree cubicOrigin := by
      rw [SimpleGraph.card_neighborFinset_eq_degree]
    _ ≤ 1 + 9 ^ d := Nat.add_le_add_left
      (continuumApproximationGraph_one_degree_le d cubicOrigin) 1

theorem continuumSpatialOrigin_mem_originUnitCube (d : ℕ) :
    continuumSpatialOrigin d ∈ continuumElementaryCube 1 cubicOrigin := by
  simpa [continuumSpatialOrigin, cubicOrigin, continuumCubeCenter] using
    continuumCubeCenter_mem_elementaryCube (d := d) (n := 1) (by omega) cubicOrigin

/-- A sphere covering the spatial origin is based in the origin cube or an adjacent `L₁`
cube. -/
theorem continuumPoissonPointCoversOrigin_cube_mem
    {d : ℕ} {Xi : ContinuumPoissonConfiguration d} {a : Cubic d × ℕ}
    (ha : continuumPoissonPointCoversOrigin Xi a) :
    a.1 ∈ continuumOriginNeighborCubes d := by
  rw [continuumOriginNeighborCubes, Finset.mem_insert]
  by_cases ha0 : a.1 = cubicOrigin
  · exact Or.inl ha0
  · right
    rw [SimpleGraph.mem_neighborFinset]
    exact continuumApproximationGraph_adj.mpr
      ⟨Ne.symm ha0, continuumSpatialOrigin d,
        continuumSpatialOrigin_mem_originUnitCube d,
        continuumPoissonPoint Xi a, continuumPoissonPoint_mem_unitCube Xi a,
        by
          rw [coordinateEuclideanDist_comm]
          exact ha.2.trans (by norm_num)⟩

/-- The occupied-cube field of a marked realization. -/
def continuumPoissonOccupiedSites {d : ℕ}
    (Xi : ContinuumPoissonConfiguration d) : Set (Cubic d) :=
  continuumOccupiedSites (continuumPoissonCubeCounts Xi)

/-- A marked point in `W(0)` projects to a site-open connection from one of the finitely many
origin-neighbour cubes. -/
theorem continuumOriginCluster_projects_to_siteConnection
    {d : ℕ} {Xi : ContinuumPoissonConfiguration d}
    {b : Cubic d × ℕ} (hb : b ∈ continuumOriginCluster Xi) :
    ∃ a : Cubic d × ℕ,
      continuumPoissonPointCoversOrigin Xi a ∧
      continuumPoissonPointActive Xi b ∧
      continuumPoissonOccupiedSites Xi ∈
        siteConnectionEvent (continuumApproximationGraph d 1) a.1 b.1 := by
  obtain ⟨a, haCover, hab⟩ := hb
  obtain ⟨hbActive, hreach⟩ :=
    continuumPoissonWalk_projects_to_occupiedCubes
      (Classical.choice hab) haCover.1
  refine ⟨a, haCover, hbActive, ?_⟩
  let G := continuumApproximationGraph d 1
  let eta := continuumPoissonOccupiedSites Xi
  let projectToSiteOpen : G.induce eta →g siteOpenGraph G eta :=
    { toFun := Subtype.val
      map_rel' := by
        intro x y hxy
        exact siteOpenGraph_adj.mpr
          ⟨SimpleGraph.induce_adj.mp hxy, x.2, y.2⟩ }
  have hsiteReach := hreach.map projectToSiteOpen
  change b.1 ∈ siteOpenCluster G eta a.1
  rw [siteOpenCluster_eq_reachable]
  exact ⟨continuumPoissonPointActive_count_ne_zero haCover.1, hsiteReach⟩

/-- A counting witness consists of a permitted starting cube, a target cube, and an active
marked-point index in that target cube, together with the projected site connection. -/
abbrev ContinuumProjectedOriginWitness {d : ℕ}
    (Xi : ContinuumPoissonConfiguration d) :=
  {q : ↥(continuumOriginNeighborCubes d) ×
      (Σ x : Cubic d, Fin (continuumPoissonCubeCounts Xi x)) //
    continuumPoissonOccupiedSites Xi ∈
      siteConnectionEvent (continuumApproximationGraph d 1) q.1.1 q.2.1}

/-- Inject a sphere of `W(0)` into the projected counting witnesses. -/
noncomputable def continuumOriginClusterRoot
    {d : ℕ} {Xi : ContinuumPoissonConfiguration d}
    (b : continuumOriginCluster Xi) : Cubic d × ℕ :=
  Classical.choose (continuumOriginCluster_projects_to_siteConnection b.2)

theorem continuumOriginClusterRoot_spec
    {d : ℕ} {Xi : ContinuumPoissonConfiguration d}
    (b : continuumOriginCluster Xi) :
    continuumPoissonPointCoversOrigin Xi (continuumOriginClusterRoot b) ∧
      continuumPoissonPointActive Xi b.1 ∧
      continuumPoissonOccupiedSites Xi ∈
        siteConnectionEvent (continuumApproximationGraph d 1)
          (continuumOriginClusterRoot b).1 b.1.1 :=
  Classical.choose_spec (continuumOriginCluster_projects_to_siteConnection b.2)

noncomputable def continuumOriginClusterToProjectedWitness
    {d : ℕ} (Xi : ContinuumPoissonConfiguration d) :
    continuumOriginCluster Xi → ContinuumProjectedOriginWitness Xi :=
  fun b ↦ ⟨
    (⟨(continuumOriginClusterRoot b).1,
        continuumPoissonPointCoversOrigin_cube_mem
          (continuumOriginClusterRoot_spec b).1⟩,
      ⟨b.1.1, ⟨b.1.2, (continuumOriginClusterRoot_spec b).2.1⟩⟩),
    (continuumOriginClusterRoot_spec b).2.2⟩

theorem continuumOriginClusterToProjectedWitness_injective
    {d : ℕ} (Xi : ContinuumPoissonConfiguration d) :
    Function.Injective (continuumOriginClusterToProjectedWitness Xi) := by
  intro b c hbc
  apply Subtype.ext
  have htarget := congrArg
    (fun q : ContinuumProjectedOriginWitness Xi ↦
      (q.1.2.1, (q.1.2.2 : ℕ))) hbc
  simpa [continuumOriginClusterToProjectedWitness] using htarget

/-- Projected marked-point mass used to dominate `|W(0)|`. -/
noncomputable def continuumProjectedOriginMass {d : ℕ}
    (Xi : ContinuumPoissonConfiguration d) : ℝ≥0∞ :=
  ENat.toENNReal (ENat.card (ContinuumProjectedOriginWitness Xi))

/-- Deterministic marked-point form of the comparison preceding (12.44). -/
theorem continuumOriginClusterSize_le_projectedOriginMass
    {d : ℕ} (Xi : ContinuumPoissonConfiguration d) :
    continuumOriginClusterSize Xi ≤ continuumProjectedOriginMass Xi := by
  rw [continuumOriginClusterSize_eq_encard]
  exact ENat.toENNReal_mono <|
    ENat.card_le_card_of_injective
      (continuumOriginClusterToProjectedWitness_injective Xi)

/-- Expand the projected witness cardinality by starting cube and target cube. -/
theorem continuumProjectedOriginMass_eq_tsum
    {d : ℕ} (Xi : ContinuumPoissonConfiguration d) :
    continuumProjectedOriginMass Xi =
      ∑' s : ↥(continuumOriginNeighborCubes d),
        ∑' x : Cubic d,
          (siteConnectionEvent (continuumApproximationGraph d 1) s.1 x).indicator
            (fun _ ↦ (continuumPoissonCubeCounts Xi x : ℝ≥0∞))
            (continuumPoissonOccupiedSites Xi) := by
  classical
  calc
    continuumProjectedOriginMass Xi =
        ∑' _q : ContinuumProjectedOriginWitness Xi, (1 : ℝ≥0∞) := by
      unfold continuumProjectedOriginMass
      simpa using (ENNReal.tsum_set_one
        (Set.univ : Set (ContinuumProjectedOriginWitness Xi))).symm
    _ = ∑' q : (↥(continuumOriginNeighborCubes d) ×
          (Σ x : Cubic d, Fin (continuumPoissonCubeCounts Xi x))),
        (show Set (↥(continuumOriginNeighborCubes d) ×
          (Σ x : Cubic d, Fin (continuumPoissonCubeCounts Xi x))) from
          {q | continuumPoissonOccupiedSites Xi ∈
            siteConnectionEvent (continuumApproximationGraph d 1) q.1.1 q.2.1}).indicator
          (fun _ ↦ (1 : ℝ≥0∞)) q := by
      exact tsum_subtype
        ({q : (↥(continuumOriginNeighborCubes d) ×
          (Σ x : Cubic d, Fin (continuumPoissonCubeCounts Xi x))) |
            continuumPoissonOccupiedSites Xi ∈
              siteConnectionEvent (continuumApproximationGraph d 1)
                q.1.1 q.2.1})
        (fun _ ↦ (1 : ℝ≥0∞))
    _ = ∑' s : ↥(continuumOriginNeighborCubes d),
        ∑' x : Cubic d,
          (siteConnectionEvent (continuumApproximationGraph d 1) s.1 x).indicator
            (fun _ ↦ (continuumPoissonCubeCounts Xi x : ℝ≥0∞))
            (continuumPoissonOccupiedSites Xi) := by
      rw [ENNReal.tsum_prod']
      apply tsum_congr
      intro s
      rw [ENNReal.tsum_sigma']
      apply tsum_congr
      intro x
      by_cases hconn : continuumPoissonOccupiedSites Xi ∈
          siteConnectionEvent (continuumApproximationGraph d 1) s.1 x
      · simp [Set.indicator_of_mem hconn, hconn]
      · simp [Set.indicator_of_notMem hconn, hconn]

/-- Open-path expansion of the projected marked-point mass, now defined directly on the
independent cube-count field. -/
noncomputable def continuumProjectedPathMass (d : ℕ)
    (N : PoissonCubeConfiguration d) : ℝ≥0∞ :=
  ∑' s : ↥(continuumOriginNeighborCubes d),
    ∑' q : SiteRootedPathCode (continuumApproximationGraph d 1) s.1,
      (siteWalkOpenEvent (siteRootedPathCodeWalk q)).indicator
        (fun _ ↦ (N q.2.1.1 : ℝ≥0∞)) (continuumOccupiedSites N)

theorem measurable_continuumProjectedPathMass (d : ℕ) :
    Measurable (continuumProjectedPathMass d) := by
  classical
  unfold continuumProjectedPathMass
  apply Measurable.tsum
  intro s
  apply Measurable.tsum
  intro q
  have hset : MeasurableSet
      (continuumOccupiedSites ⁻¹'
        siteWalkOpenEvent (siteRootedPathCodeWalk q)) :=
    (measurableSet_siteWalkOpenEvent
      (siteRootedPathCodeWalk q)).preimage measurable_continuumOccupiedSites
  have hweight : Measurable
      (fun N : PoissonCubeConfiguration d ↦ (N q.2.1.1 : ℝ≥0∞)) := by
    fun_prop
  have heq :
      (fun N : PoissonCubeConfiguration d ↦
        (siteWalkOpenEvent (siteRootedPathCodeWalk q)).indicator
          (fun _ ↦ (N q.2.1.1 : ℝ≥0∞)) (continuumOccupiedSites N)) =
        (continuumOccupiedSites ⁻¹'
          siteWalkOpenEvent (siteRootedPathCodeWalk q)).indicator
            (fun N ↦ (N q.2.1.1 : ℝ≥0∞)) := by
    funext N
    rfl
  rw [heq]
  exact hweight.indicator hset

/-- The projected witness mass is bounded pointwise by the marked mass of all open
self-avoiding paths. -/
theorem continuumProjectedOriginMass_le_pathMass
    {d : ℕ} (Xi : ContinuumPoissonConfiguration d) :
    continuumProjectedOriginMass Xi ≤
      continuumProjectedPathMass d (continuumPoissonCubeCounts Xi) := by
  rw [continuumProjectedOriginMass_eq_tsum]
  apply ENNReal.tsum_le_tsum
  intro s
  simpa [continuumProjectedPathMass, continuumPoissonOccupiedSites] using
    siteClusterWeightedMass_le_openPathWeightedMass
      (continuumApproximationGraph d 1) s.1
      (continuumOccupiedSites (continuumPoissonCubeCounts Xi))
      (fun x ↦ (continuumPoissonCubeCounts Xi x : ℝ≥0∞))

private theorem nat_sq_le_four_pow (n : ℕ) : n ^ 2 ≤ 4 ^ n := by
  cases n with
  | zero => norm_num
  | succ n =>
      induction n with
      | zero => norm_num
      | succ n ih =>
          calc
            (n + 2) ^ 2 ≤ (2 * (n + 1)) ^ 2 := by gcongr <;> omega
            _ = 4 * (n + 1) ^ 2 := by ring
            _ ≤ 4 * 4 ^ (n + 1) := Nat.mul_le_mul_left 4 ih
            _ = 4 ^ (n + 2) := by ring

/-- The square of a Poisson random variable is integrable.  The elementary exponential-series
proof is included because Mathlib's Poisson API currently has no named second-moment lemma. -/
theorem integrable_natCast_sq_poissonMeasure (r : ℝ≥0) :
    Integrable (fun n : ℕ ↦ (n : ℝ) ^ 2) (poissonMeasure r) := by
  rw [integrable_poissonMeasure_iff]
  apply Summable.of_nonneg_of_le
      (fun n ↦ mul_nonneg (by positivity) (norm_nonneg _))
      (fun n ↦ ?_)
      ((Real.summable_pow_div_factorial (4 * (r : ℝ))).mul_left
        (Real.exp (-(r : ℝ))))
  rw [Real.norm_of_nonneg (sq_nonneg (n : ℝ))]
  have hn : (n : ℝ) ^ 2 ≤ 4 ^ n := by
    exact_mod_cast nat_sq_le_four_pow n
  calc
    Real.exp (-(r : ℝ)) * (r : ℝ) ^ n / (n.factorial : ℝ) * (n : ℝ) ^ 2 ≤
        Real.exp (-(r : ℝ)) * (r : ℝ) ^ n / (n.factorial : ℝ) * 4 ^ n := by
      gcongr
    _ = Real.exp (-(r : ℝ)) *
        ((4 * (r : ℝ)) ^ n / (n.factorial : ℝ)) := by
      rw [mul_pow]
      ring

/-- Extended-real second moment of one Poisson cube count. -/
noncomputable def poissonCountSecondMoment (r : ℝ≥0) : ℝ≥0∞ :=
  ∫⁻ n : ℕ, (n : ℝ≥0∞) ^ 2 ∂poissonMeasure r

theorem poissonCountSecondMoment_lt_top (r : ℝ≥0) :
    poissonCountSecondMoment r < ⊤ := by
  unfold poissonCountSecondMoment
  convert (integrable_natCast_sq_poissonMeasure r).lintegral_lt_top using 1 <;> simp

theorem lintegral_poissonCube_count_sq
    (d : ℕ) (intensity : ℝ≥0) (x : Cubic d) :
    (∫⁻ N : PoissonCubeConfiguration d,
        (N x : ℝ≥0∞) ^ 2 ∂poissonCubeMeasure d intensity 1) =
      poissonCountSecondMoment intensity := by
  unfold poissonCubeMeasure
  calc
    (∫⁻ N : PoissonCubeConfiguration d, (N x : ℝ≥0∞) ^ 2
        ∂Measure.infinitePi fun _ : Cubic d ↦
          poissonMeasure (continuumCubeRate d intensity 1)) =
        ∫⁻ n : ℕ, (n : ℝ≥0∞) ^ 2
          ∂Measure.map (fun N : PoissonCubeConfiguration d ↦ N x)
            (Measure.infinitePi fun _ : Cubic d ↦
              poissonMeasure (continuumCubeRate d intensity 1)) :=
      (MeasureTheory.lintegral_map
        (f := fun n : ℕ ↦ (n : ℝ≥0∞) ^ 2)
        (g := fun N : PoissonCubeConfiguration d ↦ N x)
        (measurable_of_countable _) (measurable_pi_apply x)).symm
    _ = ∫⁻ n : ℕ, (n : ℝ≥0∞) ^ 2
        ∂poissonMeasure (continuumCubeRate d intensity 1) := by
      rw [Measure.infinitePi_map_eval]
    _ = poissonCountSecondMoment intensity := by
      simp [continuumCubeRate, poissonCountSecondMoment]

/-- Exact probability that the occupied Poisson cubes contain a prescribed self-avoiding
site path. -/
theorem poissonCubeMeasure_preimage_siteWalkOpenEvent
    {d : ℕ} (intensity : ℝ≥0) {s x : Cubic d}
    (w : (continuumApproximationGraph d 1).Walk s x) (hw : w.IsPath) :
    poissonCubeMeasure d intensity 1
        (continuumOccupiedSites ⁻¹' siteWalkOpenEvent w) =
      ENNReal.ofReal
        ((continuumCubeDensity d intensity 1 : ℝ) ^ (w.length + 1)) := by
  have hmap := poissonCubeMeasure_map_continuumOccupiedSites d intensity 1
  have happ := congrArg
    (fun mu : Measure (Set (Cubic d)) ↦ mu (siteWalkOpenEvent w)) hmap
  change (Measure.map continuumOccupiedSites (poissonCubeMeasure d intensity 1))
      (siteWalkOpenEvent w) = _ at happ
  rw [Measure.map_apply measurable_continuumOccupiedSites
    (measurableSet_siteWalkOpenEvent w)] at happ
  exact happ.trans
    (setBernoulli_siteWalkOpenEvent_of_isPath w hw
      (continuumCubeDensity d intensity 1))

/-- The square-root density used after applying Cauchy--Schwarz to a path event. -/
noncomputable def continuumCubeSqrtDensity
    (d : ℕ) (intensity : ℝ≥0) (n : ℕ) : I :=
  ⟨Real.sqrt (continuumCubeDensity d intensity n : ℝ), by
    constructor
    · exact Real.sqrt_nonneg _
    · rw [Real.sqrt_le_one]
      exact (continuumCubeDensity d intensity n).2.2⟩

@[simp]
theorem continuumCubeSqrtDensity_coe
    (d : ℕ) (intensity : ℝ≥0) (n : ℕ) :
    (continuumCubeSqrtDensity d intensity n : ℝ) =
      Real.sqrt (continuumCubeDensity d intensity n : ℝ) :=
  rfl

private theorem ofReal_pow_rpow_half_eq_ofReal_sqrt_pow
    {p : ℝ} (hp : 0 ≤ p) (n : ℕ) :
    (ENNReal.ofReal (p ^ n)) ^ (1 / 2 : ℝ) =
      ENNReal.ofReal ((Real.sqrt p) ^ n) := by
  rw [ENNReal.ofReal_rpow_of_nonneg (pow_nonneg hp n) (by norm_num)]
  congr 1
  rw [Real.sqrt_eq_rpow]
  calc
    (p ^ n) ^ (1 / 2 : ℝ) = (p ^ (n : ℝ)) ^ (1 / 2 : ℝ) := by
      rw [Real.rpow_natCast]
    _ = p ^ ((n : ℝ) * (1 / 2 : ℝ)) := by rw [Real.rpow_mul hp]
    _ = p ^ ((1 / 2 : ℝ) * (n : ℝ)) := by ring
    _ = (p ^ (1 / 2 : ℝ)) ^ (n : ℝ) := by rw [Real.rpow_mul hp]
    _ = (p ^ (1 / 2 : ℝ)) ^ n := by rw [Real.rpow_natCast]

/-- Cauchy--Schwarz estimate for the number of Poisson points at the endpoint of a prescribed
open path.  No false independence between the endpoint count and path event is used. -/
theorem lintegral_poissonCube_count_indicator_siteWalkOpenEvent_le
    {d : ℕ} (intensity : ℝ≥0) {s x : Cubic d}
    (w : (continuumApproximationGraph d 1).Walk s x) (hw : w.IsPath) :
    (∫⁻ N : PoissonCubeConfiguration d,
      (siteWalkOpenEvent w).indicator (fun _ ↦ (N x : ℝ≥0∞))
        (continuumOccupiedSites N) ∂poissonCubeMeasure d intensity 1) ≤
      (poissonCountSecondMoment intensity) ^ (1 / 2 : ℝ) *
        (ENNReal.ofReal
          ((continuumCubeDensity d intensity 1 : ℝ) ^ (w.length + 1))) ^
            (1 / 2 : ℝ) := by
  let mu := poissonCubeMeasure d intensity 1
  let A : Set (PoissonCubeConfiguration d) :=
    continuumOccupiedSites ⁻¹' siteWalkOpenEvent w
  let f : PoissonCubeConfiguration d → ℝ≥0∞ := fun N ↦ (N x : ℝ≥0∞)
  let g : PoissonCubeConfiguration d → ℝ≥0∞ :=
    A.indicator (fun _ ↦ 1)
  have hA : MeasurableSet A :=
    (measurableSet_siteWalkOpenEvent w).preimage measurable_continuumOccupiedSites
  have hf : Measurable f := by fun_prop
  have hg : Measurable g := measurable_const.indicator hA
  have hleft :
      (∫⁻ N : PoissonCubeConfiguration d,
        (siteWalkOpenEvent w).indicator (fun _ ↦ (N x : ℝ≥0∞))
          (continuumOccupiedSites N) ∂mu) =
        ∫⁻ N, (f * g) N ∂mu := by
    apply lintegral_congr
    intro N
    by_cases hN : continuumOccupiedSites N ∈ siteWalkOpenEvent w
    · have hNA : N ∈ A := hN
      simp [A, f, g, hN, hNA]
    · have hNA : N ∉ A := hN
      simp [A, f, g, hN, hNA]
  rw [hleft]
  refine (ENNReal.lintegral_mul_le_Lp_mul_Lq mu
    Real.HolderConjugate.two_two hf.aemeasurable hg.aemeasurable).trans_eq ?_
  have hfMoment : (∫⁻ N, f N ^ (2 : ℝ) ∂mu) =
      poissonCountSecondMoment intensity := by
    simpa [mu, f, ENNReal.rpow_two] using
      lintegral_poissonCube_count_sq d intensity x
  have hgMoment : (∫⁻ N, g N ^ (2 : ℝ) ∂mu) = mu A := by
    have heq : (fun N ↦ g N ^ (2 : ℝ)) = A.indicator (fun _ ↦ 1) := by
      funext N
      by_cases hN : N ∈ A <;> simp [g, hN]
    rw [heq, lintegral_indicator hA]
    simp
  rw [hfMoment, hgMoment]
  simp only [one_div]
  rw [show mu A = ENNReal.ofReal
      ((continuumCubeDensity d intensity 1 : ℝ) ^ (w.length + 1)) by
    exact poissonCubeMeasure_preimage_siteWalkOpenEvent intensity w hw]

/-- Path-code form of the preceding Cauchy--Schwarz estimate. -/
theorem lintegral_poissonCube_pathCodeMass_le
    {d : ℕ} (intensity : ℝ≥0)
    (s : Cubic d)
    (q : SiteRootedPathCode (continuumApproximationGraph d 1) s) :
    (∫⁻ N : PoissonCubeConfiguration d,
      (siteWalkOpenEvent (siteRootedPathCodeWalk q)).indicator
        (fun _ ↦ (N q.2.1.1 : ℝ≥0∞)) (continuumOccupiedSites N)
        ∂poissonCubeMeasure d intensity 1) ≤
      (poissonCountSecondMoment intensity) ^ (1 / 2 : ℝ) *
        setBer((Set.univ : Set (Cubic d)),
          continuumCubeSqrtDensity d intensity 1)
            (siteWalkOpenEvent (siteRootedPathCodeWalk q)) := by
  have hmem := Finset.mem_filter.mp q.2.2
  have hbound :=
    lintegral_poissonCube_count_indicator_siteWalkOpenEvent_le
      intensity (siteRootedPathCodeWalk q) hmem.2
  refine hbound.trans_eq ?_
  congr 1
  rw [setBernoulli_siteWalkOpenEvent_of_isPath
    (siteRootedPathCodeWalk q) hmem.2
      (continuumCubeSqrtDensity d intensity 1)]
  exact ofReal_pow_rpow_half_eq_ofReal_sqrt_pow
    (continuumCubeDensity d intensity 1).2.1
    ((siteRootedPathCodeWalk q).length + 1)

private theorem measurable_continuumProjectedPathTerm
    {d : ℕ} (s : ↥(continuumOriginNeighborCubes d))
    (q : SiteRootedPathCode (continuumApproximationGraph d 1) s.1) :
    Measurable (fun N : PoissonCubeConfiguration d ↦
      (siteWalkOpenEvent (siteRootedPathCodeWalk q)).indicator
        (fun _ ↦ (N q.2.1.1 : ℝ≥0∞)) (continuumOccupiedSites N)) := by
  have hset : MeasurableSet
      (continuumOccupiedSites ⁻¹'
        siteWalkOpenEvent (siteRootedPathCodeWalk q)) :=
    (measurableSet_siteWalkOpenEvent
      (siteRootedPathCodeWalk q)).preimage measurable_continuumOccupiedSites
  have hweight : Measurable
      (fun N : PoissonCubeConfiguration d ↦ (N q.2.1.1 : ℝ≥0∞)) := by
    fun_prop
  have heq :
      (fun N : PoissonCubeConfiguration d ↦
        (siteWalkOpenEvent (siteRootedPathCodeWalk q)).indicator
          (fun _ ↦ (N q.2.1.1 : ℝ≥0∞)) (continuumOccupiedSites N)) =
        (continuumOccupiedSites ⁻¹'
          siteWalkOpenEvent (siteRootedPathCodeWalk q)).indicator
            (fun N ↦ (N q.2.1.1 : ℝ≥0∞)) := by
    funext N
    rfl
  rw [heq]
  exact hweight.indicator hset

/-- The projected open-path mass has finite expectation whenever the square-root occupation
density is in the elementary bounded-degree regime. -/
theorem lintegral_continuumProjectedPathMass_lt_top
    (d : ℕ) (intensity : ℝ≥0)
    (hsmall : (9 ^ d : ℝ) *
      (continuumCubeSqrtDensity d intensity 1 : ℝ) < 1) :
    (∫⁻ N, continuumProjectedPathMass d N
      ∂poissonCubeMeasure d intensity 1) < ⊤ := by
  let p : I := continuumCubeSqrtDensity d intensity 1
  let pE : ℝ≥0∞ := ENNReal.ofReal (p : ℝ)
  let D : ℕ := 9 ^ d
  let r : ℝ≥0∞ := (D : ℝ≥0∞) * pE
  let C : ℝ≥0∞ := (poissonCountSecondMoment intensity) ^ (1 / 2 : ℝ)
  have hr : r < 1 := by
    rw [show r = ENNReal.ofReal ((D : ℝ) * (p : ℝ)) by
      simp [r, pE, ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ D)]]
    exact (ENNReal.ofReal_lt_one).2 (by simpa [D, p] using hsmall)
  have hgeom :
      (∑' n : ℕ, (D : ℝ≥0∞) ^ n * pE ^ (n + 1)) < ⊤ := by
    have heq :
        (∑' n : ℕ, (D : ℝ≥0∞) ^ n * pE ^ (n + 1)) =
          pE * (1 - r)⁻¹ := by
      calc
        (∑' n : ℕ, (D : ℝ≥0∞) ^ n * pE ^ (n + 1)) =
            ∑' n : ℕ, pE * r ^ n := by
          apply tsum_congr
          intro n
          simp only [r, pow_succ']
          ring
        _ = pE * ∑' n : ℕ, r ^ n := ENNReal.tsum_mul_left
        _ = pE * (1 - r)⁻¹ := by rw [ENNReal.tsum_geometric]
    rw [heq]
    apply ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    rw [ENNReal.inv_lt_top]
    exact tsub_pos_iff_lt.mpr hr
  have hpath (s : Cubic d) :
      (∑' q : SiteRootedPathCode (continuumApproximationGraph d 1) s,
        setBer((Set.univ : Set (Cubic d)), p)
          (siteWalkOpenEvent (siteRootedPathCodeWalk q))) < ⊤ := by
    refine lt_of_le_of_lt ?_ hgeom
    simpa [D, pE, p] using
      tsum_measure_siteOpenPathCode_le_geometric
        (continuumApproximationGraph d 1)
        (continuumApproximationGraph_one_degree_le d) p s
  have hC : C < ⊤ :=
    ENNReal.rpow_lt_top_of_nonneg (by norm_num)
      (poissonCountSecondMoment_lt_top intensity).ne
  calc
    (∫⁻ N, continuumProjectedPathMass d N
        ∂poissonCubeMeasure d intensity 1) =
        ∑' s : ↥(continuumOriginNeighborCubes d),
          ∑' q : SiteRootedPathCode (continuumApproximationGraph d 1) s.1,
            ∫⁻ N,
              (siteWalkOpenEvent (siteRootedPathCodeWalk q)).indicator
                (fun _ ↦ (N q.2.1.1 : ℝ≥0∞)) (continuumOccupiedSites N)
                ∂poissonCubeMeasure d intensity 1 := by
      unfold continuumProjectedPathMass
      rw [lintegral_tsum]
      · apply tsum_congr
        intro s
        rw [lintegral_tsum]
        intro q
        exact (measurable_continuumProjectedPathTerm s q).aemeasurable
      · intro s
        exact (Measurable.tsum fun q ↦
          measurable_continuumProjectedPathTerm s q).aemeasurable
    _ ≤ ∑' s : ↥(continuumOriginNeighborCubes d),
        ∑' q : SiteRootedPathCode (continuumApproximationGraph d 1) s.1,
          C * setBer((Set.univ : Set (Cubic d)), p)
            (siteWalkOpenEvent (siteRootedPathCodeWalk q)) := by
      apply ENNReal.tsum_le_tsum
      intro s
      apply ENNReal.tsum_le_tsum
      intro q
      simpa [C, p] using lintegral_poissonCube_pathCodeMass_le intensity s.1 q
    _ = ∑' s : ↥(continuumOriginNeighborCubes d),
        C * (∑' q : SiteRootedPathCode (continuumApproximationGraph d 1) s.1,
          setBer((Set.univ : Set (Cubic d)), p)
            (siteWalkOpenEvent (siteRootedPathCodeWalk q))) := by
      apply tsum_congr
      intro s
      exact ENNReal.tsum_mul_left
    _ < ⊤ := by
      rw [tsum_fintype, ENNReal.sum_lt_top]
      intro s _hs
      exact ENNReal.mul_lt_top hC (hpath s.1)

/-- Transfer the projected-path expectation from the marked Poisson construction to its exact
independent cube-count marginal. -/
theorem lintegral_continuumPoisson_pathMass_eq_cube
    (d : ℕ) (intensity : ℝ≥0) :
    (∫⁻ Xi, continuumProjectedPathMass d (continuumPoissonCubeCounts Xi)
      ∂continuumPoissonMeasure d intensity) =
      ∫⁻ N, continuumProjectedPathMass d N
        ∂poissonCubeMeasure d intensity 1 := by
  calc
    (∫⁻ Xi, continuumProjectedPathMass d (continuumPoissonCubeCounts Xi)
        ∂continuumPoissonMeasure d intensity) =
        ∫⁻ N, continuumProjectedPathMass d N
          ∂(continuumPoissonMeasure d intensity).map
            continuumPoissonCubeCounts :=
      (MeasureTheory.lintegral_map
        (measurable_continuumProjectedPathMass d)
        measurable_continuumPoissonCubeCounts).symm
    _ = ∫⁻ N, continuumProjectedPathMass d N
        ∂poissonCubeMeasure d intensity 1 := by
      rw [continuumPoissonMeasure_map_cubeCounts]

/-- A genuine positive-density finite-mean criterion for the Boolean model.  This is the
unit-mesh, path-counting part of Grimmett's comparison (12.44); the sharp source threshold
will later replace this elementary square-root-density hypothesis. -/
theorem continuumMeanClusterSize_lt_top_of_sqrt_density
    (d : ℕ) (intensity : ℝ≥0)
    (hsmall : (9 ^ d : ℝ) *
      (continuumCubeSqrtDensity d intensity 1 : ℝ) < 1) :
    continuumMeanClusterSize d intensity < ⊤ := by
  calc
    continuumMeanClusterSize d intensity ≤
        ∫⁻ Xi, continuumProjectedOriginMass Xi
          ∂continuumPoissonMeasure d intensity := by
      unfold continuumMeanClusterSize
      exact lintegral_mono continuumOriginClusterSize_le_projectedOriginMass
    _ ≤ ∫⁻ Xi,
        continuumProjectedPathMass d (continuumPoissonCubeCounts Xi)
          ∂continuumPoissonMeasure d intensity := by
      exact lintegral_mono continuumProjectedOriginMass_le_pathMass
    _ = ∫⁻ N, continuumProjectedPathMass d N
        ∂poissonCubeMeasure d intensity 1 :=
      lintegral_continuumPoisson_pathMass_eq_cube d intensity
    _ < ⊤ := lintegral_continuumProjectedPathMass_lt_top d intensity hsmall

/-- An explicit positive intensity in the elementary finite-mean regime. -/
noncomputable def continuumElementaryMeanIntensity (d : ℕ) : ℝ≥0 :=
  ⟨(1 / (2 * (9 ^ d : ℝ))) ^ 2, sq_nonneg _⟩

theorem continuumElementaryMeanIntensity_pos (d : ℕ) :
    0 < continuumElementaryMeanIntensity d := by
  change 0 < (1 / (2 * (9 ^ d : ℝ))) ^ 2
  exact sq_pos_of_pos (one_div_pos.mpr (mul_pos (by norm_num) (pow_pos (by norm_num) d)))

theorem continuumElementaryMeanIntensity_sqrtDensity_small (d : ℕ) :
    (9 ^ d : ℝ) *
      (continuumCubeSqrtDensity d (continuumElementaryMeanIntensity d) 1 : ℝ) < 1 := by
  let D : ℝ := 9 ^ d
  let intensity : ℝ := continuumElementaryMeanIntensity d
  have hD : 0 < D := by positivity
  have hintensity : 0 ≤ intensity := by positivity
  have hdensity_nonneg :
      0 ≤ 1 - Real.exp (-intensity) := by
    exact sub_nonneg.mpr
      (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hintensity))
  have hdensity_le : 1 - Real.exp (-intensity) ≤ intensity := by
    linarith [Real.add_one_le_exp (-intensity)]
  have hintensity_eq : intensity = (1 / (2 * D)) ^ 2 := by
    rfl
  have hsqrt : Real.sqrt (1 - Real.exp (-intensity)) ≤ 1 / (2 * D) := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · rw [← hintensity_eq]
      exact hdensity_le
  have htarget : D * Real.sqrt (1 - Real.exp (-intensity)) < 1 := calc
    D * Real.sqrt (1 - Real.exp (-intensity)) ≤ D * (1 / (2 * D)) := by
      gcongr
    _ = 1 / 2 := by field_simp
    _ < 1 := by norm_num
  simpa [D, intensity, continuumCubeSqrtDensity_coe, continuumCubeDensity_coe,
    continuumCubeRate] using htarget

/-- The Boolean model has finite mean origin-cluster size at an explicit nonzero intensity. -/
theorem continuumMeanClusterSize_elementaryIntensity_lt_top (d : ℕ) :
    continuumMeanClusterSize d (continuumElementaryMeanIntensity d) < ⊤ :=
  continuumMeanClusterSize_lt_top_of_sqrt_density d
    (continuumElementaryMeanIntensity d)
    (continuumElementaryMeanIntensity_sqrtDensity_small d)

theorem continuumElementaryMeanIntensity_mem_finiteMean (d : ℕ) :
    continuumElementaryMeanIntensity d ∈ continuumFiniteMeanIntensities d :=
  continuumMeanClusterSize_elementaryIntensity_lt_top d

/-- Positive lower bound for the mean-cluster threshold in dimensions covered by the source. -/
theorem continuumMeanClusterThreshold_pos {d : ℕ} (hd : 2 ≤ d) :
    0 < continuumMeanClusterThreshold d := by
  refine (continuumElementaryMeanIntensity_pos d).trans_le ?_
  exact le_csSup (continuumFiniteMeanIntensities_bddAbove hd)
    (continuumElementaryMeanIntensity_mem_finiteMean d)

end Percolation
