import Percolation.Critical.ClusterSizeRate
import Percolation.Critical.ClusterDensityEndpoints
import Percolation.Critical.GhostConclusion
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# Analyticity below the percolation threshold

This file formalizes Grimmett's Theorem 6.108.  The complex functions below are the genuine
animal-series extensions of the cluster density and susceptibility.  Their convergence near
zero follows from the elementary exponential bound on the number of rooted animals.  The
interior argument uses the exact cluster-size exponential rate proved in Theorem 6.78.
-/

namespace Percolation

open Set Filter Topology
open scoped BigOperators ENNReal unitInterval Topology

noncomputable section

set_option maxHeartbeats 800000

/-- The complex weight of a concrete rooted bond animal. -/
def complexAnimalWeight {d n : ℕ} (A : CubicBondAnimal d n) (z : ℂ) : ℂ :=
  z ^ A.edges.card * (1 - z) ^ A.boundary.card

/-- The size-`n` complex animal contribution to the cluster density. -/
def complexClusterDensityLevel (d n : ℕ) (z : ℂ) : ℂ :=
  (1 / (n : ℂ)) * ∑ A : CubicBondAnimal d n, complexAnimalWeight A z

/-- The size-`n` complex animal contribution to susceptibility. -/
def complexSusceptibilityLevel (d n : ℕ) (z : ℂ) : ℂ :=
  (n : ℂ) * ∑ A : CubicBondAnimal d n, complexAnimalWeight A z

/-- The complex animal series extending the density of finite open clusters. -/
def complexClusterDensitySeries (d : ℕ) (z : ℂ) : ℂ :=
  ∑' n : ℕ, complexClusterDensityLevel d n z

/-- The complex animal series extending susceptibility in the subcritical regime. -/
def complexSusceptibilitySeries (d : ℕ) (z : ℂ) : ℂ :=
  ∑' n : ℕ, complexSusceptibilityLevel d n z

/-- The real animal series for susceptibility.  Unlike `susceptibility.toReal`, this definition
also makes sense off the physical interval and is therefore the function whose analyticity is
proved below. -/
def concreteSusceptibilityLevel (d n : ℕ) (p : ℝ) : ℝ :=
  (n : ℝ) * ∑ A : CubicBondAnimal d n,
    p ^ A.edges.card * (1 - p) ^ A.boundary.card

def concreteSusceptibilitySeries (d : ℕ) (p : ℝ) : ℝ :=
  ∑' n : ℕ, concreteSusceptibilityLevel d n p

theorem complexClusterDensityLevel_differentiable (d n : ℕ) :
    Differentiable ℂ (complexClusterDensityLevel d n) := by
  unfold complexClusterDensityLevel complexAnimalWeight
  fun_prop

theorem complexSusceptibilityLevel_differentiable (d n : ℕ) :
    Differentiable ℂ (complexSusceptibilityLevel d n) := by
  unfold complexSusceptibilityLevel complexAnimalWeight
  fun_prop

theorem complexClusterDensityLevel_zero (d : ℕ) (z : ℂ) :
    complexClusterDensityLevel d 0 z = 0 := by
  simp [complexClusterDensityLevel]

theorem complexSusceptibilityLevel_zero (d : ℕ) (z : ℂ) :
    complexSusceptibilityLevel d 0 z = 0 := by
  simp [complexSusceptibilityLevel]

theorem complexClusterDensityLevel_ofReal
    {d : ℕ} (hd : 0 < d) (n : ℕ) (p : ℝ) :
    complexClusterDensityLevel d n (p : ℂ) = concreteClusterDensityLevel d n p := by
  rw [concreteClusterDensityLevel_eq_sum_animals hd]
  unfold complexClusterDensityLevel concreteAnimalDensityTerm complexAnimalWeight
  rw [Finset.mul_sum]
  push_cast
  apply Finset.sum_congr rfl
  intro A _hA
  ring

theorem complexSusceptibilityLevel_ofReal
    (d n : ℕ) (p : I) :
    complexSusceptibilityLevel d n (p : ℂ) =
      ((n : ℝ) * finiteClusterSizeProbability d p n : ℝ) := by
  rw [finiteClusterSizeProbability_eq_sum_animals]
  unfold complexSusceptibilityLevel complexAnimalWeight
  push_cast
  rfl

theorem complexSusceptibilityLevel_ofReal_real
    (d n : ℕ) (p : ℝ) :
    complexSusceptibilityLevel d n (p : ℂ) = concreteSusceptibilityLevel d n p := by
  unfold complexSusceptibilityLevel concreteSusceptibilityLevel complexAnimalWeight
  push_cast
  rfl

/-- A complex animal weight near zero has the same endpoint majorant as its real counterpart. -/
theorem norm_complexAnimalWeight_le_endpoint
    {d n : ℕ} (_hn : 1 ≤ n) {z : ℂ}
    (hz : ‖z‖ ≤ clusterDensityEndpointRadius d) (A : CubicBondAnimal d n) :
    ‖complexAnimalWeight A z‖ ≤
      clusterDensityEndpointRadius d ^ (n - 1) *
        (1 + clusterDensityEndpointRadius d) ^ (2 * d * n) := by
  let R := clusterDensityEndpointRadius d
  have hR0 : 0 ≤ R := (clusterDensityEndpointRadius_pos d).le
  have hR1 : R ≤ 1 := clusterDensityEndpointRadius_le_one d
  have hq0 : 1 ≤ 1 + R := by linarith
  have hzPow : ‖z‖ ^ A.edges.card ≤ R ^ (n - 1) := by
    calc
      ‖z‖ ^ A.edges.card ≤ R ^ A.edges.card := by gcongr
      _ ≤ R ^ (n - 1) :=
        pow_le_pow_of_le_one hR0 hR1 A.edges_card_lower
  have hq : ‖1 - z‖ ≤ 1 + R := by
    calc
      ‖1 - z‖ ≤ ‖(1 : ℂ)‖ + ‖z‖ := norm_sub_le _ _
      _ ≤ 1 + R := by simpa using add_le_add_left hz 1
  have hqPow : ‖1 - z‖ ^ A.boundary.card ≤ (1 + R) ^ (2 * d * n) := by
    calc
      ‖1 - z‖ ^ A.boundary.card ≤ (1 + R) ^ A.boundary.card := by gcongr
      _ ≤ (1 + R) ^ (2 * d * n) := pow_le_pow_right₀ hq0 A.boundary_card_le
  unfold complexAnimalWeight
  rw [norm_mul, norm_pow, norm_pow]
  gcongr

theorem norm_complexClusterWeightLevel_le_endpointGeometric
    {d n : ℕ} (hn : 1 ≤ n) {z : ℂ}
    (hz : ‖z‖ ≤ clusterDensityEndpointRadius d) :
    ‖∑ A : CubicBondAnimal d n, complexAnimalWeight A z‖ ≤
      (1 / clusterDensityEndpointRadius d) * (1 / 4 : ℝ) ^ n := by
  let R := clusterDensityEndpointRadius d
  let B : ℝ := (2 : ℝ) ^ (3 * d) * (1 + R) ^ (2 * d) * R
  have hR0 : 0 ≤ R := (clusterDensityEndpointRadius_pos d).le
  have hRne : R ≠ 0 := ne_of_gt (clusterDensityEndpointRadius_pos d)
  have hB0 : 0 ≤ B := by positivity
  have hB : B ≤ 1 / 4 := clusterDensityEndpoint_geometricBase_le_quarter d
  calc
    ‖∑ A : CubicBondAnimal d n, complexAnimalWeight A z‖ ≤
        ∑ A : CubicBondAnimal d n, ‖complexAnimalWeight A z‖ := norm_sum_le _ _
    _ ≤ ∑ _A : CubicBondAnimal d n,
        R ^ (n - 1) * (1 + R) ^ (2 * d * n) := by
      apply Finset.sum_le_sum
      intro A _hA
      exact norm_complexAnimalWeight_le_endpoint hn hz A
    _ = (Fintype.card (CubicBondAnimal d n) : ℝ) *
        (R ^ (n - 1) * (1 + R) ^ (2 * d * n)) := by simp
    _ ≤ (2 : ℝ) ^ (3 * d * n) *
        (R ^ (n - 1) * (1 + R) ^ (2 * d * n)) := by
      gcongr
      exact card_cubicBondAnimal_le_pow_two_three_d_n d n
    _ = (1 / R) * B ^ n := by
      dsimp [B]
      rw [show n = n - 1 + 1 by omega, pow_add, pow_mul, pow_mul]
      field_simp
      ring_nf
      rw [show 1 + (n - 1) - 1 = n - 1 by omega]
    _ ≤ (1 / R) * (1 / 4 : ℝ) ^ n := by gcongr

theorem norm_complexClusterDensityLevel_le_endpointGeometric
    {d n : ℕ} (hn : 1 ≤ n) {z : ℂ}
    (hz : ‖z‖ ≤ clusterDensityEndpointRadius d) :
    ‖complexClusterDensityLevel d n z‖ ≤
      (1 / clusterDensityEndpointRadius d) * (1 / 4 : ℝ) ^ n := by
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hinv : ‖(1 / (n : ℂ))‖ ≤ 1 := by
    rw [norm_div, norm_one, norm_natCast]
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hnreal
  rw [complexClusterDensityLevel, norm_mul]
  calc
    ‖(1 / (n : ℂ))‖ * ‖∑ A : CubicBondAnimal d n, complexAnimalWeight A z‖ ≤
        1 * ((1 / clusterDensityEndpointRadius d) * (1 / 4 : ℝ) ^ n) := by
      gcongr
      exact norm_complexClusterWeightLevel_le_endpointGeometric hn hz
    _ = _ := one_mul _

theorem norm_complexSusceptibilityLevel_le_endpointGeometric
    {d n : ℕ} (hn : 1 ≤ n) {z : ℂ}
    (hz : ‖z‖ ≤ clusterDensityEndpointRadius d) :
    ‖complexSusceptibilityLevel d n z‖ ≤
      (1 / clusterDensityEndpointRadius d) * (n : ℝ) * (1 / 4 : ℝ) ^ n := by
  rw [complexSusceptibilityLevel, norm_mul, norm_natCast]
  have h := norm_complexClusterWeightLevel_le_endpointGeometric hn hz
  calc
    (n : ℝ) * ‖∑ A : CubicBondAnimal d n, complexAnimalWeight A z‖ ≤
        (n : ℝ) * ((1 / clusterDensityEndpointRadius d) * (1 / 4 : ℝ) ^ n) := by
      gcongr
    _ = _ := by ring

theorem complexClusterDensitySeries_differentiableOn_endpoint
    {d : ℕ} (_hd : 0 < d) :
    DifferentiableOn ℂ (complexClusterDensitySeries d)
      (Metric.ball 0 (clusterDensityEndpointRadius d)) := by
  let C : ℝ := 1 / clusterDensityEndpointRadius d
  let u : ℕ → ℝ := fun n ↦ C * (1 / 4 : ℝ) ^ n
  have hu : Summable u :=
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 4 : ℝ)‖ < 1)).mul_left C
  apply Complex.differentiableOn_tsum_of_summable_norm hu
  · intro n
    exact (complexClusterDensityLevel_differentiable d n).differentiableOn
  · exact Metric.isOpen_ball
  · intro n z hz
    by_cases hn : n = 0
    · subst n
      rw [complexClusterDensityLevel_zero, norm_zero]
      dsimp [u, C]
      simpa using one_div_nonneg.mpr (clusterDensityEndpointRadius_pos d).le
    · have hC : 0 ≤ C := by
        dsimp [C]
        exact one_div_nonneg.mpr (clusterDensityEndpointRadius_pos d).le
      exact norm_complexClusterDensityLevel_le_endpointGeometric
        (Nat.pos_of_ne_zero hn) (by simpa [dist_zero_right] using (Metric.mem_ball.mp hz).le)

theorem complexSusceptibilitySeries_differentiableOn_endpoint
    {d : ℕ} (_hd : 0 < d) :
    DifferentiableOn ℂ (complexSusceptibilitySeries d)
      (Metric.ball 0 (clusterDensityEndpointRadius d)) := by
  let C : ℝ := 1 / clusterDensityEndpointRadius d
  let u : ℕ → ℝ := fun n ↦ C * (n : ℝ) * (1 / 4 : ℝ) ^ n
  have hgeom : Summable (fun n : ℕ ↦ (n : ℝ) * (1 / 4 : ℝ) ^ n) :=
    by
      simpa using
        (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1
          (by norm_num : ‖(1 / 4 : ℝ)‖ < 1))
  have hu : Summable u := by
    convert hgeom.mul_left C using 1
    ext n
    dsimp [u]
    ring
  apply Complex.differentiableOn_tsum_of_summable_norm hu
  · intro n
    exact (complexSusceptibilityLevel_differentiable d n).differentiableOn
  · exact Metric.isOpen_ball
  · intro n z hz
    by_cases hn : n = 0
    · subst n
      simp [complexSusceptibilityLevel_zero, u]
    · have hC : 0 ≤ C := by
        dsimp [C]
        exact one_div_nonneg.mpr (clusterDensityEndpointRadius_pos d).le
      exact norm_complexSusceptibilityLevel_le_endpointGeometric
        (Nat.pos_of_ne_zero hn) (by simpa [dist_zero_right] using (Metric.mem_ball.mp hz).le)

theorem complexClusterDensitySeries_analyticAt_zero
    {d : ℕ} (hd : 0 < d) :
    AnalyticAt ℂ (complexClusterDensitySeries d) 0 :=
  ((complexClusterDensitySeries_differentiableOn_endpoint hd).analyticOnNhd
    Metric.isOpen_ball) 0 (Metric.mem_ball_self (clusterDensityEndpointRadius_pos d))

theorem complexSusceptibilitySeries_analyticAt_zero
    {d : ℕ} (hd : 0 < d) :
    AnalyticAt ℂ (complexSusceptibilitySeries d) 0 :=
  ((complexSusceptibilitySeries_differentiableOn_endpoint hd).analyticOnNhd
    Metric.isOpen_ball) 0 (Metric.mem_ball_self (clusterDensityEndpointRadius_pos d))

/-! ### Interior subcritical neighborhoods -/

/-- The norm of a complex animal level is controlled by the physical level when both the open
and closed edge factors grow by at most `R`. -/
theorem norm_complexClusterWeightLevel_le_ratio
    {d n : ℕ} (p : I) {R : ℝ} (hR : 1 ≤ R) {z : ℂ}
    (hz : ‖z‖ ≤ (p : ℝ) * R)
    (hq : ‖1 - z‖ ≤ (1 - (p : ℝ)) * R) :
    ‖∑ A : CubicBondAnimal d n, complexAnimalWeight A z‖ ≤
      R ^ (3 * d * n) * finiteClusterSizeProbability d p n := by
  have hp0 : 0 ≤ (p : ℝ) := p.2.1
  have hp1 : 0 ≤ 1 - (p : ℝ) := sub_nonneg.mpr p.2.2
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  calc
    ‖∑ A : CubicBondAnimal d n, complexAnimalWeight A z‖ ≤
        ∑ A : CubicBondAnimal d n, ‖complexAnimalWeight A z‖ := norm_sum_le _ _
    _ ≤ ∑ A : CubicBondAnimal d n,
        R ^ (3 * d * n) *
          ((p : ℝ) ^ A.edges.card * (1 - (p : ℝ)) ^ A.boundary.card) := by
      apply Finset.sum_le_sum
      intro A _hA
      have hsum : A.edges.card + A.boundary.card ≤ 3 * d * n := by
        calc
          A.edges.card + A.boundary.card ≤ d * n + 2 * d * n :=
            Nat.add_le_add A.edges_card_upper A.boundary_card_le
          _ = 3 * d * n := by ring
      have hratio : R ^ (A.edges.card + A.boundary.card) ≤ R ^ (3 * d * n) :=
        pow_le_pow_right₀ hR hsum
      unfold complexAnimalWeight
      rw [norm_mul, norm_pow, norm_pow]
      calc
        ‖z‖ ^ A.edges.card * ‖1 - z‖ ^ A.boundary.card ≤
            ((p : ℝ) * R) ^ A.edges.card *
              ((1 - (p : ℝ)) * R) ^ A.boundary.card := by gcongr
        _ = R ^ (A.edges.card + A.boundary.card) *
            ((p : ℝ) ^ A.edges.card * (1 - (p : ℝ)) ^ A.boundary.card) := by
          rw [mul_pow, mul_pow, pow_add]
          ring
        _ ≤ R ^ (3 * d * n) *
            ((p : ℝ) ^ A.edges.card * (1 - (p : ℝ)) ^ A.boundary.card) := by
          gcongr
    _ = R ^ (3 * d * n) * finiteClusterSizeProbability d p n := by
      rw [finiteClusterSizeProbability_eq_sum_animals, Finset.mul_sum]

/-- The ratio chosen in the interior argument.  Its exponent spends exactly half of the
physical cluster-size decay rate. -/
def clusterAnalyticityRatio (d : ℕ) (zeta : ℝ) : ℝ :=
  Real.exp (zeta / (6 * d))

theorem clusterAnalyticityRatio_one_lt
    {d : ℕ} (hd : 0 < d) {zeta : ℝ} (hzeta : 0 < zeta) :
    1 < clusterAnalyticityRatio d zeta := by
  rw [clusterAnalyticityRatio, Real.one_lt_exp_iff]
  positivity

theorem clusterAnalyticity_geometricBase_eq
    {d : ℕ} (hd : 0 < d) (zeta : ℝ) :
    clusterAnalyticityRatio d zeta ^ (3 * d) * Real.exp (-zeta) =
      Real.exp (-zeta / 2) := by
  rw [clusterAnalyticityRatio, ← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  push_cast
  field_simp
  ring

/-- A radius on which both the open and closed complex edge weights are inflated by no more
than `clusterAnalyticityRatio`. -/
def clusterAnalyticityRadius (d : ℕ) (p zeta : ℝ) : ℝ :=
  min (p * (clusterAnalyticityRatio d zeta - 1))
    ((1 - p) * (clusterAnalyticityRatio d zeta - 1)) / 2

theorem clusterAnalyticityRadius_pos
    {d : ℕ} (hd : 0 < d) {p zeta : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (hzeta : 0 < zeta) :
    0 < clusterAnalyticityRadius d p zeta := by
  unfold clusterAnalyticityRadius
  have hR := clusterAnalyticityRatio_one_lt hd hzeta
  positivity

theorem norm_le_mul_ratio_of_mem_analyticityBall
    {d : ℕ} {p zeta : ℝ} (hp0 : 0 ≤ p)
    (hR : 1 ≤ clusterAnalyticityRatio d zeta) {z : ℂ}
    (hz : z ∈ Metric.ball (p : ℂ) (clusterAnalyticityRadius d p zeta)) :
    ‖z‖ ≤ p * clusterAnalyticityRatio d zeta := by
  have hdist : ‖z - (p : ℂ)‖ < clusterAnalyticityRadius d p zeta := by
    simpa [dist_eq_norm] using Metric.mem_ball.mp hz
  have hrle : clusterAnalyticityRadius d p zeta ≤
      p * (clusterAnalyticityRatio d zeta - 1) / 2 := by
    unfold clusterAnalyticityRadius
    exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hnormp : ‖(p : ℂ)‖ = p := by
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp0]
  calc
    ‖z‖ ≤ ‖z - (p : ℂ)‖ + ‖(p : ℂ)‖ := by
      simpa only [sub_add_cancel] using norm_add_le (z - (p : ℂ)) (p : ℂ)
    _ ≤ p * (clusterAnalyticityRatio d zeta - 1) / 2 + p := by
      rw [hnormp]
      gcongr
      exact hdist.le.trans hrle
    _ ≤ p * clusterAnalyticityRatio d zeta := by
      have hR0 : 0 ≤ clusterAnalyticityRatio d zeta := (Real.exp_pos _).le
      nlinarith

theorem norm_one_sub_le_mul_ratio_of_mem_analyticityBall
    {d : ℕ} {p zeta : ℝ} (hp1 : p ≤ 1)
    (hR : 1 ≤ clusterAnalyticityRatio d zeta) {z : ℂ}
    (hz : z ∈ Metric.ball (p : ℂ) (clusterAnalyticityRadius d p zeta)) :
    ‖1 - z‖ ≤ (1 - p) * clusterAnalyticityRatio d zeta := by
  have hdist : ‖z - (p : ℂ)‖ < clusterAnalyticityRadius d p zeta := by
    simpa [dist_eq_norm] using Metric.mem_ball.mp hz
  have hrle : clusterAnalyticityRadius d p zeta ≤
      (1 - p) * (clusterAnalyticityRatio d zeta - 1) / 2 := by
    unfold clusterAnalyticityRadius
    exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  have hnormq : ‖((1 - p : ℝ) : ℂ)‖ = 1 - p := by
    rw [show ((1 - p : ℝ) : ℂ) = (1 : ℂ) - (p : ℂ) by norm_cast]
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real]
    simp [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hp1)]
  have hdecomp : (1 - z) = ((1 - p : ℝ) : ℂ) - (z - (p : ℂ)) := by
    push_cast
    ring
  rw [hdecomp]
  calc
    ‖((1 - p : ℝ) : ℂ) - (z - (p : ℂ))‖ ≤
        ‖((1 - p : ℝ) : ℂ)‖ + ‖z - (p : ℂ)‖ := norm_sub_le _ _
    _ ≤ (1 - p) + (1 - p) * (clusterAnalyticityRatio d zeta - 1) / 2 := by
      rw [hnormq]
      gcongr
      exact hdist.le.trans hrle
    _ ≤ (1 - p) * clusterAnalyticityRatio d zeta := by
      have hR0 : 0 ≤ clusterAnalyticityRatio d zeta := (Real.exp_pos _).le
      nlinarith

theorem clusterAnalyticity_ratio_rate_identity
    {d n : ℕ} (hd : 0 < d) (zeta : ℝ) :
    clusterAnalyticityRatio d zeta ^ (3 * d * n) *
        Real.exp (-(n : ℝ) * zeta) =
      Real.exp (-zeta / 2) ^ n := by
  rw [show 3 * d * n = (3 * d) * n by ring, pow_mul]
  have hexp : Real.exp (-(n : ℝ) * zeta) = Real.exp (-zeta) ^ n := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hexp, ← mul_pow, clusterAnalyticity_geometricBase_eq hd]

theorem norm_complexClusterWeightLevel_le_interiorRate
    {d n : ℕ} (hd : 2 ≤ d) (p : I)
    (hp0 : 0 < (p : ℝ)) (hp : (p : ℝ) < cubicCriticalProbability d)
    {z : ℂ}
    (hz : z ∈ Metric.ball ((p : ℝ) : ℂ)
      (clusterAnalyticityRadius d p (clusterSizeDecayRate d p))) :
    ‖∑ A : CubicBondAnimal d n, complexAnimalWeight A z‖ ≤
      (p : ℝ)⁻¹ * (1 - (p : ℝ)) ^ 2 * (n : ℝ) *
        Real.exp (-clusterSizeDecayRate d p / 2) ^ n := by
  let zeta := clusterSizeDecayRate d p
  let R := clusterAnalyticityRatio d zeta
  let K := (p : ℝ)⁻¹ * (1 - (p : ℝ)) ^ 2
  have hp1 : (p : ℝ) < 1 := hp.trans (cubicCriticalProbability_pos_lt_one hd).2
  have hzeta : 0 < zeta := clusterSizeDecayRate_pos_of_lt_critical d hd p hp0 hp
  have hR : 1 ≤ R := (clusterAnalyticityRatio_one_lt (Nat.zero_lt_of_lt hd) hzeta).le
  have hnormz : ‖z‖ ≤ (p : ℝ) * R :=
    norm_le_mul_ratio_of_mem_analyticityBall hp0.le hR hz
  have hnormq : ‖1 - z‖ ≤ (1 - (p : ℝ)) * R :=
    norm_one_sub_le_mul_ratio_of_mem_analyticityBall hp1.le hR hz
  by_cases hn : n = 0
  · subst n
    have hsum0 : (∑ A : CubicBondAnimal d 0, complexAnimalWeight A z) = 0 := by
      apply Finset.sum_eq_zero
      intro A _hA
      have := A.vertices_card_pos
      omega
    rw [hsum0, norm_zero]
    norm_num
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hprob := finiteClusterSizeProbability_le_rate d p
      (Nat.zero_lt_of_lt hd) hp0 hp1 hnpos
    have hK : 0 ≤ K := mul_nonneg (inv_nonneg.mpr hp0.le) (sq_nonneg _)
    calc
      ‖∑ A : CubicBondAnimal d n, complexAnimalWeight A z‖ ≤
          R ^ (3 * d * n) * finiteClusterSizeProbability d p n :=
        norm_complexClusterWeightLevel_le_ratio p hR hnormz hnormq
      _ ≤ R ^ (3 * d * n) *
          ((n : ℝ) * K * Real.exp (-(n : ℝ) * zeta)) := by
        gcongr
        simpa only [K, zeta, mul_assoc] using hprob
      _ = K * (n : ℝ) * Real.exp (-zeta / 2) ^ n := by
        rw [← clusterAnalyticity_ratio_rate_identity (Nat.zero_lt_of_lt hd) zeta]
        ring

theorem norm_complexClusterDensityLevel_le_interiorRate
    {d n : ℕ} (hd : 2 ≤ d) (p : I)
    (hp0 : 0 < (p : ℝ)) (hp : (p : ℝ) < cubicCriticalProbability d)
    {z : ℂ}
    (hz : z ∈ Metric.ball ((p : ℝ) : ℂ)
      (clusterAnalyticityRadius d p (clusterSizeDecayRate d p))) :
    ‖complexClusterDensityLevel d n z‖ ≤
      (p : ℝ)⁻¹ * (1 - (p : ℝ)) ^ 2 * (n : ℝ) *
        Real.exp (-clusterSizeDecayRate d p / 2) ^ n := by
  by_cases hn : n = 0
  · subst n
    simp [complexClusterDensityLevel_zero]
  · have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hinv : ‖(1 / (n : ℂ))‖ ≤ 1 := by
      rw [norm_div, norm_one, norm_natCast]
      simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hnreal
    rw [complexClusterDensityLevel, norm_mul]
    calc
      ‖(1 / (n : ℂ))‖ * ‖∑ A : CubicBondAnimal d n, complexAnimalWeight A z‖ ≤
          1 * ((p : ℝ)⁻¹ * (1 - (p : ℝ)) ^ 2 * (n : ℝ) *
            Real.exp (-clusterSizeDecayRate d p / 2) ^ n) := by
        gcongr
        exact norm_complexClusterWeightLevel_le_interiorRate hd p hp0 hp hz
      _ = _ := one_mul _

theorem norm_complexSusceptibilityLevel_le_interiorRate
    {d n : ℕ} (hd : 2 ≤ d) (p : I)
    (hp0 : 0 < (p : ℝ)) (hp : (p : ℝ) < cubicCriticalProbability d)
    {z : ℂ}
    (hz : z ∈ Metric.ball ((p : ℝ) : ℂ)
      (clusterAnalyticityRadius d p (clusterSizeDecayRate d p))) :
    ‖complexSusceptibilityLevel d n z‖ ≤
      (p : ℝ)⁻¹ * (1 - (p : ℝ)) ^ 2 * (n : ℝ) ^ 2 *
        Real.exp (-clusterSizeDecayRate d p / 2) ^ n := by
  rw [complexSusceptibilityLevel, norm_mul, norm_natCast]
  have h := norm_complexClusterWeightLevel_le_interiorRate (n := n) hd p hp0 hp hz
  calc
    (n : ℝ) * ‖∑ A : CubicBondAnimal d n, complexAnimalWeight A z‖ ≤
        (n : ℝ) * ((p : ℝ)⁻¹ * (1 - (p : ℝ)) ^ 2 * (n : ℝ) *
          Real.exp (-clusterSizeDecayRate d p / 2) ^ n) := by
      exact mul_le_mul_of_nonneg_left h (Nat.cast_nonneg n)
    _ = _ := by ring

theorem complexClusterDensitySeries_differentiableOn_interior
    {d : ℕ} (hd : 2 ≤ d) (p : I)
    (hp0 : 0 < (p : ℝ)) (hp : (p : ℝ) < cubicCriticalProbability d) :
    DifferentiableOn ℂ (complexClusterDensitySeries d)
      (Metric.ball ((p : ℝ) : ℂ)
        (clusterAnalyticityRadius d p (clusterSizeDecayRate d p))) := by
  let zeta := clusterSizeDecayRate d p
  let r := Real.exp (-zeta / 2)
  let K := (p : ℝ)⁻¹ * (1 - (p : ℝ)) ^ 2
  let u : ℕ → ℝ := fun n ↦ K * (n : ℝ) * r ^ n
  have hzeta : 0 < zeta := clusterSizeDecayRate_pos_of_lt_critical d hd p hp0 hp
  have hr : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_lt_one_iff]
    linarith
  have hgeom : Summable (fun n : ℕ ↦ (n : ℝ) * r ^ n) := by
    simpa using (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hr)
  have hu : Summable u := by
    convert hgeom.mul_left K using 1
    ext n
    dsimp [u]
    ring
  apply Complex.differentiableOn_tsum_of_summable_norm hu
  · intro n
    exact (complexClusterDensityLevel_differentiable d n).differentiableOn
  · exact Metric.isOpen_ball
  · intro n z hz
    exact norm_complexClusterDensityLevel_le_interiorRate hd p hp0 hp hz

theorem complexSusceptibilitySeries_differentiableOn_interior
    {d : ℕ} (hd : 2 ≤ d) (p : I)
    (hp0 : 0 < (p : ℝ)) (hp : (p : ℝ) < cubicCriticalProbability d) :
    DifferentiableOn ℂ (complexSusceptibilitySeries d)
      (Metric.ball ((p : ℝ) : ℂ)
        (clusterAnalyticityRadius d p (clusterSizeDecayRate d p))) := by
  let zeta := clusterSizeDecayRate d p
  let r := Real.exp (-zeta / 2)
  let K := (p : ℝ)⁻¹ * (1 - (p : ℝ)) ^ 2
  let u : ℕ → ℝ := fun n ↦ K * (n : ℝ) ^ 2 * r ^ n
  have hzeta : 0 < zeta := clusterSizeDecayRate_pos_of_lt_critical d hd p hp0 hp
  have hr : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_lt_one_iff]
    linarith
  have hgeom : Summable (fun n : ℕ ↦ (n : ℝ) ^ 2 * r ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 2 hr
  have hu : Summable u := by
    convert hgeom.mul_left K using 1
    ext n
    dsimp [u]
    ring
  apply Complex.differentiableOn_tsum_of_summable_norm hu
  · intro n
    exact (complexSusceptibilityLevel_differentiable d n).differentiableOn
  · exact Metric.isOpen_ball
  · intro n z hz
    exact norm_complexSusceptibilityLevel_le_interiorRate hd p hp0 hp hz

/-! ### Restriction to the physical real parameter -/

theorem complexClusterDensitySeries_ofReal
    {d : ℕ} (hd : 0 < d) (p : ℝ) :
    complexClusterDensitySeries d (p : ℂ) = concreteClusterDensitySeries d p := by
  unfold complexClusterDensitySeries concreteClusterDensitySeries
  calc
    (∑' n : ℕ, complexClusterDensityLevel d n (p : ℂ)) =
        ∑' n : ℕ, (concreteClusterDensityLevel d n p : ℂ) := by
      apply tsum_congr
      intro n
      exact complexClusterDensityLevel_ofReal hd n p
    _ = (∑' n : ℕ, concreteClusterDensityLevel d n p : ℝ) :=
      (Complex.ofReal_tsum _).symm

theorem complexSusceptibilitySeries_ofReal (d : ℕ) (p : ℝ) :
    complexSusceptibilitySeries d (p : ℂ) = concreteSusceptibilitySeries d p := by
  unfold complexSusceptibilitySeries concreteSusceptibilitySeries
  calc
    (∑' n : ℕ, complexSusceptibilityLevel d n (p : ℂ)) =
        ∑' n : ℕ, (concreteSusceptibilityLevel d n p : ℂ) := by
      apply tsum_congr
      intro n
      exact complexSusceptibilityLevel_ofReal_real d n p
    _ = (∑' n : ℕ, concreteSusceptibilityLevel d n p : ℝ) :=
      (Complex.ofReal_tsum _).symm

theorem concreteSusceptibilitySeries_eq_finiteSusceptibility_toReal
    (d : ℕ) (p : I) :
    concreteSusceptibilitySeries d p = (finiteSusceptibility d p).toReal := by
  rw [finiteSusceptibility_toReal_eq_series]
  unfold concreteSusceptibilitySeries concreteSusceptibilityLevel
  apply tsum_congr
  intro n
  rw [finiteClusterSizeProbability_eq_sum_animals]

theorem concreteSusceptibilitySeries_eq_susceptibility_toReal_of_lt_critical
    (d : ℕ) (p : I) (hp : (p : ℝ) < cubicCriticalProbability d) :
    concreteSusceptibilitySeries d p = (susceptibility d p).toReal := by
  rw [concreteSusceptibilitySeries_eq_finiteSusceptibility_toReal,
    finiteSusceptibility_eq_susceptibility_of_theta_eq_zero d p
      (theta_eq_zero_of_lt_criticalProbability hp)]

/-- Grimmett, Theorem 6.108, cluster-density half.  `AnalyticOnNhd` at zero supplies a genuine
two-sided real neighborhood, furnished by the complex animal series. -/
theorem concreteClusterDensitySeries_analyticOnNhd_belowCritical
    (d : ℕ) (hd : 2 ≤ d) :
    AnalyticOnNhd ℝ (concreteClusterDensitySeries d)
      (Ico (0 : ℝ) (cubicCriticalProbability d)) := by
  intro p hp
  by_cases hpzero : p = 0
  · subst p
    have hc := complexClusterDensitySeries_analyticAt_zero (d := d) (Nat.zero_lt_of_lt hd)
    simpa only [complexClusterDensitySeries_ofReal (Nat.zero_lt_of_lt hd),
      Complex.ofReal_re] using hc.re_ofReal
  · have hp0 : 0 < p := lt_of_le_of_ne hp.1 (Ne.symm hpzero)
    have hp1 : p ≤ 1 :=
      (hp.2.trans (cubicCriticalProbability_pos_lt_one hd).2).le
    let pI : I := ⟨p, hp0.le, hp1⟩
    have hzeta : 0 < clusterSizeDecayRate d pI :=
      clusterSizeDecayRate_pos_of_lt_critical d hd pI hp0 (by simpa [pI] using hp.2)
    have hradius : 0 < clusterAnalyticityRadius d p
        (clusterSizeDecayRate d pI) :=
      clusterAnalyticityRadius_pos (Nat.zero_lt_of_lt hd) hp0
        (hp.2.trans (cubicCriticalProbability_pos_lt_one hd).2) hzeta
    have hdiff := complexClusterDensitySeries_differentiableOn_interior
      hd pI hp0 (by simpa [pI] using hp.2)
    have hc : AnalyticAt ℂ (complexClusterDensitySeries d) (p : ℂ) :=
      (hdiff.analyticOnNhd Metric.isOpen_ball) _ (Metric.mem_ball_self hradius)
    simpa only [complexClusterDensitySeries_ofReal (Nat.zero_lt_of_lt hd),
      Complex.ofReal_re] using hc.re_ofReal

/-- Grimmett, Theorem 6.108, susceptibility half. -/
theorem concreteSusceptibilitySeries_analyticOnNhd_belowCritical
    (d : ℕ) (hd : 2 ≤ d) :
    AnalyticOnNhd ℝ (concreteSusceptibilitySeries d)
      (Ico (0 : ℝ) (cubicCriticalProbability d)) := by
  intro p hp
  by_cases hpzero : p = 0
  · subst p
    have hc := complexSusceptibilitySeries_analyticAt_zero (d := d) (Nat.zero_lt_of_lt hd)
    simpa only [complexSusceptibilitySeries_ofReal, Complex.ofReal_re] using hc.re_ofReal
  · have hp0 : 0 < p := lt_of_le_of_ne hp.1 (Ne.symm hpzero)
    have hp1 : p ≤ 1 :=
      (hp.2.trans (cubicCriticalProbability_pos_lt_one hd).2).le
    let pI : I := ⟨p, hp0.le, hp1⟩
    have hzeta : 0 < clusterSizeDecayRate d pI :=
      clusterSizeDecayRate_pos_of_lt_critical d hd pI hp0 (by simpa [pI] using hp.2)
    have hradius : 0 < clusterAnalyticityRadius d p
        (clusterSizeDecayRate d pI) :=
      clusterAnalyticityRadius_pos (Nat.zero_lt_of_lt hd) hp0
        (hp.2.trans (cubicCriticalProbability_pos_lt_one hd).2) hzeta
    have hdiff := complexSusceptibilitySeries_differentiableOn_interior
      hd pI hp0 (by simpa [pI] using hp.2)
    have hc : AnalyticAt ℂ (complexSusceptibilitySeries d) (p : ℂ) :=
      (hdiff.analyticOnNhd Metric.isOpen_ball) _ (Metric.mem_ball_self hradius)
    simpa only [complexSusceptibilitySeries_ofReal, Complex.ofReal_re] using hc.re_ofReal

/-- **Grimmett, Theorem 6.108.**  Below the critical point, the concrete animal expansions for
the open-cluster density and susceptibility are real analytic; on physical parameters they
equal `openClustersPerVertex` and `susceptibility.toReal`, respectively. -/
theorem clusterDensity_and_susceptibility_analytic_belowCritical
    (d : ℕ) (hd : 2 ≤ d) :
    AnalyticOnNhd ℝ (concreteClusterDensitySeries d)
        (Ico (0 : ℝ) (cubicCriticalProbability d)) ∧
      AnalyticOnNhd ℝ (concreteSusceptibilitySeries d)
        (Ico (0 : ℝ) (cubicCriticalProbability d)) :=
  ⟨concreteClusterDensitySeries_analyticOnNhd_belowCritical d hd,
    concreteSusceptibilitySeries_analyticOnNhd_belowCritical d hd⟩

#print axioms complexClusterDensitySeries_analyticAt_zero
#print axioms complexSusceptibilitySeries_analyticAt_zero
#print axioms concreteClusterDensitySeries_analyticOnNhd_belowCritical
#print axioms concreteSusceptibilitySeries_analyticOnNhd_belowCritical
#print axioms clusterDensity_and_susceptibility_analytic_belowCritical

end

end Percolation
