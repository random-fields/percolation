import Percolation.Critical.SupercriticalStripFromSlab
import Percolation.Critical.SupercriticalFiniteClusterTail
import Percolation.Critical.SupercriticalSmoothness

/-!
# Compact-uniform supercritical finite-cluster tails

Grimmett's equation (8.91) requires one stretched-exponential constant on every compact
subinterval of `(p_c,1)`.  The proof below keeps the strip scale and strip survival probability
fixed at the left endpoint, so the resulting constant is genuinely uniform in `p`.
-/

namespace Percolation

open MeasureTheory Set
open scoped unitInterval

/-- A uniform exponential estimate for the reference hyperplane event, together with a uniform
strict bound on finite-cluster probability, implies the compact-uniform form of (8.91). -/
theorem exists_uniformFiniteClusterSizeTailStretchedExponential_of_hyperplane_bound
    {d : ℕ} (hd : 2 ≤ d) {a b gamma q : ℝ}
    (hgamma : 0 < gamma) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hG : ∀ p : I, a ≤ (p : ℝ) ∧ (p : ℝ) ≤ b → ∀ n : ℕ,
      (bernoulliBondMeasure d p).real
          (finiteClusterHitsHyperplaneEvent d (Nat.zero_lt_of_lt hd) n) ≤
        Real.exp (-(gamma * n)))
    (hq : ∀ p : I, a ≤ (p : ℝ) ∧ (p : ℝ) ≤ b →
      finiteClusterSizeTail d p 1 ≤ q) :
    ∃ eta : ℝ, 0 < eta ∧
      UniformFiniteClusterSizeTailStretchedExponential d a b eta := by
  by_cases hqzero : q = 0
  · refine ⟨1, by norm_num, ?_⟩
    intro p hp n
    by_cases hn0 : n = 0
    · subst n
      have hdR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
      have hle : finiteClusterSizeTail d p 0 ≤ 1 := by
        rw [finiteClusterSizeTail_eq_measure_inter]
        exact measureReal_le_one
      simpa [Real.zero_rpow (inv_ne_zero hdR.ne')] using hle
    · have htail := finiteClusterSizeTail_antitone d p
        (Nat.one_le_iff_ne_zero.mpr hn0)
      have hzero : finiteClusterSizeTail d p n ≤ 0 := htail.trans <| by
        simpa [hqzero] using hq p hp
      exact hzero.trans (Real.exp_pos _).le
  · have hqpos : 0 < q := lt_of_le_of_ne hq0 (Ne.symm hqzero)
    let C : ℝ := 2 * d
    let K : ℝ := max 6 (12 * Real.log C / gamma)
    let eta₁ := gamma / 12
    let eta₂ := -Real.log q / K
    let eta := min eta₁ eta₂
    have hC : 0 < C := by dsimp [C]; positivity
    have hK6 : 6 ≤ K := le_max_left _ _
    have hK0 : 0 < K := (by norm_num : (0 : ℝ) < 6).trans_le hK6
    have heta₁ : 0 < eta₁ := by dsimp [eta₁]; positivity
    have hlogq : Real.log q < 0 := Real.log_neg hqpos hq1
    have heta₂ : 0 < eta₂ := div_pos (neg_pos.mpr hlogq) hK0
    have heta : 0 < eta := lt_min heta₁ heta₂
    refine ⟨eta, heta, ?_⟩
    intro p hp n
    let root : ℝ := (n : ℝ) ^ ((d : ℝ)⁻¹)
    have hroot0 : 0 ≤ root := Real.rpow_nonneg (Nat.cast_nonneg n) _
    by_cases hn0 : n = 0
    · subst n
      have hdR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
      have hle : finiteClusterSizeTail d p 0 ≤ 1 := by
        rw [finiteClusterSizeTail_eq_measure_inter]
        exact measureReal_le_one
      simpa [root, Real.zero_rpow (inv_ne_zero hdR.ne')] using hle
    by_cases hrootK : root < K
    · have htail : finiteClusterSizeTail d p n ≤ q :=
        (finiteClusterSizeTail_antitone d p
          (Nat.one_le_iff_ne_zero.mpr hn0)).trans (hq p hp)
      have hetaLe : eta ≤ eta₂ := min_le_right _ _
      have hprod : eta * root ≤ -Real.log q := by
        calc
          eta * root ≤ eta * K :=
            mul_le_mul_of_nonneg_left hrootK.le heta.le
          _ ≤ eta₂ * K := mul_le_mul_of_nonneg_right hetaLe hK0.le
          _ = -Real.log q := by dsimp [eta₂]; field_simp
      calc
        finiteClusterSizeTail d p n ≤ q := htail
        _ = Real.exp (Real.log q) := (Real.exp_log hqpos).symm
        _ ≤ Real.exp (-eta * root) := Real.exp_le_exp.mpr (by linarith)
    · have hrootGe : K ≤ root := le_of_not_gt hrootK
      have hroot6 : 6 ≤ root := hK6.trans hrootGe
      have hmReal : root / 6 ≤ (clusterTailRadius d n : ℝ) :=
        root_div_six_le_clusterTailRadius hroot6
      have hm : 0 < clusterTailRadius d n := by
        have hrootPos : (0 : ℝ) < root := (by norm_num : (0 : ℝ) < 6).trans_le hroot6
        exact_mod_cast (lt_of_lt_of_le (div_pos hrootPos (by norm_num)) hmReal)
      have htail := finiteClusterSizeTail_le_finiteBoxRadius_clusterTailRadius
        (d := d) (n := n) (by omega) p hm
      have hradius : finiteBoxRadiusProbability d p (clusterTailRadius d n) ≤
          C * Real.exp (-(gamma * clusterTailRadius d n)) := by
        have hGn : (bernoulliBondMeasure d p).real
            (finiteClusterHitsHyperplaneEvent d (Nat.zero_lt_of_lt hd)
              (clusterTailRadius d n)) ≤
            Real.exp (-((clusterTailRadius d n : ℝ) * gamma)) := by
          simpa [mul_comm] using hG p hp (clusterTailRadius d n)
        simpa [C, mul_comm] using
          finiteBoxRadiusProbability_le_two_mul_d_mul_exp_of_hyperplane_bound
            (Nat.zero_lt_of_lt hd) p hGn
      have hlogC : Real.log C ≤ gamma * root / 12 := by
        have hKlog : 12 * Real.log C / gamma ≤ K := le_max_right _ _
        have hlogRoot : 12 * Real.log C / gamma ≤ root := hKlog.trans hrootGe
        rw [div_le_iff₀ hgamma] at hlogRoot
        nlinarith
      have hmGamma : gamma * root / 6 ≤ gamma * clusterTailRadius d n := by
        nlinarith [mul_le_mul_of_nonneg_left hmReal hgamma.le]
      have hetaLe : eta ≤ eta₁ := min_le_left _ _
      have hexponent : Real.log C - gamma * clusterTailRadius d n ≤ -eta * root := by
        have hetaRoot : eta * root ≤ gamma * root / 12 := by
          dsimp [eta₁] at hetaLe
          calc
            eta * root ≤ (gamma / 12) * root :=
              mul_le_mul_of_nonneg_right hetaLe hroot0
            _ = gamma * root / 12 := by ring
        nlinarith
      calc
        finiteClusterSizeTail d p n ≤
            finiteBoxRadiusProbability d p (clusterTailRadius d n) := htail
        _ ≤ C * Real.exp (-(gamma * clusterTailRadius d n)) := hradius
        _ = Real.exp (Real.log C - gamma * clusterTailRadius d n) := by
          rw [sub_eq_add_neg, Real.exp_add, Real.exp_log hC]
        _ ≤ Real.exp (-eta * root) := Real.exp_le_exp.mpr hexponent

/-- Compact-uniform (8.91) from one reference strip that is supercritical at the left endpoint. -/
theorem exists_uniformFiniteClusterSizeTailStretchedExponential_of_coordinateStrip
    {d : ℕ} (hd : 2 ≤ d) {a b : ℝ} (ha0 : 0 < a) (hab : a ≤ b) (hb1 : b < 1)
    {k : ℕ} (hk : 0 < k)
    (hcrit : regionCriticalProbability d
      (cubicCoordinateStrip d ⟨0, Nat.zero_lt_of_lt hd⟩ 0 k) < a) :
    ∃ eta : ℝ, 0 < eta ∧
      UniformFiniteClusterSizeTailStretchedExponential d a b eta := by
  let aI : I := ⟨a, ha0.le, hab.trans hb1.le⟩
  let A := cubicCoordinateStrip d ⟨0, Nat.zero_lt_of_lt hd⟩ 0 k
  let theta0 := regionThetaFrom d A aI cubicOrigin
  have hcritI : regionCriticalProbability d A < (aI : ℝ) := by simpa [A, aI] using hcrit
  have htheta0 : 0 < theta0 := by
    dsimp [theta0]
    exact regionThetaFrom_coordinateStrip_pos_of_critical_lt
      (Nat.zero_lt_of_lt hd) aI hk hcritI
  let q := 1 - theta0
  have htheta01 : theta0 ≤ 1 := measureReal_le_one
  have hq0 : 0 ≤ q := by dsimp [q]; linarith
  have hq1 : q < 1 := by dsimp [q]; linarith
  let gamma := coordinateStripExponentialRate q k
  have hgamma : 0 < gamma := coordinateStripExponentialRate_pos hq0 hq1 hk
  apply exists_uniformFiniteClusterSizeTailStretchedExponential_of_hyperplane_bound
    hd hgamma hq0 hq1
  · intro p hp n
    have hap : aI ≤ p := by
      apply Subtype.mk_le_mk.mpr
      simpa [aI] using hp.1
    have htheta : theta0 ≤ regionThetaFrom d A p cubicOrigin :=
      regionThetaFrom_mono d A cubicOrigin hap
    simpa [gamma, q] using
      (finiteClusterHitsHyperplane_probability_le_exp_of_stripTheta_ge
        (Nat.zero_lt_of_lt hd) p hk htheta0 (by simpa [A] using htheta)).2 n
  · intro p hp
    have hap : aI ≤ p := by
      apply Subtype.mk_le_mk.mpr
      simpa [aI] using hp.1
    have htheta : theta0 ≤ regionThetaFrom d A p cubicOrigin :=
      regionThetaFrom_mono d A cubicOrigin hap
    calc
      finiteClusterSizeTail d p 1 = 1 - theta d p :=
        finiteClusterSizeTail_one_eq_one_sub_theta d p
      _ ≤ 1 - regionThetaFrom d A p cubicOrigin := by
        apply sub_le_sub_left
        rw [← thetaFrom_origin d p, ← regionThetaFrom_univ]
        exact regionThetaFrom_mono_region (Set.subset_univ A) p cubicOrigin
      _ ≤ q := by dsimp [q]; linarith

/-- The compact-uniform source estimate (8.91), conditional exactly on Chapter 7 slab
approximation. -/
theorem exists_uniformFiniteClusterSizeTailStretchedExponential_of_slabCriticalApproximation
    {d : ℕ} (hd : 3 ≤ d) (happrox : SlabCriticalApproximation d)
    {a b : ℝ} (hpa : cubicCriticalProbability d < a)
    (hab : a ≤ b) (hb1 : b < 1) :
    ∃ eta : ℝ, 0 < eta ∧
      UniformFiniteClusterSizeTailStretchedExponential d a b eta := by
  let aI : I := ⟨a,
    (cubicCriticalProbability_pos_lt_one (by omega : 2 ≤ d)).1.le.trans hpa.le,
    hab.trans hb1.le⟩
  have hpcI : cubicCriticalProbability d < (aI : ℝ) := by simpa [aI] using hpa
  obtain ⟨k, hk, hcrit⟩ :=
    exists_coordinateStrip_critical_lt_of_slabCriticalApproximation hd happrox hpcI
  exact exists_uniformFiniteClusterSizeTailStretchedExponential_of_coordinateStrip
    (by omega) ((cubicCriticalProbability_pos_lt_one (by omega : 2 ≤ d)).1.trans hpa)
    hab hb1 hk (by simpa [aI] using hcrit)

/-- Interior part of Theorem 8.92 with its compact-uniform probabilistic input now discharged
from the Chapter 7 slab approximation premise. -/
theorem theta_finiteSusceptibility_clusterDensity_contDiffOn_interior_of_slabCriticalApproximation
    {d : ℕ} (hd : 3 ≤ d) (happrox : SlabCriticalApproximation d)
    {a b : ℝ} (hpa : cubicCriticalProbability d < a)
    (hab : a < b) (hb1 : b < 1) :
    ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (thetaAnimalSeries d) (Set.Ioo a b) ∧
    ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (concreteSusceptibilitySeries d) (Set.Ioo a b) ∧
    ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (concreteClusterDensitySeries d) (Set.Ioo a b) := by
  obtain ⟨eta, heta, htail⟩ :=
    exists_uniformFiniteClusterSizeTailStretchedExponential_of_slabCriticalApproximation
      hd happrox hpa hab.le hb1
  exact theta_finiteSusceptibility_clusterDensity_contDiffOn_interior
    (by omega) ((cubicCriticalProbability_pos_lt_one (by omega : 2 ≤ d)).1.trans hpa)
    hab hb1 heta htail

end Percolation
