import Percolation
import Percolation.Critical.ClusterSizeRate

namespace Review.Chapter06

open Percolation MeasureTheory Filter Set Topology
open scoped BigOperators ENNReal unitInterval Topology

theorem source_6_1 (d : ℕ) (hd : 2 ≤ d) (p : I) (hχ : susceptibility d p < ⊤) :
    ∃ sigma : ℝ, 0 < sigma ∧ ∀ n : ℕ, boxRadiusTail d p n ≤ Real.exp (-(n : ℝ) * sigma) := by
  simpa [mul_comm] using boxRadiusTail_exponential_decay_of_susceptibility_lt_top d hd p hχ

theorem source_6_10_rate (d : ℕ) (hd : 2 ≤ d) (p : I) (hp : 0 < (p : ℝ)) :
    Tendsto (fun n : ℕ ↦ -Real.log (boxRadiusTail d p n) / (n : ℝ)) atTop
      (𝓝 (boxRadiusDecayRate d p)) := boxRadiusTail_logRate_tendsto d (by omega) p hp

theorem source_6_10_two_sided_constants (d : ℕ) (hd : 2 ≤ d) :
    ∃ rho sigma : ℝ, 0 < rho ∧ 0 < sigma ∧ ∀ p : I, 0 < (p : ℝ) → ∀ n : ℕ, 1 ≤ n →
      rho / (n : ℝ) ^ (d - 1) * Real.exp (-(n : ℝ) * boxRadiusDecayRate d p) ≤ boxRadiusTail d p n ∧
        boxRadiusTail d p n ≤ sigma * (n : ℝ) ^ (d - 1) * Real.exp (-(n : ℝ) * boxRadiusDecayRate d p) := by
  obtain ⟨rho, sigma, hrho, hsigma, h⟩ := boxRadiusTail_twoSided_decay d (by omega)
  exact ⟨rho, sigma, hrho, hsigma, fun p hp n hn ↦ h p hp n (by omega)⟩

theorem source_6_14_continuous (d : ℕ) (hd : 2 ≤ d) :
    ContinuousOn (boxRadiusDecayRate d) {p : I | 0 < (p : ℝ)} :=
  boxRadiusDecayRate_continuousOn d (by omega)

theorem source_6_14_nonincreasing (d : ℕ) (hd : 2 ≤ d) :
    AntitoneOn (boxRadiusDecayRate d) {p : I | 0 < (p : ℝ)} :=
  boxRadiusDecayRate_antitoneOn_pos d (by omega)

theorem source_6_14_strictly_decreasing (d : ℕ) (hd : 2 ≤ d) :
    StrictAntiOn (boxRadiusDecayRate d) {p : I | 0 < (p : ℝ) ∧ (p : ℝ) < cubicCriticalProbability d} :=
  boxRadiusDecayRate_strictAntiOn_subcritical d hd

theorem source_6_14_positive_below_critical (d : ℕ) (hd : 2 ≤ d) (p : I)
    (hp0 : 0 < (p : ℝ)) (hpc : (p : ℝ) < cubicCriticalProbability d) :
    0 < boxRadiusDecayRate d p := boxRadiusDecayRate_pos_of_lt_critical d hd p hp0 hpc

theorem source_6_14_rate_tends_to_infinity_at_zero (d : ℕ) (hd : 2 ≤ d) :
    Tendsto (clampedBoxRadiusDecayRate d) (𝓝[>] (0 : ℝ)) atTop :=
  boxRadiusDecayRate_tendsto_top_at_zero d (by omega)

theorem source_6_14_rate_at_critical (d : ℕ) (hd : 2 ≤ d) :
    boxRadiusDecayRate d (cubicCriticalProbabilityUnit d hd) = 0 :=
  boxRadiusDecayRate_critical_eq_zero d hd

theorem source_6_40_log_ratio_comparison (d : ℕ) (hd : 2 ≤ d) (a b : I)
    (ha : 0 < (a : ℝ)) (hab : (a : ℝ) ≤ (b : ℝ)) (hb : (b : ℝ) < 1) :
    boxRadiusDecayRate d b * (Real.log (1 / (a : ℝ)) / Real.log (1 / (b : ℝ))) ≤ boxRadiusDecayRate d a :=
  boxRadiusDecayRate_log_ratio_comparison d (by omega) ha hab hb

theorem source_6_44_axis_rate (d : ℕ) (hd : 2 ≤ d) (p : I) (hp : 0 < (p : ℝ)) :
    Tendsto (fun n : ℕ ↦ -Real.log (twoPointConnectivity d p cubicOrigin (cubicAxisVertex d n)) / (n : ℝ))
      atTop (𝓝 (boxRadiusDecayRate d p)) :=
  twoPointConnectivity_axis_logRate_tendsto (d := d) (p := p) (by omega) hp

theorem source_6_44_axis_two_sided (d : ℕ) (hd : 2 ≤ d) :
    ∃ zeta : ℝ, 0 < zeta ∧ ∀ p : I, 0 < (p : ℝ) → ∀ n : ℕ, 1 ≤ n →
      zeta * (p : ℝ) / (n : ℝ) ^ (4 * (d - 1)) * Real.exp (-(n : ℝ) * boxRadiusDecayRate d p) ≤
          twoPointConnectivity d p cubicOrigin (cubicAxisVertex d n) ∧
        twoPointConnectivity d p cubicOrigin (cubicAxisVertex d n) ≤ Real.exp (-(n : ℝ) * boxRadiusDecayRate d p) := by
  obtain ⟨zeta, hzeta, h⟩ := twoPointConnectivity_axis_twoSided_decay d (by omega)
  exact ⟨zeta, hzeta, fun p hp n hn ↦ h p hp n (by omega)⟩

theorem source_6_47_two_point_upper (d : ℕ) (hd : 2 ≤ d) (p : I) (hp : 0 < (p : ℝ)) (x : Cubic d) :
    twoPointConnectivity d p cubicOrigin x ≤ Real.exp (-(cubicLInfDist cubicOrigin x : ℝ) * boxRadiusDecayRate d p) :=
  twoPointConnectivity_le_exp_neg_lInfDist_mul_rate (by omega) hp x

theorem source_6_47_two_point_lower (d : ℕ) (hd : 2 ≤ d) :
    ∃ lambda : ℝ, 0 < lambda ∧ ∀ p : I, 0 < (p : ℝ) → ∀ x : Cubic d, x ≠ cubicOrigin →
      lambda * (p : ℝ) ^ (d * cubicL1Dist cubicOrigin x) / (cubicL1Dist cubicOrigin x : ℝ) ^ (4 * d * (d - 1)) *
          Real.exp (-(cubicL1Dist cubicOrigin x : ℝ) * boxRadiusDecayRate d p) ≤ twoPointConnectivity d p cubicOrigin x := by
  obtain ⟨lambda, hlambda, h⟩ := twoPointConnectivity_lower_decay d (by omega)
  exact ⟨lambda, hlambda, h⟩

theorem source_6_49_connectivity_bound (d : ℕ) (hd : 2 ≤ d) (p : I) (hp0 : 0 < (p : ℝ))
    (hpc : (p : ℝ) < cubicCriticalProbability d) (x : Cubic d) :
    twoPointConnectivity d p cubicOrigin x ≤ (1 - ((susceptibility d p).toReal)⁻¹) ^ cubicL1Dist cubicOrigin x :=
  twoPointConnectivity_le_one_sub_susceptibility_inv_pow_of_lt_critical hd hp0 hpc x

theorem source_6_49_correlation_length_le_susceptibility (d : ℕ) (hd : 2 ≤ d) (p : I)
    (hp0 : 0 < (p : ℝ)) (hpc : (p : ℝ) < cubicCriticalProbability d) :
    correlationLength d p ≤ susceptibility d p := correlationLength_le_susceptibility hd hp0 hpc

theorem source_6_49_susceptibility_diverges_at_critical (d : ℕ) (hd : 2 ≤ d) :
    Tendsto (susceptibility d) (𝓝[<] (cubicCriticalProbabilityUnit d hd)) (𝓝 ⊤) :=
  susceptibility_tendsto_top_at_critical d hd

theorem source_6_55_correlation_length_continuous (d : ℕ) (hd : 2 ≤ d) :
    ContinuousOn (correlationLength d) {p : I | 0 < (p : ℝ) ∧ (p : ℝ) < cubicCriticalProbability d} :=
  correlationLength_continuousOn_subcritical d hd

theorem source_6_55_correlation_length_strictly_increasing (d : ℕ) (hd : 2 ≤ d) :
    StrictMonoOn (correlationLength d) {p : I | 0 < (p : ℝ) ∧ (p : ℝ) < cubicCriticalProbability d} :=
  correlationLength_strictMonoOn_subcritical d hd

theorem source_6_55_correlation_length_tends_to_zero (d : ℕ) (hd : 2 ≤ d) :
    Tendsto (clampedCorrelationLength d) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
  correlationLength_tendsto_zero_at_zero d (by omega)

theorem source_6_56_correlation_length_at_critical (d : ℕ) (hd : 2 ≤ d) :
    correlationLength d (cubicCriticalProbabilityUnit d hd) = ⊤ := correlationLength_critical_eq_top d hd

theorem source_6_56_correlation_length_tends_to_infinity (d : ℕ) (hd : 2 ≤ d) :
    Tendsto (correlationLength d) (𝓝[<] (cubicCriticalProbabilityUnit d hd)) (𝓝 ⊤) :=
  correlationLength_tendsto_top_at_critical d hd

theorem source_6_75_corrected_exponential_tail (d : ℕ) (hd : 2 ≤ d) (p : I)
    (hp0 : 0 < (p : ℝ)) (hpc : (p : ℝ) < cubicCriticalProbability d) :
    ∃ lambda : ℝ, 0 < lambda ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → clusterSizeAtLeast d p n ≤ Real.exp (-(n : ℝ) * lambda) := by
  simpa [mul_comm] using clusterSizeAtLeast_exponential_decay_of_lt_critical d hd p hp0 hpc

theorem source_6_77_concrete_cluster_tail (d : ℕ) (hd : 2 ≤ d) (p : I) (hp0 : 0 < (p : ℝ))
    (hpc : (p : ℝ) < cubicCriticalProbability d) (n : ℕ)
    (hn : (susceptibility d p).toReal ^ 2 < (n : ℝ)) :
    clusterSizeAtLeast d p n ≤ 2 * Real.exp (-(1 / 2 : ℝ) * (n : ℝ) / (susceptibility d p).toReal ^ 2) :=
  clusterSizeAtLeast_le_two_exp_neg (by omega) hp0
    (susceptibility_lt_top_of_lt_critical d hd p hpc) n (by exact_mod_cast hn)

theorem source_6_78_exact_size_rate (d : ℕ) (hd : 2 ≤ d) (p : I) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    Tendsto (fun n : ℕ ↦ -Real.log (finiteClusterSizeProbability d p n) / (n : ℝ)) atTop
      (𝓝 (clusterSizeDecayRate d p)) := clusterSizeProbability_logRate_tendsto d p (by omega) hp0 hp1

theorem source_6_78_rate_nonnegative (d : ℕ) (hd : 2 ≤ d) (p : I) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    0 ≤ clusterSizeDecayRate d p := clusterSizeDecayRate_nonneg d p (by omega) hp0 hp1

theorem source_6_80_exact_size_upper_bound (d : ℕ) (hd : 2 ≤ d) (p : I) (hp0 : 0 < (p : ℝ))
    (hp1 : (p : ℝ) < 1) (n : ℕ) (hn : 1 ≤ n) :
    finiteClusterSizeProbability d p n ≤ ((1 - (p : ℝ)) ^ 2 / (p : ℝ)) * (n : ℝ) *
      Real.exp (-(n : ℝ) * clusterSizeDecayRate d p) := by
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
    finiteClusterSizeProbability_le_rate d p (by omega) hp0 hp1 (n := n) (by omega)

theorem source_6_78_rate_positive_below_critical (d : ℕ) (hd : 2 ≤ d) (p : I)
    (hp0 : 0 < (p : ℝ)) (hpc : (p : ℝ) < cubicCriticalProbability d) :
    0 < clusterSizeDecayRate d p := clusterSizeDecayRate_pos_of_lt_critical d hd p hp0 hpc

theorem source_6_82_finite_tail_rate (d : ℕ) (hd : 2 ≤ d) (p : I)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    Tendsto (fun n : ℕ ↦ -Real.log (finiteClusterSizeTail d p n) / (n : ℝ)) atTop
      (𝓝 (clusterSizeDecayRate d p)) := finiteClusterSizeTail_logRate_tendsto_all d (by omega) p hp0 hp1

theorem source_6_83_cluster_rate_le_radius_rate (d : ℕ) (hd : 2 ≤ d) (p : I)
    (hp0 : 0 < (p : ℝ)) (hpc : (p : ℝ) < cubicCriticalProbability d) :
    clusterSizeDecayRate d p ≤ boxRadiusDecayRate d p := clusterSizeDecayRate_le_boxRadiusDecayRate d hd p hp0 hpc

universe u
theorem source_6_87_finite_terminal_deletion {V : Type u} (G : SimpleGraph V) (hG : G.Connected)
    (W : Finset V) (hW : W.Nonempty) :
    ∃ w ∈ W, ∀ x, x ∈ W → x ≠ w → ∀ y, y ∈ W → y ≠ w → (G.deleteIncidenceSet w).Reachable x y :=
  exists_terminal_deletion_preserves_connected G hG W hW

theorem source_6_89_three_point_tree_graph (d : ℕ) (hd : 2 ≤ d) (p : I) (x₀ x₁ x₂ : Cubic d) :
    bernoulliBondMeasure d p (threePointConnectionEvent d x₀ x₁ x₂) ≤
      ∑' u : Cubic d, twoPointConnectivityENNReal d p u x₀ * twoPointConnectivityENNReal d p u x₁ *
        twoPointConnectivityENNReal d p u x₂ := threePointConnectivity_le_tsum_prod d p x₀ x₁ x₂

theorem source_6_93_multipoint_tree_graph (d n : ℕ) (hd : 2 ≤ d) (p : I) (x : Fin (n + 3) → Cubic d) :
    bernoulliBondMeasure d p (orderedMultiPointConnectionEvent d n x) ≤
      ∑' s : CubicConnectivitySkeleton (n + 3), ∑' ψ : s.Vertex → Cubic d,
        skeletonConnectivityWeight p s ψ x := multiPointConnectivity_le_skeleton_sum d n p x

theorem source_6_94_cluster_moment (d n : ℕ) (hd : 2 ≤ d) (p : I) :
    clusterSizeMomentENNReal d p (n + 1) ≤ (connectivitySkeletonCount (n + 2) : ℝ≥0∞) *
      susceptibility d p ^ (2 * n + 1) := clusterSizeMoment_succ_le d n p

theorem source_6_95_skeleton_recurrence (n : ℕ) (hn : 3 ≤ n) :
    connectivitySkeletonCount (n + 1) = (2 * n - 3) * connectivitySkeletonCount n :=
  connectivitySkeletonCount_succ hn

theorem source_6_96_skeleton_double_factorial (n : ℕ) (hn : 2 ≤ n) :
    connectivitySkeletonCount (n + 1) = Nat.doubleFactorial (2 * n - 3) := by
  simpa using connectivitySkeletonCount_eq_oddDoubleFactorial (n := n + 1) (by omega)

theorem source_6_96_skeleton_factorial (n : ℕ) (hn : 2 ≤ n) :
    2 ^ (n - 1) * Nat.factorial (n - 1) * connectivitySkeletonCount (n + 1) = Nat.factorial (2 * n - 2) :=
  connectivitySkeletonCount_eq_doubleFactorial hn

theorem source_6_97_literal_exponential_moment (d : ℕ) (hd : 2 ≤ d) (p : I) (t : ℝ≥0∞)
    (ht : 2 * (t * susceptibility d p ^ 2) < 1) :
    (∫⁻ ω, clusterSizeENNReal d ω * ENNReal.ofReal (Real.exp (t * clusterSizeENNReal d ω).toReal)
      ∂bernoulliBondMeasure d p) ≤ susceptibility d p * ENNReal.ofReal
      (1 / (1 - 2 * (t * susceptibility d p ^ 2).toReal) ^ (1 / 2 : ℝ)) :=
  clusterSizeExponentialMoment_le d p t ht

theorem source_6_102_normalized_supermultiplicativity (d : ℕ) (hd : 2 ≤ d) (p : I)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    (p : ℝ) * (1 - (p : ℝ))⁻¹ ^ 2 * (finiteClusterSizeProbability d p m / (m : ℝ)) *
        (finiteClusterSizeProbability d p n / (n : ℝ)) ≤
      finiteClusterSizeProbability d p (m + n) / ((m + n : ℕ) : ℝ) :=
  by
    simpa [Nat.cast_add] using
      CubicBondAnimal.finiteClusterSizeProbability_normalized_supermultiplicative d m n p
        (by omega) (by omega) (by omega) hp0 hp1

theorem source_6_108_cluster_density_analytic (d : ℕ) (hd : 2 ≤ d) :
    AnalyticOnNhd ℝ (concreteClusterDensitySeries d) (Ico (0 : ℝ) (cubicCriticalProbability d)) :=
  concreteClusterDensitySeries_analyticOnNhd_belowCritical d hd

theorem source_6_108_susceptibility_analytic (d : ℕ) (hd : 2 ≤ d) :
    AnalyticOnNhd ℝ (concreteSusceptibilitySeries d) (Ico (0 : ℝ) (cubicCriticalProbability d)) :=
  concreteSusceptibilitySeries_analyticOnNhd_belowCritical d hd

theorem source_6_108_cluster_density_identification (d : ℕ) (hd : 2 ≤ d) :
    ∀ p : I, (p : ℝ) < cubicCriticalProbability d →
      concreteClusterDensitySeries d (p : ℝ) = openClustersPerVertex d p := by
  intro p hp
  exact concreteClusterDensitySeries_eq_openClustersPerVertex (by omega) p

theorem source_6_108_susceptibility_identification (d : ℕ) (hd : 2 ≤ d) :
    ∀ p : I, (p : ℝ) < cubicCriticalProbability d →
      concreteSusceptibilitySeries d (p : ℝ) = (susceptibility d p).toReal := by
  intro p hp
  exact concreteSusceptibilitySeries_eq_susceptibility_toReal_of_lt_critical d p hp

end Review.Chapter06
