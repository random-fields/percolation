import Percolation.Critical.GhostRectangle

/-!
# The ghost-field proof of finite subcritical susceptibility

This file derives Grimmett's Theorem 5.2 from Theorem 5.48, independently of the radius-decay
route.
-/

namespace Percolation

open Set Filter MeasureTheory
open scoped unitInterval Topology ENNReal

noncomputable section

theorem finiteSusceptibility_eq_susceptibility_of_theta_eq_zero
    (d : ℕ) (p : I) (htheta : theta d p = 0) :
    finiteSusceptibility d p = susceptibility d p := by
  let μ := bernoulliBondMeasure d p
  let A : Set (EdgeConfiguration d) := {ω | hasInfiniteOpenCluster d ω}
  have hμAReal : μ.real A = 0 := by
    simpa [theta, μ, A] using htheta
  have hμA : μ A = 0 :=
    (measureReal_eq_zero_iff (measure_ne_top μ A)).mp hμAReal
  have hae : ∀ᵐ ω : EdgeConfiguration d ∂μ, ω ∉ A := by
    rw [ae_iff]
    simpa only [Set.mem_setOf_eq, not_not] using hμA
  unfold finiteSusceptibility susceptibility
  apply lintegral_congr_ae
  filter_upwards [hae] with ω hω
  unfold finiteClusterSizeWeight
  rw [if_pos]
  apply Set.not_infinite.mp
  exact hω

private theorem cubicCriticalProbability_le_one (d : ℕ) :
    cubicCriticalProbability d ≤ 1 := by
  let A : Set ℝ := ((fun p : I ↦ (p : ℝ)) '' {p : I | theta d p = 0})
  let p0 : I := ⟨0, by norm_num, by norm_num⟩
  have hA0 : (0 : ℝ) ∈ A := by
    refine ⟨p0, ?_, rfl⟩
    exact theta_eq_zero_of_mul_cubicConnectiveConstant_lt_one d p0 (by simp [p0])
  rw [cubicCriticalProbability]
  exact csSup_le ⟨0, hA0⟩ fun x hx ↦ by
    rcases hx with ⟨q, _hq, rfl⟩
    exact q.property.2

/-- Grimmett, Theorem 5.2, via the independent Aizenman--Barsky ghost-field proof. -/
theorem susceptibility_lt_top_of_lt_critical_via_ghost
    (d : ℕ) (hd : 2 ≤ d) (p : I)
    (hp : (p : ℝ) < cubicCriticalProbability d) :
    susceptibility d p < ⊤ := by
  let pc := cubicCriticalProbability d
  have hd0 : 0 < d := by omega
  have hpc0 : 0 < pc :=
    (one_div_pos.mpr (cubicConnectiveConstant_pos hd0)).trans_le
      (connectiveConstant_inv_le_cubicCriticalProbability hd)
  have hpc1 : pc ≤ 1 := cubicCriticalProbability_le_one d
  let q := ((p : ℝ) + pc) / 2
  have hpq : (p : ℝ) ≤ q := by dsimp [q, pc]; linarith
  have hqpc : q < pc := by dsimp [q, pc]; linarith
  have hq0 : 0 < q := by dsimp [q, pc]; nlinarith [p.property.1]
  have hq1 : q < 1 := hqpc.trans_le hpc1
  let qI : I := ⟨q, hq0.le, hq1.le⟩
  have hqFinite : susceptibility d qI < ⊤ := by
    by_contra hnot
    have hqTop : susceptibility d qI = ⊤ := top_unique (not_lt.mp hnot)
    have hqTheta : theta d qI = 0 :=
      theta_eq_zero_of_lt_criticalProbability (by simpa [qI, pc] using hqpc)
    have hqFiniteTop : finiteSusceptibility d qI = ⊤ := by
      rw [finiteSusceptibility_eq_susceptibility_of_theta_eq_zero d qI hqTheta]
      exact hqTop
    rcases finiteSusceptibility_eq_top_imp_theta_lower_bound
      d hd qI hq0 hq1 hqFiniteTop with hthetaPos | hlinear
    · rw [hqTheta] at hthetaPos
      exact lt_irrefl 0 hthetaPos
    · let r := (q + pc) / 2
      have hqr : q < r := by dsimp [r]; linarith
      have hrpc : r < pc := by dsimp [r]; linarith
      have hr0 : 0 < r := hq0.trans hqr
      have hr1 : r < 1 := hrpc.trans_le hpc1
      let rI : I := ⟨r, hr0.le, hr1.le⟩
      have hqIrI : qI ≤ rI := by exact_mod_cast hqr.le
      have hrLower := hlinear.2 rI hqIrI
      have hrTheta : theta d rI = 0 :=
        theta_eq_zero_of_lt_criticalProbability (by simpa [rI, pc] using hrpc)
      rw [hrTheta] at hrLower
      have hpositive : 0 < (r - q) / (2 * r) :=
        div_pos (sub_pos.mpr hqr) (mul_pos (by norm_num) hr0)
      exact (not_lt_of_ge hrLower) hpositive
  exact (susceptibility_mono d hpq).trans_lt hqFinite

end

end Percolation
