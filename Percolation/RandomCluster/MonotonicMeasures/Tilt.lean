import Percolation.RandomCluster.MonotonicMeasures.Conditional

/-!
# One-parameter tilted finite cube measures

Source: Grimmett, *The Random-Cluster Model* (2006), Chapter 2, Section 2.4,
especially equations (2.42) and (2.45).

This file defines the finite tilted family `μ_p` from (2.42), proves the elementary
strict-positivity and FKG-lattice preservation facts used before Theorem 2.43, and
formalizes the covariance decomposition (2.45). The derivative formula itself is left
for a later calculus layer.
-/

namespace Percolation

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

namespace FiniteCubeMeasure

/-- The coordinate-open indicator `J_e`. -/
noncomputable def edgeIndicator (e : ι) (ω : Set ι) : ℝ := by
  classical
  exact if e ∈ ω then 1 else 0

/-- The number of open coordinates, as a real-valued observable. -/
noncomputable def openCountRV (ω : Set ι) : ℝ :=
  ∑ e : ι, edgeIndicator e ω

omit [Fintype ι] in
theorem edgeIndicator_isIncreasingRandomVariable (e : ι) :
    IsIncreasingRandomVariable (edgeIndicator e : Set ι → ℝ) := by
  classical
  intro ω η hωη
  by_cases hω : e ∈ ω
  · have hη : e ∈ η := hωη hω
    simp [edgeIndicator, hω, hη]
  · by_cases hη : e ∈ η
    · simp [edgeIndicator, hω, hη]
    · simp [edgeIndicator, hω, hη]

theorem openCountRV_isIncreasingRandomVariable :
    IsIncreasingRandomVariable (openCountRV (ι := ι)) := by
  intro ω η hωη
  simp only [openCountRV]
  exact Finset.sum_le_sum fun e _ => edgeIndicator_isIncreasingRandomVariable e hωη

/-- The product density factor in the tilted measure (2.42). -/
noncomputable def tiltWeight (p : ℝ) (ω : Set ι) : ℝ := by
  classical
  exact ∏ e : ι, if e ∈ ω then p else 1 - p

theorem tiltWeight_pos {p : ℝ} (h0 : 0 < p) (h1 : p < 1) (ω : Set ι) :
    0 < tiltWeight (ι := ι) p ω := by
  classical
  unfold tiltWeight
  refine Finset.prod_pos fun e _ => ?_
  by_cases he : e ∈ ω
  · simp [he, h0]
  · simp [he, sub_pos.mpr h1]

theorem tiltWeight_mul_inter_union (p : ℝ) (ω η : Set ι) :
    tiltWeight p ω * tiltWeight p η =
      tiltWeight p (ω ∩ η) * tiltWeight p (ω ∪ η) := by
  classical
  unfold tiltWeight
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl ?_
  intro e _
  by_cases hω : e ∈ ω <;> by_cases hη : e ∈ η <;> simp [hω, hη, mul_comm]

/-- The normalizing constant `Z_p` in (2.42). -/
noncomputable def tiltZ (μ : FiniteCubeMeasure ι) (p : ℝ) : ℝ :=
  ∑ ω : Set ι, μ ω * tiltWeight p ω

theorem exists_pos_mass (μ : FiniteCubeMeasure ι) : ∃ ω : Set ι, 0 < μ ω := by
  classical
  by_contra h
  have hzero : ∀ ω : Set ι, μ ω = 0 := by
    intro ω
    have hle : μ ω ≤ 0 := not_lt.mp (by intro hpos; exact h ⟨ω, hpos⟩)
    exact le_antisymm hle (μ.nonneg ω)
  have hsum : (∑ ω : Set ι, μ ω) = 0 := by simp [hzero]
  rw [μ.sum_mass] at hsum
  norm_num at hsum

theorem tiltZ_pos (μ : FiniteCubeMeasure ι) {p : ℝ} (h0 : 0 < p) (h1 : p < 1) :
    0 < tiltZ μ p := by
  classical
  obtain ⟨ω, hω⟩ := exists_pos_mass μ
  rw [tiltZ]
  refine Finset.sum_pos'
    (fun η _ => mul_nonneg (μ.nonneg η) (le_of_lt (tiltWeight_pos h0 h1 η))) ?_
  exact ⟨ω, Finset.mem_univ ω, mul_pos hω (tiltWeight_pos h0 h1 ω)⟩

/-- The tilted measure `μ_p` from equation (2.42). -/
noncomputable def tilt (μ : FiniteCubeMeasure ι) (p : ℝ) (h0 : 0 < p)
    (h1 : p < 1) : FiniteCubeMeasure ι where
  mass := fun ω => μ ω * tiltWeight p ω / tiltZ μ p
  nonneg := by
    intro ω
    exact div_nonneg (mul_nonneg (μ.nonneg ω) (le_of_lt (tiltWeight_pos h0 h1 ω)))
      (le_of_lt (tiltZ_pos μ h0 h1))
  sum_mass := by
    have hz := tiltZ_pos μ h0 h1
    have hdiv := (Finset.sum_div Finset.univ
      (fun ω : Set ι => μ ω * tiltWeight p ω) (tiltZ μ p)).symm
    rw [hdiv]
    simpa [tiltZ] using div_self (ne_of_gt hz)

@[simp]
theorem tilt_apply (μ : FiniteCubeMeasure ι) {p : ℝ} (h0 : 0 < p) (h1 : p < 1)
    (ω : Set ι) :
    tilt μ p h0 h1 ω = μ ω * tiltWeight p ω / tiltZ μ p := rfl

theorem tilt_expect (μ : FiniteCubeMeasure ι) {p : ℝ} (h0 : 0 < p) (h1 : p < 1)
    (X : Set ι → ℝ) :
    (tilt μ p h0 h1).expect X =
      μ.expect (fun ω => X ω * tiltWeight p ω) / tiltZ μ p := by
  calc
    (∑ ω : Set ι, (μ ω * tiltWeight p ω / tiltZ μ p) * X ω)
        = ∑ ω : Set ι, μ ω * (X ω * tiltWeight p ω) / tiltZ μ p := by
            exact Finset.sum_congr rfl fun _ _ => by ring
    _ = (∑ ω : Set ι, μ ω * (X ω * tiltWeight p ω)) / tiltZ μ p := by
            rw [← Finset.sum_div]

theorem tilt_strictPositive (μ : FiniteCubeMeasure ι) {p : ℝ} (h0 : 0 < p)
    (h1 : p < 1) (hμ : μ.StrictPositive) :
    (tilt μ p h0 h1).StrictPositive := by
  intro ω
  exact div_pos (mul_pos (hμ ω) (tiltWeight_pos h0 h1 ω)) (tiltZ_pos μ h0 h1)

theorem tilt_strictPositive_iff (μ : FiniteCubeMeasure ι) {p : ℝ} (h0 : 0 < p)
    (h1 : p < 1) :
    (tilt μ p h0 h1).StrictPositive ↔ μ.StrictPositive := by
  constructor
  · intro htilt ω
    let z := tiltZ μ p
    let w := tiltWeight p ω
    have hz : 0 < z := by simpa [z] using tiltZ_pos μ h0 h1
    have hw : 0 < w := by simpa [w] using tiltWeight_pos (ι := ι) h0 h1 ω
    have hmass : 0 < μ ω * w / z := by simpa [z, w] using htilt ω
    have hmul : 0 < μ ω * w := by
      have h := mul_pos hmass hz
      have hcalc : (μ ω * w / z) * z = μ ω * w := by field_simp [ne_of_gt hz]
      simpa [hcalc] using h
    nlinarith [μ.nonneg ω, hw, hmul]
  · exact tilt_strictPositive μ h0 h1

theorem fkgLatticeCondition_tilt (μ : FiniteCubeMeasure ι) {p : ℝ} (h0 : 0 < p)
    (h1 : p < 1) (hFKG : FKGLatticeCondition μ) :
    FKGLatticeCondition (tilt μ p h0 h1) := by
  intro ω η
  let z := tiltZ μ p
  let wω := tiltWeight p ω
  let wη := tiltWeight p η
  let wi := tiltWeight p (ω ∩ η)
  let wu := tiltWeight p (ω ∪ η)
  have hz : 0 < z := by simpa [z] using tiltZ_pos μ h0 h1
  have hwω : 0 < wω := by simpa [wω] using tiltWeight_pos (ι := ι) h0 h1 ω
  have hwη : 0 < wη := by simpa [wη] using tiltWeight_pos (ι := ι) h0 h1 η
  have hweight : wω * wη = wi * wu := by
    simpa [wω, wη, wi, wu] using tiltWeight_mul_inter_union (ι := ι) p ω η
  have hbase : μ ω * μ η ≤ μ (ω ∩ η) * μ (ω ∪ η) := hFKG ω η
  have hscaled := mul_le_mul_of_nonneg_right hbase
    (mul_nonneg (le_of_lt hwω) (le_of_lt hwη))
  have hscaled' : (μ ω * μ η) * (wω * wη) ≤
      (μ (ω ∩ η) * μ (ω ∪ η)) * (wi * wu) := by
    calc
      (μ ω * μ η) * (wω * wη) ≤
          (μ (ω ∩ η) * μ (ω ∪ η)) * (wω * wη) := hscaled
      _ = (μ (ω ∩ η) * μ (ω ∪ η)) * (wi * wu) := by rw [hweight]
  calc
    tilt μ p h0 h1 ω * tilt μ p h0 h1 η =
        ((μ ω * μ η) * (wω * wη)) / (z * z) := by
          simp [z, wω, wη, tilt_apply]
          ring
    _ ≤ ((μ (ω ∩ η) * μ (ω ∪ η)) * (wi * wu)) / (z * z) := by
          exact div_le_div_of_nonneg_right hscaled'
            (mul_nonneg (le_of_lt hz) (le_of_lt hz))
    _ = tilt μ p h0 h1 (ω ∩ η) * tilt μ p h0 h1 (ω ∪ η) := by
          simp [z, wi, wu, tilt_apply]
          ring

theorem monotonicMeasure_tilt_of_monotonicMeasure (μ : FiniteCubeMeasure ι)
    {p : ℝ} (h0 : 0 < p) (h1 : p < 1) (hμ : μ.StrictPositive)
    (hmono : MonotonicMeasure μ) :
    MonotonicMeasure (tilt μ p h0 h1) := by
  have hFKG : FKGLatticeCondition μ :=
    fkgLatticeCondition_of_oneMonotonicMeasure μ hμ
      (oneMonotonicMeasure_of_monotonicMeasure μ hmono)
  exact monotonicMeasure_of_fkgLatticeCondition (tilt μ p h0 h1)
    (fkgLatticeCondition_tilt μ h0 h1 hFKG)

/-- The covariance decomposition (2.45), in finite-cube form. -/
theorem covariance_openCountRV_eq_sum (μ : FiniteCubeMeasure ι) (X : Set ι → ℝ) :
    μ.covariance (openCountRV (ι := ι)) X =
      ∑ e : ι, μ.covariance (edgeIndicator e) X := by
  simpa [openCountRV] using covariance_sum_left μ (fun e : ι => edgeIndicator e) X

/-- Equation (2.45) for the tilted measure `μ_p`. -/
theorem tilt_covariance_openCountRV_eq_sum (μ : FiniteCubeMeasure ι) {p : ℝ}
    (h0 : 0 < p) (h1 : p < 1) (X : Set ι → ℝ) :
    (tilt μ p h0 h1).covariance (openCountRV (ι := ι)) X =
      ∑ e : ι, (tilt μ p h0 h1).covariance (edgeIndicator e) X :=
  covariance_openCountRV_eq_sum (tilt μ p h0 h1) X

end FiniteCubeMeasure

end Percolation
