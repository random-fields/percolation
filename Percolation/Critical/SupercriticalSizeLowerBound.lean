import Percolation.Critical.ClusterSizeRate
import Percolation.Critical.SupercriticalSizeCombinatorics

/-!
# Lower surface-order bounds for supercritical finite clusters

This file packages the supermultiplicative assembly step in Grimmett's proof of Theorem 8.61.
It converts lower bounds along the scale sequence of Lemma 8.72 into a lower bound at every
positive integer using the bounded-radix representation from Lemma 8.82.
-/

namespace Percolation

open scoped BigOperators unitInterval

private theorem clusterSizeFeketeWeight_mul_pow_le (d : ℕ) (p : I) (hd : 0 < d)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (m n k : ℕ) :
    clusterSizeFeketeWeight d p m * clusterSizeFeketeWeight d p n ^ k ≤
      clusterSizeFeketeWeight d p (m + k * n) := by
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        clusterSizeFeketeWeight d p m * clusterSizeFeketeWeight d p n ^ (k + 1) =
            (clusterSizeFeketeWeight d p m * clusterSizeFeketeWeight d p n ^ k) *
              clusterSizeFeketeWeight d p n := by rw [pow_succ]; ring
        _ ≤ clusterSizeFeketeWeight d p (m + k * n) * clusterSizeFeketeWeight d p n := by
          gcongr
          exact (clusterSizeFeketeWeight_pos d p hd hp0 hp1 n).le
        _ ≤ clusterSizeFeketeWeight d p (m + k * n + n) :=
          clusterSizeFeketeWeight_supermultiplicative d p hd hp0 hp1 _ _
        _ = clusterSizeFeketeWeight d p (m + (k + 1) * n) := by
          congr 1
          ring

private theorem finsupp_product_clusterSizeFeketeWeight_le (d : ℕ) (p : I) (hd : 0 < d)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (r : ℕ → ℕ) (w : ℕ →₀ ℕ) :
    (∏ i ∈ w.support, clusterSizeFeketeWeight d p (r i) ^ w i) ≤
      clusterSizeFeketeWeight d p (w.sum fun i a ↦ a * r i) := by
  change w.prod (fun i a ↦ clusterSizeFeketeWeight d p (r i) ^ a) ≤
    clusterSizeFeketeWeight d p (w.sum fun i a ↦ a * r i)
  induction w using Finsupp.induction with
  | zero => simp [clusterSizeFeketeWeight_zero]
  | single_add i a w ha hi ih =>
      have hpow : 0 ≤ clusterSizeFeketeWeight d p (r i) ^ a :=
        pow_nonneg (clusterSizeFeketeWeight_pos d p hd hp0 hp1 (r i)).le _
      calc
        (Finsupp.single i a + w).prod
            (fun j b ↦ clusterSizeFeketeWeight d p (r j) ^ b) =
            clusterSizeFeketeWeight d p (r i) ^ a *
              w.prod (fun j b ↦ clusterSizeFeketeWeight d p (r j) ^ b) := by
          rw [Finsupp.prod_add_index]
          · simp
          · intro j hj
            simp
          · intro j hj x y
            exact pow_add _ x y
        _ ≤ clusterSizeFeketeWeight d p (r i) ^ a *
            clusterSizeFeketeWeight d p (w.sum fun j b ↦ b * r j) := by gcongr
        _ = clusterSizeFeketeWeight d p (w.sum fun j b ↦ b * r j) *
            clusterSizeFeketeWeight d p (r i) ^ a := mul_comm _ _
        _ ≤ clusterSizeFeketeWeight d p
            ((w.sum fun j b ↦ b * r j) + a * r i) :=
          clusterSizeFeketeWeight_mul_pow_le d p hd hp0 hp1 _ _ _
        _ = clusterSizeFeketeWeight d p
            ((Finsupp.single i a + w).sum fun j b ↦ b * r j) := by
          congr 1
          rw [Finsupp.sum_add_index']
          · simp [add_comm]
          · intro j
            simp
          · intro j x y
            simp [Nat.add_mul]

/-- A lower surface-order estimate along an admissible scale sequence extends to every positive
integer.  This is the analytic assembly step of Grimmett Theorem 8.61. -/
theorem clusterSizeFeketeWeight_ge_exp_neg_surface_of_scale
    {d : ℕ} (hd : 2 ≤ d) (p : I) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    {delta : ℝ} (hdelta : 0 ≤ delta) {r : ℕ → ℕ} (hr0 : r 0 = 1)
    (hrLower : ∀ i, 2 * r i ≤ r (i + 1))
    (hrUpper : ∀ i, (r (i + 1) : ℝ) ≤ delta * r i)
    {eta : ℝ} (heta : 0 ≤ eta)
    (hscale : ∀ i, Real.exp
      (-eta * (r i : ℝ) ^ supercriticalClusterSizeExponent d) ≤
        clusterSizeFeketeWeight d p (r i)) {n : ℕ} (hn : 0 < n) :
    Real.exp (-(4 * delta) * eta *
      (n : ℝ) ^ supercriticalClusterSizeExponent d) ≤
      clusterSizeFeketeWeight d p n := by
  obtain ⟨w, hw, hweighted⟩ :=
    exists_boundedRadixRepresentation_weighted hd hdelta hr0 hrLower hrUpper hn
  have hprod : (∏ i ∈ w.support,
      clusterSizeFeketeWeight d p (r i) ^ w i) ≤ clusterSizeFeketeWeight d p n := by
    rw [← hw.2.1]
    exact finsupp_product_clusterSizeFeketeWeight_le d p (by omega) hp0 hp1 r w
  have hscaleProd : (∏ i ∈ w.support,
      Real.exp (-eta * (r i : ℝ) ^ supercriticalClusterSizeExponent d) ^ w i) ≤
        ∏ i ∈ w.support, clusterSizeFeketeWeight d p (r i) ^ w i := by
    apply Finset.prod_le_prod
    · intro i hi
      positivity
    · intro i hi
      exact pow_le_pow_left₀ (Real.exp_nonneg _) (hscale i) _
  have hprodExp : (∏ i ∈ w.support,
      Real.exp (-eta * (r i : ℝ) ^ supercriticalClusterSizeExponent d) ^ w i) =
        Real.exp (-eta * w.sum
          (fun i a ↦ (a : ℝ) * (r i : ℝ) ^ supercriticalClusterSizeExponent d)) := by
    calc
      (∏ i ∈ w.support,
          Real.exp (-eta * (r i : ℝ) ^ supercriticalClusterSizeExponent d) ^ w i) =
          ∏ i ∈ w.support, Real.exp
            ((w i : ℝ) * (-eta * (r i : ℝ) ^ supercriticalClusterSizeExponent d)) := by
        apply Finset.prod_congr rfl
        intro i hi
        rw [Real.exp_nat_mul]
      _ = Real.exp (∑ i ∈ w.support,
          (w i : ℝ) * (-eta * (r i : ℝ) ^ supercriticalClusterSizeExponent d)) :=
        (Real.exp_sum _ _).symm
      _ = Real.exp (-eta * ∑ i ∈ w.support,
          (w i : ℝ) * (r i : ℝ) ^ supercriticalClusterSizeExponent d) := by
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
  have hexp : Real.exp (-(4 * delta) * eta *
      (n : ℝ) ^ supercriticalClusterSizeExponent d) ≤
      Real.exp (-eta * w.sum
        (fun i a ↦ (a : ℝ) * (r i : ℝ) ^ supercriticalClusterSizeExponent d)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  exact hexp.trans_eq hprodExp.symm |>.trans hscaleProd |>.trans hprod

/-- Scale-by-scale exact-size lower bounds imply the all-size surface-order lower bound.  The
remaining probabilistic input for Theorem 8.61 is precisely Lemma 8.72. -/
theorem finiteClusterSizeProbability_ge_exp_neg_surface_of_scale
    {d : ℕ} (hd : 2 ≤ d) (p : I) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    {delta : ℝ} (hdelta : 0 ≤ delta) {r : ℕ → ℕ} (hr0 : r 0 = 1)
    (hrLower : ∀ i, 2 * r i ≤ r (i + 1))
    (hrUpper : ∀ i, (r (i + 1) : ℝ) ≤ delta * r i)
    {eta : ℝ} (heta : 0 ≤ eta)
    (hscale : ∀ i, (r i : ℝ) * Real.exp
      (-eta * (r i : ℝ) ^ supercriticalClusterSizeExponent d) ≤
        finiteClusterSizeProbability d p (r i)) :
    ∃ gamma : ℝ, 0 ≤ gamma ∧ ∀ n : ℕ, 0 < n →
      Real.exp (-gamma * (n : ℝ) ^ supercriticalClusterSizeExponent d) ≤
        finiteClusterSizeProbability d p n := by
  let c : ℝ := (p : ℝ) * (1 - (p : ℝ))⁻¹ ^ 2
  let ell : ℝ := min 1 c
  have hc : 0 < c := mul_pos hp0 (pow_pos (inv_pos.mpr (sub_pos.mpr hp1)) _)
  have hell : 0 < ell := lt_min one_pos hc
  have hellOne : ell ≤ 1 := min_le_left _ _
  have hellC : ell ≤ c := min_le_right _ _
  have hlogEll : Real.log ell ≤ 0 := Real.log_nonpos hell.le hellOne
  let eta' : ℝ := eta - Real.log ell
  have heta' : 0 ≤ eta' := by dsimp [eta']; linarith
  have hscaleWeight : ∀ i, Real.exp
      (-eta' * (r i : ℝ) ^ supercriticalClusterSizeExponent d) ≤
        clusterSizeFeketeWeight d p (r i) := by
    intro i
    have hri : 0 < r i := rapidlyGrowingSequence_pos hr0 hrLower i
    have hriPow : 1 ≤ (r i : ℝ) ^ supercriticalClusterSizeExponent d :=
      Real.one_le_rpow (by exact_mod_cast hri) <|
        (by norm_num : (0 : ℝ) ≤ 1 / 2).trans (half_le_supercriticalClusterSizeExponent hd)
    have hlogMul : Real.log ell * (r i : ℝ) ^ supercriticalClusterSizeExponent d ≤
        Real.log ell := by
      have := mul_nonpos_of_nonpos_of_nonneg hlogEll (sub_nonneg.mpr hriPow)
      nlinarith
    have hExpEll : Real.exp
        (-eta' * (r i : ℝ) ^ supercriticalClusterSizeExponent d) ≤
          ell * Real.exp (-eta * (r i : ℝ) ^ supercriticalClusterSizeExponent d) := by
      calc
        Real.exp (-eta' * (r i : ℝ) ^ supercriticalClusterSizeExponent d) ≤
            Real.exp (Real.log ell +
              -eta * (r i : ℝ) ^ supercriticalClusterSizeExponent d) := by
          apply Real.exp_le_exp.mpr
          dsimp [eta']
          nlinarith
        _ = ell * Real.exp
            (-eta * (r i : ℝ) ^ supercriticalClusterSizeExponent d) := by
          rw [Real.exp_add, Real.exp_log hell]
    have hAnchored : Real.exp
        (-eta * (r i : ℝ) ^ supercriticalClusterSizeExponent d) ≤
          CubicBondAnimal.anchoredMass d (r i) p := by
      rw [CubicBondAnimal.anchoredMass_eq_finiteClusterSizeProbability_div d (r i) p hri]
      apply (le_div_iff₀ (by exact_mod_cast hri : (0 : ℝ) < r i)).2
      simpa [mul_comm] using hscale i
    rw [clusterSizeFeketeWeight_of_pos d p hri]
    change _ ≤ c * CubicBondAnimal.anchoredMass d (r i) p
    exact hExpEll.trans <| (mul_le_mul_of_nonneg_right hellC (Real.exp_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hAnchored hc.le)
  let ell' : ℝ := min 1 c⁻¹
  have hell' : 0 < ell' := lt_min one_pos (inv_pos.mpr hc)
  have hell'One : ell' ≤ 1 := min_le_left _ _
  have hell'Inv : ell' ≤ c⁻¹ := min_le_right _ _
  have hlogEll' : Real.log ell' ≤ 0 := Real.log_nonpos hell'.le hell'One
  let gamma : ℝ := (4 * delta) * eta' - Real.log ell'
  refine ⟨gamma, ?_, ?_⟩
  · dsimp [gamma]
    have hmain : 0 ≤ (4 * delta) * eta' := mul_nonneg (mul_nonneg (by norm_num) hdelta) heta'
    linarith
  · intro n hn
    have hnPow : 1 ≤ (n : ℝ) ^ supercriticalClusterSizeExponent d :=
      Real.one_le_rpow (by exact_mod_cast hn) <|
        (by norm_num : (0 : ℝ) ≤ 1 / 2).trans (half_le_supercriticalClusterSizeExponent hd)
    have hweight := clusterSizeFeketeWeight_ge_exp_neg_surface_of_scale hd p hp0 hp1
      hdelta hr0 hrLower hrUpper heta' hscaleWeight hn
    have hlogMul : Real.log ell' * (n : ℝ) ^ supercriticalClusterSizeExponent d ≤
        Real.log ell' := by
      have := mul_nonpos_of_nonpos_of_nonneg hlogEll' (sub_nonneg.mpr hnPow)
      nlinarith
    have hExpEll' : Real.exp
        (-gamma * (n : ℝ) ^ supercriticalClusterSizeExponent d) ≤ ell' *
          Real.exp (-(4 * delta) * eta' *
            (n : ℝ) ^ supercriticalClusterSizeExponent d) := by
      calc
        Real.exp (-gamma * (n : ℝ) ^ supercriticalClusterSizeExponent d) ≤
            Real.exp (Real.log ell' +
              -(4 * delta) * eta' *
                (n : ℝ) ^ supercriticalClusterSizeExponent d) := by
          apply Real.exp_le_exp.mpr
          dsimp [gamma]
          nlinarith
        _ = ell' * Real.exp
            (-(4 * delta) * eta' *
              (n : ℝ) ^ supercriticalClusterSizeExponent d) := by
          rw [Real.exp_add, Real.exp_log hell']
    have hprobEq : finiteClusterSizeProbability d p n =
        (n : ℝ) * c⁻¹ * clusterSizeFeketeWeight d p n := by
      rw [clusterSizeFeketeWeight_of_pos d p hn,
        CubicBondAnimal.anchoredMass_eq_finiteClusterSizeProbability_div d n p hn]
      change _ = (n : ℝ) * c⁻¹ * (c * (_ / n))
      field_simp [hc.ne']
    calc
      Real.exp (-gamma * (n : ℝ) ^ supercriticalClusterSizeExponent d) ≤
          ell' * Real.exp
            (-(4 * delta) * eta' *
              (n : ℝ) ^ supercriticalClusterSizeExponent d) := hExpEll'
      _ ≤ ell' * clusterSizeFeketeWeight d p n := mul_le_mul_of_nonneg_left hweight hell'.le
      _ ≤ (n : ℝ) * c⁻¹ * clusterSizeFeketeWeight d p n := by
        apply mul_le_mul_of_nonneg_right
        have hnOne : (1 : ℝ) ≤ (n : ℝ) := by
          exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn.ne')
        · exact hell'Inv.trans (le_mul_of_one_le_left
            (a := (n : ℝ)) (b := c⁻¹) (inv_nonneg.mpr hc.le) hnOne)
        · exact (clusterSizeFeketeWeight_pos d p (by omega) hp0 hp1 n).le
      _ = finiteClusterSizeProbability d p n := hprobEq.symm

end Percolation
