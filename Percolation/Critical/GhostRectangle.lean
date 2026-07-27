import Percolation.Critical.GhostSqrt
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The Aizenman--Barsky rectangle argument

This file proves the joint regularity of the animal-series ghost probability and then carries
out Grimmett's rectangle integration (5.57)--(5.58), culminating in Theorem 5.48.
-/

namespace Percolation

open Set Filter MeasureTheory
open scoped unitInterval Topology BigOperators Interval

noncomputable section

private noncomputable def ghostThetaJointTerm (d n : ℕ) (z : ℝ × ℝ) : ℝ :=
  -((1 - z.2) ^ n * cubicClusterSizePolynomial d n z.1)

private noncomputable def ghostThetaJointTermFDeriv (d n : ℕ) (z : ℝ × ℝ) :
    (ℝ × ℝ) →L[ℝ] ℝ :=
  -((1 - z.2) ^ n •
      (ContinuousLinearMap.toSpanSingleton ℝ
        (cubicClusterSizePolynomialDerivative d n z.1) ∘L
          ContinuousLinearMap.fst ℝ ℝ ℝ) +
    cubicClusterSizePolynomial d n z.1 •
      (ContinuousLinearMap.toSpanSingleton ℝ
        ((n : ℝ) * (1 - z.2) ^ (n - 1) * (-1)) ∘L
          ContinuousLinearMap.snd ℝ ℝ ℝ))

private theorem ghostThetaJointTerm_hasFDerivAt (d n : ℕ) (z : ℝ × ℝ) :
    HasFDerivAt (ghostThetaJointTerm d n) (ghostThetaJointTermFDeriv d n z) z := by
  have hp :=
    (cubicClusterSizePolynomial_hasDerivAt d n z.1).hasFDerivAt.comp z hasFDerivAt_fst
  have hqOne : HasDerivAt (fun y : ℝ ↦ 1 - y) (-1) z.2 :=
    by simpa using (hasDerivAt_const z.2 1).sub (hasDerivAt_id z.2)
  have hq := (hqOne.pow n).hasFDerivAt.comp z hasFDerivAt_snd
  simpa only [Function.comp_apply, ghostThetaJointTerm,
    ghostThetaJointTermFDeriv] using (hq.mul hp).neg

@[simp]
private theorem ghostThetaJointTermFDeriv_apply_fst (d n : ℕ) (z : ℝ × ℝ) :
    ghostThetaJointTermFDeriv d n z (1, 0) =
      -((1 - z.2) ^ n * cubicClusterSizePolynomialDerivative d n z.1) := by
  simp [ghostThetaJointTermFDeriv]

@[simp]
private theorem ghostThetaJointTermFDeriv_apply_snd (d n : ℕ) (z : ℝ × ℝ) :
  ghostThetaJointTermFDeriv d n z (0, 1) =
      (n : ℝ) * (1 - z.2) ^ (n - 1) * cubicClusterSizePolynomial d n z.1 := by
  simp [ghostThetaJointTermFDeriv]
  ring

private theorem ghostThetaPSeries_eq_one_add_tsum_joint (d : ℕ) (z : ℝ × ℝ) :
    ghostThetaPSeries d z.2 z.1 = 1 + ∑' n : ℕ, ghostThetaJointTerm d n z := by
  unfold ghostThetaPSeries ghostThetaJointTerm
  rw [tsum_neg]
  ring

/-- The animal series for the ghost probability is jointly differentiable on the open unit
square.  This supplies the two-dimensional regularity used in (5.57). -/
private theorem ghostThetaJoint_hasFDerivAt (d : ℕ) {z : ℝ × ℝ}
    (hp0 : 0 < z.1) (hp1 : z.1 < 1) (hγ0 : 0 < z.2) (hγ1 : z.2 < 1) :
    HasFDerivAt (fun w : ℝ × ℝ ↦ ghostThetaPSeries d w.2 w.1)
      (∑' n : ℕ, ghostThetaJointTermFDeriv d n z) z := by
  let p₁ := z.1 / 2
  let p₂ := (1 + z.1) / 2
  let γ₁ := z.2 / 2
  let q := 1 - γ₁
  let K := (d : ℝ) / p₁ + (2 * d : ℝ) / (1 - p₂)
  let u : ℕ → ℝ := fun n ↦ K * n * q ^ n + q⁻¹ * n * q ^ n
  let s : Set (ℝ × ℝ) := Ioo p₁ p₂ ×ˢ Ioo γ₁ 1
  have hp₁0 : 0 < p₁ := by dsimp [p₁]; linarith
  have hp₂1 : p₂ < 1 := by dsimp [p₂]; linarith
  have hγ₁0 : 0 < γ₁ := by dsimp [γ₁]; linarith
  have hγ₁1 : γ₁ < 1 := by dsimp [γ₁]; linarith
  have hq0 : 0 < q := by dsimp [q]; linarith
  have hq1 : q < 1 := by dsimp [q]; linarith
  have hqnorm : ‖q‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos hq0]; exact hq1
  have hgeom : Summable (fun n : ℕ ↦ (n : ℝ) * q ^ n) := by
    simpa [pow_one] using
      (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hqnorm)
  have hu : Summable u := by
    simpa [u, mul_assoc] using (hgeom.mul_left K).add (hgeom.mul_left q⁻¹)
  have hz : z ∈ s := by
    constructor
    · dsimp [p₁, p₂]
      constructor <;> linarith
    · dsimp [γ₁]
      exact ⟨by linarith, hγ1⟩
  have hsOpen : IsOpen s := isOpen_Ioo.prod isOpen_Ioo
  have hsPreconnected : IsPreconnected s := isPreconnected_Ioo.prod isPreconnected_Ioo
  have hderivBound : ∀ n w, w ∈ s → ‖ghostThetaJointTermFDeriv d n w‖ ≤ u n := by
    intro n w hw
    have hwp0 : 0 < w.1 := hp₁0.trans hw.1.1
    have hwp1 : w.1 < 1 := hw.1.2.trans hp₂1
    have hwγ0 : 0 < w.2 := hγ₁0.trans hw.2.1
    have hwγ1 : w.2 < 1 := hw.2.2
    have hqy0 : 0 ≤ 1 - w.2 := (sub_pos.mpr hwγ1).le
    have hqyq : 1 - w.2 ≤ q := by
      dsimp [q]
      exact sub_le_sub_left hw.2.1.le 1
    let pI : I := ⟨w.1, hwp0.le, hwp1.le⟩
    have hpoly : cubicClusterSizePolynomial d n w.1 =
        finiteClusterSizeProbability d pI n :=
      cubicClusterSizePolynomial_eq_probability d n pI
    have hpolyAbs : |cubicClusterSizePolynomial d n w.1| ≤ 1 := by
      rw [hpoly, abs_of_nonneg (finiteClusterSizeProbability_nonneg d pI n)]
      exact finiteClusterSizeProbability_le_one d pI n
    have hfirst : (d : ℝ) / w.1 ≤ (d : ℝ) / p₁ :=
      div_le_div_of_nonneg_left (Nat.cast_nonneg d) hp₁0 hw.1.1.le
    have hsecond : (2 * d : ℝ) / (1 - w.1) ≤ (2 * d : ℝ) / (1 - p₂) :=
      div_le_div_of_nonneg_left (by positivity) (sub_pos.mpr hp₂1)
        (sub_le_sub_left hw.1.2.le 1)
    have hderivAbs : |cubicClusterSizePolynomialDerivative d n w.1| ≤ K * n := by
      have hbase := abs_cubicClusterSizePolynomialDerivative_le (d := d) (n := n) hwp0 hwp1
      rw [show (⟨w.1, hwp0.le, hwp1.le⟩ : I) = pI by rfl] at hbase
      have hcoef0 : 0 ≤ ((d : ℝ) / w.1 + (2 * d : ℝ) / (1 - w.1)) * n := by
        positivity
      have hdrop :
          (((d : ℝ) / w.1 + (2 * d : ℝ) / (1 - w.1)) * n) *
              finiteClusterSizeProbability d pI n ≤
            ((d : ℝ) / w.1 + (2 * d : ℝ) / (1 - w.1)) * n :=
        mul_le_of_le_one_right hcoef0 (finiteClusterSizeProbability_le_one d pI n)
      calc
        |cubicClusterSizePolynomialDerivative d n w.1| ≤
            (((d : ℝ) / w.1 + (2 * d : ℝ) / (1 - w.1)) * n) *
              finiteClusterSizeProbability d pI n := hbase
        _ ≤ (((d : ℝ) / w.1 + (2 * d : ℝ) / (1 - w.1)) * n) := hdrop
        _ ≤ K * n := mul_le_mul_of_nonneg_right (by
          dsimp [K]
          exact add_le_add hfirst hsecond) (Nat.cast_nonneg n)
    have hpow : (1 - w.2) ^ n ≤ q ^ n := pow_le_pow_left₀ hqy0 hqyq n
    have hpred : (n : ℝ) * (1 - w.2) ^ (n - 1) ≤ q⁻¹ * n * q ^ n := by
      have hpowpred : (1 - w.2) ^ (n - 1) ≤ q ^ (n - 1) :=
        pow_le_pow_left₀ hqy0 hqyq _
      have heq : (n : ℝ) * q ^ (n - 1) = q⁻¹ * n * q ^ n := by
        rw [natCast_mul_pow_pred_eq_pow_mul_div n hq0.ne']
        field_simp
      calc
        (n : ℝ) * (1 - w.2) ^ (n - 1) ≤ (n : ℝ) * q ^ (n - 1) :=
          mul_le_mul_of_nonneg_left hpowpred (Nat.cast_nonneg n)
        _ = q⁻¹ * n * q ^ n := heq
    have hpMap :
        ‖ContinuousLinearMap.toSpanSingleton ℝ
              (cubicClusterSizePolynomialDerivative d n w.1) ∘L
            ContinuousLinearMap.fst ℝ ℝ ℝ‖ ≤
          |cubicClusterSizePolynomialDerivative d n w.1| := by
      calc
        _ ≤ ‖ContinuousLinearMap.toSpanSingleton ℝ
              (cubicClusterSizePolynomialDerivative d n w.1)‖ *
            ‖ContinuousLinearMap.fst ℝ ℝ ℝ‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
        _ = |cubicClusterSizePolynomialDerivative d n w.1| *
            ‖ContinuousLinearMap.fst ℝ ℝ ℝ‖ := by
          rw [ContinuousLinearMap.norm_toSpanSingleton, Real.norm_eq_abs]
        _ ≤ |cubicClusterSizePolynomialDerivative d n w.1| * 1 :=
          mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_fst_le ℝ ℝ ℝ) (abs_nonneg _)
        _ = _ := by ring
    have hγMap :
        ‖ContinuousLinearMap.toSpanSingleton ℝ
              ((n : ℝ) * (1 - w.2) ^ (n - 1) * -1) ∘L
            ContinuousLinearMap.snd ℝ ℝ ℝ‖ ≤
          (n : ℝ) * (1 - w.2) ^ (n - 1) := by
      calc
        _ ≤ ‖ContinuousLinearMap.toSpanSingleton ℝ
              ((n : ℝ) * (1 - w.2) ^ (n - 1) * -1)‖ *
            ‖ContinuousLinearMap.snd ℝ ℝ ℝ‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
        _ = |(n : ℝ) * (1 - w.2) ^ (n - 1) * -1| *
            ‖ContinuousLinearMap.snd ℝ ℝ ℝ‖ := by
          rw [ContinuousLinearMap.norm_toSpanSingleton, Real.norm_eq_abs]
        _ ≤ |(n : ℝ) * (1 - w.2) ^ (n - 1) * -1| * 1 :=
          mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_snd_le ℝ ℝ ℝ) (abs_nonneg _)
        _ = _ := by
          rw [abs_mul, abs_mul, abs_neg, abs_one,
            abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n),
            abs_of_nonneg (pow_nonneg hqy0 _)]
          ring
    rw [ghostThetaJointTermFDeriv, norm_neg]
    calc
      ‖(1 - w.2) ^ n •
            (ContinuousLinearMap.toSpanSingleton ℝ
                (cubicClusterSizePolynomialDerivative d n w.1) ∘L
              ContinuousLinearMap.fst ℝ ℝ ℝ) +
          cubicClusterSizePolynomial d n w.1 •
            (ContinuousLinearMap.toSpanSingleton ℝ
                ((n : ℝ) * (1 - w.2) ^ (n - 1) * -1) ∘L
              ContinuousLinearMap.snd ℝ ℝ ℝ)‖ ≤
          ‖(1 - w.2) ^ n •
            (ContinuousLinearMap.toSpanSingleton ℝ
                (cubicClusterSizePolynomialDerivative d n w.1) ∘L
              ContinuousLinearMap.fst ℝ ℝ ℝ)‖ +
          ‖cubicClusterSizePolynomial d n w.1 •
            (ContinuousLinearMap.toSpanSingleton ℝ
                ((n : ℝ) * (1 - w.2) ^ (n - 1) * -1) ∘L
              ContinuousLinearMap.snd ℝ ℝ ℝ)‖ := norm_add_le _ _
      _ ≤ (1 - w.2) ^ n * |cubicClusterSizePolynomialDerivative d n w.1| +
          |cubicClusterSizePolynomial d n w.1| *
            ((n : ℝ) * (1 - w.2) ^ (n - 1)) := by
        simp only [norm_smul, Real.norm_eq_abs, abs_pow, abs_of_nonneg hqy0]
        exact add_le_add
          (mul_le_mul_of_nonneg_left hpMap (pow_nonneg hqy0 _))
          (mul_le_mul_of_nonneg_left hγMap (abs_nonneg _))
      _ ≤ q ^ n * (K * n) + 1 * (q⁻¹ * n * q ^ n) := by
        apply add_le_add
        · exact mul_le_mul hpow hderivAbs (abs_nonneg _)
            (pow_nonneg hq0.le _)
        · exact mul_le_mul hpolyAbs hpred
            (mul_nonneg (Nat.cast_nonneg n) (pow_nonneg hqy0 _)) zero_le_one
      _ = u n := by dsimp [u]; ring
  have hsumAt : Summable (fun n : ℕ ↦ ghostThetaJointTerm d n z) := by
    have hbound : ∀ n, ‖ghostThetaJointTerm d n z‖ ≤ q ^ n := by
      intro n
      let hpI : I := ⟨z.1, hp0.le, hp1.le⟩
      have hpolyZ : cubicClusterSizePolynomial d n z.1 =
          finiteClusterSizeProbability d hpI n := by
        exact cubicClusterSizePolynomial_eq_probability d n hpI
      rw [ghostThetaJointTerm, norm_neg, Real.norm_eq_abs, abs_mul,
        abs_pow, abs_of_nonneg (sub_pos.mpr hγ1).le, hpolyZ,
        abs_of_nonneg (finiteClusterSizeProbability_nonneg d hpI n)]
      exact mul_le_of_le_one_right (pow_nonneg (sub_pos.mpr hγ1).le _)
        (finiteClusterSizeProbability_le_one d hpI n) |>.trans
          (pow_le_pow_left₀ (sub_pos.mpr hγ1).le (by dsimp [q, γ₁]; linarith) n)
    exact (summable_geometric_of_norm_lt_one hqnorm).of_norm_bounded hbound
  have hsum := hasFDerivAt_tsum_of_isPreconnected hu hsOpen hsPreconnected
    (fun n w _ ↦ ghostThetaJointTerm_hasFDerivAt d n w) hderivBound hz hsumAt hz
  have heq : (fun w : ℝ × ℝ ↦ ghostThetaPSeries d w.2 w.1) =
      fun w ↦ 1 + ∑' n : ℕ, ghostThetaJointTerm d n w := by
    funext w
    exact ghostThetaPSeries_eq_one_add_tsum_joint d w
  have htotal := (hasFDerivAt_const (1 : ℝ) z).add hsum
  convert htotal using 1
  · simp

private theorem ghostThetaJointFDeriv_apply_fst (d : ℕ) {z : ℝ × ℝ}
    (hp0 : 0 < z.1) (hp1 : z.1 < 1) (hγ0 : 0 < z.2) (hγ1 : z.2 < 1) :
    (∑' n : ℕ, ghostThetaJointTermFDeriv d n z) (1, 0) =
      deriv (ghostThetaPSeries d z.2) z.1 := by
  have hjoint := ghostThetaJoint_hasFDerivAt d hp0 hp1 hγ0 hγ1
  have hpath : HasDerivAt (fun x : ℝ ↦ (x, z.2)) (1, 0) z.1 := by
    have h := (hasFDerivAt_id (𝕜 := ℝ) z.1).prodMk
      (hasFDerivAt_const z.2 z.1)
    simpa using h.hasDerivAt
  have hcomp := hjoint.comp_hasDerivAt z.1 hpath
  have hcomp' : HasDerivAt (ghostThetaPSeries d z.2)
      ((∑' n : ℕ, ghostThetaJointTermFDeriv d n z) (1, 0)) z.1 := by
    simpa [Function.comp_def] using hcomp
  have hsep := ghostThetaPSeries_hasDerivAt d hp0 hp1 hγ0 hγ1
  rw [hsep.deriv]
  exact hcomp'.unique hsep

private theorem ghostThetaJointFDeriv_apply_snd (d : ℕ) {z : ℝ × ℝ}
    (hp0 : 0 < z.1) (hp1 : z.1 < 1) (hγ0 : 0 < z.2) (hγ1 : z.2 < 1) :
    (∑' n : ℕ, ghostThetaJointTermFDeriv d n z) (0, 1) =
      deriv (ghostThetaSeries d ⟨z.1, hp0.le, hp1.le⟩) z.2 := by
  let pI : I := ⟨z.1, hp0.le, hp1.le⟩
  have hjoint := ghostThetaJoint_hasFDerivAt d hp0 hp1 hγ0 hγ1
  have hpath : HasDerivAt (fun y : ℝ ↦ (z.1, y)) (0, 1) z.2 := by
    have h := (hasFDerivAt_const z.1 z.2).prodMk
      (hasFDerivAt_id (𝕜 := ℝ) z.2)
    simpa using h.hasDerivAt
  have hcomp := hjoint.comp_hasDerivAt z.2 hpath
  have hfun : (fun y : ℝ ↦ ghostThetaPSeries d y z.1) = ghostThetaSeries d pI := by
    funext y
    unfold ghostThetaPSeries ghostThetaSeries
    congr 2
    funext n
    rw [show z.1 = (pI : ℝ) by rfl,
      cubicClusterSizePolynomial_eq_probability d n pI]
  have hcomp' : HasDerivAt (ghostThetaSeries d pI)
      ((∑' n : ℕ, ghostThetaJointTermFDeriv d n z) (0, 1)) z.2 := by
    rw [← hfun]
    simpa [Function.comp_def] using hcomp
  have hsep := ghostThetaSeries_hasDerivAt d pI hγ0 hγ1
  rw [hsep.deriv]
  exact hcomp'.unique hsep

private noncomputable def ghostThetaGammaDerivativeSeries (d : ℕ) (z : ℝ × ℝ) : ℝ :=
  ∑' n : ℕ, (n : ℝ) * (1 - z.2) ^ (n - 1) * cubicClusterSizePolynomial d n z.1

private theorem ghostThetaJointFDeriv_apply_snd_eq_series (d : ℕ) {z : ℝ × ℝ}
    (hp0 : 0 < z.1) (hp1 : z.1 < 1) (hγ0 : 0 < z.2) (hγ1 : z.2 < 1) :
    (∑' n : ℕ, ghostThetaJointTermFDeriv d n z) (0, 1) =
      ghostThetaGammaDerivativeSeries d z := by
  let pI : I := ⟨z.1, hp0.le, hp1.le⟩
  rw [ghostThetaJointFDeriv_apply_snd d hp0 hp1 hγ0 hγ1]
  have hsep := ghostThetaSeries_hasDerivAt d pI hγ0 hγ1
  rw [hsep.deriv]
  unfold ghostThetaGammaDerivativeSeries
  apply tsum_congr
  intro n
  rw [show z.1 = (pI : ℝ) by rfl,
    cubicClusterSizePolynomial_eq_probability d n pI]

private theorem continuousOn_ghostThetaPDerivativeSeries_rectangle
    (d : ℕ) {a b δ ε : ℝ} (ha0 : 0 < a) (hb1 : b < 1)
    (hδ0 : 0 < δ) (hε1 : ε < 1) (hδε : δ ≤ ε) :
    ContinuousOn (fun z : ℝ × ℝ ↦ ghostThetaPDerivativeSeries d z.2 z.1)
      (Icc a b ×ˢ Icc δ ε) := by
  let q := 1 - δ
  let K := (d : ℝ) / a + (2 * d : ℝ) / (1 - b)
  let u : ℕ → ℝ := fun n ↦ K * n * q ^ n
  have hq0 : 0 ≤ q := by dsimp [q]; linarith
  have hq1 : q < 1 := by dsimp [q]; linarith
  have hqnorm : ‖q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hq0]
    exact hq1
  have hgeom : Summable (fun n : ℕ ↦ (n : ℝ) * q ^ n) := by
    simpa [pow_one] using
      (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hqnorm)
  have hu : Summable u := by simpa [u, mul_assoc] using hgeom.mul_left K
  have hterms : ∀ n : ℕ, ContinuousOn
      (fun z : ℝ × ℝ ↦ (1 - z.2) ^ n * cubicClusterSizePolynomialDerivative d n z.1)
      (Icc a b ×ˢ Icc δ ε) := by
    intro n
    have hpoly : Continuous (cubicClusterSizePolynomialDerivative d n) := by
      unfold cubicClusterSizePolynomialDerivative
      fun_prop
    exact ((continuous_const.sub continuous_snd).pow n).mul
      (hpoly.comp continuous_fst) |>.continuousOn
  have hbound : ∀ n z, z ∈ Icc a b ×ˢ Icc δ ε →
      ‖(1 - z.2) ^ n * cubicClusterSizePolynomialDerivative d n z.1‖ ≤ u n := by
    intro n z hz
    have hzp0 : 0 < z.1 := ha0.trans_le hz.1.1
    have hzp1 : z.1 < 1 := hz.1.2.trans_lt hb1
    have hqz0 : 0 ≤ 1 - z.2 := by linarith [hz.2.2]
    have hqzq : 1 - z.2 ≤ q := by dsimp [q]; linarith [hz.2.1]
    let pI : I := ⟨z.1, hzp0.le, hzp1.le⟩
    have hfirst : (d : ℝ) / z.1 ≤ (d : ℝ) / a :=
      div_le_div_of_nonneg_left (Nat.cast_nonneg d) ha0 hz.1.1
    have hsecond : (2 * d : ℝ) / (1 - z.1) ≤ (2 * d : ℝ) / (1 - b) :=
      div_le_div_of_nonneg_left (by positivity) (sub_pos.mpr hb1)
        (sub_le_sub_left hz.1.2 1)
    have hderiv := abs_cubicClusterSizePolynomialDerivative_le
      (d := d) (n := n) hzp0 hzp1
    have hcoef0 : 0 ≤ ((d : ℝ) / z.1 + (2 * d : ℝ) / (1 - z.1)) * n := by
      positivity
    have hderivK : |cubicClusterSizePolynomialDerivative d n z.1| ≤ K * n := by
      calc
        _ ≤ (((d : ℝ) / z.1 + (2 * d : ℝ) / (1 - z.1)) * n) *
            finiteClusterSizeProbability d pI n := hderiv
        _ ≤ ((d : ℝ) / z.1 + (2 * d : ℝ) / (1 - z.1)) * n :=
          mul_le_of_le_one_right hcoef0 (finiteClusterSizeProbability_le_one d pI n)
        _ ≤ K * n := mul_le_mul_of_nonneg_right (by
          dsimp [K]
          exact add_le_add hfirst hsecond) (Nat.cast_nonneg n)
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hqz0]
    calc
      (1 - z.2) ^ n * |cubicClusterSizePolynomialDerivative d n z.1| ≤
          q ^ n * (K * n) :=
        mul_le_mul (pow_le_pow_left₀ hqz0 hqzq n) hderivK
          (abs_nonneg _) (pow_nonneg hq0 _)
      _ = u n := by dsimp [u]; ring
  unfold ghostThetaPDerivativeSeries
  exact (continuousOn_tsum hterms hu hbound).neg

private theorem continuousOn_ghostThetaGammaDerivativeSeries_rectangle
    (d : ℕ) {a b δ ε : ℝ} (ha0 : 0 < a) (hb1 : b < 1)
    (hδ0 : 0 < δ) (hε1 : ε < 1) (hδε : δ ≤ ε) :
    ContinuousOn (ghostThetaGammaDerivativeSeries d) (Icc a b ×ˢ Icc δ ε) := by
  let q := 1 - δ
  let u : ℕ → ℝ := fun n ↦ q⁻¹ * n * q ^ n
  have hq0 : 0 < q := by dsimp [q]; linarith
  have hq1 : q < 1 := by dsimp [q]; linarith
  have hqnorm : ‖q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hq0]
    exact hq1
  have hgeom : Summable (fun n : ℕ ↦ (n : ℝ) * q ^ n) := by
    simpa [pow_one] using
      (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hqnorm)
  have hu : Summable u := by simpa [u, mul_assoc] using hgeom.mul_left q⁻¹
  have hpoly (n : ℕ) : Continuous (cubicClusterSizePolynomial d n) := by
    unfold cubicClusterSizePolynomial
    fun_prop
  have hterms : ∀ n : ℕ, ContinuousOn
      (fun z : ℝ × ℝ ↦ (n : ℝ) * (1 - z.2) ^ (n - 1) *
        cubicClusterSizePolynomial d n z.1) (Icc a b ×ˢ Icc δ ε) := by
    intro n
    exact ((continuous_const.mul ((continuous_const.sub continuous_snd).pow (n - 1))).mul
      ((hpoly n).comp continuous_fst)).continuousOn
  have hbound : ∀ (n : ℕ) (z : ℝ × ℝ), z ∈ Icc a b ×ˢ Icc δ ε →
      ‖(n : ℝ) * (1 - z.2) ^ (n - 1) * cubicClusterSizePolynomial d n z.1‖ ≤ u n := by
    intro n z hz
    have hzp0 : 0 < z.1 := ha0.trans_le hz.1.1
    have hzp1 : z.1 < 1 := hz.1.2.trans_lt hb1
    have hqz0 : 0 ≤ 1 - z.2 := by linarith [hz.2.2]
    have hqzq : 1 - z.2 ≤ q := by dsimp [q]; linarith [hz.2.1]
    let pI : I := ⟨z.1, hzp0.le, hzp1.le⟩
    have hpolyEq : cubicClusterSizePolynomial d n z.1 =
        finiteClusterSizeProbability d pI n :=
      cubicClusterSizePolynomial_eq_probability d n pI
    have hpolyAbs : |cubicClusterSizePolynomial d n z.1| ≤ 1 := by
      rw [hpolyEq, abs_of_nonneg (finiteClusterSizeProbability_nonneg d pI n)]
      exact finiteClusterSizeProbability_le_one d pI n
    have hpowpred : (1 - z.2) ^ (n - 1) ≤ q ^ (n - 1) :=
      pow_le_pow_left₀ hqz0 hqzq _
    have heq : (n : ℝ) * q ^ (n - 1) = q⁻¹ * n * q ^ n := by
      rw [natCast_mul_pow_pred_eq_pow_mul_div n hq0.ne']
      field_simp
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_of_nonneg hqz0,
      abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    calc
      (n : ℝ) * (1 - z.2) ^ (n - 1) * |cubicClusterSizePolynomial d n z.1| ≤
          (n : ℝ) * q ^ (n - 1) * 1 := by
        gcongr
      _ = u n := by rw [heq]; simp [u]
  unfold ghostThetaGammaDerivativeSeries
  exact continuousOn_tsum hterms hu hbound

private theorem ghostThetaPSeries_deriv_nonneg
    (d : ℕ) (p γ : I) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hγ0 : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1) :
    0 ≤ deriv (ghostThetaPSeries d γ) p := by
  have hlim := torusGhostTheta_pDeriv_tendsto d p γ hp0 hp1 hγ0 hγ1
  apply ge_of_tendsto hlim
  filter_upwards with N
  have heq := one_sub_mul_torusGhostThetaPDerivative_eq_sum_closedPivotal
    d (N + 2) (by omega) p γ
  have hsum : 0 ≤ ∑ e ∈ cubicTorusEdgeFinset d (N + 2) (by omega),
      finiteBernoulliProbabilityFamily (torusGhostCoordinateFinset d (N + 2) (by omega))
        (torusGhostCoordinateDensity p γ)
        (torusGhostClosedPivotalJointTrace d (N + 2) e) := by
    exact Finset.sum_nonneg fun e _ ↦ finiteBernoulliProbabilityFamily_nonneg
      (torusGhostCoordinateDensity_nonneg p γ)
      (torusGhostCoordinateDensity_le_one p γ) _
  rw [← heq] at hsum
  nlinarith

private theorem ghostThetaGammaDerivativeSeries_nonneg
    (d : ℕ) {z : ℝ × ℝ} (hp0 : 0 < z.1) (hp1 : z.1 < 1)
    (hγ1 : z.2 < 1) :
    0 ≤ ghostThetaGammaDerivativeSeries d z := by
  let pI : I := ⟨z.1, hp0.le, hp1.le⟩
  unfold ghostThetaGammaDerivativeSeries
  apply tsum_nonneg
  intro n
  rw [show z.1 = (pI : ℝ) by rfl,
    cubicClusterSizePolynomial_eq_probability d n pI]
  exact mul_nonneg
    (mul_nonneg (Nat.cast_nonneg n) (pow_nonneg (sub_pos.mpr hγ1).le _))
    (finiteClusterSizeProbability_nonneg d pI n)

private theorem ghostThetaPSeries_mono_p
    (d : ℕ) {a b γ : ℝ} (ha0 : 0 < a) (hb1 : b < 1)
    (hγ0 : 0 < γ) (hγ1 : γ < 1) (hab : a ≤ b) :
    ghostThetaPSeries d γ a ≤ ghostThetaPSeries d γ b := by
  have hcont : ContinuousOn (ghostThetaPSeries d γ) (Icc a b) := by
    intro p hp
    exact (ghostThetaPSeries_hasDerivAt d (ha0.trans_le hp.1)
      (hp.2.trans_lt hb1) hγ0 hγ1).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ (ghostThetaPSeries d γ) (interior (Icc a b)) := by
    rw [interior_Icc]
    intro p hp
    exact (ghostThetaPSeries_hasDerivAt d (ha0.trans hp.1)
      (hp.2.trans hb1) hγ0 hγ1).differentiableAt.differentiableWithinAt
  have hnonneg : ∀ p ∈ interior (Icc a b), 0 ≤ deriv (ghostThetaPSeries d γ) p := by
    rw [interior_Icc]
    intro p hp
    let pI : I := ⟨p, (ha0.trans hp.1).le, (hp.2.trans hb1).le⟩
    let γI : I := ⟨γ, hγ0.le, hγ1.le⟩
    exact ghostThetaPSeries_deriv_nonneg d pI γI
      (ha0.trans hp.1) (hp.2.trans hb1) hγ0 hγ1
  exact (monotoneOn_of_deriv_nonneg (convex_Icc a b) hcont hdiff hnonneg)
    (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab) hab

private theorem ghostThetaPSeries_mono_gamma
    (d : ℕ) {p δ ε : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hδ0 : 0 < δ) (hε1 : ε < 1) (hδε : δ ≤ ε) :
    ghostThetaPSeries d δ p ≤ ghostThetaPSeries d ε p := by
  let pI : I := ⟨p, hp0.le, hp1.le⟩
  have hfun : (fun γ : ℝ ↦ ghostThetaPSeries d γ p) = ghostThetaSeries d pI := by
    funext γ
    unfold ghostThetaPSeries ghostThetaSeries
    congr 2
    funext n
    rw [show p = (pI : ℝ) by rfl, cubicClusterSizePolynomial_eq_probability d n pI]
  change (fun γ : ℝ ↦ ghostThetaPSeries d γ p) δ ≤
    (fun γ : ℝ ↦ ghostThetaPSeries d γ p) ε
  rw [hfun]
  have hcont : ContinuousOn (ghostThetaSeries d pI) (Icc δ ε) := by
    intro γ hγ
    exact (ghostThetaSeries_hasDerivAt d pI (hδ0.trans_le hγ.1)
      (hγ.2.trans_lt hε1)).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ (ghostThetaSeries d pI) (interior (Icc δ ε)) := by
    rw [interior_Icc]
    intro γ hγ
    exact (ghostThetaSeries_hasDerivAt d pI (hδ0.trans hγ.1)
      (hγ.2.trans hε1)).differentiableAt.differentiableWithinAt
  have hnonneg : ∀ γ ∈ interior (Icc δ ε),
      0 ≤ deriv (ghostThetaSeries d pI) γ := by
    rw [interior_Icc]
    intro γ hγ
    have hγ0 := hδ0.trans hγ.1
    have hγ1 := hγ.2.trans hε1
    have hsep := ghostThetaSeries_hasDerivAt d pI hγ0 hγ1
    rw [hsep.deriv]
    exact tsum_nonneg fun n ↦ mul_nonneg
      (mul_nonneg (Nat.cast_nonneg n) (pow_nonneg (sub_pos.mpr hγ1).le _))
      (finiteClusterSizeProbability_nonneg d pI n)
  exact (monotoneOn_of_deriv_nonneg (convex_Icc δ ε) hcont hdiff hnonneg)
    (left_mem_Icc.mpr hδε) (right_mem_Icc.mpr hδε) hδε

private noncomputable def ghostRectangleTheta (d : ℕ) (z : ℝ × ℝ) : ℝ :=
  ghostThetaPSeries d z.2 z.1

private noncomputable def ghostRectanglePField (d : ℕ) (z : ℝ × ℝ) : ℝ :=
  (z.1 * ghostRectangleTheta d z - z.1) / z.2

private noncomputable def ghostRectangleGammaField (d : ℕ) (z : ℝ × ℝ) : ℝ :=
  Real.log (ghostRectangleTheta d z)

private theorem ghostRectangleTheta_hasFDerivAt (d : ℕ) {z : ℝ × ℝ}
    (hp0 : 0 < z.1) (hp1 : z.1 < 1) (hγ0 : 0 < z.2) (hγ1 : z.2 < 1) :
    HasFDerivAt (ghostRectangleTheta d)
      (∑' n : ℕ, ghostThetaJointTermFDeriv d n z) z := by
  exact ghostThetaJoint_hasFDerivAt d hp0 hp1 hγ0 hγ1

private theorem ghostRectanglePField_hasFDerivAt (d : ℕ) {z : ℝ × ℝ}
    (hp0 : 0 < z.1) (hp1 : z.1 < 1) (hγ0 : 0 < z.2) (hγ1 : z.2 < 1) :
    HasFDerivAt (ghostRectanglePField d) (fderiv ℝ (ghostRectanglePField d) z) z := by
  have htheta := ghostRectangleTheta_hasFDerivAt d hp0 hp1 hγ0 hγ1
  have hfst : HasFDerivAt Prod.fst (ContinuousLinearMap.fst ℝ ℝ ℝ) z := hasFDerivAt_fst
  have hsnd : HasFDerivAt Prod.snd (ContinuousLinearMap.snd ℝ ℝ ℝ) z := hasFDerivAt_snd
  have hnum := (hfst.mul htheta).sub hfst
  have hinvBase : HasFDerivAt (fun y : ℝ ↦ y⁻¹)
      (ContinuousLinearMap.toSpanSingleton ℝ (-(z.2 ^ 2)⁻¹)) z.2 :=
    (hasDerivAt_inv hγ0.ne').hasFDerivAt
  have hinv := hinvBase.comp z hsnd
  have hfield := hnum.mul hinv
  change HasFDerivAt (ghostRectanglePField d) _ z at hfield
  rw [hfield.fderiv]
  exact hfield

private theorem ghostRectangleGammaField_hasFDerivAt (d : ℕ) {z : ℝ × ℝ}
    (hp0 : 0 < z.1) (hp1 : z.1 < 1) (hγ0 : 0 < z.2) (hγ1 : z.2 < 1)
    (htheta : 0 < ghostRectangleTheta d z) :
    HasFDerivAt (ghostRectangleGammaField d)
      (fderiv ℝ (ghostRectangleGammaField d) z) z := by
  have hbase := ghostRectangleTheta_hasFDerivAt d hp0 hp1 hγ0 hγ1
  have hlog : HasFDerivAt Real.log
      (ContinuousLinearMap.toSpanSingleton ℝ (ghostRectangleTheta d z)⁻¹)
      (ghostRectangleTheta d z) := (Real.hasDerivAt_log htheta.ne').hasFDerivAt
  have hfield0 := hlog.comp z hbase
  change HasFDerivAt (ghostRectangleGammaField d) _ z at hfield0
  rw [hfield0.fderiv]
  exact hfield0

private theorem ghostRectanglePField_fderiv_fst (d : ℕ) {z : ℝ × ℝ}
    (hp0 : 0 < z.1) (hp1 : z.1 < 1) (hγ0 : 0 < z.2) (hγ1 : z.2 < 1) :
    fderiv ℝ (ghostRectanglePField d) z (1, 0) =
      (ghostRectangleTheta d z + z.1 * deriv (ghostThetaPSeries d z.2) z.1 - 1) / z.2 := by
  have htheta := ghostRectangleTheta_hasFDerivAt d hp0 hp1 hγ0 hγ1
  have hfst : HasFDerivAt Prod.fst (ContinuousLinearMap.fst ℝ ℝ ℝ) z := hasFDerivAt_fst
  have hsnd : HasFDerivAt Prod.snd (ContinuousLinearMap.snd ℝ ℝ ℝ) z := hasFDerivAt_snd
  have hnum := (hfst.mul htheta).sub hfst
  have hinvBase : HasFDerivAt (fun y : ℝ ↦ y⁻¹)
      (ContinuousLinearMap.toSpanSingleton ℝ (-(z.2 ^ 2)⁻¹)) z.2 :=
    (hasDerivAt_inv hγ0.ne').hasFDerivAt
  have hinv := hinvBase.comp z hsnd
  have hfield := hnum.mul hinv
  change HasFDerivAt (ghostRectanglePField d) _ z at hfield
  rw [hfield.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply]
  rw [ghostThetaJointFDeriv_apply_fst d hp0 hp1 hγ0 hγ1]
  simp [ghostRectangleTheta]
  field_simp
  ring

private theorem ghostRectangleGammaField_fderiv_snd (d : ℕ) {z : ℝ × ℝ}
    (hp0 : 0 < z.1) (hp1 : z.1 < 1) (hγ0 : 0 < z.2) (hγ1 : z.2 < 1)
    (htheta : 0 < ghostRectangleTheta d z) :
    fderiv ℝ (ghostRectangleGammaField d) z (0, 1) =
      ghostThetaGammaDerivativeSeries d z / ghostRectangleTheta d z := by
  have hbase := ghostRectangleTheta_hasFDerivAt d hp0 hp1 hγ0 hγ1
  have hlog : HasFDerivAt Real.log
      (ContinuousLinearMap.toSpanSingleton ℝ (ghostRectangleTheta d z)⁻¹)
      (ghostRectangleTheta d z) := (Real.hasDerivAt_log htheta.ne').hasFDerivAt
  have hfield0 := hlog.comp z hbase
  change HasFDerivAt (ghostRectangleGammaField d) _ z at hfield0
  rw [hfield0.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply]
  rw [ghostThetaJointFDeriv_apply_snd_eq_series d hp0 hp1 hγ0 hγ1]
  simp [ghostRectangleTheta, div_eq_mul_inv, mul_comm]

/-- The integral of (5.57) over a compact rectangle, before estimating the boundary terms. -/
private theorem ghostRectangle_divergence_nonneg
    (d : ℕ) {a b δ ε : ℝ} (ha0 : 0 < a) (hb1 : b < 1) (hab : a ≤ b)
    (hδ0 : 0 < δ) (hε1 : ε < 1) (hδε : δ ≤ ε)
    (hpos : ∀ z ∈ Icc a b ×ˢ Icc δ ε, 0 < ghostRectangleTheta d z) :
    0 ≤ ((∫ p in a..b, ghostRectangleGammaField d (p, ε)) -
          ∫ p in a..b, ghostRectangleGammaField d (p, δ)) +
        (∫ γ in δ..ε, ghostRectanglePField d (b, γ)) -
          ∫ γ in δ..ε, ghostRectanglePField d (a, γ) := by
  let R := Icc a b ×ˢ Icc δ ε
  have hFcont : ContinuousOn (ghostRectangleTheta d) R := by
    intro z hz
    exact (ghostRectangleTheta_hasFDerivAt d (ha0.trans_le hz.1.1)
      (hz.1.2.trans_lt hb1) (hδ0.trans_le hz.2.1)
      (hz.2.2.trans_lt hε1)).continuousAt.continuousWithinAt
  have hPcont : ContinuousOn (ghostRectanglePField d) R := by
    intro z hz
    exact (ghostRectanglePField_hasFDerivAt d (ha0.trans_le hz.1.1)
      (hz.1.2.trans_lt hb1) (hδ0.trans_le hz.2.1)
      (hz.2.2.trans_lt hε1)).continuousAt.continuousWithinAt
  have hGcont : ContinuousOn (ghostRectangleGammaField d) R := by
    intro z hz
    exact (ghostRectangleGammaField_hasFDerivAt d (ha0.trans_le hz.1.1)
      (hz.1.2.trans_lt hb1) (hδ0.trans_le hz.2.1)
      (hz.2.2.trans_lt hε1) (hpos z hz)).continuousAt.continuousWithinAt
  have hDPcont := continuousOn_ghostThetaPDerivativeSeries_rectangle
    d ha0 hb1 hδ0 hε1 hδε
  have hDGcont := continuousOn_ghostThetaGammaDerivativeSeries_rectangle
    d ha0 hb1 hδ0 hε1 hδε
  let Q : ℝ × ℝ → ℝ := fun z ↦
    (ghostRectangleTheta d z + z.1 * ghostThetaPDerivativeSeries d z.2 z.1 - 1) / z.2 +
      ghostThetaGammaDerivativeSeries d z / ghostRectangleTheta d z
  have hQcont : ContinuousOn Q R := by
    have hnum : ContinuousOn (fun z : ℝ × ℝ ↦
        ghostRectangleTheta d z + z.1 * ghostThetaPDerivativeSeries d z.2 z.1 - 1) R :=
      (hFcont.add (continuousOn_fst.mul hDPcont)).sub continuousOn_const
    exact (hnum.div continuousOn_snd (fun z hz ↦ (hδ0.trans_le hz.2.1).ne')).add
      (hDGcont.div hFcont fun z hz ↦ (hpos z hz).ne')
  have hdivEq : EqOn (fun z : ℝ × ℝ ↦
      fderiv ℝ (ghostRectanglePField d) z (1, 0) +
        fderiv ℝ (ghostRectangleGammaField d) z (0, 1)) Q R := by
    intro z hz
    change fderiv ℝ (ghostRectanglePField d) z (1, 0) +
      fderiv ℝ (ghostRectangleGammaField d) z (0, 1) = Q z
    rw [ghostRectanglePField_fderiv_fst d (ha0.trans_le hz.1.1)
      (hz.1.2.trans_lt hb1) (hδ0.trans_le hz.2.1) (hz.2.2.trans_lt hε1),
      ghostRectangleGammaField_fderiv_snd d (ha0.trans_le hz.1.1)
        (hz.1.2.trans_lt hb1) (hδ0.trans_le hz.2.1) (hz.2.2.trans_lt hε1)
        (hpos z hz)]
    rw [(ghostThetaPSeries_hasDerivAt d (ha0.trans_le hz.1.1)
      (hz.1.2.trans_lt hb1) (hδ0.trans_le hz.2.1)
      (hz.2.2.trans_lt hε1)).deriv]
  have hQint : IntegrableOn Q R :=
    hQcont.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hDivInt : IntegrableOn (fun z : ℝ × ℝ ↦
      fderiv ℝ (ghostRectanglePField d) z (1, 0) +
        fderiv ℝ (ghostRectangleGammaField d) z (0, 1)) R :=
    hQint.congr_fun hdivEq.symm (measurableSet_Icc.prod measurableSet_Icc)
  have hdiv := integral2_divergence_prod_of_hasFDerivAt
    (ghostRectanglePField d) (ghostRectangleGammaField d)
    (fun z ↦ fderiv ℝ (ghostRectanglePField d) z)
    (fun z ↦ fderiv ℝ (ghostRectangleGammaField d) z)
    a δ b ε (by
      simpa only [uIcc_of_le hab, uIcc_of_le hδε, ← Icc_prod_Icc] using hPcont)
    (by simpa only [uIcc_of_le hab, uIcc_of_le hδε, ← Icc_prod_Icc] using hGcont) (by
      intro z hz
      simp only [min_eq_left hab, max_eq_right hab,
        min_eq_left hδε, max_eq_right hδε] at hz
      exact ghostRectanglePField_hasFDerivAt d (ha0.trans hz.1.1)
        (hz.1.2.trans hb1) (hδ0.trans hz.2.1) (hz.2.2.trans hε1)) (by
      intro z hz
      simp only [min_eq_left hab, max_eq_right hab,
        min_eq_left hδε, max_eq_right hδε] at hz
      exact ghostRectangleGammaField_hasFDerivAt d (ha0.trans hz.1.1)
        (hz.1.2.trans hb1) (hδ0.trans hz.2.1) (hz.2.2.trans hε1)
        (hpos z ⟨Ioo_subset_Icc_self hz.1, Ioo_subset_Icc_self hz.2⟩)) (by
      simpa only [uIcc_of_le hab, uIcc_of_le hδε, ← Icc_prod_Icc] using hDivInt)
  rw [← hdiv]
  apply intervalIntegral.integral_nonneg hab
  intro p hp
  apply intervalIntegral.integral_nonneg hδε
  intro γ hγ
  let pI : I := ⟨p, (ha0.trans_le hp.1).le, (hp.2.trans_lt hb1).le⟩
  let γI : I := ⟨γ, (hδ0.trans_le hγ.1).le, (hγ.2.trans_lt hε1).le⟩
  let z : ℝ × ℝ := (p, γ)
  have hz : z ∈ R := ⟨hp, hγ⟩
  have hp0 : 0 < p := ha0.trans_le hp.1
  have hp1 : p < 1 := hp.2.trans_lt hb1
  have hγ0 : 0 < γ := hδ0.trans_le hγ.1
  have hγ1 : γ < 1 := hγ.2.trans_lt hε1
  have hthetaPos := hpos z hz
  have hthetaEq : ghostRectangleTheta d z = ghostTheta d pI γI := by
    calc
      ghostRectangleTheta d z = ghostThetaSeries d pI γ := by
        exact ghostThetaPSeries_eq_ghostThetaSeries d pI γI
      _ = ghostTheta d pI γI := (ghostTheta_eq_ghostThetaSeries d pI γI hγ0).symm
  have hDPEq : ghostThetaPDerivativeSeries d γ p =
      deriv (ghostThetaPSeries d γ) p :=
    ghostThetaPSeries_hasDerivAt d hp0 hp1 hγ0 hγ1 |>.deriv.symm
  have hDGEq : ghostThetaGammaDerivativeSeries d z =
      deriv (ghostThetaSeries d pI) γ := by
    have hsep := ghostThetaSeries_hasDerivAt d pI hγ0 hγ1
    rw [hsep.deriv]
    unfold ghostThetaGammaDerivativeSeries
    apply tsum_congr
    intro n
    dsimp [z]
    rw [show p = (pI : ℝ) by rfl,
      cubicClusterSizePolynomial_eq_probability d n pI]
  have h53 := ghostTheta_le_differential d pI γI hp0 hp1 hγ0 hγ1
  rw [← hthetaEq, ← hDPEq, ← hDGEq] at h53
  change 0 ≤ (fun z : ℝ × ℝ ↦
    fderiv ℝ (ghostRectanglePField d) z (1, 0) +
      fderiv ℝ (ghostRectangleGammaField d) z (0, 1)) z
  rw [hdivEq hz]
  have hformula : Q z =
      (γ * ghostThetaGammaDerivativeSeries d z +
        ghostRectangleTheta d z *
          (ghostRectangleTheta d z + p * ghostThetaPDerivativeSeries d γ p - 1)) /
        (γ * ghostRectangleTheta d z) := by
    have htne : ghostRectangleTheta d (p, γ) ≠ 0 := by
      simpa [z] using hthetaPos.ne'
    dsimp [Q, z]
    field_simp [htne]
    ring
  rw [hformula]
  exact div_nonneg (by nlinarith) (mul_nonneg hγ0.le hthetaPos.le)

/-- Grimmett (5.57) integrated over the rectangle and bounded by its corner values. -/
private theorem ghostRectangle_integrated_inequality
    (d : ℕ) {a b δ ε : ℝ} (ha0 : 0 < a) (hb1 : b < 1) (hab : a ≤ b)
    (hδ0 : 0 < δ) (hε1 : ε < 1) (hδε : δ ≤ ε)
    (hpos : ∀ z ∈ Icc a b ×ˢ Icc δ ε, 0 < ghostRectangleTheta d z) :
    0 ≤ (b - a) * Real.log
          (ghostRectangleTheta d (b, ε) / ghostRectangleTheta d (a, δ)) +
        (b * ghostRectangleTheta d (b, ε) - b + a) * Real.log (ε / δ) := by
  have hε0 : 0 < ε := hδ0.trans_le hδε
  have hb0 : 0 < b := ha0.trans_le hab
  have hbase := ghostRectangle_divergence_nonneg d ha0 hb1 hab hδ0 hε1 hδε hpos
  have hGEcont : ContinuousOn (fun p ↦ ghostRectangleGammaField d (p, ε)) (Icc a b) := by
    intro p hp
    have hf := ghostThetaPSeries_hasDerivAt d (ha0.trans_le hp.1)
      (hp.2.trans_lt hb1) hε0 hε1
    have hlog := Real.hasDerivAt_log
      (hpos (p, ε) ⟨hp, right_mem_Icc.mpr hδε⟩).ne'
    exact (hlog.comp p hf).continuousAt.continuousWithinAt
  have hGDcont : ContinuousOn (fun p ↦ ghostRectangleGammaField d (p, δ)) (Icc a b) := by
    intro p hp
    have hf := ghostThetaPSeries_hasDerivAt d (ha0.trans_le hp.1)
      (hp.2.trans_lt hb1) hδ0 (hδε.trans_lt hε1)
    have hlog := Real.hasDerivAt_log
      (hpos (p, δ) ⟨hp, left_mem_Icc.mpr hδε⟩).ne'
    exact (hlog.comp p hf).continuousAt.continuousWithinAt
  have hGEint : IntervalIntegrable (fun p ↦ ghostRectangleGammaField d (p, ε))
      volume a b := hGEcont.intervalIntegrable_of_Icc hab
  have hGDint : IntervalIntegrable (fun p ↦ ghostRectangleGammaField d (p, δ))
      volume a b := hGDcont.intervalIntegrable_of_Icc hab
  have hGEle : ∀ p ∈ Icc a b,
      ghostRectangleGammaField d (p, ε) ≤ ghostRectangleGammaField d (b, ε) := by
    intro p hp
    apply Real.strictMonoOn_log.monotoneOn
    · exact hpos (p, ε) ⟨hp, right_mem_Icc.mpr hδε⟩
    · exact hpos (b, ε) ⟨right_mem_Icc.mpr hab, right_mem_Icc.mpr hδε⟩
    · exact ghostThetaPSeries_mono_p d (ha0.trans_le hp.1) hb1 hε0 hε1 hp.2
  have hGDge : ∀ p ∈ Icc a b,
      ghostRectangleGammaField d (a, δ) ≤ ghostRectangleGammaField d (p, δ) := by
    intro p hp
    apply Real.strictMonoOn_log.monotoneOn
    · exact hpos (a, δ) ⟨left_mem_Icc.mpr hab, left_mem_Icc.mpr hδε⟩
    · exact hpos (p, δ) ⟨hp, left_mem_Icc.mpr hδε⟩
    · exact ghostThetaPSeries_mono_p d ha0 (hp.2.trans_lt hb1) hδ0
        (hδε.trans_lt hε1) hp.1
  have hGEbound : (∫ p in a..b, ghostRectangleGammaField d (p, ε)) ≤
      (b - a) * ghostRectangleGammaField d (b, ε) := by
    have hconst : IntervalIntegrable (fun _ : ℝ ↦ ghostRectangleGammaField d (b, ε))
        volume a b := continuousOn_const.intervalIntegrable_of_Icc hab
    have h := intervalIntegral.integral_mono_on hab hGEint hconst hGEle
    simpa [mul_comm] using h
  have hGDbound : (b - a) * ghostRectangleGammaField d (a, δ) ≤
      ∫ p in a..b, ghostRectangleGammaField d (p, δ) := by
    have hconst : IntervalIntegrable (fun _ : ℝ ↦ ghostRectangleGammaField d (a, δ))
        volume a b := continuousOn_const.intervalIntegrable_of_Icc hab
    have h := intervalIntegral.integral_mono_on hab hconst hGDint hGDge
    simpa [mul_comm] using h
  have hlogBound :
      (∫ p in a..b, ghostRectangleGammaField d (p, ε)) -
          ∫ p in a..b, ghostRectangleGammaField d (p, δ) ≤
        (b - a) * Real.log
          (ghostRectangleTheta d (b, ε) / ghostRectangleTheta d (a, δ)) := by
    rw [Real.log_div
      (hpos (b, ε) ⟨right_mem_Icc.mpr hab, right_mem_Icc.mpr hδε⟩).ne'
      (hpos (a, δ) ⟨left_mem_Icc.mpr hab, left_mem_Icc.mpr hδε⟩).ne']
    dsimp [ghostRectangleGammaField] at hGEbound hGDbound ⊢
    nlinarith
  have hXBcont : ContinuousOn (fun γ ↦ ghostRectanglePField d (b, γ)) (Icc δ ε) := by
    intro γ hγ
    let bI : I := ⟨b, hb0.le, hb1.le⟩
    have hfun : (fun y : ℝ ↦ ghostThetaPSeries d y b) = ghostThetaSeries d bI := by
      funext y
      unfold ghostThetaPSeries ghostThetaSeries
      congr 2
      funext n
      rw [show b = (bI : ℝ) by rfl, cubicClusterSizePolynomial_eq_probability d n bI]
    have hf : ContinuousAt (fun y : ℝ ↦ ghostThetaPSeries d y b) γ := by
      rw [hfun]
      exact (ghostThetaSeries_hasDerivAt d bI (hδ0.trans_le hγ.1)
        (hγ.2.trans_lt hε1)).continuousAt
    exact (((continuousAt_const.mul hf).sub continuousAt_const).div continuousAt_id
      (hδ0.trans_le hγ.1).ne').continuousWithinAt
  have hXAcont : ContinuousOn (fun γ ↦ ghostRectanglePField d (a, γ)) (Icc δ ε) := by
    intro γ hγ
    let aI : I := ⟨a, ha0.le, (hab.trans_lt hb1).le⟩
    have hfun : (fun y : ℝ ↦ ghostThetaPSeries d y a) = ghostThetaSeries d aI := by
      funext y
      unfold ghostThetaPSeries ghostThetaSeries
      congr 2
      funext n
      rw [show a = (aI : ℝ) by rfl, cubicClusterSizePolynomial_eq_probability d n aI]
    have hf : ContinuousAt (fun y : ℝ ↦ ghostThetaPSeries d y a) γ := by
      rw [hfun]
      exact (ghostThetaSeries_hasDerivAt d aI (hδ0.trans_le hγ.1)
        (hγ.2.trans_lt hε1)).continuousAt
    exact (((continuousAt_const.mul hf).sub continuousAt_const).div continuousAt_id
      (hδ0.trans_le hγ.1).ne').continuousWithinAt
  have hXBint : IntervalIntegrable (fun γ ↦ ghostRectanglePField d (b, γ))
      volume δ ε := hXBcont.intervalIntegrable_of_Icc hδε
  have hXAint : IntervalIntegrable (fun γ ↦ ghostRectanglePField d (a, γ))
      volume δ ε := hXAcont.intervalIntegrable_of_Icc hδε
  let c := b * ghostRectangleTheta d (b, ε) - b + a
  have hInvInt : IntervalIntegrable (fun γ : ℝ ↦ c / γ) volume δ ε := by
    apply ContinuousOn.intervalIntegrable_of_Icc hδε
    exact continuousOn_const.div continuousOn_id fun γ hγ ↦ (hδ0.trans_le hγ.1).ne'
  have hXpoint : ∀ γ ∈ Icc δ ε,
      ghostRectanglePField d (b, γ) - ghostRectanglePField d (a, γ) ≤ c / γ := by
    intro γ hγ
    have hγ0 := hδ0.trans_le hγ.1
    have hbmono := ghostThetaPSeries_mono_gamma d hb0 hb1
      (hδ0.trans_le hγ.1) hε1 hγ.2
    have haTheta := hpos (a, γ) ⟨left_mem_Icc.mpr hab, hγ⟩
    have hbmono' : ghostRectangleTheta d (b, γ) ≤
        ghostRectangleTheta d (b, ε) := by
      simpa [ghostRectangleTheta] using hbmono
    have hbmul := mul_le_mul_of_nonneg_left hbmono' hb0.le
    have hamul : 0 ≤ a * ghostRectangleTheta d (a, γ) :=
      mul_nonneg ha0.le haTheta.le
    dsimp [ghostRectanglePField, c]
    rw [← sub_div]
    apply (div_le_div_iff_of_pos_right hγ0).mpr
    linarith
  have hXbound :
      (∫ γ in δ..ε, ghostRectanglePField d (b, γ)) -
          ∫ γ in δ..ε, ghostRectanglePField d (a, γ) ≤
        c * Real.log (ε / δ) := by
    rw [← intervalIntegral.integral_sub hXBint hXAint]
    have hsubInt : IntervalIntegrable
        (fun γ ↦ ghostRectanglePField d (b, γ) - ghostRectanglePField d (a, γ))
        volume δ ε := hXBint.sub hXAint
    have hmono := intervalIntegral.integral_mono_on hδε hsubInt hInvInt hXpoint
    calc
      _ ≤ ∫ γ in δ..ε, c / γ := hmono
      _ = c * ∫ γ in δ..ε, γ⁻¹ := by
        rw [← intervalIntegral.integral_const_mul]
        congr 1
      _ = c * Real.log (ε / δ) := by rw [integral_inv_of_pos hδ0 hε0]
  dsimp [c] at hXbound
  exact hbase.trans (by linarith)

private theorem ghostLogRatioUpper_tendsto (α ε : ℝ) :
    Tendsto (fun δ : ℝ ↦ (1 / 2 : ℝ) +
      (-Real.log α - Real.log ε / 2) / (Real.log ε - Real.log δ))
      (nhdsWithin 0 (Ioi 0)) (nhds (1 / 2 : ℝ)) := by
  have hlog := Real.tendsto_log_nhdsGT_zero
  have hneg : Tendsto (fun δ : ℝ ↦ -Real.log δ) (nhdsWithin 0 (Ioi 0)) atTop := by
    simpa [Function.comp_def] using tendsto_neg_atBot_atTop.comp hlog
  have hden : Tendsto (fun δ : ℝ ↦ Real.log ε - Real.log δ)
      (nhdsWithin 0 (Ioi 0)) atTop := by
    simpa [sub_eq_add_neg] using
      tendsto_atTop_add_const_left (nhdsWithin 0 (Ioi 0)) (Real.log ε) hneg
  have hc : Tendsto (fun _ : ℝ ↦ (1 / 2 : ℝ)) (nhdsWithin 0 (Ioi 0))
      (nhds (1 / 2 : ℝ)) := tendsto_const_nhds
  simpa using hc.add (hden.const_div_atTop (-Real.log α - Real.log ε / 2))

private theorem ghostRectangle_half_inequality
    (d : ℕ) {a b ε α γ₀ : ℝ}
    (ha0 : 0 < a) (hb1 : b < 1) (hab : a ≤ b)
    (hε0 : 0 < ε) (hε1 : ε < 1) (hεγ₀ : ε < γ₀) (hα0 : 0 < α)
    (hsqrt : ∀ γ : I, 0 < (γ : ℝ) → (γ : ℝ) < γ₀ →
      α * Real.sqrt (γ : ℝ) ≤ ghostTheta d ⟨a, ha0.le, (hab.trans_lt hb1).le⟩ γ) :
    0 ≤ (b - a) / 2 + b * ghostRectangleTheta d (b, ε) - b + a := by
  let U : ℝ → ℝ := fun δ ↦ (b - a) * ((1 / 2 : ℝ) +
      (-Real.log α - Real.log ε / 2) / (Real.log ε - Real.log δ)) +
    (b * ghostRectangleTheta d (b, ε) - b + a)
  have hγ₀0 : 0 < γ₀ := hε0.trans hεγ₀
  have hevent : ∀ᶠ δ : ℝ in nhdsWithin 0 (Ioi 0), 0 ≤ U δ := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (lt_min hε0 hγ₀0)).filter_mono inf_le_left] with δ hδ0 hδsmall
    simp only [mem_Ioi] at hδ0
    have hδε : δ ≤ ε := (hδsmall.trans_le (min_le_left _ _)).le
    have hδγ₀ : δ < γ₀ := hδsmall.trans_le (min_le_right _ _)
    have hpos : ∀ z ∈ Icc a b ×ˢ Icc δ ε, 0 < ghostRectangleTheta d z := by
      intro z hz
      let aI : I := ⟨a, ha0.le, (hab.trans_lt hb1).le⟩
      let γI : I := ⟨z.2, (hδ0.trans_le hz.2.1).le,
        (hz.2.2.trans_lt hε1).le⟩
      have hγ0 : 0 < z.2 := hδ0.trans_le hz.2.1
      have hγγ₀ : z.2 < γ₀ := hz.2.2.trans_lt hεγ₀
      have hroot : 0 < α * Real.sqrt z.2 :=
        mul_pos hα0 (Real.sqrt_pos.2 hγ0)
      have haGhost : 0 < ghostTheta d aI γI :=
        hroot.trans_le (hsqrt γI hγ0 hγγ₀)
      have haEq : ghostRectangleTheta d (a, z.2) = ghostTheta d aI γI := by
        calc
          ghostRectangleTheta d (a, z.2) = ghostThetaSeries d aI z.2 :=
            ghostThetaPSeries_eq_ghostThetaSeries d aI γI
          _ = ghostTheta d aI γI :=
            (ghostTheta_eq_ghostThetaSeries d aI γI hγ0).symm
      have hmono := ghostThetaPSeries_mono_p d ha0 (hz.1.2.trans_lt hb1)
        hγ0 (hz.2.2.trans_lt hε1) hz.1.1
      have hmono' : ghostRectangleTheta d (a, z.2) ≤ ghostRectangleTheta d z := by
        simpa [ghostRectangleTheta] using hmono
      rw [haEq] at hmono'
      exact haGhost.trans_le hmono'
    have hrect := ghostRectangle_integrated_inequality d ha0 hb1 hab hδ0 hε1 hδε hpos
    let aI : I := ⟨a, ha0.le, (hab.trans_lt hb1).le⟩
    let bI : I := ⟨b, (ha0.trans_le hab).le, hb1.le⟩
    let δI : I := ⟨δ, hδ0.le, hδε.trans hε1.le⟩
    let εI : I := ⟨ε, hε0.le, hε1.le⟩
    have hFaEq : ghostRectangleTheta d (a, δ) = ghostTheta d aI δI := by
      calc
        ghostRectangleTheta d (a, δ) = ghostThetaSeries d aI δ :=
          ghostThetaPSeries_eq_ghostThetaSeries d aI δI
        _ = ghostTheta d aI δI := (ghostTheta_eq_ghostThetaSeries d aI δI hδ0).symm
    have hFbeEq : ghostRectangleTheta d (b, ε) = ghostTheta d bI εI := by
      calc
        ghostRectangleTheta d (b, ε) = ghostThetaSeries d bI ε :=
          ghostThetaPSeries_eq_ghostThetaSeries d bI εI
        _ = ghostTheta d bI εI := (ghostTheta_eq_ghostThetaSeries d bI εI hε0).symm
    have hroot : 0 < α * Real.sqrt δ := mul_pos hα0 (Real.sqrt_pos.2 hδ0)
    have hFaLower : α * Real.sqrt δ ≤ ghostRectangleTheta d (a, δ) := by
      rw [hFaEq]
      exact hsqrt δI hδ0 hδγ₀
    have hFaPos : 0 < ghostRectangleTheta d (a, δ) := hroot.trans_le hFaLower
    have hFbePos : 0 < ghostRectangleTheta d (b, ε) :=
      hpos (b, ε) ⟨right_mem_Icc.mpr hab, right_mem_Icc.mpr hδε⟩
    have hFbeOne : ghostRectangleTheta d (b, ε) ≤ 1 := by
      rw [hFbeEq]
      exact ghostTheta_le_one d bI εI
    have hratioLe : ghostRectangleTheta d (b, ε) / ghostRectangleTheta d (a, δ) ≤
        1 / (α * Real.sqrt δ) := by
      apply (div_le_div_iff₀ hFaPos hroot).mpr
      calc
        ghostRectangleTheta d (b, ε) * (α * Real.sqrt δ) ≤
            1 * (α * Real.sqrt δ) :=
          mul_le_mul_of_nonneg_right hFbeOne hroot.le
        _ ≤ 1 * ghostRectangleTheta d (a, δ) :=
          mul_le_mul_of_nonneg_left hFaLower zero_le_one
    have hratioPos : 0 < ghostRectangleTheta d (b, ε) /
        ghostRectangleTheta d (a, δ) := div_pos hFbePos hFaPos
    have hinvPos : 0 < 1 / (α * Real.sqrt δ) := one_div_pos.mpr hroot
    have hlogLe := Real.strictMonoOn_log.monotoneOn hratioPos hinvPos hratioLe
    have hlogInv : Real.log (1 / (α * Real.sqrt δ)) =
        -Real.log α - Real.log δ / 2 := by
      rw [one_div, Real.log_inv, Real.log_mul hα0.ne'
        (Real.sqrt_pos.2 hδ0).ne', Real.log_sqrt hδ0.le]
      ring
    rw [hlogInv] at hlogLe
    have hlogδε : Real.log δ < Real.log ε :=
      Real.strictMonoOn_log hδ0 hε0 (hδsmall.trans_le (min_le_left _ _))
    have hLpos : 0 < Real.log ε - Real.log δ := sub_pos.mpr hlogδε
    let L := Real.log ε - Real.log δ
    let B := b * ghostRectangleTheta d (b, ε) - b + a
    have hdivided : 0 ≤ (b - a) *
        (Real.log (ghostRectangleTheta d (b, ε) /
          ghostRectangleTheta d (a, δ)) / L) + B := by
      have hlogED : Real.log (ε / δ) = L := by
        dsimp [L]
        exact Real.log_div hε0.ne' hδ0.ne'
      rw [hlogED] at hrect
      change 0 ≤ (b - a) * Real.log
          (ghostRectangleTheta d (b, ε) / ghostRectangleTheta d (a, δ)) + B * L at hrect
      have hq := div_nonneg hrect hLpos.le
      have heq : ((b - a) * Real.log
            (ghostRectangleTheta d (b, ε) / ghostRectangleTheta d (a, δ)) +
          B * L) / L =
          (b - a) * (Real.log
            (ghostRectangleTheta d (b, ε) / ghostRectangleTheta d (a, δ)) / L) + B := by
        rw [add_div, mul_div_cancel_right₀ B hLpos.ne']
        ring
      rw [heq] at hq
      exact hq
    have hquot : Real.log (ghostRectangleTheta d (b, ε) /
          ghostRectangleTheta d (a, δ)) / L ≤
        (-Real.log α - Real.log δ / 2) / L :=
      (div_le_div_iff_of_pos_right hLpos).mpr hlogLe
    have hrewrite : (-Real.log α - Real.log δ / 2) / L =
        (1 / 2 : ℝ) +
          (-Real.log α - Real.log ε / 2) / (Real.log ε - Real.log δ) := by
      dsimp [L]
      field_simp [hLpos.ne']
      ring
    rw [hrewrite] at hquot
    have hscaled := mul_le_mul_of_nonneg_left hquot (sub_nonneg.mpr hab)
    dsimp [U, B]
    linarith
  have hU : Tendsto U (nhdsWithin 0 (Ioi 0))
      (nhds ((b - a) * (1 / 2 : ℝ) +
        (b * ghostRectangleTheta d (b, ε) - b + a))) := by
    dsimp [U]
    exact ((ghostLogRatioUpper_tendsto α ε).const_mul (b - a)).add tendsto_const_nhds
  have hlimit := ge_of_tendsto hU hevent
  nlinarith

private theorem ghostTheta_lower_bound_of_sqrt
    (d : ℕ) {a b α γ₀ : ℝ}
    (ha0 : 0 < a) (hb1 : b < 1) (hab : a < b)
    (hα0 : 0 < α) (hγ₀0 : 0 < γ₀)
    (hsqrt : ∀ γ : I, 0 < (γ : ℝ) → (γ : ℝ) < γ₀ →
      α * Real.sqrt (γ : ℝ) ≤ ghostTheta d ⟨a, ha0.le, hab.le.trans hb1.le⟩ γ) :
    (b - a) / (2 * b) ≤ theta d ⟨b, (ha0.trans hab).le, hb1.le⟩ := by
  let bI : I := ⟨b, (ha0.trans hab).le, hb1.le⟩
  let lower := (b - a) / (2 * b)
  have hb0 : 0 < b := ha0.trans hab
  have hevent : ∀ᶠ ε : ℝ in nhdsWithin 0 (Ioi 0),
      lower ≤ ghostRectangleTheta d (b, ε) := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (lt_min hγ₀0 zero_lt_one)).filter_mono inf_le_left] with ε hε0 hεsmall
    simp only [mem_Ioi] at hε0
    have hhalf := ghostRectangle_half_inequality d ha0 hb1 hab.le hε0
      (hεsmall.trans_le (min_le_right _ _))
      (hεsmall.trans_le (min_le_left _ _)) hα0 hsqrt
    dsimp [lower]
    apply (div_le_iff₀ (mul_pos (by norm_num) hb0)).mpr
    nlinarith
  have htendsto : Tendsto (fun ε : ℝ ↦ ghostRectangleTheta d (b, ε))
      (nhdsWithin 0 (Ioi 0)) (nhds (theta d bI)) := by
    have hfun : (fun ε : ℝ ↦ ghostRectangleTheta d (b, ε)) =
        ghostThetaSeries d bI := by
      funext ε
      unfold ghostRectangleTheta ghostThetaPSeries ghostThetaSeries
      congr 2
      funext n
      rw [show b = (bI : ℝ) by rfl, cubicClusterSizePolynomial_eq_probability d n bI]
    rw [hfun]
    exact ghostTheta_tendsto_theta d bI
  exact ge_of_tendsto htendsto hevent

/-- Grimmett, Theorem 5.48.  Infinite finite-cluster susceptibility forces either an infinite
cluster already at `p`, or the explicit linear lower bound at every larger density. -/
theorem finiteSusceptibility_eq_top_imp_theta_lower_bound
    (d : ℕ) (hd : 2 ≤ d) (p : I) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (htop : finiteSusceptibility d p = ⊤) :
    0 < theta d p ∨
      (theta d p = 0 ∧ ∀ p' : I, p ≤ p' →
        ((p' : ℝ) - (p : ℝ)) / (2 * (p' : ℝ)) ≤ theta d p') := by
  by_cases htheta : 0 < theta d p
  · exact Or.inl htheta
  right
  have htheta0 : theta d p = 0 :=
    le_antisymm (not_lt.mp htheta) MeasureTheory.measureReal_nonneg
  refine ⟨htheta0, ?_⟩
  obtain ⟨α, hα0, γ₀, hγ₀0, _hγ₀1, hsqrt⟩ :=
    ghostTheta_ge_sqrt d hd p hp0 hp1 htop
  intro p' hpp'
  by_cases heq : p' = p
  · subst p'
    simp only [sub_self, zero_div]
    exact MeasureTheory.measureReal_nonneg
  have hpp'lt : (p : ℝ) < (p' : ℝ) := by
    exact_mod_cast lt_of_le_of_ne hpp' (Ne.symm heq)
  by_cases hp'1 : (p' : ℝ) < 1
  · exact ghostTheta_lower_bound_of_sqrt d hp0 hp'1 hpp'lt hα0 hγ₀0 (by
      intro γ hγ0 hγγ₀
      simpa using hsqrt γ hγ0 hγγ₀)
  · have hp'Eq : (p' : ℝ) = 1 := le_antisymm p'.property.2 (not_lt.mp hp'1)
    let r := 1 - (p : ℝ)
    let b : ℕ → ℝ := fun n ↦ 1 - r / (n + 2 : ℝ)
    have hr0 : 0 < r := by dsimp [r]; linarith
    have hbound : ∀ n : ℕ,
        (b n - (p : ℝ)) / (2 * b n) ≤ theta d p' := by
      intro n
      have hn1 : (1 : ℝ) < n + 2 := by
        have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith
      have hfrac0 : 0 < r / (n + 2 : ℝ) := div_pos hr0 (by positivity)
      have hfracr : r / (n + 2 : ℝ) < r := div_lt_self hr0 hn1
      have hpb : (p : ℝ) < b n := by dsimp [b, r]; linarith
      have hb1 : b n < 1 := by dsimp [b]; linarith
      let bI : I := ⟨b n, p.property.1.trans hpb.le, hb1.le⟩
      have hbLower : (b n - (p : ℝ)) / (2 * b n) ≤ theta d bI :=
        ghostTheta_lower_bound_of_sqrt d hp0 hb1 hpb hα0 hγ₀0 (by
          intro γ hγ0 hγγ₀
          simpa using hsqrt γ hγ0 hγγ₀)
      have hbLe : bI ≤ p' := by
        exact_mod_cast hb1.le.trans_eq hp'Eq.symm
      exact hbLower.trans (theta_mono d hbLe)
    have hncast : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop
    have hden : Tendsto (fun n : ℕ ↦ (n + 2 : ℝ)) atTop atTop := by
      simpa using tendsto_atTop_add_const_right atTop 2 hncast
    have hfrac : Tendsto (fun n : ℕ ↦ r / (n + 2 : ℝ)) atTop (nhds 0) :=
      hden.const_div_atTop r
    have hbT : Tendsto b atTop (nhds 1) := by
      dsimp [b]
      simpa using tendsto_const_nhds.sub hfrac
    have hfcont : ContinuousAt (fun x : ℝ ↦ (x - (p : ℝ)) / (2 * x)) 1 := by
      exact (continuousAt_id.sub continuousAt_const).div
        (continuousAt_const.mul continuousAt_id) (by norm_num)
    have hfT : Tendsto (fun n : ℕ ↦ (b n - (p : ℝ)) / (2 * b n)) atTop
        (nhds ((1 - (p : ℝ)) / 2)) := by
      convert hfcont.tendsto.comp hbT using 1
      · norm_num
    have hlim : (1 - (p : ℝ)) / 2 ≤ theta d p' :=
      le_of_tendsto hfT (Filter.Eventually.of_forall hbound)
    rw [hp'Eq]
    norm_num at hlim ⊢
    exact hlim
