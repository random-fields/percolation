import Percolation.Critical.ExponentialDecay
import Percolation.Critical.RadiusBlock
import Percolation.Planar.Peierls
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Topology.Semicontinuity.Basic

/-!
# Right continuity of the percolation probability

Grimmett's proof of Theorem 5.8 uses the soft fact that `θ` is the decreasing infimum of the
finite-radius polynomials `gₚ(n)`.  Hence it is upper semicontinuous; monotonicity then implies
right continuity.
-/

namespace Percolation

open Filter
open MeasureTheory
open scoped unitInterval

/-- The critical probability as a point of the unit interval. -/
noncomputable def cubicCriticalProbabilityUnit (d : ℕ) (hd : 2 ≤ d) : I :=
  ⟨cubicCriticalProbability d,
    (one_div_pos.mpr (cubicConnectiveConstant_pos (by omega))).le.trans
      (connectiveConstant_inv_le_cubicCriticalProbability hd),
    cubicCriticalProbability_le_one d⟩

@[simp] theorem coe_cubicCriticalProbabilityUnit (d : ℕ) (hd : 2 ≤ d) :
    (cubicCriticalProbabilityUnit d hd : ℝ) = cubicCriticalProbability d := rfl

theorem continuous_radiusTail_density (d n : ℕ) :
    Continuous (fun p : I ↦ radiusTail d p n) := by
  have heq : (fun p : I ↦ radiusTail d p n) = fun p : I ↦
      finiteBernoulliProbability (cubicMetricBallEdges d cubicOrigin n) p
        (eventTrace (radiusConnectionEvent d cubicOrigin n)) := by
    funext p
    exact DependsOn.bernoulliBondMeasure_real_eq_finiteBernoulliProbability
      (dependsOn_radiusConnectionEvent d cubicOrigin n) p
  rw [heq]
  unfold finiteBernoulliProbability finiteBernoulliExpectation finiteBernoulliWeight
  fun_prop

/-- `θ(p)=infₙ gₚ(n)`. -/
theorem theta_eq_iInf_radiusTail (d : ℕ) (p : I) :
    theta d p = ⨅ n : ℕ, radiusTail d p n := by
  rw [← sInf_range]
  symm
  apply csInf_eq_of_forall_ge_of_forall_gt_exists_lt
  · exact Set.range_nonempty _
  · rintro _ ⟨n, rfl⟩
    apply le_of_tendsto (radiusTail_tendsto_theta d p)
    filter_upwards [eventually_ge_atTop n] with m hm
    exact radiusTail_antitone d p hm
  · intro w hw
    have hevent : ∀ᶠ n : ℕ in atTop, radiusTail d p n < w :=
      (radiusTail_tendsto_theta d p) (Iio_mem_nhds hw)
    obtain ⟨n, hn⟩ := hevent.exists
    exact ⟨radiusTail d p n, ⟨n, rfl⟩, hn⟩

theorem theta_upperSemicontinuous (d : ℕ) : UpperSemicontinuous (theta d) := by
  have h : UpperSemicontinuous (fun p : I ↦ ⨅ n : ℕ, radiusTail d p n) :=
    upperSemicontinuous_ciInf
      (fun _ ↦ ⟨0, by rintro _ ⟨n, rfl⟩; exact measureReal_nonneg⟩)
      fun n ↦ (continuous_radiusTail_density d n).upperSemicontinuous
  convert h using 1
  funext p
  exact theta_eq_iInf_radiusTail d p

/-- Right continuity of `θ` on the unit interval, expressed with the right-neighbourhood
filter.  At the endpoint `1` this filter is trivial, as it should be. -/
theorem theta_tendsto_nhdsGT (d : ℕ) (p : I) :
    Tendsto (theta d) (nhdsWithin p (Set.Ioi p)) (nhds (theta d p)) := by
  rw [tendsto_order]
  constructor
  · intro a ha
    filter_upwards [self_mem_nhdsWithin] with q hq
    exact ha.trans_le (theta_mono d hq.le)
  · intro a ha
    exact Filter.Eventually.filter_mono inf_le_left
      ((upperSemicontinuousAt_iff.mp (theta_upperSemicontinuous d p)) a ha)

/-- Cesàro convergence in the normalization used in (5.36):
`n⁻¹ ∑_{i=0}^n g_p(i) → θ(p)`. -/
theorem radiusTailPartialSum_inv_mul_tendsto_theta (d : ℕ) (p : I) :
    Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ * radiusTailPartialSum d p n)
      atTop (nhds (theta d p)) := by
  have htail := radiusTail_tendsto_theta d p
  have hcesaro := htail.cesaro
  have hinv : Tendsto (fun n : ℕ ↦ ((n : ℝ)⁻¹)) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hrem : Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ * radiusTail d p n)
      atTop (nhds 0) := by
    simpa using hinv.mul htail
  have hadd := hcesaro.add hrem
  have hadd' : Tendsto
      (fun n : ℕ ↦ (n : ℝ)⁻¹ * (∑ i ∈ Finset.range n, radiusTail d p i) +
        (n : ℝ)⁻¹ * radiusTail d p n) atTop (nhds (theta d p)) := by
    simpa using hadd
  convert hadd' using 1
  funext n
  rw [radiusTailPartialSum, Finset.sum_range_succ]
  ring

/-- Equation (5.36): the finite-radius derivative is bounded below by the
radius tail times `n/G(p,n)-1`. -/
theorem radiusTail_deriv_ge_tail_mul_partialSum
    {d n : ℕ} {p : I} (hd : 0 < d)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    radiusTail d p n * ((n : ℝ) / radiusTailPartialSum d p n - 1) ≤
      deriv (clampedRadiusTail d n cubicOrigin) (p : ℝ) := by
  have hg : 0 < radiusTail d p n := radiusTail_pos_of_pos_density hd hp0
  have hderiv := radiusTail_russo_hasDerivAt (d := d) (n := n)
    (x := cubicOrigin) hp0 hp1
  have hpiv := conditionalExpectedPivotalCount_ge (d := d) (n := n) hd hp0
  have hcond0 : 0 ≤ conditionalExpectedRadiusPivotalCount d p cubicOrigin n :=
    conditionalExpectedRadiusPivotalCount_nonneg (by simpa [radiusTail] using hg)
  have hdiv : conditionalExpectedRadiusPivotalCount d p cubicOrigin n ≤
      conditionalExpectedRadiusPivotalCount d p cubicOrigin n / (p : ℝ) := by
    rw [le_div_iff₀ hp0]
    nlinarith [p.2.2]
  have heq := radiusTail_logDeriv_eq_conditionalExpectedPivotalCount
    (d := d) (n := n) (x := cubicOrigin) hp0 (by simpa [radiusTail] using hg)
  have hsumEq :
      (∑ e ∈ cubicMetricBallEdges d cubicOrigin n,
          (bernoulliBondMeasure d p).real
            (pivotalEvent (radiusConnectionEvent d cubicOrigin n) e)) =
        radiusTail d p n *
          (conditionalExpectedRadiusPivotalCount d p cubicOrigin n / (p : ℝ)) := by
    have hg' : radiusTail d p n ≠ 0 := hg.ne'
    simpa [radiusTail, mul_comm] using (div_eq_iff hg').mp heq
  rw [hderiv.deriv, hsumEq]
  exact mul_le_mul_of_nonneg_left (hpiv.trans hdiv) hg.le

/-- A one-sided continuation principle, formalizing the supremum argument following (5.39). -/
private theorem linear_continuation
    {F : ℝ → ℝ} {a b k : ℝ} (hk : 0 < k) (hab : a ≤ b)
    (hmono : MonotoneOn F (Set.Icc a b))
    (hlocal : ∀ x ∈ Set.Ico a b, ∃ y, x < y ∧ y ≤ b ∧
      k * (y - x) ≤ F y - F x) :
    k * (b - a) ≤ F b - F a := by
  let S : Set ℝ := {x | x ∈ Set.Icc a b ∧ k * (x - a) ≤ F x - F a}
  have hSa : a ∈ S := by simp [S, hab]
  have hSne : S.Nonempty := ⟨a, hSa⟩
  have hSbdd : BddAbove S := ⟨b, by rintro x hx; exact hx.1.2⟩
  let μ := sSup S
  have haμ : a ≤ μ := by
    exact le_csSup hSbdd hSa
  have hμb : μ ≤ b := by
    exact csSup_le hSne (fun x hx ↦ hx.1.2)
  have hμEndpoint : k * (μ - a) ≤ F μ - F a := by
    by_contra hnot
    have hgap : 0 < k * (μ - a) - (F μ - F a) := sub_pos.mpr (lt_of_not_ge hnot)
    let η := (k * (μ - a) - (F μ - F a)) / (2 * k)
    have hη : 0 < η := div_pos hgap (mul_pos (by norm_num) hk)
    have hxμ : μ - η < sSup S := by simpa [μ] using sub_lt_self μ hη
    obtain ⟨z, hzS, hxz⟩ := exists_lt_of_lt_csSup hSne hxμ
    have hzμ : z ≤ μ := le_csSup hSbdd hzS
    have hzI : z ∈ Set.Icc a b := hzS.1
    have hμI : μ ∈ Set.Icc a b := ⟨haμ, hμb⟩
    have hF : F z ≤ F μ := hmono hzI hμI hzμ
    have hηeq : 2 * k * η = k * (μ - a) - (F μ - F a) := by
      dsimp [η]
      field_simp [hk.ne']
    have hkη : k * (μ - z) < k * η := by
      have : μ - z < η := by linarith
      exact mul_lt_mul_of_pos_left this hk
    nlinarith [hzS.2]
  by_cases hμ : μ < b
  · obtain ⟨y, hμy, hyb, hstep⟩ := hlocal μ ⟨haμ, hμ⟩
    have hay : a ≤ y := haμ.trans hμy.le
    have hyS : y ∈ S := by
      refine ⟨⟨hay, hyb⟩, ?_⟩
      nlinarith
    have hyμ : y ≤ μ := le_csSup hSbdd hyS
    exact (not_lt_of_ge hyμ hμy).elim
  · have hbμ : b ≤ μ := le_of_not_gt hμ
    have hμeq : μ = b := le_antisymm hμb hbμ
    simpa [hμeq] using hμEndpoint

noncomputable def thetaLinearRate (t : ℝ) : ℝ :=
  1 / (1 + (1 - t) / 2) - t

lemma thetaLinearRate_pos {t : ℝ} (ht1 : t < 1) :
    0 < thetaLinearRate t := by
  have hden : 0 < 1 + (1 - t) / 2 := by linarith
  rw [thetaLinearRate, sub_pos, lt_div_iff₀ hden]
  nlinarith [mul_pos (sub_pos.mpr ht1) (by linarith : 0 < 2 - t)]

/-- Local form of (5.39), with a rate uniform below a fixed upper density. -/
theorem theta_local_linear_extension
    {d : ℕ} {α π : I} {t : ℝ} (hd : 0 < d)
    (hα0 : 0 < (α : ℝ)) (hpcα : cubicCriticalProbability d < (α : ℝ)) (hαπ : α < π)
    (hθπ : theta d π ≤ t) (ht1 : t < 1) :
    ∃ β : I, α < β ∧ β ≤ π ∧
      thetaLinearRate t * ((β : ℝ) - (α : ℝ)) ≤ theta d β - theta d α := by
  let h : ℝ := 1 - t
  have hh : 0 < h := sub_pos.mpr ht1
  have hθα : 0 < theta d α := theta_pos_of_criticalProbability_lt hpcα
  have hθαπ : theta d α ≤ theta d π := theta_mono d hαπ.le
  have hθαt : theta d α ≤ t := hθαπ.trans hθπ
  let δ : ℝ := theta d α * h / 4
  have hδ : 0 < δ := div_pos (mul_pos hθα hh) (by norm_num)
  have hnear : ∀ᶠ q : I in nhdsWithin α (Set.Ioi α),
      theta d q < theta d α + δ :=
    (theta_tendsto_nhdsGT d α) (Iio_mem_nhds (lt_add_of_pos_right _ hδ))
  have hbelow : ∀ᶠ q : I in nhdsWithin α (Set.Ioi α), q < π :=
    Filter.Eventually.filter_mono inf_le_left (Iio_mem_nhds hαπ)
  have habove : ∀ᶠ q : I in nhdsWithin α (Set.Ioi α), α < q :=
    self_mem_nhdsWithin
  letI : (nhdsWithin α (Set.Ioi α)).NeBot :=
    nhdsWithin_Ioi_neBot' ⟨π, hαπ⟩ le_rfl
  obtain ⟨β, ⟨hθβ, hβπ⟩, hαβ⟩ := (hnear.and hbelow |>.and habove).exists
  have hβpc : cubicCriticalProbability d < (β : ℝ) :=
    hpcα.trans (by exact_mod_cast hαβ)
  have hβ0 : 0 < (β : ℝ) := hα0.trans (by exact_mod_cast hαβ)
  have hβ1 : (β : ℝ) < 1 := by
    have hβπreal : (β : ℝ) < (π : ℝ) := by exact_mod_cast hβπ
    exact hβπreal.trans_le π.2.2
  have havgTend := radiusTailPartialSum_inv_mul_tendsto_theta d β
  have havg : ∀ᶠ n : ℕ in atTop,
      (n : ℝ)⁻¹ * radiusTailPartialSum d β n < theta d β + δ :=
    havgTend (Iio_mem_nhds (lt_add_of_pos_right _ hδ))
  have hevent : ∀ᶠ n : ℕ in atTop, 1 ≤ n ∧
      (n : ℝ)⁻¹ * radiusTailPartialSum d β n < theta d β + δ :=
    (eventually_ge_atTop (1 : ℕ)).and havg
  have hrate := thetaLinearRate_pos ht1
  refine ⟨β, hαβ, hβπ.le, ?_⟩
  have hdiffTend : Tendsto
      (fun n : ℕ ↦ radiusTail d β n - radiusTail d α n) atTop
      (nhds (theta d β - theta d α)) :=
    (radiusTail_tendsto_theta d β).sub (radiusTail_tendsto_theta d α)
  apply ge_of_tendsto hdiffTend
  filter_upwards [hevent] with n hn
  rcases hn with ⟨hn1, havgn⟩
  let B : ℝ := theta d α * (1 + h / 2)
  have hB : 0 < B := mul_pos hθα (by dsimp [h]; linarith)
  have hθβδB : theta d β + δ < B := by
    dsimp [δ, h] at hθβ
    dsimp [B, δ, h]
    nlinarith
  have hSn : radiusTailPartialSum d β n < B * n := by
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    rw [inv_mul_eq_div] at havgn
    rw [div_lt_iff₀ hnpos] at havgn
    exact havgn.trans (mul_lt_mul_of_pos_right hθβδB hnpos)
  have hderivLower : ∀ q ∈ interior (Set.Icc (α : ℝ) (β : ℝ)),
      thetaLinearRate t ≤ deriv (clampedRadiusTail d n cubicOrigin) q := by
    intro q hq
    have hqIcc : q ∈ Set.Icc (α : ℝ) (β : ℝ) := interior_subset hq
    let qI : I := ⟨q, α.2.1.trans hqIcc.1, hqIcc.2.trans β.2.2⟩
    have hq0 : 0 < q := hα0.trans_le hqIcc.1
    have hq1 : q < 1 := hqIcc.2.trans_lt hβ1
    have hderiv := radiusTail_deriv_ge_tail_mul_partialSum
      (d := d) (n := n) (p := qI) hd hq0 hq1
    have hsumMono : radiusTailPartialSum d qI n ≤ radiusTailPartialSum d β n :=
      radiusTailPartialSum_mono_density d n hqIcc.2
    have hsumPos := radiusTailPartialSum_pos d qI n
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    have hratioQB : 1 / B < (n : ℝ) / radiusTailPartialSum d qI n := by
      rw [div_lt_div_iff₀ hB hsumPos]
      have hsumB : radiusTailPartialSum d qI n < B * n := hsumMono.trans_lt hSn
      nlinarith
    have hBltOne : B < 1 := by
      have htB : B ≤ t * (1 + h / 2) := by
        dsimp [B]
        gcongr
      have hprod : t * (1 + h / 2) < 1 := by
        dsimp [h]
        nlinarith [mul_pos (sub_pos.mpr ht1) (by linarith : 0 < 2 - t)]
      exact htB.trans_lt hprod
    have hcoef0 : 0 < 1 / B - 1 := by
      rw [sub_pos, one_div, one_lt_inv₀ hB]
      exact hBltOne
    have htailLower : theta d α ≤ radiusTail d qI n := by
      calc
        theta d α ≤ theta d qI := theta_mono d hqIcc.1
        _ ≤ radiusTail d qI n := by
          apply le_of_tendsto (radiusTail_tendsto_theta d qI)
          filter_upwards [eventually_ge_atTop n] with m hm
          exact radiusTail_antitone d qI hm
    have hraw : theta d α * (1 / B - 1) ≤
        radiusTail d qI n *
          ((n : ℝ) / radiusTailPartialSum d qI n - 1) := by
      have hcoef : 1 / B - 1 ≤
          (n : ℝ) / radiusTailPartialSum d qI n - 1 := by linarith
      exact mul_le_mul htailLower hcoef hcoef0.le measureReal_nonneg
    have hrateRaw : thetaLinearRate t ≤ theta d α * (1 / B - 1) := by
      have hden : 0 < 1 + h / 2 := by linarith
      have hBform : B = theta d α * (1 + h / 2) := rfl
      have heq : theta d α * (1 / B - 1) =
          1 / (1 + h / 2) - theta d α := by
        rw [hBform]
        field_simp [hθα.ne', hden.ne']
      rw [thetaLinearRate, heq]
      dsimp [h]
      linarith
    exact (hrateRaw.trans hraw).trans hderiv
  let f : ℝ → ℝ := clampedRadiusTail d n cubicOrigin
  have hderivAt : ∀ q : ℝ, q ∈ Set.Icc (α : ℝ) (β : ℝ) →
      ∃ v : ℝ, HasDerivAt f v q := by
    intro q hq
    let qI : I := ⟨q, α.2.1.trans hq.1, hq.2.trans β.2.2⟩
    refine ⟨∑ e ∈ cubicMetricBallEdges d cubicOrigin n,
      (bernoulliBondMeasure d qI).real
        (pivotalEvent (radiusConnectionEvent d cubicOrigin n) e), ?_⟩
    simpa [f, qI] using radiusTail_russo_hasDerivAt
      (d := d) (n := n) (x := cubicOrigin)
      (hα0.trans_le hq.1) (hq.2.trans_lt hβ1)
  have hfcont : ContinuousOn f (Set.Icc (α : ℝ) (β : ℝ)) := by
    intro q hq
    exact (hderivAt q hq).choose_spec.continuousAt.continuousWithinAt
  have hfdiff : DifferentiableOn ℝ f (interior (Set.Icc (α : ℝ) (β : ℝ))) := by
    intro q hq
    exact (hderivAt q (interior_subset hq)).choose_spec.differentiableAt.differentiableWithinAt
  have hslope := (convex_Icc (α : ℝ) (β : ℝ)).mul_sub_le_image_sub_of_le_deriv
    hfcont hfdiff hderivLower (α : ℝ) ⟨le_rfl, (by exact_mod_cast hαβ.le)⟩
      (β : ℝ) ⟨(by exact_mod_cast hαβ.le), le_rfl⟩ (by exact_mod_cast hαβ.le)
  simpa [f, clampedRadiusTail_origin_eq] using hslope

noncomputable def clampedTheta (d : ℕ) (x : ℝ) : ℝ :=
  theta d (Set.projIcc 0 1 zero_le_one x)

theorem clampedTheta_mono (d : ℕ) : Monotone (clampedTheta d) := by
  intro x y hxy
  exact theta_mono d (Set.monotone_projIcc (h := zero_le_one) hxy)

/-- The continuation of the local estimate (5.39) across an arbitrary compact
supercritical interval. -/
theorem theta_linear_between
    {d : ℕ} {α π : I} {t : ℝ} (hd : 0 < d)
    (hα0 : 0 < (α : ℝ)) (hpcα : cubicCriticalProbability d < (α : ℝ))
    (hαπ : α ≤ π) (hθπ : theta d π ≤ t) (ht1 : t < 1) :
    thetaLinearRate t * ((π : ℝ) - (α : ℝ)) ≤ theta d π - theta d α := by
  by_cases hEq : α = π
  · subst π
    simp
  have hαπ' : α < π := lt_of_le_of_ne hαπ hEq
  have hcont := linear_continuation (F := clampedTheta d)
    (k := thetaLinearRate t) (a := (α : ℝ)) (b := (π : ℝ))
    (thetaLinearRate_pos ht1) (by exact_mod_cast hαπ)
    (fun _x _hx _y _hy hxy ↦ clampedTheta_mono d hxy)
  have hlocal : ∀ x ∈ Set.Ico (α : ℝ) (π : ℝ), ∃ y, x < y ∧ y ≤ (π : ℝ) ∧
      thetaLinearRate t * (y - x) ≤ clampedTheta d y - clampedTheta d x := by
    intro x hx
    have hxmem : x ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨α.2.1.trans hx.1, hx.2.le.trans π.2.2⟩
    let xI : I := ⟨x, hxmem⟩
    have hxIπ : xI < π := by exact_mod_cast hx.2
    have hxI0 : 0 < (xI : ℝ) := hα0.trans_le hx.1
    have hpcx : cubicCriticalProbability d < (xI : ℝ) := hpcα.trans_le hx.1
    obtain ⟨β, hxβ, hβπ, hstep⟩ := theta_local_linear_extension
      (d := d) (α := xI) (π := π) (t := t) hd hxI0 hpcx hxIπ hθπ ht1
    refine ⟨(β : ℝ), by exact_mod_cast hxβ, by exact_mod_cast hβπ, ?_⟩
    have hprojx : Set.projIcc 0 1 zero_le_one x = xI :=
      Set.projIcc_of_mem zero_le_one hxmem
    simpa [clampedTheta, hprojx, Set.projIcc_val] using hstep
  have hres := hcont hlocal
  simpa [clampedTheta, Set.projIcc_val] using hres

/-- **Grimmett, Theorem 5.8.** Immediately above the critical probability, the
percolation probability grows at least linearly.  No assumption about `θ(p_c)` is made. -/
theorem theta_sub_theta_critical_ge_linear (d : ℕ) (hd : 2 ≤ d) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ p : I,
      0 ≤ (p : ℝ) - cubicCriticalProbability d →
      (p : ℝ) - cubicCriticalProbability d ≤ b →
      a * ((p : ℝ) - cubicCriticalProbability d) ≤
        theta d p - theta d (cubicCriticalProbabilityUnit d hd) := by
  let pc : ℝ := cubicCriticalProbability d
  have hpc0 : 0 < pc := (cubicCriticalProbability_pos_lt_one hd).1
  have hpc1 : pc < 1 := (cubicCriticalProbability_pos_lt_one hd).2
  let πr : ℝ := (pc + 1) / 2
  have hpcπ : pc < πr := by dsimp [πr]; linarith
  have hπ1 : πr < 1 := by dsimp [πr]; linarith
  let π : I := ⟨πr, hpc0.le.trans hpcπ.le, hπ1.le⟩
  let t : ℝ := theta d π
  have ht1 : t < 1 := by
    have htTail : theta d π ≤ radiusTail d π 1 := by
      apply le_of_tendsto (radiusTail_tendsto_theta d π)
      filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
      exact radiusTail_antitone d π hn
    exact htTail.trans_lt (radiusTail_one_lt_one hπ1)
  let k : ℝ := thetaLinearRate t
  have hk : 0 < k := thetaLinearRate_pos ht1
  let a : ℝ := k / 2
  let b : ℝ := πr - pc
  have ha : 0 < a := half_pos hk
  have hb : 0 < b := sub_pos.mpr hpcπ
  refine ⟨a, b, ha, hb, ?_⟩
  intro p hpLower hpUpper
  have hpcp : pc ≤ (p : ℝ) := sub_nonneg.mp hpLower
  have hpπ : (p : ℝ) ≤ πr := by
    dsimp [b] at hpUpper
    linarith
  by_cases hpEq : (p : ℝ) = pc
  · have hpUnit : p = cubicCriticalProbabilityUnit d hd := by
      apply Subtype.ext
      simpa [pc] using hpEq
    subst p
    simp
  have hpcp' : pc < (p : ℝ) := lt_of_le_of_ne hpcp (Ne.symm hpEq)
  let αr : ℝ := (pc + (p : ℝ)) / 2
  have hpcα : pc < αr := by dsimp [αr]; linarith
  have hαp : αr < (p : ℝ) := by dsimp [αr]; linarith
  have hα0 : 0 < αr := hpc0.trans hpcα
  have hα1 : αr ≤ 1 := hαp.le.trans p.2.2
  let α : I := ⟨αr, hα0.le, hα1⟩
  have hpπI : p ≤ π := by exact_mod_cast hpπ
  have hθp : theta d p ≤ t := theta_mono d hpπI
  have hbetween := theta_linear_between (d := d) (α := α) (π := p) (t := t)
    (by omega) hα0 (by simpa [pc, α, αr] using hpcα) hαp.le hθp ht1
  have hθαCritical : theta d (cubicCriticalProbabilityUnit d hd) ≤ theta d α := by
    apply theta_mono d
    exact_mod_cast hpcα.le
  dsimp [a, k]
  have hhalf : (α : ℝ) - pc = ((p : ℝ) - pc) / 2 := by
    dsimp [α, αr]
    ring
  rw [show (p : ℝ) - (α : ℝ) = ((p : ℝ) - pc) / 2 by
    dsimp [α, αr]; ring] at hbetween
  nlinarith

#print axioms theta_sub_theta_critical_ge_linear

end Percolation
