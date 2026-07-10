import Percolation.Critical.SausageRenewal
import Percolation.Bernoulli.Reliability

/-!
# Menshikov's differential inequalities

This file develops equations 5.9--5.24 and the exponential-decay consequences from Grimmett
§5.2.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal unitInterval BigOperators

noncomputable def radiusRenewalExpectedCount (d : ℕ) (p : I) (n : ℕ) : ℝ :=
  finiteRenewalExpectedRenewalCount n (fun a : Fin (n + 1) ↦ a.1)
    (truncatedTailWeight n (radiusTail d p))

/-- The finite iid renewal calculation in (5.21), before comparison with the actual pivotal
sausages. -/
theorem radiusRenewalExpectedCount_ge (d : ℕ) (p : I) (n : ℕ) :
    (n : ℝ) / (∑ i ∈ Finset.range (n + 1), radiusTail d p i) - 1 ≤
      radiusRenewalExpectedCount d p n := by
  apply finiteRenewal_expectedRenewalCount_truncatedTail_ge n (radiusTail d p)
  · exact radiusTail_zero d p
  · intro i
    exact measureReal_nonneg
  · exact radiusTail_antitone d p

/-- The real function to which Russo's formula is applied; densities outside `[0,1]` are
clamped back to the unit interval. -/
noncomputable def clampedRadiusTail (d n : ℕ) (x : Cubic d) (p : ℝ) : ℝ :=
  (bernoulliBondMeasure d (Set.projIcc 0 1 zero_le_one p)).real
    (radiusConnectionEvent d x n)

/-- The conditional mean pivotal count, written as its finite probability ratio. -/
noncomputable def conditionalExpectedRadiusPivotalCount
    (d : ℕ) (p : I) (x : Cubic d) (n : ℕ) : ℝ :=
  (∑ e ∈ cubicMetricBallEdges d x n,
      (bernoulliBondMeasure d p).real
        (radiusConnectionEvent d x n ∩ pivotalEvent (radiusConnectionEvent d x n) e)) /
    (bernoulliBondMeasure d p).real (radiusConnectionEvent d x n)

/-- Russo's formula (5.9) for `Aₙ(x)`. -/
theorem radiusTail_russo_hasDerivAt {d n : ℕ} {x : Cubic d} {p : I}
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    HasDerivAt (clampedRadiusTail d n x)
      (∑ e ∈ cubicMetricBallEdges d x n,
        (bernoulliBondMeasure d p).real
          (pivotalEvent (radiusConnectionEvent d x n) e)) (p : ℝ) := by
  exact (isIncreasingEvent_radiusConnectionEvent d x n).bernoulliBondMeasure_real_russo_hasDerivAt
    (dependsOn_radiusConnectionEvent d x n) hp0 hp1

/-- Equation (5.10): the logarithmic derivative of the radius tail is the conditional
expected pivotal count divided by `p`. -/
theorem radiusTail_logDeriv_eq_conditionalExpectedPivotalCount {d n : ℕ}
    {x : Cubic d} {p : I} (hp0 : 0 < (p : ℝ))
    (hg : 0 < (bernoulliBondMeasure d p).real (radiusConnectionEvent d x n)) :
    (∑ e ∈ cubicMetricBallEdges d x n,
        (bernoulliBondMeasure d p).real
          (pivotalEvent (radiusConnectionEvent d x n) e)) /
      (bernoulliBondMeasure d p).real (radiusConnectionEvent d x n) =
      conditionalExpectedRadiusPivotalCount d p x n / (p : ℝ) := by
  let A := radiusConnectionEvent d x n
  let E := cubicMetricBallEdges d x n
  have hsum :
      (∑ e ∈ E, (bernoulliBondMeasure d p).real (A ∩ pivotalEvent A e)) =
        (p : ℝ) * ∑ e ∈ E, (bernoulliBondMeasure d p).real (pivotalEvent A e) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    exact (isIncreasingEvent_radiusConnectionEvent d x n).bernoulliBondMeasure_real_inter_pivotalEvent
        (dependsOn_radiusConnectionEvent d x n) he p
  rw [conditionalExpectedRadiusPivotalCount]
  change _ / _ = ((∑ e ∈ E, (bernoulliBondMeasure d p).real (A ∩ pivotalEvent A e)) /
    (bernoulliBondMeasure d p).real A) / (p : ℝ)
  rw [hsum]
  have hg0 : (bernoulliBondMeasure d p).real A ≠ 0 := by
    dsimp [A]
    linarith
  field_simp [hg0, ne_of_gt hp0]
  rw [mul_comm]

theorem radiusTail_log_hasDerivAt {d n : ℕ} {x : Cubic d} {p : I}
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hg : 0 < (bernoulliBondMeasure d p).real (radiusConnectionEvent d x n)) :
    HasDerivAt (fun q : ℝ ↦ Real.log (clampedRadiusTail d n x q))
      (conditionalExpectedRadiusPivotalCount d p x n / (p : ℝ)) (p : ℝ) := by
  have hclamp : Set.projIcc (0 : ℝ) 1 zero_le_one (p : ℝ) = p := by
    apply Subtype.ext
    simp
  have hvalue : clampedRadiusTail d n x (p : ℝ) =
      (bernoulliBondMeasure d p).real (radiusConnectionEvent d x n) := by
    simp [clampedRadiusTail, hclamp]
  have hlog := (radiusTail_russo_hasDerivAt (x := x) hp0 hp1).log (by
    rw [hvalue]
    exact ne_of_gt hg)
  convert hlog using 1
  rw [hvalue]
  exact (radiusTail_logDeriv_eq_conditionalExpectedPivotalCount hp0 hg).symm

theorem clampedRadiusTail_eq (d n : ℕ) (x : Cubic d) (p : I) :
    clampedRadiusTail d n x p =
      (bernoulliBondMeasure d p).real (radiusConnectionEvent d x n) := by
  have hclamp : Set.projIcc (0 : ℝ) 1 zero_le_one (p : ℝ) = p := by
    apply Subtype.ext
    simp
  simp [clampedRadiusTail, hclamp]

theorem clampedRadiusTail_origin_eq (d n : ℕ) (p : I) :
    clampedRadiusTail d n cubicOrigin p = radiusTail d p n :=
  clampedRadiusTail_eq d n cubicOrigin p

noncomputable def radiusTailPartialSum (d : ℕ) (p : I) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), radiusTail d p i

theorem radiusTailPartialSum_pos (d : ℕ) (p : I) (n : ℕ) :
    0 < radiusTailPartialSum d p n := by
  have hnonneg : ∀ i ∈ Finset.range (n + 1), 0 ≤ radiusTail d p i :=
    fun _i _hi ↦ measureReal_nonneg
  have hle : radiusTail d p 0 ≤ radiusTailPartialSum d p n := by
    apply Finset.single_le_sum hnonneg
    simp
  rw [radiusTail_zero] at hle
  linarith

theorem radiusTailPartialSum_mono_density (d n : ℕ) :
    Monotone fun p : I ↦ radiusTailPartialSum d p n := by
  intro p q hpq
  apply Finset.sum_le_sum
  intro i _hi
  exact radiusTail_mono_density d i hpq

theorem conditionalExpectedRadiusPivotalCount_nonneg
    {d n : ℕ} {x : Cubic d} {p : I}
    (hg : 0 < (bernoulliBondMeasure d p).real (radiusConnectionEvent d x n)) :
    0 ≤ conditionalExpectedRadiusPivotalCount d p x n := by
  unfold conditionalExpectedRadiusPivotalCount
  exact div_nonneg (Finset.sum_nonneg fun _e _he ↦ measureReal_nonneg) hg.le

theorem radiusTail_pos_of_pos_density
    {d n : ℕ} {p : I} (hd : 0 < d) (hp : 0 < (p : ℝ)) :
    0 < radiusTail d p n := by
  classical
  let i : Fin d := ⟨0, hd⟩
  let y : Cubic d := fun j ↦ if j = i then (n : ℤ) else 0
  have hydist : cubicL1Dist cubicOrigin y = n := by
    rw [cubicL1Dist]
    calc
      (∑ j, (y j - cubicOrigin j).natAbs) =
          (y i - cubicOrigin i).natAbs := by
        apply Finset.sum_eq_single i
        · intro j _hj hji
          simp [y, cubicOrigin, hji]
        · simp
      _ = n := by simp [y, cubicOrigin]
  have hy : y ∈ cubicMetricSphere d cubicOrigin n :=
    mem_cubicMetricSphere_iff_l1Dist_eq.mpr hydist
  have hsub : connectionEvent d cubicOrigin y ⊆
      radiusConnectionEvent d cubicOrigin n := by
    intro ω hω
    rw [mem_radiusConnectionEvent_iff_exists_connection]
    exact ⟨y, hy, hω⟩
  rw [radiusTail]
  exact lt_of_lt_of_le
    (bernoulliBondMeasure_real_connectionEvent_pos d hp cubicOrigin y)
    (measureReal_mono hsub)

/-- Equation (5.21): the actual conditional pivotal count dominates the iid
renewal count built from the radius-tail law. -/
theorem radiusRenewalExpectedCount_le_conditionalExpectedRadiusPivotalCount
    {d n : ℕ} {p : I} (hg : 0 < radiusTail d p n) :
    radiusRenewalExpectedCount d p n ≤
      conditionalExpectedRadiusPivotalCount d p cubicOrigin n := by
  rw [conditionalExpectedRadiusPivotalCount, radiusRenewalExpectedCount]
  rw [le_div_iff₀ (by simpa [radiusTail] using hg)]
  simpa [radiusTail] using
    finiteRenewalExpectedRenewalCount_mul_radiusTail_le_pivotalNumerator d n p

/-- **Grimmett, Lemma 5.17.** On `Aₙ`, the conditional mean number of
pivotal edges is at least `n / (gₚ(0)+⋯+gₚ(n)) - 1`. -/
theorem conditionalExpectedPivotalCount_ge_of_radiusTail_pos
    {d n : ℕ} {p : I} (hg : 0 < radiusTail d p n) :
    (n : ℝ) / (∑ i ∈ Finset.range (n + 1), radiusTail d p i) - 1 ≤
      conditionalExpectedRadiusPivotalCount d p cubicOrigin n :=
  (radiusRenewalExpectedCount_ge d p n).trans
    (radiusRenewalExpectedCount_le_conditionalExpectedRadiusPivotalCount hg)

/-- **Grimmett, Lemma 5.17**, in its source-facing parameter range. -/
theorem conditionalExpectedPivotalCount_ge
    {d n : ℕ} {p : I} (hd : 0 < d) (hp : 0 < (p : ℝ)) :
    (n : ℝ) / (∑ i ∈ Finset.range (n + 1), radiusTail d p i) - 1 ≤
      conditionalExpectedRadiusPivotalCount d p cubicOrigin n :=
  conditionalExpectedPivotalCount_ge_of_radiusTail_pos
    (radiusTail_pos_of_pos_density hd hp)

/-- Integrated master inequality (5.22), from the pivotal lower bound supplied by Lemma 5.17. -/
theorem radiusTail_master_inequality_of_pivotal_bound
    {d n : ℕ} {α β : I}
    (hα0 : 0 < (α : ℝ)) (hαβ : (α : ℝ) ≤ (β : ℝ)) (hβ1 : (β : ℝ) < 1)
    (hpos : ∀ q : I, α ≤ q → q ≤ β → 0 < radiusTail d q n)
    (hpiv : ∀ q : I, α ≤ q → q ≤ β →
      (n : ℝ) / radiusTailPartialSum d q n - 1 ≤
        conditionalExpectedRadiusPivotalCount d q cubicOrigin n) :
    radiusTail d α n ≤ radiusTail d β n *
      Real.exp (-(((β : ℝ) - (α : ℝ)) *
        ((n : ℝ) / radiusTailPartialSum d β n - 1))) := by
  let f : ℝ → ℝ := fun q ↦ Real.log (clampedRadiusTail d n cubicOrigin q)
  let C : ℝ := (n : ℝ) / radiusTailPartialSum d β n - 1
  have hderiv : ∀ (q : ℝ) (hq : q ∈ Set.Icc (α : ℝ) (β : ℝ)),
      HasDerivAt f
        (conditionalExpectedRadiusPivotalCount d
          ⟨q, hα0.le.trans hq.1, hq.2.trans hβ1.le⟩ cubicOrigin n / q) q := by
    intro q hq
    let qI : I := ⟨q, hα0.le.trans hq.1, hq.2.trans hβ1.le⟩
    have hq0 : 0 < q := hα0.trans_le hq.1
    have hq1 : q < 1 := hq.2.trans_lt hβ1
    have hqpos : 0 < (bernoulliBondMeasure d qI).real
        (radiusConnectionEvent d cubicOrigin n) := by
      simpa [radiusTail, qI] using hpos qI hq.1 hq.2
    simpa [f, qI] using radiusTail_log_hasDerivAt hq0 hq1 hqpos
  have hfcont : ContinuousOn f (Set.Icc (α : ℝ) (β : ℝ)) := by
    intro q hq
    exact (hderiv q hq).continuousAt.continuousWithinAt
  have hfdiff : DifferentiableOn ℝ f (interior (Set.Icc (α : ℝ) (β : ℝ))) := by
    intro q hq
    exact (hderiv q (interior_subset hq)).differentiableAt.differentiableWithinAt
  have hderivLower : ∀ q ∈ interior (Set.Icc (α : ℝ) (β : ℝ)),
      C ≤ deriv f q := by
    intro q hq
    have hqIcc := interior_subset hq
    let qI : I := ⟨q, hα0.le.trans hqIcc.1, hqIcc.2.trans hβ1.le⟩
    have hqpos : 0 < radiusTail d qI n := hpos qI hqIcc.1 hqIcc.2
    have hcond0 : 0 ≤ conditionalExpectedRadiusPivotalCount d qI cubicOrigin n := by
      apply conditionalExpectedRadiusPivotalCount_nonneg
      simpa [radiusTail] using hqpos
    have hq0 : 0 < q := hα0.trans_le hqIcc.1
    have hq1 : q ≤ 1 := hqIcc.2.trans hβ1.le
    have hcondDiv : conditionalExpectedRadiusPivotalCount d qI cubicOrigin n ≤
        conditionalExpectedRadiusPivotalCount d qI cubicOrigin n / q := by
      have hqle : q ≤ 1 := hq1
      rw [le_div_iff₀ hq0]
      nlinarith
    have hsumMono : radiusTailPartialSum d qI n ≤ radiusTailPartialSum d β n :=
      radiusTailPartialSum_mono_density d n hqIcc.2
    have hfrac : (n : ℝ) / radiusTailPartialSum d β n ≤
        (n : ℝ) / radiusTailPartialSum d qI n := by
      exact div_le_div_of_nonneg_left (Nat.cast_nonneg n)
        (radiusTailPartialSum_pos d qI n) hsumMono
    have hpivq := hpiv qI hqIcc.1 hqIcc.2
    rw [(hderiv q hqIcc).deriv]
    exact (sub_le_sub_right hfrac 1).trans (hpivq.trans hcondDiv)
  have hslope := (convex_Icc (α : ℝ) (β : ℝ)).mul_sub_le_image_sub_of_le_deriv
    hfcont hfdiff hderivLower (α : ℝ) ⟨le_rfl, hαβ⟩
      (β : ℝ) ⟨hαβ, le_rfl⟩ hαβ
  have hlog : Real.log (radiusTail d α n) ≤
      Real.log (radiusTail d β n) - ((β : ℝ) - (α : ℝ)) * C := by
    have hslope' : C * ((β : ℝ) - (α : ℝ)) + f (α : ℝ) ≤ f (β : ℝ) :=
      (le_sub_iff_add_le).mp hslope
    dsimp [f, C] at hslope' ⊢
    simp only [clampedRadiusTail_origin_eq] at hslope' ⊢
    nlinarith
  have hαpos := hpos α le_rfl hαβ
  have hβpos := hpos β hαβ le_rfl
  calc
    radiusTail d α n = Real.exp (Real.log (radiusTail d α n)) :=
      (Real.exp_log hαpos).symm
    _ ≤ Real.exp (Real.log (radiusTail d β n) -
        ((β : ℝ) - (α : ℝ)) * C) := Real.exp_le_exp.mpr hlog
    _ = radiusTail d β n *
        Real.exp (-(((β : ℝ) - (α : ℝ)) * C)) := by
      rw [sub_eq_add_neg, Real.exp_add, Real.exp_log hβpos]
    _ = _ := rfl

end Percolation

#print axioms Percolation.conditionalExpectedPivotalCount_ge
