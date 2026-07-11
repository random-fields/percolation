import Percolation.Critical.StaticAnnularPeeling

/-!
# Logarithmic inset geometry for Grimmett Lemma 7.97

The source uses the inner box `B(n - v log n)`.  Integer radii require a rounding convention;
we take the inset width to be `⌈v log n⌉`.  This file isolates the asymptotic facts needed to
combine density, annular coalescence, and the outer-box crossing event.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval

/-- Integer width corresponding to the source expression `v log n`. -/
noncomputable def logarithmicInsetWidth (v : ℝ) (n : ℕ) : ℕ :=
  Nat.ceil (v * Real.log n)

/-- Inner radius `n - ⌈v log n⌉`. -/
noncomputable def logarithmicInsetRadius (v : ℝ) (n : ℕ) : ℕ :=
  n - logarithmicInsetWidth v n

theorem logarithmicInsetRadius_le (v : ℝ) (n : ℕ) :
    logarithmicInsetRadius v n ≤ n :=
  Nat.sub_le _ _

/-- The rounded logarithmic width is sublinear. -/
theorem tendsto_logarithmicInsetWidth_div_nat {v : ℝ} (hv : 0 ≤ v) :
    Filter.Tendsto
      (fun n : ℕ ↦ (logarithmicInsetWidth v n : ℝ) / n)
      Filter.atTop (nhds 0) := by
  have hlog : Filter.Tendsto (fun n : ℕ ↦ Real.log (n : ℝ) / n)
      Filter.atTop (nhds 0) := by
    simpa using Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
      tendsto_natCast_atTop_atTop
  have hinv : Filter.Tendsto (fun n : ℕ ↦ (1 : ℝ) / n)
      Filter.atTop (nhds 0) := by
    exact tendsto_one_div_atTop_nhds_zero_nat
  have hupper : Filter.Tendsto
      (fun n : ℕ ↦ v * (Real.log (n : ℝ) / n) + 1 / n)
      Filter.atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul hlog).add hinv
  apply squeeze_zero'
    (Filter.Eventually.of_forall fun n ↦ div_nonneg (by positivity) (by positivity))
    (Filter.eventually_atTop.2 ⟨1, fun n hn ↦ ?_⟩) hupper
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hvlog0 : 0 ≤ v * Real.log (n : ℝ) := by
    exact mul_nonneg hv (Real.log_nonneg (by exact_mod_cast hn))
  have hceil := Nat.ceil_lt_add_one hvlog0
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  rw [div_le_iff₀ hnpos]
  have hceilCast : (logarithmicInsetWidth v n : ℝ) <
      v * Real.log (n : ℝ) + 1 := by
    simpa [logarithmicInsetWidth] using hceil
  calc
    (logarithmicInsetWidth v n : ℝ) ≤ v * Real.log (n : ℝ) + 1 := hceilCast.le
    _ = (v * (Real.log (n : ℝ) / n) + 1 / n) * n := by field_simp

/-- The logarithmically inset radius is asymptotic to the outer radius. -/
theorem tendsto_logarithmicInsetRadius_div_nat {v : ℝ} (hv : 0 ≤ v) :
    Filter.Tendsto
      (fun n : ℕ ↦ (logarithmicInsetRadius v n : ℝ) / n)
      Filter.atTop (nhds 1) := by
  have hwidth := tendsto_logarithmicInsetWidth_div_nat hv
  have hwidthLtOne : ∀ᶠ n : ℕ in Filter.atTop,
      (logarithmicInsetWidth v n : ℝ) / n < 1 :=
    (tendsto_order.1 hwidth).2 _ zero_lt_one
  have hEq : ∀ᶠ n : ℕ in Filter.atTop,
      (logarithmicInsetRadius v n : ℝ) / n =
        1 - (logarithmicInsetWidth v n : ℝ) / n := by
    filter_upwards [Filter.eventually_ge_atTop 1, hwidthLtOne] with n hn hratio
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hwidthLe : logarithmicInsetWidth v n ≤ n := by
      exact_mod_cast (show (logarithmicInsetWidth v n : ℝ) ≤ n by
        simpa using ((div_lt_iff₀ hnpos).mp hratio).le)
    rw [logarithmicInsetRadius, Nat.cast_sub]
    · field_simp
    · exact hwidthLe
  have htarget : Filter.Tendsto
      (fun n : ℕ ↦ 1 - (logarithmicInsetWidth v n : ℝ) / n)
      Filter.atTop (nhds 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hwidth
  exact htarget.congr' (hEq.mono fun _ h ↦ h.symm)

/-- A positive logarithmic inset width diverges. -/
theorem tendsto_logarithmicInsetWidth_atTop {v : ℝ} (hv : 0 < v) :
    Filter.Tendsto (logarithmicInsetWidth v) Filter.atTop Filter.atTop := by
  have hvlog : Filter.Tendsto (fun n : ℕ ↦ v * Real.log (n : ℝ))
      Filter.atTop Filter.atTop :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop hv
  rw [Filter.tendsto_atTop_atTop]
  intro b
  obtain ⟨N, hN⟩ := Filter.tendsto_atTop_atTop.1 hvlog (b : ℝ)
  exact ⟨N, fun n hn ↦ by
    rw [logarithmicInsetWidth]
    exact_mod_cast (hN n hn).trans (Nat.le_ceil (v * Real.log (n : ℝ)))⟩

/-- The inner radii themselves diverge despite the logarithmic inset. -/
theorem tendsto_logarithmicInsetRadius_atTop {v : ℝ} (hv : 0 ≤ v) :
    Filter.Tendsto (logarithmicInsetRadius v) Filter.atTop Filter.atTop := by
  have hratio := tendsto_logarithmicInsetRadius_div_nat hv
  have hhalf : ∀ᶠ n : ℕ in Filter.atTop,
      (1 / 2 : ℝ) < (logarithmicInsetRadius v n : ℝ) / n :=
    (tendsto_order.1 hratio).1 _ (by norm_num)
  rw [Filter.tendsto_atTop_atTop]
  intro b
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hhalf
  refine ⟨max N (2 * b + 1), fun n hn ↦ ?_⟩
  have hnHalf := hN n ((Nat.le_max_left _ _).trans hn)
  have hnLarge : 2 * b + 1 ≤ n := (Nat.le_max_right _ _).trans hn
  have hnOne : 1 ≤ n := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hnOne
  have hreal : (n : ℝ) / 2 < logarithmicInsetRadius v n := by
    have := (lt_div_iff₀ hn0).mp hnHalf
    nlinarith
  exact_mod_cast (show (b : ℝ) ≤ logarithmicInsetRadius v n by
    have hbn : (2 * b : ℝ) < n := by exact_mod_cast (show 2 * b < n by omega)
    have : (b : ℝ) < n / 2 := by nlinarith
    linarith)

/-- Eventually the rounded inset fits inside the outer radius. -/
theorem eventually_logarithmicInsetWidth_le {v : ℝ} (hv : 0 ≤ v) :
    ∀ᶠ n : ℕ in Filter.atTop, logarithmicInsetWidth v n ≤ n := by
  have hwidth := tendsto_logarithmicInsetWidth_div_nat hv
  have hlt : ∀ᶠ n : ℕ in Filter.atTop,
      (logarithmicInsetWidth v n : ℝ) / n < 1 :=
    (tendsto_order.1 hwidth).2 _ zero_lt_one
  filter_upwards [Filter.eventually_ge_atTop 1, hlt] with n hn hratio
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  exact_mod_cast (show (logarithmicInsetWidth v n : ℝ) ≤ n by
    simpa using ((div_lt_iff₀ hn0).mp hratio).le)

/-- Once the rounded width fits, subtraction recovers that width exactly. -/
theorem eventually_outer_sub_logarithmicInsetRadius_eq_width {v : ℝ} (hv : 0 ≤ v) :
    ∀ᶠ n : ℕ in Filter.atTop,
      n - logarithmicInsetRadius v n = logarithmicInsetWidth v n := by
  filter_upwards [eventually_logarithmicInsetWidth_le hv] with n hn
  simp [logarithmicInsetRadius, Nat.sub_sub_self hn]

/-- Coordinate-box volume at the logarithmically inset radius is asymptotic to the full box
volume. -/
theorem tendsto_logarithmicInset_boxCard_ratio {d : ℕ} {v : ℝ} (hv : 0 ≤ v) :
    Filter.Tendsto
      (fun n : ℕ ↦
        ((cubicMetricBox d cubicOrigin (logarithmicInsetRadius v n)).card : ℝ) /
          (cubicMetricBox d cubicOrigin n).card)
      Filter.atTop (nhds 1) := by
  have hratio := tendsto_logarithmicInsetRadius_div_nat hv
  have hinv : Filter.Tendsto (fun n : ℕ ↦ (1 : ℝ) / n)
      Filter.atTop (nhds 0) := tendsto_one_div_atTop_nhds_zero_nat
  have hbase : Filter.Tendsto
      (fun n : ℕ ↦
        (2 * ((logarithmicInsetRadius v n : ℝ) / n) + 1 / n) /
          (2 + 1 / n))
      Filter.atTop (nhds 1) := by
    have hnum := ((tendsto_const_nhds (x := (2 : ℝ))).mul hratio).add hinv
    have hden := (tendsto_const_nhds (x := (2 : ℝ))).add hinv
    simpa using hnum.div hden (by norm_num)
  have hbasePow : Filter.Tendsto
      (fun n : ℕ ↦
        ((2 * ((logarithmicInsetRadius v n : ℝ) / n) + 1 / n) /
          (2 + 1 / n)) ^ d)
      Filter.atTop (nhds 1) := by
    simpa using hbase.pow d
  have hEq : ∀ᶠ n : ℕ in Filter.atTop,
      ((cubicMetricBox d cubicOrigin (logarithmicInsetRadius v n)).card : ℝ) /
          (cubicMetricBox d cubicOrigin n).card =
        ((2 * ((logarithmicInsetRadius v n : ℝ) / n) + 1 / n) /
          (2 + 1 / n)) ^ d := by
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    rw [cubicMetricBox_card, cubicMetricBox_card]
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    push_cast
    rw [← div_pow]
    congr 1
    field_simp
  exact hbasePow.congr' (hEq.mono fun _ h ↦ h.symm)

/-- A box whose radius is the logarithmic inset width occupies a vanishing fraction of the
outer box. -/
theorem tendsto_logarithmicInsetWidth_boxCard_ratio {d : ℕ} (hd : 1 ≤ d)
    {v : ℝ} (hv : 0 ≤ v) :
    Filter.Tendsto
      (fun n : ℕ ↦
        ((cubicMetricBox d cubicOrigin (logarithmicInsetWidth v n)).card : ℝ) /
          (cubicMetricBox d cubicOrigin n).card)
      Filter.atTop (nhds 0) := by
  have hratio := tendsto_logarithmicInsetWidth_div_nat hv
  have hinv : Filter.Tendsto (fun n : ℕ ↦ (1 : ℝ) / n)
      Filter.atTop (nhds 0) := tendsto_one_div_atTop_nhds_zero_nat
  have hbase : Filter.Tendsto
      (fun n : ℕ ↦
        (2 * ((logarithmicInsetWidth v n : ℝ) / n) + 1 / n) /
          (2 + 1 / n))
      Filter.atTop (nhds 0) := by
    have hnum := ((tendsto_const_nhds (x := (2 : ℝ))).mul hratio).add hinv
    have hden := (tendsto_const_nhds (x := (2 : ℝ))).add hinv
    simpa using hnum.div hden (by norm_num)
  have hbasePow : Filter.Tendsto
      (fun n : ℕ ↦
        ((2 * ((logarithmicInsetWidth v n : ℝ) / n) + 1 / n) /
          (2 + 1 / n)) ^ d)
      Filter.atTop (nhds 0) := by
    simpa [zero_pow (Nat.ne_of_gt hd)] using hbase.pow d
  have hEq : ∀ᶠ n : ℕ in Filter.atTop,
      ((cubicMetricBox d cubicOrigin (logarithmicInsetWidth v n)).card : ℝ) /
          (cubicMetricBox d cubicOrigin n).card =
        ((2 * ((logarithmicInsetWidth v n : ℝ) / n) + 1 / n) /
          (2 + 1 / n)) ^ d := by
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    rw [cubicMetricBox_card, cubicMetricBox_card]
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    push_cast
    rw [← div_pow]
    congr 1
    field_simp
  exact hbasePow.congr' (hEq.mono fun _ h ↦ h.symm)

/-- Coordinate-box cardinalities diverge in every positive dimension. -/
theorem tendsto_cubicMetricBox_card_atTop {d : ℕ} (hd : 1 ≤ d) :
    Filter.Tendsto (fun n : ℕ ↦ (cubicMetricBox d cubicOrigin n).card)
      Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  refine ⟨b, fun n hn ↦ ?_⟩
  rw [cubicMetricBox_card]
  calc
    b ≤ n := hn
    _ ≤ 2 * n + 1 := by omega
    _ = (2 * n + 1) ^ 1 := by simp
    _ ≤ (2 * n + 1) ^ d :=
      pow_le_pow_right' (by omega) hd

/-- If two integer scales have asymptotic ratio one, a strict coefficient margin eventually
absorbs the unit rounding error introduced by `Nat.ceil`. -/
theorem eventually_natCeil_mul_le_mul_of_ratio_tendsto_one
    (f g : ℕ → ℕ) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hratio : Filter.Tendsto (fun n ↦ (f n : ℝ) / g n)
      Filter.atTop (nhds 1))
    (hg : Filter.Tendsto g Filter.atTop Filter.atTop) :
    ∀ᶠ n : ℕ in Filter.atTop,
      (Nat.ceil (a * g n) : ℝ) ≤ b * f n := by
  let c : ℝ := (b - a) / 2
  have hc0 : 0 < c := by dsimp [c]; linarith
  have hmarginTendsto : Filter.Tendsto
      (fun n ↦ b * ((f n : ℝ) / g n) - a)
      Filter.atTop (nhds (b - a)) := by
    simpa using (tendsto_const_nhds.mul hratio).sub tendsto_const_nhds
  have hmargin : ∀ᶠ n : ℕ in Filter.atTop,
      c < b * ((f n : ℝ) / g n) - a := by
    apply (tendsto_order.1 hmarginTendsto).1
    dsimp [c]
    linarith
  have hgLarge : ∀ᶠ n : ℕ in Filter.atTop, 1 / c ≤ (g n : ℝ) := by
    have hgCast : Filter.Tendsto (fun n ↦ (g n : ℝ)) Filter.atTop Filter.atTop :=
      tendsto_natCast_atTop_atTop.comp hg
    exact Filter.tendsto_atTop.1 hgCast (1 / c)
  have hgPos : ∀ᶠ n : ℕ in Filter.atTop, 1 ≤ g n :=
    Filter.tendsto_atTop.1 hg 1
  filter_upwards [hmargin, hgLarge, hgPos] with n hmarginN hgLargeN hgPosN
  have hg0 : (0 : ℝ) < g n := by exact_mod_cast hgPosN
  have hround := Nat.ceil_lt_add_one (mul_nonneg ha (by positivity) : 0 ≤ a * (g n : ℝ))
  have hone : 1 ≤ c * (g n : ℝ) := by
    have := mul_le_mul_of_nonneg_right hgLargeN hc0.le
    field_simp at this
    simpa [mul_comm] using this
  have hstrict : a * (g n : ℝ) + 1 < b * (f n : ℝ) := by
    have hscaled := mul_lt_mul_of_pos_right hmarginN hg0
    field_simp [hg0.ne'] at hscaled
    nlinarith
  exact hround.le.trans hstrict.le

/-- A logarithmic annulus whose coefficient beats the polynomial pair count makes the
polynomially corrected exponential two-arm estimate vanish. -/
theorem tendsto_cubicMetricBox_card_sq_mul_exp_neg_logarithmicInset
    (d : ℕ) {ξ v : ℝ} (hv : 0 < v)
    (hdegree : (2 * d + 1 : ℕ) ≤ ξ * v) :
    Filter.Tendsto
      (fun n : ℕ ↦
        ((cubicMetricBox d cubicOrigin (logarithmicInsetRadius v n)).card : ℝ) ^ 2 *
          Real.exp (-ξ * (n - logarithmicInsetRadius v n : ℕ)))
      Filter.atTop (nhds 0) := by
  let K : ℕ := 2 * d + 1
  have hinv : Filter.Tendsto (fun n : ℕ ↦ (1 : ℝ) / n)
      Filter.atTop (nhds 0) := tendsto_one_div_atTop_nhds_zero_nat
  have hupper : Filter.Tendsto (fun n : ℕ ↦ (3 : ℝ) ^ (2 * d) * (1 / n))
      Filter.atTop (nhds 0) := by
    simpa using (tendsto_const_nhds (x := (3 : ℝ) ^ (2 * d))).mul hinv
  apply squeeze_zero'
    (Filter.Eventually.of_forall fun n ↦ mul_nonneg (by positivity) (Real.exp_pos _).le)
    (by
      filter_upwards [Filter.eventually_ge_atTop 1,
        eventually_logarithmicInsetWidth_le hv.le] with n hn hwidthLe
      show _ ≤ _
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
      have hrn : logarithmicInsetRadius v n ≤ n := logarithmicInsetRadius_le v n
      have hlinNat : 2 * logarithmicInsetRadius v n + 1 ≤ 3 * n := by omega
      have hlin : (2 * logarithmicInsetRadius v n + 1 : ℝ) ≤ 3 * n := by
        exact_mod_cast hlinNat
      have hcard :
          ((cubicMetricBox d cubicOrigin (logarithmicInsetRadius v n)).card : ℝ) ^ 2 ≤
            (3 * (n : ℝ)) ^ (2 * d) := by
        rw [cubicMetricBox_card]
        norm_num [← pow_mul, Nat.mul_comm]
        simpa [Nat.mul_comm] using
          pow_le_pow_left₀ (by positivity) hlin (2 * d)
      have hlog0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
      have hceil : v * Real.log (n : ℝ) ≤ logarithmicInsetWidth v n := by
        simpa [logarithmicInsetWidth] using Nat.le_ceil (v * Real.log (n : ℝ))
      have hgap : v * Real.log (n : ℝ) ≤
          (n - logarithmicInsetRadius v n : ℕ) := by
        simpa [logarithmicInsetRadius, Nat.sub_sub_self hwidthLe] using hceil
      have hexp : Real.exp (-ξ * (n - logarithmicInsetRadius v n : ℕ)) ≤
          1 / (n : ℝ) ^ K := by
        have hexponent : -ξ * (n - logarithmicInsetRadius v n : ℕ) ≤
            -(K : ℝ) * Real.log (n : ℝ) := by
          have hdegreeReal : (K : ℝ) ≤ ξ * v := by exact_mod_cast hdegree
          dsimp [K] at hdegreeReal ⊢
          nlinarith
        calc
          Real.exp (-ξ * (n - logarithmicInsetRadius v n : ℕ)) ≤
              Real.exp (-(K : ℝ) * Real.log (n : ℝ)) := Real.exp_le_exp.mpr hexponent
          _ = 1 / (n : ℝ) ^ K := by
            rw [show -(K : ℝ) * Real.log (n : ℝ) =
                -Real.log ((n : ℝ) ^ K) by rw [Real.log_pow]; ring]
            rw [Real.exp_neg, Real.exp_log (pow_pos hn0 K)]
            simp [one_div]
      calc
        ((cubicMetricBox d cubicOrigin (logarithmicInsetRadius v n)).card : ℝ) ^ 2 *
              Real.exp (-ξ * (n - logarithmicInsetRadius v n : ℕ)) ≤
            (3 * (n : ℝ)) ^ (2 * d) * (1 / (n : ℝ) ^ K) :=
          mul_le_mul hcard hexp (Real.exp_pos _).le (by positivity)
        _ = (3 : ℝ) ^ (2 * d) * (1 / n) := by
          dsimp [K]
          field_simp
          ring) hupper

/-- The same logarithmic coefficient also beats the pair count in the full outer box. -/
theorem tendsto_cubicMetricBox_card_sq_mul_exp_neg_logarithmicInsetWidth
    (d : ℕ) {ξ v : ℝ} (hv : 0 < v)
    (hdegree : (2 * d + 1 : ℕ) ≤ ξ * v) :
    Filter.Tendsto
      (fun n : ℕ ↦ ((cubicMetricBox d cubicOrigin n).card : ℝ) ^ 2 *
        Real.exp (-ξ * logarithmicInsetWidth v n))
      Filter.atTop (nhds 0) := by
  have hinnerOuter := tendsto_logarithmicInset_boxCard_ratio (d := d) hv.le
  have houterInner : Filter.Tendsto
      (fun n : ℕ ↦
        ((cubicMetricBox d cubicOrigin n).card : ℝ) /
          (cubicMetricBox d cubicOrigin (logarithmicInsetRadius v n)).card)
      Filter.atTop (nhds 1) := by
    have hinv := hinnerOuter.inv₀ one_ne_zero
    simpa [inv_div] using hinv
  have hmult : Filter.Tendsto
      (fun n : ℕ ↦
        (((cubicMetricBox d cubicOrigin n).card : ℝ) /
          (cubicMetricBox d cubicOrigin (logarithmicInsetRadius v n)).card) ^ 2)
      Filter.atTop (nhds 1) := by
    simpa using houterInner.pow 2
  have hinner := tendsto_cubicMetricBox_card_sq_mul_exp_neg_logarithmicInset
    d hv hdegree
  have hproduct := hmult.mul hinner
  have hproduct' : Filter.Tendsto
      (fun n : ℕ ↦
        (((cubicMetricBox d cubicOrigin n).card : ℝ) /
          (cubicMetricBox d cubicOrigin (logarithmicInsetRadius v n)).card) ^ 2 *
        (((cubicMetricBox d cubicOrigin (logarithmicInsetRadius v n)).card : ℝ) ^ 2 *
          Real.exp (-ξ * (n - logarithmicInsetRadius v n : ℕ))))
      Filter.atTop (nhds 0) := by
    simpa using hproduct
  apply hproduct'.congr'
  filter_upwards [eventually_outer_sub_logarithmicInsetRadius_eq_width hv.le] with n hgap
  rw [hgap]
  have hcard0 : (0 : ℝ) <
      (cubicMetricBox d cubicOrigin (logarithmicInsetRadius v n)).card := by
    rw [cubicMetricBox_card]
    positivity
  field_simp

/-- Lemma 7.89 supplies a logarithmic inset for which all inner infinite-cluster vertices
coalesce in the outer box with probability tending to one.  The coefficient is chosen so the
exponential annular estimate beats the `O(n^(2d))` vertex-pair count. -/
theorem exists_logarithmicInset_infiniteClusterCoalescence_probability_tendsto_one
    {d L : ℕ} (hd : 2 ≤ d) (p : I) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hslab : UniformFiniteSlabConnectionLowerBound d p L δ) :
    ∃ v : ℝ, 0 < v ∧
      Filter.Tendsto
        (fun n ↦ (bernoulliBondMeasure d p).real
          (infiniteClusterCoalescenceEvent d (logarithmicInsetRadius v n) n))
        Filter.atTop (nhds 1) := by
  obtain ⟨ξ, hξ0, hpair⟩ :=
    exists_twoArmSeparation_probability_le_exp_of_uniformFiniteSlab
      hd p hp0 hp1 hδ0 hδ1 hslab
  let v : ℝ := (2 * d + 1 : ℕ) / ξ
  have hv0 : 0 < v := by
    dsimp [v]
    positivity
  refine ⟨v, hv0, ?_⟩
  apply infiniteClusterCoalescenceEvent_probability_tendsto_one_of_twoArm_bound
    p (logarithmicInsetRadius v) id
      (fun n ↦ Real.exp (-ξ * (n - logarithmicInsetRadius v n : ℕ)))
  · exact fun n ↦ logarithmicInsetRadius_le v n
  · intro n x hx y hy
    by_cases hn : logarithmicInsetRadius v n < n
    · exact hpair _ _ hn x y
    · have heq : logarithmicInsetRadius v n = n :=
        Nat.le_antisymm (logarithmicInsetRadius_le v n) (Nat.le_of_not_gt hn)
      rw [heq]
      simpa using (measureReal_le_one (μ := bernoulliBondMeasure d p)
        (s := twoArmSeparationEvent d n n x y))
  · apply tendsto_cubicMetricBox_card_sq_mul_exp_neg_logarithmicInset d hv0
    dsimp [v]
    field_simp
    norm_num

/-! ### Source-facing dense crossing cluster -/

/-- A finite box graph has a crossing component whose real cardinality exceeds `t`. -/
def FiniteBoxGraph.HasDenseCrossing {d : ℕ} {x : Cubic d} {n : ℕ}
    (t : ℝ) (G : SimpleGraph {y : Cubic d // y ∈ cubicMetricBox d x n}) : Prop :=
  ∃ C : G.ConnectedComponent,
    finiteBoxGraphComponentIsCrossing C ∧
      t ≤ (finiteBoxGraphComponentCard C : ℝ)

/-- Source event in Lemma 7.97: some all-direction crossing cluster in `x+B(n)` contains at
least `(1-ε) θ(p) |B(n)|` vertices. -/
def epsilonDenseCrossingClusterEvent
    (d : ℕ) (p : I) (ε : ℝ) (n : ℕ) (x : Cubic d) : Set (EdgeConfiguration d) :=
  {ω | FiniteBoxGraph.HasDenseCrossing
    ((1 - ε) * theta d p * ((cubicMetricBox d x n).card : ℝ))
    (finiteBoxOpenGraph d ω x n)}

theorem dependsOn_epsilonDenseCrossingClusterEvent
    (d : ℕ) (p : I) (ε : ℝ) (n : ℕ) (x : Cubic d) :
    DependsOn (cubicBoxEdges d x n) (epsilonDenseCrossingClusterEvent d p ε n x) := by
  intro ω η hagree
  change FiniteBoxGraph.HasDenseCrossing _ (finiteBoxOpenGraph d ω x n) ↔
    FiniteBoxGraph.HasDenseCrossing _ (finiteBoxOpenGraph d η x n)
  rw [finiteBoxOpenGraph_eq_of_agree hagree]

theorem measurableSet_epsilonDenseCrossingClusterEvent
    (d : ℕ) (p : I) (ε : ℝ) (n : ℕ) (x : Cubic d) :
    MeasurableSet (epsilonDenseCrossingClusterEvent d p ε n x) :=
  (dependsOn_epsilonDenseCrossingClusterEvent d p ε n x).measurableSet

/-- Natural threshold implementing the real cluster-density inequality without an implicit
floor convention. -/
noncomputable def epsilonDenseCrossingThreshold
    (d : ℕ) (p : I) (ε : ℝ) (n : ℕ) : ℕ :=
  Nat.ceil ((1 - ε) * theta d p *
    ((cubicMetricBox d cubicOrigin n).card : ℝ))

theorem epsilonDenseCrossingClusterEvent_eq_largeCrossingClusterEvent
    (d : ℕ) (p : I) (ε : ℝ) (n : ℕ) :
    epsilonDenseCrossingClusterEvent d p ε n cubicOrigin =
      largeCrossingClusterEvent d (epsilonDenseCrossingThreshold d p ε n) n cubicOrigin := by
  ext ω
  constructor
  · rintro ⟨C, hcross, hcard⟩
    exact ⟨C, hcross, Nat.ceil_le.mpr hcard⟩
  · rintro ⟨C, hcross, hcard⟩
    exact ⟨C, hcross, Nat.le_of_ceil_le hcard⟩

/-- Grimmett Lemma 7.97 from the exact finite-slab connectivity package: above the critical
regime encoded by `hslab`, a box contains an all-direction crossing cluster with at least
`(1-ε) θ(p) |B(n)|` vertices with probability tending to one. -/
theorem epsilonDenseCrossingCluster_probability_tendsto_one_of_uniformFiniteSlab
    {d L : ℕ} (hd : 2 ≤ d) (p : I) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hθ : 0 < theta d p) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hslab : UniformFiniteSlabConnectionLowerBound d p L δ)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    Filter.Tendsto
      (fun n ↦ (bernoulliBondMeasure d p).real
        (epsilonDenseCrossingClusterEvent d p ε n cubicOrigin))
      Filter.atTop (nhds 1) := by
  obtain ⟨v, hv0, hcoalesce⟩ :=
    exists_logarithmicInset_infiniteClusterCoalescence_probability_tendsto_one
      hd p hp0 hp1 hδ0 hδ1 hslab
  let q : ℕ → ℕ := epsilonDenseCrossingThreshold d p ε
  have hqPos : ∀ᶠ n : ℕ in Filter.atTop, 1 ≤ q n := by
    apply Filter.Eventually.of_forall
    intro n
    change 1 ≤ epsilonDenseCrossingThreshold d p ε n
    rw [epsilonDenseCrossingThreshold, Nat.one_le_ceil_iff]
    have hcard : 0 < ((cubicMetricBox d cubicOrigin n).card : ℝ) := by
      rw [cubicMetricBox_card]
      positivity
    exact mul_pos (mul_pos (sub_pos.mpr hε1) hθ) hcard
  have hqDensity : ∀ᶠ n : ℕ in Filter.atTop, (q n : ℝ) ≤
      (1 - ε / 2) * theta d p *
        ((cubicMetricBox d cubicOrigin (logarithmicInsetRadius v n)).card : ℝ) := by
    have hratio := tendsto_logarithmicInset_boxCard_ratio (d := d) hv0.le
    have hcardTop := tendsto_cubicMetricBox_card_atTop (d := d) (by omega)
    have ha : 0 ≤ (1 - ε) * theta d p := by positivity
    have hab : (1 - ε) * theta d p < (1 - ε / 2) * theta d p := by
      nlinarith
    simpa [q, epsilonDenseCrossingThreshold, mul_assoc] using
      (eventually_natCeil_mul_le_mul_of_ratio_tendsto_one
        (fun n ↦ (cubicMetricBox d cubicOrigin (logarithmicInsetRadius v n)).card)
        (fun n ↦ (cubicMetricBox d cubicOrigin n).card)
        ha hab hratio hcardTop)
  have hlarge := largeCrossingCluster_probability_tendsto_one_of_coalescence
    (d := d) (by omega) p hθ (δ := ε / 2) (by positivity)
      (logarithmicInsetRadius v) id q
      (tendsto_logarithmicInsetRadius_atTop hv0.le)
      (fun n ↦ logarithmicInsetRadius_le v n) hqPos hqDensity hcoalesce
  simpa [epsilonDenseCrossingClusterEvent_eq_largeCrossingClusterEvent, q] using hlarge

/-- Grimmett Theorem 7.61 from the exact finite-slab connectivity package.  The logarithmic
diameter threshold is large enough for Lemma 7.104's exponential estimate and small enough
that any competing component cannot rival the dense crossing cluster from Lemma 7.97. -/
theorem epsilonGoodBox_probability_tendsto_one_of_uniformFiniteSlab
    {d L : ℕ} (hd : 2 ≤ d) (p : I) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hθ : 0 < theta d p) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hslab : UniformFiniteSlabConnectionLowerBound d p L δ)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    Filter.Tendsto
      (fun n ↦ (bernoulliBondMeasure d p).real
        (epsilonGoodBoxEvent d p ε cubicOrigin n))
      Filter.atTop (nhds 1) := by
  obtain ⟨μ, hμ0, hsecondBound⟩ :=
    exists_secondMacroscopicCluster_probability_le_exp_of_uniformFiniteSlab
      (by omega : 1 ≤ d) p hp0 hδ0 hδ1 hslab
  let w : ℝ := (2 * d + 1 : ℕ) / μ
  let m : ℕ → ℕ := logarithmicInsetWidth w
  let q : ℕ → ℕ := epsilonDenseCrossingThreshold d p ε
  have hw0 : 0 < w := by
    dsimp [w]
    positivity
  have hsecondDecay : Filter.Tendsto
      (fun n : ℕ ↦ d * ((cubicMetricBox d cubicOrigin n).card : ℝ) ^ 2 *
        Real.exp (-μ * logarithmicInsetWidth w n))
      Filter.atTop (nhds 0) := by
    have hraw := tendsto_cubicMetricBox_card_sq_mul_exp_neg_logarithmicInsetWidth
      d hw0 (ξ := μ) (v := w) (by
        dsimp [w]
        field_simp
        norm_num)
    simpa [mul_assoc] using (tendsto_const_nhds (x := (d : ℝ))).mul hraw
  have hsecond : Filter.Tendsto
      (fun n ↦ (bernoulliBondMeasure d p).real
        (secondMacroscopicClusterEvent d (m n) n cubicOrigin))
      Filter.atTop (nhds 0) := by
    apply squeeze_zero'
      (Filter.Eventually.of_forall fun _ ↦ measureReal_nonneg)
      (by
        filter_upwards [Filter.eventually_ge_atTop 1,
          (tendsto_logarithmicInsetWidth_atTop hw0).eventually (Filter.Ici_mem_atTop 1)]
          with n hn hmPos
        show (bernoulliBondMeasure d p).real
            (secondMacroscopicClusterEvent d (m n) n cubicOrigin) ≤ _
        have hbound := hsecondBound (m n) n hmPos hn
        calc
          (bernoulliBondMeasure d p).real
              (secondMacroscopicClusterEvent d (m n) n cubicOrigin) ≤
              d * (2 * n + 1 : ℝ) ^ (2 * d) * Real.exp (-μ * m n) := hbound
          _ = d * ((cubicMetricBox d cubicOrigin n).card : ℝ) ^ 2 *
              Real.exp (-μ * logarithmicInsetWidth w n) := by
            rw [cubicMetricBox_card]
            push_cast
            change _ * Real.exp (-μ * logarithmicInsetWidth w n) = _
            rw [show 2 * d = d + d by omega, pow_add]
            ring) hsecondDecay
  have hlargeSource :=
    epsilonDenseCrossingCluster_probability_tendsto_one_of_uniformFiniteSlab
      hd p hp0 hp1 hθ hδ0 hδ1 hslab hε0 hε1
  have hlarge : Filter.Tendsto
      (fun n ↦ (bernoulliBondMeasure d p).real
        (largeCrossingClusterEvent d (q n) n cubicOrigin))
      Filter.atTop (nhds 1) := by
    simpa [q, epsilonDenseCrossingClusterEvent_eq_largeCrossingClusterEvent] using
      hlargeSource
  have hsmallRatio := tendsto_logarithmicInsetWidth_boxCard_ratio
    (d := d) (by omega : 1 ≤ d) hw0.le
  have ha0 : 0 < (1 - ε) * theta d p := mul_pos (sub_pos.mpr hε1) hθ
  have hsmall : ∀ᶠ n : ℕ in Filter.atTop,
      (2 * m n + 1) ^ d < q n := by
    have hratioLt : ∀ᶠ n : ℕ in Filter.atTop,
        ((cubicMetricBox d cubicOrigin (m n)).card : ℝ) /
            (cubicMetricBox d cubicOrigin n).card <
          (1 - ε) * theta d p := by
      exact (tendsto_order.1 hsmallRatio).2 _ ha0
    filter_upwards [hratioLt] with n hn
    have houter0 : (0 : ℝ) < (cubicMetricBox d cubicOrigin n).card := by
      rw [cubicMetricBox_card]
      positivity
    have hreal : ((cubicMetricBox d cubicOrigin (m n)).card : ℝ) <
        (1 - ε) * theta d p * (cubicMetricBox d cubicOrigin n).card := by
      exact (div_lt_iff₀ houter0).mp hn
    have hceil : (1 - ε) * theta d p *
        ((cubicMetricBox d cubicOrigin n).card : ℝ) ≤ q n := by
      simpa [q, epsilonDenseCrossingThreshold] using
        Nat.le_ceil ((1 - ε) * theta d p *
          ((cubicMetricBox d cubicOrigin n).card : ℝ))
    rw [cubicMetricBox_card] at hreal
    exact_mod_cast hreal.trans_le hceil
  have hconstraints : ∀ᶠ n : ℕ in Filter.atTop,
      m n ≤ n ∧ (2 * m n + 1) ^ d < q n ∧
        (1 - ε) * theta d p * (cubicMetricBox d cubicOrigin n).card ≤ q n := by
    filter_upwards [eventually_logarithmicInsetWidth_le hw0.le, hsmall] with n hmn hsmallN
    refine ⟨hmn, hsmallN, ?_⟩
    simpa [q, epsilonDenseCrossingThreshold] using
      Nat.le_ceil ((1 - ε) * theta d p *
        ((cubicMetricBox d cubicOrigin n).card : ℝ))
  exact epsilonGoodBox_probability_tendsto_one_of_largeCrossing_of_second
    p ε cubicOrigin m q hconstraints hlarge hsecond

end Percolation
