import Percolation.Bernoulli.Basic
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Critical probability scaffold

Critical-point work should separate definition-level monotonicity from lattice-specific theorem
statements such as the square-lattice value `p_c = 1/2`.
-/

namespace Percolation

open scoped unitInterval

/-- A named package for a critical parameter attached to a Bernoulli bond model. -/
structure CriticalParameter (V : Type u) where
  model : BernoulliBond V
  pc : ℝ
  pc_nonneg : 0 ≤ pc
  pc_le_one : pc ≤ 1

/-- The connective constant `λ(d)`, represented as the critical eventual exponential growth
bound for the self-avoiding-walk counts. Proving that this agrees with Grimmett's limit
`lim σ(n)^(1/n)` is one of the Theorem 1.10 proof obligations. -/
noncomputable def cubicConnectiveConstant (d : ℕ) : ℝ :=
  sInf {c : ℝ | 0 ≤ c ∧ ∀ᶠ n in Filter.atTop,
    (selfAvoidingWalkCount d n : ℝ) ≤ c ^ n}

/-- The connective constant is bounded above by the number `2d` of signed coordinate directions. -/
theorem cubicConnectiveConstant_le_two_mul (d : ℕ) :
    cubicConnectiveConstant d ≤ (2 * d : ℝ) := by
  unfold cubicConnectiveConstant
  apply csInf_le
  · exact ⟨0, fun c hc ↦ hc.1⟩
  · constructor
    · positivity
    · filter_upwards [Filter.eventually_ge_atTop 0] with n hn
      exact_mod_cast selfAvoidingWalkCount_le_directionWords d n

/-- In nonzero dimension, the connective constant is at least one. -/
theorem one_le_cubicConnectiveConstant {d : ℕ} (hd : 0 < d) :
    (1 : ℝ) ≤ cubicConnectiveConstant d := by
  unfold cubicConnectiveConstant
  apply le_csInf
  · exact ⟨(2 * d : ℝ), by
      constructor
      · positivity
      · filter_upwards [Filter.eventually_ge_atTop 0] with n hn
        exact_mod_cast selfAvoidingWalkCount_le_directionWords d n⟩
  · intro c hc
    have hc0 : 0 ≤ c := hc.1
    have hev := hc.2
    have hex : ∃ n, 1 ≤ n ∧ (selfAvoidingWalkCount d n : ℝ) ≤ c ^ n := by
      exact ((Filter.eventually_ge_atTop 1).and hev).exists
    rcases hex with ⟨n, hn1, hbound⟩
    have hsigma_nat : 1 ≤ selfAvoidingWalkCount d n := one_le_selfAvoidingWalkCount hd n
    have hsigma : (1 : ℝ) ≤ (selfAvoidingWalkCount d n : ℝ) := by exact_mod_cast hsigma_nat
    have hpow : (1 : ℝ) ≤ c ^ n := hsigma.trans hbound
    by_contra hnot
    have hc_lt : c < 1 := lt_of_not_ge hnot
    have hnpos : 0 < n := by omega
    have hpow_lt : c ^ n < (1 : ℝ) := pow_lt_one₀ hc0 hc_lt hnpos.ne'
    exact not_lt_of_ge hpow hpow_lt

/-- Positivity of the connective constant in nonzero dimension. -/
theorem cubicConnectiveConstant_pos {d : ℕ} (hd : 0 < d) :
    0 < cubicConnectiveConstant d :=
  zero_lt_one.trans_le (one_le_cubicConnectiveConstant hd)

/-- If the Peierls parameter `q = 1 - p` satisfies `q λ(d) < 1` in nonzero dimension, then
`p > 0`. This removes the extra positivity hypothesis on finite open events in the later
`G_m` step. -/
theorem unitInterval_pos_of_one_sub_mul_cubicConnectiveConstant_lt_one {d : ℕ}
    (hd : 0 < d) (p : I)
    (h : (1 - (p : ℝ)) * cubicConnectiveConstant d < 1) :
    0 < (p : ℝ) := by
  by_contra hpnot
  have hp0 : (p : ℝ) = 0 := le_antisymm (le_of_not_gt hpnot) p.2.1
  have hlambda_lt : cubicConnectiveConstant d < 1 := by
    simpa [hp0] using h
  exact not_lt_of_ge (one_le_cubicConnectiveConstant hd) hlambda_lt

/-- The critical probability `p_c(d)`, as the supremum of parameters in `[0,1]` for which
the origin percolation probability is zero. -/
noncomputable def cubicCriticalProbability (d : ℕ) : ℝ :=
  sSup (((fun p : I ↦ (p : ℝ)) '' {p : I | theta d p = 0}) : Set ℝ)

/-- If `σ(n)` is eventually bounded by `c^n` and `q c < 1`, then the reindexed Peierls
closed-circuit bound `(n + 1) σ(n) q^(n+1)` tends to zero. -/
theorem tendsto_succ_mul_selfAvoidingWalkCount_mul_pow_succ_of_eventually_le_pow
    (d : ℕ) {q c : ℝ} (hc0 : 0 ≤ c) (hq0 : 0 ≤ q) (hqc : q * c < 1)
    (hbound : ∀ᶠ n in Filter.atTop, (selfAvoidingWalkCount d n : ℝ) ≤ c ^ n) :
    Filter.Tendsto
      (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ) * (selfAvoidingWalkCount d n : ℝ) * q ^ (n + 1))
      Filter.atTop (nhds 0) := by
  have hr0 : 0 ≤ q * c := mul_nonneg hq0 hc0
  have hgeom : Filter.Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1) * (q * c) ^ n)
      Filter.atTop (nhds 0) := by
    have hmul := tendsto_self_mul_const_pow_of_lt_one hr0 hqc
    have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hqc
    simpa [add_mul, one_mul] using hmul.add hpow
  have hupper : Filter.Tendsto (fun n : ℕ ↦ q * (((n : ℝ) + 1) * (q * c) ^ n))
      Filter.atTop (nhds 0) := by
    simpa using hgeom.const_mul q
  have hnonneg : ∀ᶠ n : ℕ in Filter.atTop,
      0 ≤ ((n + 1 : ℕ) : ℝ) * (selfAvoidingWalkCount d n : ℝ) * q ^ (n + 1) :=
    Filter.Eventually.of_forall fun n ↦ by
      exact mul_nonneg (mul_nonneg (by positivity) (by positivity)) (pow_nonneg hq0 _)
  have hle : ∀ᶠ n : ℕ in Filter.atTop,
      ((n + 1 : ℕ) : ℝ) * (selfAvoidingWalkCount d n : ℝ) * q ^ (n + 1) ≤
        q * (((n : ℝ) + 1) * (q * c) ^ n) := by
    filter_upwards [hbound] with n hn
    calc
      ((n + 1 : ℕ) : ℝ) * (selfAvoidingWalkCount d n : ℝ) * q ^ (n + 1) ≤
          ((n + 1 : ℕ) : ℝ) * c ^ n * q ^ (n + 1) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hn (by positivity)) (pow_nonneg hq0 _)
      _ = q * (((n : ℝ) + 1) * (q * c) ^ n) := by
        rw [pow_succ, mul_pow, Nat.cast_add, Nat.cast_one]
        ring_nf
  exact squeeze_zero' hnonneg hle hupper

/-- If `σ(n)` is eventually bounded by `c^n` and `q c < 1`, then the reindexed Peierls
closed-circuit majorant `(n + 1) σ(n) q^(n+1)` is summable. -/
theorem summable_succ_mul_selfAvoidingWalkCount_mul_pow_succ_of_eventually_le_pow
    (d : ℕ) {q c : ℝ} (hc0 : 0 ≤ c) (hq0 : 0 ≤ q) (hqc : q * c < 1)
    (hbound : ∀ᶠ n in Filter.atTop, (selfAvoidingWalkCount d n : ℝ) ≤ c ^ n) :
    Summable
      (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ) * (selfAvoidingWalkCount d n : ℝ) * q ^ (n + 1)) := by
  have hr0 : 0 ≤ q * c := mul_nonneg hq0 hc0
  have hrnorm : ‖q * c‖ < 1 := by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hq0, abs_of_nonneg hc0]
    exact hqc
  have hsumm_linear : Summable (fun n : ℕ ↦ (n : ℝ) * (q * c) ^ n) := by
    simpa [pow_one] using
      (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 (r := q * c) hrnorm)
  have hsumm_geom : Summable (fun n : ℕ ↦ (q * c) ^ n) :=
    summable_geometric_of_lt_one hr0 hqc
  have hsumm_upper : Summable (fun n : ℕ ↦ q * (((n : ℝ) + 1) * (q * c) ^ n)) := by
    have hsumm : Summable (fun n : ℕ ↦ ((n : ℝ) + 1) * (q * c) ^ n) := by
      simpa [add_mul, one_mul] using hsumm_linear.add hsumm_geom
    exact hsumm.mul_left q
  refine hsumm_upper.of_norm_bounded_eventually_nat ?_
  filter_upwards [hbound] with n hn
  have hf_nonneg :
      0 ≤ ((n + 1 : ℕ) : ℝ) * (selfAvoidingWalkCount d n : ℝ) * q ^ (n + 1) :=
    mul_nonneg (mul_nonneg (by positivity) (by positivity)) (pow_nonneg hq0 _)
  rw [Real.norm_eq_abs, abs_of_nonneg hf_nonneg]
  calc
    ((n + 1 : ℕ) : ℝ) * (selfAvoidingWalkCount d n : ℝ) * q ^ (n + 1) ≤
        ((n + 1 : ℕ) : ℝ) * c ^ n * q ^ (n + 1) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hn (by positivity)) (pow_nonneg hq0 _)
    _ = q * (((n : ℝ) + 1) * (q * c) ^ n) := by
      rw [pow_succ, mul_pow, Nat.cast_add, Nat.cast_one]
      ring_nf

/-- If `σ(n)` is eventually bounded by `c^n` and `q c < 1`, then Grimmett's Peierls
closed-circuit term `n σ(n-1) q^n` tends to zero. -/
theorem tendsto_peierlsCircuitBound_of_eventually_selfAvoidingWalkCount_le_pow
    (d : ℕ) {q c : ℝ} (hc0 : 0 ≤ c) (hq0 : 0 ≤ q) (hqc : q * c < 1)
    (hbound : ∀ᶠ n in Filter.atTop, (selfAvoidingWalkCount d n : ℝ) ≤ c ^ n) :
    Filter.Tendsto
      (fun n : ℕ ↦ (n : ℝ) * (selfAvoidingWalkCount d (n - 1) : ℝ) * q ^ n)
      Filter.atTop (nhds 0) := by
  rw [← Filter.tendsto_add_atTop_iff_nat (f := fun n : ℕ ↦
    (n : ℝ) * (selfAvoidingWalkCount d (n - 1) : ℝ) * q ^ n) 1]
  simpa [Nat.add_sub_cancel] using
    (tendsto_succ_mul_selfAvoidingWalkCount_mul_pow_succ_of_eventually_le_pow
      d hc0 hq0 hqc hbound)

/-- If `σ(n)` is eventually bounded by `c^n` and `q c < 1`, then Grimmett's Peierls
closed-circuit majorant `n σ(n-1) q^n` is summable. -/
theorem summable_peierlsCircuitBound_of_eventually_selfAvoidingWalkCount_le_pow
    (d : ℕ) {q c : ℝ} (hc0 : 0 ≤ c) (hq0 : 0 ≤ q) (hqc : q * c < 1)
    (hbound : ∀ᶠ n in Filter.atTop, (selfAvoidingWalkCount d n : ℝ) ≤ c ^ n) :
    Summable (fun n : ℕ ↦ (n : ℝ) * (selfAvoidingWalkCount d (n - 1) : ℝ) * q ^ n) := by
  rw [← summable_nat_add_iff (f := fun n : ℕ ↦
    (n : ℝ) * (selfAvoidingWalkCount d (n - 1) : ℝ) * q ^ n) 1]
  simpa [Nat.add_sub_cancel] using
    (summable_succ_mul_selfAvoidingWalkCount_mul_pow_succ_of_eventually_le_pow
      d hc0 hq0 hqc hbound)

/-- Grimmett's Peierls closed-circuit tail criterion extracted from the connective constant:
if `q λ(d) < 1`, then the sequence `n σ(n-1) q^n` tends to zero. -/
theorem tendsto_peierlsCircuitBound_of_mul_cubicConnectiveConstant_lt_one
    (d : ℕ) {q : ℝ} (hq0 : 0 ≤ q) (h : q * cubicConnectiveConstant d < 1) :
    Filter.Tendsto
      (fun n : ℕ ↦ (n : ℝ) * (selfAvoidingWalkCount d (n - 1) : ℝ) * q ^ n)
      Filter.atTop (nhds 0) := by
  let S : Set ℝ := {c : ℝ | 0 ≤ c ∧ ∀ᶠ n in Filter.atTop,
    (selfAvoidingWalkCount d n : ℝ) ≤ c ^ n}
  have hS_nonempty : S.Nonempty := by
    refine ⟨(2 * d : ℝ), ?_⟩
    constructor
    · positivity
    · filter_upwards [Filter.eventually_ge_atTop 0] with n hn
      exact_mod_cast selfAvoidingWalkCount_le_directionWords d n
  by_cases hqzero : q = 0
  · refine tendsto_const_nhds.congr' ?_
    exact Filter.Eventually.of_forall fun n ↦ by
      cases n <;> simp [hqzero]
  · have hq_pos : 0 < q := lt_of_le_of_ne hq0 (Ne.symm hqzero)
    have hlambda_lt_inv : cubicConnectiveConstant d < 1 / q := by
      rw [lt_div_iff₀ hq_pos]
      simpa [mul_comm] using h
    rcases exists_between hlambda_lt_inv with ⟨b, hlambda_lt_b, hb_lt_inv⟩
    have hInf_lt_b : sInf S < b := by
      simpa [cubicConnectiveConstant, S] using hlambda_lt_b
    rcases exists_lt_of_csInf_lt hS_nonempty hInf_lt_b with ⟨c, hcS, hc_lt_b⟩
    have hq_c_lt_one : q * c < 1 := by
      have hc_lt_inv : c < 1 / q := hc_lt_b.trans hb_lt_inv
      rw [lt_div_iff₀ hq_pos] at hc_lt_inv
      simpa [mul_comm] using hc_lt_inv
    exact tendsto_peierlsCircuitBound_of_eventually_selfAvoidingWalkCount_le_pow
      d hcS.1 hq0 hq_c_lt_one hcS.2

/-- Grimmett's Peierls closed-circuit summability criterion extracted from the connective
constant: if `q λ(d) < 1`, then the majorant `n σ(n-1) q^n` is summable. -/
theorem summable_peierlsCircuitBound_of_mul_cubicConnectiveConstant_lt_one
    (d : ℕ) {q : ℝ} (hq0 : 0 ≤ q) (h : q * cubicConnectiveConstant d < 1) :
    Summable (fun n : ℕ ↦ (n : ℝ) * (selfAvoidingWalkCount d (n - 1) : ℝ) * q ^ n) := by
  let S : Set ℝ := {c : ℝ | 0 ≤ c ∧ ∀ᶠ n in Filter.atTop,
    (selfAvoidingWalkCount d n : ℝ) ≤ c ^ n}
  have hS_nonempty : S.Nonempty := by
    refine ⟨(2 * d : ℝ), ?_⟩
    constructor
    · positivity
    · filter_upwards [Filter.eventually_ge_atTop 0] with n hn
      exact_mod_cast selfAvoidingWalkCount_le_directionWords d n
  by_cases hqzero : q = 0
  · rw [← summable_nat_add_iff (f := fun n : ℕ ↦
      (n : ℝ) * (selfAvoidingWalkCount d (n - 1) : ℝ) * q ^ n) 1]
    refine summable_zero.congr ?_
    intro n
    simp [hqzero]
  · have hq_pos : 0 < q := lt_of_le_of_ne hq0 (Ne.symm hqzero)
    have hlambda_lt_inv : cubicConnectiveConstant d < 1 / q := by
      rw [lt_div_iff₀ hq_pos]
      simpa [mul_comm] using h
    rcases exists_between hlambda_lt_inv with ⟨b, hlambda_lt_b, hb_lt_inv⟩
    have hInf_lt_b : sInf S < b := by
      simpa [cubicConnectiveConstant, S] using hlambda_lt_b
    rcases exists_lt_of_csInf_lt hS_nonempty hInf_lt_b with ⟨c, hcS, hc_lt_b⟩
    have hq_c_lt_one : q * c < 1 := by
      have hc_lt_inv : c < 1 / q := hc_lt_b.trans hb_lt_inv
      rw [lt_div_iff₀ hq_pos] at hc_lt_inv
      simpa [mul_comm] using hc_lt_inv
    exact summable_peierlsCircuitBound_of_eventually_selfAvoidingWalkCount_le_pow
      d hcS.1 hq0 hq_c_lt_one hcS.2

/-- A real summable series has tails tending to zero, written in the shifted-index form used by
the Peierls circuit tail. -/
theorem tendsto_tsum_nat_add_zero_of_summable {f : ℕ → ℝ} (hf : Summable f) :
    Filter.Tendsto (fun k : ℕ ↦ ∑' n : ℕ, f (n + k)) Filter.atTop (nhds 0) := by
  have htail_eq : (fun k : ℕ ↦ ∑' n : ℕ, f (n + k)) =
      fun k : ℕ ↦ (∑' n : ℕ, f n) - ∑ n ∈ Finset.range k, f n := by
    funext k
    rw [eq_sub_iff_add_eq]
    simpa [add_comm] using hf.sum_add_tsum_nat_add k
  rw [htail_eq]
  have hpartial : Filter.Tendsto (fun k : ℕ ↦ ∑ n ∈ Finset.range k, f n)
      Filter.atTop (nhds (∑' n : ℕ, f n)) :=
    hf.hasSum.tendsto_sum_nat
  have hconst : Filter.Tendsto (fun _ : ℕ ↦ ∑' n : ℕ, f n) Filter.atTop
      (nhds (∑' n : ℕ, f n)) :=
    tendsto_const_nhds
  simpa using hconst.sub hpartial

/-- Grimmett's Peierls closed-circuit tail criterion in tail-sum form: if `q λ(d) < 1`, then
the sum of the majorants for all lengths at least `N` tends to zero as `N → ∞`. -/
theorem tendsto_peierlsCircuitTail_tsum_of_mul_cubicConnectiveConstant_lt_one
    (d : ℕ) {q : ℝ} (hq0 : 0 ≤ q) (h : q * cubicConnectiveConstant d < 1) :
    Filter.Tendsto
      (fun N : ℕ ↦ ∑' k : ℕ,
        ((k + N : ℕ) : ℝ) * (selfAvoidingWalkCount d (k + N - 1) : ℝ) * q ^ (k + N))
      Filter.atTop (nhds 0) := by
  exact tendsto_tsum_nat_add_zero_of_summable
    (summable_peierlsCircuitBound_of_mul_cubicConnectiveConstant_lt_one d hq0 h)

/-- Grimmett's lower-tail criterion extracted from the definition of the connective constant:
if `p λ(d) < 1`, then the origin percolation probability vanishes. -/
theorem theta_eq_zero_of_mul_cubicConnectiveConstant_lt_one (d : ℕ) (p : I)
    (h : (p : ℝ) * cubicConnectiveConstant d < 1) :
    theta d p = 0 := by
  let S : Set ℝ := {c : ℝ | 0 ≤ c ∧ ∀ᶠ n in Filter.atTop,
    (selfAvoidingWalkCount d n : ℝ) ≤ c ^ n}
  have hS_nonempty : S.Nonempty := by
    refine ⟨(2 * d : ℝ), ?_⟩
    constructor
    · positivity
    · filter_upwards [Filter.eventually_ge_atTop 0] with n hn
      exact_mod_cast selfAvoidingWalkCount_le_directionWords d n
  by_cases hpzero : (p : ℝ) = 0
  · rcases hS_nonempty with ⟨c, hcS⟩
    exact theta_eq_zero_of_eventually_selfAvoidingWalkCount_le_pow d p hcS.1
      (by simp [hpzero]) hcS.2
  · have hp_pos : 0 < (p : ℝ) := lt_of_le_of_ne p.2.1 (Ne.symm hpzero)
    have hlambda_lt_inv : cubicConnectiveConstant d < 1 / (p : ℝ) := by
      rw [lt_div_iff₀ hp_pos]
      simpa [mul_comm] using h
    rcases exists_between hlambda_lt_inv with ⟨b, hlambda_lt_b, hb_lt_inv⟩
    have hInf_lt_b : sInf S < b := by
      simpa [cubicConnectiveConstant, S] using hlambda_lt_b
    rcases exists_lt_of_csInf_lt hS_nonempty hInf_lt_b with ⟨c, hcS, hc_lt_b⟩
    have hp_c_lt_one : (p : ℝ) * c < 1 := by
      have hc_lt_inv : c < 1 / (p : ℝ) := hc_lt_b.trans hb_lt_inv
      rw [lt_div_iff₀ hp_pos] at hc_lt_inv
      simpa [mul_comm] using hc_lt_inv
    exact theta_eq_zero_of_eventually_selfAvoidingWalkCount_le_pow d p hcS.1 hp_c_lt_one hcS.2

/-- Grimmett's path-counting lower bound `1 / λ(d) ≤ p_c(d)`. -/
theorem connectiveConstant_inv_le_cubicCriticalProbability {d : ℕ} (hd : 2 ≤ d) :
    1 / cubicConnectiveConstant d ≤ cubicCriticalProbability d := by
  let A : Set ℝ := ((fun p : I ↦ (p : ℝ)) '' {p : I | theta d p = 0})
  let p0 : I := ⟨0, by norm_num, by norm_num⟩
  have hzero_mem_A : (0 : ℝ) ∈ A := by
    refine ⟨p0, ?_, rfl⟩
    exact theta_eq_zero_of_mul_cubicConnectiveConstant_lt_one d p0 (by simp [p0])
  have hA_nonempty : A.Nonempty := ⟨0, hzero_mem_A⟩
  have hA_bddAbove : BddAbove A := by
    refine ⟨1, ?_⟩
    rintro x ⟨p, hp, rfl⟩
    exact p.2.2
  have hdpos : 0 < d := by omega
  have hlambda_ge_one : 1 ≤ cubicConnectiveConstant d := one_le_cubicConnectiveConstant hdpos
  have hlambda_pos : 0 < cubicConnectiveConstant d := zero_lt_one.trans_le hlambda_ge_one
  have hinv_le_one : 1 / cubicConnectiveConstant d ≤ 1 := by
    rw [div_le_iff₀ hlambda_pos]
    simpa using hlambda_ge_one
  rw [cubicCriticalProbability]
  change 1 / cubicConnectiveConstant d ≤ sSup A
  rw [le_csSup_iff hA_bddAbove hA_nonempty]
  intro b hb
  have hb0 : 0 ≤ b := hb hzero_mem_A
  apply le_of_forall_lt
  intro y hy
  by_cases hyneg : y < 0
  · exact hyneg.trans_le hb0
  · have hy_nonneg : 0 ≤ y := le_of_not_gt hyneg
    rcases exists_between hy with ⟨z, hyz, hz_lt_inv⟩
    have hz_nonneg : 0 ≤ z := hy_nonneg.trans hyz.le
    have hz_le_one : z ≤ 1 := (hz_lt_inv.trans_le hinv_le_one).le
    let pz : I := ⟨z, hz_nonneg, hz_le_one⟩
    have hpz_theta : theta d pz = 0 := by
      apply theta_eq_zero_of_mul_cubicConnectiveConstant_lt_one
      have hz_mul_lt : z * cubicConnectiveConstant d < 1 := by
        rw [← lt_div_iff₀ hlambda_pos]
        exact hz_lt_inv
      simpa [pz] using hz_mul_lt
    have hz_mem_A : z ∈ A := ⟨pz, hpz_theta, rfl⟩
    exact hyz.trans_le (hb hz_mem_A)

/-- Critical probability is antitone in the cubic-lattice dimension. This formalizes the
dimension-monotonicity step used in Grimmett's proof of Theorem (1.10): a lower-dimensional
lattice embeds into any higher-dimensional one, and the Bernoulli product law projects correctly
along that embedding. -/
theorem cubicCriticalProbability_antitone_dimension {m d : ℕ} (hmd : m ≤ d) :
    cubicCriticalProbability d ≤ cubicCriticalProbability m := by
  let Ad : Set ℝ := ((fun p : I ↦ (p : ℝ)) '' {p : I | theta d p = 0})
  let Am : Set ℝ := ((fun p : I ↦ (p : ℝ)) '' {p : I | theta m p = 0})
  have hAm_bddAbove : BddAbove Am := by
    refine ⟨1, ?_⟩
    rintro x ⟨p, _hp, rfl⟩
    exact p.2.2
  have hAd_nonempty : Ad.Nonempty := by
    let p0 : I := ⟨0, by norm_num, by norm_num⟩
    refine ⟨0, ?_⟩
    refine ⟨p0, ?_, rfl⟩
    exact theta_eq_zero_of_mul_cubicConnectiveConstant_lt_one d p0 (by simp [p0])
  have hsubset : Ad ⊆ Am := by
    rintro x ⟨p, hp, rfl⟩
    exact ⟨p, theta_eq_zero_of_le_dimension hmd hp, rfl⟩
  rw [cubicCriticalProbability, cubicCriticalProbability]
  change sSup Ad ≤ sSup Am
  exact csSup_le_csSup hAm_bddAbove hAd_nonempty hsubset

/-- The missing hard ingredients in Grimmett's proof of Theorem 1.10 and Equation (1.12).

This is deliberately a hypothesis package rather than an axiom: the final theorem reductions below
are build-checked now, while the source-faithful Peierls-duality argument remains an explicit
obligation for later proving. The path-counting lower bound is proved as
`connectiveConstant_inv_le_cubicCriticalProbability`, and dimension monotonicity is proved as
`cubicCriticalProbability_antitone_dimension`. -/
structure GrimmettTheorem110Inputs : Prop where
  /-- The planar Peierls bound in Equation (1.12). -/
  planar_peierls_upper_bound :
    cubicCriticalProbability 2 ≤ 1 - 1 / cubicConnectiveConstant 2

/-- Grimmett, *Percolation*, Equation (1.12), conditional on the formalized proof inputs. -/
theorem cubicCriticalProbability_two_bounds_of_grimmettTheorem110Inputs
    (h : GrimmettTheorem110Inputs) :
    1 / cubicConnectiveConstant 2 ≤ cubicCriticalProbability 2 ∧
      cubicCriticalProbability 2 ≤ 1 - 1 / cubicConnectiveConstant 2 :=
  ⟨connectiveConstant_inv_le_cubicCriticalProbability (by norm_num),
    h.planar_peierls_upper_bound⟩

/-- Grimmett, *Percolation*, Theorem (1.10), conditional on the formalized proof inputs. -/
theorem cubicCriticalProbability_pos_lt_one_of_grimmettTheorem110Inputs
    (h : GrimmettTheorem110Inputs) {d : ℕ} (hd : 2 ≤ d) :
    0 < cubicCriticalProbability d ∧ cubicCriticalProbability d < 1 := by
  constructor
  · have hdpos : 0 < d := by omega
    exact (one_div_pos.mpr (cubicConnectiveConstant_pos hdpos)).trans_le
      (connectiveConstant_inv_le_cubicCriticalProbability hd)
  · exact (cubicCriticalProbability_antitone_dimension hd).trans_lt <|
      h.planar_peierls_upper_bound.trans_lt <| by
        have hpos : 0 < 1 / cubicConnectiveConstant 2 :=
          one_div_pos.mpr (cubicConnectiveConstant_pos (by norm_num))
        linarith

end Percolation
